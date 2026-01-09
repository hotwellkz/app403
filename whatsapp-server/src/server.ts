import express from 'express';
import { Server } from 'socket.io';
import { createServer } from 'http';
import cors from 'cors';
import { Client, LocalAuth, Message, MessageMedia } from 'whatsapp-web.js';
import qrcode from 'qrcode';
import { loadChats, addMessage, saveChats, initializeChatsCache, clearUnread, deleteChat } from './utils/chatStorage';
import { Chat, ChatMessage } from './types/chat';
import { 
    getAllContacts, 
    getContactById, 
    createContact, 
    updateContact, 
    deleteContact, 
    searchContacts 
} from './utils/contactStorage';
import { ContactResponse, ContactsResponse, CreateContactRequest, UpdateContactRequest } from './types/contact';
import { 
    getContactAvatar, 
    getMultipleContactAvatars, 
    clearAvatarCache, 
    getAvatarCacheStats 
} from './utils/avatarCache';
import { 
    updateReadStatus, 
    getReadStatus,
    getAllReadStatuses,
    calculateUnreadCount,
    calculateUnreadCountsForAllChats,
    markChatAsRead,
    deleteReadStatus,
    getReadStatusStats,
    getNewMessagesAfterTimestamp
} from './utils/readStatusStorage';
import { ReadStatusResponse, GetReadStatusResponse, UnreadCountResponse, UpdateReadStatusRequest } from './types/readStatus';
import fileUpload from 'express-fileupload';
import { uploadMediaToSupabase, initializeMediaBucket } from './config/supabase';
import axios from 'axios';
import path from 'path';
import dotenv from 'dotenv';
import fs from 'fs/promises';
import os from 'os';

// Загружаем переменные окружения
const envPath = path.resolve(__dirname, '../.env');
dotenv.config({ path: envPath });

const PORT = process.env.PORT || 3000;
const FRONTEND_URL = process.env.FRONTEND_URL || 'http://localhost:5173';

// Поддержка множественных origins для CORS
const getAllowedOrigins = (): string[] => {
    const origins = [FRONTEND_URL];
    
    // Автоматически добавляем популярные домены для разработки
    const defaultDomains = [
        'https://2wix.ru',           // Основной домен пользователя
        'http://localhost:3000',     // Локальная разработка бэка
        'http://localhost:5173',     // Локальная разработка фронта (Vite)
        'http://localhost:3001',     // Альтернативный порт
        'http://127.0.0.1:5173',     // Альтернативный localhost
    ];
    
    defaultDomains.forEach(domain => {
        if (!origins.includes(domain)) {
            origins.push(domain);
        }
    });
    
    // Добавляем дополнительные origins из переменных окружения
    if (process.env.ALLOWED_ORIGINS) {
        const additionalOrigins = process.env.ALLOWED_ORIGINS.split(',').map(origin => origin.trim());
        origins.push(...additionalOrigins);
    }
    
    // Для production добавляем и www и без www версии
    if (process.env.NODE_ENV === 'production') {
        const mainDomain = FRONTEND_URL;
        const wwwDomain = mainDomain.replace('https://', 'https://www.');
        const nonWwwDomain = mainDomain.replace('https://www.', 'https://');
        
        if (!origins.includes(wwwDomain)) origins.push(wwwDomain);
        if (!origins.includes(nonWwwDomain)) origins.push(nonWwwDomain);
    }
    
    console.log('🔗 Allowed CORS origins:', origins);
    return origins;
};

const allowedOrigins = getAllowedOrigins();

// =============================================================================
// УПРАВЛЕНИЕ АККАУНТОМ WHATSAPP
// =============================================================================

// Переменные для управления аккаунтом
let currentAccountInfo: {
    phoneNumber?: string;
    name?: string;
    profilePicUrl?: string;
    isReady: boolean;
    connectedAt?: string;
} = { isReady: false };

let qrCode: string | null = null;
let isInitializing = false;

// =============================================================================
// WHATSAPP STATE MANAGEMENT (для state replay)
// =============================================================================

type WhatsAppState = "idle" | "qr" | "authenticated" | "ready" | "disconnected" | "blocked";

let waState: WhatsAppState = "idle";
let lastQr: string | null = null;
let lastDisconnectReason: string | null = null;
let isReinitializing = false; // Флаг для предотвращения двойной инициализации

// Флаги для детекции блокировки доменов WhatsApp
let isBlocked = false;
let blockedReason: string | null = null;
let blockedUrl: string | null = null;

// Счетчики для защиты от ложных срабатываний
let criticalBlockedCount = 0; // Критичные домены (web.whatsapp.com, g.whatsapp.net)
let mediaBlockedCount = 0; // Media CDN (media-*.cdn.whatsapp.net)
const CRITICAL_BLOCK_THRESHOLD = 2; // Минимум 2 критичных блокировки для установки флага
const MEDIA_BLOCK_IGNORE_THRESHOLD = 5; // Игнорируем до 5 блокировок media CDN

// Watchdog для отслеживания ready timeout после authenticated
let readyTimer: NodeJS.Timeout | null = null;
let hasWatchdogResetAttempted = false; // Флаг для предотвращения повторных reset от watchdog

// Таймаут ожидания READY (настраиваемый через ENV WA_READY_TIMEOUT_MS, по умолчанию 60 секунд)
const READY_TIMEOUT_MS: number = (() => {
    const env = process.env.WA_READY_TIMEOUT_MS;
    const parsed = env ? parseInt(env, 10) : NaN;
    return Number.isFinite(parsed) && parsed > 0 ? parsed : 60000;
})();

// Функция для остановки watchdog таймера
const stopReadyWatchdog = (): void => {
    if (readyTimer) {
        clearTimeout(readyTimer);
        readyTimer = null;
        console.log('[WA] watchdog stopped');
    }
};

// Функция для запуска watchdog таймера после authenticated
const startReadyWatchdog = (): void => {
    // Останавливаем предыдущий таймер если есть
    stopReadyWatchdog();
    
    // Сбрасываем флаг reset попытки при новом AUTHENTICATED
    hasWatchdogResetAttempted = false;
    
    console.log(`[WA] watchdog started: waiting for ready (${READY_TIMEOUT_MS}ms timeout)`);
    
    readyTimer = setTimeout(async () => {
        console.log('[WA] watchdog timeout triggered');
        console.log(`[WA] watchdog check: waState=${waState}, resetAttempted=${hasWatchdogResetAttempted}, isReinitializing=${isReinitializing}`);
        console.log(`[WA] watchdog check: isClientReady=${isClientReady}`);
        
        // Диагностика: проверяем состояние клиента и, если возможно, снимаем снимки страницы
        try {
            if (client) {
                const anyClient = client as any;
                const page = anyClient.pupPage || (anyClient.getPage ? await anyClient.getPage() : null);
                
                console.log(`[WA] watchdog: client exists, client.info exists? ${!!client.info}`);
                
                const debugDir = path.resolve(__dirname, '../debug');
                try {
                    await fs.mkdir(debugDir, { recursive: true });
                } catch (mkdirErr: any) {
                    console.log('[WA] watchdog: error creating debug dir:', mkdirErr?.message || mkdirErr);
                }
                
                if (page) {
                    // Проверяем что page не закрыт перед диагностикой
                    try {
                        if (page.isClosed()) {
                            console.log('[WA] watchdog: page is closed, skipping diagnostics');
                            return;
                        }
                        
                        const browser = page.browser();
                        if (browser && !browser.isConnected()) {
                            console.log('[WA] watchdog: browser is disconnected, skipping diagnostics');
                            return;
                        }
                    } catch (checkErr: any) {
                        if (checkErr?.message?.includes('Session closed') || 
                            checkErr?.message?.includes('Protocol error') ||
                            checkErr?.message?.includes('Target closed')) {
                            console.log('[WA] watchdog: page/browser closed, skipping diagnostics');
                            return;
                        }
                    }
                    
                    const ts = new Date().toISOString().replace(/[:.]/g, '-');
                    const basePath = path.join(debugDir, `wa_stuck_${ts}`);
                    
                    console.log('[WA] watchdog: capturing stuck page diagnostics to', basePath);
                    
                    try {
                        // Проверяем перед скриншотом
                        if (!page.isClosed()) {
                            await page.screenshot({ path: `${basePath}.png`, fullPage: true });
                        }
                    } catch (e: any) {
                        if (e?.message?.includes('Session closed') || 
                            e?.message?.includes('Protocol error') ||
                            e?.message?.includes('Target closed')) {
                            console.log('[WA] watchdog: page closed during screenshot, skipping');
                        } else {
                            console.log('[WA] watchdog: screenshot error:', e?.message || e);
                        }
                    }
                    
                    try {
                        // Проверяем перед content
                        if (!page.isClosed()) {
                            const html = await page.content();
                            await fs.writeFile(`${basePath}.html`, html, 'utf8');
                        }
                    } catch (e: any) {
                        if (e?.message?.includes('Session closed') || 
                            e?.message?.includes('Protocol error') ||
                            e?.message?.includes('Target closed')) {
                            console.log('[WA] watchdog: page closed during content, skipping');
                        } else {
                            console.log('[WA] watchdog: saving HTML error:', e?.message || e);
                        }
                    }
                    
                    try {
                        // Проверяем перед evaluate
                        if (!page.isClosed()) {
                            // URL, стореджи и userAgent
                            const storageDump = await page.evaluate(() => {
                            const localStorageObj: any = {};
                            const sessionStorageObj: any = {};
                            try {
                                for (let i = 0; i < localStorage.length; i++) {
                                    const key = localStorage.key(i);
                                    if (key) localStorageObj[key] = localStorage.getItem(key);
                                }
                            } catch (e) {
                                localStorageObj['_error'] = String(e);
                            }
                            try {
                                for (let i = 0; i < sessionStorage.length; i++) {
                                    const key = sessionStorage.key(i);
                                    if (key) sessionStorageObj[key] = sessionStorage.getItem(key);
                                }
                            } catch (e) {
                                sessionStorageObj['_error'] = String(e);
                            }
                            return {
                                url: window.location.href,
                                readyState: document.readyState,
                                title: document.title,
                                userAgent: navigator.userAgent,
                                localStorage: localStorageObj,
                                sessionStorage: sessionStorageObj,
                            };
                            });
                            await fs.writeFile(`${basePath}.storage.json`, JSON.stringify(storageDump, null, 2), 'utf8');
                            console.log('[WA] watchdog: storage dump saved:', {
                                url: storageDump.url,
                                readyState: storageDump.readyState,
                                title: storageDump.title,
                            });
                        }
                    } catch (e: any) {
                        if (e?.message?.includes('Session closed') || 
                            e?.message?.includes('Protocol error') ||
                            e?.message?.includes('Target closed')) {
                            console.log('[WA] watchdog: page closed during evaluate, skipping');
                        } else {
                            console.log('[WA] watchdog: storage dump error:', e?.message || e);
                        }
                    }
                } else {
                    console.log('[WA] watchdog: no pupPage available, cannot capture screenshots');
                }
            } else {
                console.log('[WA] watchdog: client is null/undefined');
            }
        } catch (diagError: any) {
            console.log('[WA] watchdog: unexpected error during diagnostics:', diagError?.message || diagError);
        }
        
        // После диагностики выполняем ОДИН controlled reset, если ещё не делали
        // НО НЕ делаем reset если домены заблокированы
        if (isBlocked) {
            console.log('[WA] watchdog timeout but domains are BLOCKED - skipping reset. User action required.');
            return;
        }
        
        if (waState === 'authenticated' && !hasWatchdogResetAttempted && !isReinitializing) {
            hasWatchdogResetAttempted = true;
            console.log('[WA] READY timeout after authenticated, doing controlled reset (single attempt per session)');
            await controlledReset('READY_TIMEOUT');
        } else {
            console.log(`[WA] watchdog timeout but state=${waState}, resetAttempted=${hasWatchdogResetAttempted}, isReinitializing=${isReinitializing} - skipping reset`);
        }
        
        readyTimer = null;
    }, READY_TIMEOUT_MS);
};

// Функция для обновления состояния и отправки клиентам
const updateWaState = (newState: WhatsAppState, qrData?: string | null, reason?: string | null) => {
    const oldState = waState;
    waState = newState;
    
    if (qrData !== undefined) {
        lastQr = qrData;
    }
    
    if (reason !== undefined) {
        lastDisconnectReason = reason;
    }
    
    // Сбрасываем флаг блокировки при переходе в qr или idle (новый старт)
    if (newState === 'qr' || newState === 'idle') {
        isBlocked = false;
        blockedReason = null;
        blockedUrl = null;
        criticalBlockedCount = 0;
        mediaBlockedCount = 0;
    }
    
    console.log(`[WA] state=${oldState} -> ${newState}${lastQr ? ' (QR available)' : ''}${reason ? ` reason=${reason}` : ''}`);
    
    // Останавливаем watchdog при переходе в ready, qr или disconnected
    if (newState === 'ready' || newState === 'qr' || newState === 'disconnected') {
        stopReadyWatchdog();
    }
    
    // Отправляем новое состояние всем подключенным клиентам
    const stateData: any = {
        state: waState,
        reason: lastDisconnectReason,
        timestamp: new Date().toISOString()
    };
    
    // Добавляем информацию о блокировке если есть
    if (newState === 'blocked' && isBlocked) {
        stateData.blockedReason = blockedReason;
        stateData.blockedUrl = blockedUrl;
    }
    
    io.emit('wa:state', stateData);
    
    // Если есть QR, отправляем его тоже
    if (waState === 'qr' && lastQr) {
        io.emit('wa:qr', lastQr);
    }
};

// =============================================================================
// КОНЕЦ WHATSAPP STATE MANAGEMENT
// =============================================================================

// =============================================================================
// УТИЛИТЫ ДЛЯ БЕЗОПАСНОГО УДАЛЕНИЯ (Windows EBUSY fix)
// =============================================================================

// Функция задержки
const delay = (ms: number): Promise<void> => {
    return new Promise(resolve => setTimeout(resolve, ms));
};

// Безопасное удаление директории с retry (для Windows EBUSY/EPERM)
const safeRemoveDir = async (dirPath: string, maxAttempts: number = 12): Promise<boolean> => {
    const backoffDelays = [250, 400, 650, 1000, 1500, 2000, 2500, 3000, 3500, 4000, 4000, 4000];
    
    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
        try {
            await fs.rm(dirPath, { recursive: true, force: true });
            console.log(`[WA] removed dir: ${dirPath} (attempt ${attempt})`);
            return true;
        } catch (error: any) {
            const isRetryableError = 
                error.code === 'EBUSY' || 
                error.code === 'EPERM' || 
                error.code === 'ENOTEMPTY' ||
                error.code === 'EACCES';
            
            if (!isRetryableError) {
                console.error(`[WA] non-retryable error removing ${dirPath}:`, error.code);
                return false;
            }
            
            const delayMs = backoffDelays[attempt - 1] || 4000;
            
            if (attempt < maxAttempts) {
                console.log(`[WA] remove auth attempt ${attempt} failed ${error.code} -> retry in ${delayMs}ms`);
                await delay(delayMs);
            } else {
                console.warn(`[WA] failed to remove ${dirPath} after ${maxAttempts} attempts (${error.code})`);
                return false;
            }
        }
    }
    
    return false;
};

// =============================================================================
// КОНЕЦ УТИЛИТ ДЛЯ БЕЗОПАСНОГО УДАЛЕНИЯ
// =============================================================================

// =============================================================================
// СТАБИЛИЗАЦИЯ СОЕДИНЕНИЯ WHATSAPP
// =============================================================================

// Флаги для контроля соединения
let isClientReady = false;
let isReconnecting = false;
let reconnectAttempts = 0;
const MAX_RECONNECT_ATTEMPTS = 5;
const RECONNECT_DELAY = 5000; // 5 секунд

// Функция логирования состояния соединения
const logConnectionState = (state: string, details?: any) => {
    const timestamp = new Date().toISOString();
    console.log(`[${timestamp}] 🔌 WhatsApp Connection: ${state}`, details || '');
    
    // Уведомляем клиентов о состоянии
    io.emit('connection-state', { 
        state, 
        details, 
        timestamp,
        isReady: isClientReady,
        reconnectAttempts 
    });
};

// Функция безопасного переподключения
const safeReconnect = async (reason: string = 'Unknown'): Promise<void> => {
    if (isReconnecting || isInitializing) {
        console.log('⚠️  Reconnection already in progress, skipping...');
        return;
    }

    isReconnecting = true;
    isClientReady = false;
    currentAccountInfo.isReady = false;
    
    try {
        logConnectionState('RECONNECTING', `Reason: ${reason}, Attempt: ${reconnectAttempts + 1}`);
        
        // Уничтожаем текущий клиент если есть
        if (client) {
            try {
                await client.destroy();
                logConnectionState('CLIENT_DESTROYED');
            } catch (error) {
                console.log('⚠️  Error destroying client:', error);
            }
        }
        
        // Увеличиваем счетчик попыток
        reconnectAttempts++;
        
        if (reconnectAttempts > MAX_RECONNECT_ATTEMPTS) {
            logConnectionState('MAX_RECONNECT_ATTEMPTS_REACHED');
            io.emit('connection-failed', { 
                message: 'Максимальное количество попыток переподключения достигнуто' 
            });
            return;
        }
        
        // Ждем перед переподключением
        await new Promise(resolve => setTimeout(resolve, RECONNECT_DELAY));
        
        // Создаем новый клиент
        await initializeWhatsAppClient();
        
    } catch (error) {
        console.error('❌ Error during reconnection:', error);
        logConnectionState('RECONNECT_FAILED', error);
        
        // Попробуем снова через больший интервал
        setTimeout(() => {
            safeReconnect(`Previous attempt failed: ${error}`);
        }, RECONNECT_DELAY * 2);
        
    } finally {
        isReconnecting = false;
    }
};

// Функция проверки готовности клиента
const isClientHealthy = (): boolean => {
    return !!(client && client.info && client.info.wid && isClientReady);
};

// =============================================================================
// КОНЕЦ СТАБИЛИЗАЦИИ СОЕДИНЕНИЯ
// =============================================================================

// Инициализация Express
const app = express();
const httpServer = createServer(app);

// Инициализация Socket.IO
const io = new Server(httpServer, {
    cors: {
        origin: allowedOrigins,
        methods: ['GET', 'POST', 'PUT', 'DELETE', 'OPTIONS'],
        credentials: true,
        allowedHeaders: ['Content-Type', 'Authorization']
    },
    pingTimeout: 60000,
    transports: ['websocket', 'polling']
});

// Настройка CORS для Express
app.use(cors({
    origin: allowedOrigins,
    methods: ['GET', 'POST', 'PUT', 'DELETE', 'OPTIONS'],
    credentials: true,
    optionsSuccessStatus: 200
}));

// Настройка express-fileupload и JSON parsing
app.use(fileUpload());
app.use(express.json());

// Явная обработка OPTIONS запросов для CORS preflight
app.options('*', (req, res) => {
    console.log('OPTIONS request received for:', req.path);
    
    // Определяем origin из запроса
    const requestOrigin = req.get('origin');
    const allowedOrigin = allowedOrigins.includes(requestOrigin || '') ? requestOrigin : allowedOrigins[0];
    
    res.header('Access-Control-Allow-Origin', allowedOrigin);
    res.header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
    res.header('Access-Control-Allow-Headers', 'Content-Type, Authorization');
    res.header('Access-Control-Allow-Credentials', 'true');
    res.sendStatus(200);
});

// Инициализация клиента WhatsApp
let client: Client;

// Функция для получения длительности аудио
const getAudioDuration = async (buffer: Buffer, mimeType: string = 'audio/ogg'): Promise<number> => {
    try {
        console.log('Getting audio duration for mimetype:', mimeType);
        const { getAudioDurationInSeconds } = await import('get-audio-duration');
        
        // Определяем расширение файла на основе MIME-типа
        const extension = mimeType.split('/')[1] || 'ogg';
        const tempFile = path.join(os.tmpdir(), `temp_${Date.now()}.${extension}`);
        
        console.log('Saving temp file:', tempFile);
        await fs.writeFile(tempFile, buffer);
        
        const duration = await getAudioDurationInSeconds(tempFile);
        console.log('Audio duration:', duration);
        
        await fs.unlink(tempFile);
        return Math.round(duration);
    } catch (error: any) {
        console.error('Error getting audio duration:', error);
        return 0;
    }
};

// Получение списка чатов
app.get('/chats', async (req, res) => {
    try {
        console.log('GET /chats request received');
        const chats = await loadChats();
        console.log('Sending chats to client:', chats);
        // Отправляем чаты в том же формате, что ожидает фронтенд
        res.json(chats);
    } catch (error: any) {
        console.error('Error getting chats:', error);
        res.status(500).json({ 
            error: 'Failed to load chats',
            details: error?.message || 'Unknown error'
        });
    }
});

// Health check endpoint для мониторинга состояния сервера
// ВАЖНО: Всегда возвращает 200, чтобы фронт не ломался от CORS/503
app.get('/health', async (req, res) => {
    try {
        const healthData = {
            status: 'ok',
            timestamp: new Date().toISOString(),
            uptime: process.uptime(),
            server: {
                ready: true,
                version: '1.0.0',
                environment: process.env.NODE_ENV || 'development'
            },
            whatsapp: {
                ready: isClientHealthy(),
                connected: isClientReady,
                authenticated: currentAccountInfo.isReady,
                reconnectAttempts: reconnectAttempts,
                accountInfo: currentAccountInfo.isReady ? {
                    phoneNumber: currentAccountInfo.phoneNumber,
                    name: currentAccountInfo.name,
                    connectedAt: currentAccountInfo.connectedAt
                } : null
            },
            database: {
                connected: true, // Supabase всегда доступен
                status: 'operational'
            }
        };

        // Определяем общий статус здоровья (для информации, не для HTTP статуса)
        const overallHealthy = healthData.server.ready && 
                              healthData.database.connected;

        // ВСЕГДА возвращаем 200, чтобы фронт не ломался
        // Статус WhatsApp указываем в JSON, но не в HTTP коде
        res.status(200).json({
            ...healthData,
            status: overallHealthy ? 'ok' : 'degraded',
            message: overallHealthy ? 'All services operational' : 'Some services are not available (check whatsapp.ready)'
        });

        console.log(`🩺 Health check: ${overallHealthy ? 'HEALTHY' : 'DEGRADED'} - WhatsApp: ${healthData.whatsapp.ready ? 'READY' : 'NOT_READY'}`);
    } catch (error: any) {
        console.error('❌ Health check error:', error);
        res.status(500).json({
            status: 'error',
            timestamp: new Date().toISOString(),
            error: 'Health check failed',
            details: error?.message || 'Unknown error'
        });
    }
});

// API endpoint для очистки непрочитанных сообщений
app.post('/chats/:phoneNumber/clear-unread', async (req, res) => {
    try {
        const { phoneNumber } = req.params;
        await clearUnread(phoneNumber);
        res.json({ success: true });
    } catch (error: any) {
        console.error('Error clearing unread messages:', error);
        res.status(500).json({ 
            error: 'Failed to clear unread messages',
            details: error?.message || 'Unknown error'
        });
    }
});

// API endpoint для удаления чата
app.delete('/chats/:phoneNumber', async (req, res) => {
    try {
        const { phoneNumber } = req.params;
        console.log(`[DELETE ENDPOINT] Received delete request for chat: ${phoneNumber}`);
        
        // Проверяем готовность клиента
        if (!isClientHealthy()) {
            console.log(`[DELETE ENDPOINT] Client not ready, rejecting request`);
            return res.status(503).json({ 
                success: false,
                error: 'WhatsApp client is not ready. Please wait for connection to be established.',
                details: 'Client is not connected or authenticated',
                status: isClientReady ? 'connected' : 'disconnected'
            });
        }
        
        console.log(`[DELETE ENDPOINT] Request headers:`, req.headers);
        console.log(`[DELETE ENDPOINT] Request origin:`, req.get('origin'));
        
        const success = await deleteChat(phoneNumber);
        
        if (success) {
            console.log(`[DELETE ENDPOINT] Successfully deleted chat: ${phoneNumber}`);
            // Уведомляем всех подключенных клиентов об удалении чата
            io.emit('chat-deleted', { phoneNumber });
            
            res.json({ 
                success: true, 
                message: `Chat with ${phoneNumber} deleted successfully` 
            });
        } else {
            console.log(`[DELETE ENDPOINT] Chat not found: ${phoneNumber}`);
            res.status(404).json({ 
                success: false, 
                error: 'Chat not found' 
            });
        }
    } catch (error: any) {
        console.error('[DELETE ENDPOINT] Error deleting chat:', error);
        res.status(500).json({ 
            success: false,
            error: 'Failed to delete chat',
            details: error?.message || 'Unknown error'
        });
    }
});

// API endpoint для загрузки медиафайлов
app.post('/upload-media', async (req, res) => {
    try {
        if (!req.files || !req.files.file) {
            return res.status(400).json({ error: 'No file uploaded' });
        }

        const uploadedFile = req.files.file as fileUpload.UploadedFile;
        const buffer = Buffer.from(uploadedFile.data);
        const fileName = uploadedFile.name;
        const mediaType = uploadedFile.mimetype;

        console.log('Uploading file:', fileName, 'type:', mediaType);

        let duration = 0;
        if (mediaType.startsWith('audio/')) {
            duration = await getAudioDuration(buffer, mediaType);
        }

        // Загружаем файл в Supabase Storage
        const publicUrl = await uploadMediaToSupabase(buffer, fileName, mediaType);
        console.log('File uploaded successfully:', publicUrl);

        res.json({
            url: publicUrl,
            duration,
            isVoiceMessage: mediaType.startsWith('audio/') && fileName.includes('voice_message')
        });
    } catch (error: any) {
        console.error('Error uploading media:', error);
        res.status(500).json({ 
            error: 'Failed to upload media',
            details: error?.message || 'Unknown error'
        });
    }
});

// =============================================================================
// КОНТАКТЫ API ENDPOINTS
// =============================================================================

// Получить все контакты
app.get('/contacts', async (req, res) => {
    try {
        console.log('GET /contacts - получение всех контактов');
        const contacts = getAllContacts();
        
        const response: ContactsResponse = {
            success: true,
            contacts,
            message: `Загружено ${Object.keys(contacts).length} контактов`
        };
        
        console.log(`✅ Отправлено ${Object.keys(contacts).length} контактов`);
        res.json(response);
    } catch (error: any) {
        console.error('❌ Ошибка получения контактов:', error);
        
        const response: ContactsResponse = {
            success: false,
            error: 'Не удалось загрузить контакты',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Получить контакт по ID
app.get('/contacts/:contactId', async (req, res) => {
    try {
        const { contactId } = req.params;
        console.log(`GET /contacts/${contactId} - получение контакта`);
        
        const contact = getContactById(contactId);
        
        if (contact) {
            const response: ContactResponse = {
                success: true,
                contact,
                message: `Контакт ${contactId} найден`
            };
            
            console.log(`✅ Контакт ${contactId} найден:`, contact.customName);
            res.json(response);
        } else {
            const response: ContactResponse = {
                success: false,
                error: 'Контакт не найден'
            };
            
            console.log(`⚠️  Контакт ${contactId} не найден`);
            res.status(404).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка получения контакта:', error);
        
        const response: ContactResponse = {
            success: false,
            error: 'Не удалось получить контакт',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Создать новый контакт
app.post('/contacts', async (req, res) => {
    try {
        const { contactId, customName }: CreateContactRequest = req.body;
        
        console.log(`POST /contacts - создание контакта: ${contactId} -> "${customName}"`);
        
        // Валидация входных данных
        if (!contactId || !customName) {
            const response: ContactResponse = {
                success: false,
                error: 'Необходимо указать contactId и customName'
            };
            
            console.log('❌ Недостаточно данных для создания контакта');
            return res.status(400).json(response);
        }
        
        if (customName.trim().length === 0) {
            const response: ContactResponse = {
                success: false,
                error: 'Имя контакта не может быть пустым'
            };
            
            console.log('❌ Пустое имя контакта');
            return res.status(400).json(response);
        }
        
        const contact = createContact({ contactId, customName });
        
        if (contact) {
            const response: ContactResponse = {
                success: true,
                contact,
                message: `Контакт "${customName}" создан успешно`
            };
            
            console.log(`✅ Контакт создан: ${contactId} -> "${customName}"`);
            res.status(201).json(response);
        } else {
            const response: ContactResponse = {
                success: false,
                error: 'Контакт с таким ID уже существует'
            };
            
            console.log(`⚠️  Контакт ${contactId} уже существует`);
            res.status(409).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка создания контакта:', error);
        
        const response: ContactResponse = {
            success: false,
            error: 'Не удалось создать контакт',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Обновить контакт
app.put('/contacts/:contactId', async (req, res) => {
    try {
        const { contactId } = req.params;
        const { customName }: UpdateContactRequest = req.body;
        
        console.log(`PUT /contacts/${contactId} - обновление контакта: "${customName}"`);
        
        // Валидация входных данных
        if (!customName) {
            const response: ContactResponse = {
                success: false,
                error: 'Необходимо указать customName'
            };
            
            console.log('❌ Не указано новое имя контакта');
            return res.status(400).json(response);
        }
        
        if (customName.trim().length === 0) {
            const response: ContactResponse = {
                success: false,
                error: 'Имя контакта не может быть пустым'
            };
            
            console.log('❌ Пустое имя контакта');
            return res.status(400).json(response);
        }
        
        const contact = updateContact(contactId, { customName });
        
        if (contact) {
            const response: ContactResponse = {
                success: true,
                contact,
                message: `Контакт обновлен на "${customName}"`
            };
            
            console.log(`✅ Контакт обновлен: ${contactId} -> "${customName}"`);
            res.json(response);
        } else {
            const response: ContactResponse = {
                success: false,
                error: 'Контакт не найден'
            };
            
            console.log(`⚠️  Контакт ${contactId} не найден для обновления`);
            res.status(404).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка обновления контакта:', error);
        
        const response: ContactResponse = {
            success: false,
            error: 'Не удалось обновить контакт',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Удалить контакт
app.delete('/contacts/:contactId', async (req, res) => {
    try {
        const { contactId } = req.params;
        console.log(`DELETE /contacts/${contactId} - удаление контакта`);
        
        const success = deleteContact(contactId);
        
        if (success) {
            const response: ContactResponse = {
                success: true,
                message: `Контакт ${contactId} удален`
            };
            
            console.log(`✅ Контакт ${contactId} удален`);
            res.json(response);
        } else {
            const response: ContactResponse = {
                success: false,
                error: 'Контакт не найден'
            };
            
            console.log(`⚠️  Контакт ${contactId} не найден для удаления`);
            res.status(404).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка удаления контакта:', error);
        
        const response: ContactResponse = {
            success: false,
            error: 'Не удалось удалить контакт',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Поиск контактов
app.get('/contacts/search/:query', async (req, res) => {
    try {
        const { query } = req.params;
        console.log(`GET /contacts/search/${query} - поиск контактов`);
        
        const contacts = searchContacts(query);
        
        const response: ContactsResponse = {
            success: true,
            contacts,
            message: `Найдено ${Object.keys(contacts).length} контактов по запросу "${query}"`
        };
        
        console.log(`✅ Найдено ${Object.keys(contacts).length} контактов по запросу "${query}"`);
        res.json(response);
    } catch (error: any) {
        console.error('❌ Ошибка поиска контактов:', error);
        
        const response: ContactsResponse = {
            success: false,
            error: 'Не удалось выполнить поиск контактов',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// =============================================================================
// КОНЕЦ КОНТАКТЫ API ENDPOINTS
// =============================================================================

// =============================================================================
// АВАТАРКИ API ENDPOINTS
// =============================================================================

// Получить аватарку конкретного контакта
app.get('/avatar/:contactId', async (req, res) => {
    try {
        const { contactId } = req.params;
        console.log(`GET /avatar/${contactId} - получение аватарки контакта`);
        
        if (!isClientHealthy()) {
            return res.status(503).json({
                success: false,
                error: 'WhatsApp клиент не готов. Ожидайте подключения.',
                status: isClientReady ? 'connected' : 'disconnected'
            });
        }
        
        const avatarUrl = await getContactAvatar(client, contactId);
        
        res.json({
            success: true,
            contactId,
            avatarUrl,
            message: avatarUrl ? 'Аватарка найдена' : 'Аватарка не найдена'
        });
        
        console.log(`✅ Avatar ${avatarUrl ? 'found' : 'not found'} for ${contactId}`);
    } catch (error: any) {
        console.error('❌ Ошибка получения аватарки:', error);
        res.status(500).json({
            success: false,
            error: 'Не удалось получить аватарку',
            message: error?.message || 'Неизвестная ошибка'
        });
    }
});

// Получить аватарки для нескольких контактов
app.post('/avatars/batch', async (req, res) => {
    try {
        const { contactIds } = req.body;
        console.log(`POST /avatars/batch - получение аватарок для ${contactIds?.length || 0} контактов`);
        
        if (!Array.isArray(contactIds) || contactIds.length === 0) {
            return res.status(400).json({
                success: false,
                error: 'Необходимо передать массив contactIds'
            });
        }
        
        if (!isClientHealthy()) {
            return res.status(503).json({
                success: false,
                error: 'WhatsApp клиент не готов. Ожидайте подключения.',
                status: isClientReady ? 'connected' : 'disconnected'
            });
        }
        
        const avatars = await getMultipleContactAvatars(client, contactIds);
        
        res.json({
            success: true,
            avatars,
            message: `Получено аватарок: ${Object.keys(avatars).length}`
        });
        
        console.log(`✅ Fetched avatars for ${Object.keys(avatars).length} contacts`);
    } catch (error: any) {
        console.error('❌ Ошибка получения аватарок:', error);
        res.status(500).json({
            success: false,
            error: 'Не удалось получить аватарки',
            message: error?.message || 'Неизвестная ошибка'
        });
    }
});

// Обновить аватарки для всех чатов
app.post('/avatars/refresh', async (req, res) => {
    try {
        console.log('POST /avatars/refresh - обновление всех аватарок');
        
        if (!isClientHealthy()) {
            return res.status(503).json({
                success: false,
                error: 'WhatsApp клиент не готов. Ожидайте подключения.',
                status: isClientReady ? 'connected' : 'disconnected'
            });
        }
        
        const chats = await loadChats();
        const contactIds = Object.keys(chats);
        
        console.log(`Refreshing avatars for ${contactIds.length} chats`);
        
        const avatars = await getMultipleContactAvatars(client, contactIds);
        
        // Обновляем чаты с новыми аватарками
        let updatedCount = 0;
        for (const [phoneNumber, chat] of Object.entries(chats)) {
            const avatarUrl = avatars[phoneNumber];
            if (chat.avatarUrl !== avatarUrl) {
                chat.avatarUrl = avatarUrl || undefined;
                updatedCount++;
            }
        }
        
        // Сохраняем обновленные чаты
        await saveChats();
        
        res.json({
            success: true,
            message: `Обновлено аватарок: ${updatedCount} из ${contactIds.length}`,
            totalChats: contactIds.length,
            updatedChats: updatedCount
        });
        
        // Отправляем обновленные чаты всем клиентам
        io.emit('chats', chats);
        
        console.log(`✅ Updated ${updatedCount} avatars out of ${contactIds.length} chats`);
    } catch (error: any) {
        console.error('❌ Ошибка обновления аватарок:', error);
        res.status(500).json({
            success: false,
            error: 'Не удалось обновить аватарки',
            message: error?.message || 'Неизвестная ошибка'
        });
    }
});

// Очистить кэш аватарок
app.delete('/avatars/cache', async (req, res) => {
    try {
        console.log('DELETE /avatars/cache - очистка кэша аватарок');
        
        clearAvatarCache();
        
        res.json({
            success: true,
            message: 'Кэш аватарок очищен'
        });
        
        console.log('✅ Avatar cache cleared');
    } catch (error: any) {
        console.error('❌ Ошибка очистки кэша:', error);
        res.status(500).json({
            success: false,
            error: 'Не удалось очистить кэш',
            message: error?.message || 'Неизвестная ошибка'
        });
    }
});

// Получить статистику кэша аватарок
app.get('/avatars/cache/stats', async (req, res) => {
    try {
        console.log('GET /avatars/cache/stats - статистика кэша аватарок');
        
        const stats = getAvatarCacheStats();
        
        res.json({
            success: true,
            stats,
            message: 'Статистика кэша получена'
        });
        
        console.log('✅ Avatar cache stats retrieved:', stats);
    } catch (error: any) {
        console.error('❌ Ошибка получения статистики:', error);
        res.status(500).json({
            success: false,
            error: 'Не удалось получить статистику',
            message: error?.message || 'Неизвестная ошибка'
        });
    }
});

// =============================================================================
// КОНЕЦ АВАТАРКИ API ENDPOINTS
// =============================================================================

// =============================================================================
// READ STATUS API ENDPOINTS
// =============================================================================

// Обновить статус прочитанности чата
app.post('/read-status/update', async (req, res) => {
    try {
        const { chatId, messageId, timestamp, userId }: UpdateReadStatusRequest = req.body;
        
        console.log(`POST /read-status/update - обновление статуса для чата ${chatId}`);
        
        // Валидация входных данных
        if (!chatId || !messageId || !timestamp) {
            const response: ReadStatusResponse = {
                success: false,
                error: 'Необходимо указать chatId, messageId и timestamp'
            };
            return res.status(400).json(response);
        }
        
        const readStatus = updateReadStatus({ chatId, messageId, timestamp, userId });
        
        if (readStatus) {
            const response: ReadStatusResponse = {
                success: true,
                readStatus,
                message: `Статус прочитанности обновлен для чата ${chatId}`
            };
            
            console.log(`✅ Read status updated for chat ${chatId}: ${messageId}`);
            res.json(response);
        } else {
            const response: ReadStatusResponse = {
                success: false,
                error: 'Не удалось обновить статус прочитанности'
            };
            
            console.log(`❌ Failed to update read status for chat ${chatId}`);
            res.status(500).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка обновления статуса прочитанности:', error);
        
        const response: ReadStatusResponse = {
            success: false,
            error: 'Не удалось обновить статус прочитанности',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Пометить чат как полностью прочитанный
app.post('/read-status/mark-read/:chatId', async (req, res) => {
    try {
        const { chatId } = req.params;
        const { userId } = req.body;
        
        console.log(`POST /read-status/mark-read/${chatId} - пометить чат как прочитанный`);
        
        const readStatus = await markChatAsRead(chatId, userId);
        
        if (readStatus) {
            const response: ReadStatusResponse = {
                success: true,
                readStatus,
                message: `Чат ${chatId} помечен как прочитанный`
            };
            
            console.log(`✅ Chat ${chatId} marked as read`);
            res.json(response);
        } else {
            const response: ReadStatusResponse = {
                success: false,
                error: 'Не удалось пометить чат как прочитанный'
            };
            
            console.log(`❌ Failed to mark chat ${chatId} as read`);
            res.status(404).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка при пометке чата как прочитанного:', error);
        
        const response: ReadStatusResponse = {
            success: false,
            error: 'Не удалось пометить чат как прочитанный',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Получить статус прочитанности для чата
app.get('/read-status/:chatId', async (req, res) => {
    try {
        const { chatId } = req.params;
        const { userId } = req.query;
        
        console.log(`GET /read-status/${chatId} - получение статуса прочитанности`);
        
        const readStatus = getReadStatus(chatId, userId as string);
        
        if (readStatus) {
            const response: ReadStatusResponse = {
                success: true,
                readStatus,
                message: `Статус прочитанности найден для чата ${chatId}`
            };
            
            console.log(`✅ Read status found for chat ${chatId}`);
            res.json(response);
        } else {
            const response: ReadStatusResponse = {
                success: false,
                error: 'Статус прочитанности не найден'
            };
            
            console.log(`⚠️  No read status found for chat ${chatId}`);
            res.status(404).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка получения статуса прочитанности:', error);
        
        const response: ReadStatusResponse = {
            success: false,
            error: 'Не удалось получить статус прочитанности',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Получить все статусы прочитанности
app.get('/read-status', async (req, res) => {
    try {
        console.log('GET /read-status - получение всех статусов прочитанности');
        
        const readStatuses = getAllReadStatuses();
        
        const response: GetReadStatusResponse = {
            success: true,
            readStatuses,
            message: `Загружено ${Object.keys(readStatuses).length} статусов прочитанности`
        };
        
        console.log(`✅ Loaded ${Object.keys(readStatuses).length} read statuses`);
        res.json(response);
    } catch (error: any) {
        console.error('❌ Ошибка получения статусов прочитанности:', error);
        
        const response: GetReadStatusResponse = {
            success: false,
            error: 'Не удалось получить статусы прочитанности',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Получить количество непрочитанных сообщений для чата
app.get('/read-status/:chatId/unread-count', async (req, res) => {
    try {
        const { chatId } = req.params;
        const { userId } = req.query;
        
        console.log(`GET /read-status/${chatId}/unread-count - подсчет непрочитанных`);
        
        const unreadCount = await calculateUnreadCount(chatId, userId as string);
        
        const response: UnreadCountResponse = {
            success: true,
            chatId,
            unreadCount,
            message: `Непрочитанных сообщений в чате ${chatId}: ${unreadCount}`
        };
        
        console.log(`✅ Unread count for chat ${chatId}: ${unreadCount}`);
        res.json(response);
    } catch (error: any) {
        console.error('❌ Ошибка подсчета непрочитанных сообщений:', error);
        
        const response: UnreadCountResponse = {
            success: false,
            error: 'Не удалось подсчитать непрочитанные сообщения',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Получить количество непрочитанных сообщений для всех чатов
app.get('/read-status/unread-counts/all', async (req, res) => {
    try {
        const { userId } = req.query;
        
        console.log('GET /read-status/unread-counts/all - подсчет непрочитанных для всех чатов');
        
        const unreadCounts = await calculateUnreadCountsForAllChats(userId as string);
        
        const response = {
            success: true,
            unreadCounts,
            message: `Подсчитаны непрочитанные сообщения для ${Object.keys(unreadCounts).length} чатов`
        };
        
        console.log(`✅ Calculated unread counts for ${Object.keys(unreadCounts).length} chats`);
        res.json(response);
    } catch (error: any) {
        console.error('❌ Ошибка подсчета непрочитанных для всех чатов:', error);
        
        const response = {
            success: false,
            error: 'Не удалось подсчитать непрочитанные сообщения',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Получить новые сообщения после определенного времени
app.get('/read-status/:chatId/new-messages', async (req, res) => {
    try {
        const { chatId } = req.params;
        const { timestamp } = req.query;
        
        console.log(`GET /read-status/${chatId}/new-messages - получение новых сообщений`);
        
        if (!timestamp) {
            return res.status(400).json({
                success: false,
                error: 'Необходимо указать timestamp'
            });
        }
        
        const newMessages = await getNewMessagesAfterTimestamp(chatId, timestamp as string);
        
        const response: UnreadCountResponse = {
            success: true,
            chatId,
            lastMessages: newMessages,
            message: `Найдено ${newMessages.length} новых сообщений в чате ${chatId}`
        };
        
        console.log(`✅ Found ${newMessages.length} new messages in chat ${chatId}`);
        res.json(response);
    } catch (error: any) {
        console.error('❌ Ошибка получения новых сообщений:', error);
        
        const response: UnreadCountResponse = {
            success: false,
            error: 'Не удалось получить новые сообщения',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Удалить статус прочитанности для чата
app.delete('/read-status/:chatId', async (req, res) => {
    try {
        const { chatId } = req.params;
        const { userId } = req.body;
        
        console.log(`DELETE /read-status/${chatId} - удаление статуса прочитанности`);
        
        const success = deleteReadStatus(chatId, userId);
        
        if (success) {
            const response: ReadStatusResponse = {
                success: true,
                message: `Статус прочитанности удален для чата ${chatId}`
            };
            
            console.log(`✅ Read status deleted for chat ${chatId}`);
            res.json(response);
        } else {
            const response: ReadStatusResponse = {
                success: false,
                error: 'Не удалось удалить статус прочитанности'
            };
            
            console.log(`❌ Failed to delete read status for chat ${chatId}`);
            res.status(500).json(response);
        }
    } catch (error: any) {
        console.error('❌ Ошибка удаления статуса прочитанности:', error);
        
        const response: ReadStatusResponse = {
            success: false,
            error: 'Не удалось удалить статус прочитанности',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// Получить статистику статусов прочитанности
app.get('/read-status/stats', async (req, res) => {
    try {
        console.log('GET /read-status/stats - статистика статусов прочитанности');
        
        const stats = getReadStatusStats();
        
        const response = {
            success: true,
            stats,
            message: 'Статистика статусов прочитанности получена'
        };
        
        console.log('✅ Read status stats retrieved:', stats);
        res.json(response);
    } catch (error: any) {
        console.error('❌ Ошибка получения статистики:', error);
        
        const response = {
            success: false,
            error: 'Не удалось получить статистику',
            message: error?.message || 'Неизвестная ошибка'
        };
        
        res.status(500).json(response);
    }
});

// =============================================================================
// КОНЕЦ READ STATUS API ENDPOINTS
// =============================================================================

// Socket.IO обработчики
io.on('connection', (socket) => {
    console.log('[SOCKET] client connected:', socket.id);

    // STATE REPLAY: Отправляем текущее состояние WhatsApp при подключении
    console.log(`[SOCKET] replay sent state=${waState} hasQr=${!!lastQr} reason=${lastDisconnectReason || 'none'}`);
    socket.emit('wa:state', {
        state: waState,
        reason: lastDisconnectReason,
        timestamp: new Date().toISOString()
    });
    
    // Если есть QR код, отправляем его тоже
    if (waState === 'qr' && lastQr) {
        console.log('[SOCKET] replay sent QR code');
        socket.emit('wa:qr', lastQr);
    }

    // Отправляем текущие чаты при подключении
    (async () => {
        try {
            const chats = await loadChats();
            socket.emit('chats', chats);
        } catch (error: any) {
            console.error('Error sending chats:', error);
        }
    })();

    socket.on('send_message', async (data: {
        phoneNumber: string;
        message: string;
        mediaUrl?: string;
        fileName?: string;
        fileSize?: number;
        mediaType?: string;
        isVoiceMessage?: boolean;
        duration?: number;
    }) => {
        try {
            console.log('Received message data:', {
                ...data,
                mediaUrl: data.mediaUrl ? 'present' : 'absent',
                isVoiceMessage: data.isVoiceMessage,
                mediaType: data.mediaType
            });
            
            // Проверяем готовность клиента перед отправкой
            if (!isClientHealthy()) {
                console.log('❌ Cannot send message - client not ready');
                socket.emit('message-sent', {
                    success: false,
                    error: 'WhatsApp client is not ready. Please wait for connection to be established.',
                    details: 'Client is not connected or authenticated',
                    status: isClientReady ? 'connected' : 'disconnected',
                    originalData: data
                });
                return;
            }
            
            const { phoneNumber, message, mediaUrl, fileName, fileSize, mediaType, isVoiceMessage, duration } = data;
            
            // Форматируем номер телефона
            const formattedNumber = phoneNumber.includes('@c.us') 
                ? phoneNumber 
                : `${phoneNumber.replace(/[^\d]/g, '')}@c.us`;
            
            let whatsappMessage;
            
            // Если есть медиафайл, скачиваем его и отправляем через WhatsApp
            if (mediaUrl) {
                console.log('Downloading media from:', mediaUrl);
                try {
                    const response = await axios.get(mediaUrl, {
                        responseType: 'arraybuffer',
                        timeout: 30000 // 30 секунд таймаут
                    });
                    
                    const buffer = Buffer.from(response.data as ArrayBuffer);
                    const mimeType = mediaType || 'application/octet-stream';
                    
                    // Создаем объект MessageMedia
                    const media = new MessageMedia(
                        mimeType,
                        buffer.toString('base64'),
                        fileName
                    );
                    
                    console.log('Sending media message with options:', {
                        mimeType,
                        fileName,
                        isVoiceMessage,
                        hasCaption: !!message
                    });
                    
                    // Отправляем медиафайл через WhatsApp
                    whatsappMessage = await client.sendMessage(formattedNumber, media, {
                        caption: message, // Добавляем текст сообщения как подпись к медиафайлу
                        sendAudioAsVoice: isVoiceMessage // Отправляем аудио как голосовое сообщение
                    });
                    
                    console.log('Media message sent successfully:', whatsappMessage.id._serialized);
                } catch (error: any) {
                    console.error('Error downloading or sending media:', error);
                    throw new Error('Failed to send media message: ' + error.message);
                }
            } else {
                // Отправляем обычное текстовое сообщение
                whatsappMessage = await client.sendMessage(formattedNumber, message);
                console.log('Text message sent successfully:', whatsappMessage.id._serialized);
            }
            
            // Создаем объект сообщения для сохранения
            const chatMessage: ChatMessage = {
                id: whatsappMessage.id._serialized,
                body: message || '',
                from: whatsappMessage.from,
                to: formattedNumber,
                timestamp: new Date().toISOString(),
                fromMe: true,
                hasMedia: !!mediaUrl,
                mediaUrl,
                fileName,
                fileSize,
                mediaType,
                isVoiceMessage,
                duration
            };

            // Сохраняем сообщение и получаем обновленный чат
            const updatedChat = await addMessage(chatMessage);
            
            // Отправляем подтверждение отправки конкретному клиенту
            socket.emit('message-sent', {
                success: true,
                message: chatMessage,
                chat: updatedChat
            });
            
            // Оповещаем всех клиентов о новом сообщении и обновлении чата
            io.emit('whatsapp-message', chatMessage);
            io.emit('chat-updated', updatedChat);

        } catch (error: any) {
            console.error('❌ Error sending message:', error);
            
            // Отправляем ошибку конкретному клиенту
            socket.emit('message-sent', {
                success: false,
                error: error?.message || 'Unknown error',
                details: error?.stack || 'No additional details',
                originalData: data
            });
            
            // Проверяем, не связана ли ошибка с потерей соединения
            if (error?.message?.includes('Evaluation failed') || 
                error?.message?.includes('Session closed') ||
                error?.message?.includes('Target closed')) {
                console.log('🔌 Connection error detected, triggering reconnection');
                isClientReady = false;
                if (!isReconnecting) {
                    setTimeout(() => {
                        safeReconnect('Message sending failed due to connection error');
                    }, 1000);
                }
            }
        }
    });

    socket.on('disconnect', () => {
        console.log('[SOCKET] client disconnected:', socket.id);
    });
});

// Сохраняем чаты перед выходом
process.on('SIGINT', async () => {
    try {
        await saveChats();
        console.log('Chats saved successfully');
        process.exit(0);
    } catch (error: any) {
        console.error('Error saving chats:', error);
        process.exit(1);
    }
});

// Функция для перезапуска WhatsApp клиента
const restartWhatsAppClient = async (): Promise<void> => {
    if (isInitializing) {
        console.log('Client is already initializing, skipping restart');
        return;
    }

    try {
        isInitializing = true;
        console.log('Restarting WhatsApp client...');

        // Уничтожаем текущий клиент
        if (client) {
            await client.destroy();
            console.log('Current client destroyed');
        }

        // Создаем новый клиент
        client = new Client({
            authStrategy: new LocalAuth(),
            puppeteer: {
                args: ['--no-sandbox']
            }
        });

        // Перенастраиваем все обработчики событий
        setupEnhancedClientEventHandlers(client);
        
        // Инициализируем новый клиент
        await client.initialize();
        console.log('New WhatsApp client initialized');

    } catch (error) {
        console.error('Error restarting WhatsApp client:', error);
        io.emit('error', { message: 'Failed to restart WhatsApp client' });
    } finally {
        isInitializing = false;
    }
};

// Функция настройки обработчиков событий клиента
const setupClientEventHandlers = (clientInstance: Client): void => {
    clientInstance.on('qr', async (qr) => {
    try {
        qrCode = await qrcode.toDataURL(qr);
        io.emit('qr', qrCode);
        console.log('QR Code generated');
    } catch (error: any) {
        console.error('Error generating QR code:', error);
    }
});

    clientInstance.on('ready', async () => {
    console.log('Client is ready!');
        
        // Обновляем информацию о подключенном аккаунте
        await updateAccountInfo();
        
    io.emit('ready');
        
        // Отправляем информацию об аккаунте клиентам
        io.emit('account-connected', currentAccountInfo);
        
    qrCode = null;
});

    // Обработчик входящих сообщений
    clientInstance.on('message', async (msg) => {
    try {
            console.log('Received INCOMING message:', {
            type: msg.type,
            hasMedia: msg.hasMedia,
            body: msg.body,
            from: msg.from,
            to: msg.to,
                fromMe: msg.fromMe,
            isVoice: msg.type === 'ptt'
        });
        
            // Обрабатываем только входящие сообщения здесь
            if (!msg.fromMe) {
                // Проверяем, принадлежит ли сообщение текущему аккаунту
                if (currentAccountInfo.isReady && msg.to === currentAccountInfo.phoneNumber) {
                    await processIncomingMessage(msg);
                } else {
                    console.log('⚠️  Message not for current account, ignoring:', {
                        messageFor: msg.to,
                        currentAccount: currentAccountInfo.phoneNumber
                    });
                }
            }
            
        } catch (error: any) {
            console.error('Error processing incoming message:', error);
        }
    });

    // НОВЫЙ обработчик исходящих сообщений
    clientInstance.on('message_create', async (msg) => {
        try {
            console.log('Received OUTGOING message_create:', {
                type: msg.type,
                hasMedia: msg.hasMedia,
                body: msg.body,
                from: msg.from,
                to: msg.to,
                fromMe: msg.fromMe,
                isVoice: msg.type === 'ptt'
            });
            
            // Обрабатываем только исходящие сообщения здесь
            if (msg.fromMe) {
                // Проверяем, принадлежит ли сообщение текущему аккаунту
                if (currentAccountInfo.isReady && msg.from === currentAccountInfo.phoneNumber) {
                    await processOutgoingMessage(msg);
                } else {
                    console.log('⚠️  Outgoing message not from current account, ignoring:', {
                        messageFrom: msg.from,
                        currentAccount: currentAccountInfo.phoneNumber
                    });
                }
            }
            
        } catch (error: any) {
            console.error('Error processing outgoing message:', error);
        }
    });

    clientInstance.on('disconnected', (reason) => {
        console.log('Client was disconnected:', reason);
        
        // Сбрасываем информацию об аккаунте
        currentAccountInfo = { isReady: false };
        
        io.emit('disconnected', reason);
        io.emit('account-disconnected', { reason });
        
        qrCode = null;
    });

    clientInstance.on('auth_failure', (error) => {
        console.error('Authentication failed:', error);
        
        // Сбрасываем информацию об аккаунте
        currentAccountInfo = { isReady: false };
        
        io.emit('auth_failure', error);
        io.emit('account-auth-failed', { error });
    });
};

// Улучшенная функция настройки обработчиков событий с автоматическим переподключением
const setupEnhancedClientEventHandlers = (clientInstance: Client): void => {
    // QR код для аутентификации
    clientInstance.on('qr', async (qr) => {
        try {
            console.log('[WA] event=qr');
            logConnectionState('QR_GENERATED');
            qrCode = await qrcode.toDataURL(qr);
            // Обновляем состояние и отправляем QR
            updateWaState('qr', qrCode);
            // Также отправляем старое событие для обратной совместимости
            io.emit('qr', qrCode);
            reconnectAttempts = 0; // Сбрасываем счетчик при новом QR
            // Сбрасываем флаг watchdog reset при новом QR
            hasWatchdogResetAttempted = false;
        } catch (error: any) {
            console.error('[WA] event=qr ERROR:', error);
            console.error('[WA] Error stack:', error?.stack);
            logConnectionState('QR_ERROR', error);
        }
    });

    // Успешное подключение
    clientInstance.on('ready', async () => {
        console.log('[WA] event=ready');
        console.log('[WA] ready: current state before update=', waState);
        console.log('[WA] ready: isClientReady before update=', isClientReady);
        
        isClientReady = true;
        reconnectAttempts = 0; // Сбрасываем счетчик успешных подключений
        
        logConnectionState('READY');
        
        try {
            // Диагностика: проверяем client.info перед updateAccountInfo
            try {
                const info = clientInstance.info;
                console.log('[WA] ready: client.info exists?', !!info);
                if (info) {
                    console.log('[WA] ready: client.info.wid?', !!info.wid);
                    if (info.wid) {
                        console.log('[WA] ready: client.info.wid._serialized?', info.wid._serialized);
                    }
                }
            } catch (error: any) {
                console.error('[WA] ready: ERROR accessing client.info:', error?.message || error);
                console.error('[WA] Error stack:', error?.stack);
            }
            
            // Обновляем информацию о подключенном аккаунте
            console.log('[WA] ready: calling updateAccountInfo()...');
            await updateAccountInfo();
            console.log('[WA] ready: updateAccountInfo() completed');
            
            // Обновляем состояние на ready и очищаем QR
            updateWaState('ready', null);
            
            // Также отправляем старое событие для обратной совместимости
            io.emit('ready');
            io.emit('account-connected', currentAccountInfo);
            
            qrCode = null;
            
            logConnectionState('ACCOUNT_CONNECTED', {
                phoneNumber: currentAccountInfo.phoneNumber,
                name: currentAccountInfo.name
            });
            
        } catch (error: any) {
            console.error('[WA] event=ready ERROR updating account info:', error);
            console.error('[WA] Error stack:', error?.stack);
            // Даже при ошибке обновляем состояние на ready, чтобы фронт мог работать
            updateWaState('ready', null);
            io.emit('ready');
        }
    });

    // Аутентификация прошла успешно
    clientInstance.on('authenticated', async () => {
        console.log('[WA] event=authenticated');
        logConnectionState('AUTHENTICATED');
        
        // Диагностика: проверяем состояние клиента сразу после authenticated
        try {
            const clientInfo = clientInstance.info;
            console.log('[WA] authenticated: client.info exists?', !!clientInfo);
            if (clientInfo) {
                console.log('[WA] authenticated: client.info.wid?', !!clientInfo.wid);
            }
        } catch (error: any) {
            console.log('[WA] authenticated: error checking client.info:', error?.message || error);
        }

        // Настраиваем глубокую диагностику страницы (консоль/ошибки/сеть)
        try {
            const anyClient = clientInstance as any;
            const page = anyClient.pupPage || (anyClient.getPage ? await anyClient.getPage() : null);
            if (page && !(page as any).__waDiagnosticsAttached) {
                (page as any).__waDiagnosticsAttached = true;
                
                // Устанавливаем нормальный User-Agent для анти-детек
                try {
                    const userAgent = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';
                    await page.setUserAgent(userAgent);
                    console.log('[WA_PAGE] User-Agent set for anti-detection');
                } catch (uaErr: any) {
                    console.log('[WA_PAGE] error setting User-Agent:', uaErr?.message || uaErr);
                }
                
                page.on('console', (msg: any) => {
                    try {
                        const type = msg.type ? msg.type() : 'log';
                        console.log('[WA_PAGE][console]', type, msg.text ? msg.text() : msg);
                    } catch {
                        console.log('[WA_PAGE][console]', msg?.text?.() ?? msg);
                    }
                });
                page.on('pageerror', (err: any) => {
                    console.log('[WA_PAGE][pageerror]', err?.message || err);
                });
                page.on('requestfailed', (req: any) => {
                    try {
                        const url = req?.url?.() || 'unknown';
                        const resourceType = req?.resourceType?.() || 'unknown';
                        const failure = req?.failure?.();
                        const errorText = failure?.errorText || 'unknown';
                        const method = req?.method?.() || 'GET';
                        
                        // Проверяем, не блокируется ли запрос клиентом (AdBlock/антивирус)
                        const requestBlocked = errorText.includes('ERR_BLOCKED_BY_CLIENT') || 
                                              errorText.includes('ERR_ABORTED') ||
                                              errorText.includes('net::ERR_BLOCKED_BY_CLIENT') ||
                                              errorText.includes('blocked');
                        
                        // Разделяем критичные и некритичные домены
                        const isCriticalDomain = url.includes('web.whatsapp.com') || 
                                                url.includes('g.whatsapp.net') ||
                                                url.includes('v.whatsapp.net');
                        const isMediaCDN = url.includes('media-') && url.includes('cdn.whatsapp.net');
                        const isWhatsAppDomain = url.includes('whatsapp.com') || 
                                                url.includes('whatsapp.net');
                        
                        // DELETE запросы к media CDN часто нормальны (очистка кэша)
                        const isDeleteToMedia = method === 'DELETE' && isMediaCDN;
                        
                        console.log(`[WA_PAGE][requestfailed] ${method} ${resourceType} ${url}`);
                        console.log(`[WA_PAGE][requestfailed] errorText=${errorText}, requestBlocked=${requestBlocked}, isCritical=${isCriticalDomain}, isMedia=${isMediaCDN}, isDelete=${isDeleteToMedia}`);
                        
                        // Игнорируем DELETE к media CDN - это нормальная операция очистки кэша
                        if (isDeleteToMedia) {
                            console.log(`[WA_PAGE][requestfailed] Ignoring DELETE to media CDN (normal cache cleanup): ${url}`);
                            return;
                        }
                        
                        // Детекция блокировки: только критичные домены или множественные блокировки media CDN
                        if (requestBlocked && isWhatsAppDomain && !isBlocked) {
                            if (isCriticalDomain) {
                                criticalBlockedCount++;
                                console.error(`[WA_PAGE][requestfailed] ⚠️ CRITICAL domain blocked (count: ${criticalBlockedCount}): ${url}`);
                                
                                // Блокируем только после нескольких критичных блокировок
                                if (criticalBlockedCount >= CRITICAL_BLOCK_THRESHOLD) {
                                    isBlocked = true;
                                    blockedReason = `Critical domain blocked: ${errorText} (${method} ${resourceType})`;
                                    blockedUrl = url;
                                    console.error('[WA_PAGE][requestfailed] ⚠️ CRITICAL: WhatsApp critical domain request blocked!');
                                    console.error(`[WA_PAGE][requestfailed] ⚠️ Blocked URL: ${url}`);
                                    console.error(`[WA_PAGE][requestfailed] ⚠️ Blocked reason: ${errorText}`);
                                    console.error('[WA_PAGE][requestfailed] ⚠️ This will prevent READY state. Check AdBlock/antivirus web shield.');
                                    
                                    stopReadyWatchdog();
                                    updateWaState('blocked', null);
                                    
                                    io.emit('wa:state', {
                                        state: 'blocked',
                                        reason: blockedReason,
                                        blockedUrl: blockedUrl,
                                        failureText: errorText,
                                        method: method,
                                        resourceType: resourceType,
                                        timestamp: new Date().toISOString()
                                    });
                                    
                                    console.log('[WA] BLOCKED by client/adblock/webshield. No auto-reset. User action required.');
                                }
                            } else if (isMediaCDN) {
                                mediaBlockedCount++;
                                console.warn(`[WA_PAGE][requestfailed] ⚠️ Media CDN blocked (count: ${mediaBlockedCount}): ${url}`);
                                
                                // Блокируем только если media CDN блокируется массово (не критично для READY)
                                if (mediaBlockedCount >= MEDIA_BLOCK_IGNORE_THRESHOLD * 2) {
                                    console.error('[WA_PAGE][requestfailed] ⚠️ WARNING: Multiple media CDN blocks detected, but not blocking session (media is not critical for READY)');
                                    // НЕ устанавливаем isBlocked = true для media CDN
                                    // Media CDN не критичен для достижения READY состояния
                                }
                            }
                        }
                    } catch (e: any) {
                        console.log('[WA_PAGE][requestfailed] error logging:', e?.message || e);
                    }
                });
                page.on('response', (res: any) => {
                    try {
                        const status = res.status ? res.status() : 0;
                        const url = res.url ? res.url() : '';
                        if (status >= 400) {
                            console.log('[WA_PAGE][response]', status, url);
                            
                            // Разделяем критичные и некритичные домены
                            const isCriticalDomain = url.includes('web.whatsapp.com') || 
                                                    url.includes('g.whatsapp.net') ||
                                                    url.includes('v.whatsapp.net');
                            const isMediaCDN = url.includes('media-') && url.includes('cdn.whatsapp.net');
                            const isWhatsAppDomain = url.includes('whatsapp.com') || 
                                                    url.includes('whatsapp.net');
                            
                            // Игнорируем 404/403 на media CDN - это может быть нормально
                            if ((status === 404 || status === 403) && isMediaCDN) {
                                console.log(`[WA_PAGE][response] Ignoring ${status} on media CDN (may be normal): ${url}`);
                                return;
                            }
                            
                            // Статус 0 или критичные ошибки только на критичных доменах
                            if ((status === 0 || status >= 400) && isWhatsAppDomain && !isBlocked) {
                                if (isCriticalDomain) {
                                    criticalBlockedCount++;
                                    console.error(`[WA_PAGE][response] ⚠️ CRITICAL domain error (count: ${criticalBlockedCount}): HTTP ${status} ${url}`);
                                    
                                    if (criticalBlockedCount >= CRITICAL_BLOCK_THRESHOLD) {
                                        isBlocked = true;
                                        blockedReason = `HTTP ${status}`;
                                        blockedUrl = url;
                                        console.error('[WA_PAGE][response] ⚠️ CRITICAL: WhatsApp critical domain response error!');
                                        console.error(`[WA_PAGE][response] ⚠️ Blocked URL: ${url}`);
                                        console.error(`[WA_PAGE][response] ⚠️ Status: ${status}`);
                                        
                                        stopReadyWatchdog();
                                        updateWaState('blocked', null);
                                        
                                        io.emit('wa:state', {
                                            state: 'blocked',
                                            reason: blockedReason,
                                            blockedUrl: blockedUrl,
                                            failureText: `HTTP ${status}`,
                                            method: 'GET',
                                            resourceType: 'document',
                                            timestamp: new Date().toISOString()
                                        });
                                        
                                        console.log('[WA] BLOCKED by client/adblock/webshield. No auto-reset. User action required.');
                                    }
                                } else if (isMediaCDN) {
                                    // Media CDN ошибки не критичны - логируем, но не блокируем
                                    console.warn(`[WA_PAGE][response] Media CDN error (non-critical): HTTP ${status} ${url}`);
                                }
                            }
                        }
                    } catch {
                        // ignore
                    }
                });
                console.log('[WA_PAGE] diagnostics attached');
            } else {
                console.log('[WA_PAGE] no pupPage available on authenticated');
            }
        } catch (pageErr: any) {
            console.log('[WA_PAGE] error attaching diagnostics:', pageErr?.message || pageErr);
        }
        
        updateWaState('authenticated', null); // Очищаем QR при аутентификации
        // Запускаем watchdog таймер для отслеживания ready timeout
        startReadyWatchdog();
        
        // Дополнительная диагностика: периодическая проверка состояния каждые 2-3 секунды
        let diagnosticInterval: NodeJS.Timeout | null = null;
        let diagnosticCount = 0;
        const maxDiagnostics = 30; // 30 проверок * 3 сек = 90 секунд максимум
        
        diagnosticInterval = setInterval(async () => {
            diagnosticCount++;
            console.log(`[WA] authenticated diagnostic check #${diagnosticCount}:`);
            console.log(`[WA]   - current state: ${waState}`);
            console.log(`[WA]   - isClientReady: ${isClientReady}`);
            console.log(`[WA]   - client exists: ${!!clientInstance}`);
            
            try {
                const info = clientInstance.info;
                console.log(`[WA]   - client.info exists: ${!!info}`);
                if (info) {
                    console.log(`[WA]   - client.info.wid exists: ${!!info.wid}`);
                    console.log(`[WA]   - client.info.wid: ${info.wid?._serialized || 'N/A'}`);
                }
            } catch (error: any) {
                console.log(`[WA]   - error accessing client.info: ${error?.message || error}`);
            }

            // Диагностика DOM/URL и ключевых объектов если есть страница
            try {
                const anyClient = clientInstance as any;
                const page = anyClient.pupPage;
                if (page) {
                    // Проверяем что page не закрыт
                    try {
                        if (page.isClosed()) {
                            if (diagnosticInterval) {
                                clearInterval(diagnosticInterval);
                                diagnosticInterval = null;
                            }
                            return;
                        }
                    } catch (checkErr: any) {
                        if (checkErr?.message?.includes('Session closed') || 
                            checkErr?.message?.includes('Protocol error') ||
                            checkErr?.message?.includes('Target closed')) {
                            if (diagnosticInterval) {
                                clearInterval(diagnosticInterval);
                                diagnosticInterval = null;
                            }
                            return;
                        }
                    }
                    
                    const pageInfo = await page.evaluate(() => {
                        const hasStore = typeof (window as any).Store !== 'undefined';
                        const hasWWebJS = typeof (window as any).WWebJS !== 'undefined';
                        const hasWebpackChunk = typeof (window as any).webpackChunkwhatsapp_web_client !== 'undefined';
                        return {
                            url: window.location.href,
                            readyState: document.readyState,
                            title: document.title,
                            hasStore,
                            hasWWebJS,
                            hasWebpackChunk,
                            userAgent: navigator.userAgent,
                        };
                    });
                    console.log('[WA_PAGE][diagnostic]', pageInfo);
                    
                    // Попытка аккуратно достать "инфо" через page.evaluate
                    try {
                        // Проверяем перед evaluate
                        if (!page.isClosed()) {
                            const clientInfoFromPage = await page.evaluate(() => {
                            try {
                                const Store = (window as any).Store;
                                if (Store && Store.Conn) {
                                    const conn = Store.Conn;
                                    if (conn && conn.wid) {
                                        return {
                                            wid: conn.wid.user + '@' + conn.wid.server,
                                            platform: conn.platform,
                                        };
                                    }
                                }
                            } catch (e) {
                                return null;
                            }
                            return null;
                        });
                            if (clientInfoFromPage) {
                                console.log('[WA_PAGE][diagnostic] clientInfo from page:', clientInfoFromPage);
                            }
                        }
                    } catch (e: any) {
                        if (e?.message?.includes('Session closed') || 
                            e?.message?.includes('Protocol error') ||
                            e?.message?.includes('Target closed')) {
                            // Игнорируем ошибки закрытой сессии
                        } else {
                            console.log('[WA_PAGE][diagnostic] error getting clientInfo:', e?.message || e);
                        }
                    }
                } else {
                    console.log('[WA_PAGE][diagnostic] no page available');
                }
            } catch (e: any) {
                console.log('[WA_PAGE][diagnostic] error:', e?.message || e);
            }
            
            // Проверяем, не произошло ли отключение без события
            if (waState !== 'authenticated' || diagnosticCount >= maxDiagnostics) {
                if (diagnosticInterval) {
                    clearInterval(diagnosticInterval);
                    diagnosticInterval = null;
                }
            }
        }, 3000); // Каждые 3 секунды
    });

    // Начало загрузки
    clientInstance.on('loading_screen', (percent: number | string, message: string) => {
        const percentNum = typeof percent === 'string' ? parseFloat(percent) : percent;
        console.log(`[WA] event=loading_screen percent=${percent} message=${message || ''}`);
        console.log(`[WA] loading_screen: current state=${waState}, isClientReady=${isClientReady}`);
        logConnectionState('LOADING', `${percent}% - ${message}`);
        
        // Если loading_screen 100% после authenticated, это может быть признаком проблемы
        if (percentNum === 100 && waState === 'authenticated') {
            console.log('[WA] WARNING: loading_screen 100% but state is still authenticated (not ready)');
        }
    });

    // Изменение состояния соединения
    clientInstance.on('change_state', (state) => {
        console.log(`[WA] event=change_state state=${state}`);
        console.log(`[WA] change_state: current waState=${waState}, isClientReady=${isClientReady}`);
        logConnectionState('STATE_CHANGED', state);
        
        // Если change_state происходит после authenticated, логируем для диагностики
        if (waState === 'authenticated') {
            console.log(`[WA] change_state during authenticated: ${state} - this might indicate why ready is delayed`);
        }
    });

    // Отключение - обрабатываем LOGOUT отдельно
    clientInstance.on('disconnected', async (reason) => {
        const reasonStr = String(reason || '');
        const isLogout = reasonStr.includes('LOGOUT') || 
                        reasonStr === 'LOGOUT' || 
                        reasonStr === 'DISCONNECTED_LOGOUT' ||
                        reasonStr.includes('CONFLICT');
        
        console.log(`[WA] event=disconnected reason=${reasonStr} isLogout=${isLogout}`);
        console.log(`[WA] disconnected full reason:`, reason);
        
        isClientReady = false;
        currentAccountInfo.isReady = false;
        
        logConnectionState('DISCONNECTED', reason);
        
        // Обновляем состояние на disconnected с причиной
        updateWaState('disconnected', null, reasonStr);
        
        // Также отправляем старое событие для обратной совместимости
        io.emit('disconnected', reason);
        io.emit('account-disconnected', { reason });
        
        qrCode = null;
        
        // Если это LOGOUT или CONFLICT - выполняем полный reset
        if (isLogout) {
            await resetFlow(reasonStr);
        } else {
            // Для обычного disconnected - просто переинициализируем без удаления папок
            if (!isReconnecting && !isReinitializing) {
                isReinitializing = true;
                console.log('[WA] Starting automatic re-init after disconnected');
                
                try {
                    // Уничтожаем клиент
                    if (client) {
                        try {
                            await client.destroy();
                            console.log('[WA] destroy complete');
                            await delay(2000); // Задержка для освобождения lock (Windows EBUSY fix)
                        } catch (error: any) {
                            console.log('[WA] Warning: Error destroying client:', error?.message || error);
                            console.log('[WA] Error stack:', error?.stack);
                            await delay(2000); // Задержка даже при ошибке
                        }
                    }
                    
                    // Переинициализируем клиент
                    await initializeWhatsAppClient();
                    console.log('[WA] Client re-initialized after disconnected');
                } catch (error: any) {
                    console.error('[WA] Error during automatic re-init:', error);
                    console.error('[WA] Error stack:', error?.stack);
                    // Если автоматический re-init не удался, используем safeReconnect
                    setTimeout(() => {
                        safeReconnect(`Disconnected: ${reason}`);
                    }, 3000);
                } finally {
                    isReinitializing = false;
                }
            }
        }
    });

    // Ошибка аутентификации - требуется новый QR
    clientInstance.on('auth_failure', async (error) => {
        console.log('[WA] event=auth_failure');
        console.log('[WA] auth_failure error:', error);
        if (error && typeof error === 'object' && 'stack' in error) {
            console.log('[WA] Error stack:', (error as any).stack);
        }
        
        isClientReady = false;
        currentAccountInfo.isReady = false;
        
        logConnectionState('AUTH_FAILURE', error);
        
        // Обновляем состояние на disconnected (требуется новый QR)
        updateWaState('disconnected', null);
        
        // Также отправляем старое событие для обратной совместимости
        io.emit('auth_failure', error);
        io.emit('account-auth-failed', { error });
        
        // При ошибке аутентификации нужно очистить данные и запросить новый QR
        if (!isReconnecting && !isReinitializing) {
            setTimeout(() => {
                safeReconnect(`Auth failure: ${error}`);
            }, 2000);
        }
    });

    // Обработчик входящих сообщений
    clientInstance.on('message', async (msg) => {
        if (!isClientReady) {
            console.log('⚠️  Received message but client not ready, ignoring');
            return;
        }

        try {
            if (!msg.fromMe) {
                // Проверяем принадлежность к текущему аккаунту
                if (currentAccountInfo.isReady && msg.to === currentAccountInfo.phoneNumber) {
                    await processIncomingMessage(msg);
                } else {
                    console.log('⚠️  Message not for current account, ignoring:', {
                        messageFor: msg.to,
                        currentAccount: currentAccountInfo.phoneNumber
                    });
                }
            }
        } catch (error: any) {
            console.error('❌ Error processing incoming message:', error);
        }
    });

    // Обработчик исходящих сообщений
    clientInstance.on('message_create', async (msg) => {
        if (!isClientReady) {
            console.log('⚠️  Received message_create but client not ready, ignoring');
            return;
        }

        try {
            if (msg.fromMe) {
                // Проверяем принадлежность к текущему аккаунту
                if (currentAccountInfo.isReady && msg.from === currentAccountInfo.phoneNumber) {
                    await processOutgoingMessage(msg);
                } else {
                    console.log('⚠️  Outgoing message not from current account, ignoring:', {
                        messageFrom: msg.from,
                        currentAccount: currentAccountInfo.phoneNumber
                    });
                }
            }
        } catch (error: any) {
            console.error('❌ Error processing outgoing message:', error);
        }
    });

    // Обработка ошибок соединения
    clientInstance.on('error', (error) => {
        console.error('[WA] event=error');
        console.error('[WA] error:', error);
        if (error && typeof error === 'object' && 'stack' in error) {
            console.error('[WA] Error stack:', (error as any).stack);
        }
        logConnectionState('CLIENT_ERROR', error);
    });

    // Обработчик изменения статуса сообщений (ACK)
    clientInstance.on('message_ack', async (msg, ack) => {
        try {
            console.log('📊 Message ACK received:', {
                messageId: msg.id._serialized,
                ack: ack,
                from: msg.from,
                to: msg.to,
                fromMe: msg.fromMe
            });

            // Обновляем статус только для исходящих сообщений
            if (msg.fromMe && currentAccountInfo.isReady) {
                // Уведомляем клиентов об изменении статуса
                io.emit('message-ack-updated', {
                    messageId: msg.id._serialized,
                    ack: ack,
                    chatId: msg.to,
                    timestamp: new Date().toISOString()
                });
            }
        } catch (error: any) {
            console.error('❌ Error processing message ACK:', error);
        }
    });
};

// Функция обработки входящих сообщений
const processIncomingMessage = async (msg: Message) => {
        let mediaUrl = '';
        let mediaType = '';
        let fileName = '';
        let fileSize = 0;
    let isVoiceMessage = msg.type === 'ptt';
        let duration = 0;

        if (msg.hasMedia) {
        console.log('Processing incoming media, type:', msg.type);
            const media = await msg.downloadMedia();
            if (media) {
            const extension = isVoiceMessage ? 'ogg' : media.mimetype.split('/')[1];
            const defaultFileName = `${msg.type}_${Date.now()}.${extension}`;
            const mimeType = isVoiceMessage ? 'audio/ogg' : media.mimetype;
            
            try {
                mediaUrl = await uploadMediaToSupabase(
                    Buffer.from(media.data, 'base64'),
                    media.filename || defaultFileName,
                    mimeType
                );
                
                mediaType = mimeType;
                fileName = media.filename || defaultFileName;
                fileSize = Buffer.from(media.data, 'base64').length;
                
                if (isVoiceMessage) {
                    try {
                        const buffer = Buffer.from(media.data, 'base64');
                        duration = await getAudioDuration(buffer, mimeType);
                    } catch (error) {
                        console.error('Error getting audio duration:', error);
                        duration = 0;
                    }
                }
            } catch (error) {
                console.error('Error processing media:', error);
                throw error;
            }
        }
    }

    const message: ChatMessage = {
        id: msg.id.id,
        body: msg.body,
        from: msg.from,
        to: msg.to,
        timestamp: new Date().toISOString(),
        fromMe: false,
        hasMedia: msg.hasMedia,
        mediaUrl,
        mediaType,
        fileName,
        fileSize,
        isVoiceMessage,
        duration,
        ack: 3 // Входящие сообщения считаются прочитанными
    };

    console.log('Saving INCOMING message:', {
        id: message.id,
        from: message.from,
        body: message.body,
        fromMe: message.fromMe
    });

    const chat = await addMessage(message);
    
    io.emit('whatsapp-message', message);
    io.emit('chat-updated', chat);
};

// Функция обработки исходящих сообщений  
const processOutgoingMessage = async (msg: Message) => {
    let mediaUrl = '';
    let mediaType = '';
    let fileName = '';
    let fileSize = 0;
    let isVoiceMessage = msg.type === 'ptt';
    let duration = 0;

    if (msg.hasMedia) {
        console.log('Processing outgoing media, type:', msg.type);
        const media = await msg.downloadMedia();
        if (media) {
                const extension = isVoiceMessage ? 'ogg' : media.mimetype.split('/')[1];
                const defaultFileName = `${msg.type}_${Date.now()}.${extension}`;
                const mimeType = isVoiceMessage ? 'audio/ogg' : media.mimetype;
                
                try {
                    mediaUrl = await uploadMediaToSupabase(
                        Buffer.from(media.data, 'base64'),
                        media.filename || defaultFileName,
                        mimeType
                    );
                    
                    mediaType = mimeType;
                    fileName = media.filename || defaultFileName;
                    fileSize = Buffer.from(media.data, 'base64').length;
                    
                    if (isVoiceMessage) {
                        try {
                            const buffer = Buffer.from(media.data, 'base64');
                            duration = await getAudioDuration(buffer, mimeType);
                        } catch (error) {
                            console.error('Error getting audio duration:', error);
                            duration = 0;
                        }
                    }
                } catch (error) {
                    console.error('Error processing media:', error);
                    throw error;
                }
            }
        }

        const message: ChatMessage = {
            id: msg.id.id,
            body: msg.body,
            from: msg.from,
            to: msg.to,
            timestamp: new Date().toISOString(),
        fromMe: true,
            hasMedia: msg.hasMedia,
            mediaUrl,
            mediaType,
            fileName,
            fileSize,
            isVoiceMessage,
        duration,
        ack: msg.ack || 0 // Берем статус из whatsapp-web.js, по умолчанию 0 (отправлено)
        };

    console.log('Saving OUTGOING message:', {
            id: message.id,
        from: message.from,
        to: message.to,
        body: message.body,
        fromMe: message.fromMe
    });

        const chat = await addMessage(message);
        
    // Отправляем исходящее сообщение всем клиентам
        io.emit('whatsapp-message', message);
        io.emit('chat-updated', chat);
};

// Добавляем новый API endpoint для logout
app.post('/whatsapp/logout', async (req, res) => {
    try {
        console.log('Logout request received');
        
        // Выполняем logout
        if (client) {
            await client.logout();
            console.log('WhatsApp client logged out');
        }

        // Уведомляем клиентов о начале перезапуска
        io.emit('restarting', { message: 'Перезапуск WhatsApp клиента...' });

        // Перезапускаем клиент через небольшую задержку
        setTimeout(async () => {
            await restartWhatsAppClient();
        }, 2000);

        res.json({ 
            success: true, 
            message: 'WhatsApp client logged out and restarting' 
        });
        
    } catch (error: any) {
        console.error('Error during logout:', error);
        res.status(500).json({ 
            error: 'Failed to logout WhatsApp client',
            details: error?.message || 'Unknown error'
        });
    }
});

// Добавляем endpoint для получения статуса клиента
// ВАЖНО: Всегда возвращает 200, статус указывается в JSON
app.get('/whatsapp/status', (req, res) => {
    try {
        const isReady = client && client.info && isClientReady;
        const hasQr = !!(lastQr || qrCode);
        const currentQr = lastQr || qrCode || null;
        
        // Определяем статус на основе состояния
        let status: string = 'disconnected';
        if (isReady) {
            status = 'ready';
        } else if (hasQr) {
            status = 'qr';
        } else if (waState === 'authenticated') {
            status = 'authenticated';
        } else if (waState === 'idle') {
            status = 'idle';
        } else if (waState === 'blocked') {
            status = 'blocked';
        } else {
            status = waState || 'disconnected';
        }
        
        // ВСЕГДА возвращаем 200, даже если клиент не готов
        res.status(200).json({
            success: true,
            status: status,
            isReady,
            hasQr,
            qrCode: currentQr, // Включаем QR код если есть
            currentState: waState,
            message: isReady 
                ? 'WhatsApp client is ready' 
                : hasQr 
                    ? 'QR code available, waiting for scan'
                    : status === 'authenticated'
                        ? 'Authenticated, waiting for ready'
                        : 'WhatsApp client not ready',
            accountInfo: isReady ? currentAccountInfo : null
        });
    } catch (error: any) {
        console.error('❌ Error getting WhatsApp status:', error);
        // Даже при ошибке возвращаем 200 с информацией об ошибке
        res.status(200).json({ 
            success: false,
            status: 'error',
            error: 'Failed to get WhatsApp status',
            message: error?.message || 'Unknown error',
            hasQr: false,
            isReady: false
        });
    }
});

// Добавляем endpoint /api/whatsapp/status для единообразия с другими API endpoints
app.get('/api/whatsapp/status', (req, res) => {
    try {
        const isReady = client && client.info && isClientReady;
        const hasQr = !!(lastQr || qrCode);
        const currentQr = lastQr || qrCode || null;
        
        // Определяем статус на основе состояния
        let status: string = 'disconnected';
        if (isReady) {
            status = 'ready';
        } else if (hasQr) {
            status = 'qr';
        } else if (waState === 'authenticated') {
            status = 'authenticated';
        } else if (waState === 'idle') {
            status = 'idle';
        } else if (waState === 'blocked') {
            status = 'blocked';
        } else {
            status = waState || 'disconnected';
        }
        
        // ВСЕГДА возвращаем 200, даже если клиент не готов
        res.status(200).json({
            success: true,
            status: status,
            isReady,
            hasQr,
            qrCode: currentQr, // Включаем QR код если есть
            currentState: waState,
            message: isReady 
                ? 'WhatsApp client is ready' 
                : hasQr 
                    ? 'QR code available, waiting for scan'
                    : status === 'authenticated'
                        ? 'Authenticated, waiting for ready'
                        : 'WhatsApp client not ready',
            accountInfo: isReady ? currentAccountInfo : null
        });
    } catch (error: any) {
        console.error('❌ Error getting WhatsApp status:', error);
        // Даже при ошибке возвращаем 200 с информацией об ошибке
        res.status(200).json({ 
            success: false,
            status: 'error',
            error: 'Failed to get WhatsApp status',
            message: error?.message || 'Unknown error',
            hasQr: false,
            isReady: false
        });
    }
});

// =============================================================================
// НОВЫЕ API ENDPOINTS ДЛЯ УПРАВЛЕНИЯ АККАУНТОМ
// =============================================================================

// Получение информации о текущем аккаунте
app.get('/whatsapp/account', (req, res) => {
    try {
        res.json({
            success: true,
            account: currentAccountInfo,
            hasActiveAccount: currentAccountInfo.isReady
        });
    } catch (error: any) {
        res.status(500).json({
            success: false,
            error: 'Failed to get account info',
            details: error?.message || 'Unknown error'
        });
    }
});

// Ленивая инициализация WhatsApp клиента (вызывается по запросу из UI)
app.post('/api/whatsapp/start', async (req, res) => {
    try {
        console.log('[WA] Start request received via /api/whatsapp/start');
        
        // Если клиент уже создан и инициализируется, возвращаем текущий статус
        if (isInitializing || isReinitializing) {
            console.log('[WA] Client initialization already in progress');
            return res.json({
                success: true,
                status: 'initializing',
                message: 'WhatsApp client initialization already in progress',
                currentState: waState
            });
        }
        
        // Если клиент уже готов, возвращаем статус ready
        if (client && isClientReady && client.info) {
            console.log('[WA] Client already ready');
            return res.json({
                success: true,
                status: 'ready',
                message: 'WhatsApp client is already ready',
                currentState: waState,
                accountInfo: currentAccountInfo
            });
        }
        
        // Если клиент существует, но не готов, возвращаем текущий статус
        if (client) {
            console.log('[WA] Client exists but not ready, current state:', waState);
            return res.json({
                success: true,
                status: waState,
                message: 'WhatsApp client exists but not ready yet',
                currentState: waState,
                hasQr: !!qrCode
            });
        }
        
        // Создаем и инициализируем новый клиент
        console.log('[WA] Creating and initializing new WhatsApp client...');
        await initializeWhatsAppClient();
        
        res.json({
            success: true,
            status: 'initializing',
            message: 'WhatsApp client initialization started',
            currentState: waState
        });
    } catch (error: any) {
        console.error('[WA] Error starting WhatsApp client:', error);
        res.status(500).json({
            success: false,
            error: 'Failed to start WhatsApp client',
            details: error?.message || 'Unknown error'
        });
    }
});

// Graceful остановка WhatsApp клиента (без очистки auth/cache)
app.post('/api/whatsapp/stop', async (req, res) => {
    try {
        console.log('[WA] Stop request received via /api/whatsapp/stop');
        
        if (!client) {
            return res.json({
                success: true,
                message: 'WhatsApp client is not running',
                status: 'idle'
            });
        }
        
        // Останавливаем watchdog
        stopReadyWatchdog();
        
        // Уничтожаем клиент
        try {
            await client.destroy();
            console.log('[WA] Client destroyed successfully');
            await delay(1000);
        } catch (error: any) {
            console.log('[WA] Warning: Error destroying client:', error?.message || error);
        }
        
        client = null as any;
        isClientReady = false;
        isInitializing = false;
        isReinitializing = false;
        qrCode = null;
        currentAccountInfo = {
            phoneNumber: undefined,
            name: undefined,
            profilePicUrl: undefined,
            isReady: false
        };
        
        // Обновляем состояние
        updateWaState('idle', null);
        
        // Уведомляем клиентов
        io.emit('wa:state', {
            state: 'idle',
            reason: null
        });
        
        res.json({
            success: true,
            message: 'WhatsApp client stopped successfully',
            status: 'idle'
        });
    } catch (error: any) {
        console.error('[WA] Error stopping WhatsApp client:', error);
        res.status(500).json({
            success: false,
            error: 'Failed to stop WhatsApp client',
            details: error?.message || 'Unknown error'
        });
    }
});

// Полное отключение и очистка аккаунта
app.post('/whatsapp/reset', async (req, res) => {
    try {
        console.log('[WA] Full WhatsApp reset requested via /whatsapp/reset');
        await performManualReset();
        res.json({
            success: true,
            message: 'WhatsApp account reset completed. Please scan new QR code.',
            requiresNewAuth: true
        });
    } catch (error: any) {
        console.error('[WA] Error during reset:', error);
        res.status(500).json({
            success: false,
            error: 'Failed to reset WhatsApp account',
            details: error?.message || 'Unknown error'
        });
    }
});

// Альтернативный эндпоинт для сброса (для совместимости)
app.post('/api/whatsapp/reset', async (req, res) => {
    // Используем performManualReset для единообразия
    try {
        console.log('[WA] Full WhatsApp reset requested via /api/whatsapp/reset');
        await performManualReset();
        res.json({
            success: true,
            message: 'WhatsApp account reset completed. Please scan new QR code.',
            requiresNewAuth: true
        });
    } catch (error: any) {
        console.error('[WA] Error during reset:', error);
        res.status(500).json({
            success: false,
            error: 'Failed to reset WhatsApp account',
            details: error?.message || 'Unknown error'
        });
    }
});

// Мягкий logout (сохраняем данные, выходим из аккаунта)
app.post('/whatsapp/soft-logout', async (req, res) => {
    try {
        console.log('🚪 Soft logout requested');
        
        if (client) {
            await client.logout();
            console.log('✅ WhatsApp client logged out');
        }
        
        // Сбрасываем информацию о текущем аккаунте
        currentAccountInfo = { isReady: false };
        
        // Уведомляем клиентов о logout
        io.emit('account-logout', { 
            message: 'Выход из аккаунта WhatsApp' 
        });
        
        res.json({
            success: true,
            message: 'Logged out successfully. Data preserved.',
            requiresNewAuth: true
        });
        
        // Перезапускаем клиент
        setTimeout(async () => {
            await restartWhatsAppClient();
        }, 2000);
        
    } catch (error: any) {
        console.error('❌ Error during soft logout:', error);
        res.status(500).json({
            success: false,
            error: 'Failed to logout',
            details: error?.message || 'Unknown error'
        });
    }
});

// Получение списка сохраненных чатов с информацией о принадлежности к аккаунту
app.get('/whatsapp/chats-summary', async (req, res) => {
    try {
        const chats = await loadChats();
        const readStatuses = getAllReadStatuses();
        
        const summary = {
            totalChats: Object.keys(chats).length,
            totalMessages: Object.values(chats).reduce((total, chat) => total + chat.messages.length, 0),
            totalUnreadChats: Object.values(chats).filter(chat => (chat.unreadCount || 0) > 0).length,
            currentAccount: currentAccountInfo.isReady ? currentAccountInfo.phoneNumber : null,
            hasMultipleAccountData: false, // В будущем можем добавить логику определения
            readStatusEntries: Object.keys(readStatuses).length
        };
        
        res.json({
            success: true,
            summary,
            chats: Object.keys(chats), // Только список номеров для анализа
            accountInfo: currentAccountInfo
        });
        
    } catch (error: any) {
        console.error('❌ Error getting chats summary:', error);
        res.status(500).json({
            success: false,
            error: 'Failed to get chats summary',
            details: error?.message || 'Unknown error'
        });
    }
});

// =============================================================================
// КОНЕЦ НОВЫХ API ENDPOINTS
// =============================================================================

// =============================================================================
// ФУНКЦИИ УПРАВЛЕНИЯ АККАУНТОМ И ИНИЦИАЛИЗАЦИИ
// =============================================================================

// Функция для полной очистки данных аккаунта
const clearAccountData = async (): Promise<void> => {
    try {
        console.log('🧹 Clearing all account data...');
        
        // 1. Очищаем кэш чатов
        const { clearAllChats } = await import('./utils/chatStorage');
        await clearAllChats();
        
        // 2. Очищаем данные read status
        const { clearAllReadStatuses } = await import('./utils/readStatusStorage');
        await clearAllReadStatuses();
        
        // 3. Очищаем кэш аватарок
        const { clearAvatarCache } = await import('./utils/avatarCache');
        await clearAvatarCache();
        
        // 4. Очищаем информацию о текущем аккаунте
        currentAccountInfo = { isReady: false };
        
        console.log('✅ All account data cleared');
    } catch (error) {
        console.error('❌ Error clearing account data:', error);
        throw error;
    }
};

// Функция для очистки файлов аутентификации (использует safeRemoveDir)
const clearAuthFiles = async (): Promise<void> => {
    try {
        console.log('[WA] Clearing WhatsApp authentication files...');
        
        const authPath = path.resolve(__dirname, '../.wwebjs_auth');
        const cachePath = path.resolve(__dirname, '../.wwebjs_cache');
        
        // Удаляем папки аутентификации и кэша с retry
        const authRemoved = await safeRemoveDir(authPath);
        if (authRemoved) {
            console.log('[WA] Removed .wwebjs_auth folder');
        } else {
            console.warn('[WA] Failed to remove .wwebjs_auth folder (will continue anyway)');
        }
        
        const cacheRemoved = await safeRemoveDir(cachePath);
        if (cacheRemoved) {
            console.log('[WA] Removed .wwebjs_cache folder');
        } else {
            console.warn('[WA] Failed to remove .wwebjs_cache folder (will continue anyway)');
        }
        
    } catch (error) {
        console.error('[WA] Error clearing auth files:', error);
        // Не бросаем ошибку, продолжаем работу
    }
};

// Функция создания нового WhatsApp клиента с подпиской на события
const createWhatsAppClient = (): Client => {
    const isWindows = process.platform === 'win32';
    const isLocal = isWindows || process.env.NODE_ENV === 'development' || process.env.FORCE_LOCAL_MODE === 'true';
    
    const sessionPath = isLocal 
        ? path.resolve(__dirname, '../.wwebjs_auth')
        : (process.env.WHATSAPP_SESSION_PATH || '/app/data/.wwebjs_auth');
    
    const chromiumPath = isLocal 
        ? undefined
        : (process.env.PUPPETEER_EXECUTABLE_PATH || '/usr/bin/chromium-browser');

    const waDebug = process.env.WA_DEBUG === 'true';
    const waDebugUI = process.env.WA_DEBUG_UI === '1' || process.env.WA_DEBUG_UI === 'true';
    // По умолчанию headless=true (чтобы не было "позорища")
    // В dev можно false только если WA_DEBUG_UI=1
    const waHeadless = process.env.WA_HEADLESS === 'true' ? true : 
                       (process.env.WA_HEADLESS === 'false' ? false : 
                       (waDebugUI ? false : true)); // По умолчанию true
    const waFreshProfile = process.env.WA_FRESH_PROFILE === '1' || process.env.WA_FRESH_PROFILE === 'true';
    
    // ВАЖНО: LocalAuth сам управляет userDataDir, нельзя передавать userDataDir в puppeteer config
    // Вместо этого используем флаги для отключения расширений и чистого запуска
    
    // Безопасный минимальный набор аргументов Chromium + анти-детек
    // Важно: отключаем расширения и используем чистый профиль
    const puppeteerArgs = [
        '--no-sandbox',
        '--disable-setuid-sandbox',
        '--disable-dev-shm-usage',
        '--disable-gpu',
        '--no-first-run',
        '--no-default-browser-check',
        '--disable-extensions',
        '--disable-component-extensions-with-background-pages',
        '--disable-default-apps',
        '--disable-blink-features=AutomationControlled', // Анти-детек
    ];
    
    // Нормальный User-Agent для анти-детек
    const userAgent = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';
    
    const puppeteerConfig: any = {
        headless: waHeadless,
        args: puppeteerArgs,
        timeout: 120000,
        defaultViewport: { width: 1366, height: 768 },
        // НЕ передаём userDataDir - LocalAuth сам управляет путём сессии
    };
    
    if (waDebug) {
        puppeteerConfig.slowMo = 50;
        puppeteerConfig.devtools = true;
    }
    
    if (chromiumPath) {
        puppeteerConfig.executablePath = chromiumPath;
    }
    
    console.log('[WA] launch headless=' + waHeadless + ' args=[' + puppeteerArgs.join(', ') + ']');
    console.log('[WA] Puppeteer (createWhatsAppClient) config:', {
        headless: puppeteerConfig.headless,
        debug: waDebug,
        executablePath: puppeteerConfig.executablePath || 'auto',
        args: puppeteerArgs.length,
        userAgent: userAgent.substring(0, 50) + '...',
        note: 'LocalAuth manages userDataDir via dataPath',
    });
    
    const webVersionConfig = {
        type: 'remote' as const,
        remotePath: 'https://raw.githubusercontent.com/wppconnect-team/wa-version/main/html/2.2412.54.html',
    };
    
    console.log('[WA] createWhatsAppClient: webVersionCache config:', {
        type: webVersionConfig.type,
        remotePath: webVersionConfig.remotePath,
        source: 'wppconnect-team/wa-version (stable)',
    });
    
    const newClient = new Client({
        authStrategy: new LocalAuth({
            clientId: 'whatsapp-client',
            dataPath: sessionPath
        }),
        puppeteer: puppeteerConfig,
        webVersionCache: webVersionConfig,
        takeoverOnConflict: true,
        takeoverTimeoutMs: 60000,
        restartOnAuthFail: true,
        qrMaxRetries: 10,
        authTimeoutMs: 180000
    });
    
    // Подписываем на события
    setupEnhancedClientEventHandlers(newClient);
    
    return newClient;
};

// Функция для ручного reset (вызывается через API)
const performManualReset = async (): Promise<void> => {
    console.log('[WA] Manual reset requested');
    
    // Сбрасываем флаг блокировки
    isBlocked = false;
    blockedReason = null;
    blockedUrl = null;
    criticalBlockedCount = 0;
    mediaBlockedCount = 0;
    
    // Останавливаем watchdog
    stopReadyWatchdog();
    
    // Уничтожаем клиент
    if (client) {
        try {
            await client.destroy();
            console.log('[WA] Client destroyed');
            await delay(2000);
        } catch (error: any) {
            console.log('[WA] Warning: Error destroying client:', error?.message || error);
            await delay(2000);
        }
    }
    
    // Очищаем все данные аккаунта
    await clearAccountData();
    
    // Очищаем файлы аутентификации
    await clearAuthFiles();
    
    // Обновляем состояние
    updateWaState('idle', null);
    
    // Уведомляем клиентов о сбросе
    io.emit('account-reset', { 
        message: 'Аккаунт сброшен, требуется новая аутентификация' 
    });
    
    // Создаем новый клиент через небольшую задержку
    setTimeout(async () => {
        await initializeWhatsAppClient();
    }, 2000);
};

// Controlled reset функция для watchdog (без удаления папок, только пересоздание клиента)
const controlledReset = async (reason: string): Promise<void> => {
    // Guard: предотвращаем двойной reset
    if (isReinitializing) {
        console.log('[WA] Controlled reset already in progress, skipping');
        return;
    }
    
    isReinitializing = true;
    console.log(`[WA] controlled reset started reason=${reason}`);
    console.log(`[WA] controlled reset: current state=${waState}, isClientReady=${isClientReady}`);
    
    try {
        // Останавливаем watchdog
        stopReadyWatchdog();
        
        // Сохраняем ссылку на старый клиент для уничтожения
        const oldClient = client;
        
        // 1. Уничтожаем клиент
        if (oldClient) {
            try {
                console.log('[WA] destroying old client...');
                await oldClient.destroy();
                console.log('[WA] destroy complete');
                // Задержка для освобождения lock (важно для Windows) - 1500-2500ms
                await delay(2000);
            } catch (error: any) {
                console.log('[WA] Warning: Error destroying client:', error?.message || error);
                console.log('[WA] Error stack:', error?.stack);
                await delay(2000); // Задержка даже при ошибке
            }
        } else {
            console.log('[WA] WARNING: no client to destroy');
        }
        
        // 2. Удаляем папки аутентификации с retry (для watchdog reset тоже удаляем)
        console.log('[WA] clearing auth files...');
        await clearAuthFiles();
        
        // 3. Сбрасываем флаг watchdog reset для нового клиента
        hasWatchdogResetAttempted = false;
        console.log('[WA] watchdog reset flag cleared for new client');
        
        // 4. Создаем НОВЫЙ инстанс Client (не переиспользуем старый)
        console.log('[WA] creating new client instance...');
        client = createWhatsAppClient();
        console.log('[WA] new client instance created');
        
        // 5. Инициализируем новый клиент (с проверкой что не в процессе инициализации)
        if (isInitializing) {
            console.log('[WA] WARNING: initialize() called during controlled reset but isInitializing=true, skipping');
            return;
        }
        console.log('[WA] init called (controlled reset)');
        await client.initialize();
        console.log('[WA] initialize complete');
        
        // Состояние будет обновлено через обработчики событий (qr, ready, etc.)
        
    } catch (error: any) {
        console.error('[WA] Error during controlled reset:', error);
        console.error('[WA] Error stack:', error?.stack);
        updateWaState('disconnected', null, `Controlled reset failed: ${error?.message || error}`);
        
        // Пытаемся восстановиться через safeReconnect
        setTimeout(() => {
            safeReconnect(`Controlled reset failed: ${error?.message || error}`);
        }, 3000);
    } finally {
        isReinitializing = false;
    }
};

// Функция reset flow для обработки LOGOUT
const resetFlow = async (reason: string): Promise<void> => {
    // Guard: предотвращаем двойной reset
    if (isReinitializing) {
        console.log('[WA] Reset already in progress, skipping');
        return;
    }
    
    isReinitializing = true;
    console.log(`[WA] reset started reason=${reason}`);
    
    try {
        // Останавливаем watchdog
        stopReadyWatchdog();
        
        // 1. Уничтожаем клиент
        if (client) {
            try {
                await client.destroy();
                console.log('[WA] destroy complete');
                // Задержка для освобождения lock (важно для Windows) - 1500-2500ms
                await delay(2000);
            } catch (error: any) {
                console.log('[WA] Warning: Error destroying client:', error?.message || error);
                await delay(2000); // Задержка даже при ошибке
            }
        }
        
        // 2. Удаляем папки аутентификации с retry
        await clearAuthFiles();
        
        // 3. Создаем НОВЫЙ инстанс Client (не переиспользуем старый)
        client = createWhatsAppClient();
        console.log('[WA] new client instance created');
        
        // 4. Инициализируем новый клиент (с проверкой что не в процессе инициализации)
        if (isInitializing) {
            console.log('[WA] WARNING: initialize() called during reset flow but isInitializing=true, skipping');
            return;
        }
        console.log('[WA] init called (reset flow)');
        await client.initialize();
        console.log('[WA] initialize complete');
        
        // Состояние будет обновлено через обработчики событий (qr, ready, etc.)
        
    } catch (error: any) {
        console.error('[WA] Error during reset flow:', error);
        console.error('[WA] Error stack:', error?.stack);
        updateWaState('disconnected', null, `Reset failed: ${error?.message || error}`);
        
        // Пытаемся восстановиться через safeReconnect
        setTimeout(() => {
            safeReconnect(`Reset flow failed: ${error?.message || error}`);
        }, 3000);
    } finally {
        isReinitializing = false;
    }
};

// Функция получения информации о текущем аккаунте
const updateAccountInfo = async (): Promise<void> => {
    try {
        if (client && client.info) {
            const info = client.info;
            currentAccountInfo = {
                phoneNumber: info.wid.user + '@c.us',
                name: info.pushname || 'Пользователь',
                profilePicUrl: undefined, // Будет загружена отдельно
                isReady: true,
                connectedAt: new Date().toISOString()
            };
            
            // Получаем аватарку пользователя
            try {
                const profilePicUrl = await client.getProfilePicUrl(info.wid._serialized);
                currentAccountInfo.profilePicUrl = profilePicUrl;
            } catch (error) {
                console.log('No profile picture available');
            }
            
            console.log('📱 Account info updated:', {
                phoneNumber: currentAccountInfo.phoneNumber,
                name: currentAccountInfo.name
            });
        }
    } catch (error) {
        console.error('Error updating account info:', error);
    }
};

// Улучшенная функция инициализации WhatsApp клиента
const initializeWhatsAppClient = async (): Promise<void> => {
    if (isInitializing || isReinitializing) {
        console.log('[WA] Client initialization already in progress');
        return;
    }

    try {
        isInitializing = true;
        isClientReady = false;
        currentAccountInfo.isReady = false;
        
        // Устанавливаем начальное состояние
        updateWaState('idle', null);
        
        logConnectionState('INITIALIZING');

        // Автоопределение операционной системы и конфигурации
        const isWindows = process.platform === 'win32';
        const isLinux = process.platform === 'linux';
        const isLocal = isWindows || process.env.NODE_ENV === 'development' || process.env.FORCE_LOCAL_MODE === 'true';
        
        // Настройки путей в зависимости от ОС
        const sessionPath = isLocal 
            ? path.resolve(__dirname, '../.wwebjs_auth')  // Локальная папка для Windows/разработки
            : (process.env.WHATSAPP_SESSION_PATH || '/app/data/.wwebjs_auth'); // Docker/VM путь
        
        // Путь к браузеру - для Windows/локальной разработки не указываем (Puppeteer найдет сам)
        const chromiumPath = isLocal 
            ? undefined  // Для Windows/локальной разработки позволяем Puppeteer найти Chrome автоматически
            : (process.env.PUPPETEER_EXECUTABLE_PATH || '/usr/bin/chromium-browser'); // Docker/VM путь
        
        console.log('🔧 WhatsApp Client Configuration:');
        console.log(`   Platform: ${process.platform}`);
        console.log(`   Local Mode: ${isLocal}`);
        console.log(`   Session Path: ${sessionPath}`);
        console.log(`   Chromium Path: ${chromiumPath || 'Auto-detect'}`);
        console.log(`   Node Environment: ${process.env.NODE_ENV}`);
        console.log(`   WA_HEADLESS: ${process.env.WA_HEADLESS ?? 'default(true)'}`);
        console.log(`   WA_DEBUG: ${process.env.WA_DEBUG ?? 'false'}`);
        console.log('   WebVersionCache: remote html 2.2412.54 via wppconnect-team/wa-version');

        const waDebug = process.env.WA_DEBUG === 'true';
        const waDebugUI = process.env.WA_DEBUG_UI === '1' || process.env.WA_DEBUG_UI === 'true';
        // По умолчанию headless=true (чтобы не было "позорища")
        // В dev можно false только если WA_DEBUG_UI=1
        const waHeadless = process.env.WA_HEADLESS === 'true' ? true : 
                           (process.env.WA_HEADLESS === 'false' ? false : 
                           (waDebugUI ? false : true)); // По умолчанию true
        const waFreshProfile = process.env.WA_FRESH_PROFILE === '1' || process.env.WA_FRESH_PROFILE === 'true';

        // ВАЖНО: LocalAuth сам управляет userDataDir через dataPath в authStrategy
        // Нельзя передавать userDataDir в puppeteer config - это вызывает ошибку
        // Вместо этого используем флаги для отключения расширений
        
        if (waFreshProfile) {
            console.log('[WA] WA_FRESH_PROFILE=true: clearing auth files for fresh start...');
            try {
                await clearAuthFiles();
                console.log('[WA] Auth files cleared for fresh profile');
            } catch (e: any) {
                console.log('[WA] Warning: could not clear auth files:', e?.message || e);
            }
        }

        // SAFE-набор аргументов Puppeteer (без экстремальных флагов) + анти-детек
        const puppeteerArgs = [
            '--no-sandbox',
            '--disable-setuid-sandbox',
            '--disable-dev-shm-usage',
            '--disable-gpu',
            '--no-first-run',
            '--no-default-browser-check',
            '--disable-extensions',
            '--disable-component-extensions-with-background-pages',
            '--disable-blink-features=AutomationControlled', // Анти-детек
        ];

        console.log(`🔧 Using SAFE Puppeteer args (${puppeteerArgs.length} flags), debug=${waDebug}, headless=${waHeadless}, freshProfile=${waFreshProfile}`);
        console.log('[WA] launch headless=' + waHeadless + ' args=[' + puppeteerArgs.join(', ') + ']');
        console.log(`🔧 LocalAuth manages userDataDir via dataPath (sessionPath)`);

        // Минимальные environment variables для Puppeteer
        process.env.PUPPETEER_SKIP_CHROMIUM_DOWNLOAD = 'true';
        process.env.PUPPETEER_DISABLE_HEADLESS_WARNING = 'true';

        // Создаем конфигурацию Puppeteer с учетом ОС и ENV
        const puppeteerConfig: any = {
            headless: waHeadless,
            args: puppeteerArgs,
            timeout: 120000, // до 2 минут
            defaultViewport: { width: 1366, height: 768 },
            devtools: waDebug,
            ignoreDefaultArgs: false,
            // НЕ передаём userDataDir - LocalAuth сам управляет путём сессии через dataPath
        };

        if (waDebug) {
            puppeteerConfig.slowMo = 50;
        }

        // Добавляем executablePath только для Linux/Docker
        if (chromiumPath) {
            puppeteerConfig.executablePath = chromiumPath;
        }

        // Создаем новый клиент с безопасными настройками Puppeteer
        const webVersionConfig = {
            type: 'remote' as const,
            remotePath: 'https://raw.githubusercontent.com/wppconnect-team/wa-version/main/html/2.2412.54.html',
        };
        
        console.log('[WA] initializeWhatsAppClient: webVersionCache config:', {
            type: webVersionConfig.type,
            remotePath: webVersionConfig.remotePath,
            source: 'wppconnect-team/wa-version (stable)',
        });
        
        const newClient = new Client({
            authStrategy: new LocalAuth({
                clientId: 'whatsapp-client',
                dataPath: sessionPath
            }),
            puppeteer: puppeteerConfig,
            webVersionCache: webVersionConfig,
            takeoverOnConflict: true,
            takeoverTimeoutMs: 60000,
            restartOnAuthFail: true,
            qrMaxRetries: 10,
            authTimeoutMs: 180000
        });

        client = newClient;
        
        // Настраиваем обработчики событий
        setupEnhancedClientEventHandlers(client);
        
        console.log('🔄 Initializing WhatsApp client...');
        
        // Инициализируем клиент с расширенной retry логикой
        let initSuccess = false;
        let initAttempts = 0;
        const maxInitAttempts = 5; // Увеличиваем количество попыток
        
        while (!initSuccess && initAttempts < maxInitAttempts) {
            try {
                initAttempts++;
                console.log(`🔄 Initialization attempt ${initAttempts}/${maxInitAttempts}...`);
                
                // Добавляем pre-initialization задержку для стабильности
                if (initAttempts > 1) {
                    const delay = Math.min(initAttempts * 15000, 60000); // До 1 минуты задержки
                    console.log(`⏳ Waiting ${delay/1000} seconds before retry...`);
                    await new Promise(resolve => setTimeout(resolve, delay));
                }
                
                // Очищаем память перед попыткой
                if (global.gc) {
                    global.gc();
                }
                
                console.log('[WA] init called (initializeWhatsAppClient attempt ' + initAttempts + ')');
                await client.initialize();
                console.log('[WA] initialize complete (attempt ' + initAttempts + ')');
                
                // Логируем реальную используемую webVersion после инициализации
                try {
                    const anyClient = client as any;
                    const page = anyClient?.pupPage;
                    if (page) {
                        const pageUrl = await page.url();
                        console.log('[WA] Actual page URL after init:', pageUrl);
                        // Извлекаем версию из URL если возможно
                        const versionMatch = pageUrl.match(/\/v\/(\d+\.\d+\.\d+)/);
                        if (versionMatch) {
                            console.log('[WA] Actual webVersion from URL:', versionMatch[1]);
                        }
                    }
                    const webVersion = anyClient?.webVersion || 'unknown';
                    console.log('[WA] Actual webVersion used:', webVersion);
                } catch (e: any) {
                    console.log('[WA] Could not determine actual webVersion:', e?.message || e);
                }
                
                initSuccess = true;
                console.log('✅ WhatsApp client initialized successfully');
                
            } catch (initError: any) {
                console.error(`❌ Initialization attempt ${initAttempts} failed:`, initError.message || initError);
                
                if (initAttempts < maxInitAttempts) {
                    console.log(`⏳ Preparing for retry ${initAttempts + 1}/${maxInitAttempts}...`);
                    
                    // Уничтожаем неудавшийся клиент полностью
                    try {
                        if (client) {
                            console.log('🗑️  Destroying failed client instance...');
                            await client.destroy();
                            await new Promise(resolve => setTimeout(resolve, 5000)); // Ждем полного уничтожения
                        }
                    } catch (destroyError) {
                        console.log('⚠️  Warning: Error destroying failed client:', destroyError);
                    }
                    
                    // Создаем новый клиент для следующей попытки с уникальным ID
                    const clientId = `whatsapp-client-attempt-${initAttempts + 1}-${Date.now()}`;
                    console.log(`🔄 Creating new client with ID: ${clientId}`);
                    
                    // Создаем конфигурацию Puppeteer для retry с учетом ОС
                    const retryPuppeteerConfig: any = {
                        headless: waHeadless, // Используем тот же headless режим, что и в основном клиенте
                        args: puppeteerArgs,
                        timeout: 120000 + (initAttempts * 30000), // Увеличиваем timeout с каждой попыткой
                        defaultViewport: { width: 1366, height: 768 },
                        devtools: false,
                        ignoreDefaultArgs: false,
                        handleSIGINT: false,
                        handleSIGTERM: false,
                        handleSIGHUP: false,
                        pipe: false,
                        dumpio: false,
                        slowMo: 150 + (initAttempts * 50), // Еще больше замедляем с каждой попыткой
                        ignoreHTTPSErrors: true,
                        env: {
                            ...process.env,
                            DISPLAY: ':99',
                            CHROME_DEVEL_SANDBOX: 'false',
                            CHROME_NO_SANDBOX: 'true'
                        }
                    };

                    // Добавляем executablePath только для Linux/Docker
                    if (chromiumPath) {
                        retryPuppeteerConfig.executablePath = chromiumPath;
                    }

                    client = new Client({
                        authStrategy: new LocalAuth({
                            clientId: clientId,
                            dataPath: sessionPath
                        }),
                        puppeteer: retryPuppeteerConfig,
                        webVersionCache: {
                            type: 'remote',
                            remotePath: 'https://raw.githubusercontent.com/wppconnect-team/wa-version/main/html/2.2412.54.html',
                        },
                        takeoverOnConflict: true,
                        takeoverTimeoutMs: 60000 + (initAttempts * 15000),
                        restartOnAuthFail: true,
                        qrMaxRetries: 10,
                        authTimeoutMs: 180000 + (initAttempts * 60000)
                    });
                    
                    setupEnhancedClientEventHandlers(client);
                } else {
                    console.error(`❌ Failed to initialize after ${maxInitAttempts} attempts. Last error:`, initError);
                    throw new Error(`WhatsApp client initialization failed after ${maxInitAttempts} attempts: ${initError.message}`);
                }
            }
        }
        
        if (!initSuccess) {
            throw new Error(`Failed to initialize WhatsApp client after ${maxInitAttempts} attempts`);
        }
        
        logConnectionState('INITIALIZATION_COMPLETE');
        // Состояние будет обновлено через обработчики событий (qr, ready, etc.)

    } catch (error: any) {
        console.error('[WA] CRITICAL: Error initializing WhatsApp client:', error);
        logConnectionState('INITIALIZATION_FAILED', error);
        
        // Обновляем состояние на disconnected при ошибке
        updateWaState('disconnected', null);
        
        // Очищаем состояние
        isClientReady = false;
        currentAccountInfo.isReady = false;
        
        // Эскалируем задержку для критических ошибок
        const escalatedDelay = Math.min(RECONNECT_DELAY * 3, 30000); // До 30 секунд
        console.log(`[WA] Scheduling reconnection with escalated delay: ${escalatedDelay/1000} seconds`);
        
        setTimeout(() => {
            safeReconnect('Extreme initialization failed');
        }, escalatedDelay);
        
        throw error;
    } finally {
        isInitializing = false;
    }
};

// =============================================================================
// КОНЕЦ ФУНКЦИЙ УПРАВЛЕНИЯ АККАУНТОМ
// =============================================================================

// Инициализируем все компоненты и запускаем сервер
(async () => {
    try {
        console.log('🚀 Starting WhatsApp server...');
        
        // Загружаем чаты
        await initializeChatsCache();
        console.log('✅ Chats loaded successfully');

        // Инициализируем хранилище медиафайлов
        await initializeMediaBucket();
        console.log('✅ Media storage initialized successfully');

        // Обработка unhandledRejection и uncaughtException для диагностики
        process.on('unhandledRejection', (reason: any, promise: Promise<any>) => {
            console.error('[WA] UNHANDLED REJECTION:', reason);
            if (reason && typeof reason === 'object' && 'stack' in reason) {
                console.error('[WA] Rejection stack:', (reason as any).stack);
            }
            console.error('[WA] Promise:', promise);
            // В dev режиме не падаем, только логируем
            if (process.env.NODE_ENV === 'production') {
                console.error('[WA] Unhandled rejection in production - process may exit');
            }
        });

        process.on('uncaughtException', (error: Error) => {
            console.error('[WA] UNCAUGHT EXCEPTION:', error);
            console.error('[WA] Exception stack:', error.stack);
            // В dev режиме не падаем, только логируем
            if (process.env.NODE_ENV === 'production') {
                console.error('[WA] Uncaught exception in production - process may exit');
                process.exit(1);
            }
        });

        // НЕ инициализируем WhatsApp клиент при старте сервера
        // Клиент будет создан только по запросу через /api/whatsapp/start
        console.log('✅ Server ready. WhatsApp client will be initialized on demand via /api/whatsapp/start');

        // Запускаем HTTP сервер
        httpServer.listen(PORT, () => {
            console.log(`🌐 Server is running on port ${PORT}`);
            console.log(`🔗 Socket.IO configured with CORS origin: ${FRONTEND_URL}`);
            console.log(`📱 WhatsApp client status: ${isClientReady ? 'Ready' : 'Initializing'}`);
            console.log(`🔗 Allowed CORS origins:`, allowedOrigins);
        });

        // Обработка ошибок сервера
        httpServer.on('error', (error: Error) => {
            console.error('❌ HTTP Server error:', error);
        });
        
        // Graceful shutdown обработка
        const gracefulShutdown = async (signal: string) => {
            console.log(`\n📴 Received ${signal}, starting graceful shutdown...`);
            
            try {
                // Сохраняем чаты
                await saveChats();
                console.log('✅ Chats saved successfully');
                
                // Закрываем WhatsApp клиент
                if (client) {
                    await client.destroy();
                    console.log('✅ WhatsApp client destroyed');
                }
                
                // Закрываем HTTP сервер
                httpServer.close(() => {
                    console.log('✅ HTTP server closed');
                    process.exit(0);
                });
                
            } catch (error) {
                console.error('❌ Error during graceful shutdown:', error);
                process.exit(1);
            }
        };
        
        // Регистрируем обработчики сигналов
        process.on('SIGINT', () => gracefulShutdown('SIGINT'));
        process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));

    } catch (error: any) {
        console.error('❌ Fatal error starting server:', error);
        process.exit(1);
    }
})();

// Обработка необработанных исключений
process.on('uncaughtException', (error: Error) => {
    console.error('❌ Uncaught Exception:', error);
    logConnectionState('UNCAUGHT_EXCEPTION', error);
});

process.on('unhandledRejection', (error: Error) => {
    console.error('❌ Unhandled Rejection:', error);
    logConnectionState('UNHANDLED_REJECTION', error);
});
