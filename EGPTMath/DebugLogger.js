/**
 * DebugLogger.js - Structured Debug Logging System for EGPT Analysis
 * 
 * Features:
 * - Memory-efficient circular buffer for debug messages
 * - Static flag for console output control (default: disabled)
 * - Callback system for custom message handling
 * - Performance metrics collection per invocation
 * - Categorized message types (timing, data, analysis, etc.)
 */

export class DebugLogger {
    static MAX_BUFFER_SIZE = 1000; // Maximum number of messages to keep in memory
    static CONSOLE_ENABLED = false; // Static flag to control console output
    static callbacks = new Set(); // Set of callback functions

    constructor(invocationKey, context = 'EGPT') {
        this.invocationKey = invocationKey;
        this.context = context;
        this.startTime = performance.now();
        this.messages = [];
        this.metrics = {
            totalMessages: 0,
            errorCount: 0,
            warningCount: 0,
            timingEvents: [],
            memorySnapshots: [],
            performanceMarkers: {}
        };
        
        // Add to static collection for global access
        DebugLogger.activeLoggers = DebugLogger.activeLoggers || new Map();
        DebugLogger.activeLoggers.set(invocationKey, this);
        
        this.log('INIT', `Debug logger initialized for ${invocationKey}`, { context });
    }

    /**
     * Log a message with automatic categorization and performance tracking
     * @param {string} level - Log level: INFO, DEBUG, TIMING, ERROR, WARNING, DATA, ANALYSIS
     * @param {string} message - The message to log
     * @param {object} data - Optional data object
     */
    log(level, message, data = null) {
        const timestamp = performance.now();
        const relativeTime = timestamp - this.startTime;
        
        const logEntry = {
            timestamp,
            relativeTime,
            level,
            message,
            data,
            invocationKey: this.invocationKey,
            context: this.context,
            id: this.metrics.totalMessages++
        };

        // Add to circular buffer
        this.messages.push(logEntry);
        if (this.messages.length > DebugLogger.MAX_BUFFER_SIZE) {
            this.messages.shift(); // Remove oldest message
        }

        // Update metrics
        this.updateMetrics(level, logEntry);

        // Console output (if enabled)
        if (DebugLogger.CONSOLE_ENABLED) {
            this.outputToConsole(logEntry);
        }

        // Notify callbacks
        DebugLogger.callbacks.forEach(callback => {
            try {
                callback(logEntry, this);
            } catch (error) {
                console.warn('Debug logger callback error:', error);
            }
        });
    }

    /**
     * Update internal metrics based on log entry
     */
    updateMetrics(level, logEntry) {
        switch (level) {
            case 'ERROR':
                this.metrics.errorCount++;
                break;
            case 'WARNING':
                this.metrics.warningCount++;
                break;
            case 'TIMING':
                this.metrics.timingEvents.push({
                    message: logEntry.message,
                    time: logEntry.relativeTime,
                    data: logEntry.data
                });
                break;
        }

        // Memory snapshot (every 100 messages)
        if (this.metrics.totalMessages % 100 === 0) {
            this.metrics.memorySnapshots.push({
                messageCount: this.metrics.totalMessages,
                time: logEntry.relativeTime,
                memoryUsed: this.messages.length
            });
        }
    }

    /**
     * Output to console with appropriate formatting
     */
    outputToConsole(logEntry) {
        const prefix = `[${this.context}:${this.invocationKey}:${logEntry.relativeTime.toFixed(2)}ms]`;
        const levelStyles = {
            'ERROR': ['color: #e74c3c; font-weight: bold', '❌'],
            'WARNING': ['color: #f39c12; font-weight: bold', '⚠️'],
            'TIMING': ['color: #3498db', '⏱️'],
            'DATA': ['color: #9b59b6', '📊'],
            'ANALYSIS': ['color: #2ecc71', '🔬'],
            'DEBUG': ['color: #95a5a6', '🔧'],
            'INFO': ['color: #34495e', 'ℹ️'],
            'INIT': ['color: #e67e22; font-weight: bold', '🚀']
        };

        const [style, emoji] = levelStyles[logEntry.level] || levelStyles['DEBUG'];
        
        if (logEntry.data) {
            console.log(`%c${prefix} ${emoji} ${logEntry.message}`, style, logEntry.data);
        } else {
            console.log(`%c${prefix} ${emoji} ${logEntry.message}`, style);
        }
    }

    /**
     * Convenience methods for different log levels
     */
    info(message, data) { this.log('INFO', message, data); }
    debug(message, data) { this.log('DEBUG', message, data); }
    timing(message, data) { this.log('TIMING', message, data); }
    error(message, data) { this.log('ERROR', message, data); }
    warning(message, data) { this.log('WARNING', message, data); }
    data(message, data) { this.log('DATA', message, data); }
    analysis(message, data) { this.log('ANALYSIS', message, data); }

    /**
     * Mark a performance checkpoint
     */
    mark(label) {
        const time = performance.now() - this.startTime;
        this.metrics.performanceMarkers[label] = time;
        this.timing(`Performance marker: ${label}`, { time });
        return time;
    }

    /**
     * Measure time between two marks
     */
    measure(startLabel, endLabel) {
        const startTime = this.metrics.performanceMarkers[startLabel];
        const endTime = this.metrics.performanceMarkers[endLabel];
        if (startTime !== undefined && endTime !== undefined) {
            const duration = endTime - startTime;
            this.timing(`Measure ${startLabel} → ${endLabel}`, { duration, startTime, endTime });
            return duration;
        }
        return null;
    }

    /**
     * Get summary of this logger's activity
     */
    getSummary() {
        const duration = performance.now() - this.startTime;
        return {
            invocationKey: this.invocationKey,
            context: this.context,
            duration,
            totalMessages: this.metrics.totalMessages,
            errorCount: this.metrics.errorCount,
            warningCount: this.metrics.warningCount,
            timingEvents: this.metrics.timingEvents.length,
            memorySnapshots: this.metrics.memorySnapshots.length,
            performanceMarkers: Object.keys(this.metrics.performanceMarkers).length,
            messagesInBuffer: this.messages.length
        };
    }

    /**
     * Get all messages (or filtered subset)
     */
    getMessages(filter = null) {
        if (!filter) return [...this.messages];
        
        return this.messages.filter(msg => {
            if (filter.level && msg.level !== filter.level) return false;
            if (filter.timeRange && (msg.relativeTime < filter.timeRange[0] || msg.relativeTime > filter.timeRange[1])) return false;
            if (filter.searchText && !msg.message.toLowerCase().includes(filter.searchText.toLowerCase())) return false;
            return true;
        });
    }

    /**
     * Clean up this logger
     */
    finalize() {
        const summary = this.getSummary();
        this.info('Logger finalized', summary);
        
        // Remove from active loggers
        if (DebugLogger.activeLoggers) {
            DebugLogger.activeLoggers.delete(this.invocationKey);
        }
        
        return summary;
    }

    // =============================================================================
    // STATIC METHODS FOR GLOBAL CONTROL
    // =============================================================================

    /**
     * Enable/disable console output globally
     */
    static setConsoleEnabled(enabled) {
        DebugLogger.CONSOLE_ENABLED = enabled;
        console.log(`%cDebugLogger console output ${enabled ? 'ENABLED' : 'DISABLED'}`, 
                   `color: ${enabled ? '#2ecc71' : '#e74c3c'}; font-weight: bold;`);
    }

    /**
     * Add a callback function to receive log messages
     */
    static addCallback(callback) {
        DebugLogger.callbacks.add(callback);
    }

    /**
     * Remove a callback function
     */
    static removeCallback(callback) {
        DebugLogger.callbacks.delete(callback);
    }

    /**
     * Clear all callbacks
     */
    static clearCallbacks() {
        DebugLogger.callbacks.clear();
    }

    /**
     * Get logger for specific invocation
     */
    static getLogger(invocationKey) {
        return DebugLogger.activeLoggers?.get(invocationKey) || null;
    }

    /**
     * Get all active loggers
     */
    static getAllLoggers() {
        return DebugLogger.activeLoggers ? Array.from(DebugLogger.activeLoggers.values()) : [];
    }

    /**
     * Get summary of all active loggers
     */
    static getGlobalSummary() {
        const loggers = DebugLogger.getAllLoggers();
        return {
            totalActiveLoggers: loggers.length,
            totalMessages: loggers.reduce((sum, logger) => sum + logger.metrics.totalMessages, 0),
            totalErrors: loggers.reduce((sum, logger) => sum + logger.metrics.errorCount, 0),
            totalWarnings: loggers.reduce((sum, logger) => sum + logger.metrics.warningCount, 0),
            consoleEnabled: DebugLogger.CONSOLE_ENABLED,
            callbackCount: DebugLogger.callbacks.size,
            loggers: loggers.map(logger => logger.getSummary())
        };
    }

    /**
     * Clean up old/completed loggers (keep last N)
     */
    static cleanupOldLoggers(keepLast = 10) {
        if (!DebugLogger.activeLoggers) return;
        
        const loggers = Array.from(DebugLogger.activeLoggers.entries());
        if (loggers.length <= keepLast) return;
        
        // Sort by start time (oldest first)
        loggers.sort((a, b) => a[1].startTime - b[1].startTime);
        
        // Remove oldest loggers
        const toRemove = loggers.slice(0, loggers.length - keepLast);
        toRemove.forEach(([key, logger]) => {
            logger.finalize();
        });
        
        console.log(`%cDebugLogger: Cleaned up ${toRemove.length} old loggers, keeping ${keepLast} most recent`, 
                   'color: #f39c12;');
    }
}

export class SimpleLogger {
    
    static DEBUG_ENABLED = false; // Static flag for global debug control
    
    /**
     * SimpleLogger provides global mute/unmute control for debug output.
     * It overrides the global console methods to allow only the active SimpleLogger instance
     * to output to the console. All other console.log/warn/error calls are suppressed unless
     * allowed by the active SimpleLogger.
     *
     * Usage:
     *   const logger = new SimpleLogger();
     *   logger.activate(); // Only this logger's log/warn/error will show in console
     *   logger.log("This will appear");
     *   console.log("This will NOT appear");
     *   logger.deactivate(); // Restores normal console behavior
     */
    static _originalConsole = {
        log: console.log,
        warn: console.warn,
        error: console.error
    };
    static _activeInstance = null;

    /**
     * Create a new SimpleLogger instance
     * @param {boolean} suppressGlobalConsoleMessages - Automatically attach to global console methods. This will suppress all other console output.
     *                                  If false, you must call attachGlobal() manually to enable global control.
     */
    constructor(suppressGlobalConsoleMessages) {
        // Instance-level flag for fine-grained control
        this.enabled = true;
        if (suppressGlobalConsoleMessages) {
            this.supressGlobalConsole(); // Automatically attach to global console if requested
        }
    }

    supressGlobalConsole() {
        SimpleLogger._activeInstance = this;
        // Override global console methods
        console.log = (...args) => {
            if (SimpleLogger._activeInstance === this && this.enabled) {
                SimpleLogger._originalConsole.log.apply(console, args);
            }
        };
        console.warn = (...args) => {
            if (SimpleLogger._activeInstance === this && this.enabled) {
                SimpleLogger._originalConsole.warn.apply(console, args);
            }
        };
        console.error = (...args) => {
            if (SimpleLogger._activeInstance === this && this.enabled) {
                SimpleLogger._originalConsole.error.apply(console, args);
            }
        };
    }

    unsupressGlobalConsole() {
        if (SimpleLogger._activeInstance === this) {
            // Restore original console methods
            console.log = SimpleLogger._originalConsole.log;
            console.warn = SimpleLogger._originalConsole.warn;
            console.error = SimpleLogger._originalConsole.error;
            SimpleLogger._activeInstance = null;
        }
    }

    mute() {
        this.enabled = false;
    }

    unmute() {
        this.enabled = true;
    }

    log(...args) {
        if (SimpleLogger._activeInstance === this && this.enabled) {
            SimpleLogger._originalConsole.log.apply(console, args);
        }
    }

    warn(...args) {
        if (SimpleLogger._activeInstance === this && this.enabled) {
            SimpleLogger._originalConsole.warn.apply(console, args);
        }
    }

    error(...args) {
        if (SimpleLogger._activeInstance === this && this.enabled) {
            SimpleLogger._originalConsole.error.apply(console, args);
        }
    }
    

    static log(...args) {
        if (SimpleLogger.DEBUG_ENABLED) {
            console.log(...args);
        }
    }

    static warn(...args) {
        if (SimpleLogger.DEBUG_ENABLED) {
            console.warn(...args);
        }
    }
    static error(...args) {
        if (SimpleLogger.DEBUG_ENABLED) {
            console.error(...args);
        }
    }

} 

// =============================================================================
// CONVENIENCE FACTORY FUNCTIONS
// =============================================================================

/**
 * Create a new debug logger for an EGPT analysis
 */
export function createEGPTLogger(numberKey) {
    return new DebugLogger(numberKey.toString(), 'EGPT');
}

/**
 * Create a debug logger for crypto operations
 */
export function createCryptoLogger(operation) {
    return new DebugLogger(`crypto-${Date.now()}`, `CRYPTO-${operation.toUpperCase()}`);
}

/**
 * Create a debug logger for general operations
 */
export function createLogger(key, context = 'APP') {
    return new DebugLogger(key, context);
}

// =============================================================================
// WEB APP INTEGRATION HELPERS
// =============================================================================

/**
 * Setup debug logging for web application with UI controls
 */
export function setupWebAppDebugger() {
    // Add console toggle control
    if (typeof window !== 'undefined' && window.document) {
        // Create debug control panel (if not exists)
        let debugPanel = document.getElementById('debug-panel');
        if (!debugPanel) {
            debugPanel = document.createElement('div');
            debugPanel.id = 'debug-panel';
            debugPanel.style.cssText = `
                position: fixed;
                top: 10px;
                right: 10px;
                background: rgba(0,0,0,0.8);
                color: white;
                padding: 10px;
                border-radius: 5px;
                font-family: monospace;
                font-size: 12px;
                z-index: 10000;
                max-width: 300px;
                display: none;
            `;
            document.body.appendChild(debugPanel);
        }

        // Add toggle function to window for console access
        window.toggleDebugConsole = (enabled) => {
            DebugLogger.setConsoleEnabled(enabled);
            updateDebugPanel();
        };

        window.showDebugPanel = () => {
            debugPanel.style.display = 'block';
            updateDebugPanel();
        };

        window.hideDebugPanel = () => {
            debugPanel.style.display = 'none';
        };

        function updateDebugPanel() {
            const summary = DebugLogger.getGlobalSummary();
            debugPanel.innerHTML = `
                <div>🔧 Debug Logger Control</div>
                <div>Console: ${summary.consoleEnabled ? '✅ ON' : '❌ OFF'}</div>
                <div>Active Loggers: ${summary.totalActiveLoggers}</div>
                <div>Total Messages: ${summary.totalMessages}</div>
                <div>Errors: ${summary.totalErrors} | Warnings: ${summary.totalWarnings}</div>
                <button onclick="toggleDebugConsole(!${summary.consoleEnabled})" style="margin-top: 5px;">
                    ${summary.consoleEnabled ? 'Disable' : 'Enable'} Console
                </button>
                <button onclick="hideDebugPanel()" style="margin-left: 5px;">Hide</button>
            `;
        }

        // Global keyboard shortcut (Ctrl+Shift+D)
        document.addEventListener('keydown', (e) => {
            if (e.ctrlKey && e.shiftKey && e.key === 'D') {
                e.preventDefault();
                if (debugPanel.style.display === 'none') {
                    window.showDebugPanel();
                } else {
                    window.hideDebugPanel();
                }
            }
        });
    }

    // Add callback for web app message display
    DebugLogger.addCallback((logEntry, logger) => {
        // Could integrate with web app's message system
        if (logEntry.level === 'ERROR') {
            // Could call showError() function if available
        }
    });

    console.log('%cDebugLogger Web App Integration Ready! Press Ctrl+Shift+D to toggle debug panel', 
               'color: #2ecc71; font-weight: bold;');
}

// Initialize web app integration if in browser environment
if (typeof window !== 'undefined') {
    // Auto-setup on load
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', setupWebAppDebugger);
    } else {
        setupWebAppDebugger();
    }
}

export default DebugLogger;