/**
 * CHART.JS VALIDATION AND LOADING HELPER
 * Ensures Chart.js is available before attempting to create charts
 */

/**
 * Wait for Chart.js to be available
 * @returns {Promise<boolean>} - Resolves when Chart.js is loaded
 */
export function waitForChartJS() {
    return new Promise((resolve, reject) => {
        let attempts = 0;
        const maxAttempts = 50; // 5 seconds maximum wait
        
        const checkChart = () => {
            attempts++;
            
            if (typeof window !== 'undefined' && window.Chart) {
                console.log('✅ Chart.js loaded successfully');
                resolve(true);
                return;
            }
            
            if (attempts >= maxAttempts) {
                console.error('❌ Chart.js failed to load within timeout');
                reject(new Error('Chart.js not available after timeout'));
                return;
            }
            
            setTimeout(checkChart, 100);
        };
        
        checkChart();
    });
}

/**
 * Check if Chart.js is immediately available
 * @returns {boolean} - True if Chart.js is loaded
 */
export function isChartJSAvailable() {
    return typeof window !== 'undefined' && window.Chart;
}
