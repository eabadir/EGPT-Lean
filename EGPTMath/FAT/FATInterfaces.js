// =============================================================================
// FAT TYPE-SAFE INTERFACES: Preventing Time/Frequency Domain Confusion
// =============================================================================

import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';

/**
 * 🎯 TIME DOMAIN SIGNAL: Wrapper for time-domain data
 * 
 * Prevents accidental passing of frequency-domain spectra to forward transforms.
 * 
 * @example
 * ```javascript
 * import { TimeDomainSignal, fat, ifat } from './EGPTFAT.js';
 * 
 * const signal = TimeDomainSignal.fromArray([z0, z1, z2, ...]);
 * const spectrum = fat(signal); // ✓ Type-safe
 * const reconstructed = ifat(spectrum); // ✓ Type-safe
 * ```
 */
export class TimeDomainSignal {
    /** @type {Array<ComplexEGPTNumber>} */
    _data;
    /** @type {number} */
    _length;
    
    /**
     * Create a time-domain signal from an array
     * 
     * @param {Array<ComplexEGPTNumber>} data - Time-domain samples
     * @returns {TimeDomainSignal} Wrapped time-domain signal
     */
    static fromArray(data) {
        if (!Array.isArray(data)) {
            throw new Error('TimeDomainSignal.fromArray: Input must be an array');
        }
        const instance = new TimeDomainSignal();
        instance._data = data;
        instance._length = data.length;
        return instance;
    }
    
    /**
     * Get the underlying array data
     * 
     * @returns {Array<ComplexEGPTNumber>} Time-domain samples
     */
    getData() {
        return this._data;
    }
    
    /**
     * Get the length of the signal
     * 
     * @returns {number} Number of samples
     */
    getLength() {
        return this._length;
    }
    
    /**
     * Convert to plain array (for compatibility)
     * 
     * @returns {Array<ComplexEGPTNumber>} Time-domain samples
     */
    toArray() {
        return [...this._data];
    }
    
    /**
     * Get element at index
     * 
     * @param {number} index - Sample index
     * @returns {ComplexEGPTNumber} Sample value
     */
    at(index) {
        return this._data[index];
    }
    
    /**
     * String representation
     * 
     * @returns {string} Descriptive string
     */
    toString() {
        return `TimeDomainSignal(length=${this._length})`;
    }
}

/**
 * 🎯 FREQUENCY DOMAIN SPECTRUM: Wrapper for frequency-domain data
 * 
 * Prevents accidental passing of time-domain signals to inverse transforms.
 * 
 * @example
 * ```javascript
 * import { FrequencyDomainSpectrum, fat, ifat } from './EGPTFAT.js';
 * 
 * const spectrum = FrequencyDomainSpectrum.fromArray([Z0, Z1, Z2, ...]);
 * const signal = ifat(spectrum); // ✓ Type-safe
 * ```
 */
export class FrequencyDomainSpectrum {
    /** @type {Array<ComplexEGPTNumber>} */
    _data;
    /** @type {number} */
    _length;
    
    /**
     * Create a frequency-domain spectrum from an array
     * 
     * @param {Array<ComplexEGPTNumber>} data - Frequency-domain coefficients
     * @returns {FrequencyDomainSpectrum} Wrapped frequency-domain spectrum
     */
    static fromArray(data) {
        if (!Array.isArray(data)) {
            throw new Error('FrequencyDomainSpectrum.fromArray: Input must be an array');
        }
        const instance = new FrequencyDomainSpectrum();
        instance._data = data;
        instance._length = data.length;
        return instance;
    }
    
    /**
     * Get the underlying array data
     * 
     * @returns {Array<ComplexEGPTNumber>} Frequency-domain coefficients
     */
    getData() {
        return this._data;
    }
    
    /**
     * Get the length of the spectrum
     * 
     * @returns {number} Number of frequency bins
     */
    getLength() {
        return this._length;
    }
    
    /**
     * Convert to plain array (for compatibility)
     * 
     * @returns {Array<ComplexEGPTNumber>} Frequency-domain coefficients
     */
    toArray() {
        return [...this._data];
    }
    
    /**
     * Get element at index
     * 
     * @param {number} index - Frequency bin index
     * @returns {ComplexEGPTNumber} Frequency coefficient
     */
    at(index) {
        return this._data[index];
    }
    
    /**
     * String representation
     * 
     * @returns {string} Descriptive string
     */
    toString() {
        return `FrequencyDomainSpectrum(length=${this._length})`;
    }
}

/**
 * 🎯 TYPE GUARDS: Runtime checks for domain safety
 */

/**
 * Check if value is a TimeDomainSignal
 * 
 * @param {*} value - Value to check
 * @returns {boolean} True if TimeDomainSignal instance
 */
export function isTimeDomainSignal(value) {
    return value instanceof TimeDomainSignal;
}

/**
 * Check if value is a FrequencyDomainSpectrum
 * 
 * @param {*} value - Value to check
 * @returns {boolean} True if FrequencyDomainSpectrum instance
 */
export function isFrequencyDomainSpectrum(value) {
    return value instanceof FrequencyDomainSpectrum;
}

/**
 * 🎯 BACKWARD COMPATIBILITY: Auto-wrap plain arrays
 */

/**
 * Wrap value as appropriate domain type
 * 
 * If already wrapped, returns as-is.
 * If plain array, wraps based on context hint.
 * 
 * @param {*} value - Value to wrap
 * @param {'time'|'frequency'} domain - Domain hint
 * @returns {TimeDomainSignal|FrequencyDomainSpectrum} Wrapped value
 */
export function wrapForDomain(value, domain) {
    if (isTimeDomainSignal(value) || isFrequencyDomainSpectrum(value)) {
        return value; // Already wrapped
    }
    
    if (Array.isArray(value)) {
        if (domain === 'time') {
            return TimeDomainSignal.fromArray(value);
        } else if (domain === 'frequency') {
            return FrequencyDomainSpectrum.fromArray(value);
        } else {
            throw new Error(`wrapForDomain: domain must be 'time' or 'frequency', got ${domain}`);
        }
    }
    
    throw new Error(`wrapForDomain: Cannot wrap value of type ${typeof value}`);
}










