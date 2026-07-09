// =============================================================================
// TYPE-SAFE FAT INTERFACE: Preventing Domain Confusion
// =============================================================================

import { fat as EQFT_CANONICAL, ifat as IEQFT_CANONICAL } from './EGPTFAT.js';

function isPowerOfTwo(n) {
    return n > 0 && (n & (n - 1)) === 0;
}
import { 
    TimeDomainSignal, 
    FrequencyDomainSpectrum,
    wrapForDomain,
    isTimeDomainSignal,
    isFrequencyDomainSpectrum
} from './FATInterfaces.js';

/**
 * 🎯 TYPE-SAFE FAT: Forward Abadir Transform
 * 
 * Transforms TimeDomainSignal → FrequencyDomainSpectrum
 * 
 * **Type Safety:**
 * - ✅ Accepts: TimeDomainSignal (wrapped)
 * - ✅ Accepts: Array<ComplexEGPTNumber> (auto-wrapped for backward compatibility)
 * - ❌ Rejects: FrequencyDomainSpectrum (would cause confusion!)
 * 
 * @param {TimeDomainSignal|Array<ComplexEGPTNumber>} input - Time-domain signal
 * @returns {FrequencyDomainSpectrum} Frequency-domain spectrum
 * 
 * @example
 * ```javascript
 * import { fat_safe, TimeDomainSignal } from './EGPTFAT_TypeSafe.js';
 * 
 * const signal = TimeDomainSignal.fromArray([z0, z1, z2, ...]);
 * const spectrum = fat_safe(signal); // ✓ Type-safe
 * ```
 * 
 * @throws {Error} If input is a FrequencyDomainSpectrum (wrong domain)
 */
export function fat_safe(input) {
    // Reject frequency-domain input (common mistake)
    if (isFrequencyDomainSpectrum(input)) {
        throw new Error(
            'fat_safe: Cannot transform frequency-domain spectrum.\n' +
            '  Use ifat_safe() for inverse transform.\n' +
            '  Did you mean: ifat_safe(input)?'
        );
    }
    
    // Wrap plain arrays for backward compatibility
    const signal = isTimeDomainSignal(input) 
        ? input 
        : wrapForDomain(input, 'time');
    
    const N = signal.getLength();
    if (!isPowerOfTwo(N)) {
        throw new Error(`fat_safe: Requires power-of-2 input length, got ${N}`);
    }
    
    // Perform forward transform
    const spectrumData = EQFT_CANONICAL(signal.getData());
    
    // Return wrapped frequency-domain spectrum
    return FrequencyDomainSpectrum.fromArray(spectrumData);
}

/**
 * 🎯 TYPE-SAFE IFAT: Inverse Abadir Transform
 * 
 * Transforms FrequencyDomainSpectrum → TimeDomainSignal
 * 
 * **Type Safety:**
 * - ✅ Accepts: FrequencyDomainSpectrum (wrapped)
 * - ✅ Accepts: Array<ComplexEGPTNumber> (auto-wrapped for backward compatibility)
 * - ❌ Rejects: TimeDomainSignal (would cause confusion!)
 * 
 * @param {FrequencyDomainSpectrum|Array<ComplexEGPTNumber>} input - Frequency-domain spectrum
 * @param {boolean} normalize - Apply 1/N normalization (default: true)
 * @returns {TimeDomainSignal} Time-domain signal
 * 
 * @example
 * ```javascript
 * import { ifat_safe, FrequencyDomainSpectrum } from './EGPTFAT_TypeSafe.js';
 * 
 * const spectrum = FrequencyDomainSpectrum.fromArray([Z0, Z1, Z2, ...]);
 * const signal = ifat_safe(spectrum); // ✓ Type-safe
 * ```
 * 
 * @throws {Error} If input is a TimeDomainSignal (wrong domain)
 */
export function ifat_safe(input, normalize = true) {
    // Reject time-domain input (common mistake)
    if (isTimeDomainSignal(input)) {
        throw new Error(
            'ifat_safe: Cannot transform time-domain signal.\n' +
            '  Use fat_safe() for forward transform.\n' +
            '  Did you mean: fat_safe(input)?'
        );
    }
    
    // Wrap plain arrays for backward compatibility
    const spectrum = isFrequencyDomainSpectrum(input)
        ? input
        : wrapForDomain(input, 'frequency');
    
    const N = spectrum.getLength();
    if (!isPowerOfTwo(N)) {
        throw new Error(`ifat_safe: Requires power-of-2 input length, got ${N}`);
    }
    
    // Perform inverse transform
    const signalData = IEQFT_CANONICAL(spectrum.getData(), normalize);
    
    // Return wrapped time-domain signal
    return TimeDomainSignal.fromArray(signalData);
}

/**
 * 🎯 TYPE-SAFE ROUND-TRIP: Transform cycle with type safety
 * 
 * @param {TimeDomainSignal|Array<ComplexEGPTNumber>} signal - Time-domain input
 * @returns {{spectrum: FrequencyDomainSpectrum, reconstructed: TimeDomainSignal}} Results
 * 
 * @example
 * ```javascript
 * import { roundTrip_safe, TimeDomainSignal } from './EGPTFAT_TypeSafe.js';
 * 
 * const signal = TimeDomainSignal.fromArray([z0, z1, ...]);
 * const { spectrum, reconstructed } = roundTrip_safe(signal);
 * // Both are properly typed!
 * ```
 */
export function roundTrip_safe(signal) {
    const spectrum = fat_safe(signal);
    const reconstructed = ifat_safe(spectrum, true);
    return { spectrum, reconstructed };
}

/**
 * 🎯 BACKWARD COMPATIBILITY: Export original functions with type checking
 */

/**
 * Enhanced fat() with optional type checking
 * 
 * @param {TimeDomainSignal|Array<ComplexEGPTNumber>} input - Time-domain signal
 * @param {Object} options - Optional configuration
 * @param {boolean} options.strictTypes - Enable strict type checking (default: false for backward compatibility)
 * @returns {FrequencyDomainSpectrum|Array<ComplexEGPTNumber>} Frequency-domain spectrum
 */
export function fat_enhanced(input, options = {}) {
    const { strictTypes = false } = options;
    
    if (strictTypes) {
        return fat_safe(input);
    }
    
    // Original behavior: return plain array
    const signal = isTimeDomainSignal(input) ? input.getData() : input;
    const spectrum = EQFT_CANONICAL(signal);
    return spectrum;
}

/**
 * Enhanced ifat() with optional type checking
 * 
 * @param {FrequencyDomainSpectrum|Array<ComplexEGPTNumber>} input - Frequency-domain spectrum
 * @param {boolean|Object} normalizeOrOptions - Normalization flag or options object
 * @returns {TimeDomainSignal|Array<ComplexEGPTNumber>} Time-domain signal
 */
export function ifat_enhanced(input, normalizeOrOptions = true) {
    const options = typeof normalizeOrOptions === 'object' 
        ? normalizeOrOptions 
        : { normalize: normalizeOrOptions, strictTypes: false };
    
    const { normalize = true, strictTypes = false } = options;
    
    if (strictTypes) {
        return ifat_safe(input, normalize);
    }
    
    // Original behavior: return plain array
    const spectrum = isFrequencyDomainSpectrum(input) ? input.getData() : input;
    const signal = IEQFT_CANONICAL(spectrum, normalize);
    return signal;
}










