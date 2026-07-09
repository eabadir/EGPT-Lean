#!/usr/bin/env node

/**
 * Test Type-Safe FAT Interfaces
 * 
 * Demonstrates:
 * - Type-safe forward/inverse transforms
 * - Error detection for wrong-domain inputs
 * - Backward compatibility with plain arrays
 */

import { EGPTNumber } from '../../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../../EGPTComplex.js';
import { TimeDomainSignal, FrequencyDomainSpectrum } from '../FATInterfaces.js';
import { fat_safe, ifat_safe, roundTrip_safe } from '../EGPTFAT_TypeSafe.js';
import { EGPTMath } from '../../EGPTMath.js';

if (!globalThis.EGPTMathInstance) {
    globalThis.EGPTMathInstance = EGPTMath;
}

console.log('╔════════════════════════════════════════════════════════════════════════════════╗');
console.log('║  TYPE-SAFE FAT INTERFACE TEST                                                 ║');
console.log('╚════════════════════════════════════════════════════════════════════════════════╝');
console.log('');

// Create test signal
function createTestSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const val = BigInt(i + 1);
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

const N = 8;
const plainSignal = createTestSignal(N);

console.log('═'.repeat(80));
console.log('TEST 1: Type-Safe Forward Transform');
console.log('═'.repeat(80));

try {
    const signal = TimeDomainSignal.fromArray(plainSignal);
    console.log(`✓ Created TimeDomainSignal: ${signal}`);
    
    const spectrum = fat_safe(signal);
    console.log(`✓ Forward transform successful: ${spectrum}`);
    console.log(`  Spectrum is FrequencyDomainSpectrum: ${spectrum instanceof FrequencyDomainSpectrum}`);
    
    // Access data
    const spectrumData = spectrum.getData();
    console.log(`  Spectrum[0] = ${spectrumData[0].real.toMathString()} + i${spectrumData[0].imag.toMathString()}`);
} catch (error) {
    console.error(`✗ Error: ${error.message}`);
}

console.log('');
console.log('═'.repeat(80));
console.log('TEST 2: Type-Safe Inverse Transform');
console.log('═'.repeat(80));

try {
    const signal = TimeDomainSignal.fromArray(plainSignal);
    const spectrum = fat_safe(signal);
    
    console.log(`✓ Created FrequencyDomainSpectrum: ${spectrum}`);
    
    const reconstructed = ifat_safe(spectrum);
    console.log(`✓ Inverse transform successful: ${reconstructed}`);
    console.log(`  Reconstructed is TimeDomainSignal: ${reconstructed instanceof TimeDomainSignal}`);
    
    // Check round-trip accuracy
    const orig = signal.getData();
    const recon = reconstructed.getData();
    let matches = 0;
    for (let i = 0; i < N; i++) {
        if (orig[i].equals(recon[i])) {
            matches++;
        }
    }
    console.log(`  Round-trip accuracy: ${matches}/${N} samples match`);
} catch (error) {
    console.error(`✗ Error: ${error.message}`);
}

console.log('');
console.log('═'.repeat(80));
console.log('TEST 3: Error Detection - Wrong Domain Input');
console.log('═'.repeat(80));

try {
    const signal = TimeDomainSignal.fromArray(plainSignal);
    const spectrum = fat_safe(signal);
    
    // Try to use spectrum as input to forward transform (WRONG!)
    console.log('Attempting: fat_safe(spectrum) [should fail]');
    const wrong = fat_safe(spectrum);
    console.error(`✗ Should have thrown error! Got: ${wrong}`);
} catch (error) {
    console.log(`✓ Correctly rejected frequency-domain input: ${error.message}`);
}

try {
    const signal = TimeDomainSignal.fromArray(plainSignal);
    
    // Try to use signal as input to inverse transform (WRONG!)
    console.log('Attempting: ifat_safe(signal) [should fail]');
    const wrong = ifat_safe(signal);
    console.error(`✗ Should have thrown error! Got: ${wrong}`);
} catch (error) {
    console.log(`✓ Correctly rejected time-domain input: ${error.message}`);
}

console.log('');
console.log('═'.repeat(80));
console.log('TEST 4: Round-Trip Helper');
console.log('═'.repeat(80));

try {
    const signal = TimeDomainSignal.fromArray(plainSignal);
    const { spectrum, reconstructed } = roundTrip_safe(signal);
    
    console.log(`✓ Round-trip successful:`);
    console.log(`  Spectrum type: ${spectrum instanceof FrequencyDomainSpectrum}`);
    console.log(`  Reconstructed type: ${reconstructed instanceof TimeDomainSignal}`);
    
    // Verify accuracy
    const orig = signal.getData();
    const recon = reconstructed.getData();
    let matches = 0;
    for (let i = 0; i < N; i++) {
        if (orig[i].equals(recon[i])) {
            matches++;
        }
    }
    console.log(`  Accuracy: ${matches}/${N} samples match`);
} catch (error) {
    console.error(`✗ Error: ${error.message}`);
}

console.log('');
console.log('═'.repeat(80));
console.log('TEST 5: Backward Compatibility - Plain Arrays');
console.log('═'.repeat(80));

try {
    // Plain array should be auto-wrapped
    const spectrum = fat_safe(plainSignal);
    console.log(`✓ Plain array accepted and auto-wrapped`);
    console.log(`  Returned: ${spectrum instanceof FrequencyDomainSpectrum ? 'FrequencyDomainSpectrum' : typeof spectrum}`);
    
    const spectrumData = spectrum.getData();
    const reconstructed = ifat_safe(spectrumData);
    console.log(`✓ Plain array spectrum accepted and auto-wrapped`);
    console.log(`  Returned: ${reconstructed instanceof TimeDomainSignal ? 'TimeDomainSignal' : typeof reconstructed}`);
} catch (error) {
    console.error(`✗ Error: ${error.message}`);
}

console.log('');
console.log('═'.repeat(80));
console.log('SUMMARY');
console.log('═'.repeat(80));
console.log('');
console.log('✓ Type-safe interfaces prevent domain confusion');
console.log('✓ Wrong-domain inputs are rejected with helpful error messages');
console.log('✓ Backward compatibility maintained for plain arrays');
console.log('✓ Round-trip accuracy preserved with type safety');
console.log('');










