// =============================================================================
// Test Suite for EGPTFAT_PurePPF
// Tests the optimized pure PPF implementation with native bit encoding
// =============================================================================

import { EGPTNumber } from '../../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../../EGPTComplex.js';
import { fat_pureppf, ifat_pureppf, isPowerOfTwo } from '../EGPTFAT_PurePPF.js';
import { fat, ifat } from '../EGPTFAT.js';

/**
 * Create a simple test signal (impulse at index 0)
 */
function createImpulseSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        if (i === 0) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(BigInt(N)),
                EGPTNumber.fromBigInt(0n)
            ));
        } else {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(0n),
                EGPTNumber.fromBigInt(0n)
            ));
        }
    }
    return signal;
}

/**
 * Compare two ComplexEGPTNumber arrays for equality
 */
function arraysEqual(a, b, tolerance = 0.0001) {
    if (a.length !== b.length) return false;
    
    for (let i = 0; i < a.length; i++) {
        const a_real = a[i].real._getPPFRationalParts();
        const a_imag = a[i].imag._getPPFRationalParts();
        const b_real = b[i].real._getPPFRationalParts();
        const b_imag = b[i].imag._getPPFRationalParts();
        
        // Cross multiply to test equality: a/b = c/d iff a*d = b*c
        const real_eq = (a_real.numerator * b_real.denominator) === (b_real.numerator * a_real.denominator);
        const imag_eq = (a_imag.numerator * b_imag.denominator) === (b_imag.numerator * a_imag.denominator);
        
        if (!real_eq || !imag_eq) {
            return false;
        }
    }
    return true;
}

/**
 * Test basic functionality
 */
function testBasicFunctionality() {
    console.log('\n🧪 Testing Basic Functionality...');
    
    const sizes = [2, 4, 8, 16];
    let passed = 0;
    let failed = 0;
    
    for (const N of sizes) {
        try {
            // Create impulse signal
            const signal = createImpulseSignal(N);
            
            // Forward transform
            const spectrum_pure = fat_pureppf(signal);
            const spectrum_canonical = fat(signal);
            
            // Compare outputs
            if (arraysEqual(spectrum_pure, spectrum_canonical)) {
                console.log(`  ✅ N=${N}: Forward transform matches canonical`);
                passed++;
            } else {
                console.log(`  ❌ N=${N}: Forward transform differs from canonical`);
                failed++;
            }
            
            // Round-trip test
            const recovered_pure = ifat_pureppf(spectrum_pure, true);
            if (arraysEqual(recovered_pure, signal)) {
                console.log(`  ✅ N=${N}: Round-trip test passes`);
                passed++;
            } else {
                console.log(`  ❌ N=${N}: Round-trip test fails`);
                failed++;
            }
        } catch (error) {
            console.log(`  ❌ N=${N}: Error - ${error.message}`);
            failed++;
        }
    }
    
    console.log(`\n📊 Results: ${passed} passed, ${failed} failed`);
    return failed === 0;
}

/**
 * Test edge cases
 */
function testEdgeCases() {
    console.log('\n🧪 Testing Edge Cases...');
    
    let passed = 0;
    let failed = 0;
    
    try {
        // Test power-of-2 validation
        if (!isPowerOfTwo(2)) {
            console.log('  ❌ isPowerOfTwo(2) should return true');
            failed++;
        } else {
            passed++;
        }
        
        if (isPowerOfTwo(3)) {
            console.log('  ❌ isPowerOfTwo(3) should return false');
            failed++;
        } else {
            passed++;
        }
        
        // Test N=1 (base case)
        const one = [new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(1n),
            EGPTNumber.fromBigInt(0n)
        )];
        const result = fat_pureppf(one);
        if (result.length === 1 && arraysEqual(result, one)) {
            console.log('  ✅ N=1 base case works');
            passed++;
        } else {
            console.log('  ❌ N=1 base case fails');
            failed++;
        }
        
    } catch (error) {
        console.log(`  ❌ Edge case test error: ${error.message}`);
        failed++;
    }
    
    console.log(`\n📊 Results: ${passed} passed, ${failed} failed`);
    return failed === 0;
}

/**
 * Run all tests
 */
function runTests() {
    console.log('🚀 Starting EGPTFAT_PurePPF Test Suite');
    console.log('='.repeat(50));
    
    const basicOk = testBasicFunctionality();
    const edgeOk = testEdgeCases();
    
    console.log('\n' + '='.repeat(50));
    if (basicOk && edgeOk) {
        console.log('✅ All tests passed!');
        return 0;
    } else {
        console.log('❌ Some tests failed');
        return 1;
    }
}

// Run tests if executed directly
if (import.meta.url === `file://${process.argv[1]}`) {
    process.exit(runTests());
}

export { testBasicFunctionality, testEdgeCases, runTests };










