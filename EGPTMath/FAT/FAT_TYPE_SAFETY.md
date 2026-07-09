# FAT Type Safety: Preventing Time/Frequency Domain Confusion

## Problem

The current `fat()` and `ifat()` functions both accept `Array<ComplexEGPTNumber>`, making it easy to accidentally:
- Pass a frequency-domain spectrum to `fat()` (forward transform)
- Pass a time-domain signal to `ifat()` (inverse transform)

This confusion can lead to:
- **Silent bugs**: Wrong transforms that produce incorrect results
- **Debugging difficulty**: Hard to trace where domain confusion occurred
- **Code maintainability**: Unclear intent in function signatures

## Solution: Type-Safe Interfaces

### Core Classes

#### `TimeDomainSignal`
Wraps time-domain data to prevent accidental use in inverse transforms.

```javascript
import { TimeDomainSignal } from './FATInterfaces.js';

const signal = TimeDomainSignal.fromArray([z0, z1, z2, ...]);
```

#### `FrequencyDomainSpectrum`
Wraps frequency-domain data to prevent accidental use in forward transforms.

```javascript
import { FrequencyDomainSpectrum } from './FATInterfaces.js';

const spectrum = FrequencyDomainSpectrum.fromArray([Z0, Z1, Z2, ...]);
```

### Type-Safe Functions

#### `fat_safe(signal)`
- ✅ Accepts: `TimeDomainSignal` or `Array<ComplexEGPTNumber>` (auto-wrapped)
- ❌ Rejects: `FrequencyDomainSpectrum` (throws helpful error)
- Returns: `FrequencyDomainSpectrum`

```javascript
import { fat_safe, TimeDomainSignal } from './EGPTFAT_TypeSafe.js';

const signal = TimeDomainSignal.fromArray([z0, z1, ...]);
const spectrum = fat_safe(signal); // ✓ Type-safe

// Error case:
const wrong = fat_safe(spectrum); // ❌ Throws: "Cannot transform frequency-domain spectrum"
```

#### `ifat_safe(spectrum)`
- ✅ Accepts: `FrequencyDomainSpectrum` or `Array<ComplexEGPTNumber>` (auto-wrapped)
- ❌ Rejects: `TimeDomainSignal` (throws helpful error)
- Returns: `TimeDomainSignal`

```javascript
import { ifat_safe, FrequencyDomainSpectrum } from './EGPTFAT_TypeSafe.js';

const spectrum = FrequencyDomainSpectrum.fromArray([Z0, Z1, ...]);
const signal = ifat_safe(spectrum); // ✓ Type-safe

// Error case:
const wrong = ifat_safe(signal); // ❌ Throws: "Cannot transform time-domain signal"
```

## Benefits

1. **Compile-Time Safety**: TypeScript (future) or runtime checks catch domain confusion
2. **Clear Intent**: Function signatures make domain explicit
3. **Helpful Errors**: Rejection messages guide correct usage
4. **Backward Compatible**: Plain arrays auto-wrap for existing code

## Usage Examples

### Basic Type-Safe Transform

```javascript
import { 
    TimeDomainSignal, 
    FrequencyDomainSpectrum,
    fat_safe, 
    ifat_safe 
} from './EGPTFAT_TypeSafe.js';

// Create time-domain signal
const signal = TimeDomainSignal.fromArray([z0, z1, z2, z3]);

// Forward transform (time → frequency)
const spectrum = fat_safe(signal);

// Inverse transform (frequency → time)
const reconstructed = ifat_safe(spectrum);

// Access data
const spectrumData = spectrum.getData();
const signalData = reconstructed.getData();
```

### Round-Trip Helper

```javascript
import { roundTrip_safe, TimeDomainSignal } from './EGPTFAT_TypeSafe.js';

const signal = TimeDomainSignal.fromArray([z0, z1, ...]);
const { spectrum, reconstructed } = roundTrip_safe(signal);

// Both are properly typed:
// spectrum: FrequencyDomainSpectrum
// reconstructed: TimeDomainSignal
```

### Backward Compatibility

```javascript
// Plain arrays still work (auto-wrapped)
import { fat_safe, ifat_safe } from './EGPTFAT_TypeSafe.js';

const plainArray = [z0, z1, z2, ...];
const spectrum = fat_safe(plainArray); // Auto-wrapped as TimeDomainSignal
const signal = ifat_safe(spectrum.getData()); // Auto-wrapped as FrequencyDomainSpectrum
```

## Error Messages

### Wrong Domain Input to Forward Transform

```javascript
const spectrum = fat_safe(someSignal); // Create spectrum
const wrong = fat_safe(spectrum); // ❌ Error!

// Error message:
// "fat_safe: Cannot transform frequency-domain spectrum.
//   Use ifat_safe() for inverse transform.
//   Did you mean: ifat_safe(input)?"
```

### Wrong Domain Input to Inverse Transform

```javascript
const signal = TimeDomainSignal.fromArray([...]);
const wrong = ifat_safe(signal); // ❌ Error!

// Error message:
// "ifat_safe: Cannot transform time-domain signal.
//   Use fat_safe() for forward transform.
//   Did you mean: fat_safe(input)?"
```

## Migration Path

### Existing Code (No Changes Required)

```javascript
// Still works as before
import { fat, ifat } from './EGPTFAT.js';
const spectrum = fat(signal);
const reconstructed = ifat(spectrum);
```

### New Code (Recommended)

```javascript
// Use type-safe interfaces
import { fat_safe, ifat_safe, TimeDomainSignal } from './EGPTFAT_TypeSafe.js';

const signal = TimeDomainSignal.fromArray(signalData);
const spectrum = fat_safe(signal);
const reconstructed = ifat_safe(spectrum);
```

## Implementation Details

### Auto-Wrapping

Plain arrays are automatically wrapped based on context:
- `fat_safe(array)` → wraps as `TimeDomainSignal`
- `ifat_safe(array)` → wraps as `FrequencyDomainSpectrum`

### Type Guards

```javascript
import { 
    isTimeDomainSignal, 
    isFrequencyDomainSpectrum 
} from './FATInterfaces.js';

if (isTimeDomainSignal(value)) {
    // Value is time-domain
}
```

## Future Enhancements

1. **TypeScript Types**: Full compile-time type safety
2. **Immutable Wrappers**: Prevent accidental mutation
3. **Validation**: Check conjugate symmetry for real signals
4. **Format Converters**: Type-safe format conversions










