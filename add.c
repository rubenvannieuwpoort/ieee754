#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>
#include <stdlib.h>
#include <math.h>

#include <fenv.h>

#pragma STDC FENV_ACCESS ON



#define ROUND_RTNE 0
#define ROUND_DOWN 1
#define ROUND_UP 2
#define ROUND_TOZERO 3

// START(edit these)

// internal types to hold bitfields, need to have at least P + 3 bits
typedef int32_t int_t;
typedef uint32_t uint_t;

// floating point type
typedef float fp_t;

// sizes of bitfields, need to correspond to that of fp_t
#define E 8
#define P 24

// rounding mode used by the software implementation (ROUND_RTNE ROUND_DOWN ROUND_UP ROUND_TOZERO)
#define ROUND_MODE ROUND_TOZERO

// rounding mode used by the CPU (FE_TONEAREST FE_DOWNWARD FE_UPWARD FE_TOWARDZERO)
#define FE_ROUNDING_MODE FE_TOWARDZERO

// END(edit these)

#define EXPONENT_MASK ((((int_t)1) << E) - 1)
#define FRACTION_MASK ((((int_t)1) << (P - 1)) - 1)
#define BIAS ((((int_t)1) << (E - 1)) - 1)

#define LSB 8
#define G 4
#define R 2
#define S 1

#define IMPLIED_BIT (((int_t)1) << (P + 2))
#define OVERFLOW_BIT (((int_t)1) << (P + 3))

#define MYNAN (pack(0, -1, 1))
#define ZERO (pack(0, 0, 0))



typedef union {
    uint_t as_uint;
    fp_t as_float;
} conv_t;

__uint128_t state = 0;
const __uint128_t multiplier = ((__uint128_t)0xc580caddULL << 64) | 0x754f7336d2eaa27dULL;
uint_t rand_next(void) {
    state *= multiplier;
    state += multiplier;
    return state >> (128 - sizeof(fp_t) * 8);
}

void unpack(fp_t f, int_t *sign, int_t *exponent, int_t *fraction) {
    conv_t conv;
    conv.as_float = f;

    *sign     = (conv.as_uint >> (E + P - 1)) & 1;
    *exponent = (conv.as_uint >> (P - 1)) & EXPONENT_MASK;
    *fraction = conv.as_uint & FRACTION_MASK;
}

fp_t pack(int_t sign, int_t exponent, int_t fraction) {
    conv_t conv;
    conv.as_uint = ((sign & 1) << (E + P - 1)) | ((exponent & EXPONENT_MASK) << (P - 1)) | (fraction & FRACTION_MASK);
    return conv.as_float;
}

bool is_nan(int_t exponent, int_t fraction) {
    return exponent == EXPONENT_MASK && fraction != 0;
}

bool is_inf(int_t exponent, int_t fraction) {
    return exponent == EXPONENT_MASK && fraction == 0;
}

bool is_denormal(int_t exponent) {
    return exponent == 0;
}

int_t mantissa(int_t exponent, int_t fraction) {
    if (is_denormal(exponent)) {
        return fraction;
    } else {
        return (((int_t)1) << (P - 1)) | fraction;
    }
}

fp_t add(fp_t x, fp_t y) {
    int_t x_sign, x_exponent, x_fraction;
    int_t y_sign, y_exponent, y_fraction;
    unpack(x, &x_sign, &x_exponent, &x_fraction);
    unpack(y, &y_sign, &y_exponent, &y_fraction);


    /* handle nans and infs */

    if (is_nan(x_exponent, x_fraction) || is_nan(y_exponent, y_fraction)) {
        return MYNAN;
    }

    if (is_inf(x_exponent, x_fraction) && !is_inf(y_exponent, y_fraction)) {
        return x;
    }

    if (!is_inf(x_exponent, x_fraction) && is_inf(y_exponent, y_fraction)) {
        return y;
    }

    if (is_inf(x_exponent, x_fraction) && is_inf(y_exponent, y_fraction)) {
        if (x_sign == y_sign) {
            return x;
        } else {
            return MYNAN;
        }
    }
                                 
    int_t x_mantissa = mantissa(x_exponent, x_fraction);
    int_t y_mantissa = mantissa(y_exponent, y_fraction);

    if (x_exponent == 0) x_exponent++;
    if (y_exponent == 0) y_exponent++;

    // add G, R, S bits
    x_mantissa = x_mantissa << 3;
    y_mantissa = y_mantissa << 3;

    int shift = x_exponent - y_exponent;

    // while (x_exponent < y_exponent) {
    //     // shift right while maintaining the sticky bit if it's set
    //     x_mantissa = (x_mantissa >> 1) | (x_mantissa & 1);
    //     x_exponent++;
    // }

    // while (y_exponent < x_exponent) {
    //     // shift right while maintaining the sticky bit if it's set
    //     y_mantissa = (y_mantissa >> 1) | (y_mantissa & 1);
    //     y_exponent++;
    // }

    if (shift > 0) {
        if (shift > (P + 2)) {
            shift = P + 2;
        }

        int_t sign_bit = (y_mantissa & ((((int_t)1) << shift) - 1)) ? 1 : 0;
        y_mantissa = (y_mantissa >> shift) | sign_bit;
        y_exponent = x_exponent;
    }

    if (shift < 0) {
        shift = -shift;
        
        if (shift > (P + 2)) {
            shift = P + 2;
        }

        int_t sign_bit = (x_mantissa & ((((int_t)1) << shift) - 1)) ? 1 : 0;
        x_mantissa = (x_mantissa >> shift) | sign_bit;
        x_exponent = y_exponent;
    }

    assert(x_exponent == y_exponent);
    
    bool subtract = x_sign != y_sign;
    int_t z_exponent = x_exponent, z_mantissa = subtract ? x_mantissa - y_mantissa : x_mantissa + y_mantissa;

    if (z_mantissa == 0) {
        return ZERO;
    }

    int_t z_sign = x_sign;
    if (z_mantissa < 0) {
        z_mantissa = -z_mantissa;
        z_sign = 1 - z_sign;
    }

    // right shift on overflow
    if (z_mantissa & OVERFLOW_BIT) {
        z_mantissa = (z_mantissa >> 1) | (z_mantissa & 1);
        z_exponent++;
    }

    // normalize
    while ((z_mantissa & IMPLIED_BIT) == 0) {
        z_mantissa = z_mantissa << 1;
        z_exponent--;
    }

    if (ROUND_MODE == ROUND_RTNE) {
        // round to nearest, ties to even
        // if G & (R | S) we need to round up to nearest
        // if G & !(R | S) we are exactly halfway; if LSB is set we're odd so need to round up to even
        if ((z_mantissa & G) && ((z_mantissa & R) || (z_mantissa & S) || (z_mantissa & LSB))) {
            // round up
            z_mantissa += LSB;
        }
    } else if (ROUND_MODE == ROUND_DOWN) {
        // round down
        if (z_sign != 0 && ((z_mantissa & G) || (z_mantissa & R) || (z_mantissa & S))) {
            z_mantissa += LSB;
        }
    } else if (ROUND_MODE == ROUND_UP) {
        // round down
        if (z_sign == 0 && ((z_mantissa & G) || (z_mantissa & R) || (z_mantissa & S))) {
            z_mantissa += LSB;
        }
    } else if (ROUND_MODE == ROUND_TOZERO) {
        // discard fractional bits
    }

    // denormalize
    z_mantissa >>= 3;

    if (z_mantissa & (((int_t)1) << P)) {
        // overflow, need to right-shift an extra bit to normalize
        z_mantissa = z_mantissa >> 1;
        z_exponent += 1;
    }

    assert(z_mantissa & (((int_t)1) << (P - 1)));

    if (sizeof(fp_t) == 4) {
        fp_t mantissa = ldexpf((fp_t)z_mantissa, -(P - 1));
        return ldexpf(z_sign ? -mantissa : mantissa, z_exponent - BIAS);
    }

    assert(sizeof(fp_t) == 8);
    fp_t mantissa = ldexp((fp_t)z_mantissa, -(P - 1));
    return ldexp(z_sign ? -mantissa : mantissa, z_exponent - BIAS);
}

float to_float(uint_t x) {
    conv_t c;
    c.as_uint = x;
    return c.as_float;
}

bool float_is_nan(fp_t x) {
    int_t x_sign, x_exponent, x_fraction;
    unpack(x, &x_sign, &x_exponent, &x_fraction);
    return is_nan(x_exponent, x_fraction);
}

bool float_is_inf(fp_t x) {
    int_t x_sign, x_exponent, x_fraction;
    unpack(x, &x_sign, &x_exponent, &x_fraction);
    return is_inf(x_exponent, x_fraction);
}

bool float_is_denormal(fp_t x) {
    int_t x_sign, x_exponent, x_fraction;
    unpack(x, &x_sign, &x_exponent, &x_fraction);
    return is_denormal(x_exponent);
}

void test(void) {
    // run 100 million random test cases
    for (int i = 0; i < 100000000; i++) {
        fp_t x = to_float(rand_next()), y = to_float(rand_next());

        fp_t got = add(x, y);
        fp_t expected = x + y;

        if (expected > 0 && !(got == expected || (isnan(got) && isnan(expected)))) {
            printf("got %g\nexpected %g\n", got, expected);
            fflush(stdout);

            int_t e_sign, e_exponent, e_fraction;
            unpack(expected, &e_sign, &e_exponent, &e_fraction);
            int_t e_mantissa = mantissa(e_exponent, e_fraction);

            int_t g_sign, g_exponent, g_fraction;
            unpack(got, &g_sign, &g_exponent, &g_fraction);
            int_t g_mantissa = mantissa(g_exponent, g_fraction);

            add(x, y);
            exit(1);
        }
    }
}

int main(int argc, char *argv[]) {
    fesetround(FE_ROUNDING_MODE);
    test();
    return 0;
}
