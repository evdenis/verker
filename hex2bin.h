#ifndef __HEX2BIN__
#define __HEX2BIN__ 1

#include "kernel_definitions.h"
#include "ctype.h"

/**
 * hex_to_bin - convert a hex digit to its real value
 * @ch: ascii character represents hex digit
 *
 * hex_to_bin() converts one hex digit to its actual value or -1 in case of bad
 * input.
 */

/*@ axiomatic HexToBin {
    logic integer hex_to_bin(integer ch);
    axiom A0: hex_to_bin('0') == 0; axiom A1: hex_to_bin('1') == 1; axiom A2: hex_to_bin('2') == 2;
    axiom A3: hex_to_bin('3') == 3; axiom A4: hex_to_bin('4') == 4; axiom A5: hex_to_bin('5') == 5;
    axiom A6: hex_to_bin('6') == 6; axiom A7: hex_to_bin('7') == 7; axiom A8: hex_to_bin('8') == 8;
    axiom A9: hex_to_bin('9') == 9;

    axiom AA: hex_to_bin('a') == hex_to_bin('A') == 10;
    axiom AB: hex_to_bin('b') == hex_to_bin('B') == 11;
    axiom AC: hex_to_bin('c') == hex_to_bin('C') == 12;
    axiom AD: hex_to_bin('d') == hex_to_bin('D') == 13;
    axiom AE: hex_to_bin('e') == hex_to_bin('E') == 14;
    axiom AF: hex_to_bin('f') == hex_to_bin('F') == 15;
    }
 */

/*@ assigns \nothing;
    behavior to_digit:
       assumes isxdigit(ch);
       ensures 0 <= \result <= 15;
       ensures \result == hex_to_bin(ch);
    behavior fail:
       assumes !isxdigit(ch);
       ensures \result == -1;
    complete behaviors;
    disjoint behaviors;
 */
int hex_to_bin(char ch);

/**
 * hex2bin - convert an ascii hexadecimal string to its binary representation
 * @dst: binary result
 * @src: ascii hexadecimal string
 * @count: result length
 *
 * Return 0 on success, -1 in case of bad input.
 */
int hex2bin(u8 *dst, const char *src, size_t count);

#endif