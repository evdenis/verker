#pragma once

/*@ axiomatic IntBase {
    predicate is_hex(char *s) = s[0] == '0' && tolower(s[1]) == 'x' && isxdigit(s[2]);
    predicate is_oct(char *s) = s[0] == '0' && !is_hex(s);
    predicate is_dec(char *s) = !is_hex(s) && !is_oct(s);
    }
 */

/*@ requires \valid(s+(0..2));
    requires \valid(base);
    assigns *base;
    ensures \result == s || \result == s + 2;
    behavior guess:
       assumes *base == 0;
       ensures is_hex(s) ==> *base == 16;
       ensures is_oct(s) ==> *base == 8;
       ensures is_dec(s) ==> *base == 10;
       ensures is_hex(s) ==> \result == s + 2;
       ensures is_oct(s) || is_dec(s) ==> \result == s;
    behavior shift:
       assumes *base == 16 && s[0] == '0' && tolower(s[1]) == 'x';
       ensures \result == \old(s) + 2;
 */
const char *_parse_integer_fixup_radix(const char *s, unsigned int *base);
