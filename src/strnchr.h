#ifndef __STRNCHR_H__
#define __STRNCHR_H__

#include "kernel_definitions.h"
#include "strnlen.h"

/**
 * strnchr - Find a character in a length limited string
 * @s: The string to be searched
 * @count: The number of characters to be searched
 * @c: The character to search for
 */

/*@ requires valid_strn(s, count);
    requires count <= LONG_MAX;
    terminates \true;
    assigns \result \from s, count, c;
    exits \false;
    behavior exists:
       assumes \exists integer i; 0 <= i < strnlen(s, count) && s[i] == (char) c;
       ensures 0 <= \result - s < strnlen(s, count);
       ensures *\result == (char) c;
       ensures \forall integer i; 0 <= i < \result - s ==> s[i] != (char) c;
    behavior not_exists:
       assumes \forall integer i; 0 <= i < strnlen(s, count) ==> s[i] != (char) c;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strnchr(const char *s, size_t count, int c);

#endif // __STRNCHR_H__
