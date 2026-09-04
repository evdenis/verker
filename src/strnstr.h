#ifndef __STRNSTR_H__
#define __STRNSTR_H__

#include "kernel_definitions.h"
#include "memcmp.h"
#include "strlen.h"

/**
 * strnstr - Find the first substring in a length-limited string
 * @s1: The string to be searched
 * @s2: The string to search for
 * @len: the maximum number of characters to search
 */

/*@ requires \valid_read(s1+(0..len-1));
    requires valid_str(s2);
    requires strlen(s2) <= LONG_MAX;
    terminates \true;
    assigns \result \from s1, s2, len;
    exits \false;
    ensures \result == \null || (0 <= \result - s1 <= len);
 */
char *strnstr(const char *s1, const char *s2, size_t len);

#endif // __STRNSTR_H__