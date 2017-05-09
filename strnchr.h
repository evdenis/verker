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
    assigns \nothing;
    behavior exists:
       assumes \exists char *p; s <= p < s + strnlen(s, count) && *p == (char %) c;
       ensures s <= \result <= s + strnlen(s, count);
       ensures *\result == (char %) c;
       ensures \forall char *p; s <= p < \result ==> *p != (char %) c;
    behavior not_exists:
       assumes \forall char *p; s <= p < s + strnlen(s, count) ==> *p != (char %) c;
       ensures \result == \null;
    complete behaviors;
    disjoint behaviors;
 */
char *strnchr(const char *s, size_t count, int c);

#endif // __STRNCHR_H__