#ifndef __STRREPLACE_H__
#define __STRREPLACE_H__

#include "strlen.h"

/**
 * strreplace - Replace all occurrences of character in string.
 * @s: The string to operate on.
 * @old: The character being replaced.
 * @new: The character @old is replaced with.
 *
 * Returns pointer to the nul byte at the end of @s.
 */

/*@ requires valid_str(s);
    assigns s[0..strlen{Pre}(s)-1];
    ensures \result == \at(s,Pre) + strlen{Pre}(s);
    ensures \forall char *k; s <= k < s + strlen{Pre}(s) &&
            (\at(*k, Pre) != old) ==> *k == \at(*k, Pre);
    ensures \forall char *k; s <= k < s + strlen{Pre}(s) &&
            (\at(*k, Pre) == old) ==> *k == new;
    ensures valid_str(s);
    ensures new != '\0' ==> strlen{Pre}(s) == strlen(s);
*/
char *strreplace(char *s, char old, char new);

#endif // __STRREPLACE_H__
