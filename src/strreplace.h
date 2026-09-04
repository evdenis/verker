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
    terminates \true;
    assigns s[0..strlen{Pre}(s)-1];
    assigns \result \from s;
    exits \false;
    ensures \result == \at(s,Pre) + strlen{Pre}(s);
    ensures \forall integer i; 0 <= i < strlen{Pre}(s) &&
            \at(s[i], Pre) != old ==> s[i] == \at(s[i], Pre);
    ensures \forall integer i; 0 <= i < strlen{Pre}(s) &&
            \at(s[i], Pre) == old ==> s[i] == new;
    ensures valid_str(s);
    ensures new != '\0' ==> strlen{Pre}(s) == strlen(s);
*/
char *strreplace(char *s, char old, char new);

#endif // __STRREPLACE_H__
