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

char *strreplace(char *s, char old, char new);

#endif // __STRREPLACE_H__