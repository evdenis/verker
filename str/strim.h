#ifndef __STRIM_H__
#define __STRIM_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "skip_spaces.h"

/**
 * strim - Removes leading and trailing whitespace from @s.
 * @s: The string to be stripped.
 *
 * Note that the first trailing whitespace is replaced with a %NUL-terminator
 * in the given string @s. Returns a pointer to the first non-whitespace
 * character in @s.
 */

char *strim(char *s);

#endif // __STRIM_H__