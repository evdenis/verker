#ifndef __STRPBRK_H__
#define __STRPBRK_H__

#include "kernel_definitions.h"
#include "strlen.h"

/**
 * strpbrk - Find the first occurrence of a set of characters
 * @cs: The string to be searched
 * @ct: The characters to search for
 */

char *strpbrk(const char *cs, const char *ct);

#endif // __STRPBRK_H__