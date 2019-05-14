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

char *strnstr(const char *s1, const char *s2, size_t len);

#endif // __STRNSTR_H__