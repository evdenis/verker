#ifndef __STRSTR_H__
#define __STRSTR_H__

#include "kernel_definitions.h"
//#include "memcmp.h"
#include "strlen.h"

/**
 * strstr - Find the first substring in a %NUL terminated string
 * @s1: The string to be searched
 * @s2: The string to search for
 */

char *strstr(const char *s1, const char *s2);

#endif // __STRSTR_H__
