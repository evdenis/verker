#ifndef __STRNCASECMP_H__
#define __STRNCASECMP_H__

#include "kernel_definitions.h"

/**
 * strncasecmp - Case insensitive, length-limited string comparison
 * @s1: One string
 * @s2: The other string
 * @len: the maximum number of characters to compare
 */

int strncasecmp(const char *s1, const char *s2, size_t len);

#endif // __STRNCASECMP_H__