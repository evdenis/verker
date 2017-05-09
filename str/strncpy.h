#ifndef __STRNCPY_H__
#define __STRNCPY_H__

#include "kernel_definitions.h"
#include "strnlen.h"

/**
 * strncpy - Copy a length-limited, C-string
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 * @count: The maximum number of bytes to copy
 *
 * The result is not %NUL-terminated if the source exceeds
 * @count bytes.
 *
 * In the case where the length of @src is less than  that  of
 * count, the remainder of @dest will be padded with %NUL.
 *
 */

char *strncpy(char *dest, const char *src, size_t count);

#endif // __STRNCPY_H__