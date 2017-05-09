#ifndef __STRLCPY_H__
#define __STRLCPY_H__

#include "kernel_definitions.h"
#include "strlen.h"

/**
 * strlcpy - Copy a C-string into a sized buffer
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 * @size: size of destination buffer
 *
 * Compatible with *BSD: the result is always a valid
 * NUL-terminated string that fits in the buffer (unless,
 * of course, the buffer size is zero). It does not pad
 * out the result like strncpy() does.
 */

size_t strlcpy(char *dest, const char *src, size_t size);

#endif // __STRLCPY_H__