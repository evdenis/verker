#ifndef __STRLCAT_H__
#define __STRLCAT_H__

#include "kernel_definitions.h"
#include "strlen.h"

/**
 * strlcat - Append a length-limited, C-string to another
 * @dest: The string to be appended to
 * @src: The string to append to it
 * @count: The size of the destination buffer.
 */

size_t strlcat(char *dest, const char *src, size_t count);

#endif // __STRLCAT_H__