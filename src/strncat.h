#ifndef __STRNCAT_H__
#define __STRNCAT_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "strnlen.h"

/**
 * strncat - Append a length-limited, C-string to another
 * @dest: The string to be appended to
 * @src: The string to append to it
 * @count: The maximum numbers of bytes to copy
 *
 * Note that in contrast to strncpy(), strncat() ensures the result is
 * terminated.
 */

char *strncat(char *dest, const char *src, size_t count);

#endif // __STRNCAT_H__
