#ifndef __STRSCPY_H__
#define __STRSCPY_H__

#include "kernel_definitions.h"

/**
 * strscpy - Copy a C-string into a sized buffer
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 * @count: Size of destination buffer
 *
 * Copy the string, or as much of it as fits, into the dest buffer.
 * The routine returns the number of characters copied (not including
 * the trailing NUL) or -E2BIG if the destination buffer wasn't big enough.
 * The behavior is undefined if the string buffers overlap.
 * The destination buffer is always NUL terminated, unless it's zero-sized.
 *
 * Preferred to strlcpy() since the API doesn't require reading memory
 * from the src string beyond the specified "count" bytes, and since
 * the return value is easier to error-check than strlcpy()'s.
 * In addition, the implementation is robust to the string changing out
 * from underneath it, unlike the current strlcpy() implementation.
 *
 * Preferred to strncpy() since it always returns a valid string, and
 * doesn't unnecessarily force the tail of the destination buffer to be
 * zeroed.  If the zeroing is desired, it's likely cleaner to use strscpy()
 * with an overflow test, then just memset() the tail of the dest buffer.
 */

ssize_t strscpy(char *dest, const char *src, size_t count);

#endif // __STRSCPY_H__