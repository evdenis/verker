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

/*@ requires \valid(dest+(0..size - 1));
    requires valid_str(src);
    requires \base_addr(dest) != \base_addr(src);
    behavior size_is_lower_src:
       assumes 0 < size <= strlen(src);
       assigns dest[0..size - 1];
       ensures \forall integer i; 0 <= i < size - 1 ==> src[i] == dest[i];
       ensures valid_str(dest);
    behavior size_is_greater_src:
       assumes size > strlen(src);
       assigns dest[0..strlen(src)];
       ensures \forall integer i; 0 <= i < strlen(src) ==> src[i] == dest[i];
       ensures valid_str(dest);
    behavior zero_size:
       assumes size == 0;
       assigns \nothing;
    complete behaviors;
    disjoint behaviors;
 */
size_t strlcpy(char *dest, const char *src, size_t size);

#endif // __STRLCPY_H__
