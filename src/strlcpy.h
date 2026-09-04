#ifndef __STRLCPY_H__
#define __STRLCPY_H__

#include "kernel_definitions.h"
#include "memcpy.h"
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
    requires \separated(dest+(0..size - 1), src+(0..strlen(src)));
    requires strlen(src) <= LONG_MAX;
    terminates \true;
    exits \false;
    ensures \result == strlen{Pre}(src);
    behavior size_is_lower_src:
       assumes 0 < size <= strlen(src);
       assigns dest[0..size - 1];
       ensures \forall integer i; 0 <= i < size - 1 ==>
               \at(src[i], Pre) == dest[i];
       ensures valid_str(dest);
       ensures strlen(dest) == size - 1;
    behavior size_is_greater_src:
       assumes size > strlen(src);
       assigns dest[0..strlen{Pre}(src)];
       ensures \forall integer i; 0 <= i < strlen{Pre}(src) ==>
               \at(src[i], Pre) == dest[i];
       ensures valid_str(dest);
       ensures strlen(dest) == strlen{Pre}(src);
    behavior zero_size:
       assumes size == 0;
       assigns \nothing;
    complete behaviors;
    disjoint behaviors;
 */
size_t strlcpy(char *dest, const char *src, size_t size);

#endif // __STRLCPY_H__
