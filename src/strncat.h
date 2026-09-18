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

/*@ requires valid_src: valid_strn(src, count);
    requires valid_dest: valid_str(dest);
    requires size_fits: strlen(dest) + count <= SIZE_MAX;
    requires length_fits: strlen(dest) <= LONG_MAX;
    requires storage: \valid(dest+(0..strlen(dest)+count));
    requires separated: \separated(dest+(0..strlen(dest)+count), src+(0..count));
    terminates \true;
    assigns dest[strlen{Pre}(dest)..strlen{Pre}(dest) + strnlen{Pre}(src, count)];
    assigns \result \from dest;
    exits \false;
    ensures result: \result == dest;
    ensures prefix: \forall integer i; 0 <= i < strlen{Pre}(dest) ==>
            \at(dest[i], Pre) == \result[i];
    ensures appended: \forall integer i;
            0 <= i < strnlen{Pre}(src, count) ==>
            \at(src[i], Pre) == \result[strlen{Pre}(dest) + i];
    ensures valid_result: valid_str(\result);
    ensures length: strlen(\result) == strlen{Pre}(dest) + strnlen{Pre}(src, count);
 */
char *strncat(char *dest, const char *src, size_t count);

#endif // __STRNCAT_H__
