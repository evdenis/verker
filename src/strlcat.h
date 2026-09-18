#ifndef __STRLCAT_H__
#define __STRLCAT_H__

#include "kernel_definitions.h"
#include "memcpy.h"
#include "strlen.h"

/**
 * strlcat - Append a length-limited, C-string to another
 * @dest: The string to be appended to
 * @src: The string to append to it
 * @count: The size of the destination buffer.
 */

/*@ requires valid_dest: valid_str(dest);
    requires valid_src: valid_str(src);
    requires storage: \valid(dest + (0..count-1));
    requires capacity: strlen(dest) < count;
    requires result_fits: strlen(dest) + strlen(src) <= SIZE_MAX;
    requires lengths_fit: strlen(dest) <= LONG_MAX && strlen(src) <= LONG_MAX;
    requires separated: \separated(dest + (0..count-1), src + (0..strlen(src)));
    terminates \true;
    exits \false;
    assigns dest[strlen{Pre}(dest)..strlen{Pre}(dest) +
                 \min(strlen{Pre}(src), count - strlen{Pre}(dest) - 1)];
    ensures result: \result == strlen{Pre}(dest) + strlen{Pre}(src);
    ensures prefix: \forall integer i; 0 <= i < strlen{Pre}(dest) ==>
                    dest[i] == \at(dest[i], Pre);
    ensures appended: \forall integer i;
                      0 <= i < \min(strlen{Pre}(src), count - strlen{Pre}(dest) - 1) ==>
                      dest[strlen{Pre}(dest) + i] == \at(src[i], Pre);
    ensures terminated: dest[strlen{Pre}(dest) +
                        \min(strlen{Pre}(src), count - strlen{Pre}(dest) - 1)] == '\0';
    ensures valid_result: valid_str(dest);
    ensures length: strlen(dest) == strlen{Pre}(dest) +
                    \min(strlen{Pre}(src), count - strlen{Pre}(dest) - 1);
 */
size_t strlcat(char *dest, const char *src, size_t count);

#endif // __STRLCAT_H__
