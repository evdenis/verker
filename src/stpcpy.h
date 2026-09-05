#ifndef __STPCPY_H__
#define __STPCPY_H__

#include "strlen.h"

// Keywork __restrict__ is not supported by Frama-C
#define __restrict__

/**
 * stpcpy - copy a string from src to dest returning a pointer to the new end
 *          of dest, including src's %NUL-terminator. May overrun dest.
 * @dest: pointer to end of string being copied into. Must be large enough
 *        to receive copy.
 * @src: pointer to the beginning of string being copied from. Must not overlap
 *       dest.
 *
 * stpcpy differs from strcpy in a key way: the return value is a pointer
 * to the new %NUL-terminating character in @dest. (For strcpy, the return
 * value is a pointer to the start of @dest). This interface is considered
 * unsafe as it doesn't perform bounds checking of the inputs. As such it's
 * not recommended for usage. Instead, its definition is provided in case
 * the compiler lowers other libcalls to stpcpy.
 */

/*@ requires valid_str(src);
    requires \valid(dest+(0..strlen(src)));
    requires \separated(dest+(0..strlen(src)), src+(0..strlen(src)));
    terminates \true;
    assigns dest[0..strlen{Pre}(src)];
    assigns \result \from dest;
    exits \false;
    ensures \result == dest + strlen{Pre}(src);
    ensures *\result == '\0';
    ensures \forall integer i; 0 <= i <= strlen{Pre}(src) ==>
            dest[i] == \at(src[i], Pre);
    ensures valid_str(dest);
    ensures strlen(dest) == strlen{Pre}(src);
 */
char *stpcpy(char *__restrict__ dest, const char *__restrict__ src);

#endif // __STPCPY_H__
