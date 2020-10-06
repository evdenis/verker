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
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strlen(src)];
    ensures valid_str(\result);
    ensures *\result == '\0';
    ensures \result == dest + strlen(src);
    ensures \forall integer i; 0 <= i <= strlen(src) ==> dest[i] == src[i];
 */
char *stpcpy(char *__restrict__ dest, const char *__restrict__ src);

#endif // __STPCPY_H__
