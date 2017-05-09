#ifndef __STRCPY_H__
#define __STRCPY_H__

#include "strlen.h"

/**
 * strcpy - Copy a %NUL terminated string
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 */

/*@ requires valid_str(src);
    requires \valid(dest+(0..strlen(src)));
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strlen(src)];
    ensures valid_str(\result);
    ensures \result == dest;
    ensures \forall integer i; 0 <= i <= strlen(src) ==> \result[i] == src[i];
 */
char *strcpy(char *dest, const char *src);

#endif // __STRCPY_H__
