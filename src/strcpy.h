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
    requires \separated(dest+(0..strlen(src)), src+(0..strlen(src)));
    terminates \true;
    assigns dest[0..strlen{Pre}(src)];
    assigns \result \from dest;
    exits \false;
    ensures \result == dest;
    ensures \forall integer i; 0 <= i <= strlen{Pre}(src) ==>
            \result[i] == \at(src[i], Pre);
    ensures valid_str(\result);
    ensures strlen(\result) == strlen{Pre}(src);
 */
char *strcpy(char *dest, const char *src);

#endif // __STRCPY_H__
