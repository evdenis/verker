#ifndef __STRCPY_H__
#define __STRCPY_H__

#include "strlen.h"

/*@ requires valid_string(src);
    requires \valid(dest+(0..strlen(src)));
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strlen(src)];
    ensures \result == dest;
    ensures \forall integer i; 0 <= i <= strlen(src) ==> dest[i] == src[i];
    ensures valid_string(dest);
 */
char *strcpy(char *dest, const char *src);

#endif // __STRCPY_H__