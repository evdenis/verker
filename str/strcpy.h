#ifndef __STRCPY_H__
#define __STRCPY_H__

#include "strlen.h"

/*@ requires valid_str(src);
    requires \valid(dest+(0..strlen(src)));
    requires \base_addr(dest) != \base_addr(src);
    assigns dest[0..strlen(src)];
    ensures valid_str(dest);
    ensures \result == dest;
    ensures \forall size_t i; i <= strlen(src) ==> \result[i] == src[i];
 */
char *strcpy(char *dest, const char *src);

#endif // __STRCPY_H__