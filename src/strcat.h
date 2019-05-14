#ifndef __STRCAT_H__
#define __STRCAT_H__

#include "strlen.h"

/**
 * strcat - Append one %NUL-terminated string to another
 * @dest: The string to be appended to
 * @src: The string to append to it
 */

/*@ requires valid_str(src);
    requires valid_str(dest);
    requires strlen(dest)+strlen(src) <= SIZE_MAX;
    //requires strlen(dest)+strlen(src) == (size_t)(strlen(dest)+strlen(src));
    requires \valid(dest+(0..strlen(dest)+strlen(src)));
    assigns dest[strlen(dest)..strlen(dest)+strlen(src)];
    ensures \result == dest;
    ensures valid_str(\result);
    ensures \forall integer i; 0 <= i < strlen{Old}(dest) ==>
            \old(dest[i]) == \result[i];
    ensures \forall integer i;
            strlen{Old}(dest) <= i < strlen{Old}(dest) + strlen(src) ==>
            src[i - strlen{Old}(dest)] == \result[i];
    ensures strlen(\result) == strlen{Old}(dest) + strlen(src);
 */
char *strcat(char *dest, const char *src);

#endif // __STRCAT_H__
