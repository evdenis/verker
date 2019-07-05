#ifndef __MATCH_STRING_H__
#define __MATCH_STRING_H__

#include "strcmp.h"

/**
 * match_string - matches given string in an array
 * @array:	array of strings
 * @n:		number of strings in the array or -1 for NULL terminated arrays
 * @string:	string to match with
 *
 * Return:
 * index of a @string in the @array if matches, or %-EINVAL otherwise.
 */

/*@
    logic integer cmp(unsigned char a, unsigned char b) =
       a == b ? 0 : a < b ? -1 : 1;

    logic integer strncmp(char *cs, char *ct, integer n) =
       n == -1 ? 0 : (cs[n] == ct[n] ? strncmp(cs+1, ct+1, n-1) : cmp((u8 AENO)cs[n], (u8 AENO)ct[n]));
    logic integer strcmp(char *cs, char *ct) = strncmp(cs, ct, strlen(cs));
*/

/*@
    requires \valid_read(array + (0..n-1));
    requires valid_str(string);
    requires n <= INT_MAX;
    requires \forall integer i; 0 <= i < n && valid_str(array[i]);

    assigns   \nothing;

    behavior exists:
        assumes  \exists integer i; 0 <= i < n && strcmp(array[i], string) == 0;
        ensures  0 <= \result < n;
        ensures  strcmp(array[\result], string) == 0;
        ensures  \forall integer i; 0 <= i < \result ==>
            strcmp(array[\result], string) != 0;

    behavior missing:
        assumes  \forall integer i; 0 <= i < n ==>
            strcmp(array[i], string) != 0;
        ensures  \result == -EINVAL;

    complete behaviors;
    disjoint behaviors;
*/
int match_string(const char * const *array, size_t n, const char *string);

#endif // __MATCH_STRING_H__
