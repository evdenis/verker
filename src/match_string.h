#ifndef __MATCH_STRING_H__
#define __MATCH_STRING_H__

#include "kernel_definitions.h"
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
    requires \valid_read(array + (0..n-1));
    requires valid_str(string);
    requires n <= INT_MAX;
    requires
        (
            n == (size_t AENO)(-1) && (
                \exists integer end;
                    array[end] == NULL &&
                    (
                        \forall integer k;
                            0 < k < end && array[k] != NULL
                    ) &&
                    (
                        \forall integer k;
                            0 < k < end && valid_str(array[k])
                    )
            )
                
        ) ||
        (
            n >= 0 && (
                \forall integer i;
                    0 <= i < n && valid_str(array[i])
            )
        );

    assigns   \nothing;

    behavior exists:
        assumes  \exists integer i;
            0 <= i < n && strcmp(array[i], string) == 0;
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
