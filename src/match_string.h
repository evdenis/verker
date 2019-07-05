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
    logic size_t _real_len(char **array, size_t n) =
        array[0] == NULL
        ? (size_t) 0
        : (
            n > 0
            ? (size_t) (1 + _real_len(array + 1, (size_t)(n - 1)))
            : 0
        );
*/

/*@
    requires _real_len(array, n) <= SIZE_MAX;
    requires \valid_read(array + (0.._real_len(array, n)-1));
    requires valid_str(string);

    requires \forall integer i;
        0 <= i < _real_len(array, n) &&
        valid_str(array[i]);

    assigns \nothing;

    behavior exists:
        assumes \exists integer i;
            0 <= i < _real_len(array, n) &&
            strcmp(array[i], string) == 0;

        ensures 0 <= \result < _real_len(array, n);
        ensures strcmp(array[\result], string) == 0;
        ensures \forall integer k;
            0 <= k < \result &&
            strcmp(array[\result], string) != 0;

    behavior missing:
        assumes \forall integer i;
            0 <= i < _real_len(array, n) &&
            strcmp(array[i], string) != 0;

        ensures \result == -EINVAL;

    complete behaviors;
    disjoint behaviors;
*/
int match_string(const char * const *array, size_t n, const char *string);

#endif // __MATCH_STRING_H__
