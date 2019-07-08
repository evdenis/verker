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
    axiomatic MatchString {
        logic integer real_len(char **array, integer n) =
            ((n <= 0) || (array[0] == NULL))
            ? 0
            : 1 + real_len(array + 1, n - 1);

        predicate checked_head(char** array, char* string, integer tail) =
            \forall integer k;
                (0 <= k < tail) ==> (
                    array[k] != NULL &&
                    strcmp(array[k], string) != 0
                );

        lemma zero_len_a:
            \forall char** array;
                \valid_read(array) ==>
                    real_len(array, 0) == 0;
        
        lemma zero_len_b:
            \forall char** array, integer n;
                (
                    \valid_read(array) &&
                    array[0] == NULL &&
                    n > 0
                ) ==>
                    real_len(array, n) == 0;
        
        lemma one_element:
            \forall char** array;
                (
                    \valid_read(array) &&
                    array[0] != NULL
                ) ==>
                    real_len(array, 1) == 1;
        
        lemma basic:
            \forall char** array, integer n;
                (
                    n > 0 &&
                    \valid_read(array+(0..n)) &&
                    array[0] != NULL
                ) ==>
                    (real_len(array, n) ==
                        1 + real_len(array + 1, n - 1));
        
        lemma one_element_or_more:
            \forall char** array, integer n;
                (
                    n > 0 &&
                    \valid_read(array + (0..n)) &&
                    array[0] != NULL
                ) ==>
                    real_len(array, n + 1) > 0;

        lemma not_null_terminated:
            \forall char** array, integer n;
                (
                    \valid_read(array+(0..n)) &&
                    (\forall integer k; k <= n ==> array[k] != NULL)
                ) ==>
                    real_len(array, n + 1) == n + 1;

        lemma lower_bound:
            \forall char** array, integer n, char* string;
                (
                    valid_str(string) &&
                    n > 0 &&
                    \valid_read(array+(0..n))
                ) ==> (
                    \forall integer k;
                        0 <= k <= n &&
                        checked_head(array, string, k) ==>
                            real_len(array, n + 1) >= k
                );

        lemma upper_bound:
            \forall char** array, integer n;
                (
                    n >= 0 &&
                    \valid_read(array + (0..n))
                ) ==>
                    (0 <= real_len(array, n + 1) <= n + 1);
        
    }
*/

/*@
    requires real_len(array, n) <= SIZE_MAX;
    requires \valid_read(array + (0..real_len(array, n)-1));
    requires valid_str(string);

    requires \forall integer k;
        (0 <= k < real_len(array, n)) ==>
        valid_str(array[k]);

    assigns \nothing;

    behavior exists:
        assumes \exists integer k;
            (0 <= k < real_len(array, n)) ==>
            strcmp(array[k], string) == 0;

        ensures 0 <= \result < real_len(array, n);
        ensures strcmp(array[\result], string) == 0;
        ensures \forall integer k;
            (0 <= k < \result) ==>
                (
                    array[k] != NULL &&
                    strcmp(array[\result], string) != 0
                );

    behavior missing:
        assumes \forall integer k;
            (0 <= k < real_len(array, n)) ==>
                strcmp(array[k], string) != 0;

        ensures \result == -EINVAL;

    complete behaviors;
    disjoint behaviors;
*/

int match_string(const char * const *array, size_t n, const char *string);

#endif // __MATCH_STRING_H__
