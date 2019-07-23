#ifndef __MATCH_STRING_H__
#define __MATCH_STRING_H__

#include "kernel_definitions.h"
#include "strcmp.h"

/**
 * match_stringn - matches given string in an array
 * @array:	array of strings
 * @n:		number of strings in the array or -1 for NULL terminated arrays
 * @string:	string to match with
 *
 * Return:
 * index of a @string in the @array if matches, or %-EINVAL otherwise.
 */

/*
 * In fact this function searches in a subarray ending NULL
 * If n > INT_MAX and in array[0..INT_MAX] there are not NULL int index will
 * be overflowed
 */


/*@ axiomatic MatchString {

  logic size_t match_stringn(char** array, size_t n, char* string) =
    n == 0
      ? 0
      : (
        strcmp(array[0], string) == 0
          ? 0
          : match_stringn(array + 1, (size_t)(n - 1), string)
      );

  logic size_t real_len(char** array, size_t n) =
    ((array[0] == NULL) || (n == 0))
      ? 0
      : (size_t)((size_t)1 + real_len(array + 1, (size_t)(n - 1)));

  lemma real_len_not_nulls:
    \forall char** array, size_t i, len;
      0 <= i < real_len(array, len) ==> array[i] != NULL;

  lemma real_len_terminate:
     \forall char** array, size_t i, len;
      i == real_len(array, len) ==>
        array[i] == NULL || i == len;

  lemma real_len_maximum:
    \forall char** array, size_t len;
      (\forall size_t i; i < len ==> array[i] != NULL) ==>
        real_len(array, len) == len;

  lemma match_string_definition:
    \forall char** array, char* string, size_t i, len;
      (
        0 <= i < real_len(array, len) &&
        (
          \forall size_t j;
            0 <= j < i ==> strcmp(array[j], string) != 0
        ) &&
        strcmp(array[i], string) == 0
      ) ==>
      match_stringn(array, real_len(array, len), string) == i;

  lemma strcmp_corollary:
    \forall char* string1, char* string2;
      (
        valid_str(string1) &&
        valid_str(string2) &&
        strcmp(string1, string2) != 0
      ) ==> (
          \exists size_t i;
            0 <= i <= \min(strlen(string1), strlen(string2)) &&
              string1[i] != string2[i]
      );
}
 */

/*@
  requires n <= INT_MAX;
  requires (real_len(array, n) == n) ==> \valid(array+(0..n-1));
  requires (real_len(array, n) < n) ==> \valid(array+(0..real_len(array, n)));
  requires valid_str(string);
  requires \forall size_t i;
    0 <= i < real_len(array, n) ==> valid_str(array[i]);

  assigns \nothing;

  behavior exists:
    assumes \exists size_t k;
      (0 <= k < real_len(array, n)) &&
        strcmp(array[k], string) == 0;

    ensures \result == match_stringn(array, real_len(array, n), string);
    ensures 0 <= \result < real_len(array, n);
    ensures strcmp(array[\result], string) == 0;
    ensures \forall size_t k;
      (0 <= k < \result) ==> (
          strcmp(array[k], string) != 0
      );

  behavior missing:
    assumes \forall size_t k;
      (0 <= k < real_len(array, n)) ==> (
          strcmp(array[k], string) != 0
      );

    ensures \result == -EINVAL;

  complete behaviors;
  disjoint behaviors;
*/
int match_string(const char* const* array, size_t n, const char* string);

#endif // __MATCH_STRING_H__
