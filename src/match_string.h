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

/*@ predicate match_string_array{L}(char **array, integer n, integer length) =
       0 <= length <= n && length <= INT_MAX &&
       \valid_read(array + (0..length-1)) &&
       (length < n ==> \valid_read(array + length) && array[length] == \null) &&
       (\forall integer i; 0 <= i < length ==>
                           array[i] != \null && valid_str(array[i]));
 */

/*
 * A proved version of PR #14's comparison lemma. Its postcondition is
 * conditional so the equality branch is also checked with reachable inputs.
 */
/*@ ghost
  @ /@ requires valid_s1: valid_str(s1);
  @  @ requires valid_s2: valid_str(s2);
  @  @ terminates \true;
  @  @ exits \false;
  @  @ assigns \nothing;
  @  @ ensures differs: strcmp(s1, s2) != 0 ==>
  @  @    (\exists integer i; 0 <= i <= \min(strlen(s1), strlen(s2)) &&
  @  @                        s1[i] != s2[i]);
  @  @/
  @ void strcmp_corollary(char *s1, char *s2)
  @ {
  @   valid_str_len(s1);
  @   valid_str_len(s2);
  @   size_t i = 0;
  @   /@ loop invariant bounds: 0 <= i <= strlen(s1) && i <= strlen(s2);
  @    @ loop invariant prefix: \forall integer j; 0 <= j < i ==>
  @    @                       s1[j] == s2[j] && s1[j] != '\0';
  @    @ loop assigns i;
  @    @ loop variant strlen(s1) - i;
  @    @/
  @   while (s1[i] == s2[i] && s1[i] != '\0')
  @     i++;
  @   if (s1[i] == s2[i]) {
  @     /@ assert end: i == strlen(s1) && i == strlen(s2); @/
  @     strncmp_defn_equal(s1, s2, i);
  @   }
  @ }
  @*/

/*@ requires valid_array: \exists integer length;
                           match_string_array(array, n, length);
    requires valid_string: valid_str(string);
    terminates \true;
    exits \false;
    assigns \nothing;
    ensures result: \result == -EINVAL || 0 <= \result < n;
    ensures found: \result >= 0 ==>
       (\exists integer length; match_string_array(array, n, length) &&
          \result < length && strcmp(array[\result], string) == 0);
    ensures first: \result >= 0 ==>
       (\forall integer i; 0 <= i < \result ==>
                           array[i] != \null && strcmp(array[i], string) != 0);
    ensures missing: (\result == -EINVAL) <==>
       (\forall integer length; match_string_array(array, n, length) ==>
          (\forall integer i; 0 <= i < length ==> strcmp(array[i], string) != 0));
 */
int match_string(const char * const *array, size_t n, const char *string);

#endif // __MATCH_STRING_H__
