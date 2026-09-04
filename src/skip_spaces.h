#ifndef __SKIP_SPACES_H__
#define __SKIP_SPACES_H__

#include "kernel_definitions.h"
#include "ctype.h"
#include "strlen.h"


/*@ axiomatic SkipSpaces {
    logic char *skip_spaces(char *str) =
       isspace(*str) ? skip_spaces(str + 1) : str;
    lemma skip_spaces_iter_one:
       \forall char *str;
       valid_str(str) && isspace(*str) ==>
       skip_spaces(str) == skip_spaces(str+1);
    lemma skip_spaces_same:
       \forall char *str;
       \valid(str) && !isspace(*str) ==>
          str == skip_spaces(str);
    }
 */

/*
 * Lemma functions. See strlen.h for why these are ghost functions rather than
 * ACSL lemmas. is_space exists because ghost code is C and cannot branch on
 * the isspace predicate directly.
 */

/*@ ghost
  @ /@ terminates \true;
  @  @ assigns   \nothing;
  @  @ ensures   \result != 0 <==> isspace(c);
  @  @/
  @ int is_space(char c)
  @ {
  @   return c == ' '  || c == '\f' || c == '\n'
  @      ||  c == '\r' || c == '\t' || c == '\v';
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ terminates \true;
  @  @ decreases strlen(str);
  @  @ assigns   \nothing;
  @  @ ensures   0 <= skip_spaces(str) - str <= strlen(str);
  @  @ ensures   valid_str(skip_spaces(str));
  @  @ ensures   !isspace(*skip_spaces(str));
  @  @/
  @ void skip_spaces_range(char *str)
  @ {
  @    valid_str_len(str);
  @    if (is_space(*str)) {
  @      valid_str_shift(str);
  @      skip_spaces_range(str + 1);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  0 <= i <= strlen(str);
  @  @ requires  \forall integer j; 0 <= j < i ==> isspace(str[j]);
  @  @ requires  !isspace(str[i]);
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   skip_spaces(str) == str + i;
  @  @/
  @ void skip_spaces_defn(char *str, size_t i)
  @ {
  @    if (i > 0) {
  @      valid_str_shift(str);
  @      skip_spaces_defn(str + 1, i - 1);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  0 <= i < skip_spaces(str) - str;
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   isspace(str[i]);
  @  @/
  @ void skipped_are_spaces(char *str, size_t i)
  @ {
  @   skip_spaces_range(str);
  @   if (i > 0) {
  @     valid_str_shift(str);
  @     skipped_are_spaces(str + 1, i - 1);
  @   }
  @ }
  @*/


/**
 * skip_spaces - Removes leading whitespace from @str.
 * @str: The string to be stripped.
 *
 * Returns a pointer to the first non-whitespace character in @str.
 */

/*@ requires valid_str(str);
    terminates \true;
    assigns \result \from str;
    exits \false;
    ensures \result == skip_spaces(str);
    ensures 0 <= \result - str <= strlen(str);
    ensures !isspace(*\result);
    ensures \forall integer i; 0 <= i < \result - str ==> isspace(str[i]);
    ensures valid_str(\result);
 */
char *skip_spaces(const char *str);

#endif // __SKIP_SPACES_H__
