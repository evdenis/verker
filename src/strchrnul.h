#ifndef __STRCHRNUL_H__
#define __STRCHRNUL_H__

#include "strlen.h"

/*@ axiomatic Strchrnul {
    logic char *strchrnul(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? str : strchrnul(str+1, c));

    lemma strchrnul_iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
          strchrnul(str, c) == strchrnul(str+1, c);
    lemma strchrnul_at_end:
       \forall char *str, c;
       \valid(str) && (*str == '\0' || *str == c) ==>
          strchrnul(str, c) == str;

    }
 */

/*
 * Lemma functions. See strlen.h for why these are ghost functions rather than
 * ACSL lemmas; valid_str_shift supplies the strlen(str+1) < strlen(str) that
 * each variant needs.
 */

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ terminates \true;
  @  @ decreases strlen(str);
  @  @ assigns   \nothing;
  @  @ ensures   0 <= strchrnul(str, c) - str <= strlen(str);
  @  @/
  @ void strchrnul_mem(char *str, char c)
  @ {
  @   if (*str != '\0' && *str != c) {
  @     valid_str_shift(str);
  @     strchrnul_mem(str + 1, c);
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  c != '\0';
  @  @ terminates \true;
  @  @ decreases strlen(str);
  @  @ assigns   \nothing;
  @  @ ensures   *strchrnul(str, c) == '\0' ^^ *strchrnul(str, c) == c;
  @  @/
  @ void strchrnul_res(char *str, char c)
  @ {
  @   if (*str != '\0' && *str != c) {
  @     valid_str_shift(str);
  @     strchrnul_res(str + 1, c);
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  0 <= i <= strlen(str);
  @  @ requires  \forall integer j; 0 <= j < i ==> str[j] != c;
  @  @ requires  str[i] == c || str[i] == '\0';
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   strchrnul(str, c) == str + i;
  @  @/
  @ void strchrnul_defn(char *str, char c, size_t i)
  @ {
  @   if (i > 0) {
  @     valid_str_shift(str);
  @     strchrnul_defn(str + 1, c, i - 1);
  @   }
  @ }
  @*/


/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ terminates \true;
  @  @ decreases strlen(str);
  @  @ assigns   \nothing;
  @  @ ensures   strchrnul(str, (char)'\0') == str + strlen(str);
  @  @/
  @ void strchrnul_strlen(char *str)
  @ {
  @   if (*str != '\0') {
  @     valid_str_shift(str);
  @     strchrnul_strlen(str + 1);
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  0 <= i < strchrnul(str, c) - str;
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   str[i] != c;
  @  @/
  @ void strchrnul_skipped(char *str, char c, size_t i)
  @ {
  @   if (i > 0 && *str != '\0' && *str != c) {
  @     valid_str_shift(str);
  @     strchrnul_skipped(str + 1, c, i - 1);
  @   }
  @ }
  @*/

/**
 * strchrnul - Find and return a character in a string, or end of string
 * @s: The string to be searched
 * @c: The character to search for
 *
 * Returns pointer to first occurrence of 'c' in s. If c is not found, then
 * return a pointer to the null byte at the end of s.
 */

/*@ requires valid_str(s);
    terminates \true;
    assigns \result \from s, c;
    exits \false;
    ensures \result == strchrnul(s, (char) c);
    ensures 0 <= \result - s <= strlen(s);
    behavior not_exists:
       assumes \forall integer i; 0 <= i < strlen(s) ==> s[i] != (char) c;
       ensures \result == s + strlen(s);
       ensures *\result == '\0';
    behavior exists:
       assumes \exists integer i; 0 <= i < strlen(s) && s[i] == (char) c;
       ensures *\result == (char) c;
       ensures \forall integer i; 0 <= i < \result - s ==> s[i] != (char) c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchrnul(const char *s, int c);

#endif // __STRCHRNUL_H__
