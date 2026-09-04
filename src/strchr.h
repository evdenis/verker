#ifndef __STRCHR_H__
#define __STRCHR_H__

#include "kernel_definitions.h"
#include "strlen.h"

/*@ axiomatic Strchr {
    logic char *strchr(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? (char *) \null : strchr(str+1, c));

    lemma strchr_iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
          strchr(str, c) == strchr(str+1, c);
    lemma strchr_at_end_zero:
       \forall char *str, c;
       \valid(str) && *str == '\0' && c != '\0' ==>
          strchr(str, c) == \null;
    lemma strchr_at_end_char:
       \forall char *str, c;
       \valid(str) && *str == c ==>
          strchr(str, c) == str;

    }
 */

/*
 * Lemma functions. See strlen.h for why these are ghost functions rather than
 * ACSL lemmas. Each recurses down the string, so each needs
 * strlen(str+1) < strlen(str) to justify its variant; valid_str_shift supplies
 * that.
 */

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ terminates \true;
  @  @ decreases strlen(str);
  @  @ assigns   \nothing;
  @  @ ensures   strchr(str, c) != \null ==>
  @  @             0 <= strchr(str, c) - str <= strlen(str);
  @  @/
  @ void strchr_mem(char *str, char c)
  @ {
  @    if (*str != c && *str != '\0') {
  @      valid_str_shift(str);
  @      strchr_mem(str + 1, c);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  c != '\0';
  @  @ terminates \true;
  @  @ decreases strlen(str);
  @  @ assigns   \nothing;
  @  @ ensures   strchr(str, c) == \null ^^
  @  @           (\valid(strchr(str, c)) && *strchr(str, c) == c);
  @  @/
  @ void strchr_res(char *str, char c)
  @ {
  @    if (*str != c && *str != '\0') {
  @      valid_str_shift(str);
  @      strchr_res(str + 1, c);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  0 <= i <= strlen(str);
  @  @ requires  \forall integer j; 0 <= j < i ==> str[j] != c;
  @  @ requires  str[i] == c;
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   strchr(str, c) == str + i;
  @  @/
  @ void strchr_defn(char *str, char c, size_t i)
  @ {
  @    if (i > 0) {
  @      valid_str_shift(str);
  @      strchr_defn(str + 1, c, i - 1);
  @    }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(str);
  @  @ requires  strchr(str, c) != \null;
  @  @ requires  0 <= i < strchr(str, c) - str;
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   str[i] != c;
  @  @/
  @ void strchr_skipped(char *str, char c, size_t i)
  @ {
  @   if (i > 0 && *str != '\0' && *str != c) {
  @     valid_str_shift(str);
  @     strchr_skipped(str + 1, c, i - 1);
  @   }
  @ }
  @*/


/**
 * strchr - Find the first occurrence of a character in a string
 * @s: The string to be searched
 * @c: The character to search for
 */

/*@ requires valid_str(s);
    terminates \true;
    assigns \result \from s, c;
    exits \false;
    ensures \result == strchr(s, (char) c);
    behavior not_exists:
       assumes \forall integer i; 0 <= i <= strlen(s) ==> s[i] != (char) c;
       ensures \result == \null;
    behavior exists:
       assumes \exists integer i; 0 <= i <= strlen(s) && s[i] == (char) c;
       ensures 0 <= \result - s <= strlen(s);
       ensures *\result == (char) c;
       ensures \forall integer i; 0 <= i < \result - s ==> s[i] != (char) c;
    complete behaviors;
    disjoint behaviors;
 */
char *strchr(const char *s, int c);

#endif // __STRCHR_H__
