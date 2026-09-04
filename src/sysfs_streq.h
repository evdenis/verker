#ifndef __SYSFS_STREQ_H__
#define __SYSFS_STREQ_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "strncmp.h"

/**
 * sysfs_streq - return true if strings are equal, modulo trailing newline
 * @s1: one string
 * @s2: another string
 *
 * This routine returns true iff two strings are equal, treating both
 * NUL and newline-then-NUL as equivalent string terminations.  It's
 * geared for use with sysfs input strings, which generally terminate
 * with newlines but are compared against values without newlines.
 */

/*@ axiomatic SysfsStr {
    logic size_t sysfs_strlen(char *s) =
       ((s[0] == '\0') ||
        (s[0] == '\n' && s[1] == '\0')) ?
        (size_t)0
	:
	(size_t)(1 + sysfs_strlen(s + 1));

    }
 */

/*@ ghost
  @ /@ requires  valid_str(s1);
  @  @ requires  valid_str(s2);
  @  @ requires  0 <= i < \min(sysfs_strlen(s1), sysfs_strlen(s2));
  @  @ requires  s1[i] != s2[i];
  @  @ terminates \true;
  @  @ decreases i;
  @  @ assigns   \nothing;
  @  @ ensures   strncmp(s1, s2, (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2))) != 0;
  @  @/
  @ void sysfs_strlen_n_equal(char *s1, char *s2, size_t i)
  @ {
  @   if (i > 0 && s1[0] == s2[0]) {
  @     valid_str_shift(s1);
  @     valid_str_shift(s2);
  @     sysfs_strlen_n_equal(s1 + 1, s2 + 1, i - 1);
  @   }
  @ }
  @*/

/*
 * Lemma functions. See strlen.h for why these are ghost functions rather than
 * ACSL lemmas.
 */

/*@ ghost
  @ /@ requires  valid_str(s);
  @  @ requires  \forall integer i; 0 <= i < n ==> s[i] != '\0';
  @  @ requires  s[n] == '\n';
  @  @ requires  s[n + 1] == '\0';
  @  @ terminates \true;
  @  @ decreases n;
  @  @ assigns   \nothing;
  @  @ ensures   sysfs_strlen(s) == n;
  @  @/
  @ void sysfs_strlen_bsn(char *s, size_t n)
  @ {
  @   if (n > 0) {
  @     valid_str_shift(s);
  @     sysfs_strlen_bsn(s + 1, n - 1);
  @   }
  @ }
  @*/

/*@ ghost
  @ /@ requires  valid_str(s1);
  @  @ requires  valid_str(s2);
  @  @ requires  \forall integer i; 0 <= i < n ==> s1[i] == s2[i];
  @  @ requires  s1[n] == '\0';
  @  @ requires  s2[n] == '\0';
  @  @ terminates \true;
  @  @ decreases n;
  @  @ assigns   \nothing;
  @  @ ensures   sysfs_strlen(s1) == sysfs_strlen(s2);
  @  @/
  @ void sysfs_strlen_equal(char *s1, char *s2, size_t n)
  @ {
  @   if (n > 0 && s1[0] != '\0') {
  @     valid_str_shift(s1);
  @     valid_str_shift(s2);
  @     sysfs_strlen_equal(s1 + 1, s2 + 1, n - 1);
  @   }
  @ }
  @*/


/*@ requires valid_str(s1);
    requires valid_str(s2);
    assigns \nothing;
    behavior nulls:
       assumes sysfs_strlen(s1) == 0 && sysfs_strlen(s2) == 0;
       ensures \result;
    behavior trivial:
       assumes sysfs_strlen(s1) == 0 ^^ sysfs_strlen(s2) == 0;
       ensures !\result;
    behavior not_trivial:
       assumes sysfs_strlen(s1) != 0 && sysfs_strlen(s2) != 0;
       ensures strnequal(s1, s2, (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2)));
    complete behaviors;
    disjoint behaviors;
*/
bool sysfs_streq(const char *s1, const char *s2);

#endif // __SYSFS_STREQ_H__
