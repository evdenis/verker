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

#ifndef LEMMA_FUNCTIONS

/*@ axiomatic SysfsStr {
    logic size_t sysfs_strlen(char *s) =
       ((s[0] == '\0') ||
        (s[0] == '\n' && s[1] == '\0'))
        ? 0
        : (size_t)(1 + sysfs_strlen(s));

    lemma sysfs_strlen_n_equal:
       \forall char *s1, char *s2, size_t n;
          valid_str(s1) &&
          valid_str(s2) ==>
          (\exists size_t i;
	     (0 <= i < \min(sysfs_strlen(s1), sysfs_strlen(s2))) &&
	     (s1[i] != s2[i])) ==>
          strncmp(s1, s2, (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2))) == (bool)false;

    lemma sysfs_strlen_bsn:
       \forall char *s, size_t n;
          valid_str(s) &&
          (\forall size_t i; 0 <= i < n ==> s[i] != '\0') &&
          s[n] == '\n' &&
          s[n + 1] == '\0' ==>
          sysfs_strlen(s) == n;

    lemma sysfs_strlen_equal:
       \forall char* s1, char* s2, size_t n;
          valid_str(s1) &&
          valid_str(s2) &&
          (\forall size_t i; 0 <= i < n ==> s1[i] == s2[i]) &&
          s1[n] == '\0' &&
          s2[n] == '\0' ==>
	  (sysfs_strlen(s1) == sysfs_strlen(s2) &&
           strncmp(s1, s2, (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2))) == (bool)true);
    }
 */

#else

/*@ axiomatic SysfsStr {
    logic size_t sysfs_strlen(char *s) =
       ((s[0] == '\0') ||
        (s[0] == '\n' && s[1] == '\0'))
        ? 0
        : (size_t)(1 + sysfs_strlen(s));
   }
 */

/*@ ghost
  @ /@ lemma
  @  @ requires  valid_str(s1) && valid_str(s2);
  @  @ decreases strlen(s1);
  @  @ ensures (
  @   \exists size_t i;
  @      (
  @        0 <= i < \min(sysfs_strlen(s1), sysfs_strlen(s2))
  @      ) &&
  @      (s1[i] != s2[i])) ==>
  @         strncmp(s1, s2, (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2))) ==
  @            (bool)false;
  @  @/
  @ void sysfs_strlen_n_equal(char *s1, char *s2)
  @ {
  @   if (*s1 == *s2 && *s1 != '\0' && *s1 != '\n')
  @     sysfs_strlen_n_equal(s1, s2);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s) &&
  @       (\forall size_t i; 0 <= i < n ==> s[i] != '\0') &&
  @       s[n] == '\n' &&
  @       s[n + 1] == '\0';
  @  @ decreases strlen(s);
  @  @ ensures sysfs_strlen(s) == n;
  @  @/
  @ void sysfs_strlen_bsn(char *s, size_t n)
  @ {
  @   if (*s != '\0' && *s != '\n')
  @     sysfs_strlen_bsn(s + 1, n - 1);
  @ }
  @*/

/*@ ghost
  @ /@ lemma
  @  @ requires valid_str(s1) &&
  @       valid_str(s2) &&
  @       (\forall size_t i; 0 <= i < n ==> s1[i] == s2[i]) &&
  @       s1[n] == '\0' &&
  @       s2[n] == '\0';
  @  @ decreases strlen(s1);
  @  @ ensures (sysfs_strlen(s1) == sysfs_strlen(s2) &&
  @        strncmp(s1, s2, (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2))) == (bool)true);
  @  @/
  @ void sysfs_strlen_equal(char* s1, char* s2, size_t n)
  @ {
  @   if (*s1 == *s2 && *s1 != '\0' && *s1 != '\n')
  @     sysfs_strlen_equal(s1 + 1, s2 + 1, n - 1);
  @ }
  @*/

#endif /* LEMMA_FUNCTIONS */

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
       ensures \result == strncmp(s1, s2,
                             (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2)));

    complete behaviors;
    disjoint behaviors;
*/
bool sysfs_streq(const char *s1, const char *s2);

#endif // __SYSFS_STREQ_H__
