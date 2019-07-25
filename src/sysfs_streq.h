#ifndef __SYSFS_STREQ_H__
#define __SYSFS_STREQ_H__

#include "kernel_definitions.h"
#include "strlen.h"

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
        0
	:
	(size_t)(1 + sysfs_strlen(s));

    logic bool strncmp(char *s1, char *s2, size_t n) =
       n <= 0 ?
          (bool)true
       :
          (s1[0] == s2[0] ?
	     (s1[0] == '\0' ? (bool)true : strncmp(s1 + 1, s2 + 1, (size_t)(n - 1)))
          :
	     (bool)false);

    lemma strncmp_shift:
       \forall char *s1, char *s2, size_t n;
          valid_str(s1) &&
          valid_str(s2) &&
          n > 0 ==>
          strncmp(s1, s2, n) ==>
          strncmp(s1 + 1, s2 + 1, (size_t)(n - 1));

    lemma strncmp_definition:
       \forall char *s1, char *s2, size_t n;
          valid_str(s1) &&
          valid_str(s2) ==>
          (\forall size_t i; 0 <= i < n ==> s1[i] == s2[i]) ==>
          strncmp(s1, s2, n);

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

/*@ requires valid_str(s1);
    requires valid_str(s2);

    assigns \nothing;

    behavior nulls:
       assumes sysfs_strlen(s1) == 0;
       assumes sysfs_strlen(s2) == 0;
       ensures \result == true;

    behavior trivial:
       assumes sysfs_strlen(s1) == 0 ^^ sysfs_strlen(s2) == 0;
       ensures \result == false;

    behavior not_trivial:
       assumes sysfs_strlen(s1) != 0 && sysfs_strlen(s2) != 0;
       ensures \result == strncmp(s1, s2,
                             (size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2)));

    complete behaviors;
    disjoint behaviors;
*/
bool sysfs_streq(const char *s1, const char *s2);

#endif // __SYSFS_STREQ_H__
