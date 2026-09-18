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

/*@ predicate sysfs_prefix{L}(char *s1, char *s2, integer n) =
       \forall integer i; 0 <= i < n ==> s1[i] == s2[i] && s1[i] != '\0';

    predicate sysfs_end{L}(char *s1, char *s2, integer n) =
       (s1[n] == '\0' && s2[n] == '\0') ||
       (s1[n] == '\0' && s2[n] == '\n' && s2[n + 1] == '\0') ||
       (s2[n] == '\0' && s1[n] == '\n' && s1[n + 1] == '\0');

    predicate sysfs_equal{L}(char *s1, char *s2) =
       \exists integer n; 0 <= n <= strlen(s1) && n <= strlen(s2) &&
                          sysfs_prefix(s1, s2, n) && sysfs_end(s1, s2, n);
 */

/*@ requires valid_s1: valid_str(s1);
    requires valid_s2: valid_str(s2);
    terminates \true;
    exits \false;
    assigns \nothing;
    ensures result: (\result != 0) <==> sysfs_equal(s1, s2);
 */
bool sysfs_streq(const char *s1, const char *s2);

#endif // __SYSFS_STREQ_H__
