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

bool sysfs_streq(const char *s1, const char *s2);

#endif // __SYSFS_STREQ_H__