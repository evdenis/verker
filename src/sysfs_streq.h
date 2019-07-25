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


/*@
	axiomatic SysfsStr {
		logic size_t sysfs_strlen(char* string) =
			(
				(string[0] == '\0') ||
				(string[0] == '\n' && string[1] == '\0')
			)
				? 0
				: (size_t)(1 + sysfs_strlen(string));

		logic bool strncmp(char* string1, char* string2, size_t n) =
			n <= 0
				? (bool)true
				: (
					string1[0] == string2[0]
						? (
							string1[0] == '\0'
								? (bool)true
								: strncmp(string1 + 1, string2 + 1, (size_t)(n - 1))
						)
						:	(bool)false
				);

		lemma strncmp_shift:
			\forall char* string1, char* string2, size_t n;
				(
					valid_str(string1) &&
					valid_str(string2) &&
					n > 0
				) ==> (
					strncmp(string1, string2, n) ==>
						strncmp(string1 + 1, string2 + 1, (size_t)(n - 1))
				);

		lemma strncmp_definition:
			\forall char* string1, char* string2, size_t n;
				(
					valid_str(string1) &&
					valid_str(string2)
				) ==> (
					(
						\forall size_t i;
							0 <= i < n ==> string1[i] == string2[i]
					) ==> strncmp(string1, string2, n)
				);

		lemma sysfs_strlen_n_equal:
			\forall char* string1, char* string2, size_t n;
				(
					valid_str(string1) &&
					valid_str(string2)
				) ==> (
					(
						\exists size_t i;
							(0 <= i < \min(sysfs_strlen(string1), sysfs_strlen(string2))) &&
								(string1[i] != string2[i])
					) ==>
						strncmp(
							string1,
							string2,
							(size_t)\min(
								sysfs_strlen(string1),
								sysfs_strlen(string2)
							)
						) == (bool)false
				);

		lemma sysfs_strlen_bsn:
			\forall char* string, size_t n;
				(
					valid_str(string) &&
					(
						\forall size_t i;
							0 <= i < n ==> string[i] != '\0'
					) &&
					string[n] == '\n' &&
					string[n + 1] == '\0'
				) ==> (
					sysfs_strlen(string) == n
				);

		lemma sysfs_strlen_equal:
			\forall char* string1, char* string2, size_t n;
				(
					valid_str(string1) &&
					valid_str(string2) &&
					(
						\forall size_t i;
							0 <= i < n ==> string1[i] == string2[i]
					) &&
					string1[n] == '\0' &&
					string2[n] == '\0'
				) ==> (
					sysfs_strlen(string1) == sysfs_strlen(string2) &&
					strncmp(
							string1,
							string2,
							(size_t)\min(
								sysfs_strlen(string1),
								sysfs_strlen(string2)
							)
						) == (bool)true
				);
	}
 */

/*@
	requires valid_str(s1);
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

		ensures \result ==
			strncmp(
				s1,
				s2,
				(size_t)\min(sysfs_strlen(s1), sysfs_strlen(s2))
			);

	complete behaviors;
	disjoint behaviors;

*/
bool sysfs_streq(const char *s1, const char *s2);

#endif // __SYSFS_STREQ_H__
