#ifndef __STRSEP_H__
#define __STRSEP_H__

#include "kernel_definitions.h"
#include "strpbrk.h"

/**
 * strsep - Split a string into tokens
 * @s: The string to be searched
 * @ct: The characters to search for
 *
 * strsep() updates @s to point after the token, ready for the next call.
 *
 * It returns empty tokens, too, behaving exactly like the libc function
 * of that name. In fact, it was stolen from glibc2 and de-fancy-fied.
 * Same semantics, slimmer shape. ;)
 */

char *strsep(char **s, const char *ct);

#endif // __STRSEP_H__