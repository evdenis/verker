#ifndef __STRNCMP_H__
#define __STRNCMP_H__

#include "kernel_definitions.h"
#include "strnlen.h"

/**
 * strncmp - Compare two length-limited strings
 * @cs: One string
 * @ct: Another string
 * @count: The maximum number of bytes to compare
 */

int strncmp(const char *cs, const char *ct, size_t count);

#endif // __STRNCMP_H__