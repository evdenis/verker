#ifndef __MEMCMP_H__
#define __MEMCMP_H__

#include "kernel_definitions.h"

/**
 * memcmp - Compare two areas of memory
 * @cs: One area of memory
 * @ct: Another area of memory
 * @count: The size of the area.
 */

__visible int memcmp(const void *cs, const void *ct, size_t count);

#endif // __MEMCMP_H__
