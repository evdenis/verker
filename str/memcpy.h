#ifndef __MEMCPY_H__
#define __MEMCPY_H__

#include "kernel_definitions.h"

/**
 * memcpy - Copy one area of memory to another
 * @dest: Where to copy to
 * @src: Where to copy from
 * @count: The size of the area.
 *
 * You should not use this function to access IO space, use memcpy_toio()
 * or memcpy_fromio() instead.
 */

void *memcpy(void *dest, const void *src, size_t count);

#endif // __MEMCPY_H__
