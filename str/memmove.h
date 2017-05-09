#ifndef __MEMMOVE_H__
#define __MEMMOVE_H__

#include "kernel_definitions.h"

/**
 * memmove - Copy one area of memory to another
 * @dest: Where to copy to
 * @src: Where to copy from
 * @count: The size of the area.
 *
 * Unlike memcpy(), memmove() copes with overlapping areas.
 */

void *memmove(void *dest, const void *src, size_t count);

#endif // __MEMMOVE_H__