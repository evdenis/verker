#ifndef __MEMCHR_INV_H__
#define __MEMCHR_INV_H__

#include "kernel_definitions.h"
#include "check_bytes8.h"

void *memchr_inv(const void *start, int c, size_t bytes);

#endif // __MEMCHR_INV_H__