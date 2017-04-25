#ifndef __MEMSCAN_H__
#define __MEMSCAN_H__

#include "kernel_definitions.h"

void *memscan(void *addr, int c, size_t size);

#endif // __MEMSCAN_H__