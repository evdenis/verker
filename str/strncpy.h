#ifndef __STRNCPY_H__
#define __STRNCPY_H__

#include "kernel_definitions.h"
#include "strnlen.h"

char *strncpy(char *dest, const char *src, size_t count);

#endif // __STRNCPY_H__