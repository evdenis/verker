#ifndef __STRLCPY_H__
#define __STRLCPY_H__

#include "kernel_definitions.h"
#include "strlen.h"

size_t strlcpy(char *dest, const char *src, size_t size);

#endif // __STRLCPY_H__