#ifndef __STRLCAT_H__
#define __STRLCAT_H__

#include "kernel_definitions.h"
#include "strlen.h"

size_t strlcat(char *dest, const char *src, size_t count);

#endif // __STRLCAT_H__