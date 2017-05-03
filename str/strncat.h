#ifndef __STRNCAT_H__
#define __STRNCAT_H__

#include "kernel_definitions.h"
#include "strlen.h"
#include "strnlen.h"

char *strncat(char *dest, const char *src, size_t count);

#endif // __STRNCAT_H__
