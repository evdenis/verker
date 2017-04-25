#ifndef __STRNSTR_H__
#define __STRNSTR_H__

#include "kernel_definitions.h"
#include "memcmp.h"
#include "strlen.h"

char *strnstr(const char *s1, const char *s2, size_t len);

#endif // __STRNSTR_H__