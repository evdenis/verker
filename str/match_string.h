#ifndef __MATCH_STRING_H__
#define __MATCH_STRING_H__

#include "kernel_definitions.h"
#include "strcmp.h"

ssize_t match_string(const char * const *array, size_t n, const char *string);

#endif // __MATCH_STRING_H__