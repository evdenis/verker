#include "memzero_explicit.h"

void memzero_explicit(void *s, size_t count)
{
	memset(s, 0, count);
	barrier_data(s);
}