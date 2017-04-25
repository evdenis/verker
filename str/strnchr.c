#include "strnchr.h"

char *strnchr(const char *s, size_t count, int c)
{
	for (; count-- && *s != '\0'; ++s)
		if (*s == (char)c)
			return (char *)s;
	return NULL;
}