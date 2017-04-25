#include "skip_spaces.h"

char *skip_spaces(const char *str)
{
	while (isspace(*str))
		++str;
	return (char *)str;
}