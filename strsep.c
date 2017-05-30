#include "strsep.h"

char *strsep(char **s, const char *ct)
{
	char *sbegin = *s;
	char *end;

	if (sbegin == NULL)
		return NULL;

	end = strpbrk(sbegin, ct);
	//@ assert strpbrk(sbegin, ct) == end;
	if (end)
		*end++ = '\0';
	// assert strlen(sbegin) == end - 1 - sbegin;
	*s = end;
	return sbegin;
}
