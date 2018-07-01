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


#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	char change[] = "abc1d2e3g4";
	const char *sep = "1234567890";
	char *res = change;

	strsep(&res, sep);
	strsep(&res, sep);
	strsep(&res, sep);
	strsep(&res, sep);
	strsep(&res, sep);

	return 0;
}
#endif
