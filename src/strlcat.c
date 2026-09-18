#include "strlcat.h"

size_t strlcat(char *dest, const char *src, size_t count)
{
	//@ ghost char *odest = dest;
	//@ ghost char *osrc = (char *)src;
	//@ ghost valid_str_len(odest);
	//@ ghost valid_str_len(osrc);
	size_t dsize = strlen(dest);
	size_t len = strlen(src);
	size_t res = dsize + len;

	dest += dsize;
	//@ assert cursor: dest == odest + dsize;
	//@ assert terminator: *dest == '\0';
	count -= dsize;
	if (len >= count)
		len = count-1;
	//@ assert room: len < count;
	memcpy(dest, src, len);
	//@ assert copied: \forall integer i; 0 <= i < len ==> odest[dsize + i] == \at(src[i], Pre);
	dest[len] = 0;
	//@ ghost intro_valid_str_len(dest, len);
	//@ ghost intro_valid_str_len(odest, (size_t)(dsize + len));
	return res;
}

#ifdef DUMMY_MAIN
#include <assert.h>
#include <string.h>

int main(void)
{
	char full[8] = "ab";
	char truncated[6] = {'a', 'b', 0, 'X', 'Y', 'Z'};
	char no_room[4] = {'a', 'b', 0, 'X'};

	assert(strlcat(full, "cd", sizeof(full)) == 4);
	assert(strcmp(full, "abcd") == 0);
	assert(strlcat(truncated, "cde", 4) == 5);
	assert(strcmp(truncated, "abc") == 0);
	assert(truncated[4] == 'Y' && truncated[5] == 'Z');
	assert(strlcat(no_room, "cd", 3) == 4);
	assert(strcmp(no_room, "ab") == 0 && no_room[3] == 'X');
	assert(strlcat(full, "", sizeof(full)) == 4);
	return 0;
}
#endif
