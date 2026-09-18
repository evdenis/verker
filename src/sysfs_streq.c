#include "sysfs_streq.h"


bool sysfs_streq(const char *s1, const char *s2)
{
	//@ ghost const char *old_s1 = s1;
	//@ ghost const char *old_s2 = s2;
	//@ ghost size_t index = 0;
	//@ ghost valid_str_len((char *)s1);
	//@ ghost valid_str_len((char *)s2);

	/*@ loop invariant bounds: 0 <= index <= strlen(old_s1) &&
	                           index <= strlen(old_s2);
	    loop invariant cursor1: s1 == old_s1 + index;
	    loop invariant cursor2: s2 == old_s2 + index;
	    loop invariant prefix: sysfs_prefix(old_s1, old_s2, index);
	    loop assigns s1, s2, index;
	    loop variant strlen(old_s1) - index;
	 */
	while (*s1 && *s1 == *s2) {
		//@ ghost index++;
		s1++;
		s2++;
	}

	if (*s1 == *s2)
		return true;

	if (!*s1 && *s2 == '\n' && !s2[1])
		return true;

	if (*s1 == '\n' && !s1[1] && !*s2)
		return true;

	return false;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && size % 2 == 0 && data[(size/2) - 1] == '\0' && data[size-1] == '\0') {
		sysfs_streq((const char *)data, (const char *)(data + size / 2));
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
int main(int argc, char *argv[])
{
	const char *s1 = "asbcd\n";
	const char *s2 = "asbcd";
	const char *s3 = "asd";

	sysfs_streq(s1, s2);
	sysfs_streq(s2, s1);
	sysfs_streq(s1, s1);
	sysfs_streq(s1, s3);

	return 0;
}
#endif
