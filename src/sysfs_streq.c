#include "sysfs_streq.h"


bool sysfs_streq(const char *s1, const char *s2)
{
	//@ ghost const char* old_s1 = s1;
	//@ ghost const char* old_s2 = s2;
	//@ ghost size_t index = 0;

	/*@ loop invariant s1 == old_s1 + index;
	    loop invariant s2 == old_s2 + index;

	    loop invariant \valid(s1);
	    loop invariant \valid(s2);

	    loop invariant index <= strlen(old_s1);
	    loop invariant index <= strlen(old_s2);

	    loop invariant \forall size_t i; 0 <= i < index ==> old_s1[i] == old_s2[i];

	    loop invariant strncmp(old_s1, old_s2, index);

	    loop assigns s1;
	    loop assigns s2;
	    loop assigns index;

	    loop variant \max(strlen(old_s1), strlen(old_s2)) - index;
	*/
	while (*s1 && *s1 == *s2) {
		//@ ghost index++;
		s1++;
		s2++;
	}

	//@ assert \forall size_t i; 0 <= i < index ==> old_s1[i] == old_s2[i];
	//@ assert \forall size_t i; 0 <= i < index ==> old_s1[i] != '\0';
	//@ assert \forall size_t i; 0 <= i < index ==> old_s2[i] != '\0';

	if (*s1 == *s2)
		//@ assert *s1 == '\0';
		//@ assert *s2 == '\0';
		//@ assert sysfs_strlen(old_s1) == sysfs_strlen(old_s2);
		return true;

	if (!*s1 && *s2 == '\n' && !s2[1])
		//@ assert sysfs_strlen(s1) == sysfs_strlen(s2);
		//@ assert strncmp(s1, s2, sysfs_strlen(s2)) == true;
		//@ assert s2[0] == '\n';
		//@ assert s2[0] != '\0';
		//@ assert s2 == old_s2 + index;
		//@ assert old_s2[index] == '\n';
		//@ assert old_s2[index + 1] == '\0';
		//@ assert index == sysfs_strlen(old_s2);
		return true;

	if (*s1 == '\n' && !s1[1] && !*s2)
		//@ assert sysfs_strlen(s1) == sysfs_strlen(s2);
		//@ assert strncmp(s1, s2, sysfs_strlen(s1)) == true;
		//@ assert s1[0] == '\n';
		//@ assert s1[0] != '\0';
		//@ assert s1 == old_s1 + index;
		//@ assert old_s1[index] == '\n';
		//@ assert old_s1[index + 1] == '\0';
		//@ assert index == sysfs_strlen(old_s1);
		return true;

	//@ assert (*s1 == '\0') ==> ((*s2 != '\n') || (s2[1] != '\0'));
	//@ assert (*s2 == '\0') ==> ((*s1 != '\n') || (s1[1] != '\0'));
	//@ assert ((*s1 != '\0') && (*s2 != '\0')) ==> (*s1 != *s2);

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
