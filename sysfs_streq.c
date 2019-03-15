#include "sysfs_streq.h"

/*@ axiomatic SysfsStr {
    predicate newline_end(char *s) = s[0] == '\n' && s[1] == '\0';
    predicate sysfs_strend(char *s) = s[0] == '\0' || newline_end(s);
    logic size_t sysfs_strend_len(char *s) = s[strlen(s) - 1] == '\n' ? (size_t)(strlen(s) - 1) : strlen(s);
    }
 */

/*@ requires valid_str(s1);
    requires valid_str(s2);
    assigns \nothing;
    ensures \forall integer i; 0 <= i < \min(sysfs_strend_len(s1),sysfs_strend_len(s2)) ==>
       s1[i] == s2[i];
    //ensures \forall integer i; sysfs_strend_len(s1) <= i <= strlen(s1) ==>
    //   sysfs_strend(s1+i) && sysfs_strend(s2+i);
*/
bool sysfs_streq(const char *s1, const char *s2)
{
	//@ ghost char *os1 = s1, *os2 = s2;
	/*@ loop invariant os1 <= s1 <= os1 + strlen(os1);
	    loop invariant os2 <= s2 <= os2 + strlen(os2);
	    loop invariant s1 - os1 == s2 - os2;
	    loop invariant valid_str(s1) && valid_str(s2);
	    loop invariant \forall integer i; 0 <= i < s1 - os1 ==> os1[i] == os2[i];
	    loop assigns s1, s2;
	    loop variant strlen(os1) - (s1 - os1);
	 */
	while (*s1 && *s1 == *s2) {
		s1++;
		s2++;
	}

	if (*s1 == *s2)
		//@ assert *s1 == *s2 == '\0';
		//@ assert strlen(os1) == strlen(os2);
		//@ assert \forall integer i; 0 <= i <= strlen(os1) ==> os1[i] == os2[i];
		//@ assert s1 > os1 ==> s1[-1] == s2[-1];
		//@ assert s1 > os1 ==> s1[-1] == '\n' || s1[-1] != '\n';
		//@ assert sysfs_strend_len(os1) == sysfs_strend_len(os2);
		return true;
	if (!*s1 && *s2 == '\n' && !s2[1])
		//@ assert *s1 == '\0' && newline_end(s2);
		//@ assert sysfs_strend_len(os2) == (size_t)(s2 - os2);
		return true;
	if (*s1 == '\n' && !s1[1] && !*s2)
		//@ assert newline_end(s1) && *s2 == '\0';
		//@ assert sysfs_strend_len(os1) == (size_t)(s1 - os1);
		return true;
	//@ assert !sysfs_strend(s1) || !sysfs_strend(s2);
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
