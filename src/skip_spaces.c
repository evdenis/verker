#include "skip_spaces.h"

char *skip_spaces(const char *str)
{
	//@ ghost char *ostr = (char *)str;
	//@ ghost size_t k = 0;
	/*@ loop invariant valid:  valid_str(str);
	    loop invariant idx:    str == ostr + k;
	    loop invariant bound:  0 <= k <= strlen(ostr);
	    loop invariant len:    strlen(ostr) == strlen(str) + k;
	    loop invariant spaces: \forall integer i; 0 <= i < k ==> isspace(ostr[i]);
	    loop assigns str, k;
	    loop variant strlen(ostr) - k;
	 */
	while (isspace(*str)) {
		//@ ghost valid_str_shift((char *)str);
		++str;
		//@ ghost k++;
	}
	//@ ghost valid_str_len(ostr);
	//@ ghost skip_spaces_defn(ostr, k);
	//@ ghost skip_spaces_range(ostr);
	return (char *)str;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && data[size-1] == '\0') {
		skip_spaces((const char *)data);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	skip_spaces("   123");
	skip_spaces("");

	return 0;
}
#endif
