#include "memscan.h"

void *memscan(void *addr, int c, size_t size)
{
	char *p = /*CODE_CHANGE:*/addr;

	/*@ loop invariant bound:   0 <= size <= \at(size,Pre);
	    loop invariant offset:  p == (char *)addr + (\at(size,Pre) - size);
	    loop invariant nomatch: \forall integer i; 0 <= i < \at(size,Pre) - size ==>
	                            (unsigned char)((char *)addr)[i] != c;
	    loop assigns p, size;
	    loop variant size;
	 */
	while (size) {
		if (/*CODE_CHANGE:*/(unsigned char)*p == c)
			return (void *)p;
		p++;
		size--;
	}
	return (void *)p;
}


#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 1) {
		memscan((void *)data, data[size - 1], size - 1);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	char *s = "123456788889";

	memscan(s, '6', strlen(s));
	memscan(s, '8', strlen(s));
	memscan(s, '\0', strlen(s));

	return 0;
}
#endif
