#include "memscan.h"

void *memscan(void *addr, int c, size_t size)
{
	unsigned char *p = addr;

	/*@ loop invariant 0 <= size <= \at(size,Pre);
	    loop invariant p - (u8 *)addr == \at(size,Pre) - size;
	    loop invariant \base_addr(p) == \base_addr((u8 *)addr);
	    loop invariant (u8 *)addr <= p <= (u8 *)addr + \at(size,Pre);
	    loop invariant \forall integer i; 0 <= i < \at(size,Pre) - size ==>
	                   ((u8 *)addr)[i] != c;
	    loop variant size;
	 */
	while (size) {
		if (*p == c)
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
