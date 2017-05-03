#include "check_bytes8.h"

/*@ requires \valid(start+(0..bytes-1));
    assigns \nothing;
    behavior found:
       assumes \exists integer i; 0 <= i < bytes && start[i] == value;
       ensures \base_addr(start) == \base_addr(\result);
       ensures start <= (u8 *)\result <= start + bytes;
       ensures \exists integer i; 0 <= i < bytes &&
               (\forall integer j; 0 <= j < i ==> start[j] != value) &&
               start[i] == value &&
               \result == start + i;
    behavior not_exists:
       assumes \forall integer i; 0 <= i < bytes ==> start[i] != value;
       ensures \result == start + bytes;
    complete behaviors;
    disjoint behaviors;
 */
static void *check_bytes8(const u8 *start, u8 value, unsigned int bytes)
{
	/*@ loop invariant 0 <= bytes <= \at(bytes,Pre);
	    loop invariant \base_addr(\at(start,Pre)) == \base_addr(start);
	    loop invariant \at(start,Pre) <= start <= \at(start,Pre) + \at(bytes,Pre);
	    loop invariant \at(start,Pre) - start == \at(bytes,Pre) - bytes;
	    loop invariant \forall integer i; 0 <= i < \at(bytes,Pre) - bytes ==>
	                   \at(start,Pre)[i] != value;
	    loop variant bytes;
	 */
	while (bytes) {
		if (*start != value)
			return (void *)start;
		start++;
		bytes--;
	}
	return NULL;
}
