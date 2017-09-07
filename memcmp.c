#include "memcmp.h"

/*@ axiomatic Mem {
    logic integer memcmp{L}(char *cs, char *ct, integer count);
    axiom eq{L}:
         \forall integer i, char *cs, *ct;
         0 <= i && \valid(cs+(0..i)) && \valid(ct+(0..i)) &&
         cs[i] == ct[i] <==>
            memcmp(cs, ct, i) == 0;
    axiom lt{L}:
         \exists integer i, char *cs, *ct;
         0 <= i && \valid(cs+(0..i)) && \valid(ct+(0..i)) &&
         (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
         cs[i] < ct[i] <==>
            memcmp(cs, ct, i) < 0;
    axiom gt{L}:
         \exists integer i, char *cs, *ct;
         0 <= i && \valid(cs+(0..i)) && \valid(ct+(0..i)) &&
         (\forall integer j; 0 <= j < i ==> cs[j] == ct[j]) &&
         cs[i] > ct[i] <==>
            memcmp{L}(cs, ct, i) > 0;
    }
 */

/*@ requires \typeof(cs) <: \type(u8 *);
    requires \typeof(ct) <: \type(u8 *);
    requires \valid(((u8 *)cs)+(0..count-1));
    requires \valid(((u8 *)ct)+(0..count-1));
    requires \base_addr((u8 *)cs) == \base_addr((u8 *)ct) ^^
             \base_addr((u8 *)cs) != \base_addr((u8 *)ct);
    assigns \nothing;
    ensures \result == 0 <==> memcmp((char *)cs, (char *)ct, count) == 0;
    ensures \result < 0  <==> memcmp((char *)cs, (char *)ct, count) < 0;
    ensures \result > 0  <==> memcmp((char *)cs, (char *)ct, count) > 0;
    behavior equal:
       assumes \forall integer i; 0 <= i < count ==> ((u8 *)cs)[i] == ((u8 *)ct)[i];
       ensures \result == 0;
    behavior diff:
       assumes \exists integer i; 0 <= i < count && ((u8 *)cs)[i] != ((u8 *)ct)[i];
       ensures \exists integer i; 0 <= i < count &&
               (\forall integer j; 0 <= j < i ==> ((u8 *)cs)[j] == ((u8 *)ct)[j]) &&
               ((u8 *)cs)[i] != ((u8 *)ct)[i] &&
               \result == ((u8 *)cs)[i] - ((u8 *)ct)[i];
    complete behaviors;
    disjoint behaviors;
 */
__visible int memcmp(const void *cs, const void *ct, size_t count)
{
	const unsigned char *su1, *su2;
	int res = 0;

	/*@ loop invariant 0 <= count <= \at(count,Pre);
	    loop invariant (u8 *)cs <= su1 <= (u8 *)cs + \at(count,Pre);
	    loop invariant (u8 *)ct <= su2 <= (u8 *)ct + \at(count,Pre);
	    loop invariant su1 - (u8 *)cs ==
	                   su2 - (u8 *)ct ==
	                   \at(count,Pre) - count;
	    loop invariant \forall integer i; 0 <= i < \at(count,Pre) - count ==>
	                   ((u8 *)cs)[i] == ((u8 *)ct)[i];
	    loop invariant memcmp((char *)cs, (char *)ct, \at(count,Pre)) ==
	                   memcmp((char *)su1, (char *)su2, count);
	    loop invariant res == 0;
	    loop assigns res;
	    loop variant count;
	 */
	for (su1 = cs, su2 = ct; 0 < count; ++su1, ++su2, count--)
		if ((res = *su1 - *su2) != 0)
			break;

	return res;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size % 2 == 0) {
		memcmp(data, data + size / 2, size / 2);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int src[]  = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
	int dest[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
	int res;
	res = memcmp(dest, src, sizeof(src));
	dest[ARRAY_SIZE(dest)-1]--;
	res = memcmp(dest, src, sizeof(src));
	dest[ARRAY_SIZE(dest)-1]+=2;
	res = memcmp(dest, src, sizeof(src));
	res = res;
	return 0;
}
#endif
