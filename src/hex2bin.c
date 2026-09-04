#include "hex2bin.h"

int hex_to_bin(char ch)
{
	if ((ch >= '0') && (ch <= '9'))
		return ch - '0';
	ch = tolower(ch);
	if ((ch >= 'a') && (ch <= 'f'))
		return ch - 'a' + 10;
	return -1;
}

/*@ requires \valid(dst+(0..count));
    requires \valid_read(src+(0..2*count));
    requires \separated(dst+(0..count), src+(0..2*count));
    terminates \true;
    assigns dst[0..count-1];
    exits \false;
    behavior err_ok:
       assumes \forall integer i; 0 <= i < 2*count ==> isxdigit(src[i]);
       ensures \result == 0;
    behavior err_fail:
       assumes \exists integer i; 0 <= i < 2*count && !isxdigit(src[i]);
       ensures \result == -1;
    complete behaviors;
    disjoint behaviors;
 */
int hex2bin(u8 *dst, const char *src, size_t count)
{
	//@ ghost size_t ocount = count;
	//@ ghost char *osrc = src;
	//@ ghost u8 *odst = dst;

	/*@ loop invariant bound:  0 <= count <= ocount;
	    loop invariant srcoff: src == osrc + 2 * (ocount - count);
	    loop invariant dstoff: dst == odst + (ocount - count);
	    loop invariant hexdig: \forall integer i; 0 <= i < 2 * (ocount - count) ==>
	                           isxdigit(osrc[i]);
	    loop assigns count, src, dst, odst[0..ocount-1];
	    loop variant count;
	 */
	while (count--) {
		int hi = hex_to_bin(*src++);
		int lo = hex_to_bin(*src++);

		if ((hi < 0) || (lo < 0))
			return -1;

		//@ assert 0 <= hi < 16 && 0 <= lo < 16;
		//@ assert 0 <= hi * 16 + lo <= 255;
		/* The kernel writes '(hi << 4) | lo'. The two operands occupy
		 * disjoint nibbles, so the OR is the sum; WP proves the shift
		 * but no prover or tactic closes 'disjoint bits implies sum'
		 * within a usable budget, so the sum is written directly. */
		*dst++ = /*CODE_CHANGE:*/hi * 16 + lo;
	}
	//@ assert count == ((size_t)-1);
	return 0;
}

#ifdef DUMMY_MAIN
#include <string.h>

int main(int argc, char *argv[])
{
	const char *src = "ABCDF1011FFA";
	u8 dst[strlen(src)/2];
	hex2bin(dst, src, strlen(src)/2);
	return 0;
}
#endif
