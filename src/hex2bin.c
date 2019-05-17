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
    assigns dst[0..count-1];
    //ensures \forall char *p; src <= p < src + 2*count ==> isxdigit(*p);
    behavior err_ok:
       assumes \forall char *p; src <= p < src + 2*count ==> isxdigit(*p);
       ensures \result == 0;
    behavior err_fail:
       assumes \exists char *p; src <= p < src + 2*count && !isxdigit(*p);
       ensures \result == -1;
    complete behaviors;
    disjoint behaviors;
 */
int hex2bin(u8 *dst, const char *src, size_t count)
{
	//@ ghost size_t ocount = count;
	//@ ghost char *osrc = src;
	//@ ghost u8 *odst = dst;

	/*@ loop invariant 0 <= count <= ocount;
	    loop invariant osrc <= src <= src + 2 * ocount;
	    loop invariant (osrc - src) % 2 == 0;
	    loop invariant odst <= dst <= dst + count;
	    loop invariant ocount - count == dst - odst == (src - osrc) / 2;
	    loop invariant \forall char *p; osrc <= p < src ==> isxdigit(*p);
	    loop assigns count, src, src, odst[0..ocount-1];
	    loop variant count;
	 */
	while (count-- AENOC) {
		int hi = hex_to_bin(*src++);
		int lo = hex_to_bin(*src++);

		if ((hi < 0) || (lo < 0))
			return -1;

		//@ assert 0 <= hi < 16 && 0 <= lo < 16;
		//@ assert (hi << 4) == hi * 16;
		//@ assert ((hi << 4) | lo) == hi * 16 + lo;
		//@ assert 0 <= (hi << 4) <= 240;
		//@ assert 0 <= ((hi << 4) | lo) <= 255;
		*dst++ = (hi << 4) | lo;
	}
	//@ assert count == ((size_t AENO)-1);
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
