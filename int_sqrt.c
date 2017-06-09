#include "int_sqrt.h"

/*@ assigns \nothing;
 */
unsigned long int_sqrt(unsigned long x)
{
	unsigned long b, m, y = 0;

	if (x <= 1)
		return x;

	m = 1UL << (BITS_PER_LONG - 2);
	/*@
	    loop variant m;
	 */
	while (m != 0) {
		b = y + m;
		y >>= 1;

		if (x >= b) {
			x -= b;
			y += m;
		}
		m >>= 2;
	}

	return y;
}

#ifdef DUMMY_MAIN

int main(int argc, char *argv[])
{
	int_sqrt(0);
	int_sqrt(2);
	int_sqrt(16);
	int_sqrt(25);
	int_sqrt(30);
	return 0;
}
#endif