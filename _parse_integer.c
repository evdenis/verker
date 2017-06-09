#include "_parse_integer.h"

/*@ requires valid_str(s);
    requires \valid(p);
    requires base % 2 == 0 && base <= 16;
 */
unsigned int _parse_integer(const char *s, unsigned int base, unsigned long long *p)
{
	unsigned long long res;
	unsigned int rv;

	res = 0;
	rv = 0;
	while (*s) {
		unsigned int val;

		if ('0' <= *s && *s <= '9')
			val = *s - '0';
		else if ('a' <= _tolower(*s) && _tolower(*s) <= 'f')
			val = _tolower(*s) - 'a' + 10;
		else
			break;

		if (val >= base)
			break;
		/*
		 * Check for overflow only if we are within range of
		 * it in the max base we support (16)
		 */
		if (unlikely(res & (~0ull << 60))) {
			if (res > div_u64(ULLONG_MAX - val, base))
				rv |= KSTRTOX_OVERFLOW;
		}
		res = res * base + val;
		rv++;
		s++;
	}
	*p = res;
	return rv;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 0 && data[size-1] == '\0') {
		unsigned long long res;
		_parse_integer((const char *)data, 1, &res);
		_parse_integer((const char *)data, 2, &res);
		_parse_integer((const char *)data, 4, &res);
		_parse_integer((const char *)data, 8, &res);
		_parse_integer((const char *)data, 10, &res);
		_parse_integer((const char *)data, 16, &res);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
int main(int argc, char *argv[])
{
	unsigned long long res;
	_parse_integer("000000", 1, &res);
	_parse_integer("101010101", 2, &res);
	_parse_integer("101232", 4, &res);
	_parse_integer("012345670", 8, &res);
	_parse_integer("1234567890", 10, &res);
	_parse_integer("0xff", 16, &res);
	_parse_integer("0xffabcde0010fffffffff", 16, &res);
	return 0;
}
#endif
