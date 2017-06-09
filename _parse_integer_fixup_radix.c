#include "_parse_integer_fixup_radix.h"

const char *_parse_integer_fixup_radix(const char *s, unsigned int *base)
{
	if (*base == 0) {
		if (s[0] == '0') {
			if (_tolower(s[1]) == 'x' && isxdigit(s[2]))
				*base = 16;
			else
				*base = 8;
		} else
			*base = 10;
	}
	if (*base == 16 && s[0] == '0' && _tolower(s[1]) == 'x')
		s += 2;
	return s;
}

#ifdef FUZZ_MAIN

int LLVMFuzzerTestOneInput(const uint8_t *data,
                           size_t size)
{
	if (size > 3) {
		unsigned base = 0;
		_parse_integer_fixup_radix((const char *)data, &base);
		base = 16;
		_parse_integer_fixup_radix((const char *)data, &base);
	}
	return 0;
}
#endif

#ifdef DUMMY_MAIN
int main(int argc, char *argv[])
{
	unsigned int base = 16;
	_parse_integer_fixup_radix("0x", &base);
	_parse_integer_fixup_radix("0", &base);
	base = 0;
	_parse_integer_fixup_radix("0x", &base);
	_parse_integer_fixup_radix("0", &base);
	_parse_integer_fixup_radix("10", &base);
	return 0;
}
#endif
