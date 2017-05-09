#include "kstrbool.h"

int kstrtobool(const char *s, bool *res)
{
	if (!s)
		return -EINVAL;

	switch (s[0]) {
	case 'y':
	case 'Y':
	case '1':
		*res = true;
		return 0;
	case 'n':
	case 'N':
	case '0':
		*res = false;
		return 0;
	case 'o':
	case 'O':
		switch (s[1]) {
		case 'n':
		case 'N':
			*res = true;
			return 0;
		case 'f':
		case 'F':
			*res = false;
			return 0;
		default:
			break;
		}
	default:
		break;
	}

	return -EINVAL;
}
