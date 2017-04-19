#include <defs.h>
#include <ctype.h>

typedef unsigned long __kernel_ulong_t;

typedef unsigned int u32;

typedef unsigned long long u64;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_size_t size_t;

/**
 * strncasecmp - Case insensitive, length-limited string comparison
 * @s1: One string
 * @s2: The other string
 * @len: the maximum number of characters to compare
 */
int strncasecmp(const char *s1, const char *s2, size_t len)
{
	/* Yes, Virginia, it had better be unsigned */
	unsigned char c1, c2;

	if (!len)
		return 0;

	do {
		c1 = *s1++;
		c2 = *s2++;
		if (!c1 || !c2)
			break;
		if (c1 == c2)
			continue;
		c1 = tolower(c1);
		c2 = tolower(c2);
		if (c1 != c2)
			break;
	} while (--len);
	return (int)c1 - (int)c2;
}
EXPORT_SYMBOL(strncasecmp);

/*@ requires \valid(s1);
 */
int strcasecmp(const char *s1, const char *s2)
{
	int c1, c2;

	do {
		c1 = tolower(*s1++);
		c2 = tolower(*s2++);
	} while (c1 == c2 && c1 != 0);
	return c1 - c2;
}
EXPORT_SYMBOL(strcasecmp);

/**
 * strcpy - Copy a %NUL terminated string
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 */
char *strcpy(char *dest, const char *src)
{
	char *tmp = dest;

	while ((*dest++ = *src++) != '\0')
		/* nothing */;
	return tmp;
}
EXPORT_SYMBOL(strcpy);

/**
 * strncpy - Copy a length-limited, C-string
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 * @count: The maximum number of bytes to copy
 *
 * The result is not %NUL-terminated if the source exceeds
 * @count bytes.
 *
 * In the case where the length of @src is less than  that  of
 * count, the remainder of @dest will be padded with %NUL.
 *
 */
char *strncpy(char *dest, const char *src, size_t count)
{
	char *tmp = dest;

	while (count) {
		if ((*tmp = *src) != 0)
			src++;
		tmp++;
		count--;
	}
	return dest;
}
EXPORT_SYMBOL(strncpy);

/**
 * strcat - Append one %NUL-terminated string to another
 * @dest: The string to be appended to
 * @src: The string to append to it
 */
char *strcat(char *dest, const char *src)
{
	char *tmp = dest;

	while (*dest)
		dest++;
	while ((*dest++ = *src++) != '\0')
		;
	return tmp;
}
EXPORT_SYMBOL(strcat);

/**
 * strcmp - Compare two strings
 * @cs: One string
 * @ct: Another string
 */
int strcmp(const char *cs, const char *ct)
{
	unsigned char c1, c2;

	while (1) {
		c1 = *cs++;
		c2 = *ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
	}
	return 0;
}
EXPORT_SYMBOL(strcmp);

/**
 * strncmp - Compare two length-limited strings
 * @cs: One string
 * @ct: Another string
 * @count: The maximum number of bytes to compare
 */
int strncmp(const char *cs, const char *ct, size_t count)
{
	unsigned char c1, c2;

	while (count) {
		c1 = *cs++;
		c2 = *ct++;
		if (c1 != c2)
			return c1 < c2 ? -1 : 1;
		if (!c1)
			break;
		count--;
	}
	return 0;
}
EXPORT_SYMBOL(strncmp);

/**
 * strchr - Find the first occurrence of a character in a string
 * @s: The string to be searched
 * @c: The character to search for
 */
char *strchr(const char *s, int c)
{
	for (; *s != (char)c; ++s)
		if (*s == '\0')
			return NULL;
	return (char *)s;
}
EXPORT_SYMBOL(strchr);

/**
 * strchrnul - Find and return a character in a string, or end of string
 * @s: The string to be searched
 * @c: The character to search for
 *
 * Returns pointer to first occurrence of 'c' in s. If c is not found, then
 * return a pointer to the null byte at the end of s.
 */
char *strchrnul(const char *s, int c)
{
	while (*s && *s != (char)c)
		s++;
	return (char *)s;
}
EXPORT_SYMBOL(strchrnul);

/**
 * strrchr - Find the last occurrence of a character in a string
 * @s: The string to be searched
 * @c: The character to search for
 */
char *strrchr(const char *s, int c)
{
	const char *last = NULL;
	do {
		if (*s == (char)c)
			last = s;
	} while (*s++);
	return (char *)last;
}
EXPORT_SYMBOL(strrchr);

/**
 * strnchr - Find a character in a length limited string
 * @s: The string to be searched
 * @count: The number of characters to be searched
 * @c: The character to search for
 */
char *strnchr(const char *s, size_t count, int c)
{
	for (; count-- && *s != '\0'; ++s)
		if (*s == (char)c)
			return (char *)s;
	return NULL;
}
EXPORT_SYMBOL(strnchr);

/**
 * skip_spaces - Removes leading whitespace from @str.
 * @str: The string to be stripped.
 *
 * Returns a pointer to the first non-whitespace character in @str.
 */
char *skip_spaces(const char *str)
{
	while (isspace(*str))
		++str;
	return (char *)str;
}
EXPORT_SYMBOL(skip_spaces);

#define SIZE_MAX (~((size_t)(0)))

/*@ axiomatic Strings {
    predicate is_string(char *s) =
	    \exists integer n;
		    0 <= n <= SIZE_MAX &&
		    s[n] == '\0';
    predicate is_valid_string(char *s) =
	    \exists integer n;
		    0 <= n <= SIZE_MAX &&
			 s[n] == '\0' &&
			 \valid(s+(0..n));
	 lemma string_validity:
	    \forall char *s; is_valid_string(s) ==> is_string(s);
	 logic integer strlen(char *s) = //reads s[0..] =
	    s[0] == '\0' ? 0 : 1 + strlen(++s);

	 lemma strlen_diaposone_down:
	    \forall char *s; is_valid_string(s) ==> 0 <= strlen(s);

	 axiom strlen_diaposone_up:
	    \forall char *s; is_valid_string(s) ==> strlen(s) <= SIZE_MAX;

	 lemma strlen_before_null:
       \forall char* s, integer i;
		 is_valid_string(s) &&
		 0 <= i < strlen(s) ==> s[i] != '\0';

    lemma strlen_at_null:
       \forall char* s; is_valid_string(s) ==> s[strlen(s)] == '\0';

    lemma strlen_create:
       \forall char* s, integer i;
	       is_valid_string(s) &&
          0 <= i <= SIZE_MAX &&
	       s[i] == '\0' ==> 0 <= strlen(s) <= i;
    }
 */

/**
 * strlen - Find the length of a string
 * @s: The string to be sized
 */
/*@ requires is_valid_string(s);
    assigns \nothing;
	 ensures \result == strlen(s);
 */
size_t strlen(const char *s)
{
	const char *sc;
   /*@ loop invariant s <= sc <= s + strlen(s);
	    loop invariant \forall integer i; 0 <= i < sc - s ==> s[i] != '\0';
	    loop variant strlen(s) - (sc - s);
	 */
	for (sc = s; *sc != '\0'; ++sc)
		/* nothing */;
	return sc - s;
}
EXPORT_SYMBOL(strlen);

/**
 * strreplace - Replace all occurrences of character in string.
 * @s: The string to operate on.
 * @old: The character being replaced.
 * @new: The character @old is replaced with.
 *
 * Returns pointer to the nul byte at the end of @s.
 */
char *strreplace(char *s, char old, char new)
{
	for (; *s; ++s)
		if (*s == old)
			*s = new;
	return s;
}
EXPORT_SYMBOL(strreplace);
