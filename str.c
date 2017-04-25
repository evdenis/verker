#include <defs.h>
#include <ctype.h>

typedef unsigned long __kernel_ulong_t;

typedef unsigned int u32;

typedef unsigned long long u64;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_size_t size_t;

/*@ axiomatic Strings {
    predicate valid_string(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));

    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));

    lemma strlen_before_null:
       \forall char* s, integer i;
          valid_string(s) &&
          0 <= i < strlen(s) ==> s[i] != '\0';

    lemma strlen_at_null:
       \forall char* s;
          valid_string(s) ==> s[strlen(s)] == '\0';

    lemma strlen_shift:
       \forall char *s, size_t i;
          valid_string(s) &&
          i <= strlen(s)  ==>
          strlen(s+i) == strlen(s) + i;
    }
 */


/**
 * strncasecmp - Case insensitive, length-limited string comparison
 * @s1: One string
 * @s2: The other string
 * @len: the maximum number of characters to compare
 */
/*@ requires valid_string(s1);
    requires valid_string(s2);
    requires \base_addr(s1) == \base_addr(s2) || \base_addr(s1) != \base_addr(s2);
	 assigns \nothing;
	 behavior zero_len:
	    assumes len == 0;
		 ensures \result == 0;
 */
int strncasecmp(const char *s1, const char *s2, size_t len)
{
	/* Yes, Virginia, it had better be unsigned */
	unsigned char c1, c2;

	if (!len)
		return 0;

   /*@ loop invariant 0 <= len;
       loop invariant \base_addr(s1) == \base_addr{Pre}(s1);
       loop invariant \base_addr(s2) == \base_addr{Pre}(s2);
       loop invariant \forall char *s; \base_addr(s1) == \base_addr(s) && \at(s1,Pre) <= s < s1 ==> *s != '\0';
       loop invariant \forall char *s; \base_addr(s2) == \base_addr(s) && \at(s2,Pre) <= s < s2 ==> *s != '\0';
       loop invariant \forall size_t i; i < s1 - \at(s1,Pre) ==> tolower(*(\at(s1,Pre)+i)) == tolower(*(\at(s2,Pre)+i));
       loop variant len;
    */
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

/*@ requires valid_string(s1);
    requires valid_string(s2);
    assigns \nothing;
    //ensures \forall size_t i; i <= \min(strlen(s1), strlen(s2)) ==> s1[i] == s2[i];
 */
int strcasecmp(const char *s1, const char *s2)
{
	int c1, c2;

   /*@ loop invariant \base_addr(s1) == \base_addr(\at(s1,Pre));
       loop invariant \base_addr(s2) == \base_addr(\at(s2,Pre));
       loop invariant \at(s1,Pre) <= s1 <= \at(s1,Pre) + \min(strlen(\at(s1,Pre)),strlen(\at(s2,Pre)));
       loop invariant \at(s2,Pre) <= s2 <= \at(s2,Pre) + \min(strlen(\at(s1,Pre)),strlen(\at(s2,Pre)));
       loop invariant \forall size_t i; i < s1 - \at(s1,Pre) ==> tolower(s1[i]) == tolower(s2[i]);
       loop variant strlen(s1);
    */
	do {
		c1 = tolower(*s1++);
		c2 = tolower(*s2++);
	} while (c1 == c2 && c1 != 0);
   //@ assert c1 != c2 || c1 == 0 && c2 == 0;
	return c1 - c2;
}
EXPORT_SYMBOL(strcasecmp);

/* predicate same_base_addr{L1,L2}(char *s) =
       \base_addr{L1}(\at(s,L1)) == \base_addr{L2}(\at(s,L2));
 */

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
/*@ requires valid_string(src);
    requires \valid(dest+(0..\min(strlen(src),count)));
 */
char *strncpy(char *dest, const char *src, size_t count)
{
	char *tmp = dest;

	/*@ loop invariant count >= 0;
	    loop variant count;
	 */
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
/*@ requires valid_string(src);
    requires valid_string(dest) && \valid(dest+(0..strlen(dest)+strlen(src)-1));
	 assigns dest[strlen(dest)..strlen(dest)+strlen(src)-1];
 */
char *strcat(char *dest, const char *src)
{
	char *tmp = dest;

	while (*dest)
		dest++;
	//@ assert *dest == '\0';
	while ((*dest++ = *src++) != '\0')
		;
	return tmp;
}
EXPORT_SYMBOL(strcat);

/**
 * strncmp - Compare two length-limited strings
 * @cs: One string
 * @ct: Another string
 * @count: The maximum number of bytes to compare
 */
int strncmp(const char *cs, const char *ct, size_t count)
{
	unsigned char c1, c2;
	/*@ loop invariant count >= 0;
	    loop variant count;
	 */
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
/*@ requires valid_string(s);
    requires -128 <= c <= 127;
    assigns \nothing;
 */
char *strchr(const char *s, int c)
{
   //@ ghost char *old_s = s;
   /*@ loop invariant \base_addr(s) == \base_addr(old_s);
       loop invariant old_s <= s <= old_s + strlen(old_s);
       loop variant strlen(old_s) - (s - old_s);
    */
	for (; *s != (char)c; ++s)
		if (*s == '\0')
			return NULL;
   //@ assert *s == '\0' || *s == c;
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

#define SIZE_MAX 32000

/**
 * skip_spaces - Removes leading whitespace from @str.
 * @str: The string to be stripped.
 *
 * Returns a pointer to the first non-whitespace character in @str.
 */
/*@ requires \forall size_t i; isspace(*(str+i)) ==> \valid(str+i);
    assigns \nothing;
	 ensures \base_addr(\result) == \base_addr(str);
	 ensures !isspace(*\result);
	 ensures \exists size_t i; str + i == \result &&
	         (\forall size_t j; j < i ==> isspace(str[j]));
 */
char *skip_spaces(const char *str)
{
	/*@ loop invariant \forall size_t s; s < str - \at(str, Pre) ==> isspace(str[s]);
	    loop variant SIZE_MAX - (str - \at(str,Pre));
	 */
	while (isspace(*str))
		++str;
	return (char *)str;
}
EXPORT_SYMBOL(skip_spaces);

/**
 * strreplace - Replace all occurrences of character in string.
 * @s: The string to operate on.
 * @old: The character being replaced.
 * @new: The character @old is replaced with.
 *
 * Returns pointer to the nul byte at the end of @s.
 */
/*@ requires valid_string(s);
    assigns s[0..strlen(s)];
 */
char *strreplace(char *s, char old, char new)
{
   /*@ loop invariant \base_addr(s) == \base_addr(\at(s,Pre));
       loop invariant \at(s,Pre) <= s <= \at(s,Pre) + strlen(\at(s,Pre));
       loop invariant \forall size_t i; i < s - \at(s,Pre) && \at(s[i],Pre) != old ==> \at(s[i],Pre) == s[i];
       loop invariant \forall size_t i; i < s - \at(s,Pre) && \at(s[i],Pre) == old ==> s[i] == new;
       loop variant strlen(s);
    */
	for (; *s; ++s)
		if (*s == old)
			*s = new;
	return s;
}
EXPORT_SYMBOL(strreplace);
