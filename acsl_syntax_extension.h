#ifndef ACSL_SYNTAX_EXTENSION_H
#define ACSL_SYNTAX_EXTENSION_H 1

#ifndef ASTRAVER_TOOLCHAIN /* used by default */
# define FRAMAC_ISSPACE_BUG || c == '\v'
#else
# define FRAMAC_ISSPACE_BUG
#endif

#endif /* ACSL_SYNTAX_EXTENSION_H */
