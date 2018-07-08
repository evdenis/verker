#ifndef ACSL_SYNTAX_EXTENSION_H
#define ACSL_SYNTAX_EXTENSION_H 1

/*
 * Comment this define if you want to use
 * vanilla Frama-C.
 */
#define ASTRAVER_TOOLCHAIN 1


#ifdef ASTRAVER_TOOLCHAIN /* used by default */

/*
 * Frama-C BTS 0002382: handling of escape sequences
 * https://bts.frama-c.com/view.php?id=2382
 */
# define FRAMAC_VTAB_BUG || c == '\v'

/*
 * ACSL extension: don't check for overflow on
 * an operation (type casting, arithmetic, ...)
 * AENO  - ACSL Extension No Overflow
 * AENOC - ACSL Extension No Overflow Comment
 */
# define AENO %
# define AENOC /*@%*/

#else /* !ASTRAVER_TOOLCHAIN */

# define FRAMAC_VTAB_BUG
# define AENO
# define AENOC

#endif /* ASTRAVER_TOOLCHAIN */

#endif /* ACSL_SYNTAX_EXTENSION_H */
