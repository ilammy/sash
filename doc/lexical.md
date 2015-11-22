Lexical syntax
==============

## 1 – Input format

Sash operates on source code represented with Unicode text encoded in UTF-8
format. Alphabetic case is significant. Indentation and line-breaking are
free-form.


## 2 – Whitespace

Sash recognizes space (U+0020), tab (U+0009), newline (U+000A), and return
(U+000D) characters as whitespace. Newline (LF) and return-newline (CRLF)
sequences are recognized as line endings.

Whitespace is not semantically significant, but affects syntactical meaning
by denoting token boundaries.


## 3 – Comments

Comments are allowed where whitespace is allowed and are treated as whitespace
(i.e., they are not semantically significant).

Examples of comments:

    // line comments span until the end of the line

    /*
     * block comments /* can be nested */
     */


### 3.1 – Documentation comments

Sash also defined a special kind of comments for writing inline source-level
documentation. These comments are not completely ignored and can be used by
automated tools. The compiler may also check for their existence as well as
for their well-formedness, possibly producing compilation errors. However,
they still do not affect the semantics of programs in any way.

Examples of documentation comments:

    /// Line documentation comment applied to the entity
    /// which follows it in the source code.

    //! Line documentation comment applied to the entity
    //! which encloses it in the source code.

    /**
     *  Block documentation comment applied to the entity
     *  which follows it in the source code.
     */

    /*!
     *  Block documentation comment applied to the entity
     *  which encloses it in the source code.
     */


## 4 – Identifiers

Sash has flexible syntax of identifiers which are divided into three _kinds_:
**words**, **marks**, and **quotes**. `Variable` is an example of a word, `=>`
is an example of a mark, and `⌊ ⌋` is an example of a quote.

Three kinds are needed to cleanly support _user-defined operators_. Words are
intended for general usage; marks are intended for infix, prefix, and postfix
operators; and quotes are intended for some outfix (enclosing) operators. All
identifier kinds are composed of nonitersecting sets of characters so that
they could be told apart even when whitespace is omitted, as in `a+b`.

Unicode is supported in all identifier kinds, but has its peculiarities.
Unicode can be freely mixed with ASCII. There is also an ASCII compatibility
form for the cases when full Unicode range is not available.


### 4.1 – Words

Words are your usual C-style identifiers. A word starts with an English letter
of any case, and is followed by zero or more English letters and decimal digits.
The underscore character `_` is considered a (lowercase) letter.

Examples of words:

    foo         ExampleIdentifier42     snake_cased_identifier      __PYTHON__


#### 4.1.1 – Unicode words

Unicode words are supported in a manner similar to the one described in
[_Unicode Annex #31_](http://unicode.org/reports/tr31/).

Specifically, a word starts with a character that has one of the following
Unicode _general categories_:

  - **Lu** — uppercase letters
  - **Ll** — lowercase letters
  - **Lt** — titlecase letters
  - **Lm** — modifier letters
  - **Lo** — other letters
  - **Nl** — letter numbers

After the first character the following additional general categories are
allowed to be used:

  - **Mn** — nonspacing marks
  - **Mc** — spacing combining marks
  - **Nd** — decimal numbers
  - **Pc** — connector punctuation

As an extension, Sash also allows the following two format control characters
to be used in word continuations (after the first character):

  - U+200C ZERO-WIDTH NON-JOINER
  - U+200D ZERO-WIDTH JOINER

Finally, due to Unicode stability requirements, starter characters include
several extra ones with Unicode property **Other_ID_Start**, and continuation
characters include the ones with the property **Other_ID_Continue**.

Examples of Unicode words:

    TODO


### 4.2 – Marks

Marks consist of one or more of the following non-alphabetical characters:

    ! $ % & * + - ~ / < = > ? @ ^ |

Marks can also include two or more consecutive dots: `..`

Examples of marks:

    +         /         <<=        &&         @         <*>        ...


#### 4.2.1 – Unicode marks

Unicode marks are composed of characters of the following general categories:

  - **Pd** — dash punctuation
  - **Po** — other punctuation
  - **Sc** — currency symbols
  - **Sm** — mathematical symbols
  - **So** — other symbols

After the first character marks can also contain the following modifiers:

  - **Mc** — spacing combining modifiers
  - **Mn** — non-spacing combining modifiers
  - **Me** — enclosing modifiers

Marks are also affected by Unicode stability requirements, but the exceptional
characters sets for them are currently empty (as of Unicode 8.0.0).

Examples of Unicode marks:

    TODO


### 4.3 – Quotes

Quotes are peculiar identifier kind. While words and marks can span multiple
characters, quote identifiers are always restricted to one character. This
means that they do not coalesce when placed near each other, which helps them
to be used in enclosing contexts without additional whitespace.

There are no ASCII characters for quote identifiers. `( ) [ ] { } ' " \`` would
qualify for the role of ASCII quotes, but they already have reserved meanings.

Unicode quotes are formed by the following character general categories:

  - **Ps** — opening punctuation
  - **Pe** — closing punctuation
  - **Pi** — initial quotes
  - **Pf** — final quotes

Unicode quotes do not allow any combining modifiers after them.

Examples of Unicode quotes:

    TODO


### 4.4 – Unicode in identifiers

Sash supports Unicode identifiers, the ASCII set of characters allowed in them
is not affected by Unicode general categories described above. As it is, ASCII
repertoire of Sash stated here is complete and exhausive.

Also, Unicode support usually has several important implications for programming
languages, namely:

  - how identifiers are compared for equality
  - what happens when Unicode Stardard gets updated
  - is Unicode support required to use the language


#### 4.4.1 – Identifier normalization

All identifiers in Sash are compared after being processed with _Normalization
Form KC_ (see [Unicode Annex #15](http://unicode.org/reports/tr15/)). Also,
_Zero-Width Non-Joiner_ and _Zero-Width Joiner_ characters are ignored when
comparing word identifiers. This helps to fold differences between `différence`
and `différence` (if you can see it) and avoids some security issues arising
from visual ambiguity. However, normalization does not eliminate them
completely (e.g., `foo` and `foо` are still different).

In order to support NFKC normalization character sets of identifiers are not
exactly equal to unions of general categories described above. Several
characters are excluded from them to make the character sets closed over NFKC.
That is, to ensure that if a character sequence is an identifier of a certain
kind then its normalized form is also a valid identifier of the same kind.


#### 4.4.2 – Identifier stability

Stability is Another important point with Unicode support. That is, once
something is considered an identifier in a certain version of Unicode Standard,
it should stay an identifier of the same kind in all subsequent versions.

This requirement can be trivially satisfied if we ensure that the sets of
identifier characters are only expanded when a new Unicode version comes out.
No character must change its kind affinity once it was determined. General
categories of Unicode characters are kept as stable as possible, but they are
not guaranteed to be immutable. In fact, there are multiple characters which
switched their categories in an incompatible way.

The aforementioned issue is resolved by using so called _grandfathered
characters_: additional sets of exceptional characters which are added to the
normal character sets in order to satisfy the stability requirements. For
example, U+212E ESTIMATED SYMBOL (℮) has general category _So_ (other symbols)
in Unicode 8.0.0. This should have placed it into mark character set, but in
Unicode 2.0 this character was considered to be lowercase letter. Thus it is
included into _Other_ID_Start_ — the grandfathered set of the initial word
characters — and ℮ is considered a valid word character.

Here is a full list of current grandfathered sets for Sash identifiers:

  - **words:**
    - additional starter characters:
      - U+2118 SCRIPT CAPITAL P (℘)
      - U+212E ESTIMATED SYMBOL (℮)
    - additional continuations (includes all starters):
      - U+00B7 MIDDLE DOT (·)
      - U+0387 GREEK ANO TELEIA (·)
      - U+1369 ETHIOPIC DIGIT ONE (፩)
      - U+136A ETHIOPIC DIGIT TWO (፪)
      - U+136B ETHIOPIC DIGIT THREE (፫)
      - U+136C ETHIOPIC DIGIT FOUR (፬)
      - U+136D ETHIOPIC DIGIT FIVE (፭)
      - U+136E ETHIOPIC DIGIT SIX (፮)
      - U+136F ETHIOPIC DIGIT SEVEN (፯)
      - U+1370 ETHIOPIC DIGIT EIGHT (፰)
      - U+1371 ETHIOPIC DIGIT NINE (፱)
      - U+19DA NEW TAI LUE THAM DIGIT ONE (᧚)
  - **marks:** none
  - **quotes:** none

We also need to ensure that no identifier is a valid substring of an identifier
of different kind. General categories of starter characters of identifier kinds
do not intersect so grandfathered characters are the only possible source of
problems here. In order to avoid these problems any special grandfathered
characters must be excluded from character sets of all other identifer kinds.


#### 4.4.3 – ASCII compatibility

In certain cases the source code is necessarily restricted to ASCII by some
external protocol (like SMTP). Sash supports ASCII fallback for Unicode
characters in order to deal with such restrictions. With it, `糖果` can be
written in the form of Unicode escapes: `\u{FA03}\u{679C}`. The same syntax
is also supported by strings, characters, and symbols which all allow Unicode
usage as well.

ASCII fallback allows to restrict any valid Sash program to ASCII character set
and to convert it back to the full Unicode form if necessary. Both forms are
semantically equivalent and introduce no differences in identifier treatment.
Unicode identifiers are still normalized and inter-kind token boundaries are
still detected just fine be it `ĳ+`, `ij＋`, or `\u{133}\u{ff0b}`.

However, note that this is _a fallback_, not a backdoor. ASCII Unicode escapes
do not extend allowed character sets for identifiers in any way, nor they allow
to use reserved identifiers. Any _valid_ program is completely unchanged when
any or all non-ASCII characters in it are coverted to Unicode escapes and back.

ASCII escapes are considered an exceptional form of identifier characters. Thus
it is not possible to encode any ASCII characters with Unicode escapes. There
are no such restrictions for characters, strings, and (explicit) symbols which
can all use C escapes (`\n`), byte escapes (`\x32`), and Unicode escapes for
ASCII range (`\u{6F}`).


### 4.5 – Multipart identifiers

TODO


### 4.6 – Reserved identifiers

TODO

------------------------------------------------------------------------

Sash supports usage of valid Unicode in identifiers. However, the ASCII range
is handled using Sash-specific rules, regardless of Unicode categories and
other properties assigned to these code points. Unicode can be freely mixed
with ASCII.


#### 4.3.1 Unicode words

Unicode words are supported as per [_Unicode Annex #31_] [2]. Such identifiers
are composed of a _XID_Start_ character followed by zero or more _XID_Continue_
characters.

UAX #31 provides precise definitions of XID_Start and XID_Continue properties.
In short, an identifier starts with a letter and after that can also include
numbers, combining modifiers, and connectors of various sorts.

UAX #31 also implies _NFKC normalization_ of identifier names. Thus, there is
no difference between `différence ` and `différence` (if you can see it).
Again, [UAX #15] [3] provides precise rules of character normalization.
In short, if identifiers look alike then they are considered the same.

[2]: http://unicode.org/reports/tr31/
[3]: http://unicode.org/reports/tr15/


#### 4.3.2 Unicode symbols

Unicode symbols can start with a Unicode code point of general category Pc, Pd,
Pe, Pf, Pi, Po, Ps, Sc, Sk, Sm, So (with ASCII characters excluded from them).
After the first character combining modifiers are also allowed.

Examples of Unicode symbols:

> **TODO:** examples

> **TODO:** normalization of symbols


#### 4.3.3 ASCII fallback

Finally, ASCII fallback for Unicode identifiers is provided so that `糖果` could
be written as `\uFA03\u679C` if the source code is constrained to ASCII. See the
[_Characters_] [4] section for complete syntax of Unicode escapes. (Note that
this is _a fallback_, not a backdoor. It does not extend the set of characters
allowed in identifiers, it does not allow mixing word and symbol characters,
and it does not allow usage of reserved identifiers.)

[4]: #8characters


### 4.4 Reserved identifiers

A number of words and symbols have reserved meaning in Sash. You cannot use them
as identifiers. Even with the Unicode escapes.

> **TODO**: the list

> **TODO**: compound identifiers (?)


## 5 Delimiters

    ( ) [ ] { } , : :: ; # .

> **TODO:** elaborate, extend


## 6 Booleans

Boolean constants are `true` and `false`. These are reserved identifiers.


## 7 Numbers

### 7.1 Integers

Integers are typically written using decimal digits:

    123             -42             +9

But you can use binary, octal, and hexadecimal forms if needed:

    0b01001110      0o755           0xDeadBeef


### 7.2 Floating point

Floating-point numbers use decimal dot as a separator between the integer and
fractional parts:

    2.0             -3.1415926

_No part_ can be omitted. One-half is written as `0.5`, not `.5`. Floating zero
is written as `0.0`, not as `0.` or `.0`.

> **Q:** Why is that so?
>
> **A:** Because ~I said so~ it avoids making arbitrary decisions about how
> ambiguous strings like `1.foo` and `?.0` should be parsed in the presence
> of used-defined operators. Plus, it simplifies scanning a bit: in cases like
> `1.___4` the scanner is not required to use backtracking to correctly choose
> between 'a float' and 'an integer, a dot, an identifer'. And yeah, finally,
> because I hate when people 'shorten' floating-point literals by removing
> 'unnecessary' zeros. They _are_ necessary! They act as a marker for floats.

Exponential form is also available. It permits dropping the fractional part:

    1.0e10          2E-10

Radix prefixes are not allowed for floating-point numbers. They are all written
using decimal digits. No binary form is provided for floating-point numbers.


### 7.3 Type suffixes

Type suffixes (`i8`, `usize`, `f32`, etc.) can be used to specify precise type
of a number literal.

> **TODO:** elaborate precise list

If a suffix is specified, the literal value must fit into the specified type.
If no suffix is specified, a suitable type for literal is inferred from the
context. If the literal's type cannot be inferred due to lack of information,
a sensible default is used (which is defined as `i32` for integers and `f64`
for floats).


### 7.4 Separators

All numbers allow `_` to be used as a separator between digits and structural
parts (radix prefix, number value, floating-point exponent, and type suffix):

    -10_000
    0x_FF_u8
    2.0_e+41_f32
    1__2__3__4__5


### 7.5 Vexing parses

Strictly speaking, _any_ literal can have a type suffix, which can be _any_ word
identifier. However, only numbers have defined suffixes and they are defined as
canonical names of primitive types (that is, they are not affected by module
import renaming). Other uses of the type suffixes are reserved for language
expansion.

This is the reason for required fractional part of floating point numbers.
Otherwise it would be necessary to establish arbitrary rules for disambiguating
things like `2.f32` (a number with a suffix vs. a dot operator application).

> **TODO:** should it read _field access_ now?

One more thing. From the lexical standpoint, the sign cannot be included into
number literals because it is impossible for the lexer to disambiguate unary
and binary plus and minus operators. Furthermore, remember that `_` is a valid
character in identifiers. Thus underscore used like this: `+_2` does not mean
a number, it is an identifier `+` followed by another identifier `_2`. We cannot
do anything about it as unary operators in Sash are not limited to `+` and `-`.

However, we can fix another problem. The separators are allowed only _between_
the structural parts. Thus, strings like `2._0`, `2_.0`, `2_._0` are considered
syntatically invalid numbers instead of being weirdly parsed sometimes into
a number, and sometimes into an operator application, depending on where you
put the underscore.

> **TODO:** this is too long, and is not really necessary in user-level docs.
> It should be shortened or removed entirely after the imlementation.


## 8 Characters

Characters are quoted with single quotes: `'x'`, including the quote character
itself: `'''`.

A character literal can include any Unicode scalar value except for Unicode
control codes (general category Cc). Control codes can be written only using
escapes. Surrogates cannot be placed into a character.

Some traditional C-style escapes are supported: `'\0'` (null, U+0000), `'\t'`
(tab, U+0009), `'\n'` (newline, U+000A), `'\r'` (return, U+000D). Any Unicode
scalar value can also be written using explict Unicode escapes:

<table>
  <tr><td><tt>'\x12'</tt></td>    <td>exactly two hex digits</td></tr>
  <tr><td><tt>'\u3456'</tt></td>  <td>exactly four hex digits</td></tr>
  <tr><td><tt>'\U109ABC'</tt></td><td>exactly six hex digits</td></tr>
  <tr><td><tt>'\u{123}'</tt></td> <td>one to six hex digits</td></tr>
</table>


## 9 Strings

Strings are quoted with double quotes: `"string"`. Double quotes themselves
must be escaped with a backslash: `"\""`. The backslash must also be escaped:
`"\\"`. All character escape sequences are also supported inside strings.

> **TODO:** UTF-8 in strings?


### 9.1 Multiline strings

Line breaks (and other control codes) can be used in strings. However, a line
break in the source code is always represented with a single newline character
`\n` in the string, regardless of its actual representation in the source.

    "foo        "foo\nbar"      "foo        "foo\n    bar"
    bar"                            bar"

(As you can see, leading whitespace is also preserved.)

You can also break long strings into logical lines without actually inserting
newline characters into them. If the `\` character immediately precedes a line
break, it is be ignored together with the line ending and any leading whitespace
on the following line:

    "foo\       "foobar"
        bar"


### 9.2 Raw strings

There are also _raw strings_ which ignore escape sequences and permit writing
double quotes without escapes. They are mostly useful for regular expressions.

    r"/.*@.*/"      ".*@.*"
    r"/""/"         "\"\""

> **TODO:** better examples

Actually, you can use whatever character you want instead of `/`, except for
the four whitespace characters (space, tab, newline, and return).

    r""f\"oo""      "f\\\"oo"       r"♥L♥O♥V♥E♥"        "L♥O♥V♥E"

You can also use line breaks in raw strings. As with regular strings, they are
converted into `\n` characters regardless of their source code representation.

    r"|\            "\\\n  "
      |"

## 10 Symbols

Symbols are normally used as keywords, so symbols can be conveniently written
as identifiers _immediately_ followed by a single `:` character:

    keyword:

They can also be written explicitly, as strings prefixed with a hash `#`:

    #"foo"      #r"#"bar" "baz"#"      #""

Well, effectively, they _are_ strings. Only with an additional guarantee
of shared storage for equal values, a different syntactic category and type.

> **TODO:** are symbols normalized as identifiers?
