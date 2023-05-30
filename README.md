# polyrec-SML

To answer a request by Fritz Henglein and Martin Elsman of DIKU, U Copenhagen, 
my plan is to make available an implementation of SMLNJ with polymorphic recursion. 
The code was written in 1995 for smlnj-0.93 and adapted to smlnj-110.0.3 in 1998 while
Martin Emms and myself were employed at Ludwig-Maximilans-Universität München (LMU).

It remains to be checked if the LMU has any objections in making it public and if the
code can be adapted to smlnj-110.99 with reasonable amount of work. So currently the 
repository is still empty, except for the README file of 1998 included below.

Hans Leiß, May 30, 2023. h.leiss@gmx.de


Poly Rec: SML with polymorphic recursion
----------------------------------------

The code in this directory implements a type checker for SML using the
Milner-Mycroft type system rather than the Damas-Milner system.  The
difference is that in the first system, recursive functions are
polymorphic within their defining expression, not only outside.

Though typbility in the Milner-Mycroft system is undecidable in general,
there seems to be no real difficulty in type inference with this system.
Our intention was to make polymorphic recursion available to SML
programmers, without writing a brand new type checker. 

In particular, we did not modify SML-NJ's datatypes of types and
expressions (which would allow more efficent data structures for
type inequation constraint solving). Poly Rec extends the range
of functions that can be typed, but it slows down type checking of
Damas-Milner typable functions somewhat. (Parsing of all the compiler
code using Poly Rec (Version 1.5 for 0.93) takes about twice the time
it takes with SML's monomorphic recursion.)

Since one can switch back to SML's type checker, we hope the
implementation allows to gain some experience with polymorphic
recursion in actual programming. 

Documentation: see subdirectory doc.
Installation:  see doc/INSTALL_NOTES and doc/xmakeml-polyrec
User-manual:   see doc/USER_MANUAL
Examples:      see examples.sml, doc/polyrec.threeExpls.dvi.gz


Dr.Martin Emms, emms@cis.uni-muenchen.de,   June 1995
Dr.Hans Leiss,  leiss@cis.uni-muenchen.de, March 1998

Centrum fuer Informations- und Sprachverarbeitung (CIS)
Ludwig-Maximilians-Universitaet Muenchen
Oettingenstr. 67
D-80538 Muenchen
Germany
