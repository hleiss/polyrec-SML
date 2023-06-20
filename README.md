# polyrec-SML

To answer a request by Fritz Henglein and Martin Elsman of DIKU,
University of Copenhagen, I make available an implementation of a
typechecker for Standard ML of New Jersey (SML/NJ) that uses
polymorphic rather than monomorphic recursion (i.e. Milner/Mycroft
rather than Hindley/Milner/Damas type system).

The code was written by Martin Emms and myself in 1995 for smlnj-0.93
and adapted to smlnj-110.0.3 in 1998 while we were employed at
Ludwig-Maximilans-Universität München (LMU).

I have adapted the code to smlnj-110.99.3, the latest stable version
of SML/NJ, available from https://github.com/smlnj/legacy. For
explanation and examples see the README and examples.sml files in the
subdirectory doc, but use INSTALL_NOTES.110.99.3 instead of those in
doc.

Proviso:

Some Milner/Mycroft typable functions pass the type checking phase of
SML/NJ [Poly Rec] version 110, but raise a compiler bug in a later
phase (which was not so with SML/NJ [Poly Rec] version 0.93.).  As
explained in doc/aritiy-problem.doc, the reason is that smlnj-110
translates expressions of the abstract syntax to an intermediate
language FLINT, which does its own type-based optimizations. However,
the suggested fix in doc/arity-problem.doc is insufficient: a bug is
raised not only for arity mismatches as in `fun f x = f x x', but also
for arity-correct declarations like `fun f x = f (x,x)' (cf. Example21
and Example22 of example.sml).

Hans Leiß, June 20, 2023. h.leiss (at) gmx.de


