/-
Copyright (c) 2024 Grothendieck Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Donato
-/

/-!
# Subobject classifiers

Following [MLM94, Section I.3], we introduce the notion `CategoryTheory.Subobject.Classifier C` of
subobject classifier in a category `C`.

## Main Results

⋆ `CategoryTheory.Subobject.Classifier.is_representable` : a category `C` has a subobject classifier
`Ω` if and only if the functor `CategoryTheory.Subobject` mapping any object `X` of `C` to the set
of subobjects of `X` is representable by `Ω` (Proposition 1 in Section I.3 of [MLM94]).

## References

⋆ [MLM94] Mac Lane, Saunders and Moerdijk, Ieke. "Sheaves in Geometry and Logic: a First
Introduction to Topos Theory." 1992. http://link.springer.com/book/10.1007/978-1-4612-0927-0.

## Tags

subobject, subobject classifier
-/
