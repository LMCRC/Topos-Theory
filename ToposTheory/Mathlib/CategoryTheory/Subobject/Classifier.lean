/-
Copyright (c) 2024 Grothendieck Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Donato
-/

import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Subobject classifiers

Following Section I.3 of [Sheaves in Geometry and Logic][MLM92], we introduce the notion
`CategoryTheory.Subobject.Classifier C` of subobject classifier in a category `C`.

## Main Results

⋆ `CategoryTheory.Subobject.Classifier.is_representable` : a category `C` has a subobject classifier
`Ω` if and only if the subobjects functor `CategoryTheory.Subobject.Sub` that pulls back
monomorphisms is representable by `Ω` (Proposition 1 in Section I.3 of [MLM94]).

## References

* [S. MacLane and I. Moerdijk, *Sheaves in geometry and logic: A first introduction to topos
  theory*][MLM92]

## Tags

subobject, subobject classifier
-/

namespace CategoryTheory.Subobject

open CategoryTheory

universe u v

/-! ### The notion of subobject classifier -/

section SubobjectClassifier

variable (C : Type u) [Category.{v} C]

/-- A monomorphism `f` is a subobject classifier when it satisfies the universal property that every
    monomorphism is uniquely a pullback of `f`. -/
def IsClassifier {C : Type u} [Category.{v} C] {Ω Ω₀ : C} (f : Ω₀ ⟶ Ω) [Mono f] : Prop :=
  ∀ {S X : C} {m : S ⟶ X} [Mono m],
  ∃ one, ∃! (χ : X ⟶ Ω), IsPullback one m f χ

class Classifier where
  (Ω Ω₀ : C)
  truth : Ω₀ ⟶ Ω
  truth_mono : Mono truth
  is_classifier : IsClassifier truth

/-- A category `C` has a subobject classifier if there exists a monomorphism `truth : Ω₀ ⟶ Ω` that
    is a subobject classifier. -/
def HasClassifier := Nonempty (Classifier C)

end SubobjectClassifier

/-! ### The presheaf of subobjects `Sub` -/

section Sub

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

noncomputable instance Sub : Cᵒᵖ ⥤ Type (max u v) where
  obj X := (@Subobject C _ X.unop)

  map f := (pullback f.unop).obj

  map_id := by {
    simp only
    intro X
    funext
    rw [unop_id, pullback_id]
    simp
  }

  map_comp := by {
    simp only
    intro X Y Z f g
    funext
    rw [unop_comp, pullback_comp]
    simp
  }

end Sub

/-! ### A category has a subobject classifier if and only if `Sub` is representable -/

namespace Classifier

open CategoryTheory.Yoneda

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

theorem is_representable : HasClassifier C ↔ (@Sub C).IsRepresentable := by {
  sorry
}

end Classifier
end CategoryTheory.Subobject
