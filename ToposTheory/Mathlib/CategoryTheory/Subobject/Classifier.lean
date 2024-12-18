/-
Copyright (c) 2024 Grothendieck Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Donato
-/

import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

-- import Mathlib.Tactic.Widget.CommDiag
-- import ProofWidgets.Component.Panel.GoalTypePanel
-- import ProofWidgets.Component.Panel.SelectionPanel

/-!
# Subobject classifiers

Following Section I.3 of [Sheaves in Geometry and Logic][MLM92], we introduce the notion
`CategoryTheory.Subobject.Classifier C` of subobject classifier in a category `C`.

## Main Results

⋆ `CategoryTheory.Subobject.Classifier.is_representable` : a category `C` has a subobject classifier
`Ω` if and only if the subobjects functor `CategoryTheory.Subobject.Sub` that pulls back
monomorphisms is representable by `Ω` (Proposition 1 in Section I.3 of [MLM92]).

## References

* [S. MacLane and I. Moerdijk, *Sheaves in geometry and logic: A first introduction to topos
  theory*][MLM92]

## Tags

subobject, subobject classifier
-/

namespace CategoryTheory.Subobject

open CategoryTheory
open Limits
open Subobject

-- open ProofWidgets

universe u v

variable {C : Type u} [Category.{v} C]

/-! ### The notion of subobject classifier -/

section SubobjectClassifier

/-- A monomorphism `f` from the terminal object `⊤_ C` is a subobject classifier when it satisfies
    the universal property that every monomorphism is uniquely a pullback of `f`.

    **Implementation note**: maybe we want to relax strict equality in `Unique` to equivalence, i.e.
    up to 2-isomorphism?
-/
def IsClassifier {C : Type u} [Category.{v} C] [HasTerminal C]
    {Ω : C} (f : ⊤_ C ⟶ Ω) [Mono f] : Type (max u v) :=
  Π {X : C} (S : Subobject X),
  Unique {φ : X ⟶ Ω // IsPullback (terminal.from (S : C)) S.arrow f φ}

variable (C : Type u) [Category.{v} C] [HasTerminal C]

class Classifier where
  (Ω : C)
  true! : ⊤_ C ⟶ Ω
  true!_mono : Mono true!
  is_classifier : IsClassifier true!

/-- A category `C` has a subobject classifier if there exists a monomorphism `truth : ⊤_ C ⟶ Ω` that
    is a subobject classifier. -/
class HasClassifier : Prop where
  has_classifier : Nonempty (Classifier C)

open Classifier

variable {C : Type u} [Category.{v} C] [HasTerminal C] [𝒞 : Classifier C]

instance : Mono 𝒞.true! := true!_mono

/-- `truth` is the subobject associated to the subobject classifier `true!`. -/
noncomputable def truth : Subobject 𝒞.Ω := Subobject.mk true!

lemma true_truth_arrow : (underlyingIso 𝒞.true!).hom ≫ 𝒞.true! = truth.arrow := by
  simp [truth]

/-- `S.cmap` is the unique characteristic map of subobject `S` given by the subobject classifier. -/
def cmap {X : C} (S : Subobject X) : X ⟶ Ω :=
  (is_classifier S).default.val

/-- `compr χ` builds the subobject associated to characteristic map `χ` by pulling back `truth`
    along it. This generalizes the construction of a subset "by comprehension" from its
    characteristic function in set theory.  -/
noncomputable def compr [HasPullbacks C] {X : C} (χ : X ⟶ Ω) : Subobject X :=
  (pullback χ).obj truth

end SubobjectClassifier

/-! ### The presheaf of subobjects `Sub` -/

section SubPresheaf

variable [HasPullbacks C]

noncomputable instance Sub : Cᵒᵖ ⥤ Type (max u v) where
  obj X := (@Subobject C _ X.unop)

  map f := (pullback f.unop).obj

  map_id := by
    simp only
    intro X
    funext
    rw [unop_id, pullback_id]
    simp

  map_comp := by
    simp only
    intro X Y Z f g
    funext
    rw [unop_comp, pullback_comp]
    simp

end SubPresheaf

section HelperLemmas

/-! ### Additional lemmas about pullbacks and subobjects -/

variable [HasPullbacks C]

noncomputable def pullback_congr_left_iso {X X' Y Z : C} (f : X ⟶ Y) (f' : X' ⟶ Y) (g : Z ⟶ Y)
    (i : X ≅ X') (w : i.hom ≫ f' = f) :
    Limits.pullback f g ≅ Limits.pullback f' g := {
  hom := by
    refine pullback.lift (pullback.fst f g ≫ i.hom) (pullback.snd f g) ?_
    rw [Category.assoc, w]
    exact pullback.condition
  inv := by
    refine pullback.lift (pullback.fst f' g ≫ i.inv) (pullback.snd f' g) ?_
    conv =>
      lhs
      rw [Category.assoc, ← w]
      rhs
      rw [← Category.assoc, i.inv_hom_id, Category.id_comp]
    exact pullback.condition
  hom_inv_id := by
    aesop_cat
  inv_hom_id := by
    aesop_cat
}

noncomputable def pullback_obj_iso {X Y : C} (f : Y ⟶ X) (S : Subobject X) :
    ((pullback f).obj S : C) ≅ Limits.pullback S.arrow f := {
  hom := by
    refine pullback.lift ?_ ((pullback f).obj S).arrow ?_
    sorry
    sorry
  inv := by
    sorry
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry
}

lemma pullback_obj_snd {X Y : C} (f : Y ⟶ X) (S : Subobject X) :
    (pullback f).obj S = Subobject.mk (pullback.snd S.arrow f) :=
  eq_mk_of_comm (pullback.snd S.arrow f) (pullback_obj_iso f S) (by simp [pullback_obj_iso])

end HelperLemmas

/-! ### A category has a subobject classifier if and only if `Sub` is representable -/

namespace Classifier

open CategoryTheory.Yoneda
open Opposite

variable [HasPullbacks C] [HasTerminal C]

lemma cmap_compr_self [Classifier C] {X : C} (χ : X ⟶ Ω) :
    (compr χ).cmap = χ := by
  set S := compr χ
  obtain h := (is_classifier S).uniq
  have hχ : IsPullback (terminal.from (S : C)) S.arrow true! χ := by
    have h' := IsPullback.of_hasPullback true! χ
    have : S = Subobject.mk (pullback.snd true! χ) := by
      have eqp := pullback_obj_snd χ truth
      simp only [S, compr, eqp]
      let i := pullback_congr_left_iso _ _ χ (underlyingIso true!) true_truth_arrow
      apply mk_eq_mk_of_comm (pullback.snd truth.arrow χ) (pullback.snd true! χ) i
      simp [i, pullback_congr_left_iso]
    -- have : terminal.from ((pullback χ).obj truth : C) = pullback.fst true! χ := by
    sorry
  have hS : IsPullback (terminal.from (S : C)) S.arrow true! S.cmap :=
    sorry
  have hχ := h ⟨χ, hχ⟩
  have hS := h ⟨S.cmap, hS⟩
  have eqχ := congr_arg Subtype.val hχ
  have eqS := congr_arg Subtype.val hS
  simp only at eqχ eqS
  rw [eqχ, eqS]

lemma compr_cmap_self [Classifier C] {X : C} (S : Subobject X) :
    (pullback S.cmap).obj truth = S := by
  sorry

theorem is_representable : HasClassifier C ↔ (@Sub C).IsRepresentable := by
  constructor <;> intro h
  · obtain ⟨⟨𝒞⟩⟩ := h
    exists Ω
    constructor
    exact {
      /- The correspondence `cmap` sending each subobject to its (unique) characteristic map is a
         bijection. -/
      homEquiv := {
        toFun := compr
        invFun := cmap
        left_inv := cmap_compr_self
        right_inv := compr_cmap_self
      }
      /- Furthermore, this bijection is natural by the fact that two pullback squares placed side by
         side yield a pullback rectangle. -/
      homEquiv_comp := by
        intro X X' m χ
        simp only [Sub, Equiv.coe_fn_mk, Quiver.Hom.unop_op]
        sorry
    }
  · sorry

end Classifier
end CategoryTheory.Subobject
