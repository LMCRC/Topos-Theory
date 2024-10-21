/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
import Mathlib.Data.Rel
import Mathlib.Order.GaloisConnection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import ToposTheory.GrothendieckSubtopos
import ToposTheory.Saturation

/-!
# The Galois Connection Induced by a Relation

In this file, we show that an arbitrary relation `R` between a pair of types `α` and `β` defines
a pair `toDual ∘ R.leftDual` and `R.rightDual ∘ ofDual` of adjoint order-preserving maps between the
corresponding posets `Set α` and `(Set β)ᵒᵈ`.
We define `R.leftFixedPoints` (resp. `R.rightFixedPoints`) as the set of fixed points `J`
(resp. `I`) of `Set α` (resp. `Set β`) such that `rightDual (leftDual J) = J`
(resp. `leftDual (rightDual I) = I`).

## Main Results

⋆ `Rel.gc_leftDual_rightDual`: we prove that the maps `toDual ∘ R.leftDual` and
  `R.rightDual ∘ ofDual` form a Galois connection.
⋆ `Rel.equivFixedPoints`: we prove that the maps `R.leftDual` and `R.rightDual` induce inverse
  bijections between the sets of fixed points.

## References

⋆ Engendrement de topologies, démontrabilité et opérations sur les sous-topos, Olivia Caramello and
  Laurent Lafforgue (in preparation)

## Tags

relation, Galois connection, induced bijection, fixed points
-/

namespace Rel

variable {α β : Type*} (R : Rel α β)

/-! ### Pairs of adjoint maps defined by relations -/

open OrderDual

/-- `leftDual` maps any set `J` of elements of type `α` to the set `{b : β | ∀ a ∈ J, R a b}` of
elements `b` of type `β` such that `R a b` for every element `a` of `J`. -/
def leftDual (J : Set α) : Set β := {b : β | ∀ ⦃a⦄, a ∈ J → R a b}

/-- `rightDual` maps any set `I` of elements of type `β` to the set `{a : α | ∀ b ∈ I, R a b}`
of elements `a` of type `α` such that `R a b` for every element `b` of `I`. -/
def rightDual (I : Set β) : Set α := {a : α | ∀ ⦃b⦄, b ∈ I → R a b}

/-- The pair of functions `toDual ∘ leftDual` and `rightDual ∘ ofDual` forms a Galois connection. -/
theorem gc_leftDual_rightDual : GaloisConnection (toDual ∘ R.leftDual) (R.rightDual ∘ ofDual) :=
  fun J I ↦ ⟨fun h a ha b hb ↦ h (by simpa) ha, fun h b hb a ha ↦ h (by simpa) hb⟩

/-! ### Induced equivalences between fixed points -/

/-- `leftFixedPoints` is the set of elements `J : Set α` satisfying `rightDual (leftDual J) = J`. -/
def leftFixedPoints := {J : Set α | R.rightDual (R.leftDual J) = J}

/-- `rightFixedPoints` is the set of elements `I : Set β` satisfying `leftDual (rightDual I) = I`.
-/
def rightFixedPoints := {I : Set β | R.leftDual (R.rightDual I) = I}

open GaloisConnection

/-- `leftDual` maps every element `J` to `rightFixedPoints`. -/
theorem leftDual_mem_rightFixedPoint (J : Set α) : R.leftDual J ∈ R.rightFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_l; exact R.gc_leftDual_rightDual.le_u_l J
  · exact R.gc_leftDual_rightDual.l_u_le (R.leftDual J)

/-- `rightDual` maps every element `I` to `leftFixedPoints`. -/
theorem rightDual_mem_leftFixedPoint (I : Set β) : R.rightDual I ∈ R.leftFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_u; exact R.gc_leftDual_rightDual.l_u_le I
  · exact R.gc_leftDual_rightDual.le_u_l (R.rightDual I)

/-- The maps `leftDual` and `rightDual` induce inverse bijections between the sets of fixed points.
-/
def equivFixedPoints : R.leftFixedPoints ≃ R.rightFixedPoints where
  toFun := fun ⟨J, _⟩ => ⟨R.leftDual J, R.leftDual_mem_rightFixedPoint J⟩
  invFun := fun ⟨I, _⟩ => ⟨R.rightDual I, R.rightDual_mem_leftFixedPoint I⟩
  left_inv J := by obtain ⟨_, hJ⟩ := J; rw [Subtype.mk.injEq, hJ]
  right_inv I := by obtain ⟨_, hI⟩ := I; rw [Subtype.mk.injEq, hI]

theorem rightDual_leftDual_le_of_le {J J' : Set α} (h : J' ∈ R.leftFixedPoints) (h₁ : J ≤ J') :
    R.rightDual (R.leftDual J) ≤ J' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_u
  apply R.gc_leftDual_rightDual.monotone_l
  exact h₁

theorem leftDual_rightDual_le_of_le {I I' : Set β} (h : I' ∈ R.rightFixedPoints) (h₁ : I ≤ I') :
    R.leftDual (R.rightDual I) ≤ I' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_l
  apply R.gc_leftDual_rightDual.monotone_u
  exact h₁

end Rel

open CategoryTheory

namespace Subtopos

/-! ### The induced duality of topologies and subtoposes -/

universe u

variable {C : Type u} [SmallCategory C]

open Limits NatTrans Rel

def restrictionMap {X : C} (P : Cᵒᵖ ⥤ Type u)  (S : Sieve X) {X' : C} (f : X' ⟶ X) :
    (yoneda.obj X' ⟶ P) → ((Sieve.pullback f S).functor ⟶ P) :=
  ((Sieve.pullback f S).functorInclusion ≫ .)

def bij_of_restrictionMap (XS : (X : C) × Sieve X) (P : Cᵒᵖ ⥤ Type u) : Prop :=
  ∀ {X' : C} (f : X' ⟶ XS.1), Function.Bijective (restrictionMap P XS.2 f)

theorem bij_of_restrictionMap_iff_isSheafFor {X : C} (S : Sieve X) :
    (∀ {X' : C} (f : X' ⟶ X), Presieve.IsSheafFor P (Sieve.pullback f S).arrows) ↔ bij_of_restrictionMap ⟨X, S⟩ P := by
  conv =>
    lhs
    ext X' f
    rw [Presieve.isSheafFor_iff_yonedaSheafCondition]
    unfold Presieve.YonedaSheafCondition
  conv =>
    rhs
    unfold bij_of_restrictionMap
    simp [restrictionMap, Function.bijective_iff_existsUnique]

theorem mem_leftFixedPoint (J : GrothendieckTopology C) :
    {⟨X, S⟩ : (X : C) × Sieve X | S ∈ J.sieves X} ∈ (leftFixedPoints bij_of_restrictionMap) := by
  ext ⟨X, S⟩
  simp [leftFixedPoints, leftDual, rightDual]
  apply Iff.intro
  . rw [← Presheaf.sheaves_respect_iff_covering]
    intros h P hP
    have: (∀ {X' : C} (f : X' ⟶ X), Presieve.IsSheafFor P (Sieve.pullback f S).arrows) := by
      rw [bij_of_restrictionMap_iff_isSheafFor]
      apply h
      intros YS hYS
      obtain ⟨Y, S'⟩ := YS
      rw [← bij_of_restrictionMap_iff_isSheafFor]
      intros _ f
      exact hP.isSheafFor (Sieve.pullback f S') (J.pullback_stable f hYS)
    have := this (𝟙 _)
    rw [Sieve.pullback_id] at this
    exact this
  . tauto

def yoneda_iso_top_functor (X : C) : yoneda.obj X ≅ Sieve.functor (X := X) ⊤ :=
  NatIso.ofComponents (fun X' ↦ by simp; exact Equiv.toIso {
    toFun := fun f ↦ ⟨f, trivial⟩
    invFun := fun g ↦ g.1
    left_inv := by tauto
    right_inv := by tauto
  })

lemma bij_of_restrictionMap_top (X : C) (P : Cᵒᵖ ⥤ Type u) : bij_of_restrictionMap ⟨X, ⊤⟩ P := by
  unfold bij_of_restrictionMap restrictionMap
  intros X' f
  rw [Function.bijective_iff_has_inverse]
  use (fun g ↦ by
    simp at g
    exact (yoneda_iso_top_functor X').hom ≫ g)
  aesop_cat

lemma bij_of_restrictionMap_pullback {X : C} (S : Sieve X) (P : C ᵒᵖ ⥤ Type u)
    (h : bij_of_restrictionMap ⟨X, S⟩ P) {Y : C} (f : Y ⟶ X) : bij_of_restrictionMap ⟨Y, Sieve.pullback f S⟩ P := by
  unfold bij_of_restrictionMap restrictionMap
  intros Z g
  simp
  rw [← Sieve.pullback_comp]
  exact h (g ≫ f)

instance instGrothendieckTopologyOfleftFixedPoint {J : Set ((X : C) × Sieve X)}
    (h : J ∈ leftFixedPoints bij_of_restrictionMap) : GrothendieckTopology C := by
  simp [leftFixedPoints, rightDual, leftDual] at h
  exact {
    sieves := fun X ↦ {S : Sieve X | ⟨X, S⟩ ∈ J}
    top_mem' := by
      intros X
      rw [← h]
      intros P _
      exact bij_of_restrictionMap_top X P
    pullback_stable' := by
      intros _ _ S f hS
      rw [← h]
      intros P hP
      exact bij_of_restrictionMap_pullback S P (hP hS) f
    transitive' := by
      intros _ S hS R hR
      rw [← h]
      intros P hP

      unfold bij_of_restrictionMap restrictionMap
      intros Z f
      sorry
  }

open GrothendieckTopos

variable {I : Set (Cᵒᵖ ⥤ Type u)}

theorem mem_rightFixedPoint (ℰ : Subtopos (Cᵒᵖ ⥤ Type u)) (h : ∀ P, ℰ.obj P ↔ P ∈ I) :
    I ∈ rightFixedPoints bij_of_restrictionMap := by admit

instance subtopos_of_rightFixedPoint (h : I ∈ rightFixedPoints bij_of_restrictionMap) :
    Subtopos (Cᵒᵖ ⥤ Type u) where
  obj P := P ∈ I
  adj := sorry
  flat := sorry
  mem := sorry

instance : GrothendieckTopology C ≃ Subtopos (Cᵒᵖ ⥤ Type u) := sorry

end Subtopos
