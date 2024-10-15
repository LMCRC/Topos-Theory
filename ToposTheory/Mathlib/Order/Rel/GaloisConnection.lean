/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
import Mathlib.Data.Rel
import Mathlib.Order.GaloisConnection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import ToposTheory.GrothendieckSubtopos

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
  left_inv J := by cases' J with J hJ; rw [Subtype.mk.injEq, hJ]
  right_inv I := by cases' I with I hI; rw [Subtype.mk.injEq, hI]

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

--NOTE(@doctorn) I feel like this must exist in MathLib, but I couldn't find it
def presheaf_iso_globalSections.{u} {C : Type*} [Category C]
    (P : C ᵒᵖ ⥤ Type u): P ⋙ coyoneda.obj (Opposite.op PUnit.{u + 1}) ≅ P :=
  NatIso.ofComponents fun _ ↦ equivEquivIso <| Equiv.mk (fun e ↦ e PUnit.unit) (fun a ↦ fun _ ↦ a) (by tauto) (by tauto)

universe u

variable {C : Type*} [Category C] (XS : (X : C) × Sieve X) (P Q : Cᵒᵖ ⥤ Type u)

open Limits NatTrans Rel

noncomputable def restrictionMap {X' : C} (f : X' ⟶ XS.1) :
    (yoneda.obj X' ⟶ P) → (pullback XS.2.functorInclusion (yoneda.map f) ⟶ P) :=
  (pullback.snd XS.2.functorInclusion (yoneda.map f) ≫ .)

def bij_of_restrictMap : Prop :=
  ∀ {X' : C} (f : X' ⟶ XS.1), Function.Bijective (restrictionMap XS P f)

def bij_of_restrictMap_coe (α : P ≅ Q) : bij_of_restrictMap XS P → bij_of_restrictMap XS Q := by
  admit

def bij_of_restrictMap_iff_yonedaSheafCondition : bij_of_restrictMap XS P ↔ Presieve.YonedaSheafCondition P XS.2 := by
  apply Iff.intro
  . intro h
    unfold Presieve.YonedaSheafCondition
    intro α
    apply Function.Bijective.existsUnique
    unfold bij_of_restrictMap at h
    rw [← Category.comp_id XS.snd.functorInclusion, ← yoneda.map_id]
    have bij: Function.Bijective (restrictionMap XS P (𝟙 _)) := h (𝟙 _)
    unfold restrictionMap at bij
    sorry
  . sorry

def sheaf_implies_bij_of_restrictMap (J : GrothendieckTopology C)
    (hP : Presheaf.IsSheaf J P) (hXS : XS.2 ∈ J XS.1) : bij_of_restrictMap XS P := by
  apply bij_of_restrictMap_coe _ _ _ (presheaf_iso_globalSections P)
  apply (bij_of_restrictMap_iff_yonedaSheafCondition XS _).mpr
  apply Presieve.isSheafFor_iff_yonedaSheafCondition.mp
  unfold Presheaf.IsSheaf Presieve.IsSheaf at hP
  exact (hP PUnit XS.2 hXS)

def allSheavesRespect_implies_covering (J : GrothendieckTopology C) :
    (∀ {P : C ᵒᵖ ⥤ Type u}, (hP : Presheaf.IsSheaf J P) → Presieve.YonedaSheafCondition P XS.2) → XS.2 ∈ J XS.1 := by
  admit

theorem mem_leftFixedPoint (J : GrothendieckTopology C) :
    {XS : (X : C) × Sieve X | XS.2 ∈ J.sieves XS.1} ∈ (leftFixedPoints bij_of_restrictMap) := by
  ext XS
  simp [leftFixedPoints, leftDual, rightDual]
  apply Iff.intro
  . intro h
    apply allSheavesRespect_implies_covering
    intros P hP
    apply (bij_of_restrictMap_iff_yonedaSheafCondition XS P).mp
    apply h
    intro XS
    apply sheaf_implies_bij_of_restrictMap
    exact hP
  . intros hXS _ hP
    exact hP hXS

instance instGrothendieckTopologyOfleftFixedPoint {J : Set ((X : C) × Sieve X)}
    (h : J ∈ leftFixedPoints bij_of_restrictMap) : GrothendieckTopology C where
  sieves X := {S : Sieve X | ⟨X, S⟩ ∈ J}
  top_mem' := sorry
  pullback_stable' := sorry
  transitive' := sorry

open GrothendieckTopos

variable {I : Set (Cᵒᵖ ⥤ Type u)}

theorem mem_rightFixedPoint (ℰ : Subtopos (Cᵒᵖ ⥤ Type u)) (h : ∀ P, ℰ.obj P ↔ P ∈ I) :
    I ∈ rightFixedPoints bij_of_restrictMap := by admit

instance subtopos_of_rightFixedPoint (h : I ∈ rightFixedPoints bij_of_restrictMap) :
    Subtopos (Cᵒᵖ ⥤ Type u) where
  obj P := P ∈ I
  adj := sorry
  flat := sorry
  mem := sorry

instance : GrothendieckTopology C ≃ Subtopos (Cᵒᵖ ⥤ Type u) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end Subtopos
