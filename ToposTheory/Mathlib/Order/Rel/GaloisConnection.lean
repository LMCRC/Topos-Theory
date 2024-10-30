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

open CategoryTheory Opposite

namespace Subtopos

/-! ### The induced duality of topologies and subtoposes -/

universe u

variable {C : Type u} [SmallCategory C]

open Limits NatTrans Rel

def restrictionMap {X : C} (S : Sieve X) {X' : C} (f : X' ⟶ X) :
    (coyoneda.obj (op (yoneda.obj X'))) ⟶ (coyoneda.obj (op (S.pullback f).functor)) :=
  coyoneda.map (S.pullback f).functorInclusion.op

def restrictionMap' {X : C} (S : Sieve X):
    (coyoneda.obj (op (yoneda.obj X))) ⟶ (coyoneda.obj (op S.functor)) :=
  coyoneda.map S.functorInclusion.op

def isIso_restrictionMap (XS : (X : C) × Sieve X) (P : Cᵒᵖ ⥤ Type u) : Prop :=
  ∀ {X' : C} (f : X' ⟶ XS.1), IsIso ((restrictionMap XS.2 f).app P)

lemma isIso_restrictionMap'_of_isIso_restrictionMap {XS : (X : C) × Sieve X} {P : Cᵒᵖ ⥤ Type u} (h : isIso_restrictionMap XS P) :
    IsIso ((restrictionMap' XS.2).app P) := by
  have := h (𝟙 _)
  simp [restrictionMap] at this
  rw [Sieve.pullback_id] at this
  unfold restrictionMap'
  exact this

theorem isIso_restrictionMap_iff_isSheafFor {X : C} (S : Sieve X) :
    (∀ {X' : C} (f : X' ⟶ X), Presieve.IsSheafFor P (S.pullback f).arrows) ↔ isIso_restrictionMap ⟨X, S⟩ P := by
  conv =>
    lhs
    ext X' f
    rw [Presieve.isSheafFor_iff_yonedaSheafCondition]
    unfold Presieve.YonedaSheafCondition
  conv =>
    rhs
    unfold isIso_restrictionMap
    simp [restrictionMap, isIso_iff_bijective, Function.bijective_iff_existsUnique]

theorem mem_leftFixedPoint (J : GrothendieckTopology C) :
    {⟨X, S⟩ : (X : C) × Sieve X | S ∈ J.sieves X} ∈ (leftFixedPoints isIso_restrictionMap) := by
  ext ⟨X, S⟩
  simp [leftFixedPoints, leftDual, rightDual]
  apply Iff.intro
  . rw [← Presheaf.sheaves_respect_iff_covering]
    intros h P hP
    have: (∀ {X' : C} (f : X' ⟶ X), Presieve.IsSheafFor P (S.pullback f).arrows) := by
      rw [isIso_restrictionMap_iff_isSheafFor]
      apply h
      intros YS hYS
      obtain ⟨Y, S'⟩ := YS
      rw [← isIso_restrictionMap_iff_isSheafFor]
      intros _ f
      exact hP.isSheafFor (S'.pullback f) (J.pullback_stable f hYS)
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

lemma isIso_restrictionMap_top (X : C) (P : Cᵒᵖ ⥤ Type u) : isIso_restrictionMap ⟨X, ⊤⟩ P := by
  unfold isIso_restrictionMap restrictionMap
  intros X' f
  use (fun g ↦ by
    simp at g
    exact (yoneda_iso_top_functor X').hom ≫ g)
  aesop_cat

lemma isIso_restrictionMap_pullback {X : C} (S : Sieve X) (P : C ᵒᵖ ⥤ Type u)
    (h : isIso_restrictionMap ⟨X, S⟩ P) {Y : C} (f : Y ⟶ X) : isIso_restrictionMap ⟨Y, S.pullback f⟩ P := by
  unfold isIso_restrictionMap restrictionMap
  intros Z g
  rw [← Sieve.pullback_comp]
  exact h (g ≫ f)

--TODO(@doctorn) move this out
namespace Sieve

  def pullbackInclusion {X : C} (S : Sieve X) {Y : C} (f : Y ⟶ X) :
      (S.pullback f).functor ⟶ S.functor := by
    simp [Sieve.functor, Sieve.pullback]
    exact { app := fun Z ↦ fun ⟨g, hg⟩ ↦ ⟨g ≫ f, hg⟩ }

  def pullback_comp_functor_eq {X : C} (S : Sieve X) {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
      (S.pullback (g ≫ f)).functor = ((S.pullback f).pullback g).functor := by
    rw [Sieve.pullback_comp]

  -- I originally had eqToIso of the above, but then the following lemma wouldn't come out
  def compPullbackInclusionIso {X : C} (S : Sieve X) {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
      (S.pullback (g ≫ f)).functor ≅ ((S.pullback f).pullback g).functor where
    hom := { app := by intros W i; rw [← pullback_comp_functor_eq]; exact i }
    inv := { app := by intros W i; rw [pullback_comp_functor_eq]; exact i }

  def compPullbackInclusionIso_eq_cast {X : C} (S : Sieve X) {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
      ∀ W i, (compPullbackInclusionIso S f g).hom.app W i = cast (congrArg (fun F ↦ F.obj W) (pullback_comp_functor_eq S f g)) i := by
    intros W i
    simp [compPullbackInclusionIso]
end Sieve

--TODO(@doctorn) rename this
def descends {X : C} (S R : Sieve X) (P : C ᵒᵖ ⥤ Type u) : Prop :=
  ∀ {Y : C} {f : Y ⟶ X}, S.arrows f → isIso_restrictionMap ⟨Y, R.pullback f⟩ P

lemma descends_of_pullback {X : C} {S R : Sieve X} {P : C ᵒᵖ ⥤ Type u} (hR : descends S R P) {Y : C} (f : Y ⟶ X) :
    descends (S.pullback f) (R.pullback f) P := by
  intros Z g hg
  rw [← Sieve.pullback_comp]
  unfold isIso_restrictionMap
  intros W h
  exact hR hg h

lemma isIso_restrictionMap_transitive {X : C} (S R : Sieve X) (P : C ᵒᵖ ⥤ Type u)
    (hS : isIso_restrictionMap ⟨X, S⟩ P) (hR : descends S R P) : isIso_restrictionMap ⟨X, R⟩ P := by
  -- Restrictions of the two sieves at P
  let i := (restrictionMap' S).app P
  let j := (restrictionMap' R).app P
  -- We immediately know i is an isomorphism
  have := isIso_restrictionMap'_of_isIso_restrictionMap hS
  -- Recall the Yoneda lemma
  let θ := curriedYonedaLemma'.app P
  -- Aliases for pullback inclusion
  let ι : ∀ {X Y : C} (R : Sieve X) (g : Y ⟶ X), ((R.pullback g).functor ⟶ R.functor) := fun R g ↦ Sieve.pullbackInclusion R g
  let α : ∀ {Y Z : C} (g : Y ⟶ X) (h : Z ⟶ Y), (R.pullback (h ≫ g)).functor ≅ ((R.pullback g).pullback h).functor :=
    fun g h ↦ Sieve.compPullbackInclusionIso R g h
  -- First projection
  let π : ∀ {Y : C} (g : Y ⟶ X), (R.pullback g).functor ⟶ yoneda.obj Y := fun g ↦ (R.pullback g).functorInclusion
  -- Composition lemma
  have composition: ∀ {Y Z : C} (g : Y ⟶ X) (h : Z ⟶ Y), (α g h).hom ≫ ι (R.pullback g) h ≫ ι R g = ι R (h ≫ g) := by
    intros Y Z g h
    ext W i
    simp [ι, Sieve.pullbackInclusion, α, Sieve.compPullbackInclusionIso_eq_cast]
  -- Naturality lemma
  have naturality: ∀ {Y Z : C} (g : Y ⟶ X) (h : Z ⟶ Y), π (h ≫ g) ≫ yoneda.map h = (α g h).hom ≫ ι (R.pullback g) h ≫ π g := by
    intros Y Z g h
    ext W i
    simp [ι, Sieve.pullbackInclusion, π, α, Sieve.compPullbackInclusionIso_eq_cast]
  -- Restriction map for pullback sieve
  let ρ : ∀ {Y : C} {g : Y ⟶ X}, S.arrows g → ((yoneda.obj Y ⟶ P) ≅ ((R.pullback g).functor ⟶ P)) := by
    intros Y g hg
    have := isIso_restrictionMap'_of_isIso_restrictionMap (hR hg)
    exact asIso ((restrictionMap' (R.pullback g)).app P)
  -- Construction of elements from matching families
  let η : (R.functor ⟶ P) → (S.functor ⟶ (yoneda.op ⋙ (yoneda.obj P))) := fun p ↦ {
    app := fun Y ⟨g, hg⟩ ↦ (ρ hg).inv (ι R g ≫ p)
    naturality := by
      intros Y Z h
      ext ⟨g, hg⟩
      simp

      have hgh := S.downward_closed hg h.unop
      have := by
        calc (ρ hgh).hom (yoneda.map h.unop ≫ (ρ hg).inv (ι R g ≫ p))
          _ = π (h.unop ≫ g) ≫ yoneda.map h.unop ≫ (ρ hg).inv (ι R g ≫ p) := by aesop_cat
          _ = (π (h.unop ≫ g) ≫ yoneda.map h.unop) ≫ (ρ hg).inv (ι R g ≫ p) := by rw [Category.assoc]
          _ = ((α g h.unop).hom ≫ ι (R.pullback g) h.unop ≫ π g) ≫ (ρ hg).inv (ι R g ≫ p) := by rw [naturality]
          _ = (α g h.unop).hom ≫ ι (R.pullback g) h.unop ≫ (ρ hg).hom ((ρ hg).inv (ι R g ≫ p)) := by aesop_cat
          _ = ι R (h.unop ≫ g) ≫ p := by simp [← composition]

      simp [← this]
  }
  -- Yoneda of previous construction
  let σ : (R.functor ⟶ P) → (S.functor ⟶ P) := fun p ↦ η p ≫ θ.hom

  have: IsIso j := by
    use σ ≫ inv i
    apply And.intro
    . ext q
      simp
      have: σ (j q) = i q := by
        ext Y g
        simp [σ, η]
        sorry
      calc inv i (σ (j q))
        _ = inv i (i q) := by rw [this]
        _ = (i ≫ inv i) q := by simp
        _ = q := by rw [IsIso.hom_inv_id]; simp
    . ext q
      simp [σ]
      ext Y g
      sorry

  sorry
  -- unfold isIso_restrictionMap restrictionMap
  -- intros Y f
  -- unfold isIso_restrictionMap at hS

  -- have := hS f
  -- have hRf: descends (S.pullback f) (R.pullback f) P := descends_of_pullback hR f

  -- rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  -- intro p
  -- use inv ((restrictionMap S f).app P) (inducedFamily hRf p)
  -- apply And.intro
  -- . sorry
  -- . intros q hq
  --   sorry

instance instGrothendieckTopologyOfleftFixedPoint {J : Set ((X : C) × Sieve X)}
    (h : J ∈ leftFixedPoints isIso_restrictionMap) : GrothendieckTopology C := by
  simp [leftFixedPoints, rightDual, leftDual] at h
  apply GrothendieckTopology.mk (fun X ↦ {S : Sieve X | ⟨X, S⟩ ∈ J})
  . intros X
    rw [← h]
    intros P _
    exact isIso_restrictionMap_top X P
  . intros _ _ S f hS
    rw [← h]
    intros P hP
    exact isIso_restrictionMap_pullback S P (hP hS) f
  . intros _ S _ R _
    rw [← h]
    intros P _
    exact isIso_restrictionMap_transitive S R P (by tauto) (by tauto)

-- open GrothendieckTopos

-- variable {I : Set (Cᵒᵖ ⥤ Type u)}

-- theorem mem_rightFixedPoint (ℰ : Subtopos (Cᵒᵖ ⥤ Type u)) (h : ∀ P, ℰ.obj P ↔ P ∈ I) :
--     I ∈ rightFixedPoints isIso_restrictionMap := sorry

-- instance subtopos_of_rightFixedPoint (h : I ∈ rightFixedPoints isIso_restrictionMap) :
--     Subtopos (Cᵒᵖ ⥤ Type u) where
--   obj P := P ∈ I
--   adj := sorry
--   flat := sorry
--   mem := sorry

-- instance : GrothendieckTopology C ≃ Subtopos (Cᵒᵖ ⥤ Type u) := sorry

end Subtopos
