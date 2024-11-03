import ToposTheory.GrothendieckSubtopos
import ToposTheory.Saturation
import Mathlib.Order.Rel.GaloisConnection

open CategoryTheory Opposite

namespace Subtopos

/-! ### The induced duality of topologies and subtoposes -/

universe u

variable {C : Type u} [SmallCategory C]

open Limits NatTrans Rel

--TODO(@doctorn) move this out
namespace Sieve

  def pullbackInclusion {X : C} (S : Sieve X) {Y : C} (f : Y ⟶ X) :
      (S.pullback f).functor ⟶ S.functor := by
    simp [Sieve.functor, Sieve.pullback]
    exact { app := fun Z ↦ fun ⟨g, hg⟩ ↦ ⟨g ≫ f, hg⟩ }

  def pullback_comp_functor_eq {X : C} (S : Sieve X) {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
      (S.pullback (g ≫ f)).functor = ((S.pullback f).pullback g).functor := by
    rw [Sieve.pullback_comp]

  def compPullbackInclusionIso {X : C} (S : Sieve X) {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
      (S.pullback (g ≫ f)).functor ≅ ((S.pullback f).pullback g).functor where
    hom := Sieve.natTransOfLe _
    inv := Sieve.natTransOfLe _

  def yonedaIsoTopFunctor (X : C) : yoneda.obj X ≅ Sieve.functor (X := X) ⊤ :=
    NatIso.ofComponents (fun X' ↦ by simp; exact Equiv.toIso {
      toFun := fun f ↦ ⟨f, trivial⟩
      invFun := fun g ↦ g.1
      left_inv := by tauto
      right_inv := by tauto
    })

end Sieve

@[simp]
def restrictionMap {X : C} (S : Sieve X) {X' : C} (f : X' ⟶ X) :
    (coyoneda.obj (op (yoneda.obj X'))) ⟶ (coyoneda.obj (op (S.pullback f).functor)) :=
  coyoneda.map (S.pullback f).functorInclusion.op

@[simp]
def idRestrictionMap {X : C} (S : Sieve X):
    (coyoneda.obj (op (yoneda.obj X))) ⟶ (coyoneda.obj (op S.functor)) :=
  coyoneda.map S.functorInclusion.op

def isIso_restrictionMap (XS : (X : C) × Sieve X) (P : Cᵒᵖ ⥤ Type u) : Prop :=
  ∀ {X' : C} (f : X' ⟶ XS.1), IsIso ((restrictionMap XS.2 f).app P)

lemma isIso_idRestrictionMap_of_isIso_restrictionMap {XS : (X : C) × Sieve X} {P : Cᵒᵖ ⥤ Type u} (h : isIso_restrictionMap XS P) :
    IsIso ((idRestrictionMap XS.2).app P) := by
  unfold idRestrictionMap
  rw [← XS.snd.pullback_id]
  exact h (𝟙 _)

lemma isIso_restrictionMap_top (X : C) (P : Cᵒᵖ ⥤ Type u) : isIso_restrictionMap ⟨X, ⊤⟩ P := by
  unfold isIso_restrictionMap restrictionMap
  intros X' _
  use (fun g ↦ by simp at g; exact (Sieve.yonedaIsoTopFunctor X').hom ≫ g)
  aesop_cat

lemma isIso_restrictionMap_pullback {X : C} {S : Sieve X} {P : C ᵒᵖ ⥤ Type u}
    (h : isIso_restrictionMap ⟨X, S⟩ P) {Y : C} (f : Y ⟶ X) : isIso_restrictionMap ⟨Y, S.pullback f⟩ P := by
  unfold isIso_restrictionMap restrictionMap
  intros Z g
  rw [← Sieve.pullback_comp]
  exact h (g ≫ f)

section Transitivity

-- TODO(@doctorn) this probably wants renaming
def descends {X : C} (S R : Sieve X) (P : C ᵒᵖ ⥤ Type u) : Prop :=
  ∀ {Y : C} {f : Y ⟶ X}, S.arrows f → isIso_restrictionMap ⟨Y, R.pullback f⟩ P

variable {X : C} {S R : Sieve X} {P : C ᵒᵖ ⥤ Type u}

lemma descends_of_pullback (hR : descends S R P) {Y : C} (f : Y ⟶ X) :
    descends (S.pullback f) (R.pullback f) P := by
  intros Z g hg
  rw [← Sieve.pullback_comp]
  unfold isIso_restrictionMap
  intros W h
  exact hR hg h

noncomputable def restrictionOfDescends (hR : descends S R P) {Y : C} {g : Y ⟶ X} (hg : S.arrows g) :
    ((yoneda.obj Y ⟶ P) ≅ ((R.pullback g).functor ⟶ P)) := by
  have := isIso_idRestrictionMap_of_isIso_restrictionMap (hR hg)
  exact asIso ((idRestrictionMap (R.pullback g)).app P)

noncomputable def liftingOfDescends (hR : descends S R P) (p : R.functor ⟶ P) :
    (S.functor ⟶ (yoneda.op ⋙ (yoneda.obj P))) where
  app Y g := (restrictionOfDescends hR g.2).inv (Sieve.pullbackInclusion R g.1 ≫ p)
  naturality Y Z h := by
    ext ⟨g, hg⟩
    have hgh := S.downward_closed hg h.unop
    have := by
      calc (restrictionOfDescends hR hgh).hom (yoneda.map h.unop ≫ (restrictionOfDescends hR hg).inv (Sieve.pullbackInclusion R g ≫ p))
        _ = (Sieve.compPullbackInclusionIso R g h.unop).hom
              ≫ Sieve.pullbackInclusion (R.pullback g) h.unop
              ≫ (restrictionOfDescends hR hg).hom ((restrictionOfDescends hR hg).inv (Sieve.pullbackInclusion R g ≫ p))
          := by simp [restrictionOfDescends]; aesop_cat
        _ = Sieve.pullbackInclusion R (h.unop ≫ g) ≫ p
          := by ext W i; simp [Sieve.pullbackInclusion]; aesop_cat
    simp [← this]

noncomputable def yonedaLiftingOfDescends (hR : descends S R P) (p : R.functor ⟶ P) : S.functor ⟶ P :=
  liftingOfDescends hR p ≫ (curriedYonedaLemma'.app P).hom

theorem isIso_idRestrictionMap_transitive {X : C} {S R : Sieve X} {P : C ᵒᵖ ⥤ Type u}
    (hS : isIso_restrictionMap ⟨X, S⟩ P) (hR : descends S R P) : IsIso ((idRestrictionMap R).app P) := by
  have := isIso_idRestrictionMap_of_isIso_restrictionMap hS
  use yonedaLiftingOfDescends hR ≫ inv ((idRestrictionMap S).app P)
  apply And.intro
  . have: (idRestrictionMap R).app P ≫ yonedaLiftingOfDescends hR = (idRestrictionMap S).app P := by
      ext q Y ⟨g, hg⟩
      calc _
        _ = (curriedYonedaLemma'.app P).hom.app Y ((restrictionOfDescends hR hg).inv ((restrictionOfDescends hR hg).hom (yoneda.map g ≫ q)))
          := by simp [restrictionOfDescends]; aesop_cat
        _ = q.app Y g
          := by simp [curriedYonedaLemma', yonedaEquiv]
    rw [← Category.assoc, this, IsIso.hom_inv_id]
  . sorry

lemma isIso_restrictionMap_transitive {X : C} {S R : Sieve X} {P : C ᵒᵖ ⥤ Type u}
    (hS : isIso_restrictionMap ⟨X, S⟩ P) (hR : descends S R P) : isIso_restrictionMap ⟨X, R⟩ P := by
  unfold isIso_restrictionMap
  intros Y f
  exact isIso_idRestrictionMap_transitive (isIso_restrictionMap_pullback hS f) (descends_of_pullback hR f)

end Transitivity

instance instGrothendieckTopologyOfLeftFixedPoint {J : Set ((X : C) × Sieve X)}
    (h : J ∈ leftFixedPoints isIso_restrictionMap) : GrothendieckTopology C := by
  simp [leftFixedPoints, rightDual, leftDual] at h
  apply GrothendieckTopology.mk (fun X ↦ {S : Sieve X | ⟨X, S⟩ ∈ J})
  . intros X; rw [← h]; intros P _
    exact isIso_restrictionMap_top X P
  . intros _ _ _ f hS; rw [← h]; intros _ hP
    exact isIso_restrictionMap_pullback (hP hS) f
  . intros; rw [← h]; intros P _
    exact isIso_restrictionMap_transitive (by tauto) (by tauto)

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
    rw [← S.pullback_id]
    exact this (𝟙 _)
  . tauto

instance instLeftFixedPointsEquivGrothendieckTopologies :
    leftFixedPoints (isIso_restrictionMap (C := C)) ≃ GrothendieckTopology C where
  toFun := fun ⟨_, hJ⟩ ↦ instGrothendieckTopologyOfLeftFixedPoint hJ
  invFun J := ⟨_, mem_leftFixedPoint J⟩
  left_inv := by tauto
  right_inv := by tauto

open GrothendieckTopos

instance instSubtoposOfRightFixedPoint {I : Set (Cᵒᵖ ⥤ Type u)} (h : I ∈ rightFixedPoints isIso_restrictionMap) :
    Subtopos (Cᵒᵖ ⥤ Type u) where
  obj P := P ∈ I
  adj := sorry
  flat := sorry
  mem := sorry

theorem mem_rightFixedPoint (ℰ : Subtopos (Cᵒᵖ ⥤ Type u)) :
    {P : C ᵒᵖ ⥤ Type u | ℰ.obj P} ∈ rightFixedPoints isIso_restrictionMap := sorry

instance instRightFixedPointsEquivSubtopoi :
    rightFixedPoints (isIso_restrictionMap (C := C)) ≃ Subtopos (C ᵒᵖ ⥤ Type u) where
  toFun := fun ⟨_, hI⟩ ↦ instSubtoposOfRightFixedPoint hI
  invFun ℰ := ⟨_, mem_rightFixedPoint ℰ⟩
  left_inv := by tauto
  right_inv := by intro; ext; simp [instSubtoposOfRightFixedPoint]

-- TODO(@doctorn) note that this proves an equivalence of types, not an equivalence of categories.
-- We should aim to upgrade this theorem to show that the two categories are equivalent.
instance: GrothendieckTopology C ≃ Subtopos (Cᵒᵖ ⥤ Type u) :=
  Equiv.trans
    (Equiv.symm instLeftFixedPointsEquivGrothendieckTopologies)
    (Equiv.trans (equivFixedPoints (isIso_restrictionMap (C := C))) instRightFixedPointsEquivSubtopoi)

end Subtopos
