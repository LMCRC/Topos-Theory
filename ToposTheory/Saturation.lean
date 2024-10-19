import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Equivalence
import ToposTheory.Reflective

universe u

namespace CategoryTheory

open Opposite CategoryTheory Category Limits

variable {C : Type u} [SmallCategory C]

namespace Presheaf

private
noncomputable def identityElement (J : GrothendieckTopology C) (X : C) : (sheafify J (yoneda.obj X)).obj (Opposite.op X) :=
  (toSheafify J (yoneda.obj X)).app (Opposite.op X) (𝟙 _)

private
theorem sheafify_identityElement_naturality (J : GrothendieckTopology C) {X Y : C} (f : Y ⟶ X) :
    (sheafify J (yoneda.obj X)).map f.op (identityElement J X) = (toSheafify J (yoneda.obj X)).app (op Y) f := by
 have := congrFun ((toSheafify J (yoneda.obj X)).naturality f.op) (𝟙 X)
 simp at this
 exact this.symm

private
theorem imageSieve_identityElement_le (J : GrothendieckTopology C) (X : C) (S : Sieve X) :
    S ≤ Presheaf.imageSieve (sheafifyMap J S.functorInclusion) (identityElement J X) := by
  simp [Presheaf.imageSieve]
  intros Y f hf

  use (toSheafify J S.functor).app (op Y) (by simp [Sieve.functor]; exact ⟨f, hf⟩)

  -- NOTE(@doctorn) this calc block should not have to be this complicated (look how simple the steps are!).
  -- For whatever reason, I couldn't get Lean4 to accept that the previous lemma would apply without this
  -- massive blob of symbols. I'd really like to fix this...
  calc ((sheafifyMap J S.functorInclusion).app (op Y)) ((toSheafify J S.functor).app (op Y) ⟨f, hf⟩)
    _ = ((toSheafify J S.functor).app (op Y) ≫ ((sheafifyMap J S.functorInclusion).app (op Y))) ⟨f, hf⟩
      := by simp
    _ = ((toSheafify J S.functor) ≫ (sheafifyMap J S.functorInclusion)).app (op Y) ⟨f, hf⟩
      := by rw [← NatTrans.comp_app]
    _ = (S.functorInclusion ≫ (toSheafify J (yoneda.obj X))).app (op Y) ⟨f , hf⟩
      := by rw [toSheafify_naturality J (S.functorInclusion)]
    _ = ((S.functorInclusion.app (op Y)) ≫ (toSheafify J (yoneda.obj X)).app (op Y)) ⟨f , hf⟩
      := by rw [NatTrans.comp_app]
    _ = (toSheafify J (yoneda.obj X)).app (op Y) (S.functorInclusion.app (op Y) ⟨f , hf⟩)
      := by simp
    _ = (toSheafify J (yoneda.obj X)).app (op Y) f
      := by unfold Sieve.functorInclusion; simp
    _ = (sheafify J (yoneda.obj X)).map f.op (identityElement J X)
      := (sheafify_identityElement_naturality J f).symm

private
theorem imageSieve_identityElement_ge (J : GrothendieckTopology C) (X : C) (S : Sieve X) :
    Presheaf.imageSieve (sheafifyMap J S.functorInclusion) (identityElement J X) ≤ S := sorry

private
theorem imageSieve_identityElement_eq (J : GrothendieckTopology C) (X : C) (S : Sieve X) :
    S = Presheaf.imageSieve (sheafifyMap J S.functorInclusion) (identityElement J X) := by
  apply le_antisymm
  . exact imageSieve_identityElement_le J X S
  . exact imageSieve_identityElement_ge J X S

-- NOTE(@doctorn) this should definitely be correctly generalised and added to MathLib.
-- We also want an iff version of `CategoryTheory.Functor.FullyFaithful.isIso_of_isIso_map`.
theorem isIso_iff_isIso_val (J : GrothendieckTopology C) {P Q : Sheaf J (Type u)} (α : P ⟶ Q) :
    IsIso α ↔ IsIso α.val := by
  have: IsIso α.val ↔ IsIso ((sheafToPresheaf J (Type u)).map α) := by simp [sheafToPresheaf]
  rw [this]
  apply Iff.intro
  . intro
    exact (sheafToPresheaf J (Type u)).map_isIso α
  . intro
    exact (fullyFaithfulSheafToPresheaf J (Type u)).isIso_of_isIso_map α

theorem isIso_sheafifyMap_iff_isIso_whiserking (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    IsIso (sheafifyMap J S.functorInclusion)
      ↔ IsIso (whiskerLeft (sheafToPresheaf J (Type u)) (coyoneda.map S.functorInclusion.op)) := by
  have := isIso_reflection_iff_locally_iso (sheafToPresheaf J (Type u)) (S.functorInclusion)
  simp [← this, reflector, Reflective.L, sheafifyMap, isIso_iff_isIso_val]

theorem isIso_whiserking_iff_yonedaSheafCondition (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    IsIso (whiskerLeft (sheafToPresheaf J (Type u)) (coyoneda.map S.functorInclusion.op))
      ↔ ∀ (P : Sheaf J (Type u)), Presieve.YonedaSheafCondition P.val S := by
  unfold Presieve.YonedaSheafCondition
  rw [NatTrans.isIso_iff_isIso_app]
  conv =>
    lhs
    ext P
    rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  simp

theorem allSheavesRespect_iff_isIso_sheafifyMap (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    (∀ {P : C ᵒᵖ ⥤ Type u}, Presheaf.IsSheaf J P → Presieve.IsSheafFor P S.arrows)
      ↔ IsIso (sheafifyMap J S.functorInclusion) := by
  rw [isIso_sheafifyMap_iff_isIso_whiserking, isIso_whiserking_iff_yonedaSheafCondition]
  conv =>
    rhs
    ext P
    rw [← Presieve.isSheafFor_iff_yonedaSheafCondition]
  apply Iff.intro
  . intros h P
    exact h P.cond
  . intros h P hP
    let F: Sheaf J (Type u) := { val := P, cond := hP }
    exact h F

theorem isIso_sheafifyMap_functorInclusion_iff_covering (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    IsIso (sheafifyMap J S.functorInclusion) ↔ S ∈ J X := by
  apply Iff.intro
  . intro
    rw [imageSieve_identityElement_eq (S := S)]
    have := Presheaf.isLocallySurjective_of_iso J (sheafifyMap J S.functorInclusion)
    apply Presheaf.imageSieve_mem at this
    exact this (identityElement J X)
  . intro h
    rw [isIso_sheafifyMap_iff_isIso_whiserking, isIso_whiserking_iff_yonedaSheafCondition]
    intro P
    rw [← Presieve.isSheafFor_iff_yonedaSheafCondition]
    exact P.cond.isSheafFor S h

theorem allSheavesRespect_iff_covering (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    (∀ {P : C ᵒᵖ ⥤ Type u}, Presheaf.IsSheaf J P → Presieve.IsSheafFor P S.arrows) ↔ S ∈ J X := by
  rw [← isIso_sheafifyMap_functorInclusion_iff_covering, allSheavesRespect_iff_isIso_sheafifyMap]

end Presheaf

end CategoryTheory
