import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Equivalence

universe u

namespace CategoryTheory

open CategoryTheory

variable (C : Type u) [SmallCategory C]

open Opposite CategoryTheory Category Limits

namespace Presieve

private
noncomputable def identityElement (J : GrothendieckTopology C) (X : C) : (sheafify J (yoneda.obj X)).obj (Opposite.op X) :=
  (toSheafify J (yoneda.obj X)).app (Opposite.op X) (𝟙 _)

private
theorem sheafify_identityElement_naturality (J : GrothendieckTopology C) {X Y : C} (f : Y ⟶ X) :
    (sheafify J (yoneda.obj X)).map f.op (identityElement C J X) = (toSheafify J (yoneda.obj X)).app (op Y) f := by
 have := congrFun ((toSheafify J (yoneda.obj X)).naturality f.op) (𝟙 X)
 simp at this
 exact this.symm

private
theorem imageSieve_identityElement_le (J : GrothendieckTopology C) (X : C) (S : Sieve X) :
    S ≤ Presheaf.imageSieve (sheafifyMap J S.functorInclusion) (identityElement C J X) := by
  unfold Presheaf.imageSieve
  simp
  intros Y f hf

  use (toSheafify J S.functor).app (op Y) (by unfold Sieve.functor; simp; exact ⟨f, hf⟩)

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
    _ = (sheafify J (yoneda.obj X)).map f.op (identityElement C J X)
      := (sheafify_identityElement_naturality C J f).symm

private
theorem imageSieve_identityElement_ge (J : GrothendieckTopology C) (X : C) (S : Sieve X) :
    Presheaf.imageSieve (sheafifyMap J S.functorInclusion) (identityElement C J X) ≤ S := sorry

private
theorem imageSieve_identityElement_eq (J : GrothendieckTopology C) (X : C) (S : Sieve X) :
    S = Presheaf.imageSieve (sheafifyMap J S.functorInclusion) (identityElement C J X) := by
  apply le_antisymm
  . exact imageSieve_identityElement_le C J X S
  . exact imageSieve_identityElement_ge C J X S

theorem isIso_functorInclusion_iff_yonedaSheafCondition {X : C} (S : Sieve X) (P : C ᵒᵖ ⥤ Type u):
    IsIso ((yoneda.map S.functorInclusion).app (op P)) ↔ Presieve.YonedaSheafCondition P S :=
  sorry

theorem isIso_sheafifyMap_functorInclusion_iff_covering (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    IsIso (sheafifyMap J S.functorInclusion) ↔ S ∈ J X := by
  apply Iff.intro
  . intro
    rw [imageSieve_identityElement_eq C J X S]

    have h: Presheaf.IsLocallySurjective J (sheafifyMap J S.functorInclusion) :=
      Presheaf.isLocallySurjective_of_iso J (sheafifyMap J S.functorInclusion)

    apply Presheaf.imageSieve_mem at h
    exact h (identityElement C J X)
  . intro h
    -- NOTE(@doctorn) use the fact that an isomorphism in the image of a reflector is determined by the
    -- local objects. This doesn't appear to be in MathLib so we will need to prove it, but hopefully
    -- moving to the abstract setting will make this slightly less painful.
    sorry

    -- have: ∀ (F : SheafOfTypes J), IsIso ((yoneda.map S.functorInclusion).app (op F.val)) := by
    --   intro F
    --   apply (isIso_functorInclusion_iff_yonedaSheafCondition C S F.val).mpr
    --   apply (Presieve.isSheafFor_iff_yonedaSheafCondition).mp
    --   exact F.cond S h

    -- have: IsIso (yoneda.map ((presheafToSheaf J (Type u)).map S.functorInclusion)) := by
    --   apply (NatTrans.isIso_iff_isIso_app _).mpr
    --   intro F
    --   unfold yoneda
    --   simp
    --   sorry

    -- apply Yoneda.isIso

theorem allSheavesRespect_iff_isIso_sheafifyMap (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    (∀ {P : C ᵒᵖ ⥤ Type u}, Presieve.IsSheaf J P → Presieve.IsSheafFor P S.arrows)
      ↔ IsIso (sheafifyMap J S.functorInclusion) := by
  apply Iff.intro
  . sorry
  . intro h
    apply (isIso_sheafifyMap_functorInclusion_iff_covering C J S).mp at h
    tauto

theorem allSheavesRespect_iff_covering (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    (∀ {P : C ᵒᵖ ⥤ Type u}, Presieve.IsSheaf J P → Presieve.IsSheafFor P S.arrows) ↔ S ∈ J X := by
  apply Iff.intro
  . intro h
    apply (isIso_sheafifyMap_functorInclusion_iff_covering C J S).mp
    exact (allSheavesRespect_iff_isIso_sheafifyMap C J S).mp h
  . tauto

end Presieve

end CategoryTheory
