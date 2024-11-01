/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Grothendieck toposes

In this file we define Grothendieck toposes.

## Main definitions

Given two categories `C` and `E` and a functor `l` from `C` to `E`, we define a functor
`CategoryTheory.ToposTheory.AssociatedFunctor.associatedFunctor`, from `E` to the category of
presheaves on `C`, associated with `l`. This associated functor coincides with the Yoneda embedding
when `l` is the identity functor (see
`CategoryTheory.ToposTheory.AssociatedFunctor.associatedFunctor_of_id`).

Given a Grothendieck topology `J` on `C`, we define a type class
`CategoryTheory.ToposTheory.AssociatedFunctor.IsPresentation` to express the properties that the
functor associated with `l` is fullyfaithful, its essential image consists of the `J`-sheaves and
there exists a cocontinuous functor extending `l` along the Yoneda embedding.

Finally, we define the type class `CategoryTheory.ToposTheory.Topos` of Grothendieck toposes as the
class of categories `E` for which there exists a small category `C`, a Grothendieck topology `J` on
`C` and a functor `l` from `C` to `E` such that `IsPresentation l J`, i.e. the functor associated
with l satisfies the three properties mentioned above.

Additionally, we define the type class `CategoryTheory.Presieve.JointlyEpicFam` of jointly
epimorphic families of morphisms with a given target `X` in a category `C`, and add a comment to the
effect that, in the previous situation (i.e. with `IsPresentation l J` inhabited), one could prove
the sieve generated by a presieve `P` is `J`-covering if and only if the image of `P` under `l` is a
jointly epimorphic family.

## Main results

We prove that if `C` is a small category endowed with a Grothendieck topology, `E` the corresponding
category of sheaves and `l` is the Yoneda embedding followed by the sheafification functor, then its
associated functor is, up to a natural isomorphism, the embedding of sheaves into presheaves
(see `CategoryTheory.ToposTheory.associatedFunctor_iso_sheafToPresheaf`).

We use the previous result to prove that every category of sheaves on a small site is a Grothendieck
topos in the sense of our definition (see `CategoryTheory.ToposTheory.instToposSheafType`).

## Implementation notes

This implementation follows a definition of Grothendieck toposes suggested by Laurent Lafforgue.

## Tags

Grothendieck topos, category of sheaves, jointly epimorphic family
-/

namespace CategoryTheory

namespace Presieve

/-! ### Jointly epimorphic families -/

variable {C : Type*} [Category C]

class JointlyEpicFam {X : C} (P : Presieve X) : Prop where
/-- A jointly epimorphic family is a presieve satisfying a left-cancellation property. -/
  left_cancellation : ∀ {Y : C} (g h : X ⟶ Y), (∀ {Z} {f : Z ⟶ X}, P f → f ≫ g = f ≫ h) → g = h

end Presieve

namespace ToposTheory

namespace AssociatedFunctor

/-! ### The presheaf-valued associated functor -/

universe u₁ v₁ u₂ v₂

variable {E : Type u₁} [Category.{v₁} E]
variable {C : Type u₂} [Category.{v₂} C]
variable (l : C ⥤ E)

/-- Given a functor `l : C ⥤ E`, we define its associated functor which maps an object `X` of `E`
to the presheaf $\mathrm{Hom}(l(-), X)$. -/
def associatedFunctor : E ⥤ (Cᵒᵖ ⥤ Type v₁) where
  obj := fun X => l.op ⋙ yoneda.obj X
  map := fun f => whiskerLeft l.op (yoneda.map f)

/-- The functor associated with the identity functor is the Yoneda embedding. -/
theorem associatedFunctor_of_id : associatedFunctor (𝟭 E) = yoneda := rfl

variable (J : GrothendieckTopology C)

open Presheaf Functor

class IsPresentation : Prop where
  /-- We require the associated functor to be faithful. -/
  faithful : (associatedFunctor l).Faithful
  /-- The associated functor should also be full. -/
  full : (associatedFunctor l).Full
  /-- Its essential image consists exactly of the `J`sheaves. -/
  isSheaf_iff : ∀ ⦃P : Cᵒᵖ ⥤ Type v₁⦄, IsSheaf J P ↔ P ∈ essImage (associatedFunctor l)
  /-- There exists a cocontinuous functor extending the functor `l` along the Yoneda embedding. -/
  left_adjoint : ∃ (L : (Cᵒᵖ ⥤ Type v₂) ⥤ E) (_ : Limits.PreservesColimits L), yoneda ⋙ L = l

/-
open Sieve Presieve

-- One could show the following result:
theorem covering_family_iff {X : C} (P : Presieve X) (h : IsPresentation l J) :
  generate P ∈ J X ↔ JointlyEpicFam (functorPushforward l P) := by admit
-/

end AssociatedFunctor

open AssociatedFunctor

/-! ### Grothendieck toposes -/

universe w v u

class Topos (E : Type u) [Category.{v} E] : Prop where
  /-- A topos is a category `E` such that there exists a small site (`C`, `J`) and a functor
  `l : C ⥤ E` satisfying `IsPresentation l J`. -/
  presentation : ∃ (C : Type w) (_ : SmallCategory C) (J : GrothendieckTopology C) (l : C ⥤ E),
    IsPresentation l J

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

noncomputable instance associatedFunctor_iso_sheafToPresheaf_obj_obj
    (F : Sheaf J (Type w)) (X : Cᵒᵖ) :
      ((associatedFunctor (yoneda ⋙ presheafToSheaf J (Type w))).obj F).obj X ≅
        ((sheafToPresheaf J (Type w)).obj F).obj X where
  hom := ((sheafificationAdjunction J (Type w)).homEquiv (yoneda.obj X.unop) F).toFun ≫
      yonedaEquiv.toFun
  inv := yonedaEquiv.invFun ≫
      ((sheafificationAdjunction J (Type w)).homEquiv (yoneda.obj X.unop) F).invFun
  hom_inv_id := by aesop_cat
  inv_hom_id := by
    set f := ((sheafificationAdjunction J (Type w)).homEquiv (yoneda.obj X.unop) F).invFun
    set g := ((sheafificationAdjunction J (Type w)).homEquiv (yoneda.obj X.unop) F).toFun
    let hom := yoneda.obj X.unop ⟶ (sheafToPresheaf J (Type w)).obj F
    rw [← Category.assoc]
    apply Eq.trans (b := (yonedaEquiv.invFun ≫ f ≫ g) ≫ yonedaEquiv.toFun)
    case h₁ => rw [← Category.assoc]
    case h₂ => have eq : f ≫ g = 𝟙 hom := by
                apply Equiv.self_comp_symm
               rw [eq]
               rw[Category.comp_id]
               apply Equiv.self_comp_symm

noncomputable def natTrans_associatedFunctor_sheafToPresheaf :
    associatedFunctor (yoneda ⋙ presheafToSheaf J (Type w)) ⟶ sheafToPresheaf J (Type w) where
  app F := { app := fun X => (associatedFunctor_iso_sheafToPresheaf_obj_obj J F X).hom
             naturality := by
              intros
              apply funext
              intro
              unfold associatedFunctor_iso_sheafToPresheaf_obj_obj
              simp only [Equiv.toFun_as_coe, types_comp_apply]
              rw [yonedaEquiv_naturality']
              simp only [EmbeddingLike.apply_eq_iff_eq]
              apply Adjunction.homEquiv_naturality_left
            }
  naturality F G α := by
    ext X β
    have : ((sheafificationAdjunction J (Type w)).homEquiv (yoneda.obj X.unop) G) (β ≫ α) =
        ((sheafificationAdjunction J (Type w)).homEquiv (yoneda.obj X.unop) F) β ≫
          (sheafToPresheaf J (Type w)).map α := by
      apply Adjunction.homEquiv_naturality_right
    apply Eq.trans (b := yonedaEquiv (((sheafificationAdjunction J (Type w)).homEquiv
        (yoneda.obj X.unop) F) β ≫ (sheafToPresheaf J (Type w)).map α))
    case w.h.h.h₁ => unfold associatedFunctor_iso_sheafToPresheaf_obj_obj
                     simpa
    case w.h.h.h₂ => apply yonedaEquiv_comp

instance isIso_natTrans_associatedFunctor_sheafToPresheaf_app_app (F : Sheaf J (Type w)) (X : Cᵒᵖ) :
    IsIso (((natTrans_associatedFunctor_sheafToPresheaf J).app F).app X) :=
  Iso.isIso_hom (associatedFunctor_iso_sheafToPresheaf_obj_obj J F X)

instance isIso_natTrans_associatedFunctor_sheafToPresheaf_app (F : Sheaf J (Type w)) :
    IsIso ((natTrans_associatedFunctor_sheafToPresheaf J).app F) :=
  NatIso.isIso_of_isIso_app ((natTrans_associatedFunctor_sheafToPresheaf J).app F)

instance isIso_natTrans_associatedFunctor_sheafToPresheaf :
    IsIso (natTrans_associatedFunctor_sheafToPresheaf J) :=
  NatIso.isIso_of_isIso_app (natTrans_associatedFunctor_sheafToPresheaf J)

/-- The functor `associatedFunctor (yoneda ⋙ presheafToSheaf J (Type w))` associated with the
Yoneda embedding followed by the sheafification functor is, up to a natural isomorphism, the
inclusion `sheafToPresheaf J (Type w)` of sheaves into presheaves. -/
noncomputable def associatedFunctor_iso_sheafToPresheaf :
    associatedFunctor (yoneda ⋙ presheafToSheaf J (Type w)) ≅ sheafToPresheaf J (Type w) :=
  asIso (natTrans_associatedFunctor_sheafToPresheaf J)

/-- As a result of the above isomorphism, one has
`IsPresentation (yoneda ⋙ presheafToSheaf J (Type w)) J`. -/
instance isPresentation_of_yoneda_comp_presheafToSheaf :
    IsPresentation (yoneda ⋙ presheafToSheaf J (Type w)) J where
  faithful := by
    apply Functor.Faithful.of_iso (F := sheafToPresheaf J (Type w))
    apply Iso.symm
    exact (associatedFunctor_iso_sheafToPresheaf J)
  full := by
    apply Functor.Full.of_iso (F := sheafToPresheaf J (Type w))
    apply Iso.symm
    exact (associatedFunctor_iso_sheafToPresheaf J)
  isSheaf_iff := by
    rw [Functor.essImage_eq_of_natIso (associatedFunctor_iso_sheafToPresheaf J)]
    intro P
    constructor
    · intro h
      use ⟨P, h⟩
      exact (Iso.nonempty_iso_refl P)
    · intro h
      cases' h with Q h
      rw [← Presheaf.isSheaf_of_iso_iff (Classical.choice h)]
      cases' Q with Q hQ
      exact hQ
  left_adjoint := ⟨presheafToSheaf J (Type w), inferInstance, rfl⟩

/-- Every category of sheaves is a Grothendieck topos. -/
instance : Topos.{w} (Sheaf J (Type w)) where
  presentation := by
    use C, inferInstance, J, yoneda ⋙ presheafToSheaf J (Type w)
    exact (isPresentation_of_yoneda_comp_presheafToSheaf J)

end ToposTheory

end CategoryTheory
