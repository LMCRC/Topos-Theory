/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Grothendieck Toposes

-/

open CategoryTheory

namespace Presieve

variable {C : Type*} [Category C]

/-! ### Jointly epimorphic families -/

class JointlyEpicFam {X : C} (P : Presieve X) : Prop where
  left_cancellation : ∀ {Y : C} (g h : X ⟶ Y), (∀ {Z} {f : Z ⟶ X}, P f → f ≫ g = f ≫ h) → g = h

end Presieve

namespace GrothendieckTopos

/-! ### Grothendieck toposes -/

universe w

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

namespace InducedPresentation

universe u v

variable {E : Type u} [Category.{v} E] (l : C ⥤ E)

--theorem isSheaf_of_induced_presentation (X : E) : Presheaf.IsSheaf J (l.op ⋙ yoneda.obj X) := by admit

def inducedPresentation : E ⥤ (Cᵒᵖ ⥤ (Type v)) where
  --obj := fun X => ⟨l.op ⋙ yoneda.obj X, isSheaf_of_induced_presentation J l X⟩
  --map := fun f => ⟨whiskerLeft l.op (yoneda.map f)⟩
  obj := fun X => l.op ⋙ yoneda.obj X
  map := fun f => whiskerLeft l.op (yoneda.map f)

open Sieve Presieve

/-theorem covering_family_iff {X : C} (P : Presieve X) (h : (inducedPresentation J l).IsEquivalence) :
  generate P ∈ J X ↔ JointlyEpicFam (functorPushforward l P) := by admit
-/

end InducedPresentation

open InducedPresentation

/-class Topos (ℰ : Type*) [Category ℰ] : Prop where
  presentation : ∃ (C : Type w) (_ : SmallCategory C) (J : GrothendieckTopology C) (l : C ⥤ ℰ),
    (inducedPresentation J l).IsEquivalence
-/
class Topos (ℰ : Type*) [Category ℰ] : Prop where
  presentation : ∃ (C : Type w) (_ : SmallCategory C) (J : GrothendieckTopology C) (l : C ⥤ ℰ)
    (F : ℰ ≌ Sheaf J (Type w)), F.functor ⋙ sheafToPresheaf J (Type w) = inducedPresentation l

instance : Topos.{w} (Sheaf J (Type w)) where
  presentation := by
    use C, inferInstance, J
    have : HasWeakSheafify J (Type w) := by
      exact instHasWeakSheafifyOfHasSheafify J (Type w)
    use yoneda ⋙ presheafToSheaf J (Type w)
    sorry

end GrothendieckTopos
