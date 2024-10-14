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

-- namespace InducedPresentation

-- universe u v

-- variable {E : Type u} [Category.{v} E] (l : C ⥤ E)

-- theorem isSheaf_of_induced_presentation (X : E) : Presheaf.IsSheaf J (l.op ⋙ yoneda.obj X) := by admit

-- def inducedPresentation : E ⥤ Sheaf J (Type v) where
--   obj := fun X => ⟨l.op ⋙ yoneda.obj X, isSheaf_of_induced_presentation J l X⟩
--   map := fun f => ⟨whiskerLeft l.op (yoneda.map f)⟩

-- open Sieve Presieve

-- /-theorem covering_family_iff {X : C} (P : Presieve X) (h : (inducedPresentation J l).IsEquivalence) :
--   generate P ∈ J X ↔ JointlyEpicFam (functorPushforward l P) := by admit
-- -/

-- end InducedPresentation

-- open InducedPresentation

class Topos (E : Type*) [Category E] : Prop where
  presentation : ∃ (C : Type w) (_ : SmallCategory C) (J : GrothendieckTopology C) (F : E ⥤ Sheaf J (Type w)),
    F.IsEquivalence

-- associated sheaf functor at the Yoneda embedding
-- noncomputable def sheafifyYoneda : C ⥤ Sheaf J (Type w) :=
--   yoneda ⋙ (presheafToSheaf J (Type w))

-- -- Left Kan extension of ay along the Yoneda embedding
-- noncomputable def lanSheafifyYoneda : Sheaf J (Type w) ⥤ Sheaf J (Type w) :=
--   inducedPresentation J (sheafifyYoneda J)

-- noncomputable def lanSheafifyYoneda_to_identity_components_components (X : Sheaf J (Type w)) (c : C ᵒᵖ):
--   ((lanSheafifyYoneda J).obj X).val.obj c ≅ X.val.obj c :=
--     Equiv.toIso ((Adjunction.homEquiv (sheafificationAdjunction J (Type w)) (yoneda.obj (Opposite.unop c)) X)) ≪≫ Equiv.toIso yonedaEquiv

instance : Topos.{w} (Sheaf J (Type w)) where
  presentation := by
    use C, inferInstance, J, Functor.id _
    exact Functor.isEquivalence_refl

end GrothendieckTopos
