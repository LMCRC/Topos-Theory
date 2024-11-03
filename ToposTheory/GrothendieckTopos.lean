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

class Topos (ℰ : Type*) [Category ℰ] : Prop where
  presentation : ∃ (C : Type w) (_ : SmallCategory C) (J : GrothendieckTopology C) (F : ℰ ⥤ Sheaf J (Type w)),
    F.IsEquivalence

instance: Topos.{w} (C ᵒᵖ ⥤ Type w) where
  presentation := by
    use C, inferInstance, GrothendieckTopology.trivial C
    sorry

instance: Topos.{w} (Sheaf J (Type w)) where
  presentation := by
    use C, inferInstance, J, Functor.id _
    exact Functor.isEquivalence_refl

end GrothendieckTopos
