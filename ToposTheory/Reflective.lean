import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Yoneda

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory Category Opposite

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable (i : C ⥤ D)
variable [Reflective i]

--NOTE(@doctorn) the two `sorry`s in this file had previously just been `aesop_cat`, but
-- unfortunately, aesop can't find the proof in the latest version.

def adjunctOfReflection {X Y : D} (f : X ⟶ Y) : i ⋙ (coyoneda.obj (op Y)) ⟶ i ⋙ (coyoneda.obj (op X)) where
  app Z := by
    simp [coyoneda]
    let α := (reflectorAdjunction i).homEquiv
    exact (α X Z).toFun ∘ (coyoneda.map ((reflector i).map f).op).app Z ∘ (α Y Z).invFun
  naturality Z W g := by sorry

theorem isIso_reflector_iff_isIso_coyoneda_reflector {X Y : D} (f : X ⟶ Y) :
    IsIso ((reflector i).map f) ↔ IsIso (coyoneda.map ((reflector i).map f).op) := by
  apply Iff.intro
  . intro
    apply Functor.map_isIso
  . intro
    have: IsIso ((reflector i).map f).op := by apply Coyoneda.isIso
    apply isIso_of_op

theorem yonedaMap_eq_adjunctOfReflection (i : C ⥤ D) [Reflective i] {X Y : D} (f : X ⟶ Y) :
    whiskerLeft i (coyoneda.map f.op) = adjunctOfReflection i f := by
  unfold adjunctOfReflection
  sorry

theorem isIso_iff_isIso_adjunctOfReflection {X Y : D} (f : X ⟶ Y) :
    IsIso ((reflector i).map f) ↔ IsIso (adjunctOfReflection i f) := by
  simp [isIso_reflector_iff_isIso_coyoneda_reflector, NatTrans.isIso_iff_isIso_app, adjunctOfReflection, isIso_iff_bijective]

theorem isIso_reflection_iff_locally_iso {X Y : D} (f : X ⟶ Y) :
    IsIso ((reflector i).map f) ↔ IsIso (whiskerLeft i (coyoneda.map f.op)) := by
  rw [isIso_iff_isIso_adjunctOfReflection]
  conv =>
    rhs
    rw [yonedaMap_eq_adjunctOfReflection]

end CategoryTheory
