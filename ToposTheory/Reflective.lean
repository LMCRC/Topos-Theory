import MathLib.CategoryTheory.Adjunction.Reflective
import MathLib.CategoryTheory.Yoneda

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory Category Adjunction Opposite

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable (i : C ⥤ D)
variable [Reflective i]

def adjunctOfReflection {X Y : D} (f : X ⟶ Y) : i ⋙ (coyoneda.obj (op Y)) ⟶ i ⋙ (coyoneda.obj (op X)) where
  app := by
    intro Z
    simp [coyoneda]
    have rf := (yoneda.obj Z).map ((reflector i).map f).op
    simp [yoneda] at rf
    exact ((reflectorAdjunction i).homEquiv X Z).toFun ∘ rf ∘ ((reflectorAdjunction i).homEquiv Y Z).invFun

theorem isIso_reflector_iff_isIso_yoneda_reflector {X Y : D} (f : X ⟶ Y) :
    IsIso ((reflector i).map f) ↔ ∀ (Z : C), IsIso ((yoneda.obj Z).map ((reflector i).map f).op) := by
  apply Iff.intro
  . intros h Z
    apply Functor.map_isIso
  . intro h
    have: ∀ (Z : C), (yoneda.obj Z).map ((reflector i).map f).op = (coyoneda.map ((reflector i).map f).op).app Z := by
      simp [yoneda, coyoneda]
    conv at h =>
      ext Z
      rw [this Z]
    rw [← NatTrans.isIso_iff_isIso_app] at h
    have := Coyoneda.isIso ((reflector i).map f).op
    apply isIso_of_op

theorem isIso_iff_isIso_adjunctOfReflection {X Y : D} (f : X ⟶ Y) :
    IsIso ((reflector i).map f) ↔ IsIso (adjunctOfReflection i f) := by
  conv =>
    rhs
    rw [NatTrans.isIso_iff_isIso_app]
    ext Z
    simp [isIso_iff_bijective, adjunctOfReflection]
    rw [← isIso_iff_bijective]
  exact isIso_reflector_iff_isIso_yoneda_reflector i f

theorem yonedaMap_eq_adjunctOfReflection (i : C ⥤ D) [Reflective i] {X Y : D} (f : X ⟶ Y) {Z : C} :
    (yoneda.obj (i.obj Z)).map f.op = (adjunctOfReflection i f).app Z := by
  unfold adjunctOfReflection
  aesop_cat

theorem isIso_reflection_iff_locally_iso {X Y : D} (f : X ⟶ Y) :
    IsIso ((reflector i).map f) ↔ ∀ (Z : C), IsIso ((yoneda.obj (i.obj Z)).map f.op) := by
  rw [isIso_iff_isIso_adjunctOfReflection]
  conv =>
    rhs
    ext
    rw [yonedaMap_eq_adjunctOfReflection]
  rw [← NatTrans.isIso_iff_isIso_app]
