/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
import ToposTheory.GrothendieckTopos
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Grothendieck Subtoposes

-/

open CategoryTheory

namespace GrothendieckTopos

variable (ℰ : Type*) [Category ℰ] [Topos ℰ]

open Functor Limits Adjunction

structure Subtopos where
  obj : ℰ → Prop
  adj : IsRightAdjoint (fullSubcategoryInclusion obj)
  flat : PreservesFiniteLimits (fullSubcategoryInclusion obj).leftAdjoint
  mem : ∀ (E : ℰ), obj E ↔ IsIso ((ofIsRightAdjoint (fullSubcategoryInclusion obj)).unit.app E)

namespace Subtopos

@[ext]
theorem ext {ℰ₁ ℰ₂ : Subtopos ℰ} {h : ℰ₁.obj = ℰ₂.obj} : ℰ₁ = ℰ₂ := by
  sorry

instance: LE (Subtopos ℰ) where
  le ℰ₁ ℰ₂ := ℰ₁.obj ≤ ℰ₂.obj

theorem le_def {ℰ₁ ℰ₂ : Subtopos ℰ} : ℰ₁ ≤ ℰ₂ ↔ ℰ₁.obj ≤ ℰ₂.obj := Iff.refl _

instance: PartialOrder (Subtopos ℰ) where
  __ := instLE ℰ
  le_refl := fun ℰ₁ => (le_def ℰ).mpr le_rfl
  le_trans := fun ℰ₁ ℰ₂ ℰ₃ h₁₂ h₂₃ => (le_def ℰ).mpr (le_trans h₁₂ h₂₃)
  le_antisymm := by aesop

end Subtopos

end GrothendieckTopos
