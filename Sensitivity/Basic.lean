/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs

/-!
# Elementary Properties of Sensitivity

Basic bounds and symmetries for Boolean function sensitivity.
-/

namespace Sensitivity

variable {n : ℕ}

/-- The local sensitivity of the complement equals the local sensitivity. -/
theorem BoolFun.localSensitivity_not (f : BoolFun n) (x : Fin n → Bool) :
    BoolFun.localSensitivity (fun y => !f y) x = f.localSensitivity x := by
  unfold localSensitivity sensitiveAt
  congr 1
  ext i
  simp

/-- The sensitivity of the complement equals the sensitivity. -/
theorem BoolFun.sensitivity_not (f : BoolFun n) :
    BoolFun.sensitivity (fun y => !f y) = f.sensitivity := by
  unfold sensitivity
  congr 1
  funext x
  exact f.localSensitivity_not x

/-- Local sensitivity at x is at most n. -/
theorem BoolFun.localSensitivity_le (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ n := by
  unfold localSensitivity
  calc (Finset.univ.filter fun i => f.sensitiveAt x i).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n

/-- If f is sensitive at x in coordinate i, then flipping i gives a different value. -/
theorem BoolFun.sensitiveAt_iff (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt x i ↔ f (flipBit x i) ≠ f x :=
  Iff.rfl

/-- Sensitivity at x is symmetric: if f is sensitive at x in direction i,
    then f is sensitive at (flipBit x i) in direction i. -/
theorem BoolFun.sensitiveAt_flipBit (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt (flipBit x i) i ↔ f.sensitiveAt x i := by
  unfold sensitiveAt
  rw [flipBit_flipBit_same]
  exact ne_comm

end Sensitivity
