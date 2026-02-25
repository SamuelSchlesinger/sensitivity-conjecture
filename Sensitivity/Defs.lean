/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Boolean Function Definitions

Core definitions for Boolean functions on the hypercube `Fin n → Bool`,
including sensitivity.
-/

namespace Sensitivity

/-- A Boolean function on n variables. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

variable {n : ℕ}

/-- Flip the i-th bit of an input. -/
def flipBit (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

@[simp]
theorem flipBit_apply_same (x : Fin n → Bool) (i : Fin n) :
    flipBit x i i = !x i := by
  simp [flipBit]

@[simp]
theorem flipBit_apply_ne (x : Fin n → Bool) (i : Fin n) {j : Fin n} (h : j ≠ i) :
    flipBit x i j = x j := by
  simp [flipBit, Function.update_of_ne h]

@[simp]
theorem flipBit_flipBit_same (x : Fin n → Bool) (i : Fin n) :
    flipBit (flipBit x i) i = x := by
  ext j
  by_cases h : j = i
  · subst h; simp [flipBit, Bool.not_not]
  · simp [flipBit, Function.update_of_ne h]

theorem flipBit_ne_self (x : Fin n → Bool) (i : Fin n) :
    flipBit x i ≠ x := by
  intro h
  have := congr_fun h i
  simp [flipBit] at this

theorem flipBit_injective (x : Fin n → Bool) : Function.Injective (flipBit x) := by
  intro i j hij
  by_contra h
  push_neg at h
  have h1 : flipBit x i i = !x i := flipBit_apply_same x i
  have h2 : flipBit x j i = x i := flipBit_apply_ne x j h
  rw [congr_fun hij i, h2] at h1
  simp at h1

/-- Whether f is sensitive at input x in coordinate i. -/
def BoolFun.sensitiveAt (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) : Prop :=
  f (flipBit x i) ≠ f x

instance (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    Decidable (f.sensitiveAt x i) :=
  inferInstanceAs (Decidable (f (flipBit x i) ≠ f x))

/-- The local sensitivity of f at input x: number of sensitive coordinates. -/
def BoolFun.localSensitivity (f : BoolFun n) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => f.sensitiveAt x i).card

/-- The sensitivity of f: maximum local sensitivity over all inputs. -/
noncomputable def BoolFun.sensitivity (f : BoolFun n) : ℕ :=
  Finset.univ.sup (fun x => f.localSensitivity x)

/-- The sensitivity is at most n. -/
theorem BoolFun.sensitivity_le (f : BoolFun n) : f.sensitivity ≤ n := by
  apply Finset.sup_le
  intro x _
  unfold localSensitivity
  calc (Finset.univ.filter fun i => f.sensitiveAt x i).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n

/-- The local sensitivity is at most the sensitivity. -/
theorem BoolFun.localSensitivity_le_sensitivity (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ f.sensitivity := by
  exact Finset.le_sup (f := fun x => f.localSensitivity x) (Finset.mem_univ x)

/-- Flip all bits in a set of coordinates. -/
def flipCoords (x : Fin n → Bool) (S : Finset (Fin n)) : Fin n → Bool :=
  fun j => if j ∈ S then !x j else x j

end Sensitivity
