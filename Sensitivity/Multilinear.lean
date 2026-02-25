/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic

/-!
# Multilinear Representation and Degree

Every Boolean function has a unique multilinear polynomial representation
over ℤ. We define the Möbius coefficients and the degree.

## Main definitions

- `BoolFun.moebius` — the Möbius coefficient c_S of f
- `BoolFun.degree` — the multilinear degree
-/

namespace Sensitivity

variable {n : ℕ}

/-- Indicator assignment: x_i = true iff i ∈ S. -/
def indicator (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

@[simp]
theorem indicator_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = true ↔ i ∈ S := by
  simp [indicator]

@[simp]
theorem indicator_not_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = false ↔ i ∉ S := by
  simp [indicator]

/-- The integer encoding of a Bool: true ↦ 1, false ↦ 0. -/
def boolToInt (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem boolToInt_true : boolToInt true = 1 := rfl
@[simp] theorem boolToInt_false : boolToInt false = 0 := rfl

/-- The Möbius coefficient of f at S: coefficient of ∏_{i∈S} x_i
    in the unique multilinear polynomial representing f.
    Computed by inclusion-exclusion: c_S = ∑_{T⊆S} (-1)^{|S|-|T|} f(1_T). -/
def BoolFun.moebius (f : BoolFun n) (S : Finset (Fin n)) : ℤ :=
  ∑ T ∈ S.powerset,
    (-1) ^ (S.card - T.card) * boolToInt (f (indicator T))

/-- The multilinear degree of f: maximum |S| over S with nonzero Möbius coefficient. -/
noncomputable def BoolFun.degree (f : BoolFun n) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)).sup
    Finset.card

/-- The degree is at most n. -/
theorem BoolFun.degree_le (f : BoolFun n) : f.degree ≤ n := by
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter] at hS
  exact le_trans (Finset.card_le_univ S) (le_of_eq (Fintype.card_fin n))

/-- If the degree is d > 0, there exists a set S of size d with nonzero coefficient. -/
theorem BoolFun.exists_degree_witness (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n), S.card = f.degree ∧ f.moebius S ≠ 0 := by
  unfold degree at hd ⊢
  set F := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)
  have hne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [F, h] at hd
  obtain ⟨S, hS, heq⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  rw [Finset.mem_filter] at hS
  exact ⟨S, heq.symm, hS.2⟩

end Sensitivity
