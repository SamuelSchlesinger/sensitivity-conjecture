/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs
import Sensitivity.Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
# Parity Function and Imbalance Lemma

The parity function and its interaction with Boolean functions and sensitivity.

## Main results

- `parity_flipBit` — flipping a bit negates the parity
- `moebius_parity_sum` — the Möbius coefficient relates to parity-weighted sum
- `fullDegree_imbalance` — if f has full degree n, one "parity-sign class"
  has more than half the vertices
-/

namespace Sensitivity

variable {n : ℕ}

/-- Parity: (-1)^(number of true bits). -/
def parity (x : Fin n → Bool) : ℤ :=
  (-1) ^ (Finset.univ.filter (fun i => x i)).card

/-- ±1 encoding of a Boolean function: true ↦ 1, false ↦ -1. -/
def BoolFun.pmOne (f : BoolFun n) (x : Fin n → Bool) : ℤ :=
  if f x then 1 else -1

/-- The parity-signed function: g(x) = f_pm(x) · parity(x). -/
def BoolFun.paritySigned (f : BoolFun n) (x : Fin n → Bool) : ℤ :=
  f.pmOne x * parity x

theorem BoolFun.pmOne_ne_zero (f : BoolFun n) (x : Fin n → Bool) :
    f.pmOne x ≠ 0 := by
  unfold pmOne; split <;> omega

theorem parity_ne_zero (x : Fin n → Bool) : parity x ≠ 0 := by
  unfold parity; positivity

private theorem filter_flipBit_true (x : Fin n → Bool) (i : Fin n) (hi : x i = true) :
    Finset.univ.filter (fun j : Fin n => flipBit x i j = true) =
    (Finset.univ.filter (fun j : Fin n => x j = true)).erase i := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hj
    by_cases hji : j = i
    · subst hji; simp [flipBit_apply_same, hi] at hj
    · exact ⟨hji, by rwa [flipBit_apply_ne x i hji] at hj⟩
  · intro ⟨hji, hj⟩
    rwa [flipBit_apply_ne x i hji]

private theorem filter_flipBit_false (x : Fin n → Bool) (i : Fin n) (hi : x i = false) :
    Finset.univ.filter (fun j : Fin n => flipBit x i j = true) =
    insert i (Finset.univ.filter (fun j : Fin n => x j = true)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hj
    by_cases hji : j = i
    · left; exact hji
    · right; rwa [flipBit_apply_ne x i hji] at hj
  · intro hj
    rcases hj with rfl | hj
    · simp [flipBit_apply_same, hi]
    · by_cases hji : j = i
      · subst hji; simp [flipBit_apply_same, hi]
      · rwa [flipBit_apply_ne x i hji]

/-- Flipping a bit negates the parity. -/
theorem parity_flipBit (x : Fin n → Bool) (i : Fin n) :
    parity (flipBit x i) = -parity x := by
  unfold parity
  have key : ∀ (a b : ℕ), a + 1 = b ∨ b + 1 = a →
      (-1 : ℤ) ^ a = -((-1 : ℤ) ^ b) := by
    intro a b hab
    rcases hab with ⟨rfl⟩ | ⟨rfl⟩ <;> simp [pow_succ]
  apply key
  cases hxi : x i
  · right
    have hS : Finset.univ.filter (fun j : Fin n => flipBit x i j) =
              insert i (Finset.univ.filter (fun j : Fin n => x j)) := by
      ext j; simp [flipBit]; by_cases h : j = i <;> simp [h, hxi, Function.update]
    have hni : i ∉ Finset.univ.filter (fun j : Fin n => x j) := by simp [hxi]
    rw [hS, Finset.card_insert_of_notMem hni]
  · left
    have hS : Finset.univ.filter (fun j : Fin n => flipBit x i j) =
              (Finset.univ.filter (fun j : Fin n => x j)).erase i := by
      ext j; simp [flipBit]; by_cases h : j = i <;> simp [h, hxi, Function.update]
    have hi : i ∈ Finset.univ.filter (fun j : Fin n => x j) := by simp [hxi]
    rw [hS, Finset.card_erase_of_mem hi]
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    omega

/-- If paritySigned is the same at x and flipBit x i, then f is sensitive there.

    Proof: parity flips sign under flipBit. If f_pm · parity stays the same,
    f_pm must also flip, so f changes value. -/
theorem BoolFun.sensitiveAt_of_paritySigned_eq (f : BoolFun n)
    (x : Fin n → Bool) (i : Fin n)
    (h : f.paritySigned (flipBit x i) = f.paritySigned x) :
    f.sensitiveAt x i := by
  unfold sensitiveAt
  unfold paritySigned pmOne at h
  rw [parity_flipBit] at h
  -- h : (if f (flipBit x i) then 1 else -1) * -parity x =
  --     (if f x then 1 else -1) * parity x
  intro heq
  rw [heq] at h
  have hpnz := parity_ne_zero x
  -- Now h says: (if f x then 1 else -1) * -parity x = (if f x then 1 else -1) * parity x
  -- So (if f x then 1 else -1) * (-parity x - parity x) = 0
  have : (if f x then (1 : ℤ) else -1) * (-parity x - parity x) = 0 := by linarith
  rw [show -parity x - parity x = -2 * parity x from by ring] at this
  have := mul_eq_zero.mp this
  rcases this with h1 | h1
  · split_ifs at h1; all_goals omega
  · exact hpnz (by linarith)

/-- Key identity: the parity-weighted sum relates to the top Möbius coefficient.
    ∑_x f_pm(x) · parity(x) = 2 · (-1)^n · c_{univ}(f).

    This follows from expanding the Möbius coefficients and using the
    bijection between Boolean vectors and subsets. -/
theorem moebius_parity_sum (f : BoolFun n) :
    ∑ x : Fin n → Bool, f.paritySigned x =
    2 * (-1 : ℤ) ^ n * f.moebius Finset.univ := by
  sorry

/-- If f has full degree (moebius at univ ≠ 0), the parity-weighted sum is nonzero. -/
theorem fullDegree_paritySigned_sum_ne_zero (f : BoolFun n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∑ x : Fin n → Bool, f.paritySigned x ≠ 0 := by
  rw [moebius_parity_sum]
  apply mul_ne_zero
  apply mul_ne_zero
  · omega
  · positivity
  · exact h

/-- Imbalance: if the parity-weighted sum is nonzero, then one of the two
    "parity-sign classes" has more than 2^{n-1} elements. -/
theorem fullDegree_imbalance (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      2 ^ (n - 1) < (Finset.univ.filter (fun x : Fin n → Bool =>
        f.paritySigned x = c)).card := by
  sorry

end Sensitivity
