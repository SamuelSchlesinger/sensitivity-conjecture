/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs
import Sensitivity.Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
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

/-- The parity sum over all Boolean vectors is zero for n ≥ 1.
    Proof: pairing x with flipBit x 0 gives an involution that negates parity. -/
private theorem parity_sum_zero (hn : 0 < n) :
    ∑ x : Fin n → Bool, parity x = 0 := by
  have i₀ : Fin n := ⟨0, hn⟩
  -- flipBit · i₀ is a bijection (it's an involution)
  have hbij : Function.Bijective (fun x : Fin n → Bool => flipBit x i₀) :=
    ⟨fun a b h => by
       -- h : flipBit a i₀ = flipBit b i₀ (after beta-reduction)
       have h' : flipBit a i₀ = flipBit b i₀ := h
       calc a = flipBit (flipBit a i₀) i₀ := (flipBit_flipBit_same a i₀).symm
         _ = flipBit (flipBit b i₀) i₀ := by rw [h']
         _ = b := flipBit_flipBit_same b i₀,
     fun y => ⟨flipBit y i₀, flipBit_flipBit_same y i₀⟩⟩
  have h : ∑ x : Fin n → Bool, parity x =
           ∑ x : Fin n → Bool, -parity x := by
    conv_lhs =>
      rw [← Fintype.sum_bijective _ hbij _ _ (fun x => rfl)]
    simp [parity_flipBit]
  linarith [Finset.sum_neg_distrib (f := fun x : Fin n → Bool => parity x)
              (s := Finset.univ)]

/-- The indicator function is a left inverse to the "true bits" map. -/
private theorem indicator_filter_true (x : Fin n → Bool) :
    indicator (Finset.univ.filter (fun i => x i)) = x := by
  ext i
  simp [indicator]

/-- The "true bits" map is a left inverse to indicator. -/
private theorem filter_true_indicator (T : Finset (Fin n)) :
    Finset.univ.filter (fun i => indicator T i) = T := by
  ext i
  simp [indicator]

/-- Key identity: the parity-weighted sum relates to the top Möbius coefficient.
    ∑_x f_pm(x) · parity(x) = 2 · (-1)^n · c_{univ}(f).

    This follows from expanding the Möbius coefficients and using the
    bijection between Boolean vectors and subsets. -/
theorem moebius_parity_sum (f : BoolFun n) (hn : 0 < n) :
    ∑ x : Fin n → Bool, f.paritySigned x =
    2 * (-1 : ℤ) ^ n * f.moebius Finset.univ := by
  -- Step 1: Express paritySigned in terms of boolToInt
  -- f.pmOne x = 2 * boolToInt(f x) - 1
  have pmOne_eq : ∀ x, f.pmOne x = 2 * boolToInt (f x) - 1 := by
    intro x; unfold BoolFun.pmOne boolToInt; split <;> ring
  simp_rw [BoolFun.paritySigned, pmOne_eq, sub_mul, Finset.sum_sub_distrib, one_mul]
  -- LHS = ∑ 2 * boolToInt(f x) * parity x - ∑ parity x
  rw [parity_sum_zero hn, sub_zero]
  -- Goal: ∑ x, 2 * boolToInt (f x) * parity x = 2 * (-1) ^ n * f.moebius univ
  -- Factor out 2 and reduce to the core identity
  suffices h : ∑ x : Fin n → Bool, boolToInt (f x) * parity x =
               (-1 : ℤ) ^ n * f.moebius Finset.univ by
    simp_rw [show ∀ x : Fin n → Bool,
      2 * boolToInt (f x) * parity x = 2 * (boolToInt (f x) * parity x) from
      fun x => by ring]
    rw [← Finset.mul_sum, h]; ring
  -- Now prove: ∑ x, boolToInt(f x) * parity x = (-1)^n * f.moebius univ
  unfold BoolFun.moebius parity
  -- RHS = (-1)^n * ∑ T ∈ univ.powerset, (-1)^(univ.card-T.card) * boolToInt(f(indicator T))
  rw [Finset.mul_sum]
  -- Simplify (-1)^n * (-1)^(univ.card-T.card) = (-1)^T.card
  conv_rhs =>
    arg 2; ext T
    rw [← mul_assoc, ← pow_add, Finset.card_univ, Fintype.card_fin]
    rw [show n + (n - Finset.card T) =
        Finset.card T + 2 * (n - Finset.card T) from by
      have : T.card ≤ n := by
        have := Finset.card_le_univ T
        rwa [Fintype.card_fin] at this
      omega]
    rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  -- Now both sides sum (-1)^card * boolToInt(f ...)
  -- LHS sums over x : Fin n → Bool with card = (filter true x).card
  -- RHS sums over T ∈ univ.powerset with card = T.card
  -- Use the bijection x ↔ (filter true x) / indicator T
  rw [show Finset.univ.powerset = (Finset.univ : Finset (Finset (Fin n))) from by
    ext S; simp]
  -- Now RHS = ∑ T : Finset (Fin n), (-1)^T.card * boolToInt(f(indicator T))
  -- Change the LHS sum using the bijection
  symm
  apply Fintype.sum_equiv
    (Equiv.ofBijective (fun T : Finset (Fin n) => indicator T)
      ⟨fun S T h => by
         have h' : indicator S = indicator T := h
         rw [← filter_true_indicator S, h', filter_true_indicator],
       fun x => ⟨Finset.univ.filter (fun i => x i), indicator_filter_true x⟩⟩)
  intro T
  simp only [Equiv.ofBijective_apply]
  rw [filter_true_indicator]
  ring

/-- If f has full degree (moebius at univ ≠ 0), the parity-weighted sum is nonzero. -/
theorem fullDegree_paritySigned_sum_ne_zero (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∑ x : Fin n → Bool, f.paritySigned x ≠ 0 := by
  rw [moebius_parity_sum _ hn]
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
  -- The parity-weighted sum is nonzero
  have hne := fullDegree_paritySigned_sum_ne_zero f hn h
  -- Each paritySigned value is ±1 (since pmOne is ±1 and parity is ±1)
  have hval : ∀ x : Fin n → Bool, f.paritySigned x = 1 ∨ f.paritySigned x = -1 := by
    intro x; unfold BoolFun.paritySigned BoolFun.pmOne parity
    rcases neg_one_pow_eq_or (R := ℤ)
      (Finset.univ.filter (fun i => x i)).card with h | h <;>
      cases f x <;> simp [h]
  -- Let A = {x | paritySigned x = 1}, B = {x | paritySigned x = -1}
  set A := Finset.univ.filter (fun x : Fin n → Bool => f.paritySigned x = 1)
  set B := Finset.univ.filter (fun x : Fin n → Bool => f.paritySigned x = -1)
  -- A ∪ B = univ and they are disjoint
  have hunion : A ∪ B = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A, B]
    exact iff_of_true (hval x) trivial
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxB
    linarith
  -- ∑ paritySigned = |A| - |B|
  have hsum : ∑ x : Fin n → Bool, f.paritySigned x = ↑A.card - ↑B.card := by
    have hA_sum : ∑ x ∈ A, f.paritySigned x = (A.card : ℤ) := by
      calc ∑ x ∈ A, f.paritySigned x = ∑ _ ∈ A, (1 : ℤ) :=
            Finset.sum_congr rfl (fun x hx => by
              simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx)
        _ = ↑A.card := by simp
    have hB_sum : ∑ x ∈ B, f.paritySigned x = -(↑B.card : ℤ) := by
      calc ∑ x ∈ B, f.paritySigned x = ∑ _ ∈ B, (-1 : ℤ) :=
            Finset.sum_congr rfl (fun x hx => by
              simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx)
        _ = -(↑B.card : ℤ) := by simp
    -- Decompose the sum over univ into A ∪ B
    have key : ∑ x ∈ A ∪ B, f.paritySigned x = ↑A.card - ↑B.card := by
      rw [Finset.sum_union hdisj, hA_sum, hB_sum]; ring
    rwa [hunion] at key
  -- |A| + |B| = 2^n (total number of Boolean vectors)
  have htotal : A.card + B.card = 2 ^ n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
        Fintype.card_pi_const, Fintype.card_bool]
  -- Since sum ≠ 0, one of |A|, |B| must be > 2^(n-1)
  by_cases hA : A.card > 2 ^ (n - 1)
  · exact ⟨1, Or.inl rfl, hA⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    push_neg at hA
    -- Unify the goal's filter expression with B
    show 2 ^ (n - 1) < B.card
    -- hA : A.card ≤ 2^(n-1), htotal : A.card + B.card = 2^n
    -- Need: 2^(n-1) < B.card
    -- Strict inequality: if B.card = 2^(n-1), then A.card = 2^(n-1), sum = 0, contradiction
    suffices hne' : B.card ≠ 2 ^ (n - 1) by
      -- Prove h2pow with concrete expressions, then abstract for omega
      have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]; ring
      set p := 2 ^ (n - 1)
      omega
    intro heq
    have hA_eq : A.card = 2 ^ (n - 1) := by
      have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]; ring
      set p := 2 ^ (n - 1)
      omega
    apply hne
    rw [hsum, hA_eq, heq]; push_cast; omega

end Sensitivity
