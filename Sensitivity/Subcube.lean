/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs
import Sensitivity.Multilinear

/-!
# Subcube Restriction

We define "restriction" of a Boolean function by fixing some coordinates,
and prove that this preserves relevant properties.
-/

namespace Sensitivity

variable {n : ℕ}

/-- Embed an assignment into the "restricted" hypercube: keep values for
    coordinates in `free`, use `base` for the rest. -/
def embed (free : Finset (Fin n)) (base : Fin n → Bool)
    (x : Fin n → Bool) : Fin n → Bool :=
  fun j => if j ∈ free then x j else base j

/-- Restriction of f: fix coordinates outside `free` to `base`. -/
def BoolFun.restrictTo (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) : BoolFun n :=
  fun x => f (embed free base x)

theorem embed_flipBit_free (free : Finset (Fin n)) (base x : Fin n → Bool)
    (i : Fin n) (hi : i ∈ free) :
    embed free base (flipBit x i) = flipBit (embed free base x) i := by
  funext j
  by_cases hji : j = i
  · subst hji; simp [embed, flipBit, hi]
  · by_cases hj : j ∈ free
    · simp [embed, hj, flipBit, Function.update_of_ne hji]
    · simp only [embed, hj, ↓reduceIte, flipBit]
      rw [Function.update_of_ne hji]
      simp [embed, hj]

theorem embed_flipBit_nonfree (free : Finset (Fin n)) (base x : Fin n → Bool)
    (i : Fin n) (hi : i ∉ free) :
    embed free base (flipBit x i) = embed free base x := by
  funext j
  simp only [embed, flipBit]
  by_cases hj : j ∈ free
  · simp [hj, Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
  · simp [hj]

/-- Flipping a coordinate outside `free` doesn't change the restriction. -/
theorem BoolFun.restrictTo_flipBit_nonfree (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    f.restrictTo free base (flipBit x i) = f.restrictTo free base x := by
  unfold restrictTo
  rw [embed_flipBit_nonfree free base x i hi]

/-- The restriction is not sensitive outside `free`. -/
theorem BoolFun.restrictTo_not_sensitiveAt_nonfree (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    ¬(f.restrictTo free base).sensitiveAt x i := by
  unfold sensitiveAt
  push_neg
  exact f.restrictTo_flipBit_nonfree free base x i hi

/-- Sensitivity of the restriction is at most the sensitivity of f. -/
theorem BoolFun.restrictTo_sensitivity_le (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) :
    (f.restrictTo free base).sensitivity ≤ f.sensitivity := by
  apply Finset.sup_le
  intro x _
  apply le_trans _ (f.localSensitivity_le_sensitivity (embed free base x))
  unfold localSensitivity
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hi
  unfold sensitiveAt at hi ⊢
  by_cases him : i ∈ free
  · unfold restrictTo at hi
    rw [embed_flipBit_free free base x i him] at hi
    exact hi
  · exfalso
    exact f.restrictTo_not_sensitiveAt_nonfree free base x i him hi

/-- Embedding the indicator of T ⊆ S ⊆ free with base = false
    gives back the indicator of T. -/
theorem embed_indicator_subset (free S T : Finset (Fin n))
    (hS : S ⊆ free) (hT : T ⊆ S) :
    embed free (fun _ => false) (indicator T) = indicator T := by
  funext j
  simp only [embed]
  by_cases hj : j ∈ free
  · simp [hj]
  · simp [hj, indicator]
    intro hjT
    exact absurd (hS (hT hjT)) hj

/-- When we restrict with base = false, the Möbius coefficient at
    S ⊆ free is preserved. -/
theorem BoolFun.restrictTo_moebius_subset (f : BoolFun n) (free : Finset (Fin n))
    (S : Finset (Fin n)) (hS : S ⊆ free) :
    (f.restrictTo free (fun _ => false)).moebius S = f.moebius S := by
  unfold moebius restrictTo
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  congr 1
  rw [embed_indicator_subset free S T hS hT]

/-- Key lemma: if f has degree d ≥ 1, there exists S with |S| = d,
    f.moebius S ≠ 0, and the restriction preserves the coefficient. -/
theorem BoolFun.exists_fullDegree_restriction (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n),
      S.card = f.degree ∧
      f.moebius S ≠ 0 ∧
      (f.restrictTo S (fun _ => false)).moebius S ≠ 0 := by
  obtain ⟨S, hcard, hne⟩ := f.exists_degree_witness hd
  exact ⟨S, hcard, hne, by rwa [f.restrictTo_moebius_subset S S Finset.Subset.rfl]⟩

end Sensitivity
