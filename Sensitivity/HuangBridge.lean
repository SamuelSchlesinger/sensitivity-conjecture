/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs
import Archive.Sensitivity
import Mathlib.Data.Fintype.Pi

/-!
# Bridge to Mathlib's Huang Theorem

Repackages Mathlib's `Sensitivity.huang_degree_theorem` in terms compatible
with our definitions.
-/

namespace Sensitivity

/-- Mathlib's Huang theorem restated with Finsets. -/
theorem huang_finset {m : ℕ} (H : Finset (Fin (m + 1) → Bool))
    (hH : 2 ^ m + 1 ≤ H.card) :
    ∃ q ∈ H, Real.sqrt (↑m + 1) ≤
      ↑(H.filter (fun p => ∃ i, p = flipBit q i)).card := by
  classical
  -- `Archive.Sensitivity` states Huang's theorem over `Set (Q m.succ)`.
  -- We bridge from our `Finset (Fin (m+1) → Bool)` without changing reducibility attributes.
  let HQ : Set (Q m.succ) := {x | (show Fin (m + 1) → Bool from x) ∈ H}
  letI : DecidablePred (fun a : Q m.succ => a ∈ HQ) := Classical.decPred _
  let eEmb : Q m.succ ↪ (Fin (m + 1) → Bool) :=
    ⟨fun x => (show Fin (m + 1) → Bool from x), fun _ _ h => h⟩
  have hmap : HQ.toFinset.map eEmb = H := by
    ext x
    simp [HQ, eEmb]
  have hHQcard : HQ.toFinset.card = H.card := by
    calc
      HQ.toFinset.card = (HQ.toFinset.map eEmb).card := by simp
      _ = H.card := by rw [hmap]
  have hHQ : HQ.toFinset.card ≥ 2 ^ m + 1 := by
    omega
  obtain ⟨q, hqH, hbound⟩ := huang_degree_theorem HQ hHQ
  have hqH' : (show Fin (m + 1) → Bool from q) ∈ H := by
    simpa [HQ] using hqH
  refine ⟨(show Fin (m + 1) → Bool from q), hqH', le_trans hbound ?_⟩
  -- Show Card(↑H ∩ q.adjacent) ≤ ↑(H.filter ...).card
  push_cast [Nat.cast_le]
  apply Finset.card_le_card
  intro p hp
  simp only [Set.mem_toFinset, Set.mem_inter_iff] at hp
  rw [Finset.mem_filter]
  refine ⟨hp.1, ?_⟩
  -- hp.2 : p ∈ Q.adjacent q, i.e., ∃! i, q i ≠ p i
  -- Need: ∃ i, p = flipBit q i
  simp only [Q.adjacent, Set.mem_setOf_eq] at hp
  obtain ⟨i, hne, huniq⟩ := hp.2
  exact ⟨i, funext fun j => by
    by_cases hji : j = i
    · subst hji; simp only [flipBit_apply_same]
      revert hne; cases q j <;> cases p j <;> simp
    · rw [flipBit_apply_ne _ _ hji]
      have := mt (huniq j) hji; push_neg at this; exact this.symm⟩

end Sensitivity
