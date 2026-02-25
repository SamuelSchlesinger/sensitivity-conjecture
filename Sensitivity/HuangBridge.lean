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

Mathlib's theorem:
```
huang_degree_theorem {m : ℕ} (H : Set (Q m.succ))
  (hH : H.toFinset.card ≥ 2 ^ m + 1) :
  ∃ q ∈ H, √(m + 1) ≤ (H ∩ q.adjacent).toFinset.card
```

Where `Q n = Fin n → Bool` and `q.adjacent = {p | ∃! i, q i ≠ p i}`.
-/

namespace Sensitivity

/-- Mathlib's Huang theorem restated with Finsets.

    If H ⊆ Q(m+1) with |H| ≥ 2^m + 1, then some q ∈ H has at least
    √(m+1) neighbors in H (where neighbors differ in exactly one bit). -/
theorem huang_finset {m : ℕ} (H : Finset (Fin (m + 1) → Bool))
    (hH : 2 ^ m + 1 ≤ H.card) :
    ∃ q ∈ H, Real.sqrt (↑m + 1) ≤
      ↑(H.filter (fun p => ∃ i, p = flipBit q i)).card := by
  sorry

end Sensitivity
