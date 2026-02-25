/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs
import Sensitivity.Basic
import Sensitivity.Multilinear
import Sensitivity.Main

/-!
# Consequences of the Sensitivity Theorem

## Main results

- `degree_le_sensitivity_sq` — the degree is at most the square of sensitivity
-/

namespace Sensitivity

/-- The degree is at most the square of the sensitivity.
    Immediate corollary of the sensitivity theorem s(f) ≥ √deg(f):
    √d ≤ s implies d ≤ s². -/
theorem degree_le_sensitivity_sq {n : ℕ} (f : BoolFun n) :
    f.degree ≤ f.sensitivity ^ 2 := by
  by_cases hd : f.degree = 0
  · simp [hd]
  · have hd' : 1 ≤ f.degree := by omega
    have hsqrt := sensitivity_ge_sqrt_degree f hd'
    -- From √d ≤ s (as reals), squaring both sides: d ≤ s²
    -- Since d and s are naturals, this gives the result.
    -- From √d ≤ s we get d ≤ s²
    have hsq : (f.degree : ℝ) ≤ (f.sensitivity : ℝ) ^ 2 := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) f.degree),
                 Real.sqrt_nonneg (↑f.degree : ℝ)]
    exact_mod_cast hsq

end Sensitivity
