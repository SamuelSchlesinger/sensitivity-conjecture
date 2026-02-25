/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sensitivity.Defs
import Sensitivity.Multilinear
import Sensitivity.Subcube
import Sensitivity.Parity
import Sensitivity.HuangBridge

/-!
# The Sensitivity Theorem

**Main result**: For any Boolean function f of degree d ≥ 1,
the sensitivity satisfies s(f) ≥ √d.

This was conjectured by Nisan and Szegedy (1992) and proved by Hao Huang (2019).

## Proof outline

1. Find a d-dimensional subcube where f restricted has full degree d
   (the top Möbius coefficient c_S is nonzero, with |S| = d).
2. On this subcube, parity imbalance: the set
   `H = {x : paritySigned(x) = c}` for some c ∈ {-1, 1} has |H| > 2^{d-1}.
3. Apply Huang's theorem: some q ∈ H has ≥ √d neighbors in H.
4. Each neighbor y of q in H satisfies paritySigned(y) = paritySigned(q),
   and since y = flipBit q i, this implies f is sensitive at q in direction i.
   Each neighbor contributes a distinct sensitive coordinate.
5. Sensitivity on the subcube ≤ sensitivity of f, concluding s(f) ≥ √d.
-/

namespace Sensitivity

/-- **Sensitivity Theorem** (Huang 2019).
    For any Boolean function f of degree d ≥ 1,
    the sensitivity satisfies s(f) ≥ ⌈√d⌉, i.e., √d ≤ s(f) as reals. -/
theorem sensitivity_ge_sqrt_degree {n : ℕ} (f : BoolFun n) (hd : 1 ≤ f.degree) :
    Real.sqrt (f.degree : ℝ) ≤ (f.sensitivity : ℝ) := by
  sorry

end Sensitivity
