# Sensitivity Theorem in Lean 4

A formalization of Hao Huang's proof of the Sensitivity Conjecture (2019) in Lean 4,
building on Mathlib's formalization of the graph-theoretic lemma (`Archive/Sensitivity.lean`).

## Statement

For any Boolean function $f : \{0,1\}^n \to \{0,1\}$ with multilinear degree $d \geq 1$:

$$s(f) \geq \sqrt{d}$$

where $s(f)$ is the sensitivity (maximum number of input bits that can be individually
flipped to change the output, over all inputs).

This resolves the 30-year-old Nisan-Szegedy Sensitivity Conjecture, proving that
all major Boolean function complexity measures are polynomially related.

## Module Structure

```
Sensitivity/
  Defs.lean          -- BoolFun, flipBit, sensitivity (0 sorry)
  Basic.lean         -- s(f) ≤ n, complement symmetry (0 sorry)
  Multilinear.lean   -- Mobius coefficients, degree (0 sorry)
  Subcube.lean       -- Subcube restriction, coefficient preservation (0 sorry)
  Parity.lean        -- Parity function, parity-flip, imbalance (2 sorry)
  HuangBridge.lean   -- Bridge to Mathlib's huang_degree_theorem (1 sorry)
  Main.lean          -- THE theorem: s(f) >= sqrt(deg(f)) (1 sorry)
  Consequences.lean  -- Corollary: deg <= s^2 (1 sorry)
```

## Sorry Inventory

| File | Theorem | Description |
|------|---------|-------------|
| Parity.lean | `moebius_parity_sum` | Algebraic identity connecting Mobius coefficients to parity-weighted sums |
| Parity.lean | `fullDegree_imbalance` | Pigeonhole: one parity-sign class has > half the vertices |
| HuangBridge.lean | `huang_finset` | Translation of Mathlib's Set-based Huang theorem to Finset |
| Main.lean | `sensitivity_ge_sqrt_degree` | Assembly of subcube + parity + Huang |
| Consequences.lean | `degree_le_sensitivity_sq` | sqrt bound implies square bound (depends on Main) |

## Proof Strategy

1. **Multilinear representation**: Every Boolean function has unique Mobius coefficients.
   Degree d means some set S with |S|=d has nonzero coefficient.
2. **Subcube restriction**: Fix variables outside S to 0. The restricted function
   preserves the top Mobius coefficient.
3. **Parity imbalance**: Nonzero top coefficient implies the parity-weighted sum is
   nonzero, so one "parity-sign class" has > 2^{d-1} vertices.
4. **Huang's theorem**: Mathlib's `huang_degree_theorem` gives a vertex with >= sqrt(d)
   neighbors in the large class.
5. **Parity flip -> sensitivity**: Each neighbor differs in one bit and the parity flips,
   so the function value must change, giving >= sqrt(d) sensitive coordinates.

## Building

```bash
lake update    # fetch Mathlib
lake build     # build everything
```

## References

- Huang, H. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture."
  *Annals of Mathematics* 190(3), 949-955. 2019.
- Nisan, N. and Szegedy, M. "On the degree of Boolean functions as real polynomials."
  *Computational Complexity* 4, 301-313. 1994.
