# Sensitivity Theorem in Lean 4

This repository formalizes the sensitivity lower bound for Boolean functions in Lean 4,
building on Mathlib's formalization of Huang's hypercube lemma in
`Archive/Sensitivity.lean`.

## Main Result

For any Boolean function `f : {0,1}^n -> {0,1}` with multilinear degree `d >= 1`,

`sqrt(d) <= s(f)`

where `s(f)` is the sensitivity of `f`.

In Lean:

- `Sensitivity.sensitivity_ge_sqrt_degree`
- `Sensitivity.degree_le_sensitivity_sq`

The current codebase is proof-complete (no `sorry`).

## File Layout

```text
Sensitivity/
  Defs.lean          -- Boolean functions, bit flips, sensitivity
  Basic.lean         -- Basic sensitivity lemmas and symmetries
  Multilinear.lean   -- Mobius coefficients and degree
  Subcube.lean       -- Restriction to subcubes and coefficient preservation
  Parity.lean        -- Parity identities and imbalance lemma
  HuangBridge.lean   -- Finset bridge to Mathlib's huang_degree_theorem
  Main.lean          -- The sensitivity lower bound sqrt(deg) <= s
  Consequences.lean  -- Corollary deg <= s^2
```

## Proof Outline

1. Use a nonzero top Möbius coefficient as a degree witness.
2. Restrict to a subcube that preserves this coefficient.
3. Derive a parity-sign imbalance on the restricted cube.
4. Apply Mathlib's Huang theorem to obtain many same-class neighbors.
5. Convert these neighbors into sensitive coordinates and lift back to `f`.

## Build

```bash
lake update
lake build
```

## References

- Hao Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture*, Annals of Mathematics 190(3), 949-955, 2019.
- Noam Nisan and Mario Szegedy, *On the degree of Boolean functions as real polynomials*, Computational Complexity 4, 301-313, 1994.
