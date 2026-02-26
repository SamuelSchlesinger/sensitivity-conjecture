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
  -- Step 1: Find d coordinates where the top Möbius coefficient is nonzero.
  -- exists_fullDegree_restriction gives us S with |S| = degree(f),
  -- and the restriction of f to S (fixing other coords to false)
  -- has moebius(S) ≠ 0.
  obtain ⟨S, hcard, _, hmoeb⟩ := f.exists_fullDegree_restriction (by omega)
  -- Now we have:
  --   S : Finset (Fin n)           — the "good" coordinates
  --   hcard : S.card = f.degree    — exactly d of them
  --   hmoeb : (f.restrictTo S (fun _ => false)).moebius S ≠ 0
  -- We abbreviate the restricted function for readability.
  set f' := f.restrictTo S (fun _ => false) with f'_def

  -- Step 2: Reindex to d dimensions.
  -- Since d ≥ 1, write d = m + 1 (needed for huang_finset which wants Fin (m+1)).
  obtain ⟨m, hm⟩ : ∃ m, f.degree = m + 1 := ⟨f.degree - 1, by omega⟩
  -- Build the equivalence e : S ≃ Fin (m+1), since |S| = d = m+1.
  have hcard' : Fintype.card S = Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_coe, Fintype.card_fin]; omega
  let e : S ≃ Fin (m + 1) := Fintype.equivOfCardEq hcard'
  -- toN maps each "new" coordinate i : Fin (m+1) back to its position in Fin n.
  let toN : Fin (m + 1) → Fin n := fun i => (e.symm i).val
  -- Define g : BoolFun (m+1), the reindexed function.
  -- Given y : Fin (m+1) → Bool, we build the n-dim input:
  --   coordinate j gets y(e ⟨j, _⟩) if j ∈ S, else false.
  let g : BoolFun (m + 1) := fun y =>
    f (fun j => if hj : j ∈ S then y (e ⟨j, hj⟩) else false)

  -- Step 3: Show g has full degree (moebius at univ ≠ 0).
  -- Strategy: g.moebius(univ) = f'.moebius(S), which is nonzero by hmoeb.
  -- The equality holds because the two sums are related by a bijection
  -- U ↦ U.map ⟨toN, toN_inj⟩ between subsets of Fin(m+1) and subsets of S.
  have toN_inj : Function.Injective toN :=
    fun i j h => e.symm.injective (Subtype.ext h)
  have hg_moeb : g.moebius Finset.univ ≠ 0 := by
    suffices h : g.moebius Finset.univ = f'.moebius S by rwa [h]
    -- Helper: toN (e ⟨j, hj⟩) = j
    have toN_e : ∀ (j : Fin n) (hj : j ∈ S), toN (e ⟨j, hj⟩) = j :=
      fun j hj => show (e.symm (e ⟨j, hj⟩)).val = j by simp
    unfold BoolFun.moebius
    apply Finset.sum_nbij (fun U => U.map ⟨toN, toN_inj⟩)
    · -- Maps into S.powerset
      intro U _; rw [Finset.mem_powerset]; intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj; exact (e.symm i).property
    · -- Injective
      exact fun _ _ _ _ h => Finset.map_injective ⟨toN, toN_inj⟩ h
    · -- Surjective
      intro T hT
      simp only [Finset.mem_coe, Finset.mem_powerset] at hT
      rw [Set.mem_image]
      refine ⟨T.preimage toN (toN_inj.injOn.mono (Set.subset_univ _)),
              Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.subset_univ _)),
              Finset.ext fun j => ?_⟩
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨i, hi, hij⟩ => hij ▸ hi,
             fun hj => ⟨e ⟨j, hT hj⟩,
               show toN (e ⟨j, hT hj⟩) ∈ T by rw [toN_e]; exact hj,
               toN_e j (hT hj)⟩⟩
    · -- Terms match: (-1)^(|univ|-|U|) * boolToInt(g(ind U))
      --            = (-1)^(|S|-|U.map|) * boolToInt(f'(ind(U.map)))
      intro U _
      congr 1
      · -- Exponents match
        congr 1
        rw [Finset.card_univ, Fintype.card_fin, Finset.card_map]; omega
      · -- boolToInt values match: g(indicator U) = f'(indicator(U.map ...))
        congr 1
        -- Both reduce to f applied to some input; show inputs equal
        change f (fun j => if hj : j ∈ S then indicator U (e ⟨j, hj⟩) else false) =
               f (embed S (fun _ => false) (indicator (U.map ⟨toN, toN_inj⟩)))
        congr 1; funext j; simp only [embed]
        by_cases hj : j ∈ S
        · simp only [hj, dite_true, ite_true, indicator,
                    Finset.mem_map, Function.Embedding.coeFn_mk]
          -- Goal: decide (e ⟨j, hj⟩ ∈ U) = decide (∃ a ∈ U, toN a = j)
          have hiff : (e ⟨j, hj⟩ ∈ U) ↔ (∃ a ∈ U, toN a = j) :=
            ⟨fun h => ⟨e ⟨j, hj⟩, h, toN_e j hj⟩,
             fun ⟨i, hi, hij⟩ => by
               rwa [show i = e ⟨j, hj⟩ from by
                 rw [← Equiv.apply_symm_apply e i]; congr 1
                 exact Subtype.ext hij] at hi⟩
          simp only [hiff]
        · simp only [hj, dite_false, ite_false]
  -- Step 4: Apply imbalance and Huang's theorem.
  obtain ⟨c, _, hH⟩ := fullDegree_imbalance g (Nat.succ_pos m) hg_moeb
  set H := Finset.univ.filter (fun x : Fin (m + 1) → Bool => g.paritySigned x = c)
  -- Simplify the exponent: (m+1)-1 = m, so 2^((m+1)-1) < H.card becomes 2^m < H.card.
  rw [show m + 1 - 1 = m from by omega] at hH
  obtain ⟨q, hqH, hq_bound⟩ := huang_finset H (by omega)
  have hq_par : g.paritySigned q = c := (Finset.mem_filter.mp hqH).2

  -- Step 5: Rewrite √(f.degree) as √(m+1) and reduce to a ℕ inequality.
  rw [show (f.degree : ℝ) = ↑m + 1 from by exact_mod_cast hm]
  apply le_trans hq_bound
  push_cast [Nat.cast_le]
  -- Goal: (H.filter (fun p => ∃ i, p = flipBit q i)).card ≤ f.sensitivity

  -- The n-dimensional embedding of q
  let embedQ : Fin n → Bool := fun j => if hj : j ∈ S then q (e ⟨j, hj⟩) else false

  -- Key helpers for the equivalence between dimensions
  have toN_e : ∀ (j : Fin n) (hj : j ∈ S), toN (e ⟨j, hj⟩) = j :=
    fun j hj => show (e.symm (e ⟨j, hj⟩)).val = j by simp
  have e_toN : ∀ (i : Fin (m + 1)), e ⟨toN i, (e.symm i).property⟩ = i :=
    fun i => show e (e.symm i) = i by simp
  have toN_mem : ∀ (i : Fin (m + 1)), toN i ∈ S := fun i => (e.symm i).property

  -- Flipping bit i in the (m+1)-dim world = flipping bit toN(i) in the n-dim world.
  have g_flip_eq : ∀ i, g (flipBit q i) = f (flipBit embedQ (toN i)) := by
    intro i; show f _ = f _; congr 1; funext j
    by_cases hj : j ∈ S
    · simp only [hj, dite_true]
      by_cases hji : j = toN i
      · -- j = toN i: both sides = !(q i)
        subst hji
        rw [show (e ⟨toN i, hj⟩ : Fin (m + 1)) = i from e_toN i,
            flipBit_apply_same, flipBit_apply_same]
        -- Goal is (!q i) = !embedQ (toN i) as Bool.not.
        -- We avoid `show` here because `!` is ambiguous between Bool.not and Not.
        -- Instead, prove embedQ (toN i) = q i and rewrite.
        have : embedQ (toN i) = q i := by
          change (if h : toN i ∈ S then q (e ⟨toN i, h⟩) else false) = q i
          rw [dif_pos (toN_mem i)]
          congr 1; exact e_toN i
        rw [this]
      · -- j ≠ toN i: both sides = q(e ⟨j, hj⟩)
        have : e ⟨j, hj⟩ ≠ i := fun h => hji (by rw [← toN_e j hj, h])
        rw [flipBit_apply_ne _ _ this, flipBit_apply_ne _ _ hji]
        show q (e ⟨j, hj⟩) = (if h : j ∈ S then q (e ⟨j, h⟩) else false)
        rw [dif_pos hj]
    · -- j ∉ S: both sides = false
      simp only [hj, dite_false]
      have : j ≠ toN i := fun h => hj (h ▸ toN_mem i)
      rw [flipBit_apply_ne _ _ this]
      show false = embedQ j
      show false = (if h : j ∈ S then q (e ⟨j, h⟩) else false)
      rw [dif_neg hj]

  -- If g is sensitive at q in direction i, then f is sensitive at embedQ in direction toN(i).
  have g_to_f : ∀ i, g.sensitiveAt q i → f.sensitiveAt embedQ (toN i) := by
    intro i hi; unfold BoolFun.sensitiveAt at hi ⊢; rwa [← g_flip_eq]

  -- Step 6: Chain the cardinality inequalities.
  calc (H.filter (fun p => ∃ i, p = flipBit q i)).card
      ≤ g.localSensitivity q := by
        -- Each neighbor p = flipBit q i in H has same paritySigned as q,
        -- so g is sensitive at q in direction i.
        unfold BoolFun.localSensitivity
        -- Strategy: the filtered neighbors ⊆ image of sensitive directions under flipBit q,
        -- and |image| ≤ |preimage| by card_image_le.
        have key : H.filter (fun p => ∃ i, p = flipBit q i) ⊆
            (Finset.univ.filter (fun i => g.sensitiveAt q i)).image (flipBit q) := by
          intro p hp
          simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hp ⊢
          obtain ⟨hp_par, i, rfl⟩ := hp
          exact ⟨i, g.sensitiveAt_of_paritySigned_eq q i (hp_par.trans hq_par.symm), rfl⟩
        exact le_trans (Finset.card_le_card key) Finset.card_image_le
    _ ≤ f.localSensitivity embedQ := by
        -- Injection via toN: sensitive dirs of g map to sensitive dirs of f.
        unfold BoolFun.localSensitivity
        apply Finset.card_le_card_of_injOn toN
          (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            g_to_f i (Finset.mem_filter.mp hi).2⟩)
          (fun _ _ _ _ h => toN_inj h)
    _ ≤ f.sensitivity := f.localSensitivity_le_sensitivity embedQ

end Sensitivity
