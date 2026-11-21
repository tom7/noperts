module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Stieltjes Matrix Decomposition

A real `n × n` *Stieltjes matrix* is a symmetric positive definite matrix `G` with all
off-diagonal entries `G i j ≤ 0` (`i ≠ j`).

Main results (`Fin n`, with `Fin 3` corollaries):
* `stieltjes_inv_nonneg`: every entry of `G⁻¹` is `≥ 0`.
* `stieltjes_inv_mulVec_ones_pos`: `d := G⁻¹ *ᵥ 1` has strictly positive entries.
* `stieltjes_decomp`: with `ξ k := 1 / d k`, `μ k := ξ k > 0`, and
  `lam i j := -G i j / (ξ i * ξ j) ≥ 0`,
  `G = ∑ k, μ k • e_k e_kᵀ + ∑ i < j, lam i j • (ξ i e_i - ξ j e_j)(ξ i e_i - ξ j e_j)ᵀ`.
* `posDef_of_stieltjes_sum`: converse — any such sum with `μ > 0`, `ξ > 0`, `lam ≥ 0` is
  symmetric positive definite with nonpositive off-diagonals.
-/

namespace Minimality.Stieltjes

open Matrix Finset

/-- If `G` is a Stieltjes matrix and `G *ᵥ x ≥ 0` entrywise, then `x ≥ 0` entrywise. -/
private theorem stieltjes_nonneg_of_mulVec_nonneg {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hoff : ∀ i j : Fin n, i ≠ j → G i j ≤ 0)
    {x : Fin n → ℝ} (hx : ∀ i : Fin n, 0 ≤ (G *ᵥ x) i) :
    ∀ i : Fin n, 0 ≤ x i := by
  let xp : Fin n → ℝ := fun i => max (x i) 0
  let xm : Fin n → ℝ := fun i => max (-x i) 0
  have hxp_nonneg : ∀ i, 0 ≤ xp i := fun i => le_max_right _ _
  have hxm_nonneg : ∀ i, 0 ≤ xm i := fun i => le_max_right _ _
  have hx_split : x = xp - xm := by
    ext i
    simp only [Pi.sub_apply, xp, xm]
    rcases le_total 0 (x i) with hi | hi
    · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
    · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), zero_sub, neg_neg]
  by_contra hneg
  push Not at hneg
  have hxm_ne : xm ≠ 0 := by
    rcases hneg with ⟨i, hi⟩
    intro h0
    have hxm0 : xm i = 0 := congr_fun h0 i
    have : 0 < xm i := lt_of_lt_of_le (neg_pos.mpr hi) (le_max_left _ _)
    linarith
  have hpos : 0 < xm ⬝ᵥ (G *ᵥ xm) := by
    simpa [star_trivial] using hG.dotProduct_mulVec_pos hxm_ne
  have hmul_nonneg : 0 ≤ xm ⬝ᵥ (G *ᵥ x) := by
    refine Finset.sum_nonneg fun i _ => mul_nonneg (hxm_nonneg i) (hx i)
  have hcross_nonpos : xm ⬝ᵥ (G *ᵥ xp) ≤ 0 := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    rcases eq_or_ne i j with rfl | hij
    · have h0 : xm i * xp i = 0 := by
        rcases le_total 0 (x i) with hi | hi
        · simp [xm, max_eq_right (neg_nonpos.mpr hi)]
        · simp [xp, max_eq_right hi]
      have hterm : xm i * (G i i * xp i) = (xm i * xp i) * G i i := by ring
      rw [hterm, h0, zero_mul]
    · have h1 : xm i * (G i j * xp j) = (xm i * xp j) * G i j := by ring
      rw [h1]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (hxm_nonneg i) (hxp_nonneg j)) (hoff i j hij)
  have hrel : xm ⬝ᵥ (G *ᵥ x) = xm ⬝ᵥ (G *ᵥ xp) - xm ⬝ᵥ (G *ᵥ xm) := by
    rw [hx_split, mulVec_sub, dotProduct_sub]
  linarith

/-- **(a1) Inverse nonnegativity of a Stieltjes matrix (`n × n`).**
If `G : Matrix (Fin n) (Fin n) ℝ` is symmetric positive definite (`G.PosDef`) with all
off-diagonal entries `≤ 0`, then every entry of `G⁻¹` is `≥ 0`. -/
theorem stieltjes_inv_nonneg {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hoff : ∀ i j : Fin n, i ≠ j → G i j ≤ 0) :
    ∀ i j : Fin n, 0 ≤ G⁻¹ i j := by
  intro i j
  let ej : Fin n → ℝ := Pi.single j 1
  have hmul : G *ᵥ (G⁻¹ *ᵥ ej) = ej := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv G hG.det_pos.ne'.isUnit, one_mulVec]
  have hej : ∀ k : Fin n, 0 ≤ (G *ᵥ (G⁻¹ *ᵥ ej)) k := by
    intro k
    rw [hmul]
    by_cases hk : k = j
    · subst hk; simp [ej]
    · simp [ej, hk]
  have hx := stieltjes_nonneg_of_mulVec_nonneg G hG hoff hej i
  simpa [ej, mulVec_single] using hx

/-- **(a2) Strict positivity of `d = G⁻¹ 1` for a Stieltjes matrix (`n × n`).**
If `G` is a Stieltjes matrix, then `d := G⁻¹ *ᵥ 1` has strictly positive entries. -/
theorem stieltjes_inv_mulVec_ones_pos {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hoff : ∀ i j : Fin n, i ≠ j → G i j ≤ 0) :
    ∀ i : Fin n, 0 < (G⁻¹ *ᵥ fun _ => (1 : ℝ)) i := by
  let d : Fin n → ℝ := G⁻¹ *ᵥ fun _ => 1
  have hmul : G *ᵥ d = fun _ => 1 := by
    dsimp [d]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv G hG.det_pos.ne'.isUnit, one_mulVec]
  have hd_nonneg : ∀ j : Fin n, 0 ≤ d j := by
    intro j
    exact stieltjes_nonneg_of_mulVec_nonneg G hG hoff (fun k => by rw [hmul]; norm_num) j
  intro i
  have hrow : (∑ j : Fin n, G i j * d j) = 1 := by
    have := congr_fun hmul i
    simpa [mulVec, dotProduct] using this
  have hoff_sum : (∑ j ∈ univ.erase i, G i j * d j) ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    exact mul_nonpos_of_nonpos_of_nonneg (hoff i j (Finset.ne_of_mem_erase hj).symm) (hd_nonneg j)
  have hsplit : G i i * d i + ∑ j ∈ univ.erase i, G i j * d j = 1 := by
    have hs := Finset.add_sum_erase univ (fun j => G i j * d j) (mem_univ i)
    linarith [hs, hrow]
  have hprod_pos : 0 < G i i * d i := by linarith
  have hii_pos : 0 < G i i := by
    have hpos_i : 0 < (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ (G *ᵥ Pi.single i 1) := by
      have hne : (Pi.single i (1 : ℝ) : Fin n → ℝ) ≠ 0 := by
        intro h0
        have := congr_fun h0 i
        simp at this
      simpa [star_trivial] using hG.dotProduct_mulVec_pos hne
    simpa [dotProduct, mulVec_single, Pi.single_apply] using hpos_i
  exact pos_of_mul_pos_right hprod_pos hii_pos.le

/-- Entry of `vecMulVec (a • e_i - b • e_j) (a • e_i - b • e_j)` at `(r, c)`. -/
private theorem vecMulVec_pair_apply {n : ℕ} (a b : ℝ) (i j r c : Fin n) :
    vecMulVec (a • Pi.single i (1 : ℝ) - b • Pi.single j (1 : ℝ))
              (a • Pi.single i (1 : ℝ) - b • Pi.single j (1 : ℝ)) r c =
      ((if r = i then a else 0) - (if r = j then b else 0)) *
      ((if c = i then a else 0) - (if c = j then b else 0)) := by
  simp [vecMulVec, Pi.single_apply, mul_ite, mul_zero, mul_one]

/-- **(b1) Canonical Stieltjes rank-1 decomposition (`n × n`).**
For a Stieltjes matrix `G : Matrix (Fin n) (Fin n) ℝ`, with `d := G⁻¹ *ᵥ 1`, `ξ k := 1 / d k`,
`μ k := ξ k`, and `lam i j := -G i j / (ξ i * ξ j)`, we have `d k > 0`, `μ k > 0`,
`lam i j ≥ 0` for `i < j`, and
`G = ∑ k, μ k • e_k e_kᵀ + ∑ i < j, lam i j • (ξ i e_i - ξ j e_j)(ξ i e_i - ξ j e_j)ᵀ`. -/
theorem stieltjes_decomp {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hoff : ∀ i j : Fin n, i ≠ j → G i j ≤ 0) :
    let d : Fin n → ℝ := G⁻¹ *ᵥ fun _ => 1
    let ξ : Fin n → ℝ := fun k => 1 / d k
    let μ : Fin n → ℝ := ξ
    let lam : Fin n → Fin n → ℝ := fun i j => -G i j / (ξ i * ξ j)
    (∀ k, 0 < d k) ∧ (∀ k, 0 < μ k) ∧ (∀ i j, i < j → 0 ≤ lam i j) ∧
    G = (∑ k : Fin n, μ k • vecMulVec (Pi.single k 1) (Pi.single k 1)) +
        ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j),
          lam i j • vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                              (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) := by
  intro d ξ μ lam
  have hd_pos : ∀ k, 0 < d k := stieltjes_inv_mulVec_ones_pos G hG hoff
  have hξ_pos : ∀ k, 0 < ξ k := fun k => one_div_pos.mpr (hd_pos k)
  have hlam_nonneg : ∀ i j, i < j → 0 ≤ lam i j := by
    intro i j hij
    have hGij : G i j ≤ 0 := hoff i j hij.ne
    exact div_nonneg (neg_nonneg.mpr hGij) (mul_pos (hξ_pos i) (hξ_pos j)).le
  refine ⟨hd_pos, hξ_pos, hlam_nonneg, ?_⟩
  have hsym : ∀ r c : Fin n, G r c = G c r := fun r c => by
    have := congr_fun (congr_fun hG.isHermitian.eq r) c
    simpa using this.symm
  have hGd : ∀ r : Fin n, (∑ c : Fin n, G r c * d c) = 1 := by
    have hmul : G *ᵥ d = fun _ => 1 := by
      dsimp [d]
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv G hG.det_pos.ne'.isUnit, one_mulVec]
    intro r
    simpa [mulVec, dotProduct] using congr_fun hmul r
  ext r c
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hdiag_sum :
      (∑ k : Fin n, μ k * vecMulVec (Pi.single k (1 : ℝ)) (Pi.single k 1) r c) =
        if r = c then ξ r else 0 := by
    have hterm : ∀ k : Fin n,
        μ k * vecMulVec (Pi.single k (1 : ℝ)) (Pi.single k 1) r c =
          if k = r then (if r = c then ξ r else 0) else 0 := by
      intro k
      by_cases hkr : k = r <;> by_cases hrc : r = c
      · subst hkr hrc; simp [vecMulVec_apply, μ]
      · subst hkr; simp [vecMulVec_apply, hrc, Ne.symm hrc]
      · subst hrc; simp [vecMulVec_apply, hkr, Ne.symm hkr]
      · simp [vecMulVec_apply, Pi.single_apply, hkr]
    simp_rw [hterm, Finset.sum_ite_eq', mem_univ, ite_true]
  rw [hdiag_sum]
  rcases lt_trichotomy r c with hrc | rfl | hcr
  · -- Case `r < c`: only `(i, j) = (r, c)` contributes `-lam r c * ξ r * ξ c = G r c`.
    simp only [hrc.ne, ite_false, zero_add]
    have hinner : ∀ i : Fin n,
        (∑ j ∈ univ.filter (fun j : Fin n => i < j),
          lam i j * vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                              (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) r c) =
          if i = r then G r c else 0 := by
      intro i
      by_cases hir : i = r
      · subst hir
        simp only [ite_true]
        have hterm : ∀ j ∈ univ.filter (fun j : Fin n => i < j),
            lam i j * vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                                (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) i c =
              if j = c then G i c else 0 := by
          intro j hj
          have hij : i < j := (Finset.mem_filter.mp hj).2
          rw [vecMulVec_pair_apply]
          by_cases hjc : j = c
          · subst hjc
            simp only [ite_true, hij.ne, hij.ne.symm, ite_false, sub_zero, zero_sub]
            have hξi : ξ i ≠ 0 := (hξ_pos i).ne'
            have hξj : ξ j ≠ 0 := (hξ_pos j).ne'
            dsimp [lam]
            field_simp [hξi, hξj]
          · simp [hij.ne, hrc.ne.symm, hjc, Ne.symm hjc]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
        simp [hrc]
      · simp only [hir, ite_false]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hij : i < j := (Finset.mem_filter.mp hj).2
        rw [vecMulVec_pair_apply]
        have h1 : r ≠ i := Ne.symm hir
        by_cases hrj : r = j
        · subst hrj
          by_cases hcj : c = r
          · exact absurd hcj.symm hrc.ne
          · by_cases hci : c = i
            · exact absurd (lt_of_eq_of_lt hci hij) (lt_asymm hrc)
            · simp [hij.ne.symm, hci, hcj]
        · simp [h1, hrj]
    simp_rw [hinner, Finset.sum_ite_eq', mem_univ, ite_true]
  · -- Case `r = c` (diagonal):
    simp only [ite_true]
    have hdiag_pair : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j : Fin n => i < j),
        lam i j * vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                            (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) r r =
          if i = r then -G r j * d j / d r
          else if j = r then -G r i * d i / d r
          else 0 := by
      intro i j hj
      have hij : i < j := (Finset.mem_filter.mp hj).2
      rw [vecMulVec_pair_apply]
      by_cases hir : i = r
      · subst hir
        simp only [ite_true, hij.ne, hij.ne.symm, ite_false, sub_zero]
        have hd_i : d i ≠ 0 := (hd_pos i).ne'
        have hd_j : d j ≠ 0 := (hd_pos j).ne'
        dsimp [lam, ξ]
        field_simp [hd_i, hd_j]
      · simp only [hir, ite_false]
        by_cases hjr : j = r
        · subst hjr
          simp only [ite_true, hij.ne.symm, ite_false, zero_sub]
          have hd_i : d i ≠ 0 := (hd_pos i).ne'
          have hd_j : d j ≠ 0 := (hd_pos j).ne'
          dsimp [lam, ξ]
          rw [hsym i j]
          field_simp [hd_i, hd_j]
        · simp only [hjr, ite_false]
          simp [Ne.symm hir, Ne.symm hjr]
    -- Rewrite the double sum over `i < j` into `∑ j ≠ r, -G r j * d j / d r`:
    have hsum_pair :
        (∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j),
          lam i j * vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                              (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) r r) =
          ∑ k ∈ univ.erase r, -G r k * d k / d r := by
      have h1 : ∀ i : Fin n,
          (∑ j ∈ univ.filter (fun j : Fin n => i < j),
            lam i j * vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                                (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) r r) =
            (if i = r then ∑ j ∈ univ.filter (fun j : Fin n => r < j), -G r j * d j / d r
             else if i < r then -G r i * d i / d r else 0) := by
        intro i
        rw [Finset.sum_congr rfl (hdiag_pair i)]
        by_cases hir : i = r
        · subst hir; simp
        · simp only [hir, ite_false, Finset.sum_ite_eq', Finset.mem_filter, mem_univ, true_and]
      simp_rw [h1]
      have hsplit_sum :
          (∑ i : Fin n,
            if i = r then ∑ j ∈ univ.filter (fun j : Fin n => r < j), -G r j * d j / d r
            else if i < r then -G r i * d i / d r else 0) =
            (∑ j ∈ univ.filter (fun j : Fin n => r < j), -G r j * d j / d r) +
            (∑ i ∈ univ.filter (fun i : Fin n => i < r), -G r i * d i / d r) := by
        rw [Finset.sum_ite, Finset.sum_ite]
        simp only [Finset.filter_eq', mem_univ, ite_true, Finset.sum_singleton, Finset.sum_const_zero, add_zero]
        congr 1
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext x
        simp only [Finset.mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
        exact fun h => ne_of_lt h
      rw [hsplit_sum, ← Finset.sum_union]
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext k
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_comm]
        constructor
        · rintro (hk | hk)
          · exact ⟨ne_of_lt hk, trivial⟩
          · exact ⟨ne_of_gt hk, trivial⟩
        · intro hk
          exact lt_or_gt_of_ne hk.1
      · rw [Finset.disjoint_left]
        intro k hk1 hk2
        simp only [Finset.mem_filter, mem_univ, true_and] at hk1 hk2
        exact absurd (lt_trans hk1 hk2) (lt_irrefl _)
    rw [hsum_pair]
    have hGd_r : G r r * d r + ∑ k ∈ univ.erase r, G r k * d k = 1 := by
      have hs := Finset.add_sum_erase univ (fun k => G r k * d k) (mem_univ r)
      linarith [hs, hGd r]
    have hsum_neg : (∑ k ∈ univ.erase r, -G r k * d k / d r) =
        -(∑ k ∈ univ.erase r, G r k * d k) / d r := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine congr_arg₂ (· * ·) (Finset.sum_congr rfl fun k _ => by ring) rfl
    rw [hsum_neg]
    have hdr : d r ≠ 0 := (hd_pos r).ne'
    dsimp [ξ]
    field_simp [hdr]
    linarith
  · -- Case `c < r`: symmetric to `r < c`, using `G r c = G c r`.
    simp only [hcr.ne', ite_false, zero_add]
    have hinner : ∀ i : Fin n,
        (∑ j ∈ univ.filter (fun j : Fin n => i < j),
          lam i j * vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                              (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) r c) =
          if i = c then G r c else 0 := by
      intro i
      by_cases hic : i = c
      · subst hic
        simp only [ite_true]
        have hterm : ∀ j ∈ univ.filter (fun j : Fin n => i < j),
            lam i j * vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                                (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) r i =
              if j = r then G r i else 0 := by
          intro j hj
          have hij : i < j := (Finset.mem_filter.mp hj).2
          rw [vecMulVec_pair_apply]
          by_cases hjr : j = r
          · subst hjr
            simp only [ite_true, hij.ne, hij.ne.symm, ite_false, sub_zero, zero_sub]
            have hξi : ξ i ≠ 0 := (hξ_pos i).ne'
            have hξj : ξ j ≠ 0 := (hξ_pos j).ne'
            dsimp [lam]
            rw [hsym j i]
            field_simp [hξi, hξj]
          · simp [hij.ne, hcr.ne', hjr, Ne.symm hjr]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
        simp [hcr]
      · simp only [hic, ite_false]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hij : i < j := (Finset.mem_filter.mp hj).2
        rw [vecMulVec_pair_apply]
        have h1 : c ≠ i := Ne.symm hic
        by_cases hcj : c = j
        · subst hcj
          by_cases hri : r = i
          · exact absurd (lt_of_eq_of_lt hri hij) (lt_asymm hcr)
          · by_cases hrc : r = c
            · exact absurd hrc hcr.ne'
            · simp [h1, hri, hrc]
        · simp [h1, hcj]
    simp_rw [hinner, Finset.sum_ite_eq', mem_univ, ite_true]

/-- **(b2) Converse (`n × n`).**
Any sum `∑ k, μ k e_k e_kᵀ + ∑ i < j, lam i j (ξ i e_i - ξ j e_j)(ξ i e_i - ξ j e_j)ᵀ`
with `μ > 0`, `ξ > 0`, and `lam i j ≥ 0` (`i < j`) is symmetric positive definite with
nonpositive off-diagonal entries. -/
theorem posDef_of_stieltjes_sum {n : ℕ}
    (μ ξ : Fin n → ℝ) (lam : Fin n → Fin n → ℝ)
    (hμ : ∀ k, 0 < μ k) (hξ : ∀ k, 0 < ξ k) (hlam : ∀ i j, i < j → 0 ≤ lam i j) :
    let M : Matrix (Fin n) (Fin n) ℝ :=
      (∑ k : Fin n, μ k • vecMulVec (Pi.single k 1) (Pi.single k 1)) +
      ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j),
        lam i j • vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                            (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
    M.PosDef ∧ ∀ i j : Fin n, i ≠ j → M i j ≤ 0 := by
  intro M
  have hsym : M.IsHermitian := by
    ext r c
    simp only [M, Matrix.conjTranspose_apply, star_trivial, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    refine congr_arg₂ (· + ·)
      (Finset.sum_congr rfl fun k _ => by ring)
      (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  have hpd : M.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hsym ?_
    intro x hx
    have hdot_vv : ∀ v : Fin n → ℝ, x ⬝ᵥ (vecMulVec v v *ᵥ x) = (v ⬝ᵥ x) ^ 2 := by
      intro v
      calc x ⬝ᵥ (vecMulVec v v *ᵥ x)
          = ∑ r : Fin n, ∑ c : Fin n, x r * (v r * v c * x c) := by
              simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum]
        _ = ∑ r : Fin n, (v r * x r) * (∑ c : Fin n, v c * x c) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun c _ => by ring
        _ = (∑ r : Fin n, v r * x r) * (∑ c : Fin n, v c * x c) := by rw [← Finset.sum_mul]
        _ = (v ⬝ᵥ x) ^ 2 := by simp [dotProduct, sq]
    have hquad : star x ⬝ᵥ (M *ᵥ x) =
        (∑ k : Fin n, μ k * (x k) ^ 2) +
        ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j),
          lam i j * (ξ i * x i - ξ j * x j) ^ 2 := by
      simp only [M, star_trivial, add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum,
        smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [hdot_vv]
        simp [dotProduct, Pi.single_apply]
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hdot_vv]
        have hs : ((ξ i • Pi.single i (1 : ℝ) - ξ j • Pi.single j (1 : ℝ)) ⬝ᵥ x) =
            ξ i * x i - ξ j * x j := by
          rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
          simp [dotProduct, Pi.single_apply]
        rw [hs]
    rw [hquad]
    have hx_ne : ∃ k : Fin n, x k ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    rcases hx_ne with ⟨k₀, hk₀⟩
    have h1 : 0 < ∑ k : Fin n, μ k * (x k) ^ 2 := by
      refine Finset.sum_pos' (fun k _ => mul_nonneg (hμ k).le (sq_nonneg _)) ?_
      exact ⟨k₀, mem_univ k₀, mul_pos (hμ k₀) (sq_pos_of_ne_zero hk₀)⟩
    have h2 : 0 ≤ ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j),
        lam i j * (ξ i * x i - ξ j * x j) ^ 2 := by
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj => ?_
      exact mul_nonneg (hlam i j (Finset.mem_filter.mp hj).2) (sq_nonneg _)
    linarith
  refine ⟨hpd, ?_⟩
  intro r c hrc
  simp only [M, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hdiag0 : (∑ k : Fin n, μ k * vecMulVec (Pi.single k (1 : ℝ)) (Pi.single k 1) r c) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkr : k = r
    · subst hkr; simp [vecMulVec, Pi.single_apply, hrc.symm]
    · simp [vecMulVec, Pi.single_apply, Ne.symm hkr]
  rw [hdiag0, zero_add]
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have hlam_ij : 0 ≤ lam i j := hlam i j hij
  rw [vecMulVec_pair_apply]
  have hprod_nonpos :
      ((if r = i then ξ i else 0) - (if r = j then ξ j else 0)) *
      ((if c = i then ξ i else 0) - (if c = j then ξ j else 0)) ≤ 0 := by
    by_cases hri : r = i
    · subst hri
      by_cases hci : c = r
      · exact absurd hci.symm hrc
      · by_cases hcj : c = j <;> simp [hij.ne, hij.ne.symm, hci, hcj]
        exact mul_nonneg (hξ r).le (hξ j).le
    · by_cases hrj : r = j
      · subst hrj
        by_cases hcj : c = r
        · exact absurd hcj.symm hrc
        · by_cases hci : c = i <;> simp [hij.ne, hij.ne.symm, hci, hcj]
          exact mul_nonneg (hξ r).le (hξ i).le
      · simp [hri, hrj]
  exact mul_nonpos_of_nonneg_of_nonpos hlam_ij hprod_nonpos

/-- **3×3 corollary (forward): Stieltjes decomposition on `Fin 3`.** -/
theorem stieltjes_decomp_fin3 (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : G.PosDef) (hoff : ∀ i j : Fin 3, i ≠ j → G i j ≤ 0) :
    let d : Fin 3 → ℝ := G⁻¹ *ᵥ fun _ => 1
    let ξ : Fin 3 → ℝ := fun k => 1 / d k
    let μ : Fin 3 → ℝ := ξ
    let lam : Fin 3 → Fin 3 → ℝ := fun i j => -G i j / (ξ i * ξ j)
    (∀ i j : Fin 3, 0 ≤ G⁻¹ i j) ∧
    (∀ k, 0 < d k) ∧ (∀ k, 0 < μ k) ∧ (∀ i j, i < j → 0 ≤ lam i j) ∧
    G = (∑ k : Fin 3, μ k • vecMulVec (Pi.single k 1) (Pi.single k 1)) +
        ∑ i : Fin 3, ∑ j ∈ univ.filter (fun j : Fin 3 => i < j),
          lam i j • vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                              (ξ i • Pi.single i 1 - ξ j • Pi.single j 1) :=
  ⟨stieltjes_inv_nonneg G hG hoff, stieltjes_decomp G hG hoff⟩

/-- **3×3 corollary (converse): Stieltjes sum is SPD with nonpositive off-diagonals on `Fin 3`.** -/
theorem posDef_of_stieltjes_sum_fin3
    (μ ξ : Fin 3 → ℝ) (lam : Fin 3 → Fin 3 → ℝ)
    (hμ : ∀ k, 0 < μ k) (hξ : ∀ k, 0 < ξ k) (hlam : ∀ i j, i < j → 0 ≤ lam i j) :
    let M : Matrix (Fin 3) (Fin 3) ℝ :=
      (∑ k : Fin 3, μ k • vecMulVec (Pi.single k 1) (Pi.single k 1)) +
      ∑ i : Fin 3, ∑ j ∈ univ.filter (fun j : Fin 3 => i < j),
        lam i j • vecMulVec (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
                            (ξ i • Pi.single i 1 - ξ j • Pi.single j 1)
    M.PosDef ∧ ∀ i j : Fin 3, i ≠ j → M i j ≤ 0 :=
  posDef_of_stieltjes_sum μ ξ lam hμ hξ hlam

end Minimality.Stieltjes
