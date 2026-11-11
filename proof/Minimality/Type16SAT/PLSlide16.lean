module

public import Minimality.Type29KSAT.CaseBSlide
public import Minimality.Type16SAT.FinalA16
public import Minimality.Type16SAT.FinalZS16

@[expose] public section

/-!
# Type 16 on the stratum `PL`: the Slide Lemma leaf

`PL` is the part of the stratum `Z = {g = d = q = 1}` of the type 16 normal form (the quad `1356` a
parallelogram with `x 1 - x 3 = (x 5 - x 3) + (x 6 - x 3)`, `x 4` on the plane `y = 1` of `145`)
where the edge `x 1 - x 6` is orthogonal to `x 0 - x 3` and `x 0 - x 6`: then `E₂ = x 5 - x 3` is
orthogonal to `E₁ = x 0 - x 3` and `E₃ = x 6 - x 3`, the facets `D = 036` and `F = 145` are
parallel, and the quad `B = 1356` is a rectangle orthogonal to both.  With `c = ⟪E₁, E₃⟫`, `ℓ = ⟪E₃, E₃⟫`, the
coordinate along the edge `15` of the deep vertices `0, 2, 4` (`X = ⟪· - x 1, x 5 - x 1⟫`) is
`ℓ - c`, `ℓ - a c`, `(1 - r) ℓ - p c`, and `ℓ - X` is `c`, `a c`, `p c + r ℓ`.  So if `c ≤ 0` and
`r < 1` all deep vertices lie beyond the plane through `x 1` orthogonal to `15`, and if `0 < c` all
lie before the plane through `x 5`: the slab hypothesis of the Slide Lemma holds at one end, and
the (K) condition holds at one of the two walls by `kdich`.

* `NF16.pl_data`: the coordinate tables on `PL`.
* `NF16.isRupert_PL_slide_le`: a normal form on `PL` with `r ≤ 1` and (`r < 1` or `c ≠ 0`) is Rupert (no other
  hypothesis; `a, p, r > 0` and `b < 1` come from the normal form); at `r = 1` the residue of the wall is `c = 0`.
  Only the coordinate `X_4 = (1 - r) ℓ - p c` of the case `c ≤ 0` needs `r < 1`; at `r = 1` it is `-p c > 0` for `c < 0`.
* `NF16.isRupert_PL_slide`: the case `r < 1`.
* `NF16.zshape_nf`, `NF16.r_lt_one`: `ZShape16` gives `g = d = q = 1`; `C [0134] < 0` gives `r < 1`.
* `H16.SAT.isRupert_PL16`, `isRupert_PL16_sigma`: the leaf for a type 16 shape (and its `sigma16`
  image) with `C [0134] < 0` (resp. `C [2346] < 0`), both inner products zero and `ZShape16`.  This
  covers every class with that sign, in particular `+---` and `+-+-`.
* `H16.SAT.isRupert_cls16M_resid`: the class `+---` (or `----`) outside `Cls16A` and `Cls16Z`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.NF16

variable {x : Fin 7 → ℝ³}

/-- **`PL` coordinates.**  On `g = d = q = 1` with
`⟪x 0 - x 3, x 1 - x 6⟫ = ⟪x 0 - x 6, x 1 - x 6⟫ = 0`:
`E₂ ⟂ E₁, E₃`; with `ℓ = ⟪E₃, E₃⟫`, `h = ⟪E₂, E₂⟫`, `c = ⟪E₁, E₃⟫` and the normal
`W = ℓ E₁ - c E₃` of the rectangle `1356` (`ω = ⟪E₁, W⟫ > 0`), the tables of `⟪x i - x 1, E₃⟫`,
`⟪x i - x 1, E₂⟫`, `⟪x i - x 1, W⟫`. -/
theorem pl_data (N : NF16 x) (hg : N.g = 1) (hd : N.d = 1) (hq : N.q = 1)
    (h1 : ⟪x 0 - x 3, x 1 - x 6⟫ = 0) (h2 : ⟪x 0 - x 6, x 1 - x 6⟫ = 0) :
    ∃ (ℓ h c ω : ℝ) (W : ℝ³), 0 < ℓ ∧ 0 < h ∧ 0 < ω ∧ W ≠ 0 ∧ N.E₂ ≠ 0 ∧ N.E₃ ≠ 0 ∧
      ⟪N.E₃, N.E₃⟫ = ℓ ∧ ⟪N.E₂, N.E₂⟫ = h ∧ ⟪N.E₂, N.E₃⟫ = 0 ∧ ⟪N.E₂, W⟫ = 0 ∧ ⟪N.E₃, W⟫ = 0 ∧
      (∀ i, ⟪x i - x 1, N.E₃⟫ =
        ![c - ℓ, 0, N.a * c - ℓ, -ℓ, N.p * c - (1 - N.r) * ℓ, -ℓ, 0] i) ∧
      (∀ i, ⟪x i - x 1, N.E₂⟫ = ![-h, 0, (N.b - 1) * h, -h, 0, 0, -h] i) ∧
      (∀ i, ⟪x i - x 1, W⟫ = ![ω, 0, N.a * ω, 0, N.p * ω, 0, 0] i) := by
  set E1 := N.E₁ with hE1
  set E2 := N.E₂ with hE2
  set E3 := N.E₃ with hE3
  have c21 : ⟪E2, E1⟫ = ⟪E1, E2⟫ := real_inner_comm _ _
  have c31 : ⟪E3, E1⟫ = ⟪E1, E3⟫ := real_inner_comm _ _
  have c32 : ⟪E3, E2⟫ = ⟪E2, E3⟫ := real_inner_comm _ _
  simp only [N.x0, N.x3, N.x1, N.x6, nfP_sub, inner_nfV, inner_nfV_right, hg, hd, ← hE1, ← hE2,
    ← hE3] at h1 h2
  have e12 : ⟪E1, E2⟫ = 0 := by linear_combination h1
  have e23 : ⟪E2, E3⟫ = 0 := by linear_combination -h2 + e12 - c32
  have hne : ∀ i j : Fin 7, i ≠ j → x i ≠ x j := fun i j h e => h (N.inj e)
  have v53 : x 5 - x 3 = E2 := by rw [N.x5, N.x3]; simp only [nfP]; module
  have v63 : x 6 - x 3 = E3 := by rw [N.x6, N.x3]; simp only [nfP]; module
  have hE20 : E2 ≠ 0 := by
    rw [← v53]; exact sub_ne_zero.2 (hne 5 3 (by decide))
  have hE30 : E3 ≠ 0 := by
    rw [← v63]; exact sub_ne_zero.2 (hne 6 3 (by decide))
  set ℓ := ⟪E3, E3⟫ with hℓ
  set h := ⟪E2, E2⟫ with hh
  set c := ⟪E1, E3⟫ with hc
  set W : ℝ³ := ℓ • E1 - c • E3 with hW
  set ω := ℓ * ⟪E1, E1⟫ - c ^ 2 with hω
  have hℓ0 : 0 < ℓ := by rw [hℓ, real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.2 hE30) 2
  have hh0 : 0 < h := by rw [hh, real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.2 hE20) 2
  have w1 : ⟪E1, W⟫ = ω := by
    simp only [hW, inner_sub_right, real_inner_smul_right, hω]; ring
  have w2 : ⟪E2, W⟫ = 0 := by
    simp only [hW, inner_sub_right, real_inner_smul_right, c21, e12, e23]; ring
  have w3 : ⟪E3, W⟫ = 0 := by
    simp only [hW, inner_sub_right, real_inner_smul_right, c31]; ring
  have hW0 : W ≠ 0 := by
    intro h0
    have hj : ∀ j, ℓ * E1 j - c * E3 j = 0 := by
      intro j
      have := congrArg (fun v : ℝ³ => v j) h0
      simpa [hW] using this
    have hdet : ℓ * det3 E1 E2 E3 = 0 := by
      rw [det3_expand]
      linear_combination (E2 1 * E3 2 - E2 2 * E3 1) * hj 0 +
        (E2 2 * E3 0 - E2 0 * E3 2) * hj 1 + (E2 0 * E3 1 - E2 1 * E3 0) * hj 2
    rcases mul_eq_zero.1 hdet with h' | h'
    · exact hℓ0.ne' h'
    · exact N.hD h'
  have hω0 : 0 < ω := by
    have hWW : ⟪W, W⟫ = ℓ * ω := by
      have h' := (show ⟪ℓ • E1 - c • E3, W⟫ = ℓ * ω by
        simp only [inner_sub_left, real_inner_smul_left, w1, w3]; ring)
      exact h'
    have : 0 < ⟪W, W⟫ := by
      rw [real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.2 hW0) 2
    rw [hWW] at this
    exact (mul_pos_iff_of_pos_left hℓ0).1 this
  refine ⟨ℓ, h, c, ω, W, hℓ0, hh0, hω0, hW0, hE20, hE30, rfl, rfl, e23, w2, w3, ?_, ?_, ?_⟩ <;>
  · intro i
    fin_cases i <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, N.x0, N.x1, N.x2, N.x3,
        N.x4, N.x5, N.x6, nfP_sub, inner_nfV, hg, hd, hq, ← hE1, ← hE2, ← hE3]
      simp only [c32, e12, e23, w1, w2, w3, ← hℓ, ← hh, ← hc, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      ring

set_option hygiene false in
/-- Closer for the per-vertex obligations of the four walls (uses the local name `k2`). -/
macro "pl_close" : tactic => `(tactic| first
  | linarith
  | exact ⟨by linarith, by linarith⟩
  | (have := k2 (by linarith); linarith)
  | (rcases h2 with h' | h' <;> linarith)
  | (rcases h2 with h' | h' <;> (have := k2 (by linarith); linarith)))

set_option maxHeartbeats 1000000 in
/-- **Type 16 on `PL` with `r ≤ 1`, by the Slide Lemma**: the Slide Lemma leaf with `r ≤ 1` and (`r < 1` or
`⟪x 0 - x 3, x 6 - x 3⟫ ≠ 0`, `c ≠ 0`); at `r = 1` the residue is `c = 0`. -/
theorem isRupert_PL_slide_le (N : NF16 x) (hg : N.g = 1) (hd : N.d = 1) (hq : N.q = 1)
    (h1 : ⟪x 0 - x 3, x 1 - x 6⟫ = 0) (h2 : ⟪x 0 - x 6, x 1 - x 6⟫ = 0) (hr1 : N.r ≤ 1)
    (hc0 : N.r < 1 ∨ ⟪x 0 - x 3, x 6 - x 3⟫ ≠ 0) :
    IsRupert (univ.image x) := by
  obtain ⟨ℓ, h, c, ω, W, hℓ, hh, hω, hW0, hE20, hE30, eℓ, eh, e23, w2, w3, tA, tB, tY⟩ :=
    pl_data N hg hd hq h1 h2
  have ha := N.ha
  have hp := N.hp
  have hr := N.hr
  have hb := N.hb
  have hb1 : N.b < 1 := by
    have t := N.tB125
    rw [hg, hd, hq] at t
    have : 0 < N.p * (1 - N.b) := by linarith
    linarith [(mul_pos_iff_of_pos_left hp).1 this]
  have qa : 0 < N.a * ω := mul_pos ha hω
  have qp : 0 < N.p * ω := mul_pos hp hω
  have qb0 : 0 < (1 - N.b) * h := mul_pos (by linarith) hh
  have qb1 : 0 < N.b * h := mul_pos hb hh
  have hsh : ∀ i a : Fin 7, ∀ v : ℝ³, ⟪x i - x a, v⟫ = ⟪x i - x 1, v⟫ - ⟪x a - x 1, v⟫ := by
    intro i a v; rw [← inner_sub_left]; congr 1; abel
  have v51 : x 5 - x 1 = -N.E₃ := by rw [N.x5, N.x1, hg, hd]; simp only [nfP]; module
  have v61 : x 6 - x 1 = -N.E₂ := by rw [N.x6, N.x1, hg, hd]; simp only [nfP]; module
  have v31 : x 3 - x 1 = -N.E₃ + -N.E₂ := by rw [N.x3, N.x1, hg, hd]; simp only [nfP]; module
  have v36 : x 3 - x 6 = -N.E₃ := by rw [N.x3, N.x6]; simp only [nfP]; module
  have v16 : x 1 - x 6 = N.E₂ := by rw [N.x1, N.x6, hg, hd]; simp only [nfP]; module
  have v56 : x 5 - x 6 = -N.E₃ + N.E₂ := by rw [N.x5, N.x6]; simp only [nfP]; module
  have v15 : x 1 - x 5 = N.E₃ := by rw [N.x1, N.x5, hg, hd]; simp only [nfP]; module
  have v35 : x 3 - x 5 = -N.E₂ := by rw [N.x3, N.x5]; simp only [nfP]; module
  have v65 : x 6 - x 5 = N.E₃ + -N.E₂ := by rw [N.x6, N.x5]; simp only [nfP]; module
  have v63 : x 6 - x 3 = N.E₃ := by rw [N.x6, N.x3]; simp only [nfP]; module
  have v53 : x 5 - x 3 = N.E₂ := by rw [N.x5, N.x3]; simp only [nfP]; module
  have v13 : x 1 - x 3 = N.E₃ + N.E₂ := by rw [N.x1, N.x3, hg, hd]; simp only [nfP]; module
  have e32 : ⟪N.E₃, N.E₂⟫ = 0 := by rw [real_inner_comm]; exact e23
  have nℓ : ‖N.E₃‖ ^ 2 = ℓ := by rw [← real_inner_self_eq_norm_sq]; exact eℓ
  have nh : ‖N.E₂‖ ^ 2 = h := by rw [← real_inner_self_eq_norm_sq]; exact eh
  have nE2 : -N.E₂ ≠ 0 := neg_ne_zero.2 hE20
  have nE3 : -N.E₃ ≠ 0 := neg_ne_zero.2 hE30
  rcases le_or_gt c 0 with hc | hc
  · -- `c ≤ 0`: the deep vertices beyond `x1` (σ = +1)
    have P0 : 0 < -(c - ℓ) := by linarith
    have P2 : 0 < -(N.a * c - ℓ) := by nlinarith
    have P4 : 0 < -(N.p * c - (1 - N.r) * ℓ) := by
      rcases hc0 with hr' | hc'
      · nlinarith
      · have hcc : ⟪x 0 - x 3, x 6 - x 3⟫ = c := by
          rw [v63, hsh 0 3, tA 0, tA 3]
          simp only [Matrix.cons_val]; ring
        have hcn : c < 0 := lt_of_le_of_ne hc (fun e => hc' (by rw [hcc, e]))
        nlinarith [mul_pos hp (neg_pos.2 hcn), mul_nonneg (sub_nonneg.2 hr1) hℓ.le]
    rcases Minimality.Split.Slide.kdich hℓ P4 P0 qp hω with ⟨κ, k1, k2⟩ | ⟨κ, k1, k2⟩
    · -- wall `F = 145`, edge `15`: `(a, b, a', b') = (1, 5, 6, 3)`
      refine Minimality.Split.Slide.slide_tab
        x 1 5 6 3 (-N.E₃) (-N.E₂) W (fun i => -⟪x i - x 1, N.E₃⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => -⟪x i - x 1, N.E₂⟫)
        (fun i => by rw [inner_neg_right]) (fun _ => rfl) (fun i => by rw [inner_neg_right])
        v51 v61 v31 nE3 nE2 hW0 (by rw [inner_neg_left, inner_neg_right, e32, neg_zero, neg_zero])
        (by rw [inner_neg_left, w3, neg_zero]) (by rw [inner_neg_left, w2, neg_zero])
        ?_ ?_ ?_ ⟨0, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> pl_close
      · intro i; fin_cases i <;> simp [tB, nh] <;> pl_close
      · intro i h; fin_cases i <;> simp [tA, tY] at h ⊢ <;> pl_close
      · simp [tY]; pl_close
      · simp [tB, nh]
      · intro i h1 h2; fin_cases i <;> simp [tA, tY, tB, nh] at h1 h2 ⊢ <;> pl_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tA, tY, tB, nℓ] at h1 h2 h3 ⊢ <;> pl_close
    · -- wall `D = 036`, edge `63`: `(a, b, a', b') = (6, 3, 1, 5)`
      refine Minimality.Split.Slide.slide_tab
        x 6 3 1 5 (-N.E₃) N.E₂ W (fun i => -⟪x i - x 1, N.E₃⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => h + ⟪x i - x 1, N.E₂⟫) ?_ ?_ ?_ v36 v16 v56 nE3
        hE20 hW0 (by rw [inner_neg_left, e32, neg_zero]) (by rw [inner_neg_left, w3, neg_zero]) w2
        ?_ ?_ ?_ ⟨4, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i
        rw [hsh i 6, inner_neg_right, inner_neg_right, tA 6]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 6, tY 6]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 6, tB 6]; simp only [Matrix.cons_val]; ring
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> pl_close
      · intro i; fin_cases i <;> simp [tB, nh] <;> pl_close
      · intro i h; fin_cases i <;> simp [tA, tY] at h ⊢ <;> pl_close
      · simp [tY]; pl_close
      · simp [tB, nh]
      · intro i h1 h2; fin_cases i <;> simp [tA, tY, tB, nh] at h1 h2 ⊢ <;> pl_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tA, tY, tB, nℓ] at h1 h2 h3 ⊢ <;> pl_close
  · -- `0 < c`: the deep vertices before `x5` (σ = -1)
    have M0 : 0 < ℓ + (c - ℓ) := by linarith
    have M4 : 0 < ℓ + (N.p * c - (1 - N.r) * ℓ) := by nlinarith
    have M2 : 0 < ℓ + (N.a * c - ℓ) := by nlinarith
    rcases Minimality.Split.Slide.kdich hℓ M4 M0 qp hω with ⟨κ, k1, k2⟩ | ⟨κ, k1, k2⟩
    · -- wall `F = 145`, edge `51`: `(a, b, a', b') = (5, 1, 3, 6)`
      refine Minimality.Split.Slide.slide_tab
        x 5 1 3 6 N.E₃ (-N.E₂) W (fun i => ℓ + ⟪x i - x 1, N.E₃⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => -⟪x i - x 1, N.E₂⟫) ?_ ?_ ?_ v15 v35 v65 hE30 nE2
        hW0 (by rw [inner_neg_right, e32, neg_zero]) w3 (by rw [inner_neg_left, w2, neg_zero])
        ?_ ?_ ?_ ⟨0, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i; rw [hsh i 5, tA 5]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 5, tY 5]; simp only [Matrix.cons_val]; ring
      · intro i
        rw [hsh i 5, inner_neg_right, inner_neg_right, tB 5]; simp only [Matrix.cons_val]; ring
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> pl_close
      · intro i; fin_cases i <;> simp [tB, nh] <;> pl_close
      · intro i h; fin_cases i <;> simp [tA, tY] at h ⊢ <;> pl_close
      · simp [tY]; pl_close
      · simp [tB, nh]
      · intro i h1 h2; fin_cases i <;> simp [tA, tY, tB, nh] at h1 h2 ⊢ <;> pl_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tA, tY, tB, nℓ] at h1 h2 h3 ⊢ <;> pl_close
    · -- wall `D = 036`, edge `36`: `(a, b, a', b') = (3, 6, 5, 1)`
      refine Minimality.Split.Slide.slide_tab
        x 3 6 5 1 N.E₃ N.E₂ W (fun i => ℓ + ⟪x i - x 1, N.E₃⟫)
        (fun i => ⟪x i - x 1, W⟫) (fun i => h + ⟪x i - x 1, N.E₂⟫) ?_ ?_ ?_ v63 v53 v13 hE30
        hE20 hW0 e32 w3 w2 ?_ ?_ ?_ ⟨4, ?_, ?_⟩ ⟨κ, ?_, ?_⟩
      · intro i; rw [hsh i 3, tA 3]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 3, tY 3]; simp only [Matrix.cons_val]; ring
      · intro i; rw [hsh i 3, tB 3]; simp only [Matrix.cons_val]; ring
      · intro i h1 h2 h3 h4; fin_cases i <;> simp [tY] at h1 h2 h3 h4 ⊢ <;> pl_close
      · intro i; fin_cases i <;> simp [tB, nh] <;> pl_close
      · intro i h; fin_cases i <;> simp [tA, tY] at h ⊢ <;> pl_close
      · simp [tY]; pl_close
      · simp [tB, nh]
      · intro i h1 h2; fin_cases i <;> simp [tA, tY, tB, nh] at h1 h2 ⊢ <;> pl_close
      · intro i h1 h2 h3; fin_cases i <;> simp [tA, tY, tB, nℓ] at h1 h2 h3 ⊢ <;> pl_close

/-- **Type 16 on `PL` with `r < 1`**, a special case of `isRupert_PL_slide_le`. -/
theorem isRupert_PL_slide (N : NF16 x) (hg : N.g = 1) (hd : N.d = 1) (hq : N.q = 1)
    (h1 : ⟪x 0 - x 3, x 1 - x 6⟫ = 0) (h2 : ⟪x 0 - x 6, x 1 - x 6⟫ = 0) (hr1 : N.r < 1) :
    IsRupert (univ.image x) :=
  isRupert_PL_slide_le N hg hd hq h1 h2 hr1.le (Or.inl hr1)

/-- **The stratum `Z` from the shape entries.**  Three of the 18 entries of `ZShape16` give
`g = d = q = 1`: `[0 1 5 | 3 6] = (1 - g) D`, `[0 1 6 | 3 5] = (d - 1) D`, and the facet `036` takes
the same value at `x 4` and `x 5` (`f (x 4) = q f (x 5)`, `f (x 5) < 0`). -/
theorem zshape_nf (N : NF16 x) (F : H21.S0xFac 8 Minimality.V2.fIdx x)
    (hZ : H16.SAT.ZShape16 x F) : N.g = 1 ∧ N.d = 1 ∧ N.q = 1 := by
  obtain ⟨z1, z2, -, -, -, -, -, z8, -, -, -, -, -, -, -, -, -, -⟩ := hZ
  simp only [N.x0, N.x1, N.x3, N.x5, N.x6, nfP_sub, det3_nfV] at z1 z2
  have y1 := (mul_eq_zero.1 z1).resolve_right N.hD
  have y2 := (mul_eq_zero.1 z2).resolve_right N.hD
  simp only [det3c] at y1 y2
  refine ⟨by linarith, by linarith, ?_⟩
  rw [F.inner_sub] at z8
  have o3 : N.o = x 3 := by rw [N.x3]; simp only [nfP]; module
  have o0 : N.o + N.E₁ = x 0 := by rw [N.x0]; simp only [nfP]; module
  have o5 : N.o + N.E₂ = x 5 := by rw [N.x5]; simp only [nfP]; module
  have o6 : N.o + N.E₃ = x 6 := by rw [N.x6]; simp only [nfP]; module
  have e4 := affine_nfP (F.hN 3) N.o N.E₁ N.E₂ N.E₃ N.p N.q N.r
  rw [← N.x4, o0, o5, o6, o3, F.zero 3 0 (by decide), F.zero 3 3 (by decide),
    F.zero 3 6 (by decide)] at e4
  have n5 := F.neg 3 5 (by decide)
  have : (N.q - 1) * F.f 3 (x 5) = 0 := by linear_combination z8 - e4
  have := (mul_eq_zero.1 this).resolve_right n5.ne
  linarith

/-- **`r < 1` from the class sign.**  On `g = d = q = 1`, `C [0134] = (r - 1) D²`. -/
theorem r_lt_one (N : NF16 x) (hg : N.g = 1) (hd : N.d = 1) (hq : N.q = 1)
    (h : H16.SAT.C16 x * H16.SAT.br16 x 0 1 3 4 < 0) : N.r < 1 := by
  have e : H16.SAT.C16 x * H16.SAT.br16 x 0 1 3 4 = (N.r - 1) * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
    simp only [H16.SAT.C16, H16.SAT.br16, N.x0, N.x1, N.x3, N.x4, N.x5, N.x6, nfP_sub,
      det3_nfV, det3c, hg, hd, hq]
    ring
  rw [e] at h
  have hD2 : 0 < det3 N.E₁ N.E₂ N.E₃ ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 N.hD))
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.2 hc) hD2.le]

end Minimality.NF16

namespace Minimality.H16.SAT

open Minimality

/-- **Type 16 on `PL`.**  A type 16 shape with `C [0134] < 0` (`C = [3056]`), with `x 1 - x 6`
orthogonal to `x 0 - x 3` and `x 0 - x 6` (`¬ CaseT16`) and the shape entries of `Z` zero (for any
facet family) is Rupert.  Every class with that sign is covered (`+---`, `+-+-`, ...). -/
theorem isRupert_PL16 {x : Fin 7 → ℝ³} (T : Type16 x) (F : H21.S0xFac 8 Minimality.V2.fIdx x)
    (hb2 : C16 x * br16 x 0 1 3 4 < 0) (hT : ¬ CaseT16 x) (hZ : ZShape16 x F) :
    IsRupert (univ.image x) := by
  have N := T.toNF
  obtain ⟨hg, hd, hq⟩ := N.zshape_nf F hZ
  simp only [CaseT16, not_or, not_not] at hT
  exact N.isRupert_PL_slide hg hd hq hT.1 hT.2 (N.r_lt_one hg hd hq hb2)

/-- **The `sigma16` image**: `C [2346] < 0` and the hypotheses of `isRupert_PL16` for
`x ∘ sigma16`. -/
theorem isRupert_PL16_sigma {x : Fin 7 → ℝ³} (T : Type16 x)
    (F' : H21.S0xFac 8 Minimality.V2.fIdx (x ∘ sigma16)) (hb4 : C16 x * br16 x 2 3 4 6 < 0)
    (hT : ¬ CaseT16 (x ∘ sigma16)) (hZ : ZShape16 (x ∘ sigma16) F') :
    IsRupert (univ.image x) := by
  have := isRupert_PL16 T.sigma F' (by rw [C16_sigma, b2_sigma]; linarith) hT hZ
  rwa [Minimality.image_sigma16] at this

/-- The strict class vector (signs of `C * [0126]`, `C * [0134]`, `C * [1234]`, `C * [2346]`) is
`+---` or its `sigma16` image `----`. -/
def Cls16M (x : Fin 7 → ℝ³) : Prop :=
  let C := C16 x
  let b1 := br16 x 0 1 2 6
  let b2 := br16 x 0 1 3 4
  let b3 := br16 x 1 2 3 4
  let b4 := br16 x 2 3 4 6
  (0 < C * b1 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ C * b4 < 0) ∨
  (C * b1 < 0 ∧ C * b2 < 0 ∧ C * b3 < 0 ∧ C * b4 < 0)

/-- **Type 16, the class `+---` (and `----`): the residual of `Cls16A` and `Cls16Z` is Rupert.**
Outside `Cls16A` both inner products of `CaseT16` vanish, outside `Cls16Z` all 18 shape entries of
`Z` vanish: the stratum `PL`, closed by `isRupert_PL16` (`isRupert_PL16_sigma` for `----`). -/
theorem isRupert_cls16M_resid {x : Fin 7 → ℝ³} (T : Type16 x) (hM : Cls16M x) (hA : ¬ Cls16A x)
    (hZ : ¬ Cls16Z x T) : IsRupert (univ.image x) := by
  simp only [Cls16M] at hM
  rcases hM with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · refine isRupert_PL16 T (Minimality.H16A.h16g_fac T) h2
      (fun hc => hA (Or.inl ⟨h1, h2, h3, h4, hc⟩)) ?_
    by_contra hc
    exact hZ (Or.inl ⟨h1, h2, h3, h4, hc⟩)
  · refine isRupert_PL16_sigma T (Minimality.H16A.h16g_fac T.sigma) h4
      (fun hc => hA (Or.inr ⟨h1, h2, h3, h4, hc⟩)) ?_
    by_contra hc
    exact hZ (Or.inr ⟨h1, h2, h3, h4, hc⟩)

/-- The class `+-+-` on `x`, from the two class cores of the shape of `Cls16C` / `Cls16Z` (off `PL`)
and `isRupert_PL16` (on `PL`). -/
theorem isRupert_pmpm_of (hT : Core16T 1 (-1) 1 (-1)) (hZc : Core16Z 1 (-1) 1 (-1))
    {x : Fin 7 → ℝ³} (T : Type16 x)
    (h1 : 0 < C16 x * br16 x 0 1 2 6) (h2 : C16 x * br16 x 0 1 3 4 < 0)
    (h3 : 0 < C16 x * br16 x 1 2 3 4) (h4 : C16 x * br16 x 2 3 4 6 < 0) :
    IsRupert (univ.image x) := by
  have F := Minimality.H16A.h16g_fac T
  have hne : C16 x ≠ 0 := T.det_ne
  by_cases hc : CaseT16 x
  · exact rupert_of_core_bothT hT F hne (by linarith) (by linarith) (by linarith) (by linarith) hc
  by_cases hz : ZShape16 x F
  · exact isRupert_PL16 T F h2 hc hz
  · exact rupert_of_core_bothZ hZc F hne (by linarith) (by linarith) (by linarith) (by linarith) hz

/-- **Type 16, the class `+-+-` and its `sigma16` image `--+-`, from two class cores** (the cores
`Core16T 1 (-1) 1 (-1)` and `Core16Z 1 (-1) 1 (-1)` are the off-`PL` cases; `PL` is
`isRupert_PL16`). -/
theorem isRupert_clsPMPM_of (hT : Core16T 1 (-1) 1 (-1)) (hZc : Core16Z 1 (-1) 1 (-1))
    {x : Fin 7 → ℝ³} (T : Type16 x)
    (h : (0 < C16 x * br16 x 0 1 2 6 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
        C16 x * br16 x 2 3 4 6 < 0) ∨
      (C16 x * br16 x 0 1 2 6 < 0 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
        C16 x * br16 x 2 3 4 6 < 0)) :
    IsRupert (univ.image x) := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact isRupert_pmpm_of hT hZc T h1 h2 h3 h4
  · have e1 := C16_sigma x
    have e2 := b1_sigma x
    have e3 := b2_sigma x
    have e4 := b3_sigma x
    have e5 := b4_sigma x
    have := isRupert_pmpm_of hT hZc T.sigma (by rw [e1, e2]; linarith) (by rw [e1, e3]; linarith)
      (by rw [e1, e4]; linarith) (by rw [e1, e5]; linarith)
    rwa [Minimality.image_sigma16] at this

end Minimality.H16.SAT

