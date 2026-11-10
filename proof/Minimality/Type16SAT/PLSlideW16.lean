module

public import Minimality.Type16SAT.PLSlide16

@[expose] public section

/-!
# Type 16 on `PL` at `r ≤ 1`: the Slide Lemma leaf on the wall `[0134] = 0`

`NF16.isRupert_PL_slide_le`: the proof of `NF16.isRupert_PL_slide` (PLSlide16) with `r < 1` weakened to `r ≤ 1` and
`r < 1 ∨ c ≠ 0`, `c = ⟪x 0 - x 3, x 6 - x 3⟫`.  Only the coordinate `X_4 = (1 - r) ℓ - p c` of the case `c ≤ 0` used `r < 1`;
at `r = 1` it is `-p c > 0` when `c < 0`.  The residue of the wall `r = 1` on `PL` is `c = 0` (both slab ends touched:
`X_4 = 0`, `ℓ - X_0 = c = 0`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.NF16

variable {x : Fin 7 → ℝ³}

set_option maxHeartbeats 1000000 in
/-- **Type 16 on `PL` with `r ≤ 1`, by the Slide Lemma**: as `isRupert_PL_slide`, with `r ≤ 1` and (`r < 1` or
`⟪x 0 - x 3, x 6 - x 3⟫ ≠ 0`). -/
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

end Minimality.NF16
