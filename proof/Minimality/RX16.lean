module

public import Minimality.R046

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012 Minimality.T24.R046

namespace Minimality.T24.RX16


variable {x : Fin 7 → ℝ³}

/-- The tie parameter on the 012 circle: `⟪x 1 - x 6, u0 x t⟫ = 0` (depths of 1 and 6 agree). -/
noncomputable def t16 (x : Fin 7 → ℝ³) : ℝ :=
  - ⟪x 1 - x 6, x 0 - x 1⟫ / ⟪x 1 - x 6, x 2 - x 1⟫

/-- The base view `u16 = u0 (t16)`. -/
noncomputable def u16 (x : Fin 7 → ℝ³) : ℝ³ := u0 x (t16 x)

theorem inner_tie16 (hΔ : ⟪x 1 - x 6, x 2 - x 1⟫ ≠ 0) : ⟪x 1, u16 x⟫ = ⟪x 6, u16 x⟫ := by
  have : ⟪x 1 - x 6, u16 x⟫ = 0 := by
    dsimp [u16, u0, t16]
    rw [inner_add_right, real_inner_smul_right]
    have : - ⟪x 1 - x 6, x 0 - x 1⟫ / ⟪x 1 - x 6, x 2 - x 1⟫ * ⟪x 1 - x 6, x 2 - x 1⟫ =
        - ⟪x 1 - x 6, x 0 - x 1⟫ := div_mul_cancel₀ _ hΔ
    rw [this]; ring
  rw [← sub_eq_zero, ← inner_sub_left]; exact this

lemma ev_aff_lt (c t σ : ℝ) (h : t < c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t + σ * ε < c := by
  have := eventually_pos_affine (A := c - t) (B := -σ) (Or.inl (by linarith))
  filter_upwards [this] with ε hε; nlinarith

lemma ev_aff_gt (c t σ : ℝ) (h : c < t) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c < t + σ * ε := by
  have := eventually_pos_affine (A := t - c) (B := σ) (Or.inl (by linarith))
  filter_upwards [this] with ε hε; nlinarith

private lemma ev_inner_pos (N : ℝ³) (x : Fin 7 → ℝ³) (t σ : ℝ) (h : 0 < ⟪N, u0 x t⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪N, u0 x (t + σ * ε)⟫ := by
  have := eventually_pos_affine (A := ⟪N, u0 x t⟫) (B := σ * ⟪N, x 2 - x 1⟫) (Or.inl h)
  filter_upwards [this] with ε hε
  rw [inner_u0_add]; nlinarith

private lemma ev_inner_neg (N : ℝ³) (x : Fin 7 → ℝ³) (t σ : ℝ) (h : ⟪N, u0 x t⟫ < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪N, u0 x (t + σ * ε)⟫ < 0 := by
  have := eventually_pos_affine (A := -⟪N, u0 x t⟫) (B := -(σ * ⟪N, x 2 - x 1⟫)) (Or.inl (by linarith))
  filter_upwards [this] with ε hε
  rw [inner_u0_add]; nlinarith

lemma sat_of_gen (p : ZMod 4 → ℝ³) (b : ℝ³) (htie : ⟪p 2, b⟫ = ⟪p 3, b⟫)
    (hg : ∀ i j : ZMod 4, i ≠ j → (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ ⟪p i - p j, b⟫ ≠ 0) :
    SingleAdjacentTie p b 2 := by
  refine ⟨htie, ?_⟩
  intro i j h
  by_cases hij : i = j
  · exact Or.inl hij
  · right
    rcases hg i j hij with h1 | h1 | h1
    · exact Or.inl ⟨h1.1, by rw [h1.2]; decide⟩
    · exact Or.inr ⟨by rw [h1.1]; decide, h1.2⟩
    · exact absurd (by rw [inner_sub_left, h]; ring) h1

lemma branch_real (L T R s : ℝ) (hL : L ≠ T) (hR : R ≠ T)
    (h : 0 < (T - L) * (T - R) ∨ 0 < s * (L - R)) :
    ((L < T ∧ R < T) ∨ (T < L ∧ T < R)) ∨
      (((L < T ∧ T < R) ∨ (R < T ∧ T < L)) ∧ (0 < L - R ↔ 0 < s)) := by
  rcases lt_or_gt_of_ne hL with h1 | h1 <;> rcases lt_or_gt_of_ne hR with h2 | h2
  · exact Or.inl (Or.inl ⟨h1, h2⟩)
  · refine Or.inr ⟨Or.inl ⟨h1, h2⟩, ?_⟩
    rcases h with h | h
    · nlinarith
    · constructor
      · intro h3; linarith
      · intro h3; nlinarith
  · refine Or.inr ⟨Or.inr ⟨h2, h1⟩, ?_⟩
    rcases h with h | h
    · nlinarith
    · constructor
      · intro h3; nlinarith
      · intro h3; nlinarith
  · exact Or.inl (Or.inr ⟨h1, h2⟩)

/-- Splitting the tie of a 4-rim `p` at `a = 2`: the merged 3-cycle is always unimodal; the only
condition is the branch (peak or valley of the tie, or the tilt sign matching the slope). -/
theorem split4_ev (p : ZMod 4 → ℝ³) (b d : ℝ³) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (htie : SingleAdjacentTie p b 2) (hΔ : ⟪p 2 - p 3, d⟫ ≠ 0)
    (hbr : 0 < (⟪p 2, b⟫ - ⟪p 1, b⟫) * (⟪p 2, b⟫ - ⟪p 0, b⟫) ∨
      0 < σ * ⟪p 2 - p 3, d⟫ * (⟪p 1, b⟫ - ⟪p 0, b⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, b + (σ * ε) • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, b + (σ * ε) • d⟫) := by
  have e1 : (2 : ZMod 4) - 1 = 1 := by decide
  have e2 : (2 : ZMod 4) + 2 = 0 := by decide
  have e3 : (2 : ZMod 4) + 1 = 3 := by decide
  have hinj : Function.Injective (mergedDepths (fun i => ⟪p i, b⟫) 2) :=
    merged_inj_of_singleAdjacentTie (k := 3) p b 2 htie
  have huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪p i, b⟫) 2) :=
    isCyclicUnimodal_three _ hinj
  have w0 : mergedDepths (fun i => ⟪p i, b⟫) 2 0 = ⟪p 2, b⟫ := by
    have := mergedDepths_zero' (m := 3) (fun i => ⟪p i, b⟫) 2
    rw [e3] at this; rw [this]; exact htie.1.symm
  have wm : mergedDepths (fun i => ⟪p i, b⟫) 2 (-1) = ⟪p 1, b⟫ := by
    have := mergedDepths_neg_one (m := 3) (fun i => ⟪p i, b⟫) 2
    rw [e1] at this; exact this
  have w1 : mergedDepths (fun i => ⟪p i, b⟫) 2 1 = ⟪p 0, b⟫ := by
    have := mergedDepths_one (m := 3) (by omega) (fun i => ⟪p i, b⟫) 2
    rw [e2] at this; exact this
  have n1 : ⟪p 1, b⟫ ≠ ⟪p 2, b⟫ := by
    rw [← wm, ← w0]; intro h; have := hinj h; revert this; decide
  have n2 : ⟪p 0, b⟫ ≠ ⟪p 2, b⟫ := by
    rw [← w1, ← w0]; intro h; have := hinj h; revert this; decide
  have hbranch :
      (IsMergedExtremum (mergedDepths (fun i => ⟪p i, b⟫) 2)) ∨
      (IsMergedMonotone (mergedDepths (fun i => ⟪p i, b⟫) 2) ∧
        (0 < ⟪p (2 - 1), b⟫ - ⟪p (2 + 2), b⟫ ↔ 0 < σ * ⟪p 2 - p (2 + 1), d⟫)) := by
    rw [e1, e2, e3]
    unfold IsMergedExtremum IsMergedMonotone
    rw [w0, wm, w1]
    exact branch_real _ _ _ _ n1 n2 hbr
  exact splitUnimodal_step (m := 3) (by omega) p b d 2 σ hσ htie (by rw [e3]; exact hΔ) huni hbranch

lemma quad_x (a b c d : Fin 7) : ∀ i : ZMod 4, x (quad a b c d i) = quad (x a) (x b) (x c) (x d) i := by
  intro i; fin_cases i <;> rfl

/-- **q012_x16, branch `t16 < -1`** (A21 Rank 3): the view on the circle of `012` where `z1 = z6`,
perturbed along `x2 - x1` by `ε > 0`; rim `(4, 0, 1, 6)`, chord `0 → 1`, middle `2`. -/
theorem q012_x16_lo (F : S0xFac 9 s0x_S24 x)
    (hΔ : ⟪x 1 - x 6, x 2 - x 1⟫ ≠ 0) (ht : t16 x < -1)
    (hN3 : ⟪F.N 3, u16 x⟫ < 0) (hN4 : 0 < ⟪F.N 4, u16 x⟫) (hN8 : ⟪F.N 8, u16 x⟫ < 0)
    (hbr : 0 < (⟪x 1, u16 x⟫ - ⟪x 0, u16 x⟫) * (⟪x 1, u16 x⟫ - ⟪x 4, u16 x⟫) ∨
      0 < ⟪x 1 - x 6, x 2 - x 1⟫ * (⟪x 0, u16 x⟫ - ⟪x 4, u16 x⟫))
    (hgen : ∀ i j : ZMod 4, i ≠ j → (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      ⟪quad (x 4) (x 0) (x 1) (x 6) i - quad (x 4) (x 0) (x 1) (x 6) j, u16 x⟫ ≠ 0)
    (hfar : (F.f 0 (x 6) < F.f 0 (x 4) ∧
        (⟪F.N 0, cross (x 1 - x 0) (x 6 - x 0)⟫ ≠ 0 ∨
          ⟪x 6 - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x 6 - x 1, x 0 - x 1⟫ < 0)) ∨
      (F.f 0 (x 4) < F.f 0 (x 6) ∧
        (⟪F.N 0, cross (x 1 - x 0) (x 4 - x 0)⟫ ≠ 0 ∨
          ⟪x 4 - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x 4 - x 1, x 0 - x 1⟫ < 0))) :
    FaceChordView F 0 := by
  set p : ZMod 4 → ℝ³ := quad (x 4) (x 0) (x 1) (x 6) with hp
  have hsat : SingleAdjacentTie p (u16 x) 2 := sat_of_gen p _ (inner_tie16 hΔ) hgen
  have hs := split4_ev p (u16 x) (x 2 - x 1) 1 (Or.inl rfl) hsat hΔ
    (by rcases hbr with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [one_mul]; exact h))
  have hs' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, u0 x (t16 x + 1 * ε)⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, u0 x (t16 x + 1 * ε)⟫) := by
    filter_upwards [hs] with ε hε
    have heq : u16 x + (1 * ε) • (x 2 - x 1) = u0 x (t16 x + 1 * ε) := (u0_add x (t16 x) (1 * ε)).symm
    rwa [heq] at hε
  have e3 := ev_inner_neg (F.N 3) x (t16 x) 1 hN3
  have e4 := ev_inner_pos (F.N 4) x (t16 x) 1 hN4
  have e8 := ev_inner_neg (F.N 8) x (t16 x) 1 hN8
  have et := ev_aff_lt (-1) (t16 x) 1 ht
  obtain ⟨ε, ⟨hinj, huni⟩, h3, h4, h8, ht'⟩ := (hs'.and (e3.and (e4.and (e8.and et)))).exists
  set t' := t16 x + 1 * ε with ht'def
  set u := u0 x t' with hu
  have h1 : 0 < ⟪F.N 1, u⟫ := by
    rw [hu, inner_N1_u0]; have := lambda1_pos F; nlinarith
  have h5 : ⟪F.N 5, u⟫ < 0 := inner_N5_u0_neg F t'
  have h0 : ⟪F.N 0, u⟫ = 0 := inner_N0_u0 F t'
  have hne_PA := cross_ne_zero_of_facet_sign F 3 4 0 (by decide) (by decide) h3.ne 8 (by decide) (by decide)
  have hne_AB := cross_ne_zero_of_facet_sign F 1 0 1 (by decide) (by decide) h1.ne' 2 (by decide) (by decide)
  have hne_BQ := cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) h1.ne' 0 (by decide) (by decide)
  have hne_QP := cross_ne_zero_of_facet_sign F 4 6 4 (by decide) (by decide) h4.ne' 1 (by decide) (by decide)
  obtain ⟨ρ, hρ, hcyc, hint⟩ := quadRim_of_signs_gen F 4 0 1 6 3 4 0 5 1 8 4
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    hne_PA hne_AB hne_BQ hne_QP ⟨h3, h4⟩ h0 ⟨h5, h1⟩ ⟨h8, h4⟩
  set r : ZMod 4 → Fin 7 := quad (4 : Fin 7) 0 1 6 with hr
  have hrx : ∀ i, x (r i) = p i := quad_x 4 0 1 6
  have far6 : ∀ m : ZMod 4, m ≠ 3 → quad (4 : Fin 7) 0 1 6 m ∉ s0x_S24 0 → m = 0 := by decide
  have far4 : ∀ m : ZMod 4, m ≠ 0 → quad (4 : Fin 7) 0 1 6 m ∉ s0x_S24 0 → m = 3 := by decide
  obtain ⟨w, hwS, hfarw, hoffw⟩ : ∃ w : ZMod 4, r w ∉ s0x_S24 0 ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 0 → F.f 0 (x (r w)) < F.f 0 (x (r m))) ∧
      (⟪F.N 0, cross (x (r (1 + 1)) - x (r 1)) (x (r w) - x (r 1))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r 1), x (r (1 + 1)) - x (r 1)⟫ < 0 ∨
        ⟪x (r w) - x (r (1 + 1)), x (r 1) - x (r (1 + 1))⟫ < 0) := by
    rcases hfar with ⟨hf, ho⟩ | ⟨hf, ho⟩
    · refine ⟨3, by decide, ?_, ho⟩
      intro m hm hmS
      have := far6 m hm hmS
      subst this
      exact hf
    · refine ⟨0, by decide, ?_, ho⟩
      intro m hm hmS
      have := far4 m hm hmS
      subst this
      exact hf
  have ext : ∀ q : Fin 7, q ∉ s0x_S24 0 → (∀ j : ZMod 4, q ≠ r j) → q = 3 ∨ q = 5 := by decide
  have mid : ∀ q : Fin 7, q ∈ s0x_S24 0 → (∀ j : ZMod 4, q ≠ r j) → q = 2 := by decide
  have htn : t' ≠ 0 := by intro h; rw [h] at ht'; linarith
  refine ⟨u, 4, inferInstance, r, 1, w, ρ, h0, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, hwS, hfarw, hoffw⟩
  · show quad (4 : Fin 7) 0 1 6 1 ∈ s0x_S24 0; decide
  · show quad (4 : Fin 7) 0 1 6 (1 + 1) ∈ s0x_S24 0; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    simp_rw [hrx]
    rcases ext q hqS hqr with rfl | rfl
    · exact hint 3 (by decide) (by decide) (by decide) (by decide) i
    · exact hint 5 (by decide) (by decide) (by decide) (by decide) i
  · intro q hqS hqr
    have hq2 := mid q hqS hqr
    subst hq2
    have hra : x (r 1) = x 0 := rfl
    have hra1 : x (r (1 + 1)) = x 1 := rfl
    rw [hra, hra1]
    have hs0 : 0 < 1 + 1 / t' := by
      have : 1 + 1 / t' = (t' + 1) / t' := by field_simp
      rw [this]; exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hs1 : 1 + 1 / t' < 1 := by
      have := one_div_neg.mpr (show t' < 0 by linarith); linarith
    have key : x 2 = x 0 + (1 + 1 / t') • (x 1 - x 0) + (1 / t') • u0 x t' := by
      ext j
      simp only [u0, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
    exact ⟨1 + 1 / t', 1 / t', hs0, hs1, one_div_ne_zero htn, key⟩
  · simp_rw [hrx]; exact hinj
  · simp_rw [hrx]; exact Or.inl (strictUnimodal_of_cyclic (by decide) huni)

/-- **q012_x16, branch `-1 < t16 < 0`** (A21 Rank 3): the same base view, perturbed along
`-(x2 - x1)` (`σ = -1`); rim `(3, 2, 1, 6)`, chord `2 → 1`, middle `0`. -/
theorem q012_x16_hi (F : S0xFac 9 s0x_S24 x)
    (hΔ : ⟪x 1 - x 6, x 2 - x 1⟫ ≠ 0) (ht1 : -1 < t16 x) (ht0 : t16 x < 0)
    (hN6 : 0 < ⟪F.N 6, u16 x⟫) (hN7 : ⟪F.N 7, u16 x⟫ < 0) (hN8 : 0 < ⟪F.N 8, u16 x⟫)
    (hbr : 0 < (⟪x 1, u16 x⟫ - ⟪x 2, u16 x⟫) * (⟪x 1, u16 x⟫ - ⟪x 3, u16 x⟫) ∨
      0 < -⟪x 1 - x 6, x 2 - x 1⟫ * (⟪x 2, u16 x⟫ - ⟪x 3, u16 x⟫))
    (hgen : ∀ i j : ZMod 4, i ≠ j → (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      ⟪quad (x 3) (x 2) (x 1) (x 6) i - quad (x 3) (x 2) (x 1) (x 6) j, u16 x⟫ ≠ 0)
    (hfar : (F.f 0 (x 6) < F.f 0 (x 3) ∧
        (⟪F.N 0, cross (x 1 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨
          ⟪x 6 - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x 6 - x 1, x 2 - x 1⟫ < 0)) ∨
      (F.f 0 (x 3) < F.f 0 (x 6) ∧
        (⟪F.N 0, cross (x 1 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨
          ⟪x 3 - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x 3 - x 1, x 2 - x 1⟫ < 0))) :
    FaceChordView F 0 := by
  set p : ZMod 4 → ℝ³ := quad (x 3) (x 2) (x 1) (x 6) with hp
  have hsat : SingleAdjacentTie p (u16 x) 2 := sat_of_gen p _ (inner_tie16 hΔ) hgen
  have hs := split4_ev p (u16 x) (x 2 - x 1) (-1) (Or.inr rfl) hsat hΔ
    (by rcases hbr with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [neg_one_mul]; exact h))
  have hs' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, u0 x (t16 x + -1 * ε)⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, u0 x (t16 x + -1 * ε)⟫) := by
    filter_upwards [hs] with ε hε
    have heq : u16 x + (-1 * ε) • (x 2 - x 1) = u0 x (t16 x + -1 * ε) :=
      (u0_add x (t16 x) (-1 * ε)).symm
    rwa [heq] at hε
  have e6 := ev_inner_pos (F.N 6) x (t16 x) (-1) hN6
  have e7 := ev_inner_neg (F.N 7) x (t16 x) (-1) hN7
  have e8 := ev_inner_pos (F.N 8) x (t16 x) (-1) hN8
  have et1 := ev_aff_gt (-1) (t16 x) (-1) ht1
  have et0 := ev_aff_lt 0 (t16 x) (-1) ht0
  obtain ⟨ε, ⟨hinj, huni⟩, h6, h7, h8, ht1', ht0'⟩ :=
    (hs'.and (e6.and (e7.and (e8.and (et1.and et0))))).exists
  set t' := t16 x + -1 * ε with ht'def
  set u := u0 x t' with hu
  have h1 : 0 < ⟪F.N 1, u⟫ := by
    rw [hu, inner_N1_u0]; have := lambda1_pos F; nlinarith
  have h5 : ⟪F.N 5, u⟫ < 0 := inner_N5_u0_neg F t'
  have h0 : ⟪F.N 0, u⟫ = 0 := inner_N0_u0 F t'
  have hne_PA := cross_ne_zero_of_facet_sign F 6 3 2 (by decide) (by decide) h6.ne' 8 (by decide) (by decide)
  have hne_AB := cross_ne_zero_of_facet_sign F 5 2 1 (by decide) (by decide) h5.ne 2 (by decide) (by decide)
  have hne_BQ := cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) h1.ne' 0 (by decide) (by decide)
  have hne_QP := cross_ne_zero_of_facet_sign F 7 6 3 (by decide) (by decide) h7.ne 1 (by decide) (by decide)
  obtain ⟨ρ, hρ, hcyc, hint⟩ := quadRim_of_signs_gen F 3 2 1 6 7 6 0 5 1 7 8
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    hne_PA hne_AB hne_BQ hne_QP ⟨h7, h6⟩ h0 ⟨h5, h1⟩ ⟨h7, h8⟩
  set r : ZMod 4 → Fin 7 := quad (3 : Fin 7) 2 1 6 with hr
  have hrx : ∀ i, x (r i) = p i := quad_x 3 2 1 6
  have far6 : ∀ m : ZMod 4, m ≠ 3 → quad (3 : Fin 7) 2 1 6 m ∉ s0x_S24 0 → m = 0 := by decide
  have far3 : ∀ m : ZMod 4, m ≠ 0 → quad (3 : Fin 7) 2 1 6 m ∉ s0x_S24 0 → m = 3 := by decide
  obtain ⟨w, hwS, hfarw, hoffw⟩ : ∃ w : ZMod 4, r w ∉ s0x_S24 0 ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 0 → F.f 0 (x (r w)) < F.f 0 (x (r m))) ∧
      (⟪F.N 0, cross (x (r (1 + 1)) - x (r 1)) (x (r w) - x (r 1))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r 1), x (r (1 + 1)) - x (r 1)⟫ < 0 ∨
        ⟪x (r w) - x (r (1 + 1)), x (r 1) - x (r (1 + 1))⟫ < 0) := by
    rcases hfar with ⟨hf, ho⟩ | ⟨hf, ho⟩
    · refine ⟨3, by decide, ?_, ho⟩
      intro m hm hmS
      have := far6 m hm hmS
      subst this
      exact hf
    · refine ⟨0, by decide, ?_, ho⟩
      intro m hm hmS
      have := far3 m hm hmS
      subst this
      exact hf
  have ext : ∀ q : Fin 7, q ∉ s0x_S24 0 → (∀ j : ZMod 4, q ≠ r j) → q = 4 ∨ q = 5 := by decide
  have mid : ∀ q : Fin 7, q ∈ s0x_S24 0 → (∀ j : ZMod 4, q ≠ r j) → q = 0 := by decide
  refine ⟨u, 4, inferInstance, r, 1, w, ρ, h0, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, hwS, hfarw, hoffw⟩
  · show quad (3 : Fin 7) 2 1 6 1 ∈ s0x_S24 0; decide
  · show quad (3 : Fin 7) 2 1 6 (1 + 1) ∈ s0x_S24 0; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    simp_rw [hrx]
    rcases ext q hqS hqr with rfl | rfl
    · exact hint 4 (by decide) (by decide) (by decide) (by decide) i
    · exact hint 5 (by decide) (by decide) (by decide) (by decide) i
  · intro q hqS hqr
    have hq0 := mid q hqS hqr
    subst hq0
    have hra : x (r 1) = x 2 := rfl
    have hra1 : x (r (1 + 1)) = x 1 := rfl
    rw [hra, hra1]
    have key : x 0 = x 2 + (1 + t') • (x 1 - x 2) + (1 : ℝ) • u0 x t' := by
      ext j
      simp only [u0, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    exact ⟨1 + t', 1, by linarith, by linarith, one_ne_zero, key⟩
  · simp_rw [hrx]; exact hinj
  · simp_rw [hrx]; exact Or.inl (strictUnimodal_of_cyclic (by decide) huni)

end Minimality.T24.RX16
