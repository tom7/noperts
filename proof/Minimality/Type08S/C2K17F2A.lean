module

public import Minimality.Type08S.C2K17BZ

@[expose] public section


/-!
# K17F / P2: S1.1b template (Zdb(i), Tc regime: `ζ(d,b) = 0 ∧ ⟪c'-c,a-b'⟫ = 0`): a plateau cell with a corner tilt

Frame of `k6t4_zdb_core` (C2K6TDC): `P = b-d, Q = c-d, R = a-b'`, `a = (0,κ,σ)`, `b' = (0,κ,σ-1)`, `c' = (β1,κα1,α1σ)`,
`a' = (β6,1,0)`, `κ = -γ4/(α4-1)`, `σ = -1/(α4-1)`.  Cycle `kmCyc1 = (a, c', a', c, d)` at `R`; the tie makes the plateau
`c' = a' = c` (depth `⟪Q,R⟫ < 0`), peak `d`.  LexUni iff `a'` is not a w-peak of the plateau:
`⟪a'-c, v⟫ < 0` (L1) or `⟪a'-c', v⟫ < 0` (L2).  The tilt cone of the TS tests (affine, `k6t1_km1_tsc`) is
`v1 > 0 ∧ κ(α1-1) v1 < β1 v2`, rays `ρ_hi = (0,1)` and `ρ_lo = (β1, κ(α1-1))`.
* `⟪P,Q⟫ < 0`: L1 holds at `ρ_hi`; segment `(−λ⟪P,Q⟫, ⟪P,P⟫)`.
* `G := ⟪a'-c', β1 P + κ(α1-1) Q⟫ < 0`: L2 holds at `ρ_lo`; segment `(β1, κ(α1-1) + λη)`, `η` from `k8_eta`.
Numerics (`tiltsec.exe`, 6,000 metric-free zdb1_Tc samples, 2,746 with `ζ_{c'-b}(d,b) ≤ 0`): the cell exists exactly when
`⟪P,Q⟫ < 0 ∨ G < 0` (both ends never fail otherwise); 6/2,746 have neither (leftover, other cell).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k17f_zsub : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧
    (3 : ZMod 5) - 1 = 2 ∧ (4 : ZMod 5) - 1 = 3 := by decide

open Classical in
/-- A 5-cycle is lex unimodal if `m` is a lex peak and no other index is. -/
theorem k17f_lexUni5_of_peak (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) (m : ZMod 5)
    (hm : LexLt (z (m - 1), w (m - 1)) (z m, w m) ∧ LexLt (z (m + 1), w (m + 1)) (z m, w m))
    (ho : ∀ i, i ≠ m → ¬ (LexLt (z (i - 1), w (i - 1)) (z i, w i) ∧ LexLt (z (i + 1), w (i + 1)) (z i, w i))) :
    LexUni z w := by
  refine ⟨hinj, ?_⟩
  rw [Finset.card_eq_one]
  refine ⟨m, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; by_contra hne; exact ho i hne h
  · rintro rfl; exact hm

/-- Plateau lemma: peak at 4, `z 1 = z 2 = z 3 < z 0 < z 4`, and `a'` (index 2) below one plateau neighbour in `w`. -/
theorem k17f_lex_plateau (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : z 1 < z 0) (h04 : z 0 < z 4) (h12 : z 1 = z 2) (h23 : z 2 = z 3) (h34 : z 3 < z 4)
    (hw : w 2 < w 3 ∨ w 2 < w 1) : LexUni z w := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17f_zsub
  refine k17f_lexUni5_of_peak z w hinj 4 ?_ (fun i hi => ?_)
  · simp only [t4, s4, LexLt]; exact ⟨Or.inl h34, Or.inl h04⟩
  · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [t0, s0, LexLt]; rintro ⟨a1, -⟩; rcases a1 with a1 | ⟨a1, -⟩ <;> linarith
    · simp only [t1, s1, LexLt]; rintro ⟨a1, -⟩; rcases a1 with a1 | ⟨a1, -⟩ <;> linarith
    · simp only [t2, s2, LexLt]; rintro ⟨a1, a2⟩
      rcases a1 with a1 | ⟨-, a1⟩ <;> rcases a2 with a2 | ⟨-, a2⟩ <;> rcases hw with hw | hw <;> linarith
    · simp only [t3, s3, LexLt]; rintro ⟨-, a2⟩; rcases a2 with a2 | ⟨a2, -⟩ <;> linarith
    · exact absurd rfl hi

/-- Tilt weight of a frame point in canonical atoms. -/
theorem k17f_wexp (P Q R d : ℝ³) (t : ℝ × ℝ × ℝ) (v1 v2 : ℝ) :
    ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := by
  have h : ∀ x : ℝ³, ⟪x, fcomb P Q R v1 v2 0⟫ = v1 * ⟪x, P⟫ + v2 * ⟪x, Q⟫ := by
    intro x; simp [fcomb, inner_add_right, inner_smul_right]
  rw [inner_fpoint, h, h, h, h]
  rw [real_inner_comm P Q, real_inner_comm P R, real_inner_comm Q R]
  ring

set_option maxHeartbeats 3200000 in
/-- **S1.1b frame cell** `(a, c', a', c, d)` at `R` on the tie `ζ(c',c) = 0`, given L1 at `ρ_hi` or L2 at `ρ_lo`. -/
theorem k17f_qtc1_tie_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 ≤ β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : ⟪P, R⟫ = 0)
    (hζ : ⟪Q, R⟫ = α1 * (κ * ⟪Q, R⟫ + σ * ⟪R, R⟫))
    (hL : ⟪P, Q⟫ < 0 ∨
      β1 * ((β6 - β1) * ⟪P, P⟫ + (1 - κ * α1) * ⟪P, Q⟫ - α1 * σ * ⟪P, R⟫) +
        κ * (α1 - 1) * ((β6 - β1) * ⟪P, Q⟫ + (1 - κ * α1) * ⟪Q, Q⟫ - α1 * σ * ⟪Q, R⟫) < 0)
    (hmem : ∀ i, fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hP0 : P ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  -- depths
  set Za := κ * ⟪Q, R⟫ + σ * ⟪R, R⟫ with hZa
  have hZa0 : Za < 0 := by
    have e : Za * (1 - κ * α1) = σ * ⟪R, R⟫ := by rw [hZa]; linear_combination κ * hζ
    have h1 : 0 < 1 - κ * α1 := by nlinarith [mul_pos nk (by linarith : (0 : ℝ) < α1)]
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hh h1.le, mul_pos (neg_pos.2 hσ) hA]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexC : ∀ v1 v2 : ℝ,
      (v1 * (β6 * ⟪P, P⟫) + v2 * (β6 * ⟪P, Q⟫) < 0 ∨
        v1 * ((β6 - β1) * ⟪P, P⟫ + (1 - κ * α1) * ⟪P, Q⟫ - α1 * σ * ⟪P, R⟫) +
          v2 * ((β6 - β1) * ⟪P, Q⟫ + (1 - κ * α1) * ⟪Q, Q⟫ - α1 * σ * ⟪Q, R⟫) < 0) →
      (∀ i j, ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), R⟫ = ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 j), R⟫ →
        ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), fcomb P Q R v1 v2 0⟫ =
          ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 j), fcomb P Q R v1 v2 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), R⟫)
        (fun i => ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), fcomb P Q R v1 v2 0⟫) := by
    intro v1 v2 hw hinj
    refine k17f_lex_plateau _ _ hinj ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [kmCyc1_0, kmCyc1_1, hz, hBz]; nlinarith [mul_pos a1 (neg_pos.2 hZa0)]
    · simp only [kmCyc1_0, kmCyc1_4, hz, hBz]; nlinarith
    · simp only [kmCyc1_1, kmCyc1_2, hz, hBz]; linarith
    · simp only [kmCyc1_2, kmCyc1_3, hz, hBz]; ring
    · simp only [kmCyc1_3, kmCyc1_4, hz, hBz]; nlinarith [mul_pos (by linarith : (0 : ℝ) < α1) (neg_pos.2 hZa0)]
    · simp only [kmCyc1_1, kmCyc1_2, kmCyc1_3, k17f_wexp, hBz]
      rcases hw with hw | hw
      · left; nlinarith
      · right; rw [hBz] at hw; nlinarith
  rcases hL with hL | hL
  · -- L1 at `ρ_hi = (0,1)`: segment `(-λ ⟪P,Q⟫, ⟪P,P⟫)`
    refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (kmCyc1 κ σ α1 β1 β6)
      (k6t1_km1_inj hκ hα1 hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
      (u1 := 0) (u2 := ⟪P, P⟫) (t1 := -⟪P, Q⟫) (t2 := 0) (lo := 0) (hi := 1) (by nlinarith) (by norm_num)
      (fun v1 v2 => 0 < v1 ∧ κ * (α1 - 1) * v1 < β1 * v2 ∧ v1 * (β6 * ⟪P, P⟫) + v2 * (β6 * ⟪P, Q⟫) < 0)
      ?_ ?_ ?_
    · intro y hy
      rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inl ⟨1, rfl⟩
      · exact Or.inl ⟨2, rfl⟩
      · exact Or.inl ⟨3, rfl⟩
      · exact Or.inl ⟨4, rfl⟩
      · exact Or.inr ⟨_, by simp, rfl⟩
      · exact Or.inr ⟨_, by simp, rfl⟩
    · intro lam h0 h1
      refine ⟨by nlinarith, by nlinarith [mul_pos (mul_pos nk a1) (mul_pos h0 (neg_pos.2 hL))], ?_⟩
      have hb6p : 0 < β6 := by linarith
      nlinarith [mul_pos (mul_pos hb6p hPP) (mul_pos (sub_pos.2 h1) (neg_pos.2 hL))]
    · rintro v1 v2 ⟨hv1, hc, -⟩
      exact k6t1_km1_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
    · rintro v1 v2 ⟨-, -, hw⟩ hinj
      exact hlexC v1 v2 (Or.inl hw) hinj
  · -- L2 at `ρ_lo = (β1, κ(α1-1))`: segment `(β1, κ(α1-1) + λη)`
    set X2 := (β6 - β1) * ⟪P, Q⟫ + (1 - κ * α1) * ⟪Q, Q⟫ - α1 * σ * ⟪Q, R⟫ with hX2
    set G := β1 * ((β6 - β1) * ⟪P, P⟫ + (1 - κ * α1) * ⟪P, Q⟫ - α1 * σ * ⟪P, R⟫) + κ * (α1 - 1) * X2 with hG
    obtain ⟨η, hη, hηx⟩ := k8_eta (x := X2) (y := G) hL.ne
    have hGabs : |G| = -G := abs_of_neg hL
    refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (kmCyc1 κ σ α1 β1 β6)
      (k6t1_km1_inj hκ hα1 hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
      (u1 := β1) (u2 := κ * (α1 - 1)) (t1 := 0) (t2 := η) (lo := 0) (hi := 1) (by nlinarith) (by norm_num)
      (fun v1 v2 => 0 < v1 ∧ κ * (α1 - 1) * v1 < β1 * v2 ∧
        v1 * ((β6 - β1) * ⟪P, P⟫ + (1 - κ * α1) * ⟪P, Q⟫ - α1 * σ * ⟪P, R⟫) + v2 * X2 < 0)
      ?_ ?_ ?_
    · intro y hy
      rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inl ⟨1, rfl⟩
      · exact Or.inl ⟨2, rfl⟩
      · exact Or.inl ⟨3, rfl⟩
      · exact Or.inl ⟨4, rfl⟩
      · exact Or.inr ⟨_, by simp, rfl⟩
      · exact Or.inr ⟨_, by simp, rfl⟩
    · intro lam h0 h1
      refine ⟨by simpa using hβ1, by nlinarith [mul_pos hβ1 (mul_pos h0 hη)], ?_⟩
      have hle : lam * η * X2 ≤ η * |X2| := by
        have := abs_nonneg X2
        have h2 : lam * X2 ≤ |X2| := by
          rcases le_total 0 X2 with hx | hx
          · rw [abs_of_nonneg hx]; nlinarith
          · rw [abs_of_nonpos hx]; nlinarith
        nlinarith
      have e : (β1 + lam * 0) * ((β6 - β1) * ⟪P, P⟫ + (1 - κ * α1) * ⟪P, Q⟫ - α1 * σ * ⟪P, R⟫) +
          (κ * (α1 - 1) + lam * η) * X2 = G + lam * η * X2 := by rw [hG]; ring
      rw [e]; nlinarith [abs_nonneg X2]
    · rintro v1 v2 ⟨hv1, hc, -⟩
      exact k6t1_km1_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
    · rintro v1 v2 ⟨-, -, hw⟩ hinj
      exact hlexC v1 v2 (Or.inr hw) hinj

set_option maxHeartbeats 6400000 in
/-- **S1.1b (template)**: Zdb(i) in the Tc regime.  A cell `(a,d,c,a',c')@a-b'` when `⟪b-d,c-d⟫ < 0` or
`⟪a'-c', β1(α4-1)(b-d) - γ4(α1-1)(c-d)⟫ < 0`; otherwise the leftover (for S1.1a / the new S1.1c' cell). -/
theorem k17f_s11b_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨
      ∃ α1 α4 β1 γ4 β6 : ℝ, c' = d + α1 • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
        a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) ∧ 1 < α1 ∧ 1 < α4 ∧ 0 < β1 ∧ 0 < γ4 ∧
        0 ≤ ⟪b - d, c - d⟫ ∧ 0 ≤ ⟪a' - c', (β1 * (α4 - 1)) • (b - d) - (γ4 * (α1 - 1)) • (c - d)⟫ := by
  obtain ⟨⟨hT, hT', hκc, -⟩, hα4, hζ0, -⟩ := h
  have hfar := k5z_far2 W hT hT'
  have hκb := k5z_kb_pos W hT hT'
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : 1 < α4 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  obtain ⟨μ, hμa, hμb⟩ := gale_pt W hdet hc' hb' ha' (by linarith)
  have hμ : 0 < μ := by
    rw [hμb] at hκb
    have : 0 < β6 * (α1 - 1) := mul_pos hβ6 (by linarith)
    by_contra hh; push Not at hh
    nlinarith
  have hE0 : 0 ≤ α4 - α4 * β1 - α1 + α1 * γ4 := by
    have := W.hκa
    rw [hμa] at this
    exact nonneg_of_mul_nonneg_right this hμ
  obtain ⟨w, hwdef⟩ : ∃ w, w = α4 - 1 := ⟨_, rfl⟩
  have hw : 0 < w := by linarith
  have hb6 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (by linarith : 0 ≤ 1 - β6)]
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = -1 / w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = -γ4 / w := ⟨_, rfl⟩
  have hσw : σ * w = -1 := by rw [hσ]; field_simp
  have hκw : κ * w = -γ4 := by rw [hκ]; field_simp
  have hσ0 : σ < 0 := by rw [hσ]; exact div_neg_of_neg_of_pos (by norm_num) hw
  have hκ0 : κ < 0 := by rw [hκ]; exact div_neg_of_neg_of_pos (by linarith) hw
  have hκ6 : κ * (1 - β6) = 1 := by
    have : (κ * (1 - β6) - 1) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  have hbc : 1 < β1 + κ * α1 * (1 - β6) := by
    have : κ * α1 * (1 - β6) = α1 := by
      calc κ * α1 * (1 - β6) = (κ * (1 - β6)) * α1 := by ring
        _ = α1 := by rw [hκ6]; ring
    linarith
  have hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ) := by
    have : ((σ - 1) * (1 - β1) - α1 * (σ - κ)) * w ≤ 0 := by nlinarith
    by_contra hh; push Not at hh
    nlinarith [mul_pos (sub_pos.2 hh) hw]
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := a - b' with hR
  have hRv : R = (-w) • p - γ4 • r := by
    rw [hR, hb', hp, hr, hwdef]; module
  have hpR : p = σ • R + κ • r := by
    rw [hRv]
    match_scalars <;> nlinarith
  have hΔ : det3 q r R ≠ 0 := by
    have e : det3 q r R = (-w) * det3 p q r := by
      rw [hRv]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (neg_ne_zero.2 hw.ne') hdet
  have hfp : ∀ x y z : ℝ, fpoint q r R d (x, y, z) = d + x • q + y • r + z • R := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint q r R d (0, 0, 0) = d := by rw [hfp]; simp
  have eB : fpoint q r R d (1, 0, 0) = b := by rw [hfp, hq]; module
  have eC : fpoint q r R d (0, 1, 0) = c := by rw [hfp, hr]; module
  have eA : fpoint q r R d (0, κ, σ) = a := by
    rw [hfp]; have h := hpR; rw [hp] at h
    linear_combination (norm := module) (-1 : ℝ) • h
  have eB' : fpoint q r R d (0, κ, σ - 1) = b' := by
    rw [hfp]; have h := hpR; rw [hp] at h
    linear_combination (norm := module) (-1 : ℝ) • h + (1 : ℝ) • hR
  have eC' : fpoint q r R d (β1, κ * α1, α1 * σ) = c' := by
    rw [hfp, hc']; have h := hpR; rw [hp] at h
    linear_combination (norm := module) (-α1) • h
  have eA' : fpoint q r R d (β6, 1, 0) = a' := by
    rw [hfp, ha']; module
  have hRne : R ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hB0 : ⟪q, R⟫ = 0 := by
    have e : ⟪q, R⟫ = -⟪d - b, a - b'⟫ := by rw [hq, hR, ← inner_neg_left]; congr 1; abel
    rw [e, hζ0]; simp
  have hcc : ⟪c' - c, a - b'⟫ = α1 * (κ * ⟪r, R⟫ + σ * ⟪R, R⟫) - ⟪r, R⟫ := by
    have e : c' - c = β1 • q + (κ * α1 - 1) • r + (α1 * σ) • R := by
      have h : p = σ • R + κ • r := hpR
      have hc : c = d + r := by rw [hr]; abel
      rw [hc', hc]
      linear_combination (norm := module) α1 • h
    rw [e, ← hR, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, hB0]
    ring
  have hζ : ⟪r, R⟫ = α1 * (κ * ⟪r, R⟫ + σ * ⟪R, R⟫) := by rw [hcc] at hz1; linarith
  -- the literal in frame atoms
  have hac : a' - c' = (β6 - β1) • q + (1 - κ * α1) • r + (-(α1 * σ)) • R := by
    rw [← eA', ← eC', hfp, hfp]; module
  have hX1 : ⟪a' - c', q⟫ = (β6 - β1) * ⟪q, q⟫ + (1 - κ * α1) * ⟪q, r⟫ - α1 * σ * ⟪q, R⟫ := by
    rw [hac]; simp only [inner_add_left, real_inner_smul_left]; rw [real_inner_comm r q, real_inner_comm R q]; ring
  have hX2 : ⟪a' - c', r⟫ = (β6 - β1) * ⟪q, r⟫ + (1 - κ * α1) * ⟪r, r⟫ - α1 * σ * ⟪r, R⟫ := by
    rw [hac]; simp only [inner_add_left, real_inner_smul_left]; rw [real_inner_comm R r]; ring
  have hGw : ⟪a' - c', (β1 * (α4 - 1)) • (b - d) - (γ4 * (α1 - 1)) • (c - d)⟫ =
      w * (β1 * ((β6 - β1) * ⟪q, q⟫ + (1 - κ * α1) * ⟪q, r⟫ - α1 * σ * ⟪q, R⟫) +
        κ * (α1 - 1) * ((β6 - β1) * ⟪q, r⟫ + (1 - κ * α1) * ⟪r, r⟫ - α1 * σ * ⟪r, R⟫)) := by
    rw [← hq, ← hr, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hX1, hX2, ← hwdef]
    linear_combination (-(α1 - 1) * ((β6 - β1) * ⟪q, r⟫ + (1 - κ * α1) * ⟪r, r⟫ - α1 * σ * ⟪r, R⟫)) * hκw
  by_cases hL : ⟪q, r⟫ < 0 ∨ ⟪a' - c', (β1 * (α4 - 1)) • (b - d) - (γ4 * (α1 - 1)) • (c - d)⟫ < 0
  · left
    refine ⟨R, hRne, k17f_qtc1_tie_frame (V8 a a' b b' c c' d) q r R d hΔ hκ0 hσ0 hα11 hβ1 hb6.le hbc hE
      hB0 hζ ?_ ?_ ?_⟩
    · rcases hL with hL | hL
      · exact Or.inl hL
      · right
        rw [hGw] at hL
        by_contra hh; push Not at hh
        nlinarith [mul_nonneg hw.le hh]
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kmCyc1_0, eA]; simp [V8]
      · simp only [kmCyc1_1, eC']; simp [V8]
      · simp only [kmCyc1_2, eA']; simp [V8]
      · simp only [kmCyc1_3, eC]; simp [V8]
      · simp only [kmCyc1_4, eO]; simp [V8]
    · intro y hy
      rw [eA, eC', eA', eC, eO, eB, eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · right
    push Not at hL
    exact ⟨α1, α4, β1, γ4, β6, hc', hb', ha', hα11, hα41, hβ1, hγ4, hL.1, hL.2⟩

/-- On the Zdb(i) tie (`ζ(d,b) = ζ(c',c) = 0`, T frame) the ray literal `G` is `(α4-1) ζ_{a-c'}(c',a')`. -/
theorem k17f_s11_G {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ}
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hζ0 : ⟪d - b, a - b'⟫ = 0) (hz1 : ⟪c' - c, a - b'⟫ = 0) :
    ⟪a' - c', (β1 * (α4 - 1)) • (b - d) - (γ4 * (α1 - 1)) • (c - d)⟫ = (α4 - 1) * ⟪c' - a', a - c'⟫ := by
  have e1 : (β1 * (α4 - 1)) • (b - d) - (γ4 * (α1 - 1)) • (c - d) =
      (-(α4 - 1)) • (a - c') + (α1 - 1) • (a - b') := by
    rw [hc', hb']; module
  have e2 : a' - c' = β6 • (-(d - b)) - (c' - c) := by rw [ha']; module
  have h3 : ⟪a' - c', a - b'⟫ = 0 := by
    rw [e2, inner_sub_left, inner_smul_left, inner_neg_left, hζ0, hz1]; simp
  rw [e1, inner_add_right, real_inner_smul_right, real_inner_smul_right, h3, ← neg_sub c' a', inner_neg_left]
  ring

/-- **S1.1 (Tc), K15 literals**: a cell, or `⟪b-d,c-d⟫ ≥ 0 ∧ ζ_{a-c'}(c',a') ≥ 0` (then S1.1a at `d-b` if
`ζ_{c'-b}(d,b) > 0`, else the S1.1c cell `(a,d,b,a',b')@a-c'`). -/
theorem k17f_s11_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ (0 ≤ ⟪b - d, c - d⟫ ∧ 0 ≤ ⟪c' - a', a - c'⟫) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.1
  rcases k17f_s11b_tc W h hz1 with h1 | ⟨α1, α4, β1, γ4, β6, hc', hb', ha', hα1, hα4, -, -, hq, hG⟩
  · exact Or.inl h1
  · right
    refine ⟨hq, ?_⟩
    rw [k17f_s11_G hc' hb' ha' hζ0 hz1] at hG
    by_contra hh; push Not at hh
    nlinarith [mul_pos (sub_pos.2 hα4) (neg_pos.2 hh)]

end C2
end Type08Sp
end Minimality
