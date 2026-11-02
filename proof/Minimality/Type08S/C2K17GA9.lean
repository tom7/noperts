module

public import Minimality.Type08S.C2K17GA8

@[expose] public section


/-!
# K17GA / GA9: S1.2b (Zdb(ii), `ζ_{a-c'}(a,d) < 0`): cell `(a,d,c,a',c')@a-b'`, two plateaus
Frame of `k6t4_zdb_core` (`P = b-d, Q = c-d, R = a-b'`), cycle `kmCyc1 = (a, c', a', c, d)`.  With `⟪P,R⟫ = 0` and
`z(a) = z(d)` the depths are `a = d = c'` (high) and `a' = c` (low).  Tilt near the ray `(0,1)`: `(λ η, 1)`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
/-- Cycle `0..4 = (a, c', a', c, d)`: high plateau `d = a = c'` (4, 0, 1), low plateau `a' = c` (2, 3),
and `a` is not the `w`-valley of the high plateau. -/
theorem k17ga_lex_2plat (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h40 : z 4 = z 0) (h01 : z 0 = z 1) (h23 : z 2 = z 3) (h21 : z 2 < z 1)
    (hw : w 1 < w 0) : LexUni z w := by
  have tot : ∀ i j : ZMod 5, i ≠ j → LexLt (z i, w i) (z j, w j) ∨ LexLt (z j, w j) (z i, w i) := by
    intro i j hij
    apply lexLt_total
    intro h; exact hij (hinj i j (congrArg Prod.fst h) (congrArg Prod.snd h))
  have le : ∀ i j, LexLt (z i, w i) (z j, w j) → z i ≤ z j := fun i j h => lexLt_fst_le' h
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17f_zsub
  have h34 : z 3 < z 4 := by linarith
  -- a (0) is a peak iff w4 < w0 ; otherwise 1 is the peak
  have L10 : LexLt (z 1, w 1) (z 0, w 0) := Or.inr ⟨h01.symm, hw⟩
  rcases tot 4 0 (by decide) with h40' | h04
  · refine k17f_lexUni5_of_peak z w hinj 0 ?_ ?_
    · simp only [t0, s0]; exact ⟨h40', L10⟩
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · simp only [t1, s1]; rintro ⟨h, -⟩; exact lexLt_asymm L10 h
      · simp only [t2, s2]; rintro ⟨h, -⟩; have := le _ _ h; linarith
      · simp only [t3, s3]; rintro ⟨-, h⟩; have := le _ _ h; linarith
      · simp only [t4, s4]; rintro ⟨-, h⟩; exact lexLt_asymm h40' h
  · refine k17f_lexUni5_of_peak z w hinj 4 ?_ ?_
    · simp only [t4, s4]; exact ⟨Or.inl h34, h04⟩
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0]; rintro ⟨h, -⟩; exact lexLt_asymm h04 h
      · simp only [t1, s1]; rintro ⟨h, -⟩; exact lexLt_asymm L10 h
      · simp only [t2, s2]; rintro ⟨h, -⟩; have := le _ _ h; linarith
      · simp only [t3, s3]; rintro ⟨-, h⟩; have := le _ _ h; linarith
      · exact absurd rfl hi

set_option maxHeartbeats 3200000 in
/-- **S1.2b frame cell** `(a, d, c, a', c')` at `R = a - b'` on the Zdb(ii) tie (`⟪P,R⟫ = 0`, `z(a) = z(d)`), given
`w(a) > w(c')` at the ray `(0,1)`: `X2' := ⟪a - c', Q⟫ > 0`. -/
theorem k17ga_qtc1_zd_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 ≤ β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : ⟪P, R⟫ = 0) (hZa : κ * ⟪Q, R⟫ + σ * ⟪R, R⟫ = 0)
    (hL : 0 < -β1 * ⟪P, Q⟫ + κ * (1 - α1) * ⟪Q, Q⟫ + σ * (1 - α1) * ⟪Q, R⟫)
    (hmem : ∀ i, fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have hy : ⟪Q, R⟫ < 0 := by nlinarith [mul_pos (neg_pos.2 hσ) hA]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  set X1 := -β1 * ⟪P, P⟫ + κ * (1 - α1) * ⟪P, Q⟫ with hX1
  set X2 := -β1 * ⟪P, Q⟫ + κ * (1 - α1) * ⟪Q, Q⟫ + σ * (1 - α1) * ⟪Q, R⟫ with hX2
  obtain ⟨η, hη, hηx⟩ := k8_eta (x := X1) (y := X2) hL.ne'
  have hXabs : |X2| = X2 := abs_of_pos hL
  have hlexC : ∀ v1 v2 : ℝ, 0 < v1 * X1 + v2 * X2 →
      (∀ i j, ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), R⟫ = ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 j), R⟫ →
        ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), fcomb P Q R v1 v2 0⟫ =
          ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 j), fcomb P Q R v1 v2 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), R⟫)
        (fun i => ⟪fpoint P Q R d (kmCyc1 κ σ α1 β1 β6 i), fcomb P Q R v1 v2 0⟫) := by
    intro v1 v2 hw hinj
    refine k17ga_lex_2plat _ _ hinj ?_ ?_ ?_ ?_ ?_
    · simp only [kmCyc1_0, kmCyc1_4, hz, hBz]; linarith
    · simp only [kmCyc1_0, kmCyc1_1, hz, hBz]; nlinarith
    · simp only [kmCyc1_2, kmCyc1_3, hz, hBz]; ring
    · simp only [kmCyc1_1, kmCyc1_2, hz, hBz]; nlinarith
    · simp only [kmCyc1_0, kmCyc1_1, k17f_wexp, hBz]; nlinarith
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (kmCyc1 κ σ α1 β1 β6)
    (k6t1_km1_inj hκ hα1 hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)] ?_
    (u1 := 0) (u2 := 1) (t1 := η) (t2 := 0) (lo := 0) (hi := 1) (by nlinarith) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ κ * (α1 - 1) * v1 < β1 * v2 ∧ 0 < v1 * X1 + v2 * X2) ?_ ?_ ?_
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
    refine ⟨by simpa using mul_pos h0 hη, by nlinarith [mul_pos (mul_pos nk a1) (mul_pos h0 hη)], ?_⟩
    have hle : -(η * |X1|) ≤ lam * η * X1 := by
      have h2 : -|X1| ≤ lam * X1 := by
        rcases le_total 0 X1 with hx | hx
        · rw [abs_of_nonneg hx]; nlinarith
        · rw [abs_of_nonpos hx]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hη.le]
    have e : (0 + lam * η) * X1 + (1 + lam * 0) * X2 = lam * η * X1 + X2 := by ring
    rw [e]; rw [hXabs] at hηx; nlinarith [abs_nonneg X1]
  · rintro v1 v2 ⟨hv1, hc, -⟩
    exact k6t1_km1_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
  · rintro v1 v2 ⟨-, -, hw⟩ hinj
    exact hlexC v1 v2 hw hinj

set_option maxHeartbeats 6400000 in
/-- **S1.2b core**: Zdb(ii) (`ζ(d,b) = 0`, `z(a) = z(d)` at `a - b'`) with `ζ_{a-c'}(a,d) = ⟪a-d,a-c'⟫ < 0`:
the cell `(a,d,c,a',c')@a-b'`. -/
theorem k17ga_s12b_core {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d))
    (hα11 : 1 < α1) (hα41 : 1 < α4) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hb6 : 1 ≤ β6)
    (hbc0 : 1 < β1 + (-γ4 / (α4 - 1)) * α1 * (1 - β6))
    (hE0 : 0 ≤ α4 - α4 * β1 - α1 + α1 * γ4) (hζ0 : ⟪d - b, a - b'⟫ = 0)
    (hZ : ⟪a - d, a - b'⟫ = 0) (hlit : ⟪a - d, a - c'⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = α4 - 1 := ⟨_, rfl⟩
  have hw : 0 < w := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = -1 / w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = -γ4 / w := ⟨_, rfl⟩
  have hσw : σ * w = -1 := by rw [hσ]; field_simp
  have hκw : κ * w = -γ4 := by rw [hκ]; field_simp
  have hσ0 : σ < 0 := by rw [hσ]; exact div_neg_of_neg_of_pos (by norm_num) hw
  have hκ0 : κ < 0 := by rw [hκ]; exact div_neg_of_neg_of_pos (by linarith) hw
  have hκσ : κ = σ * γ4 := by
    have : (κ - σ * γ4) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  have hbc : 1 < β1 + κ * α1 * (1 - β6) := by rw [hκ, hwdef]; exact hbc0
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
  have hBR : ⟪q, R⟫ = -⟪d - b, a - b'⟫ := by
    rw [hq, hR, ← inner_neg_left]; congr 1; abel
  have hRne : R ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine ⟨R, hRne, ?_⟩
  have hB0 : ⟪q, R⟫ = 0 := by rw [hBR, hζ0]; simp
  have haa : ⟪a - d, a - b'⟫ = κ * ⟪r, R⟫ + σ * ⟪R, R⟫ := by
    rw [← hR, ← hp, hpR, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [real_inner_comm R r]; ring
  have hZa : κ * ⟪r, R⟫ + σ * ⟪R, R⟫ = 0 := by rw [← haa]; exact hZ
  have hac : a - c' = (-β1) • q + (κ * (1 - α1)) • r + (σ * (1 - α1)) • R := by
    have h : p = σ • R + κ • r := hpR
    rw [hc']
    have : a - (d + α1 • (a - d) + β1 • (b - d)) = (1 - α1) • p - β1 • q := by rw [hp, hq]; module
    rw [this, h]; module
  have hL : 0 < -β1 * ⟪q, r⟫ + κ * (1 - α1) * ⟪r, r⟫ + σ * (1 - α1) * ⟪r, R⟫ := by
    have h1 : ⟪a - c', r⟫ = -β1 * ⟪q, r⟫ + κ * (1 - α1) * ⟪r, r⟫ + σ * (1 - α1) * ⟪r, R⟫ := by
      rw [hac, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm R r]
    rw [← h1]
    have h2 : ⟪a - d, a - c'⟫ = κ * ⟪a - c', r⟫ := by
      rw [h1, ← hp, hpR]
      conv_lhs => rw [hac]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm q R, real_inner_comm q r, real_inner_comm r R]
      linear_combination (-σ * β1) * hB0 + σ * (1 - α1) * hZa
    nlinarith

  refine k17ga_qtc1_zd_frame (V8 a a' b b' c c' d) q r R d hΔ hκ0 hσ0 hα11 hβ1 hb6 hbc hE hB0 hZa hL ?_ ?_
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

end C2
end Type08Sp
end Minimality
