module

public import Minimality.Type08S.C2K33EE
public import Minimality.Type08S.C2K33ZA
public import Minimality.Type08S.G3p
public import Minimality.OctAxis

@[expose] public section

set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality
namespace Type08Sp
open C2

/-- Identity (I2): at X4 = 0, (α1+β1-1) L = - X3 * H. -/
theorem k41_Lid {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (hX4 : ⟪c' - a, b' - c⟫ = 0) :
    (α1 + β1 - 1) * ⟪a - a', k28l2aU0 a b c d α1 β1⟫ =
      -(⟪a - c', a - b'⟫ * ⟪c' - a', b' - c⟫) := by
  obtain ⟨hPR, hpp, hqq, hrr⟩ := k32e_facts hC hM
  have hα : 1 < α1 := hH1.1.1
  have hβ : 1 < β1 := hH1.1.2.1
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  have e1 : c' - a' = α1 • (a - d) + (β1 - β6) • (b - d) + (-γ6) • (c - d) := by
    rw [hc', ha']; module
  have e2 : b' - c = α1 • (a - d) + (0:ℝ) • (b - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  have e5 : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e6 : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e7 : a - b' = (1 - α1) • (a - d) + (0:ℝ) • (b - d) + (-β1) • (c - d) := by rw [hb']; module
  have e8 : a - a' = (1:ℝ) • (a - d) + (-β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  rw [e1, e2]; rw [e6, e7]
  rw [e5, e2] at hX4
  rw [e8, k32e_U, k32e_ip _ _ _ hPR]
  rw [k32e_ip _ _ _ hPR] at hX4 ⊢
  rw [k32e_ip _ _ _ hPR]
  have hW : 0 < ⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫ := by linarith
  have := k32e_core_x4 α1 β1 β6 γ6 _ _ _ _ _ hα hβ
    (by have := hrel.1; linarith) hW hX4
  linarith

/-- C2 splits: X3 = 0, or X3 < 0 and H = 0. -/
theorem k41_c2_split {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (_hL2 : K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6) (hne : ⟪c - a', a - b'⟫ ≠ 0)
    (h4 : ⟪c' - a, b' - c⟫ = 0) (hl : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0) :
    ⟪a - c', a - b'⟫ = 0 ∨ (⟪a - c', a - b'⟫ < 0 ∧ ⟪c' - a', b' - c⟫ = 0) := by
  have hX3 : ⟪a - c', a - b'⟫ ≤ 0 := by
    rcases hH1.2.2 with h0 | h0
    · exact (hne h0).elim
    · exact h0.2
  have hid := k41_Lid hC hM hrel hH1 h4
  rw [hl] at hid
  rcases lt_or_eq_of_le hX3 with h | h
  · right; refine ⟨h, ?_⟩
    have : ⟪a - c', a - b'⟫ * ⟪c' - a', b' - c⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' h.ne
    · exact h'
  · exact Or.inl h


/-- Pure real core: on the R0 locus (X4 = 0, H = 0, X3 < 0, z(c) <= z(a')) one has
`β6 (α1-1) <= β1 (γ6-1)`. -/
theorem k58_core (α β b g pp s qq qr rr : ℝ) (hα : 1 < α) (hβ : 1 < β) (hg : 0 < g)
    (hqq : qr < qq) (hrr : qr < rr) (hD : 0 < qq * rr - qr ^ 2)
    (hrel : α * s * (qq + rr - 2 * qr) = -(β - 1) * (qq * rr - qr ^ 2))
    (hX4 : k32e_G pp s qq qr rr (α - 1) β 0 α 0 (β - 1) = 0)
    (hH : k32e_G pp s qq qr rr α (β - b) (-g) α 0 (β - 1) = 0)
    (hX3 : k32e_G pp s qq qr rr (1 - α) (-β) 0 (1 - α) 0 (-β) < 0)
    (hz : k32e_G pp s qq qr rr 0 (-b) (1 - g) ((1 - α) * s - β * qr) 0 (-((1 - α) * pp - β * s)) ≤ 0) :
    b * (α - 1) ≤ β * (g - 1) := by
  have hα0 : α ≠ 0 := by linarith
  have hα1 : α - 1 ≠ 0 := by linarith
  have hW : 0 < qq + rr - 2 * qr := by linarith
  have hWne : qq + rr - 2 * qr ≠ 0 := hW.ne'
  have hWne2 : qq + rr - qr * 2 ≠ 0 := by intro h; linarith
  have hy : 0 < rr - qr := by linarith
  have hx : 0 < qq - qr := by linarith
  have hs : s = -(β - 1) * (qq * rr - qr ^ 2) / (α * (qq + rr - 2 * qr)) := by
    rw [eq_div_iff (mul_ne_zero hα0 hW.ne')]; linear_combination hrel
  have hpp : pp = -((α * β + (α - 1) * (β - 1)) * s + β * (β - 1) * qr) / (α * (α - 1)) := by
    rw [eq_div_iff (mul_ne_zero hα0 hα1)]; simp only [k32e_G] at hX4; linear_combination hX4
  have hHk : k32e_G pp s qq qr rr α (β - b) (-g) α 0 (β - 1) =
      -(β - 1) * (rr - qr) / ((α - 1) * (qq + rr - 2 * qr)) *
        ((α - 1) * (g * (rr - qr) - b * (qq - qr)) - β * (qq - qr)) := by
    simp only [k32e_G]; rw [hpp, hs]; field_simp; ring
  have hX3k : k32e_G pp s qq qr rr (1 - α) (-β) 0 (1 - α) 0 (-β) =
      (α + β - 1) / α * ((α - 1) * s + β * qr) := by
    simp only [k32e_G]; rw [hpp]; field_simp; ring
  have hzk : k32e_G pp s qq qr rr 0 (-b) (1 - g) ((1 - α) * s - β * qr) 0 (-((1 - α) * pp - β * s)) =
      -(((α - 1) * s + β * qr) / α) *
        ((β - 1) * (rr - qr) * (b * (qq - qr) + (1 - g) * (rr - qr)) / (qq + rr - 2 * qr)) := by
    simp only [k32e_G]; rw [hpp, hs]; field_simp; ring
  have hN : (α - 1) * s + β * qr < 0 := by
    rw [hX3k] at hX3
    have : 0 < (α + β - 1) / α := by apply div_pos <;> linarith
    by_contra h; push Not at h; nlinarith
  rw [hzk] at hz
  have hZ : (β - 1) * (rr - qr) * (b * (qq - qr) + (1 - g) * (rr - qr)) / (qq + rr - 2 * qr) ≤ 0 := by
    have h1 : 0 < -(((α - 1) * s + β * qr) / α) := by
      have := div_neg_of_neg_of_pos hN (by linarith : (0:ℝ) < α); linarith
    by_contra h; push Not at h; nlinarith
  have hZ2 : b * (qq - qr) + (1 - g) * (rr - qr) ≤ 0 := by
    have h1 : 0 < (β - 1) * (rr - qr) := by apply mul_pos <;> linarith
    have h2 : (β - 1) * (rr - qr) * (b * (qq - qr) + (1 - g) * (rr - qr)) ≤ 0 := by
      by_contra h; push Not at h
      have := div_pos h hW; linarith
    by_contra h; push Not at h; nlinarith
  rw [hHk] at hH
  have hk : -(β - 1) * (rr - qr) / ((α - 1) * (qq + rr - 2 * qr)) ≠ 0 := by
    apply div_ne_zero
    · have : 0 < (β - 1) * (rr - qr) := by apply mul_pos <;> linarith
      linarith
    · exact mul_ne_zero hα1 hW.ne'
  have hH2 : (α - 1) * (g * (rr - qr) - b * (qq - qr)) - β * (qq - qr) = 0 :=
    (mul_eq_zero.1 hH).resolve_left hk
  -- (α-1) y <= β x
  have hyx : (α - 1) * (rr - qr) ≤ β * (qq - qr) := by nlinarith
  -- multiply target by x
  have : (b * (α - 1) - β * (g - 1)) * (qq - qr) ≤ 0 := by nlinarith
  by_contra h; push Not at h; nlinarith


/-- The R0 branch of C2 forces `κ_b = 0` (the Gale sign `κ_b ≥ 0` gives only `≥`, the branch `≤`). -/
theorem k83_r0_gWb {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (W : Norm08w a a' b b' c c' d)
    (hs : K6sMN2 a a' b b' c c' d) (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (h4 : ⟪c' - a, b' - c⟫ = 0)
    (hzc : ⟪c, k28l2aU0 a b c d α1 β1⟫ ≤ ⟪a', k28l2aU0 a b c d α1 β1⟫)
    (hX3 : ⟪a - c', a - b'⟫ < 0) (hH : ⟪c' - a', b' - c⟫ = 0) :
    β6 * (α1 - 1) = β1 * (γ6 - 1) := by
  obtain ⟨hα, hβ, hσ, hβ6, hγ6⟩ := hH1.1
  have hrel : K16Rel a b c d α1 β1 := by
    obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
    exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ hγ6' h3
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, -, -⟩ := hC
  have hPR : ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ := by
    have h0 := hs.2.2.1
    have : b - c = (b - d) - (c - d) := by abel
    rw [this, inner_sub_right] at h0; linarith
  have hM1 := hs.2.2.2.1
  have hM2 := hs.2.2.2.2
  have e1 : c' - a' = α1 • (a - d) + (β1 - β6) • (b - d) + (-γ6) • (c - d) := by
    rw [hc', ha']; module
  have e2 : b' - c = α1 • (a - d) + (0 : ℝ) • (b - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  have e5 : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) + (0 : ℝ) • (c - d) := by rw [hc']; module
  have e6 : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) + (0 : ℝ) • (c - d) := by rw [hc']; module
  have e7 : a - b' = (1 - α1) • (a - d) + (0 : ℝ) • (b - d) + (-β1) • (c - d) := by rw [hb']; module
  have e8 : c - a' = (0 : ℝ) • (a - d) + (-β6) • (b - d) + (1 - γ6) • (c - d) := by rw [ha']; module
  have e9 : c' - d = α1 • (a - d) + β1 • (b - d) + (0 : ℝ) • (c - d) := by rw [hc']; module
  have e10 : b' - d = α1 • (a - d) + (0 : ℝ) • (b - d) + β1 • (c - d) := by rw [hb']; module
  have e11 : b - c = (0 : ℝ) • (a - d) + (1 : ℝ) • (b - d) + (-1 : ℝ) • (c - d) := by module
  have hU : k28l2aU0 a b c d α1 β1 = ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) • (a - d) +
      (0 : ℝ) • (b - d) + (-((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫)) • (c - d) := by
    unfold k28l2aU0; module
  have hzc' : ⟪c - a', k28l2aU0 a b c d α1 β1⟫ ≤ 0 := by
    rw [inner_sub_left]; linarith
  rw [e9, e11, k32e_ip _ _ _ hPR] at hM1
  rw [e10, e11, k32e_ip _ _ _ hPR] at hM2
  rw [e5, e2, k32e_ip _ _ _ hPR] at h4
  rw [e1, e2, k32e_ip _ _ _ hPR] at hH
  rw [e6, e7, k32e_ip _ _ _ hPR] at hX3
  rw [e8, hU, k32e_ip _ _ _ hPR] at hzc'
  simp only [k32e_G] at hM1 hM2
  have hβpos : 0 < β1 := by linarith
  have hqq1 : ⟪b - d, c - d⟫ < ⟪b - d, b - d⟫ := by
    have : 0 < β1 * (⟪b - d, b - d⟫ - ⟪b - d, c - d⟫) := by linarith
    have := pos_of_mul_pos_right this hβpos.le
    linarith
  have hrr1 : ⟪b - d, c - d⟫ < ⟪c - d, c - d⟫ := by
    have : 0 < β1 * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) := by linarith
    have := pos_of_mul_pos_right this hβpos.le
    linarith
  have hcore := k58_core α1 β1 β6 γ6 ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫
    ⟪c - d, c - d⟫ hα hβ (by linarith) hqq1 hrr1 hrel.2 hrel.1 h4 hH hX3 hzc'
  -- Gale
  obtain ⟨μ, hμ0, -, hμb, -, hμU⟩ := gale_nf08w W.G (p := α1) (q := β1) (r := α1) (s := β1)
    (t := β6) (u := γ6) hdet hc' hb' ha' (by linarith)
  have hbc : galeD W.G.l W.G.m b c ≠ 0 := galeD_ne_zero W.F.perm₁₂.perm₂₃ W.G.perm₁₂.perm₂₃
  have hUle := W.hU
  have hkb := W.hκb
  rw [hμU] at hUle hbc
  rw [hμb] at hkb
  simp only [gWU, gWb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at hUle hbc hkb
  have hneg : β1 * (β6 * (1 - α1 - β1) + γ6 * (1 - α1 - β1) - β1 * (1 - β6 - γ6)) < 0 := by
    have h1 : 0 < (α1 - 1) * (β6 + γ6) + β1 := by
      have : 0 < (α1 - 1) * (β6 + γ6) := mul_pos (by linarith) (by linarith)
      linarith
    nlinarith [mul_pos hβpos h1]
  have hμpos : 0 < μ := by
    rcases lt_or_gt_of_ne hμ0 with h | h
    · exfalso
      have := mul_pos_of_neg_of_neg h hneg
      apply hbc
      nlinarith
    · exact h
  have hgb : β1 * (1 - β6 - γ6) - β6 * (1 - α1 - β1) = 0 := by
    have : 0 ≤ μ * (β1 * (1 - β6 - γ6) - β6 * (1 - α1 - β1)) := hkb
    have h2 : β1 * (1 - β6 - γ6) - β6 * (1 - α1 - β1) ≤ 0 := by nlinarith
    have h3 := nonneg_of_mul_nonneg_right this hμpos
    linarith
  linarith


theorem k83_Uip {a b c d : ℝ³} {α1 β1 : ℝ} (hPR : ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫) :
    ⟪k28l2aU0 a b c d α1 β1, a - d⟫ = -β1 * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) ∧
    ⟪k28l2aU0 a b c d α1 β1, b - d⟫ = (α1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) ∧
    ⟪k28l2aU0 a b c d α1 β1, c - d⟫ = ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) * ⟪a - d, b - d⟫
      + ((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫) * (-⟪c - d, c - d⟫) := by
  rw [k32e_U]
  refine ⟨?_, ?_, ?_⟩
  · rw [k32e_ipP _ _ _ hPR]; ring
  · rw [k32e_ipQ _ _ _ hPR]; ring
  · rw [k32e_ipR _ _ _ hPR]; ring

theorem k83_I2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d) :
    γ6 * ⟪c - a', k28l2aU0 a b c d α1 β1⟫ = (γ6 - 1) * ⟪a - a', k28l2aU0 a b c d α1 β1⟫ -
      (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) * (β6 * (α1 - 1) - β1 * (γ6 - 1)) := by
  obtain ⟨hPR, -, -, -⟩ := k32e_facts hC hM
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, -, -⟩ := hC
  have e8 : c - a' = (0:ℝ) • (a - d) + (-β6) • (b - d) + (1 - γ6) • (c - d) := by rw [ha']; module
  have e9 : a - a' = (1:ℝ) • (a - d) + (-β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  rw [e8, e9, k32e_U, k32e_ip _ _ _ hPR, k32e_ip _ _ _ hPR]
  simp only [k32e_G]; ring

theorem k83_U0zero {a b c d : ℝ³} {α1 β1 : ℝ} (hPR : ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫)
    (h1 : ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2 = 0)
    (h2 : ⟪k28l2aU0 a b c d α1 β1, c - d⟫ = 0) : k28l2aU0 a b c d α1 β1 = 0 := by
  obtain ⟨i1, i2, -⟩ := k83_Uip (α1 := α1) (β1 := β1) hPR
  rw [h1] at i1
  have h3 : ⟪k28l2aU0 a b c d α1 β1, k28l2aU0 a b c d α1 β1⟫ = 0 := by
    nth_rewrite 2 [k32e_U]
    simp only [inner_add_right, real_inner_smul_right, i1, h2, zero_smul, inner_zero_right]
    ring
  exact inner_self_eq_zero.1 h3

theorem k83_C1 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hα : 1 < α1) (hβ : 1 < β1) (h3 : ⟪a - c', a - b'⟫ = 0) (h4 : ⟪c' - a, b' - c⟫ = 0) : k28l2aU0 a b c d α1 β1 = 0 := by
  obtain ⟨hPR, -, -, -⟩ := k32e_facts hC hM
  obtain ⟨hdet, hc', hb', ha', hs1, -, -, -, -, -⟩ := hC
  have e2 : b' - c = α1 • (a - d) + (0:ℝ) • (b - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  have e5 : c' - a = (α1 - 1) • (a - d) + β1 • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e6 : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
  have e7 : a - b' = (1 - α1) • (a - d) + (0:ℝ) • (b - d) + (-β1) • (c - d) := by rw [hb']; module
  rw [e5, e2, k32e_ip _ _ _ hPR] at h4
  rw [e6, e7, k32e_ip _ _ _ hPR] at h3
  simp only [k32e_G] at h3 h4
  rw [k32e_U]
  have E3 : (α1 - 1) * ((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫) +
      β1 * ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) = 0 := by linear_combination (-1:ℝ) * h3
  have E4 : α1 * ((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫) +
      (β1 - 1) * ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) = 0 := by linear_combination (-1:ℝ) * h4
  have hd : (1 - α1 - β1) ≠ 0 := by intro h; linarith
  have hmp : (1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫ = 0 := by
    have : ((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫) * (1 - α1 - β1) = 0 := by
      linear_combination (β1 - 1) * E3 - β1 * E4
    exact (mul_eq_zero.1 this).resolve_right hd
  have hmr : (1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫ = 0 := by
    have : ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) * (1 - α1 - β1) = 0 := by
      linear_combination (-α1) * E3 + (α1 - 1) * E4
    exact (mul_eq_zero.1 this).resolve_right hd
  rw [hmp, hmr]; simp
