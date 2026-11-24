module

public import Minimality.ThinArc
public import Minimality.ThinBox
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Assembly of "thin solid => BoxApplies" (THIN-LEAN-SPEC.md 2.0, 2.1, 2.2).
L3 and L4 (exists_dir_small_dots, exists_line_fit) are in Minimality/ThinArc.lean. -/

@[expose] public section

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-! ## Definitions of 2.0 not in ThinBox -/

/-- Perpendicular offset of `v` from the line through `p` with direction `q - p`. -/
noncomputable def lineOffset (p q v : ℝ³) : ℝ³ :=
  (v - p) - (⟪q - p, v - p⟫ / ‖q - p‖ ^ 2) • (q - p)

/-- Chord from `j` to the segment `i k` at the level of `j` (levels `⟪a, ·⟫`; draft 8.1). -/
noncomputable def chordVec (a i j k : ℝ³) : ℝ³ :=
  j - ((⟪a, k⟫ - ⟪a, j⟫) / (⟪a, k⟫ - ⟪a, i⟫)) • i - ((⟪a, j⟫ - ⟪a, i⟫) / (⟪a, k⟫ - ⟪a, i⟫)) • k

noncomputable def needleKappa (N : ℕ) : ℝ := 1 / (2 * ((N : ℝ) ^ 3 + 1) ^ 2)
noncomputable def plateKappa (N : ℕ) : ℝ := 1 / (2 * ((N : ℝ) ^ 2 + 1) ^ 2)
noncomputable def thinAlpha (N : ℕ) : ℝ := needleKappa N * plateKappa N / 33
/-! ## Helpers -/

theorem inner_chordVec (a m i j k : ℝ³) :
    ⟪m, chordVec a i j k⟫ = ⟪m, j⟫ - ((⟪a, k⟫ - ⟪a, j⟫) * ⟪m, i⟫ + (⟪a, j⟫ - ⟪a, i⟫) * ⟪m, k⟫)
      / (⟪a, k⟫ - ⟪a, i⟫) := by
  simp only [chordVec, inner_sub_right, inner_smul_right]; ring

theorem inner_chordVec_self_axis (a i j k : ℝ³) (h : ⟪a, i⟫ < ⟪a, k⟫) :
    ⟪a, chordVec a i j k⟫ = 0 := by
  rw [inner_chordVec]; have : ⟪a, k⟫ - ⟪a, i⟫ ≠ 0 := by linarith
  field_simp; ring
/-- Lagrange's identity for the cross product. -/
theorem inner_cross_self_eq (a b : ℝ³) :
    ⟪cross a b, cross a b⟫ = ⟪a, a⟫ * ⟪b, b⟫ - ⟪a, b⟫ ^ 2 := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  ring

/-- The chord as `j` minus a point of the segment `i k`. -/
theorem chordVec_eq (a i j k : ℝ³) (h : ⟪a, i⟫ ≠ ⟪a, k⟫) :
    chordVec a i j k = j - ((1 - (⟪a, j⟫ - ⟪a, i⟫) / (⟪a, k⟫ - ⟪a, i⟫)) • i
      + ((⟪a, j⟫ - ⟪a, i⟫) / (⟪a, k⟫ - ⟪a, i⟫)) • k) := by
  have hne : ⟪a, k⟫ - ⟪a, i⟫ ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have e : (⟪a, k⟫ - ⟪a, j⟫) / (⟪a, k⟫ - ⟪a, i⟫) = 1 - (⟪a, j⟫ - ⟪a, i⟫) / (⟪a, k⟫ - ⟪a, i⟫) := by
    field_simp; ring
  rw [chordVec, e]
  abel

/-- Along the diameter axis, the chord over `p q` at `v` is the line offset. -/
theorem chordVec_eq_lineOffset (p q v : ℝ³) (hD : 0 < ‖q - p‖) :
    chordVec ((1 / ‖q - p‖) • (q - p)) p v q = lineOffset p q v := by
  set D := ‖q - p‖ with hDdef
  set a : ℝ³ := (1 / D) • (q - p) with ha
  have h1 : ⟪a, v⟫ - ⟪a, p⟫ = ⟪q - p, v - p⟫ / D := by
    rw [← inner_sub_right, ha, real_inner_smul_left]; ring
  have h2 : ⟪a, q⟫ - ⟪a, p⟫ = D := by
    rw [← inner_sub_right, ha, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hDdef]
    field_simp
  rw [chordVec_eq a p v q (by intro h; have := h2; rw [h, sub_self] at this; linarith), h1, h2,
    lineOffset, ← hDdef]
  have e : ⟪q - p, v - p⟫ / D / D = ⟪q - p, v - p⟫ / D ^ 2 := by ring
  rw [e]
  simp only [sub_smul, one_smul, smul_sub]
  abel

/-- Inner products with a vector perpendicular to the axis see the offset only. -/
theorem inner_lineOffset (x p q v : ℝ³) (hx : ⟪x, q - p⟫ = 0) :
    ⟪x, lineOffset p q v⟫ = ⟪x, v - p⟫ := by
  simp [lineOffset, inner_sub_right, real_inner_smul_right, hx]
theorem inner_cross_sq_gram (n d y : ℝ³) (hn : ⟪n, n⟫ = 1) :
    ⟪n, cross d y⟫ ^ 2 = (⟪d, d⟫ * ⟪y, y⟫ - ⟪d, y⟫ ^ 2)
      - (⟪n, d⟫ ^ 2 * ⟪y, y⟫ - 2 * ⟪n, d⟫ * ⟪n, y⟫ * ⟪d, y⟫ + ⟪n, y⟫ ^ 2 * ⟪d, d⟫) := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at *
  simp
  linear_combination ((d 0 * d 0 + d 1 * d 1 + d 2 * d 2) * (y 0 * y 0 + y 1 * y 1 + y 2 * y 2)
    - (d 0 * y 0 + d 1 * y 1 + d 2 * y 2) ^ 2) * hn
/-! ## Plate helpers -/

theorem plateKappa_pos (N : ℕ) : 0 < plateKappa N := by
  unfold plateKappa; positivity

theorem plateKappa_le_half (N : ℕ) : plateKappa N ≤ 1 / 2 := by
  unfold plateKappa
  have : (1 : ℝ) ≤ ((N : ℝ) ^ 2 + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 2 + 1 := by nlinarith [sq_nonneg (N : ℝ)]
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem lo_sq_aux (d y : ℝ³) (h : d ≠ 0) :
    ‖d‖ ^ 2 * ‖y - (⟪d, y⟫ / ‖d‖ ^ 2) • d‖ ^ 2 = ‖d‖ ^ 2 * ‖y‖ ^ 2 - ⟪d, y⟫ ^ 2 := by
  have hd : ‖d‖ ^ 2 ≠ 0 := by positivity
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm]
  field_simp
  ring

theorem lineOffset_norm_sq (p q v : ℝ³) (h : q - p ≠ 0) :
    ‖q - p‖ ^ 2 * ‖lineOffset p q v‖ ^ 2 = ‖q - p‖ ^ 2 * ‖v - p‖ ^ 2 - ⟪q - p, v - p⟫ ^ 2 :=
  lo_sq_aux (q - p) (v - p) h

theorem norm_lineOffset_le (p q v : ℝ³) : ‖lineOffset p q v‖ ≤ ‖v - p‖ := by
  by_cases h : q - p = 0
  · simp [lineOffset, h]
  · have h1 := lineOffset_norm_sq p q v h
    have hd : 0 < ‖q - p‖ ^ 2 := by positivity
    apply le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith [sq_nonneg ⟪q - p, v - p⟫]

theorem plate_X_le (a b c Y Dd w : ℝ) (ha : |a| ≤ w) (hb : |b| ≤ w) (hY : Y ≤ Dd)
    (hY0 : 0 ≤ Y) (hc : |c| ≤ Dd) :
    a ^ 2 * Y - 2 * a * b * c + b ^ 2 * Dd ≤ 4 * w ^ 2 * Dd := by
  have hw : 0 ≤ w := (abs_nonneg _).trans ha
  have hD : 0 ≤ Dd := hY0.trans hY
  have a2 : a ^ 2 ≤ w ^ 2 := by rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have b2 : b ^ 2 ≤ w ^ 2 := by rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have t1 : a ^ 2 * Y ≤ w ^ 2 * Dd := mul_le_mul a2 hY hY0 (by positivity)
  have t2 : b ^ 2 * Dd ≤ w ^ 2 * Dd := mul_le_mul_of_nonneg_right b2 hD
  have ab : |a * b| ≤ w * w := by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hw
  have t3 : -(2 * a * b * c) ≤ 2 * (w * w * Dd) := by
    have : |a * b * c| ≤ w * w * Dd := by
      rw [abs_mul]; exact mul_le_mul ab hc (abs_nonneg _) (by positivity)
    nlinarith [neg_abs_le (a * b * c)]
  nlinarith

theorem bessel2 (u v c : ℝ³) (huu : ⟪u, u⟫ = 1) (hvv : ⟪v, v⟫ = 1) (huv : ⟪u, v⟫ = 0) :
    ⟪u, c⟫ ^ 2 + ⟪v, c⟫ ^ 2 ≤ ‖c‖ ^ 2 := by
  have h := real_inner_self_nonneg (x := c - ⟪u, c⟫ • u - ⟪v, c⟫ • v)
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    huu, hvv, huv, hvu] at h
  rw [real_inner_comm c u, real_inner_comm c v, real_inner_self_eq_norm_sq] at h
  rw [real_inner_comm c u, real_inner_comm c v]
  nlinarith

theorem abs_inner_unit_le (u c : ℝ³) (huu : ⟪u, u⟫ = 1) : |⟪u, c⟫| ≤ ‖c‖ := by
  have hu : ‖u‖ = 1 := by
    have := real_inner_self_eq_norm_sq u
    rw [huu] at this
    nlinarith [norm_nonneg u]
  have := abs_real_inner_le_norm u c
  rwa [hu, one_mul] at this

/-! ## L5 -/

theorem boxApplies_of_needle (V : Finset ℝ³) (N : ℕ) (hcard : V.card ≤ N)
    (p q : ℝ³) (hp : p ∈ V) (hq : q ∈ V)
    (hdiam : ∀ x ∈ V, ∀ y ∈ V, ‖x - y‖ ≤ ‖q - p‖)
    (ρ : ℝ) (hρ : ∀ v ∈ V, ‖lineOffset p q v‖ ≤ ρ) (hρ' : ∃ v ∈ V, ρ ≤ ‖lineOffset p q v‖)
    (hρ0 : 0 < ρ) (hneedle : 8 * ρ < needleKappa N * ‖q - p‖) :
    BoxApplies V := by
  classical
  -- constants
  set κ := needleKappa N with hκ
  have hκ0 : 0 < κ := by rw [hκ, needleKappa]; positivity
  have hκ1 : κ < 1 := by
    rw [hκ, needleKappa, div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
    nlinarith
  set D := ‖q - p‖ with hDdef
  have hD : 0 < D := by
    by_contra h
    push Not at h
    have : κ * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ0.le h
    linarith
  -- step 0: the axis and levels
  set a : ℝ³ := (1 / D) • (q - p) with ha
  have hqp : q - p = D • a := by rw [ha, smul_smul, mul_one_div_cancel hD.ne', one_smul]
  have haa : ⟪a, a⟫ = 1 := by
    rw [ha, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hDdef]
    field_simp
  have hzqp : ⟪a, q⟫ - ⟪a, p⟫ = D := by
    rw [← inner_sub_right, hqp, real_inner_smul_right, haa, mul_one]
  have hlev : ∀ v ∈ V, ⟪a, p⟫ ≤ ⟪a, v⟫ ∧ ⟪a, v⟫ ≤ ⟪a, q⟫ := by
    intro v hv
    obtain ⟨h1, h2⟩ := inner_mem_of_diam hp hq hdiam v hv
    have e1 : ⟪a, v⟫ - ⟪a, p⟫ = ⟪q - p, v - p⟫ / D := by
      rw [← inner_sub_right, ha, real_inner_smul_left]; ring
    constructor
    · have : 0 ≤ ⟪q - p, v - p⟫ / D := div_nonneg h1 hD.le
      linarith
    · have : ⟪q - p, v - p⟫ / D ≤ D := by
        rw [div_le_iff₀ hD]; rw [← hDdef] at h2; linarith [show D ^ 2 = D * D by ring]
      linarith
  have hpq : ⟪a, p⟫ < ⟪a, q⟫ := by linarith
  -- offsets seen by unit vectors perpendicular to the axis
  have hoff : ∀ x : ℝ³, ⟪x, x⟫ = 1 → ⟪x, a⟫ = 0 → ∀ v ∈ V, |⟪x, v⟫ - ⟪x, p⟫| ≤ ρ := by
    intro x hx hxa v hv
    rw [← inner_sub_right,
      ← inner_lineOffset x p q v (by rw [hqp, real_inner_smul_right, hxa, mul_zero])]
    exact (abs_inner_unit_le x _ hx).trans (hρ v hv)
  -- step 1: chords
  let S : Finset ((ℝ³ × ℝ³) × ℝ³) := ((V ×ˢ V) ×ˢ V).filter
    (fun t => ⟪a, t.1.1⟫ ≤ ⟪a, t.1.2⟫ ∧ ⟪a, t.1.2⟫ ≤ ⟪a, t.2⟫ ∧ ⟪a, t.1.1⟫ < ⟪a, t.2⟫)
  let Ch : (ℝ³ × ℝ³) × ℝ³ → ℝ³ := fun t => chordVec a t.1.1 t.1.2 t.2
  have hmemS : ∀ i ∈ V, ∀ j ∈ V, ∀ k ∈ V, ⟪a, i⟫ ≤ ⟪a, j⟫ → ⟪a, j⟫ ≤ ⟪a, k⟫ →
      ⟪a, i⟫ < ⟪a, k⟫ → ((i, j), k) ∈ S := by
    intro i hi j hj k hk h1 h2 h3
    simp only [S, mem_filter, mem_product]
    exact ⟨⟨⟨hi, hj⟩, hk⟩, h1, h2, h3⟩
  have hcardS : S.card ≤ N ^ 3 := by
    calc S.card ≤ ((V ×ˢ V) ×ˢ V).card := card_filter_le _ _
      _ = V.card * V.card * V.card := by simp [card_product]
      _ ≤ N * N * N := by gcongr
      _ = N ^ 3 := by ring
  obtain ⟨v₀, hv₀, hρv₀⟩ := hρ'
  have hS0 : ((p, v₀), q) ∈ S :=
    hmemS p hp v₀ hv₀ q hq (hlev v₀ hv₀).1 (hlev v₀ hv₀).2 hpq
  obtain ⟨⟨⟨i, j⟩, k⟩, hts, hmax⟩ := exists_max_image S (fun t => ‖Ch t‖) ⟨_, hS0⟩
  have hts' := hts
  simp only [S, mem_filter, mem_product] at hts'
  obtain ⟨⟨⟨hi, hj⟩, hk⟩, hij, hjk, hik⟩ := hts'
  set C := chordVec a i j k with hC
  set R := ‖C‖ with hRdef
  have hRρ : ρ ≤ R := by
    have h := hmax _ hS0
    simp only [Ch] at h
    rw [ha, chordVec_eq_lineOffset p q v₀ hD] at h
    linarith
  have hR : 0 < R := by linarith
  have hCa : ⟪a, C⟫ = 0 := inner_chordVec_self_axis a i j k hik
  -- step 2: frame of the chord plane and the arc lemma
  set g : ℝ³ := (1 / R) • C with hg
  have hgg : ⟪g, g⟫ = 1 := by
    rw [hg, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hRdef]
    field_simp
  have hga : ⟪g, a⟫ = 0 := by rw [hg, real_inner_smul_left, real_inner_comm, hCa, mul_zero]
  have hag : ⟪a, g⟫ = 0 := by rw [real_inner_comm]; exact hga
  have hgC : ⟪g, C⟫ = R := by
    rw [hg, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hRdef]; field_simp
  clear_value g
  set g' := cross a g with hg'
  have hg'a : ⟪g', a⟫ = 0 := inner_cross_left a g
  have hg'g : ⟪g', g⟫ = 0 := inner_cross_right a g
  have hg'g' : ⟪g', g'⟫ = 1 := by rw [hg', inner_cross_self_eq, haa, hgg, hag]; ring
  clear_value g'
  have hbess : ∀ t ∈ S, ⟪g, Ch t⟫ ^ 2 + ⟪g', Ch t⟫ ^ 2 ≤ R ^ 2 := by
    intro t ht
    have h1 := bessel2 g g' (Ch t) hgg hg'g' (by rw [real_inner_comm]; exact hg'g)
    have h2 : ‖Ch t‖ ≤ R := hmax t ht
    have h3 : ‖Ch t‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith
  obtain ⟨α, β, hαβ, hdots⟩ := exists_dir_small_dots S (fun t => ⟪g, Ch t⟫)
    (fun t => ⟪g', Ch t⟫) R hR.le hbess (N ^ 3) hcardS
  have hlam : (1 - 1 / (2 * (((N ^ 3 : ℕ) : ℝ) + 1) ^ 2)) = 1 - κ := by
    rw [hκ, needleKappa]; push_cast; ring
  set lam := 1 - κ with hlamdef
  set m : ℝ³ := α • g + β • g' with hm
  have hma : ⟪m, a⟫ = 0 := by
    rw [hm, inner_add_left, real_inner_smul_left, real_inner_smul_left, hga, hg'a]; ring
  have ham : ⟪a, m⟫ = 0 := by rw [real_inner_comm]; exact hma
  have hmm : ⟪m, m⟫ = 1 := by
    have hgg' : ⟪g, g'⟫ = 0 := by rw [real_inner_comm]; exact hg'g
    rw [hm]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hgg,
      hg'g', hgg', hg'g]
    linarith
  have hmC : ∀ t ∈ S, |⟪m, Ch t⟫| ≤ lam * R := by
    intro t ht
    have h := hdots t ht
    rw [hlam] at h
    simpa only [hm, inner_add_left, real_inner_smul_left] using h
  clear_value m
  -- step 3: Chebyshev line fit of the m-coordinates against the levels
  set E := lam * R / 2 with hE
  have hlam0 : 0 < lam := by rw [hlamdef]; linarith
  have hE0 : 0 < E := by rw [hE]; positivity
  obtain ⟨tt, β₀, hfit⟩ := exists_line_fit V (fun v => ⟪a, v⟫) (fun v => ⟪m, v⟫) E
    ⟨p, hp, q, hq, hpq⟩ (by
      intro i' hi' j' hj' k' hk' h1 h2 h3
      rw [← inner_chordVec]
      have := hmC _ (hmemS i' hi' j' hj' k' hk' h1 h2 h3)
      simp only [Ch] at this
      rw [hE]; linarith)
  set s := Real.sqrt (1 + tt ^ 2) with hs
  have hss : s ^ 2 = 1 + tt ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    have h := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg tt) : (1 : ℝ) ≤ 1 + tt ^ 2)
    rwa [Real.sqrt_one, ← hs] at h
  have hs0 : 0 < s := by linarith
  clear_value s
  set e : ℝ³ := (1 / s) • (m - tt • a) with he
  have hee : ⟪e, e⟫ = 1 := by
    have hin : ⟪m - tt • a, m - tt • a⟫ = 1 + tt ^ 2 := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hmm,
        haa, hma, ham]
      ring
    rw [he, real_inner_smul_left, real_inner_smul_right, hin, ← hss]
    field_simp
  set n : ℝ³ := cross a m with hn
  have hna : ⟪n, a⟫ = 0 := inner_cross_left a m
  have hnm : ⟪n, m⟫ = 0 := inner_cross_right a m
  have hnn : ⟪n, n⟫ = 1 := by rw [hn, inner_cross_self_eq, haa, hmm, ham]; ring
  have hen : ⟪e, n⟫ = 0 := by
    rw [he, real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_comm,
      hnm, real_inner_comm, hna]
    ring
  have hev : ∀ v, ⟪e, v⟫ = (⟪m, v⟫ - tt * ⟪a, v⟫) / s := by
    intro v
    rw [he, real_inner_smul_left, inner_sub_left, real_inner_smul_left]; ring
  have hbox : ∀ v ∈ V, (β₀ - E) / s ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ (β₀ - E) / s + 2 * E / s ∧
      ⟪n, p⟫ - ρ ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ ⟪n, p⟫ - ρ + 2 * ρ := by
    intro v hv
    obtain ⟨f1, f2⟩ := abs_le.1 (hfit v hv)
    obtain ⟨o1, o2⟩ := abs_le.1 (hoff n hnn hna v hv)
    refine ⟨?_, ?_, by linarith, by linarith⟩
    · rw [hev, div_le_div_iff_of_pos_right hs0]; linarith
    · rw [hev, show (β₀ - E) / s + 2 * E / s = (β₀ + E) / s by ring,
        div_le_div_iff_of_pos_right hs0]
      linarith
  -- step 4: the long chord as a triangle base
  set θ := (⟪a, j⟫ - ⟪a, i⟫) / (⟪a, k⟫ - ⟪a, i⟫) with hθ
  have hki : 0 < ⟪a, k⟫ - ⟪a, i⟫ := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hki.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hki]; linarith
  set qs : ℝ³ := (1 - θ) • i + θ • k with hqs
  have hCeq : C = j - qs := by rw [hC, chordVec_eq a i j k hik.ne]
  have hqsH : HullComb V qs := hullComb_segment hi hk hθ0 hθ1
  have ha_qs : ⟪a, qs⟫ = ⟪a, j⟫ := by
    have := hCa; rw [hCeq, inner_sub_right] at this; linarith
  have hg_j : ⟪g, j⟫ = ⟪g, qs⟫ + R := by
    have := hgC; rw [hCeq, inner_sub_right] at this; linarith
  have hgqp : ⟪g, q⟫ = ⟪g, p⟫ := by
    have : ⟪g, q - p⟫ = 0 := by rw [hqp, real_inner_smul_right, hga, mul_zero]
    rw [inner_sub_right] at this; linarith
  have hg_qs : |⟪g, qs⟫ - ⟪g, p⟫| ≤ ρ := by
    obtain ⟨i1, i2⟩ := abs_le.1 (hoff g hgg hga i hi)
    obtain ⟨k1, k2⟩ := abs_le.1 (hoff g hgg hga k hk)
    have e : ⟪g, qs⟫ - ⟪g, p⟫ = (1 - θ) * (⟪g, i⟫ - ⟪g, p⟫) + θ * (⟪g, k⟫ - ⟪g, p⟫) := by
      rw [hqs, inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
    have hθ' : 0 ≤ 1 - θ := by linarith
    rw [e, abs_le]
    constructor
    · linarith [mul_le_mul_of_nonneg_left i1 hθ', mul_le_mul_of_nonneg_left k1 hθ0]
    · linarith [mul_le_mul_of_nonneg_left i2 hθ', mul_le_mul_of_nonneg_left k2 hθ0]
  -- step 5: apply L2
  have finish : ∀ (u' P₃ : ℝ³) (y₀ h : ℝ), ⟪u', u'⟫ = 1 → ⟪g, u'⟫ = 0 → HullComb V P₃ →
      ⟪g, P₃⟫ = ⟪g, p⟫ → ⟪u', qs⟫ = y₀ → ⟪u', j⟫ = y₀ → ⟪u', P₃⟫ = y₀ + h → D / 2 ≤ h →
      BoxApplies V := by
    intro u' P₃ y₀ h hu' hgu' hP₃ hgP₃ hy1 hy2 hy3 hh
    have hh0 : 0 < h := by linarith
    refine boxApplies_of_triangle V e n g u' hee hnn hen hgg hu' hgu' ((β₀ - E) / s)
      (⟪n, p⟫ - ρ) (2 * E / s) (2 * ρ) R h ⟪g, qs⟫ y₀ ⟪g, P₃⟫ (by positivity) (by positivity) hh0
      hbox qs j P₃ hqsH (hullComb_of_mem hj) hP₃ ⟨rfl, hy1⟩ ⟨hg_j, hy2⟩ ⟨rfl, hy3⟩ ?_
    rw [hgP₃]
    have e1 : |⟪g, p⟫ - ⟪g, qs⟫| ≤ ρ := by rw [abs_sub_comm]; exact hg_qs
    have e2 : |⟪g, qs⟫ + R - ⟪g, p⟫| ≤ ρ := by rw [← hg_j]; exact hoff g hgg hga j hj
    have hμle : 2 * E / s ≤ lam * R := by
      rw [hE, show 2 * (lam * R / 2) = lam * R by ring]
      exact div_le_self (by positivity) hs1
    have h4 : 4 * ρ < κ * h := by
      have := mul_le_mul_of_nonneg_left (show D ≤ 2 * h by linarith) hκ0.le
      linarith
    have t1 : 2 * E / s * h ≤ lam * R * h := mul_le_mul_of_nonneg_right hμle hh0.le
    have t2 : 2 * ρ * (|⟪g, p⟫ - ⟪g, qs⟫| + |⟪g, qs⟫ + R - ⟪g, p⟫|) ≤ 2 * ρ * (2 * ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have t3 : 4 * ρ * ρ ≤ 4 * ρ * R := mul_le_mul_of_nonneg_left hRρ (by positivity)
    have t4 : 4 * ρ * R < κ * h * R := mul_lt_mul_of_pos_right h4 hR
    rw [hlamdef] at t1
    linarith
  by_cases hcase : D / 2 ≤ ⟪a, q⟫ - ⟪a, j⟫
  · exact finish a q ⟪a, j⟫ (⟪a, q⟫ - ⟪a, j⟫) haa hga (hullComb_of_mem hq) hgqp ha_qs rfl
      (by ring) hcase
  · push Not at hcase
    refine finish (-a) p (-⟪a, j⟫) (⟪a, j⟫ - ⟪a, p⟫) (by rw [inner_neg_left, inner_neg_right, neg_neg, haa]) (by simp [hga])
      (hullComb_of_mem hp) rfl (by rw [inner_neg_left, ha_qs]) (by rw [inner_neg_left])
      (by rw [inner_neg_left]; ring) (by linarith)

theorem plate_core (V : Finset ℝ³) (N : ℕ) (hcard : V.card ≤ N)
    (n u u' : ℝ³) (hnn : ⟪n, n⟫ = 1) (huu : ⟪u, u⟫ = 1) (hu'u' : ⟪u', u'⟫ = 1)
    (hnu : ⟪n, u⟫ = 0) (hnu' : ⟪n, u'⟫ = 0) (huu' : ⟪u, u'⟫ = 0)
    (b w : ℝ) (hw : 0 < w) (hslab : ∀ v ∈ V, b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (p q r : ℝ³) (hp : p ∈ V) (hq : q ∈ V) (hr : r ∈ V)
    (hdiam : ∀ x ∈ V, ∀ y ∈ V, ‖x - y‖ ≤ ‖q - p‖)
    (ρ Db : ℝ) (hρ0 : 0 < ρ) (hDb : ‖q - p‖ - w ≤ Db)
    (hu_d : ⟪u, q - p⟫ = Db) (hu'_d : ⟪u', q - p⟫ = 0)
    (hh : ρ / 2 ≤ ⟪u', r - p⟫)
    (hplate : 4 * w * ‖q - p‖ < ρ * (plateKappa N * ‖q - p‖ - w)) :
    BoxApplies V := by
  set D := ‖q - p‖ with hD
  set κ := plateKappa N with hκ
  have hκ0 : 0 < κ := plateKappa_pos N
  have hκ2 : κ ≤ 1 / 2 := plateKappa_le_half N
  have hD0 : 0 ≤ D := norm_nonneg _
  have hkw : 0 < κ * D - w := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonneg hρ0.le (neg_nonneg.2 hneg), mul_nonneg hw.le hD0]
  have hDpos : 0 < D := by
    by_contra hneg
    have : D = 0 := le_antisymm (not_lt.1 hneg) hD0
    rw [this] at hkw; linarith
  have hh0 : 0 < ⟪u', r - p⟫ := by linarith
  set h := ⟪u', r - p⟫ with hhdef
  -- inner frame by L3
  set S : Finset (ℝ³ × ℝ³) := V ×ˢ V with hS
  have hScard : S.card ≤ N ^ 2 := by
    rw [hS, Finset.card_product, sq]; exact Nat.mul_le_mul hcard hcard
  obtain ⟨α, β, hαβ, hsm⟩ := exists_dir_small_dots S (fun k => ⟪u, k.1 - k.2⟫)
    (fun k => ⟪u', k.1 - k.2⟫) D hD0 (by
      intro k hk
      rw [hS, Finset.mem_product] at hk
      have := bessel2 u u' (k.1 - k.2) huu hu'u' huu'
      have h2 := hdiam k.1 hk.1 k.2 hk.2
      have h3 : ‖k.1 - k.2‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      linarith) (N ^ 2) hScard
  have hκeq : (1 : ℝ) / (2 * (((N ^ 2 : ℕ) : ℝ) + 1) ^ 2) = κ := by
    rw [hκ]; unfold plateKappa; push_cast; rfl
  rw [hκeq] at hsm
  set e : ℝ³ := α • u + β • u' with he
  have hvu : ⟪u', u⟫ = 0 := by rw [real_inner_comm]; exact huu'
  have hee : ⟪e, e⟫ = 1 := by
    simp only [he, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huu, hu'u', huu', hvu]
    nlinarith
  have hen : ⟪e, n⟫ = 0 := by
    have h1 : ⟪u, n⟫ = 0 := by rw [real_inner_comm]; exact hnu
    have h2 : ⟪u', n⟫ = 0 := by rw [real_inner_comm]; exact hnu'
    simp only [he, inner_add_left, real_inner_smul_left, h1, h2]; ring
  have hed : ∀ c : ℝ³, ⟪e, c⟫ = α * ⟪u, c⟫ + β * ⟪u', c⟫ := by
    intro c; simp only [he, inner_add_left, real_inner_smul_left]
  have hVne : V.Nonempty := ⟨p, hp⟩
  obtain ⟨v0, hv0, hmin⟩ := V.exists_min_image (fun v => ⟪e, v⟫) hVne
  have hbox : ∀ v ∈ V, ⟪e, v0⟫ ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ ⟪e, v0⟫ + (1 - κ) * D ∧
      b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w := by
    intro v hv
    refine ⟨hmin v hv, ?_, (hslab v hv).1, (hslab v hv).2⟩
    have := hsm (v, v0) (by rw [hS, Finset.mem_product]; exact ⟨hv, hv0⟩)
    rw [← hed (v - v0), inner_sub_right] at this
    linarith [le_abs_self (⟪e, v⟫ - ⟪e, v0⟫)]
  have hκ1 : 0 < 1 - κ := by linarith
  have hx3 : |⟪u, r⟫ - ⟪u, p⟫| ≤ D := by
    rw [← inner_sub_right]
    exact (abs_inner_unit_le u _ huu).trans (hdiam r hr p hp)
  have hx4 : |⟪u, p⟫ + Db - ⟪u, r⟫| ≤ D := by
    have : ⟪u, p⟫ + Db - ⟪u, r⟫ = ⟪u, q - r⟫ := by
      rw [inner_sub_right, ← hu_d, inner_sub_right]; ring
    rw [this]
    exact (abs_inner_unit_le u _ huu).trans (hdiam q hq r hr)
  have hDbpos : 0 < Db := by nlinarith
  refine boxApplies_of_triangle V e n u u' hee hnn hen huu hu'u' huu' ⟪e, v0⟫ b ((1 - κ) * D) w
    Db h ⟪u, p⟫ ⟪u', p⟫ ⟪u, r⟫ (by positivity) hw hh0 hbox p q r (hullComb_of_mem hp)
    (hullComb_of_mem hq) (hullComb_of_mem hr) ⟨rfl, rfl⟩ ?_ ?_ ?_
  · refine ⟨?_, by have := hu'_d; rw [inner_sub_right] at this; linarith⟩
    rw [← hu_d, inner_sub_right]; ring
  · refine ⟨rfl, ?_⟩
    rw [hhdef, inner_sub_right]; ring
  · have e1 : |⟪u, r⟫ - ⟪u, p⟫| ≤ D := hx3
    have e2 : |⟪u, p⟫ + Db - ⟪u, r⟫| ≤ D := hx4
    have e3 : (1 - κ) * D * h + w * (|⟪u, r⟫ - ⟪u, p⟫| + |⟪u, p⟫ + Db - ⟪u, r⟫|) < Db * h := by
      have : w * (|⟪u, r⟫ - ⟪u, p⟫| + |⟪u, p⟫ + Db - ⟪u, r⟫|) ≤ w * (2 * D) := by
        apply mul_le_mul_of_nonneg_left (by linarith) hw.le
      nlinarith [mul_nonneg hkw.le (sub_nonneg.2 hh), mul_le_mul_of_nonneg_right hDb hh0.le]
    exact e3

theorem cross_unit (n u : ℝ³) (hnn : ⟪n, n⟫ = 1) (huu : ⟪u, u⟫ = 1) (hnu : ⟪n, u⟫ = 0) :
    ⟪cross n u, cross n u⟫ = 1 := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at *
  simp
  linear_combination (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) * hnn + huu
    - (n 0 * u 0 + n 1 * u 1 + n 2 * u 2) * hnu

theorem inner_cross_decomp (n u d y : ℝ³) (t Db : ℝ) (hd : d = t • n + Db • u) :
    ⟪n, cross d y⟫ = Db * ⟪cross n u, y⟫ := by
  subst hd
  simp [cross, PiLp.inner_apply, Fin.sum_univ_three]
  ring

set_option maxHeartbeats 1600000 in
/-- Lemma L6 (plate case). -/
theorem boxApplies_of_plate (V : Finset ℝ³) (N : ℕ) (hcard : V.card ≤ N)
    (n : ℝ³) (hnn : ⟪n, n⟫ = 1) (b w : ℝ) (hw : 0 < w)
    (hslab : ∀ v ∈ V, b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (p q : ℝ³) (hp : p ∈ V) (hq : q ∈ V)
    (hdiam : ∀ x ∈ V, ∀ y ∈ V, ‖x - y‖ ≤ ‖q - p‖)
    (r : ℝ³) (hr : r ∈ V) (ρ : ℝ) (hρ : ρ ≤ ‖lineOffset p q r‖) (hρ0 : 0 < ρ)
    (hplate : 4 * w * ‖q - p‖ < ρ * (plateKappa N * ‖q - p‖ - w)) :
    BoxApplies V := by
  set d := q - p with hd
  set D := ‖d‖ with hD
  set κ := plateKappa N with hκ
  have hκ0 : 0 < κ := plateKappa_pos N
  have hκ2 : κ ≤ 1 / 2 := plateKappa_le_half N
  have hD0 : 0 ≤ D := norm_nonneg _
  have hkw : 0 < κ * D - w := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonneg hρ0.le (neg_nonneg.2 hneg), mul_nonneg hw.le hD0]
  have hDpos : 0 < D := by
    by_contra hneg
    have : D = 0 := le_antisymm (not_lt.1 hneg) hD0
    rw [this] at hkw; linarith
  have hwD : w < D / 2 := by nlinarith
  have hd0 : d ≠ 0 := by
    intro h; rw [h, norm_zero] at hD; linarith
  -- n-components
  set t := ⟪n, d⟫ with ht
  have hslab' : ∀ v ∈ V, ∀ v' ∈ V, |⟪n, v - v'⟫| ≤ w := by
    intro v hv v' hv'
    rw [inner_sub_right, abs_le]
    have := hslab v hv; have := hslab v' hv'
    constructor <;> linarith
  have htw : |t| ≤ w := hslab' q hq p hp
  have ht2 : t ^ 2 ≤ w ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) htw 2
  have hD2 : 0 ≤ D ^ 2 - t ^ 2 := by nlinarith
  set Db := Real.sqrt (D ^ 2 - t ^ 2) with hDbdef
  have hDb2 : Db ^ 2 = D ^ 2 - t ^ 2 := Real.sq_sqrt hD2
  have hDbw : D - w ≤ Db := by
    have := Real.abs_le_sqrt (x := D - w) (y := D ^ 2 - t ^ 2) (by nlinarith)
    exact (le_abs_self _).trans this
  have hDbD : Db ≤ D := Real.sqrt_le_iff.2 ⟨hD0, by nlinarith⟩
  have hDbpos : 0 < Db := by linarith
  -- outer frame
  set u : ℝ³ := (1 / Db) • (d - t • n) with hu
  have hdec : d = t • n + Db • u := by
    rw [hu, smul_smul, mul_one_div_cancel hDbpos.ne', one_smul]; abel
  have hnd : ⟪n, d⟫ = t := rfl
  have hnu : ⟪n, u⟫ = 0 := by
    rw [hu, real_inner_smul_right, inner_sub_right, real_inner_smul_right, hnn, hnd]; ring
  have huu : ⟪u, u⟫ = 1 := by
    have h1 : ⟪d, d⟫ = t ^ 2 + Db ^ 2 * ⟪u, u⟫ := by
      have hnu' : ⟪u, n⟫ = 0 := by rw [real_inner_comm]; exact hnu
      conv_lhs => rw [hdec]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hnn, hnu, hnu']
      ring
    have h2 : ⟪d, d⟫ = D ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have : Db ^ 2 * ⟪u, u⟫ = Db ^ 2 * 1 := by nlinarith
    exact mul_left_cancel₀ (by positivity) this
  have hu_d : ⟪u, d⟫ = Db := by
    conv_lhs => rw [hdec]
    have hnu' : ⟪u, n⟫ = 0 := by rw [real_inner_comm]; exact hnu
    simp only [inner_add_right, real_inner_smul_right, hnu', huu]; ring
  set u₁ := cross n u with hu₁
  have h1n : ⟪n, u₁⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left n u
  have h1u : ⟪u, u₁⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right n u
  have h11 : ⟪u₁, u₁⟫ = 1 := cross_unit n u hnn huu hnu
  have h1d : ⟪u₁, d⟫ = 0 := by
    conv_lhs => rw [hdec]
    simp only [inner_add_right, real_inner_smul_right, hu₁, inner_cross_left, inner_cross_right]
    ring
  -- height
  set y := r - p with hy
  set h0 := ⟪u₁, y⟫ with hh0
  have hcr : ⟪n, cross d y⟫ = Db * h0 := inner_cross_decomp n u d y t Db hdec
  have hG := inner_cross_sq_gram n d y hnn
  have hyD : ‖y‖ ≤ D := hdiam r hr p hp
  have hy2 : ⟪y, y⟫ ≤ ⟪d, d⟫ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hyD 2
  have hdd : ⟪d, d⟫ = D ^ 2 := real_inner_self_eq_norm_sq d
  have hcd : |⟪d, y⟫| ≤ ⟪d, d⟫ := by
    refine (abs_real_inner_le_norm d y).trans ?_
    rw [hdd]; nlinarith [norm_nonneg y]
  have hX := plate_X_le ⟪n, d⟫ ⟪n, y⟫ ⟪d, y⟫ ⟪y, y⟫ ⟪d, d⟫ w htw (hslab' r hr p hp) hy2
    (real_inner_self_nonneg) hcd
  have hlo := lineOffset_norm_sq p q r hd0
  have hρ2 : ρ ^ 2 ≤ ‖lineOffset p q r‖ ^ 2 := pow_le_pow_left₀ hρ0.le hρ 2
  have hyy : ⟪y, y⟫ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  have hkey : D ^ 2 * ρ ^ 2 - 4 * w ^ 2 * D ^ 2 ≤ (Db * h0) ^ 2 := by
    rw [← hcr]
    have : ‖d‖ ^ 2 * ρ ^ 2 ≤ ‖d‖ ^ 2 * ‖lineOffset p q r‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hρ2 (by positivity)
    rw [← hD] at this hlo
    rw [hG, hdd, hyy]
    rw [hdd, hyy] at hX
    linarith
  have hρD : ρ ≤ D := hρ.trans ((norm_lineOffset_le p q r).trans hyD)
  have hw4 : 4 * w < ρ := by
    have h1 : ρ * (κ * D - w) ≤ ρ * (κ * D) := by nlinarith [mul_pos hρ0 hw]
    have h2 : ρ * (κ * D) ≤ ρ * (D / 2) := by
      nlinarith [mul_nonneg (mul_nonneg hρ0.le hD0) (sub_nonneg.2 hκ2)]
    have : 4 * w * D < ρ * (D / 2) := by linarith
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hD0, mul_pos hw hDpos]
  have hsq : (ρ / 2) ^ 2 ≤ h0 ^ 2 := by
    have h1 : Db ^ 2 * (ρ / 2) ^ 2 ≤ Db ^ 2 * h0 ^ 2 := by
      have e1 : Db ^ 2 * (ρ / 2) ^ 2 ≤ D ^ 2 * (ρ / 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ hDbpos.le hDbD 2
      have e2 : D ^ 2 * (ρ / 2) ^ 2 ≤ D ^ 2 * ρ ^ 2 - 4 * w ^ 2 * D ^ 2 := by
        have : 16 * w ^ 2 ≤ ρ ^ 2 := by nlinarith
        nlinarith [sq_nonneg D, mul_nonneg (sq_nonneg D) (sub_nonneg.2 this)]
      nlinarith
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hh_abs : ρ / 2 ≤ |h0| := by
    by_contra hc
    push Not at hc
    nlinarith [abs_nonneg h0, sq_abs h0]
  have hdiam' := hdiam
  have hDbw' : ‖q - p‖ - w ≤ Db := hDbw
  rcases le_or_gt 0 h0 with hpos | hneg
  · rw [abs_of_nonneg hpos] at hh_abs
    exact plate_core V N hcard n u u₁ hnn huu h11 hnu h1n h1u b w hw hslab p q r hp hq hr hdiam
      ρ Db hρ0 hDbw' hu_d h1d hh_abs hplate
  · rw [abs_of_neg hneg] at hh_abs
    refine plate_core V N hcard n u (-u₁) hnn huu (by rw [inner_neg_neg]; exact h11) hnu
      (by rw [inner_neg_right, h1n, neg_zero]) (by rw [inner_neg_right, h1u, neg_zero]) b w hw hslab
      p q r hp hq hr hdiam ρ Db hρ0 hDbw' hu_d (by rw [inner_neg_left, h1d, neg_zero])
      (by rw [inner_neg_left]; exact hh_abs) hplate

/-! ## Main theorems (spec 2.1) -/

theorem needleKappa_pos (N : ℕ) : 0 < needleKappa N := by
  unfold needleKappa; positivity

theorem needleKappa_le_half (N : ℕ) : needleKappa N ≤ 1 / 2 := by
  unfold needleKappa
  have : (1 : ℝ) ≤ ((N : ℝ) ^ 3 + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ 3 + 1 := by nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) N) 3]
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem thinAlpha_pos (N : ℕ) : 0 < thinAlpha N := by
  unfold thinAlpha
  have := needleKappa_pos N; have := plateKappa_pos N
  positivity

theorem boxApplies_of_thin (V : Finset ℝ³) (N : ℕ) (hcard : V.card ≤ N)
    (hV : ¬ Collinear ℝ (V : Set ℝ³))
    (n : ℝ³) (hnn : ⟪n, n⟫ = 1) (b w : ℝ)
    (hslab : ∀ v ∈ V, b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (x y : ℝ³) (hx : x ∈ V) (hy : y ∈ V) (hthin : w < thinAlpha N * ‖x - y‖) :
    BoxApplies V := by
  obtain ⟨p, hp, q, hq, hdiam⟩ := exists_diam_pair V ⟨x, hx⟩
  set D := ‖q - p‖ with hDdef
  have hw0 : 0 ≤ w := by
    have h1 := hslab x hx; linarith [h1.1, h1.2]
  have hα := thinAlpha_pos N
  have hxy : ‖x - y‖ ≤ D := hdiam x hx y hy
  have hαD : thinAlpha N * ‖x - y‖ ≤ thinAlpha N * D := mul_le_mul_of_nonneg_left hxy hα.le
  have hD : 0 < D := by
    by_contra h
    push Not at h
    have : thinAlpha N * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα.le h
    linarith
  obtain ⟨r, hr, hmax⟩ := V.exists_max_image (fun v => ‖lineOffset p q v‖) ⟨x, hx⟩
  set ρ := ‖lineOffset p q r‖ with hρdef
  have hρ0 : 0 < ρ := by
    by_contra h
    push Not at h
    apply hV
    rw [collinear_iff_of_mem (p₀ := p) (by exact_mod_cast hp)]
    refine ⟨q - p, fun v hv => ?_⟩
    have hv' : v ∈ V := by exact_mod_cast hv
    have h0 : ‖lineOffset p q v‖ = 0 :=
      le_antisymm ((hmax v hv').trans h) (norm_nonneg _)
    have h1 : lineOffset p q v = 0 := norm_eq_zero.1 h0
    refine ⟨⟪q - p, v - p⟫ / D ^ 2, ?_⟩
    have : v - p = (⟪q - p, v - p⟫ / D ^ 2) • (q - p) := by
      have := h1; unfold lineOffset at this; rw [← hDdef] at this
      exact sub_eq_zero.1 this
    rw [vadd_eq_add, ← this]; abel
  have hκ0 := needleKappa_pos N
  have hκ2 := needleKappa_le_half N
  by_cases hcase : 8 * ρ < needleKappa N * D
  · exact boxApplies_of_needle V N hcard p q hp hq hdiam ρ (fun v hv => hmax v hv)
      ⟨r, hr, le_rfl⟩ hρ0 hcase
  · push Not at hcase
    have hc := plateKappa_pos N
    set a := needleKappa N with ha
    set c := plateKappa N with hcdef
    have hw' : 0 < thinAlpha N * D := by positivity
    have key : 0 < ρ * (33 - a) - 4 * a * D := by nlinarith [mul_pos hκ0 hD]
    refine boxApplies_of_plate V N hcard n hnn b (thinAlpha N * D) hw'
      (fun v hv => ⟨(hslab v hv).1, by linarith [(hslab v hv).2]⟩) p q hp hq hdiam r hr ρ le_rfl
      hρ0 ?_
    have hth : thinAlpha N = a * c / 33 := rfl
    rw [hth]
    nlinarith [mul_pos (mul_pos hc hD) key]

theorem boxApplies_of_thin_fin {k : ℕ} (x : Fin k → ℝ³)
    (hsol : (interior (convexHull ℝ ((Finset.univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty)
    (n : ℝ³) (hnn : ⟪n, n⟫ = 1) (w : ℝ) (hpair : ∀ i j, |⟪n, x i - x j⟫| ≤ w)
    (i₀ j₀ : Fin k) (hthin : w < thinAlpha k * ‖x i₀ - x j₀‖) :
    BoxApplies (Finset.univ.image x) := by
  classical
  have hne : (Finset.univ.image x).Nonempty := ⟨x i₀, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  obtain ⟨v0, hv0, hmin⟩ := (Finset.univ.image x).exists_min_image (fun v => ⟪n, v⟫) hne
  refine boxApplies_of_thin (Finset.univ.image x) k ?_ (not_collinear_of_interior_nonempty _ hsol)
    n hnn ⟪n, v0⟫ w ?_ (x i₀) (x j₀) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)) hthin
  · exact Finset.card_image_le.trans (by simp)
  · intro v hv
    refine ⟨hmin v hv, ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv0
    have := hpair i j
    rw [inner_sub_right] at this
    linarith [(abs_le.1 this).2]

theorem thinAlpha_seven : thinAlpha 7 = 1 / 39050880000 := by
  simp only [thinAlpha, needleKappa, plateKappa]; norm_num

end Minimality

end

#print axioms Minimality.boxApplies_of_thin
#print axioms Minimality.boxApplies_of_thin_fin
#print axioms Minimality.thinAlpha_seven
