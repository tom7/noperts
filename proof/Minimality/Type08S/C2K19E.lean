module

public import Minimality.Type08S.C2K19D
public import Minimality.Type08S.C2K17GA2
public import Minimality.Type08S.C2K17GB2

@[expose] public section


/-!
# K19 / E: the S1.3 tie (L4): `K6tTaA41`, `ζ(d,b) = 0`, `β6 > 1`, `⟪a-b',a-c'⟫ = 0` (⟺ `pr = 0`)

`ζ(d,b) = 0` gives `qr = 0`; the tie gives `pr = 0`.  Split by `L = ⟪a-d,a-c'⟫`:
* `L > 0`: S1.3a pentagon `(a,d,b,a',b')` at `a - c'` (`k17gaR3`, frame `(b-d, c-d, a-c')`, cone `v1, v2 > 0`).  At
  `pr = 0` the cycle tie `z(a) = z(b')` is broken by the cone itself: `w(b') - w(a) = γ4 v2 |r|² > 0`, so `b'` wins.
  `L > 0` forces `z(b) < z(d)` (`L = -τ|R|² - β1 τ (z(b)-z(d))`), so the single peak is `b'`.
* `L < 0`: S1.3b pentagon `(a',c,d,a,c')` at `d - c` (`k17gbY3`, frame `(a-d, b-d, d-c)`, cone `v1 < 0 < v2`).  At
  `pr = 0` the top plateau is `d, a, c'`; the lex needs `w(c') < w(a)`, which is `-L` at the ray `(-1,0)`.
* `L = 0`: leftover.
Numerics (K18 census L4, 1,200 exact Gram samples): `L > 0` ⟹ S1.3a 339/339, `L < 0` ⟹ S1.3b 861/861.
`GA2`, `GB0..GB2` here are copies of the K17GA/K17GB scratch files, recompiled against the rebuilt tree.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 12800000 in
/-- `L > 0`: the S1.3a pentagon at `a - c'` on the tie `pr = 0`. -/
theorem k19_s13a_tie {a a' b b' c c' d : ℝ³} {α1 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 1 < γ4)
    (hb6 : 1 < β6) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) (hL : 0 < ⟪a - d, a - c'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hkey : ⟪c - d, a - c'⟫ = 0 := by
    have e : a - c' = (1 - α1) • (a - d) + (-β1) • (b - d) := by rw [hc']; module
    have h1 : ⟪c - d, a - d⟫ = 0 := by rw [real_inner_comm]; exact hpr
    have h2 : ⟪c - d, b - d⟫ = 0 := by rw [real_inner_comm]; exact hqr
    rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right, h1, h2]; ring
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = 1 / (α1 - 1) := ⟨_, rfl⟩
  have hα1' : 0 < α1 - 1 := by linarith
  have hτ : 0 < τ := by rw [hτdef]; positivity
  have hτα : τ * (α1 - 1) = 1 := by rw [hτdef]; field_simp
  set P := b - d with hP
  set Q := c - d with hQ
  set R := a - c' with hR
  have hRv : R = (1 - α1) • (a - d) - β1 • (b - d) := by rw [hR, hc']; module
  have hpR : a - d = (-τ) • R + (-(β1 * τ)) • P := by
    rw [hRv, hP]
    match_scalars <;> nlinarith
  have hΔ : det3 P Q R ≠ 0 := by
    have e : det3 P Q R = (1 - α1) * det3 (a - d) (b - d) (c - d) := by
      rw [hRv, hP, hQ]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (by linarith) hdet
  have Ea : fpoint P Q R d (-(β1 * τ), 0, -τ) = a := by
    rw [k17ga_fp]; have h := hpR
    linear_combination (norm := module) (-1 : ℝ) • h
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17ga_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17ga_fp, hP]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17ga_fp, hQ]; module
  have Ea' : fpoint P Q R d (β6, 1, 0) = a' := by rw [k17ga_fp, ha', hP, hQ]; module
  have Eb' : fpoint P Q R d (-(1 * β1 * τ), γ4, -(1 * τ)) = b' := by
    rw [k17ga_fp, hb', hQ]; have h := hpR
    linear_combination (norm := module) (-1 : ℝ) • h
  have Ec' : fpoint P Q R d (-(β1 * τ), 0, -(τ + 1)) = c' := by
    rw [k17ga_fp]; have h := hpR
    have : c' = a - R := by rw [hR]; abel
    rw [this]
    linear_combination (norm := module) (-1 : ℝ) • h
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hpRR : ⟪a - d, R⟫ = -τ * ⟪R, R⟫ + (-(β1 * τ)) * ⟪P, R⟫ := by
    rw [hpR, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hR0 : R ≠ 0 := k17ga_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hPQ : ⟪P, Q⟫ = 0 := hqr
  have hQR : ⟪Q, R⟫ = 0 := hkey
  have hLz : 0 < -τ * ⟪R, R⟫ + (-(β1 * τ)) * ⟪P, R⟫ := by rw [← hpRR]; exact hL
  have hα : (1 : ℝ) ≤ 1 := le_rfl
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gaR3 τ β1 1 γ4 β6)
    (k17gaR3_inj hτ hβ1 hα (by linarith)) ?_ [(1, 0), (0, 1)] (by simp) ?_ ?_ ?_
    (ρ1 := 1) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gaR3, pc5_0, Ea]; simp [V8]
    · simp only [k17gaR3, pc5_1, Ed]; simp [V8]
    · simp only [k17gaR3, pc5_2, Eb]; simp [V8]
    · simp only [k17gaR3, pc5_3, Ea']; simp [V8]
    · simp only [k17gaR3, pc5_4, Eb']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (1, 0) (by simp)
    have h2 := hC (0, 1) (by simp)
    simp only at h1 h2
    exact k17ga_r3_tsc hD hτ hβ1 hα hγ4 hb6.le (by linarith) (by linarith) (by nlinarith)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (-(β1 * τ), 0, -τ) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (-(1 * β1 * τ), γ4, -(1 * τ)) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (-(β1 * τ), 0, -(τ + 1)) := by
      rw [Ea, Ed, Eb, Ea', Eb', Ec, Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gaR3, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gaR3, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gaR3, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gaR3, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gaR3, pc5_4])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact (k17ga_r3_rest hD hτ hβ1 hα hγ4 hb6.le (by linarith) (by linarith) (by nlinarith)).1 i
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact (k17ga_r3_rest hD hτ hβ1 hα hγ4 hb6.le (by linarith) (by linarith) (by nlinarith)).2 i
  · intro v1 v2 hC hinj
    have h1 := hC (1, 0) (by simp)
    have h2 := hC (0, 1) (by simp)
    simp only at h1 h2
    have hv1 : 0 < v1 := by linarith
    have hv2 : 0 < v2 := by linarith
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    -- `a < b'` (z tie, `w(b') - w(a) = γ4 v2 |Q|²`)
    have hab' : LexLt (⟪fpoint P Q R d (k17gaR3 τ β1 1 γ4 β6 0), R⟫,
        ⟪fpoint P Q R d (k17gaR3 τ β1 1 γ4 β6 0), fcomb P Q R v1 v2 0⟫)
        (⟪fpoint P Q R d (k17gaR3 τ β1 1 γ4 β6 4), R⟫,
        ⟪fpoint P Q R d (k17gaR3 τ β1 1 γ4 β6 4), fcomb P Q R v1 v2 0⟫) := by
      right
      refine ⟨by simp only [k17gaR3, pc5_0, pc5_4, hz, hQR]; ring, ?_⟩
      simp only [k17gaR3, pc5_0, pc5_4, hwx, hPQ, hQR]
      nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < γ4) hv2) hQQ]
    have hZ : ⟪P, R⟫ < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_pos hτ hRR, mul_nonneg (mul_pos hβ1 hτ).le hh]
    refine k19_lexUni_nb _ _ hinj 4 ?_ ?_ ?_
    · rw [e4]; left; simp only [k17gaR3, pc5_3, pc5_4, hz, hQR]
      nlinarith [mul_pos (sub_pos.2 hb6) (neg_pos.2 hZ)]
    · rw [f4]; exact hab'
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; rw [e0]; exact hab'
      · left; rw [e1]; left; simp only [k17gaR3, pc5_0, pc5_1, hz, hQR]; nlinarith
      · left; rw [e2]; left; simp only [k17gaR3, pc5_1, pc5_2, hz, hQR]; nlinarith
      · left; rw [e3]; left; simp only [k17gaR3, pc5_2, pc5_3, hz, hQR]
        nlinarith [mul_pos (sub_pos.2 hb6) (neg_pos.2 hZ)]
      · exact absurd rfl hi
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> (left; norm_num)

set_option maxHeartbeats 12800000 in
/-- `L < 0`: the S1.3b pentagon at `d - c` on the tie `pr = 0`. -/
theorem k19_s13b_tie {a a' b b' c c' d : ℝ³} {α1 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4)
    (hβ6 : 1 < β6) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) (hL : ⟪a - d, a - c'⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := b - d with hQ
  set R := d - c with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 P Q R := by
      simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h, neg_zero]
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17gb_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gb_fp]; module
  have Eb : fpoint P Q R d (0, 1, 0) = b := by rw [k17gb_fp, hQ]; module
  have Ec : fpoint P Q R d (0, 0, -1) = c := by rw [k17gb_fp, hR]; module
  have Ea' : fpoint P Q R d (0, β6, -1) = a' := by rw [k17gb_fp, ha', hR, hQ]; module
  have Eb' : fpoint P Q R d (1, 0, -γ4) = b' := by rw [k17gb_fp, hb', hR, hP]; module
  have Ec' : fpoint P Q R d (α1, β1, 0) = c' := by rw [k17gb_fp, hc', hP, hQ]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, show d - c = -(c - d) by abel, inner_neg_right, hpr, neg_zero]
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - c = -(c - d) by abel, inner_neg_right, hqr, neg_zero]
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17gb_r0 hΔ)
  have hLf : ⟪a - d, a - c'⟫ = -((α1 - 1) * ⟪P, P⟫ + β1 * ⟪P, Q⟫) := by
    have e : a - c' = (1 - α1) • P + (-β1) • Q := by rw [hc', hP, hQ]; module
    rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
  refine ⟨R, k17gb_r0 hΔ, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gbY3 α1 β1 β6)
    (k17gbY3_inj hα1 hβ1 hβ6) ?_
    [(-1, 0), (0, 1), (-((α1 - 1) * ⟪P, P⟫ + β1 * ⟪P, Q⟫), -((α1 - 1) * ⟪P, Q⟫ + β1 * ⟪Q, Q⟫))] (by simp)
    ?_ ?_ ?_ (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := 1) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gbY3, pc5_0, Ea']; simp [V8]
    · simp only [k17gbY3, pc5_1, Ec]; simp [V8]
    · simp only [k17gbY3, pc5_2, Ed]; simp [V8]
    · simp only [k17gbY3, pc5_3, Ea]; simp [V8]
    · simp only [k17gbY3, pc5_4, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    obtain ⟨h1, h2, -⟩ := k19_cone3 hC
    simp only at h1 h2
    exact k17gb_s13b_tsc hD hα1 hβ1 hβ6 (by linarith) (by linarith)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, β6, -1) ∨ y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
        y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α1, β1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (1, 0, -γ4) := by
      rw [Ea', Ec, Ed, Ea, Ec', Eb, Eb']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gbY3, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gbY3, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gbY3, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gbY3, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gbY3, pc5_4])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, -⟩ := k19_cone3 hC
      simp only at h1 h2
      exact (k17gb_s13b_rest hD hα1 hβ1 hβ6 hγ4 (by linarith) (by linarith)).1 i
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, -⟩ := k19_cone3 hC
      simp only at h1 h2
      exact (k17gb_s13b_rest hD hα1 hβ1 hβ6 hγ4 (by linarith) (by linarith)).2 i
  · intro v1 v2 hC hinj
    obtain ⟨h1, h2, h3⟩ := k19_cone3 hC
    simp only at h1 h2 h3
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    have hc'a : LexLt (⟪fpoint P Q R d (k17gbY3 α1 β1 β6 4), R⟫,
        ⟪fpoint P Q R d (k17gbY3 α1 β1 β6 4), fcomb P Q R v1 v2 0⟫)
        (⟪fpoint P Q R d (k17gbY3 α1 β1 β6 3), R⟫,
        ⟪fpoint P Q R d (k17gbY3 α1 β1 β6 3), fcomb P Q R v1 v2 0⟫) := by
      right
      refine ⟨by simp only [k17gbY3, pc5_3, pc5_4, hz, hPR, hQR]; ring, ?_⟩
      simp only [k17gbY3, pc5_3, pc5_4, hwx, hPR, hQR]; nlinarith
    refine k19_lexUni_nb2 _ _ hinj 2 (by decide) ?_ ?_ ?_
    · rw [e2]; left; simp only [k17gbY3, pc5_1, pc5_2, hz, hPR, hQR]; nlinarith
    · rw [f2, f3]; exact hc'a
    · intro i hi hi'
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; rw [e0]; left; simp only [k17gbY3, pc5_0, pc5_4, hz, hPR, hQR]; nlinarith
      · right; rw [f1]; left; simp only [k17gbY3, pc5_1, pc5_2, hz, hPR, hQR]; nlinarith
      · exact absurd rfl hi
      · exact absurd (by decide) hi'
      · left; rw [e4]; exact hc'a
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; norm_num
    · right; norm_num
    · left; simp only; rw [hLf] at hL; linarith

/-- **S1.3 tie** (`k17ga_s13a` / `k17gb_s13b` leftover `⟪a-b',a-c'⟫ = 0`, β6 > 1): a cell unless `⟪a-d,a-c'⟫ = 0`. -/
theorem k19_s13_tie {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K6tTaA41 a a' b b' c c' d) (hz : ⟪d - b, a - b'⟫ = 0)
    (hβ6 : 0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d)) (h0 : ⟪a - b', a - c'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, a - c'⟫ = 0 := by
  obtain ⟨α1, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hγ4, hβ6', hqr, hLf⟩ :=
    k17gb_a41_frame W hT' h hz
  rw [k17gb_det_beta6 ha'] at hβ6
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  have hb61 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have hpr : ⟪a - d, c - d⟫ = 0 := by
    rw [hLf] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2 <;> (exfalso; linarith)
    · exact h1
  rcases lt_trichotomy ⟪a - d, a - c'⟫ 0 with hn | hz0 | hp
  · exact Or.inl (k19_s13b_tie hdet hc' hb' ha' hα1 (by linarith) (by linarith) hb61 hqr hpr hn)
  · exact Or.inr hz0
  · exact Or.inl (k19_s13a_tie hdet hc' hb' ha' hα1 (by linarith) hγ4 hb61 hqr hpr hp)

end C2
end Type08Sp
end Minimality
