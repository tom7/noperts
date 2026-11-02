module

public import Minimality.Type08S.C2K17GB1

@[expose] public section


/-!
# K17GB / GB2: S1.3b.  A41 + `ζ(d,b) = 0` + `β6 > 1` + `ζ_{a-c'}(a,b') < 0` (`⟺ ⟪a-d,c-d⟫ < 0`):
quad-with-tie cell `(a', c, d, a, c')` at `d - c`, frame `(a-d, b-d, d-c)`, tilt `(-1, λ)`.
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

theorem k17gb_fp (P Q R d : ℝ³) (x y z : ℝ) : fpoint P Q R d (x, y, z) = d + x • P + y • Q + z • R := by
  simp only [fpoint, fcomb]; module

theorem k17gb_r0 {P Q R : ℝ³} (h : det3 P Q R ≠ 0) : R ≠ 0 := by
  intro h0; rw [h0] at h; simp [det3_expand] at h

/-- ccw `a' (0,β6,-1), c (0,0,-1), d 0, a (1,0,0), c' (α1,β1,0)` in the frame `(a-d, b-d, d-c)`. -/
def k17gbY3 (α1 β1 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (0, β6, -1) (0, 0, -1) (0, 0, 0) (1, 0, 0) (α1, β1, 0)

set_option maxHeartbeats 3200000 in
theorem k17gb_s13b_tsc {D α1 β1 β6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6)
    (hv1 : v1 < 0) (hv2 : 0 < v2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k17gbY3 α1 β1 β6 (i + 1) - k17gbY3 α1 β1 β6 i) (k17gbY3 α1 β1 β6 j - k17gbY3 α1 β1 β6 i)
        (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (by linarith : (0:ℝ) < β6)
  have ka1 := mul_pos hD (sub_pos.2 hα1)
  have ka1b := mul_pos (mul_pos hD (sub_pos.2 hα1)) (by linarith : (0:ℝ) < β6)
  have kab := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β6)
  have kab1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (sub_pos.2 hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have knv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD hv2
  have kb6nv1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β6)) (neg_pos.2 hv1)
  have kav2 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) hv2
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k17gbY3, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17gb_s13b_rest {D α1 β1 β6 γ4 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6)
    (hγ4 : 0 < γ4) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    (∀ i : ZMod 5, TSc D (k17gbY3 α1 β1 β6 (i + 1) - k17gbY3 α1 β1 β6 i) ((0, 1, 0) - k17gbY3 α1 β1 β6 i)
        (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k17gbY3 α1 β1 β6 (i + 1) - k17gbY3 α1 β1 β6 i) ((1, 0, -γ4) - k17gbY3 α1 β1 β6 i)
        (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (by linarith : (0:ℝ) < β6)
  have ka1 := mul_pos hD (sub_pos.2 hα1)
  have ka1b := mul_pos (mul_pos hD (sub_pos.2 hα1)) (by linarith : (0:ℝ) < β6)
  have kab := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β6)
  have kab1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (sub_pos.2 hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have knv1 := mul_pos hD (neg_pos.2 hv1)
  have kv2 := mul_pos hD hv2
  have kb6nv1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β6)) (neg_pos.2 hv1)
  have kav2 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) hv2
  have kg := mul_pos hD hγ4
  have kgv2 := mul_pos (mul_pos hD hγ4) hv2
  have kgb1 := mul_pos (mul_pos (mul_pos hD hγ4) hβ1) (neg_pos.2 hv1)
  have kga := mul_pos (mul_pos (mul_pos hD hγ4) (sub_pos.2 hα1)) hv2
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gbY3, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gbY3_inj {α1 β1 β6 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6) :
    ∀ i j, k17gbY3 α1 β1 β6 i = k17gbY3 α1 β1 β6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gbY3, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
/-- **S1.3b cell**: `(a',c,d,a,c')` at `d - c`. -/
theorem k17gb_s13b_cell {a a' b b' c c' d : ℝ³} {α1 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4)
    (hβ6 : 1 < β6) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := b - d with hQ
  set R := d - c with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 P Q R := by simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
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
  have hPR : ⟪P, R⟫ = -⟪a - d, c - d⟫ := by
    rw [hP, hR, show d - c = -(c - d) by abel, inner_neg_right]
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - c = -(c - d) by abel, inner_neg_right, hqr, neg_zero]
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17gb_r0 hΔ)
  refine ⟨R, k17gb_r0 hΔ, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gbY3 α1 β1 β6)
    (k17gbY3_inj hα1 hβ1 hβ6) (u1 := -1) (u2 := 0) (t1 := 0) (t2 := 1) (by norm_num) ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gbY3, pc5_0, Ea']; simp [V8]
    · simp only [k17gbY3, pc5_1, Ec]; simp [V8]
    · simp only [k17gbY3, pc5_2, Ed]; simp [V8]
    · simp only [k17gbY3, pc5_3, Ea]; simp [V8]
    · simp only [k17gbY3, pc5_4, Ec']; simp [V8]
  · intro lam h0 h1 D hD
    exact k17gb_s13b_tsc hD hα1 hβ1 hβ6 (by nlinarith) (by nlinarith)
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
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s13b_rest hD hα1 hβ1 hβ6 hγ4 (by nlinarith) (by nlinarith)).1 i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s13b_rest hD hα1 hβ1 hβ6 hγ4 (by nlinarith) (by nlinarith)).2 i
  · intro w hw
    refine k17gb_lex5_plat01 _ w hw ?_ ?_ ?_ ?_
    · simp only [k17gbY3, pc5_0, pc5_2, hz, hPR, hQR]; nlinarith
    · simp only [k17gbY3, pc5_1, pc5_2, hz, hPR, hQR]; nlinarith
    · simp only [k17gbY3, pc5_2, pc5_3, hz, hPR, hQR]; nlinarith
    · simp only [k17gbY3, pc5_3, pc5_4, hz, hPR, hQR]; nlinarith

/-- **S1.3b**: `K6tTaA41` (with `¬ T'`), `ζ(d,b) = 0`, `β6 > 1`: a lex cell unless `ζ_{a-c'}(a,b') ≥ 0`. -/
theorem k17gb_s13b {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K6tTaA41 a a' b b' c c' d) (hz : ⟪d - b, a - b'⟫ = 0)
    (hβ6 : 0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d)) :
    HasLexCell (V8 a a' b b' c c' d) ∨ 0 ≤ ⟪a - b', a - c'⟫ := by
  obtain ⟨α1, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hγ4, hβ6', hqr, hL⟩ :=
    k17gb_a41_frame W hT' h hz
  by_cases hle : 0 ≤ ⟪a - b', a - c'⟫
  · exact Or.inr hle
  · push Not at hle
    left
    rw [k17gb_det_beta6 ha'] at hβ6
    have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
    have hb61 : 1 < β6 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
    have hpr : ⟪a - d, c - d⟫ < 0 := by
      rw [hL] at hle
      by_contra hh; push Not at hh
      have : 0 < γ4 * (α1 - 1) := mul_pos (by linarith) (by linarith)
      nlinarith
    exact k17gb_s13b_cell hdet hc' hb' ha' hα1 (by linarith) (by linarith) hb61 hqr hpr

end C2
end Type08Sp
end Minimality
