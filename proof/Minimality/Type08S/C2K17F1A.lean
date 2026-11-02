module

public import Minimality.Type08S.C2K17BZ

@[expose] public section


/-!
# K17F / P1: S1.7 (Pa(2): `ζ(b',c) = 0`, `β1 = 1`, `α4 < 1`) -- metric-free, split by the sign of `⟪a-d,c-d⟫`.

Frame data (`k17f_pa2_frame`): T' frame with `β1 = γ4 = 1` and `⟪a-d,b-d⟫ = 0`.
* `pr = ⟪a-d,c-d⟫ > 0`: pentagon `(a,d,b,a',b')` at `a - d`, frame `(b-d, c-d, a-d)`, tilt `(1 + λ(β6+γ6-1), -1)`.
* `pr < 0`: hexagon `(a,b',c,a',b,c')` at `a - d`, frame `(c-d, b-d, a-d)`, tilt `(γ6, β6 + λ)`.
* `pr = 0`: leftover (codim + 1).
No ParEnd / Coll5 data is used: the T/T' tie slices are metric-free (K17F numerics).
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
open C2

/-! ## Frame data of the Pa(2) slice -/

/-- **Relation lemma, Pa(2) (`K14LeftPa` 2nd disjunct, `β1 = 1` branch).**  T' frame with `β1 = γ4 = 1`, `α4 < 1`,
`γ6 < 1` and the tie as `⟪a-d,b-d⟫ = 0`. -/
theorem k17f_pa2_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h0 : ⟪b' - c, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) :
    ∃ α4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d) ∧ b' = d + α4 • (a - d) + (1 : ℝ) • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ α4 < 1 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 ∧
      ⟪a - d, b - d⟫ = 0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, hαγ, hβ6, hγ6, hs, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_beta1 hc'] at hβ
  have hb1 : β1 = 1 := by
    have : (β1 - 1) * (det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d)) = 0 := by
      linear_combination hβ
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hΔ2.ne'
  subst hb1
  rw [det_alpha4 hb'] at hα
  have hα1 : α4 < 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have hg4 : γ4 = 1 := by
    have := (planar_a_iff hdet hc' hb').1 hκ
    linarith
  subst hg4
  have hpq : ⟪a - d, b - d⟫ = 0 := by
    have e : b' - c = α4 • (a - d) := by rw [hb']; module
    have e2 : d - b = -(b - d) := by abel
    rw [e, e2, inner_smul_left, inner_neg_right] at h0
    simp only [conj_trivial] at h0
    have : α4 * ⟪a - d, b - d⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  exact ⟨α4, β6, γ6, hdet, hc', hb', ha', hα4, hα1, hβ6, hγ6, hfa hfar, hs, hpq⟩

/-! ## The pentagon `(a,d,b,a',b')` at `a - d` (frame `(b-d, c-d, a-d)`) -/

/-- ccw pentagon `a (0,0,1), d (0,0,0), b (1,0,0), a' (β6,γ6,0), b' (0,1,α4)`. -/
def k17fPent (α4 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (0, 0, 1) (0, 0, 0) (1, 0, 0) (β6, γ6, 0) (0, 1, α4)

set_option maxHeartbeats 3200000 in
theorem k17f_pent_tsc {D α4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0)
    (hc1 : (1 - γ6) * v1 < β6 * (-v2)) (hc2 : (1 - β6) * (-v2) < γ6 * v1) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k17fPent α4 β6 γ6 (i + 1) - k17fPent α4 β6 γ6 i) (k17fPent α4 β6 γ6 j - k17fPent α4 β6 γ6 i)
        (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kb := mul_pos hD hβ6
  have ka := mul_pos hD hα4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kc1 := mul_pos hD (sub_pos.2 hc1)
  have kc2 := mul_pos hD (sub_pos.2 hc2)
  have kgv := mul_pos (mul_pos hD hγ6) hv1
  have kbv := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  have kav := mul_pos (mul_pos hD hα4) hv1
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k17fPent, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17f_pent_rest {D α4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0)
    (hc1 : (1 - γ6) * v1 < β6 * (-v2)) (hc2 : (1 - β6) * (-v2) < γ6 * v1) :
    (∀ i : ZMod 5, TSc D (k17fPent α4 β6 γ6 (i + 1) - k17fPent α4 β6 γ6 i) ((0, 1, 0) - k17fPent α4 β6 γ6 i)
        (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k17fPent α4 β6 γ6 (i + 1) - k17fPent α4 β6 γ6 i) ((1, 0, 1) - k17fPent α4 β6 γ6 i)
        (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kb := mul_pos hD hβ6
  have ka := mul_pos hD hα4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kc1 := mul_pos hD (sub_pos.2 hc1)
  have kc2 := mul_pos hD (sub_pos.2 hc2)
  have kgv := mul_pos (mul_pos hD hγ6) hv1
  have kbv := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  have kav := mul_pos (mul_pos hD hα4) hv1
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17fPent, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17fPent_inj {α4 β6 γ6 : ℝ} (hα4 : 0 < α4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, k17fPent α4 β6 γ6 i = k17fPent α4 β6 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17fPent, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

/-! ## The hexagon `(a,b',c,a',b,c')` at `a - d` (frame `(c-d, b-d, a-d)`) -/

/-- ccw hexagon `a (0,0,1), b' (1,0,α4), c (1,0,0), a' (γ6,β6,0), b (0,1,0), c' (0,1,1)`. -/
def k17fHex (α4 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 0, 1) (1, 0, α4) (1, 0, 0) (γ6, β6, 0) (0, 1, 0) (0, 1, 1)

set_option maxHeartbeats 3200000 in
theorem k17f_hex_tsc {D α4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hγ61 : γ6 < 1) (hv1 : 0 < v1) (hv2 : 0 < v2) (hc : (β6 - 1) * v1 < γ6 * v2) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k17fHex α4 β6 γ6 (i + 1) - k17fHex α4 β6 γ6 i) (k17fHex α4 β6 γ6 j - k17fHex α4 β6 γ6 i)
        (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kb := mul_pos hD hβ6
  have ka := mul_pos hD hα4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kc := mul_pos hD (sub_pos.2 hc)
  have kav1 := mul_pos (mul_pos hD hα4) hv1
  have kav2 := mul_pos (mul_pos hD hα4) hv2
  have kabv := mul_pos (mul_pos (mul_pos hD hα4) hv1) hβ6
  have kagv := mul_pos (mul_pos (mul_pos hD hα4) hv2) (sub_pos.2 hγ61)
  intro i j h1 h2'
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k17fHex, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17f_hex_rest {D α4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hγ61 : γ6 < 1) (hv1 : 0 < v1) (hv2 : 0 < v2) (hc : (β6 - 1) * v1 < γ6 * v2) :
    ∀ i : ZMod 6, TSc D (k17fHex α4 β6 γ6 (i + 1) - k17fHex α4 β6 γ6 i) ((0, 0, 0) - k17fHex α4 β6 γ6 i)
        (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kb := mul_pos hD hβ6
  have ka := mul_pos hD hα4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kc := mul_pos hD (sub_pos.2 hc)
  intro i
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17fHex, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17fHex_inj {α4 β6 γ6 : ℝ} (hα4 : 0 < α4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, k17fHex α4 β6 γ6 i = k17fHex α4 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17fHex, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

/-! ## The two cells and S1.7 -/

theorem k17f_fp (P Q R d : ℝ³) (x y z : ℝ) : fpoint P Q R d (x, y, z) = d + x • P + y • Q + z • R := by
  simp only [fpoint, fcomb]; module

theorem k17f_r0 {P Q R : ℝ³} (h : det3 P Q R ≠ 0) : R ≠ 0 := by
  intro h0; rw [h0] at h; simp [det3_expand] at h

set_option maxHeartbeats 3200000 in
/-- **S1.7, `pr > 0`**: pentagon `(a,d,b,a',b')` at `a - d`. -/
theorem k17f_s17_pent {a a' b b' c c' d : ℝ³} {α4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α4 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hpq : ⟪a - d, b - d⟫ = 0)
    (hpr : 0 < ⟪a - d, c - d⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  set P := b - d with hP
  set Q := c - d with hQ
  set R := a - d with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by simp only [hP, hQ, hR, det3_expand]; ring
    rw [e, h]
  have Ea : fpoint P Q R d (0, 0, 1) = a := by rw [k17f_fp, hR]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17f_fp, hP]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17f_fp, hQ]; module
  have Ea' : fpoint P Q R d (β6, γ6, 0) = a' := by rw [k17f_fp, ha']; module
  have Eb' : fpoint P Q R d (0, 1, α4) = b' := by rw [k17f_fp, hb']; module
  have Ec' : fpoint P Q R d (1, 0, 1) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hPR : ⟪P, R⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have hQR : 0 < ⟪Q, R⟫ := by rw [real_inner_comm]; exact hpr
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17f_r0 hΔ)
  set s := β6 + γ6 - 1 with hsdef
  have hs0 : 0 < s := by linarith
  have hlam : ∀ lam : ℝ, 0 < lam → lam < 1 → (1 - γ6) * (1 + lam * s) < β6 * (-(-1 + lam * 0)) := by
    intro lam h0 h1; nlinarith [mul_pos (sub_pos.2 hγ61) (mul_pos hs0 (sub_pos.2 h1))]
  have hlam2 : ∀ lam : ℝ, 0 < lam → lam < 1 → (1 - β6) * (-(-1 + lam * 0)) < γ6 * (1 + lam * s) := by
    intro lam h0 h1; nlinarith [mul_pos (mul_pos hγ6 h0) hs0]
  have hlam0 : ∀ lam : ℝ, 0 < lam → 0 < 1 + lam * s := fun lam h0 => by nlinarith [mul_pos h0 hs0]
  refine ⟨R, k17f_r0 hΔ, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17fPent α4 β6 γ6)
    (k17fPent_inj hα4 hβ6 hγ6) (u1 := 1) (u2 := -1) (t1 := s) (t2 := 0) (by nlinarith) ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17fPent, pc5_0, Ea]; simp [V8]
    · simp only [k17fPent, pc5_1, Ed]; simp [V8]
    · simp only [k17fPent, pc5_2, Eb]; simp [V8]
    · simp only [k17fPent, pc5_3, Ea']; simp [V8]
    · simp only [k17fPent, pc5_4, Eb']; simp [V8]
  · intro lam h0 h1 D hD
    exact k17f_pent_tsc hD hα4 hβ6 hγ6 hs (hlam0 lam h0) (by norm_num) (hlam lam h0 h1) (hlam2 lam h0 h1)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (0, 1, α4) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (1, 0, 1) := by
      rw [Ea, Ed, Eb, Ea', Eb', Ec, Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17fPent, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17fPent, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17fPent, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17fPent, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17fPent, pc5_4])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17f_pent_rest hD hα4 hβ6 hγ6 hs (hlam0 lam h0) (by norm_num) (hlam lam h0 h1)
        (hlam2 lam h0 h1)).1 i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17f_pent_rest hD hα4 hβ6 hγ6 hs (hlam0 lam h0) (by norm_num) (hlam lam h0 h1)
        (hlam2 lam h0 h1)).2 i
  · intro w hw
    refine lexUni5_top _ w hw ?_ ?_ ?_
    · left; simp only [k17fPent, pc5_0, pc5_1, hz, hPR]; nlinarith
    · left; simp only [k17fPent, pc5_2, pc5_3, hz, hPR]; nlinarith [mul_pos hγ6 hQR]
    · left; simp only [k17fPent, pc5_3, pc5_4, hz, hPR]
      nlinarith [mul_pos hα4 hRR, mul_pos (sub_pos.2 hγ61) hQR]

set_option maxHeartbeats 3200000 in
/-- **S1.7, `pr < 0`**: hexagon `(a,b',c,a',b,c')` at `a - d`. -/
theorem k17f_s17_hex {a a' b b' c c' d : ℝ³} {α4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α4 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hpq : ⟪a - d, b - d⟫ = 0)
    (hpr : ⟪a - d, c - d⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  set P := c - d with hP
  set Q := b - d with hQ
  set R := a - d with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 P Q R := by simp only [hP, hQ, hR, det3_expand]; ring
    rw [e, h, neg_zero]
  have Ea : fpoint P Q R d (0, 0, 1) = a := by rw [k17f_fp, hR]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (0, 1, 0) = b := by rw [k17f_fp, hQ]; module
  have Ec : fpoint P Q R d (1, 0, 0) = c := by rw [k17f_fp, hP]; module
  have Ea' : fpoint P Q R d (γ6, β6, 0) = a' := by rw [k17f_fp, ha']; module
  have Eb' : fpoint P Q R d (1, 0, α4) = b' := by rw [k17f_fp, hb']; module
  have Ec' : fpoint P Q R d (0, 1, 1) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hQR : ⟪Q, R⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have hPR : ⟪P, R⟫ < 0 := by rw [real_inner_comm]; exact hpr
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17f_r0 hΔ)
  refine ⟨R, k17f_r0 hΔ, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k17fHex α4 β6 γ6)
    (k17fHex_inj hα4 hβ6 hγ6) (u1 := γ6) (u2 := β6) (t1 := 0) (t2 := 1) (by nlinarith) ?_ ?_ ?_ ?_
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k17fHex, pc6_0, Ea]; simp [V8]
    · simp only [k17fHex, pc6_1, Eb']; simp [V8]
    · simp only [k17fHex, pc6_2, Ec]; simp [V8]
    · simp only [k17fHex, pc6_3, Ea']; simp [V8]
    · simp only [k17fHex, pc6_4, Eb]; simp [V8]
    · simp only [k17fHex, pc6_5, Ec']; simp [V8]
  · intro lam h0 h1 D hD
    exact k17f_hex_tsc hD hα4 hβ6 hγ6 hs hγ61 (by nlinarith) (by nlinarith) (by nlinarith)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (1, 0, α4) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (γ6, β6, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 1, 1) ∨
        y = fpoint P Q R d (0, 0, 0) := by
      rw [Ea, Eb', Ec, Ea', Eb, Ec', Ed]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17fHex, pc6_0])).elim
    · exact (hyx 1 (by simp only [k17fHex, pc6_1])).elim
    · exact (hyx 2 (by simp only [k17fHex, pc6_2])).elim
    · exact (hyx 3 (by simp only [k17fHex, pc6_3])).elim
    · exact (hyx 4 (by simp only [k17fHex, pc6_4])).elim
    · exact (hyx 5 (by simp only [k17fHex, pc6_5])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact k17f_hex_rest hD hα4 hβ6 hγ6 hs hγ61 (by nlinarith) (by nlinarith) (by nlinarith) i
  · intro w hw
    refine lexUni6_top2 _ w hw ?_ ?_ ?_ ?_
    · left; simp only [k17fHex, pc6_0, pc6_1, hz, hQR]; nlinarith [mul_pos (sub_pos.2 hα41) hRR]
    · left; simp only [k17fHex, pc6_2, pc6_3, hz, hQR]; nlinarith [mul_pos (sub_pos.2 hγ61) (neg_pos.2 hPR)]
    · left; simp only [k17fHex, pc6_3, pc6_4, hz, hQR]; nlinarith [mul_pos hγ6 (neg_pos.2 hPR)]
    · left; left; simp only [k17fHex, pc6_4, pc6_5, hz, hQR]; nlinarith

/-- **S1.7** (Pa(2) with `β1 = 1`): a cell, or the leftover tie `⟪a-d,c-d⟫ = 0` (codim + 1). -/
theorem k17f_s17 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h0 : ⟪b' - c, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, c - d⟫ = 0 := by
  obtain ⟨α4, β6, γ6, hdet, hc', hb', ha', hα4, hα41, hβ6, hγ6, hγ61, hs, hpq⟩ :=
    k17f_pa2_frame W hT' hκ hfar h0 hα hβ
  rcases lt_trichotomy ⟪a - d, c - d⟫ 0 with h | h | h
  · exact Or.inl (k17f_s17_hex hdet hc' hb' ha' hα4 hα41 hβ6 hγ6 hγ61 hs hpq h)
  · exact Or.inr h
  · exact Or.inl (k17f_s17_pent hdet hc' hb' ha' hα4 hα41 hβ6 hγ6 hγ61 hs hpq h)

end Type08Sp
end Minimality
