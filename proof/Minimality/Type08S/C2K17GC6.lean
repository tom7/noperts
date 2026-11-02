module

public import Minimality.Type08S.C2K17GC5

@[expose] public section


/-!
# K17GC / GC6: U1 (`K14LeftPa` 1st disjunct: Pa(1), `ζ(a,c) = ζ(a,d) = 0` at `d - b`, `α4 ≤ 1`).

The ties give `⟪p,q⟫ = ⟪q,r⟫ = 0`: `d - b` is the normal of the face `Q_ac`, and `a, d, c, b'` (all in that plane) are a
4-plateau at the top (`c', b, a'` below).  Everything on the screen is affine; the plateau order is decided by the tilt
functional restricted to the plane.  Split by `pr = ⟪a-d,c-d⟫`:
* `pr > 0` (U1b): the U2b pentagon `(b,c',b',c,d)` (`k17gc_u2b_cell`, valid for `α4 ≤ 1`, any `β1 > 0`): plateau
  `b',c,d`, tilt with `w(c) > w(d)`.
* `pr < 0` (U1a): pentagon `(a,d,c,b',c')` at `d - b`, frame `(c-d, a-d, d-b)`, cone `v1, v2 > 0`; tilt
  `v = (pp + rr) r + λ(-pr) p` gives `w(a) < w(d) < w(c)` (Cauchy-Schwarz for `w(c) > w(d)`), so the plateau path
  `a,d,c,b'` rises to `c` or `b'` (`lexUni5_two`) whatever `w(b')` is.
* `pr = 0`: leftover (the split literal's tie: `p, q, r` pairwise orthogonal).
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

/-- **Relation lemma, U1**: T' frame, `α4 ≤ 1`, `⟪p,q⟫ = ⟪q,r⟫ = 0`. -/
theorem k17gc_u1_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h1 : ⟪a - c, d - b⟫ = 0) (h2 : ⟪a - d, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≤ 0) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ α4 ≤ 1 ∧ 0 < β1 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧
      0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ ⟪a - d, b - d⟫ = 0 ∧ ⟪b - d, c - d⟫ = 0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, hαγ, hβ6, hγ6, hs, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_alpha4 hb'] at hα
  have hα1 : α4 ≤ 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos (sub_pos.2 hh) hΔ2]
  have e2 : d - b = -(b - d) := by abel
  have hpq : ⟪a - d, b - d⟫ = 0 := by
    rw [e2, inner_neg_right] at h2; linarith
  have hqr : ⟪b - d, c - d⟫ = 0 := by
    have e : a - c = (a - d) - (c - d) := by abel
    rw [e, e2, inner_neg_right, inner_sub_left, hpq, real_inner_comm] at h1; linarith
  exact ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hα1, hβ1, hγ4, hαγ, hβ6, hγ6, hfa hfar, hpq, hqr⟩

/-- ccw pentagon `a (0,1,0), d 0, c (1,0,0), b' (γ4,α4,0), c' (0,1,-β1)` (frame `(c-d, a-d, d-b)`). -/
def k17gcPentU1 (α4 β1 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (0, 1, 0) (0, 0, 0) (1, 0, 0) (γ4, α4, 0) (0, 1, -β1)

set_option maxHeartbeats 6400000 in
theorem k17gc_pentU1_tsc {α4 β1 γ4 β6 γ6 v1 v2 : ℝ} (hα4 : 0 < α4) (hα41 : α4 ≤ 1) (hβ1 : 0 < β1)
    (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcPentU1 α4 β1 γ4 (i + 1) - k17gcPentU1 α4 β1 γ4 i)
        (k17gcPentU1 α4 β1 γ4 j - k17gcPentU1 α4 β1 γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (γ6, 0, -β6)], ∀ i : ZMod 5,
      TSc 1 (k17gcPentU1 α4 β1 γ4 (i + 1) - k17gcPentU1 α4 β1 γ4 i) (t - k17gcPentU1 α4 β1 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have ka : 0 ≤ 1 - α4 := by linarith
  have kag := sub_pos.2 hαγ
  have k1 := mul_pos hβ1 hv1
  have k2 := mul_pos hβ1 hv2
  have k3 := mul_pos hγ4 hv2
  have k4 := mul_pos hγ4 hv1
  have k5 := mul_pos hα4 hv1
  have k6 := mul_pos hα4 hv2
  have k7 := mul_pos hγ6 hv2
  have k8 := mul_pos hβ6 hv2
  have k9 := mul_nonneg ka hv1.le
  have k10 := mul_pos (mul_pos hβ1 hγ4) hv2
  have k11 := mul_pos (mul_pos hβ1 hα4) hv1
  have k12 := mul_nonneg (mul_pos hβ1 hv1).le ka
  have k13 := mul_pos kag hβ1
  have k14 := mul_pos (mul_pos kag hβ1) hv2
  have k15 := mul_pos (mul_pos kag hβ1) hv1
  have k16 := mul_pos (mul_pos hβ6 hγ4) hv2
  have k17 := mul_pos (mul_pos hβ6 hα4) hv1
  have k18 := mul_pos (sub_pos.2 hγ61) hv2
  have k19 := mul_pos kag hv1
  have k20 := mul_pos kag hv2
  have k21 := mul_pos (mul_pos hγ6 hα4) hv2
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcPentU1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcPentU1, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcPentU1_inj {α4 β1 γ4 : ℝ} (hα4 : 0 < α4) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) :
    ∀ i j, k17gcPentU1 α4 β1 γ4 i = k17gcPentU1 α4 β1 γ4 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcPentU1, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
/-- **U1a cell** (`pr < 0`): pentagon `(a,d,c,b',c')` at `d - b` on the 4-plateau `a,d,c,b'`. -/
theorem k17gc_u1a_cell {a a' b b' c c' d : ℝ³} {α4 β1 γ4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 ≤ 1) (hβ1 : 0 < β1)
    (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := c - d with hP
  set Q := a - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 P Q R := by
      simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h, neg_zero]
  have Ea : fpoint P Q R d (0, 1, 0) = a := by rw [k17gc_fp, hQ]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gc_fp]; module
  have Eb : fpoint P Q R d (0, 0, -1) = b := by rw [k17gc_fp, hR]; module
  have Ec : fpoint P Q R d (1, 0, 0) = c := by rw [k17gc_fp, hP]; module
  have Ea' : fpoint P Q R d (γ6, 0, -β6) = a' := by rw [k17gc_fp, ha', hP, hR]; module
  have Eb' : fpoint P Q R d (γ4, α4, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (0, 1, -β1) = c' := by rw [k17gc_fp, hc', hQ, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm, hqr, neg_zero]
  have hPQ : ⟪P, Q⟫ < 0 := by rw [hP, hQ, real_inner_comm]; exact hpr
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hCS : ⟪P, Q⟫ * ⟪P, Q⟫ ≤ ⟪P, P⟫ * ⟪Q, Q⟫ := real_inner_mul_inner_self_le P Q
  refine ⟨R, hR0, ?_⟩
  refine cyc_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gcPentU1 α4 β1 γ4)
    (k17gcPentU1_inj hα4 hβ1 hγ4) ?_ [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (γ6, 0, -β6)] ?_
    (u1 := ⟪P, P⟫ + ⟪Q, Q⟫) (u2 := 0) (t1 := 0) (t2 := -⟪P, Q⟫)
    (by nlinarith [mul_pos (add_pos hPP hQQ) (neg_pos.2 hPQ)]) (lo := 0) (hi := 1) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ 0 < v2 ∧ v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫ < 0 ∧ 0 < v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gcPentU1, pc5_0, Ea]; simp [V8]
    · simp only [k17gcPentU1, pc5_1, Ed]; simp [V8]
    · simp only [k17gcPentU1, pc5_2, Ec]; simp [V8]
    · simp only [k17gcPentU1, pc5_3, Eb']; simp [V8]
    · simp only [k17gcPentU1, pc5_4, Ec']; simp [V8]
  · intro y hy
    have hV : y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (γ4, α4, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨ y = fpoint P Q R d (0, 0, -1) ∨
        y = fpoint P Q R d (γ6, 0, -β6) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by nlinarith, by nlinarith [mul_pos h0 (neg_pos.2 hPQ)], ?_, ?_⟩
    · have e : (⟪P, P⟫ + ⟪Q, Q⟫ + lam * 0) * ⟪P, Q⟫ + (0 + lam * -⟪P, Q⟫) * ⟪Q, Q⟫ =
          ⟪P, Q⟫ * (⟪P, P⟫ + (1 - lam) * ⟪Q, Q⟫) := by ring
      rw [e]
      have k := mul_pos (sub_pos.2 h1) hQQ
      exact mul_neg_of_neg_of_pos hPQ (by nlinarith)
    · have e : (⟪P, P⟫ + ⟪Q, Q⟫ + lam * 0) * ⟪P, P⟫ + (0 + lam * -⟪P, Q⟫) * ⟪P, Q⟫ =
          ⟪P, P⟫ * ⟪P, P⟫ + ⟪P, P⟫ * ⟪Q, Q⟫ - lam * (⟪P, Q⟫ * ⟪P, Q⟫) := by ring
      rw [e]
      have k := mul_pos (mul_pos (sub_pos.2 h1) hPP) hQQ
      have k2 := mul_le_mul_of_nonneg_left hCS h0.le
      nlinarith [mul_pos hPP hPP]
  · rintro v1 v2 ⟨hv1, hv2, -, -⟩
    exact k17gc_pentU1_tsc hα4 hα41 hβ1 hγ4 hαγ hβ6 hγ6 hγ61 hv1 hv2
  · rintro v1 v2 ⟨-, -, hfa, hfc⟩ hinj
    refine lexUni5_two _ _ hinj ?_ ?_ (Or.inl ?_)
    · right
      simp only [k17gcPentU1, pc5_1, pc5_2]
      refine ⟨by rw [hz, hz, hPR, hQR]; simp only; ring, ?_⟩
      rw [k17f_wexp, k17f_wexp]; simp only; nlinarith
    · left; simp only [k17gcPentU1, pc5_3, pc5_4, hz, hPR, hQR]; nlinarith [mul_pos hβ1 hRR]
    · right
      simp only [k17gcPentU1, pc5_0, pc5_1]
      refine ⟨by rw [hz, hz, hPR, hQR]; simp only; ring, ?_⟩
      rw [k17f_wexp, k17f_wexp]; simp only; nlinarith

/-- **U1** (`K14LeftPa` 1st disjunct: `ζ(a,c) = ζ(a,d) = 0`, `α4 ≤ 1`): a cell, or the tie `⟪a-d,c-d⟫ = 0`. -/
theorem k17gc_u1 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (h1 : ⟪a - c, d - b⟫ = 0) (h2 : ⟪a - d, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ≤ 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, c - d⟫ = 0 := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hα41, hβ1, hγ4, hαγ, hβ6, hγ6, hγ61, hpq, hqr⟩ :=
    k17gc_u1_frame W hT' (k5z_far1 W hT' hnT) h1 h2 hα
  rcases lt_trichotomy ⟪a - d, c - d⟫ 0 with hn | h0 | hp
  · exact Or.inl (k17gc_u1a_cell hdet hc' hb' ha' hα4 hα41 hβ1 hγ4 hαγ hβ6 hγ6 hγ61 hpq hqr hn)
  · exact Or.inr h0
  · exact Or.inl (k17gc_u2b_cell hdet hc' hb' ha' hα4 hα41 hβ1 hγ4 hαγ hβ6 hγ6 hγ61 hpq hqr hp)

end C2
end Type08Sp
end Minimality
