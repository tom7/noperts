module

public import Minimality.Type08S.C2K17GC2

@[expose] public section


/-!
# K17GC / GC3: S1.6a (QPc, `u = 0 < w`, `pq < 0`): hexagon `(a,b',c,a',b,d)` at `c - a'`, and the S1.6 wrapper.

Frame of `k6t3_pc1` (C2K6TCG): `P = a-d`, `Q = (b-d)/m`, `R = (c-a')/m`, `m = 1-γ6`; `a (1,0,0)`, `b' (1,γ4,γ4)`,
`c (0,1,1)`, `a' (0,1,1-m)`, `b (0,m,0)`, `d 0`, `c' (1,β1 m,0)`.  `u = 0` is `⟪P,R⟫ = 0`, so `z(a) = z(d)`;
`w > 0` is `⟪Q,R⟫ + ⟪R,R⟫ > 0`: `a < b'`, `b < a' < c`.  TS cone `v1 < 0 ∧ v2 < (γ4-1) v1` (zero screen edge `c a'`,
`c'` on the screen edge `a b'` since `β1 m < γ4`).  Lex: `w(a) > w(d)` (`v1 ⟪P,P⟫ + v2 ⟪P,Q⟫ > 0`), then
`lexUni6_two` (peak `b'` or `c`).  Segment `(λ⟪P,Q⟫, -(⟪P,P⟫ - (γ4+1)⟪P,Q⟫))`.
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

/-- ccw hexagon `a (1,0,0), b' (1,γ4,γ4), c (0,1,1), a' (0,1,1-m), b (0,m,0), d 0` (frame of `k6t3_pc1`). -/
def k17gcHexC (m γ4 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (1, 0, 0) (1, γ4, γ4) (0, 1, 1) (0, 1, 1 - m) (0, m, 0) (0, 0, 0)

set_option maxHeartbeats 6400000 in
theorem k17gc_hexC_tsc {m γ4 e v1 v2 : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hγ4 : 0 < γ4) (he : 0 < e)
    (heg : e < γ4) (hv1 : v1 < 0) (hv2 : v2 < (γ4 - 1) * v1) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcHexC m γ4 (i + 1) - k17gcHexC m γ4 i) (k17gcHexC m γ4 j - k17gcHexC m γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), e, (0 : ℝ))], ∀ i : ZMod 6,
      TSc 1 (k17gcHexC m γ4 (i + 1) - k17gcHexC m γ4 i) (t - k17gcHexC m γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have n1 : 0 < -v1 := by linarith
  have n2 : 0 < (γ4 - 1) * v1 - v2 := by linarith
  have n3 : 0 < -v1 - v2 := by nlinarith
  have km1 := sub_pos.2 hm1
  have k1 := mul_pos hm0 n1
  have k2 := mul_pos hm0 n2
  have k3 := mul_pos km1 n1
  have k4 := mul_pos hγ4 n1
  have k5 := mul_pos he n1
  have k6 := mul_pos (sub_pos.2 heg) n1
  have k7 := mul_pos (mul_pos hm0 km1) n1
  have k8 := mul_pos hm0 hγ4
  have k9 := mul_pos km1 hγ4
  have k10 := mul_pos hm0 km1
  have k11 := mul_pos (mul_pos hm0 hγ4) n1
  have k12 := mul_pos hm0 n3
  have k13 := mul_pos (sub_pos.2 heg) hm0
  have k14 := mul_pos (mul_pos (sub_pos.2 heg) hm0) n1
  have k15 := mul_pos km1 n2
  have k16 := mul_pos hγ4 n2
  have k17 := mul_pos he n2
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcHexC, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcHexC, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcHexC_inj {m γ4 : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hγ4 : 0 < γ4) :
    ∀ i j, k17gcHexC m γ4 i = k17gcHexC m γ4 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcHexC, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
/-- **S1.6a cell**: Pc frame, `u = 0`, `w > 0`, `⟪a-d,b-d⟫ < 0`: the hexagon `(a,b',c,a',b,d)` at `c - a'`. -/
theorem k17gc_s16a_cell {a a' b b' c c' d : ℝ³} {β1 γ4 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hfacet : β1 * (1 - γ6) < γ4) (hu : ⟪c - a', a - d⟫ = 0) (hw : 0 < ⟪c - d, c - a'⟫)
    (hpq : ⟪a - d, b - d⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  set m : ℝ := 1 - γ6 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hm1 : m < 1 := by rw [hm]; linarith
  have hmne : m ≠ 0 := hm0.ne'
  have hγ6m : γ6 = 1 - m := by rw [hm]; ring
  set P := a - d with hP
  set Q := (1 / m) • (b - d) with hQ
  set R := (1 / m) • (c - a') with hR
  have hca' : c - a' = m • (c - d) - (b - d) := by
    rw [ha', hγ6m]; module
  have hΔ0 : det3 P Q R = det3 (a - d) (b - d) (c - d) / m := by
    rw [hP, hQ, hR, hca']
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hΔ : det3 P Q R ≠ 0 := by rw [hΔ0]; exact div_ne_zero hdet hmne
  have hfp : ∀ x y z : ℝ, fpoint P Q R d (x, y, z) = d + x • P + y • Q + z • R := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint P Q R d (0, 0, 0) = d := by rw [hfp]; simp
  have eA : fpoint P Q R d (1, 0, 0) = a := by rw [hfp, hP]; module
  have eB' : fpoint P Q R d (1, γ4, γ4) = b' := by
    rw [hfp, hb', hP, hQ, hR, hca']; match_scalars <;> field_simp <;> ring
  have eC : fpoint P Q R d (0, 1, 1) = c := by
    rw [hfp, hQ, hR, hca']; match_scalars <;> field_simp <;> ring
  have eA' : fpoint P Q R d (0, 1, 1 - m) = a' := by
    rw [hfp, hQ, hR, hca', ha', hγ6m]
    match_scalars <;> field_simp <;> ring
  have eC' : fpoint P Q R d (1, β1 * m, 0) = c' := by
    rw [hfp, hc', hP, hQ]; match_scalars <;> field_simp <;> ring
  have eB : fpoint P Q R d (0, m, 0) = b := by
    rw [hfp, hQ]; match_scalars <;> field_simp <;> ring
  have hmpos : 0 < 1 / m := by positivity
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, real_inner_smul_right, real_inner_comm, hu, mul_zero]
  have hw' : ⟪Q, R⟫ + ⟪R, R⟫ = (1 / m) * ⟪c - d, c - a'⟫ := by
    rw [← inner_add_left]
    have : Q + R = c - d := by
      rw [hQ, hR, hca']; match_scalars <;> field_simp <;> ring
    rw [this, hR, real_inner_smul_right]
  have hw0 : 0 < ⟪Q, R⟫ + ⟪R, R⟫ := by rw [hw']; exact mul_pos hmpos hw
  have hPQ : ⟪P, Q⟫ < 0 := by
    rw [hP, hQ, real_inner_smul_right]; exact mul_neg_of_pos_of_neg hmpos hpq
  have hR0 : R ≠ 0 := by
    intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have he : 0 < β1 * m := mul_pos hβ1 hm0
  have heg : β1 * m < γ4 := by rw [hm]; exact hfacet
  set X := ⟪P, P⟫ - (γ4 + 1) * ⟪P, Q⟫ with hX
  have hPP : 0 < ⟪P, P⟫ := by
    have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
    exact real_inner_self_pos.2 hP0
  have hX0 : 0 < X := by rw [hX]; nlinarith
  refine ⟨R, hR0, ?_⟩
  refine cyc_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k17gcHexC m γ4)
    (k17gcHexC_inj hm0 hm1 hγ4) ?_ [((1 : ℝ), β1 * m, (0 : ℝ))] ?_ (u1 := 0) (u2 := -X) (t1 := ⟪P, Q⟫) (t2 := 0)
    (by nlinarith) (lo := 0) (hi := 1) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ v2 < (γ4 - 1) * v1 ∧ 0 < v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) ?_ ?_ ?_
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k17gcHexC, pc6_0, eA]; simp [V8]
    · simp only [k17gcHexC, pc6_1, eB']; simp [V8]
    · simp only [k17gcHexC, pc6_2, eC]; simp [V8]
    · simp only [k17gcHexC, pc6_3, eA']; simp [V8]
    · simp only [k17gcHexC, pc6_4, eB]; simp [V8]
    · simp only [k17gcHexC, pc6_5, eO]; simp [V8]
  · intro y hy
    have hV : y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, γ4, γ4) ∨ y = fpoint P Q R d (0, 1, 1) ∨
        y = fpoint P Q R d (0, 1, 1 - m) ∨ y = fpoint P Q R d (0, m, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
        y = fpoint P Q R d (1, β1 * m, 0) := by
      rw [eO, eA, eB', eC, eA', eC', eB]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨5, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    have hb : 0 < (γ4 + 1) - (γ4 - 1) * lam := by nlinarith
    refine ⟨by nlinarith, ?_, ?_⟩
    · have : -X - (γ4 - 1) * (0 + lam * ⟪P, Q⟫) = -⟪P, P⟫ + ⟪P, Q⟫ * ((γ4 + 1) - (γ4 - 1) * lam) := by
        rw [hX]; ring
      nlinarith [mul_pos (neg_pos.2 hPQ) hb]
    · have : (0 + lam * ⟪P, Q⟫) * ⟪P, P⟫ + (-X + lam * 0) * ⟪P, Q⟫ =
          (-⟪P, Q⟫) * ((1 - lam) * ⟪P, P⟫ - (γ4 + 1) * ⟪P, Q⟫) := by rw [hX]; ring
      rw [this]
      exact mul_pos (neg_pos.2 hPQ) (by nlinarith [mul_pos (sub_pos.2 h1) hPP])
  · rintro v1 v2 ⟨hv1, hv2, -⟩
    exact k17gc_hexC_tsc hm0 hm1 hγ4 he heg hv1 hv2
  · rintro v1 v2 ⟨-, -, hf⟩ hinj
    refine lexUni6_two _ _ hinj ?_ ?_ ?_ (Or.inl ?_)
    · left; simp only [k17gcHexC, pc6_0, pc6_1, hz, hPR]; nlinarith
    · left; simp only [k17gcHexC, pc6_2, pc6_3, hz, hPR]; nlinarith
    · right
      simp only [k17gcHexC, pc6_0, pc6_5]
      refine ⟨by rw [hz, hz, hPR]; simp only; ring, ?_⟩
      rw [k17f_wexp, k17f_wexp]; simp only; nlinarith
    · left; simp only [k17gcHexC, pc6_3, pc6_4, hz, hPR]; nlinarith [mul_pos hm0 hw0]

set_option maxHeartbeats 3200000 in
/-- **S1.6** (`K6t3LeftPc`): a cell, or the literal's tie `⟪a-d,a-c'⟫ = 0`, or (S1.6a) `w = ⟪c-d,c-a'⟫ = 0`
(view `c - a'` normal to `Q_ac`), or (S1.6b) the double tie `⟪c-b',d-b⟫ = ⟪c-b',c-d⟫ = 0`. -/
theorem k17gc_s16 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftPc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, a - c'⟫ = 0 ∨
      (0 < ⟪a - d, a - c'⟫ ∧ ⟪c - d, c - a'⟫ = 0) ∨
      (⟪a - d, a - c'⟫ < 0 ∧ ⟪c - b', d - b⟫ = 0 ∧ ⟪c - b', c - d⟫ = 0) := by
  obtain ⟨hPc, hu, hw⟩ := h
  obtain ⟨β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, hfacet⟩ := k17gc_pc_frame W hPc
  have e : ⟪a - d, a - c'⟫ = -β1 * ⟪a - d, b - d⟫ := by
    have : a - c' = (-β1) • (b - d) := by rw [hc']; module
    rw [this, real_inner_smul_right]
  rcases lt_trichotomy ⟪a - d, b - d⟫ 0 with hn | h0 | hp
  · rcases hw.lt_or_eq with hw' | hw'
    · exact Or.inl (k17gc_s16a_cell hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hfacet hu hw' hn)
    · right; right; left; refine ⟨by rw [e]; nlinarith, hw'.symm⟩
  · right; left; rw [e, h0, mul_zero]
  · rcases k17gc_s16b_cells hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hp with hc | hl
    · exact Or.inl hc
    · right; right; right; exact ⟨by rw [e]; nlinarith, hl⟩

end C2
end Type08Sp
end Minimality
