module

public import Minimality.Type08S.C2K19B

@[expose] public section


/-!
# K19 / C: S1.6a's `w = 0` side (L9w): `K6t3LeftPc` with `⟪a-d,a-c'⟫ > 0` (`pq < 0`) and `w = ⟪c-d,c-a'⟫ = 0`

Pc frame (`α4 = β6 = 1`); `u = 0` and `w = 0` make the face `a,b',c,d` a plateau at the view `c - a'`
(`P = a-d`, `Q = (b-d)/m`, `R = (c-a')/m`, `m = 1-γ6`; `⟪P,R⟫ = 0`, `⟪Q,R⟫ = -⟪R,R⟫`).  Split literal
`L = ⟪b'-c,d-b⟫` (= `z(b') - z(c)` at the view `d - b`):
* `L > 0`: the S1.6a hexagon `(a,b',c,a',b,d)` at `c - a'` (`k17gc_hexC_tsc` cone `v1 < 0`, `v2 < (γ4-1) v1`) with
  `w(a) > w(d)` and `w(b') > w(c)`; the plateau path `d,a,b',c` then has its peak at `a` or `b'`.  Ray witness
  `ρ = (0,-1)`, `δ = (-1,0)`: the functional `w(b') - w(c)` is `L/m > 0` at `ρ` (`k18_cone_cell`).
* `L < 0`: the pentagon `(c,b',c',a,d)` at `d - b` (frame `(c-d,a-d,d-b)`, cone `v1, v2 > 0`), w-free: peak `a`
  (`z(a) > z(d) > z(c) > z(b')`, `z(c') < z(a)`).
* `L = 0`: leftover (numerics: S1.6a never, the pentagon 255/941, the rest at view `a - d`).
Numerics (gsec, K17F pcu0 data, ties u, w, literal > 0): `L > 0` ⟹ hexagon 755/755, `L < 0` ⟹ pentagon 1061/1061.
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

/-- **Two adjacent candidate peaks** `i0, i0+1`: both rise from outside, every other index has a higher neighbour. -/
theorem k19_lexUni_nb2 {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (i0 : ZMod k) (hne : i0 + 1 ≠ i0) (h1 : LexLt (z (i0 - 1), w (i0 - 1)) (z i0, w i0))
    (h2 : LexLt (z (i0 + 1 + 1), w (i0 + 1 + 1)) (z (i0 + 1), w (i0 + 1)))
    (hnb : ∀ i, i ≠ i0 → i ≠ i0 + 1 →
      LexLt (z i, w i) (z (i - 1), w (i - 1)) ∨ LexLt (z i, w i) (z (i + 1), w (i + 1))) :
    LexUni z w := by
  have hd : (z i0, w i0) ≠ (z (i0 + 1), w (i0 + 1)) := fun e =>
    hne (hinj _ _ (congrArg Prod.fst e).symm (congrArg Prod.snd e).symm)
  rcases lexLt_total hd with h | h
  · refine k19_lexUni_nb z w hinj (i0 + 1) (by rwa [add_sub_cancel_right]) h2 (fun i hi => ?_)
    by_cases h0 : i = i0
    · subst h0; right; exact h
    · exact hnb i h0 hi
  · refine k19_lexUni_nb z w hinj i0 h1 h (fun i hi => ?_)
    by_cases h0 : i = i0 + 1
    · subst h0; left; rwa [add_sub_cancel_right]
    · exact hnb i hi h0

theorem k19_ip3 (P Q R : ℝ³) (x y z μ : ℝ) :
    ⟪x • P + y • Q + z • R, μ • Q⟫ = μ * (x * ⟪P, Q⟫ + y * ⟪Q, Q⟫ + z * ⟪Q, R⟫) := by
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, real_inner_comm R Q]; ring

theorem k19_cone4' {x y u s : ℝ × ℝ} {v1 v2 : ℝ} (h : k18Cone [x, y, u, s] v1 v2) :
    0 < x.1 * v1 + x.2 * v2 ∧ 0 < y.1 * v1 + y.2 * v2 ∧ 0 < u.1 * v1 + u.2 * v2 ∧ 0 < s.1 * v1 + s.2 * v2 :=
  ⟨h x (by simp), h y (by simp), h u (by simp), h s (by simp)⟩

set_option maxHeartbeats 12800000 in
/-- `L > 0`: the S1.6a hexagon at `c - a'` on the plateau. -/
theorem k19_s16w_hex {a a' b b' c c' d : ℝ³} {β1 γ4 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hfacet : β1 * (1 - γ6) < γ4) (hu : ⟪c - a', a - d⟫ = 0) (hw : ⟪c - d, c - a'⟫ = 0)
    (hpq : ⟪a - d, b - d⟫ < 0) (hL : 0 < ⟪b' - c, d - b⟫) : HasLexCell (V8 a a' b b' c c' d) := by
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
  have hQR : ⟪Q, R⟫ = -⟪R, R⟫ := by
    have h1 : ⟪Q, R⟫ + ⟪R, R⟫ = (1 / m) * ⟪c - d, c - a'⟫ := by
      rw [← inner_add_left]
      have : Q + R = c - d := by
        rw [hQ, hR, hca']; match_scalars <;> field_simp <;> ring
      rw [this, hR, real_inner_smul_right]
    rw [hw, mul_zero] at h1; linarith
  have hPQ : ⟪P, Q⟫ < 0 := by
    rw [hP, hQ, real_inner_smul_right]; exact mul_neg_of_pos_of_neg hmpos hpq
  have hR0 : R ≠ 0 := by
    intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  -- the literal in the frame
  have hLf : ⟪b' - c, d - b⟫ = -m * (⟪P, Q⟫ + (γ4 - 1) * (⟪Q, Q⟫ + ⟪Q, R⟫)) := by
    have e1 : b' - c = (1 : ℝ) • P + (γ4 - 1) • Q + (γ4 - 1) • R := by rw [← eB', ← eC, hfp, hfp]; module
    have e2 : d - b = (-m) • Q := by rw [← eB, hfp]; module
    rw [e1, e2, k19_ip3]
    ring
  have hLQ : 0 < -(⟪P, Q⟫ + (γ4 - 1) * (⟪Q, Q⟫ + ⟪Q, R⟫)) := by
    rw [hLf] at hL; nlinarith
  have he : 0 < β1 * m := mul_pos hβ1 hm0
  have heg : β1 * m < γ4 := by rw [hm]; exact hfacet
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k17gcHexC m γ4)
    (k17gcHexC_inj hm0 hm1 hγ4) ?_
    [(⟪P, P⟫ + (γ4 - 1) * ⟪P, Q⟫, ⟪P, Q⟫ + (γ4 - 1) * (⟪Q, Q⟫ + ⟪Q, R⟫)), (-1, 0), (γ4 - 1, -1),
      (⟪P, P⟫, ⟪P, Q⟫)] (by simp) ?_ ?_ ?_ (ρ1 := 0) (ρ2 := -1) (δ1 := -1) (δ2 := 0) ?_
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k17gcHexC, pc6_0, eA]; simp [V8]
    · simp only [k17gcHexC, pc6_1, eB']; simp [V8]
    · simp only [k17gcHexC, pc6_2, eC]; simp [V8]
    · simp only [k17gcHexC, pc6_3, eA']; simp [V8]
    · simp only [k17gcHexC, pc6_4, eB]; simp [V8]
    · simp only [k17gcHexC, pc6_5, eO]; simp [V8]
  · intro v1 v2 hC D hD i j hi hj
    obtain ⟨-, h1, h2, -⟩ := k19_cone4' hC
    simp only at h1 h2
    exact tsc_scale hD ((k17gc_hexC_tsc hm0 hm1 hγ4 he heg (by linarith) (by linarith)).1 i j hi hj)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, γ4, γ4) ∨ y = fpoint P Q R d (0, 1, 1) ∨
        y = fpoint P Q R d (0, 1, 1 - m) ∨ y = fpoint P Q R d (0, m, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
        y = fpoint P Q R d (1, β1 * m, 0) := by
      rw [eO, eA, eB', eC, eA', eC', eB]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gcHexC, pc6_0])).elim
    · exact (hyx 1 (by simp only [k17gcHexC, pc6_1])).elim
    · exact (hyx 2 (by simp only [k17gcHexC, pc6_2])).elim
    · exact (hyx 3 (by simp only [k17gcHexC, pc6_3])).elim
    · exact (hyx 4 (by simp only [k17gcHexC, pc6_4])).elim
    · exact (hyx 5 (by simp only [k17gcHexC, pc6_5])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨-, h1, h2, -⟩ := k19_cone4' hC
      simp only at h1 h2
      exact tsc_scale hD ((k17gc_hexC_tsc hm0 hm1 hγ4 he heg (by linarith) (by linarith)).2 _ (by simp) i)
  · intro v1 v2 hC hinj
    obtain ⟨hmf, h1, h2, hg⟩ := k19_cone4' hC
    simp only at hmf h1 h2 hg
    obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := k19_z6
    refine k19_lexUni_nb2 _ _ hinj 0 (by decide) ?_ ?_ ?_
    · rw [e0]; right
      refine ⟨by simp only [k17gcHexC, pc6_0, pc6_5, hz, hPR]; ring, ?_⟩
      simp only [k17gcHexC, pc6_0, pc6_5, hwx, hPR]; nlinarith
    · rw [f0, f1]; right
      refine ⟨by simp only [k17gcHexC, pc6_1, pc6_2, hz, hPR, hQR]; ring, ?_⟩
      simp only [k17gcHexC, pc6_1, pc6_2, hwx, hPR]; nlinarith
    · intro i hi hi'
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · exact absurd rfl hi'
      · left; rw [e2]; right
        refine ⟨by simp only [k17gcHexC, pc6_1, pc6_2, hz, hPR, hQR]; ring, ?_⟩
        simp only [k17gcHexC, pc6_1, pc6_2, hwx, hPR]; nlinarith
      · left; rw [e3]; left; simp only [k17gcHexC, pc6_2, pc6_3, hz, hPR, hQR]; nlinarith [mul_pos hm0 hRR]
      · right; rw [f4]; left; simp only [k17gcHexC, pc6_4, pc6_5, hz, hPR, hQR]; nlinarith [mul_pos hm0 hRR]
      · right; rw [f5]; right
        refine ⟨by simp only [k17gcHexC, pc6_0, pc6_5, hz, hPR]; ring, ?_⟩
        simp only [k17gcHexC, pc6_0, pc6_5, hwx, hPR]; nlinarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · left; simp only; linarith
    · right; norm_num
    · left; norm_num
    · left; simp only; linarith

set_option maxHeartbeats 12800000 in
/-- `L < 0`: the pentagon `(c,b',c',a,d)` at `d - b`, w-free, peak `a`. -/
theorem k19_s16w_pent {a a' b b' c c' d : ℝ³} {β1 γ4 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hw : ⟪c - d, c - a'⟫ = 0) (hpq : ⟪a - d, b - d⟫ < 0) (hL : ⟪b' - c, d - b⟫ < 0) :
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
  have Ea' : fpoint P Q R d (γ6, 0, -1) = a' := by rw [k17gc_fp, ha', hP, hR]; module
  have Eb' : fpoint P Q R d (γ4, 1, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (0, 1, -β1) = c' := by rw [k17gc_fp, hc', hQ, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hQR : 0 < ⟪Q, R⟫ := by
    have : ⟪Q, R⟫ = -⟪a - d, b - d⟫ := by
      rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right]
    rw [this]; linarith
  have hPR : ⟪P, R⟫ < 0 := by
    have e1 : c - a' = (1 - γ6) • P - (b - d) := by rw [ha', hP]; module
    rw [e1, inner_sub_right, real_inner_smul_right] at hw
    have : ⟪P, R⟫ = -⟪P, b - d⟫ := by
      rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right]
    rw [this]; nlinarith [mul_pos (sub_pos.2 hγ61) hPP]
  have hLf : ⟪b' - c, d - b⟫ = (γ4 - 1) * ⟪P, R⟫ + ⟪Q, R⟫ := by
    have e1 : b' - c = (γ4 - 1) • P + Q := by rw [hb', hP, hQ]; module
    rw [e1, inner_add_left, real_inner_smul_left]
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gcPent6 β1 γ4)
    (k17gcPent6_inj hβ1 hγ4) ?_ [(1, 0), (0, 1)] (by simp) ?_ ?_ ?_ (ρ1 := 1) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gcPent6, pc5_0, Ec]; simp [V8]
    · simp only [k17gcPent6, pc5_1, Eb']; simp [V8]
    · simp only [k17gcPent6, pc5_2, Ec']; simp [V8]
    · simp only [k17gcPent6, pc5_3, Ea]; simp [V8]
    · simp only [k17gcPent6, pc5_4, Ed]; simp [V8]
  · intro v1 v2 hC D hD i j hi hj
    have h1 := hC (1, 0) (by simp)
    have h2 := hC (0, 1) (by simp)
    simp only at h1 h2
    exact tsc_scale hD ((k17gc_pent6_tsc hβ1 hγ4 hγ6 hγ61 (by linarith) (by linarith)).1 i j hi hj)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
        y = fpoint P Q R d (γ6, 0, -1) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gcPent6, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gcPent6, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gcPent6, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gcPent6, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gcPent6, pc5_4])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact tsc_scale hD ((k17gc_pent6_tsc hβ1 hγ4 hγ6 hγ61 (by linarith) (by linarith)).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact tsc_scale hD ((k17gc_pent6_tsc hβ1 hγ4 hγ6 hγ61 (by linarith) (by linarith)).2 _ (by simp) i)
  · intro v1 v2 hC hinj
    rw [hLf] at hL
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    refine k19_lexUni_nb _ _ hinj 3 ?_ ?_ ?_
    · rw [e3]; left; simp only [k17gcPent6, pc5_2, pc5_3, hz]; nlinarith [mul_pos hβ1 hRR]
    · rw [f3]; left; simp only [k17gcPent6, pc5_3, pc5_4, hz]; nlinarith
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; rw [e0]; left; simp only [k17gcPent6, pc5_0, pc5_4, hz]; nlinarith
      · left; rw [e1]; left; simp only [k17gcPent6, pc5_0, pc5_1, hz]; nlinarith
      · right; rw [f2]; left; simp only [k17gcPent6, pc5_2, pc5_3, hz]; nlinarith [mul_pos hβ1 hRR]
      · exact absurd rfl hi
      · left; rw [e4]; left; simp only [k17gcPent6, pc5_3, pc5_4, hz]; nlinarith
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> (left; norm_num)

/-- **S1.6a, `w = 0` side** (`k17gc_s16`'s third leftover): a cell unless `⟪b'-c,d-b⟫ = 0`. -/
theorem k19_s16w {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftPc a a' b b' c c' d)
    (hlit : 0 < ⟪a - d, a - c'⟫) (hw : ⟪c - d, c - a'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪b' - c, d - b⟫ = 0 := by
  obtain ⟨hPc, hu, -⟩ := h
  obtain ⟨β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, hfacet⟩ := k17gc_pc_frame W hPc
  have e : ⟪a - d, a - c'⟫ = -β1 * ⟪a - d, b - d⟫ := by
    have : a - c' = (-β1) • (b - d) := by rw [hc']; module
    rw [this, real_inner_smul_right]
  have hpq : ⟪a - d, b - d⟫ < 0 := by
    rw [e] at hlit; nlinarith
  rcases lt_trichotomy ⟪b' - c, d - b⟫ 0 with hn | h0 | hp
  · exact Or.inl (k19_s16w_pent hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hw hpq hn)
  · exact Or.inr h0
  · exact Or.inl (k19_s16w_hex hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hfacet hu hw hpq hp)

end C2
end Type08Sp
end Minimality
