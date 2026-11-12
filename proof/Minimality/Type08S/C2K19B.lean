module

public import Minimality.Type08S.C2K19A

@[expose] public section


/-!
# K19 / B: the all-orthogonal corner `pq = qr = pr = 0` with `α4 = 1`, `γ4 = β1` (U1 at `α4 = 1`, L10e; and U3's
K19A leftover, which is the same configuration with `β1 > 1`)

`p, q, r = a-d, b-d, c-d` pairwise orthogonal: at the view `d - b` the face `a,d,c,b'` is a 4-plateau and the tilt
functional restricted to it is diagonal (`w = v_a |p|² t_a + v_c |r|² t_c`), so the two cells below are w-sign
conditions only.  Split by `β1 ⋛ 1` (the affine parameter of `c'`):
* `β1 > 1`: the U2b pentagon `(b,c',b',c,d)` (frame `(a-d, c-d, d-b)`), cone `v1 > 0 > v2` and
  `w(b') < w(c)` (`v1 |p|² + (β1-1) v2 |r|² < 0`); single peak `d`.
* `β1 < 1`: hexagon `(b,a',c,b',a,c')` (frame `(c-d, a-d, d-b)`; screen `a = c'`, `b = d`), cone `v1, v2 < 0` and
  `w(b') > w(c)` (`(β1-1) v1 |r|² + v2 |p|² > 0`); single peak `a`.
* `β1 = 1`: leftover.
Numerics (gsec, K17F pa1eq data, ties `ζ(a,c) = ζ(a,d) = pr = 0`): `β1 > 1` ⟹ U1b 802/802, `β1 < 1` ⟹ hexagon 398/398.
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

/-- **Lex unimodality from one peak**: `i0` is a lex peak and every other index has a lex-higher neighbour. -/
theorem k19_lexUni_nb {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (i0 : ZMod k) (h1 : LexLt (z (i0 - 1), w (i0 - 1)) (z i0, w i0))
    (h2 : LexLt (z (i0 + 1), w (i0 + 1)) (z i0, w i0))
    (hnb : ∀ i, i ≠ i0 → LexLt (z i, w i) (z (i - 1), w (i - 1)) ∨ LexLt (z i, w i) (z (i + 1), w (i + 1))) :
    LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_eq_one]
  refine ⟨i0, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, hb⟩
    by_contra hne
    rcases hnb i hne with h | h
    · exact lexLt_asymm h ha
    · exact lexLt_asymm h hb
  · rintro rfl; exact ⟨h1, h2⟩

theorem k19_cone3 {x y u : ℝ × ℝ} {v1 v2 : ℝ} (h : k18Cone [x, y, u] v1 v2) :
    0 < x.1 * v1 + x.2 * v2 ∧ 0 < y.1 * v1 + y.2 * v2 ∧ 0 < u.1 * v1 + u.2 * v2 :=
  ⟨h x (by simp), h y (by simp), h u (by simp)⟩

theorem k19_z5 : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧ (3 : ZMod 5) - 1 = 2 ∧
    (4 : ZMod 5) - 1 = 3 ∧ (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧
    (3 : ZMod 5) + 1 = 4 ∧ (4 : ZMod 5) + 1 = 0 := by decide

theorem k19_z6 : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧ (3 : ZMod 6) - 1 = 2 ∧
    (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 ∧ (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧
    (2 : ZMod 6) + 1 = 3 ∧ (3 : ZMod 6) + 1 = 4 ∧ (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide

set_option maxHeartbeats 12800000 in
/-- **β1 > 1**: the U2b pentagon `(b,c',b',c,d)` at `d - b`, peak `d`. -/
theorem k19_orth_u1b_cell {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := c - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by
      simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h]
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17gc_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gc_fp]; module
  have Eb : fpoint P Q R d (0, 0, -1) = b := by rw [k17gc_fp, hR]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17gc_fp, hQ]; module
  have Ea' : fpoint P Q R d (0, γ6, -β6) = a' := by rw [k17gc_fp, ha', hQ, hR]; module
  have Eb' : fpoint P Q R d (1, β1, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (1, 0, -β1) = c' := by rw [k17gc_fp, hc', hP, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm, hqr, neg_zero]
  have hPQ : ⟪P, Q⟫ = 0 := hpr
  have hγ4 : (0 : ℝ) < β1 := by linarith
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gcPentU2 1 β1 β1)
    (k17gcPentU2_inj one_pos hγ4 hγ4) ?_ [(1, 0), (0, -1), (-⟪P, P⟫, -((β1 - 1) * ⟪Q, Q⟫))] (by simp)
    ?_ ?_ ?_ (ρ1 := 0) (ρ2 := -1) (δ1 := 1) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gcPentU2, pc5_0, Eb]; simp [V8]
    · simp only [k17gcPentU2, pc5_1, Ec']; simp [V8]
    · simp only [k17gcPentU2, pc5_2, Eb']; simp [V8]
    · simp only [k17gcPentU2, pc5_3, Ec]; simp [V8]
    · simp only [k17gcPentU2, pc5_4, Ed]; simp [V8]
  · intro v1 v2 hC D hD i j hi hj
    obtain ⟨h1, h2, -⟩ := k19_cone3 hC
    simp only at h1 h2
    exact tsc_scale hD ((k17gc_pentU2_tsc one_pos le_rfl hγ4 hγ4 (by linarith) hβ6 hγ6 hγ61 (by linarith)
      (by linarith) (by nlinarith)).1 i j hi hj)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (1, β1, 0) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (0, γ6, -β6) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gcPentU2, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gcPentU2, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gcPentU2, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gcPentU2, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gcPentU2, pc5_4])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, -⟩ := k19_cone3 hC
      simp only at h1 h2
      exact tsc_scale hD ((k17gc_pentU2_tsc one_pos le_rfl hγ4 hγ4 (by linarith) hβ6 hγ6 hγ61 (by linarith)
        (by linarith) (by nlinarith)).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, -⟩ := k19_cone3 hC
      simp only at h1 h2
      exact tsc_scale hD ((k17gc_pentU2_tsc one_pos le_rfl hγ4 hγ4 (by linarith) hβ6 hγ6 hγ61 (by linarith)
        (by linarith) (by nlinarith)).2 _ (by simp) i)
  · intro v1 v2 hC hw
    obtain ⟨h1, h2, h3⟩ := k19_cone3 hC
    simp only at h1 h2 h3
    obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    refine k19_lexUni_nb _ _ hw 4 ?_ ?_ ?_
    · rw [e4]; right
      refine ⟨by simp only [k17gcPentU2, pc5_3, pc5_4, hz, hPR, hQR]; ring, ?_⟩
      simp only [k17gcPentU2, pc5_3, pc5_4, hwx, hPQ, hPR, hQR]; nlinarith
    · rw [f4]; left; simp only [k17gcPentU2, pc5_0, pc5_4, hz, hPR, hQR]; nlinarith
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; rw [e0]; left; simp only [k17gcPentU2, pc5_0, pc5_4, hz, hPR, hQR]; nlinarith
      · right; rw [f1]; left; simp only [k17gcPentU2, pc5_1, pc5_2, hz, hPR, hQR]
        nlinarith [mul_pos (by linarith : (0:ℝ) < β1) hRR]
      · right; rw [f2]; right
        refine ⟨by simp only [k17gcPentU2, pc5_2, pc5_3, hz, hPR, hQR]; ring, ?_⟩
        simp only [k17gcPentU2, pc5_2, pc5_3, hwx, hPQ, hPR, hQR]; nlinarith
      · right; rw [f3]; right
        refine ⟨by simp only [k17gcPentU2, pc5_3, pc5_4, hz, hPR, hQR]; ring, ?_⟩
        simp only [k17gcPentU2, pc5_3, pc5_4, hwx, hPQ, hPR, hQR]; nlinarith
      · exact absurd rfl hi
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · right; norm_num
    · left; norm_num
    · left; simp only; nlinarith [mul_pos (sub_pos.2 hβ1) hQQ]

/-- Hexagon `(b,a',c,b',a,c')` in the frame `(c-d, a-d, d-b)`. -/
def k19HexX (β1 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 0, -1) (γ6, 0, -β6) (1, 0, 0) (β1, 1, 0) (0, 1, 0) (0, 1, -β1)

set_option maxHeartbeats 3200000 in
theorem k19_hexX_tsc {D β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k19HexX β1 β6 γ6 (i + 1) - k19HexX β1 β6 γ6 i) (k19HexX β1 β6 γ6 j - k19HexX β1 β6 γ6 i)
        (v1, v2, 0)) ∧
    (∀ i : ZMod 6, TSc D (k19HexX β1 β6 γ6 (i + 1) - k19HexX β1 β6 γ6 i) ((0, 0, 0) - k19HexX β1 β6 γ6 i)
      (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have n1 : 0 < -v1 := by linarith
  have n2 : 0 < -v2 := by linarith
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kb := mul_pos hD hβ6
  have kb1 := mul_pos hD hβ1
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD n1
  have kv2 := mul_pos hD n2
  have kgv2 := mul_pos (mul_pos hD hγ6) n2
  have kbv2 := mul_pos (mul_pos hD hβ6) n2
  have ksv2 := mul_pos (mul_pos hD (sub_pos.2 hs)) n2
  have kb1v1 := mul_pos (mul_pos hD hβ1) n1
  have kb1v2 := mul_pos (mul_pos hD hβ1) n2
  have kbbv2 := mul_pos (mul_pos (mul_pos hD hβ1) hβ1) n2
  have kbgv2 := mul_pos (mul_pos (mul_pos hD hβ1) hγ6) n2
  constructor
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k19HexX, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k19HexX, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k19HexX_inj {β1 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) :
    ∀ i j, k19HexX β1 β6 γ6 i = k19HexX β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k19HexX, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
/-- **β1 < 1**: the hexagon `(b,a',c,b',a,c')` at `d - b`, peak `a`. -/
theorem k19_orth_x1p_cell {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hβ11 : β1 < 1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
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
  have Eb' : fpoint P Q R d (β1, 1, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (0, 1, -β1) = c' := by rw [k17gc_fp, hc', hQ, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm, hqr, neg_zero]
  have hPQ : ⟪P, Q⟫ = 0 := by rw [hP, hQ, real_inner_comm]; exact hpr
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k19HexX β1 β6 γ6)
    (k19HexX_inj hβ1 hβ6 hγ6 hγ61) ?_ [(-1, 0), (0, -1), ((β1 - 1) * ⟪P, P⟫, ⟪Q, Q⟫)] (by simp)
    ?_ ?_ ?_ (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := -1) ?_
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k19HexX, pc6_0, Eb]; simp [V8]
    · simp only [k19HexX, pc6_1, Ea']; simp [V8]
    · simp only [k19HexX, pc6_2, Ec]; simp [V8]
    · simp only [k19HexX, pc6_3, Eb']; simp [V8]
    · simp only [k19HexX, pc6_4, Ea]; simp [V8]
    · simp only [k19HexX, pc6_5, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    obtain ⟨h1, h2, -⟩ := k19_cone3 hC
    simp only at h1 h2
    exact (k19_hexX_tsc hD hβ1 hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (γ6, 0, -β6) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (β1, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨
        y = fpoint P Q R d (0, 0, 0) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k19HexX, pc6_0])).elim
    · exact (hyx 1 (by simp only [k19HexX, pc6_1])).elim
    · exact (hyx 2 (by simp only [k19HexX, pc6_2])).elim
    · exact (hyx 3 (by simp only [k19HexX, pc6_3])).elim
    · exact (hyx 4 (by simp only [k19HexX, pc6_4])).elim
    · exact (hyx 5 (by simp only [k19HexX, pc6_5])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, -⟩ := k19_cone3 hC
      simp only at h1 h2
      exact (k19_hexX_tsc hD hβ1 hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).2 i
  · intro v1 v2 hC hw
    obtain ⟨h1, h2, h3⟩ := k19_cone3 hC
    simp only at h1 h2 h3
    have hv1 : v1 < 0 := by linarith
    obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := k19_z6
    refine k19_lexUni_nb _ _ hw 4 ?_ ?_ ?_
    · rw [e4]; right
      refine ⟨by simp only [k19HexX, pc6_3, pc6_4, hz, hPR, hQR]; ring, ?_⟩
      simp only [k19HexX, pc6_3, pc6_4, hwx, hPQ, hPR, hQR]; nlinarith [mul_pos hβ1 (mul_pos (neg_pos.2 hv1) hPP)]
    · rw [f4]; left; simp only [k19HexX, pc6_5, pc6_4, hz, hPR, hQR]; nlinarith [mul_pos hβ1 hRR]
    · intro i hi
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · left; rw [e0]; left; simp only [k19HexX, pc6_0, pc6_5, hz, hPR, hQR]
        nlinarith [mul_pos (sub_pos.2 hβ11) hRR]
      · right; rw [f1]; left; simp only [k19HexX, pc6_1, pc6_2, hz, hPR, hQR]; nlinarith [mul_pos hβ6 hRR]
      · right; rw [f2]; right
        refine ⟨by simp only [k19HexX, pc6_2, pc6_3, hz, hPR, hQR]; ring, ?_⟩
        simp only [k19HexX, pc6_2, pc6_3, hwx, hPQ, hPR, hQR]; nlinarith
      · right; rw [f3]; right
        refine ⟨by simp only [k19HexX, pc6_3, pc6_4, hz, hPR, hQR]; ring, ?_⟩
        simp only [k19HexX, pc6_3, pc6_4, hwx, hPQ, hPR, hQR]; nlinarith [mul_pos hβ1 (mul_pos (neg_pos.2 hv1) hPP)]
      · exact absurd rfl hi
      · left; rw [e5]; left; simp only [k19HexX, pc6_5, pc6_4, hz, hPR, hQR]; nlinarith [mul_pos hβ1 hRR]
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; norm_num
    · right; norm_num
    · left; simp only; nlinarith [mul_pos (sub_pos.2 hβ11) hPP]

/-- **U3 closed**: `k17gc_u3`'s leftover `⟪a-d,a-c'⟫ = 0` has a cell (K19A for `pr ≠ 0`, U2b pentagon for `pr = 0`). -/
theorem k19_u3_closed {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (h0 : ⟪b' - c, d - b⟫ = 0) (hZ : ⟪a - d, a - c'⟫ = 0) : HasLexCell (V8 a a' b b' c c' d) := by
  rcases k19_u3_tie W h hα hβ h0 hZ with hc | ⟨hpq, hqr, hpr⟩
  · exact hc
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨β1, β6, γ6, hdet, hc', hb', ha', hβ1, hβ6, hγ6, hγ61, hs, -⟩ :=
    k17gc_u3_frame W hT' hκ (k5z_far1 W hT' hnT) hα hβ h0
  exact k19_orth_u1b_cell hdet hc' hb' ha' hβ1 hβ6 hγ6 hγ61 hpq hqr hpr

/-- Frame of U1 at `α4 = 1`: `γ4 = β1`, `pq = qr = 0`. -/
theorem k19_u1e_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h1 : ⟪a - c, d - b⟫ = 0) (h2 : ⟪a - d, d - b⟫ = 0) (hα : det3 (b' - a) (b - d) (c - d) = 0) :
    ∃ β1 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + (1 : ℝ) • (a - d) + β1 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < β1 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 ∧
      ⟪a - d, b - d⟫ = 0 ∧ ⟪b - d, c - d⟫ = 0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, hαγ, hβ6, hγ6, hs, hfa⟩ :=
    norm08w_coordsTp W hT'
  rw [det_alpha4 hb'] at hα
  have ha1 : α4 = 1 := by
    rcases mul_eq_zero.1 hα with h | h
    · linarith
    · exact absurd h hdet
  subst ha1
  have hg4 : γ4 = β1 := by
    have := (planar_a_iff hdet hc' hb').1 hκ
    linarith
  subst hg4
  have e2 : d - b = -(b - d) := by abel
  have hpq : ⟪a - d, b - d⟫ = 0 := by
    rw [e2, inner_neg_right] at h2; linarith
  have hqr : ⟪b - d, c - d⟫ = 0 := by
    have e : a - c = (a - d) - (c - d) := by abel
    rw [e, e2, inner_neg_right, inner_sub_left, hpq, real_inner_comm] at h1; linarith
  exact ⟨γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hβ6, hγ6, hfa hfar, hs, hpq, hqr⟩

/-- **U1 tie at `α4 = 1`** (`k17gc_u1`'s leftover `⟪a-d,c-d⟫ = 0` with `det3 (b'-a) (b-d) (c-d) = 0`): a cell
unless `β1 = 1` (`det3 (a-d) (c'-b) (c-d) = 0`). -/
theorem k19_u1_eq {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (h1 : ⟪a - c, d - b⟫ = 0) (h2 : ⟪a - d, d - b⟫ = 0) (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hpr : ⟪a - d, c - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ det3 (a - d) (c' - b) (c - d) = 0 := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨β1, β6, γ6, hdet, hc', hb', ha', hβ1, hβ6, hγ6, hγ61, hs, hpq, hqr⟩ :=
    k19_u1e_frame W hT' hκ (k5z_far1 W hT' hnT) h1 h2 hα
  rcases lt_trichotomy β1 1 with hl | he | hg
  · exact Or.inl (k19_orth_x1p_cell hdet hc' hb' ha' hβ1 hl hβ6 hγ6 hγ61 hs hpq hqr hpr)
  · right; rw [det_beta1 hc', he, sub_self, zero_mul]
  · exact Or.inl (k19_orth_u1b_cell hdet hc' hb' ha' hg hβ6 hγ6 hγ61 hpq hqr hpr)

end C2
end Type08Sp
end Minimality
