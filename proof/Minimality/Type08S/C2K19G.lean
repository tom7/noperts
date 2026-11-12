module

public import Minimality.Type08S.C2K19F

@[expose] public section


/-!
# K19 / G: U1 at `pr = 0` with `α4 < 1` (L10l): `p, q, r` pairwise orthogonal, `γ4 = 1 - α4 + α4 β1`

* `β1 < 1`: hexagon `(b,a',c,b',a,c')` at `d - b` (`k19HexZ`, frame `(c-d, a-d, d-b)`, cone `v1, v2 < 0`) with
  `w(b') > w(a)` (`γ4 v1 |r|² - (1-α4) v2 |p|² > 0`, ray `(0,-1)`); `b < c'` in depth since `β1 < 1`.
* `β1 > 1`: the view `a - d` is face-on to `(d,b,a',c)`; screen `(q, r)`: `a = d = 0`, `c' = (β1,0)`, `b' = (0,γ4)`,
  `b`, `c` on the edges `a c'`, `b' a` (tilt), `a' = (β6,γ6)`.  Triangle `(a,c',b')` if `a'` is strictly inside
  (`β1γ4 - β1γ6 - β6γ4 > 0`), quadrilateral `(a,c',a',b')` if strictly outside; both cones `v1, v2 > 0`, single peak `c'`
  (`w(c') - w(a) = β1 v1 |q|² > 0`).  All affine: no Gram literal.
* Leftovers: `β1 = 1` (`det3 (a-d)(c'-b)(c-d) = 0`) and `a'` on the screen line `c'b'` (`det3 (c'-a')(b'-a')(a-d) = 0`).
Numerics (gsec, K17F pa1lt data, ties ζ(a,c) = ζ(a,d) = pr = 0): β1 < 1 ⟹ hexagon 254/254; β1 > 1 ⟹ triangle 668 +
quadrilateral 278 = 946/946 (disjoint).
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

/-! ## β1 < 1: hexagon at `d - b` -/

/-- Hexagon `(b,a',c,b',a,c')` in the frame `(c-d, a-d, d-b)`, `b' = (γ4,α4,0)`. -/
def k19HexZ (α4 β1 γ4 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 0, -1) (γ6, 0, -β6) (1, 0, 0) (γ4, α4, 0) (0, 1, 0) (0, 1, -β1)

set_option maxHeartbeats 6400000 in
theorem k19_hexZ_tsc {D α4 β1 γ4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hα41 : α4 ≤ 1) (hβ1 : 0 < β1)
    (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hγg : (1 - α4) * γ6 < γ4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k19HexZ α4 β1 γ4 β6 γ6 (i + 1) - k19HexZ α4 β1 γ4 β6 γ6 i)
        (k19HexZ α4 β1 γ4 β6 γ6 j - k19HexZ α4 β1 γ4 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 6, TSc D (k19HexZ α4 β1 γ4 β6 γ6 (i + 1) - k19HexZ α4 β1 γ4 β6 γ6 i)
      ((0, 0, 0) - k19HexZ α4 β1 γ4 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have n1 : 0 < -v1 := by linarith
  have n2 : 0 < -v2 := by linarith
  have ka := sub_nonneg.2 hα41
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kb := mul_pos hD hβ6
  have kb1 := mul_pos hD hβ1
  have kg4 := mul_pos hD hγ4
  have ka4 := mul_pos hD hα4
  have kag := mul_pos hD (sub_pos.2 hαγ)
  have kgg := mul_pos hD (sub_pos.2 hγg)
  have kag6 := mul_pos (mul_pos hD hα4) hγ6
  have kag61 := mul_pos (mul_pos hD hα4) (sub_pos.2 hγ61)
  have kbg4 := mul_pos (mul_pos hD hβ1) hγ4
  have kba4 := mul_pos (mul_pos hD hβ1) hα4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD n1
  have kv2 := mul_pos hD n2
  have kgv2 := mul_pos (mul_pos hD hγ6) n2
  have kbv2 := mul_pos (mul_pos hD hβ6) n2
  have ksv2 := mul_pos (mul_pos hD (sub_pos.2 hs)) n2
  have kb1v1 := mul_pos (mul_pos hD hβ1) n1
  have kb1v2 := mul_pos (mul_pos hD hβ1) n2
  have kbg4v2 := mul_pos (mul_pos (mul_pos hD hβ1) hγ4) n2
  have kbgv2 := mul_pos (mul_pos (mul_pos hD hβ1) hγ6) n2
  have kbav1 := mul_nonneg (mul_nonneg (mul_pos hD hβ1).le ka) n1.le
  constructor
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k19HexZ, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k19HexZ, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k19HexZ_inj {α4 β1 γ4 β6 γ6 : ℝ} (hα4 : 0 < α4) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) : ∀ i j, k19HexZ α4 β1 γ4 β6 γ6 i = k19HexZ α4 β1 γ4 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k19HexZ, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
/-- `β1 < 1`: the hexagon `(b,a',c,b',a,c')` at `d - b`. -/
theorem k19_u1l_hex {a a' b b' c c' d : ℝ³} {α4 β1 γ4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ1 : 0 < β1) (hβ11 : β1 < 1)
    (hγ : γ4 = 1 - α4 + α4 * β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hγ4 : 0 < γ4 := by rw [hγ]; nlinarith [mul_pos hα4 hβ1]
  have hαγ : 1 < α4 + γ4 := by rw [hγ]; nlinarith [mul_pos hα4 hβ1]
  have hγg : (1 - α4) * γ6 < γ4 := by rw [hγ]; nlinarith [mul_pos hα4 hβ1, mul_pos (sub_pos.2 hα41) (sub_pos.2 hγ61)]
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
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm, hqr, neg_zero]
  have hPQ : ⟪P, Q⟫ = 0 := by rw [hP, hQ, real_inner_comm]; exact hpr
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k19HexZ α4 β1 γ4 β6 γ6)
    (k19HexZ_inj hα4 hβ1 hγ4 hβ6 hγ6 hγ61) ?_ [(-1, 0), (0, -1), (γ4 * ⟪P, P⟫, (α4 - 1) * ⟪Q, Q⟫)] (by simp)
    ?_ ?_ ?_ (ρ1 := 0) (ρ2 := -1) (δ1 := -1) (δ2 := 0) ?_
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [k19HexZ, pc6_0, Eb]; simp [V8]
    · simp only [k19HexZ, pc6_1, Ea']; simp [V8]
    · simp only [k19HexZ, pc6_2, Ec]; simp [V8]
    · simp only [k19HexZ, pc6_3, Eb']; simp [V8]
    · simp only [k19HexZ, pc6_4, Ea]; simp [V8]
    · simp only [k19HexZ, pc6_5, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    obtain ⟨h1, h2, -⟩ := k19_cone3 hC
    simp only at h1 h2
    exact (k19_hexZ_tsc hD hα4 hα41.le hβ1 hγ4 hαγ hγg hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (γ6, 0, -β6) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (γ4, α4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨
        y = fpoint P Q R d (0, 0, 0) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k19HexZ, pc6_0])).elim
    · exact (hyx 1 (by simp only [k19HexZ, pc6_1])).elim
    · exact (hyx 2 (by simp only [k19HexZ, pc6_2])).elim
    · exact (hyx 3 (by simp only [k19HexZ, pc6_3])).elim
    · exact (hyx 4 (by simp only [k19HexZ, pc6_4])).elim
    · exact (hyx 5 (by simp only [k19HexZ, pc6_5])).elim
    · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
      obtain ⟨h1, h2, -⟩ := k19_cone3 hC
      simp only at h1 h2
      exact (k19_hexZ_tsc hD hα4 hα41.le hβ1 hγ4 hαγ hγg hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).2 i
  · intro v1 v2 hC hw
    obtain ⟨h1, h2, h3⟩ := k19_cone3 hC
    simp only at h1 h2 h3
    obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := k19_z6
    have hab' : LexLt (⟪fpoint P Q R d (k19HexZ α4 β1 γ4 β6 γ6 4), R⟫,
        ⟪fpoint P Q R d (k19HexZ α4 β1 γ4 β6 γ6 4), fcomb P Q R v1 v2 0⟫)
        (⟪fpoint P Q R d (k19HexZ α4 β1 γ4 β6 γ6 3), R⟫,
        ⟪fpoint P Q R d (k19HexZ α4 β1 γ4 β6 γ6 3), fcomb P Q R v1 v2 0⟫) := by
      right
      refine ⟨by simp only [k19HexZ, pc6_3, pc6_4, hz, hPR, hQR]; ring, ?_⟩
      simp only [k19HexZ, pc6_3, pc6_4, hwx, hPQ, hPR, hQR]; nlinarith
    refine k19_lexUni_nb2 _ _ hw 2 (by decide) ?_ ?_ ?_
    · rw [e2]; left; simp only [k19HexZ, pc6_1, pc6_2, hz, hPR, hQR]; nlinarith [mul_pos hβ6 hRR]
    · rw [f2, f3]; exact hab'
    · intro i hi hi'
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · left; rw [e0]; left; simp only [k19HexZ, pc6_0, pc6_5, hz, hPR, hQR]
        nlinarith [mul_pos (sub_pos.2 hβ11) hRR]
      · right; rw [f1]; left; simp only [k19HexZ, pc6_1, pc6_2, hz, hPR, hQR]; nlinarith [mul_pos hβ6 hRR]
      · exact absurd rfl hi
      · exact absurd rfl hi'
      · left; rw [e4]; exact hab'
      · left; rw [e5]; left; simp only [k19HexZ, pc6_4, pc6_5, hz, hPR, hQR]; nlinarith [mul_pos hβ1 hRR]
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · right; norm_num
    · left; norm_num
    · left; simp only; nlinarith [mul_pos (sub_pos.2 hα41) hQQ]

/-! ## β1 > 1: triangle / quadrilateral at `a - d` (frame `(b-d, c-d, a-d)`) -/

/-- Triangle `a (0,0,1), c' (β1,0,1), b' (0,γ4,α4)`. -/
def k19Tri (α4 β1 γ4 : ℝ) : ZMod 3 → ℝ × ℝ × ℝ := ![(0, 0, 1), (β1, 0, 1), (0, γ4, α4)]

theorem k19Tri_0 : k19Tri α4 β1 γ4 0 = (0, 0, 1) := rfl
theorem k19Tri_1 : k19Tri α4 β1 γ4 1 = (β1, 0, 1) := rfl
theorem k19Tri_2 : k19Tri α4 β1 γ4 2 = (0, γ4, α4) := rfl

theorem k19_z3 : (0 : ZMod 3) + 1 = 1 ∧ (1 : ZMod 3) + 1 = 2 ∧ (2 : ZMod 3) + 1 = 0 ∧
    (0 : ZMod 3) - 1 = 2 ∧ (1 : ZMod 3) - 1 = 0 ∧ (2 : ZMod 3) - 1 = 1 := by decide

theorem k19_z3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

theorem k19_z4 : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧ (3 : ZMod 4) + 1 = 0 ∧
    (0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧ (3 : ZMod 4) - 1 = 2 := by decide

theorem k19_z4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

set_option maxHeartbeats 3200000 in
theorem k19_tri_tsc {D α4 β1 γ4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hβ1 : 1 < β1) (hγ4 : 1 < γ4)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hin : 0 < β1 * γ4 - β1 * γ6 - β6 * γ4) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      TSc D (k19Tri α4 β1 γ4 (i + 1) - k19Tri α4 β1 γ4 i) (k19Tri α4 β1 γ4 j - k19Tri α4 β1 γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0), (β6, γ6, 0)], ∀ i : ZMod 3,
      TSc D (k19Tri α4 β1 γ4 (i + 1) - k19Tri α4 β1 γ4 i) (t - k19Tri α4 β1 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, -, -, -⟩ := k19_z3
  have k1 := hD
  have kb := mul_pos hD (by linarith : (0:ℝ) < β1)
  have kg := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kbg := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) (by linarith : (0:ℝ) < γ4)
  have kb1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) (sub_pos.2 hβ1)
  have kg1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) (sub_pos.2 hγ4)
  have kin := mul_pos hD hin
  have kbg6 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) hγ6
  have kb6g := mul_pos (mul_pos hD hβ6) (by linarith : (0:ℝ) < γ4)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kbv2 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) hv2
  have kgv1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hv1
  have kagv1 := mul_pos (mul_pos (mul_pos hD hα4) (by linarith : (0:ℝ) < β1)) hv1
  have kag := mul_pos (mul_pos hD hα4) (sub_pos.2 hγ4)
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k19_z3_cases i with rfl | rfl | rfl <;>
      rcases k19_z3_cases j with rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, s0, s1, s2, k19Tri_0, k19Tri_1, k19Tri_2, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
    rcases k19_z3_cases i with rfl | rfl | rfl <;>
      (simp only [TSc, d3, s0, s1, s2, k19Tri_0, k19Tri_1, k19Tri_2, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k19Tri_inj {α4 β1 γ4 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) :
    ∀ i j, k19Tri α4 β1 γ4 i = k19Tri α4 β1 γ4 j → i = j := by
  intro i j h
  rcases k19_z3_cases i with rfl | rfl | rfl <;>
    rcases k19_z3_cases j with rfl | rfl | rfl <;>
    simp only [k19Tri_0, k19Tri_1, k19Tri_2, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

/-- Quadrilateral `a (0,0,1), c' (β1,0,1), a' (β6,γ6,0), b' (0,γ4,α4)`. -/
def k19Qd (α4 β1 γ4 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := ![(0, 0, 1), (β1, 0, 1), (β6, γ6, 0), (0, γ4, α4)]

theorem k19Qd_0 : k19Qd α4 β1 γ4 β6 γ6 0 = (0, 0, 1) := rfl
theorem k19Qd_1 : k19Qd α4 β1 γ4 β6 γ6 1 = (β1, 0, 1) := rfl
theorem k19Qd_2 : k19Qd α4 β1 γ4 β6 γ6 2 = (β6, γ6, 0) := rfl
theorem k19Qd_3 : k19Qd α4 β1 γ4 β6 γ6 3 = (0, γ4, α4) := rfl

set_option maxHeartbeats 3200000 in
theorem k19_qd_tsc {D α4 β1 γ4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hβ1 : 1 < β1) (hγ4 : 1 < γ4)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hout : 0 < β1 * γ6 + β6 * γ4 - β1 * γ4) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k19Qd α4 β1 γ4 β6 γ6 (i + 1) - k19Qd α4 β1 γ4 β6 γ6 i)
        (k19Qd α4 β1 γ4 β6 γ6 j - k19Qd α4 β1 γ4 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc D (k19Qd α4 β1 γ4 β6 γ6 (i + 1) - k19Qd α4 β1 γ4 β6 γ6 i) (t - k19Qd α4 β1 γ4 β6 γ6 i)
        (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, -, -, -, -⟩ := k19_z4
  have hc : 0 < β1 * γ6 + β6 - β1 := by
    have k0 := mul_pos (mul_pos (by linarith : (0:ℝ) < β1) hγ6) (sub_pos.2 hγ4)
    have : 0 < γ4 * (β1 * γ6 + β6 - β1) := by nlinarith
    exact pos_of_mul_pos_right this (by linarith)
  have hb : 0 < γ4 * (β6 - 1) + γ6 := by
    have k0 := mul_pos (mul_pos hβ6 (by linarith : (0:ℝ) < γ4)) (sub_pos.2 hβ1)
    have : 0 < β1 * (γ4 * (β6 - 1) + γ6) := by nlinarith
    exact pos_of_mul_pos_right this (by linarith)
  have k1 := hD
  have kb := mul_pos hD (by linarith : (0:ℝ) < β1)
  have kg := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kbg := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) (by linarith : (0:ℝ) < γ4)
  have kbg6 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) hγ6
  have kb6g := mul_pos (mul_pos hD hβ6) (by linarith : (0:ℝ) < γ4)
  have kout := mul_pos hD hout
  have kc := mul_pos hD hc
  have khb := mul_pos hD hb
  have kg61 := mul_pos (mul_pos hD hγ6) (sub_pos.2 hβ1)
  have kb6g1 := mul_pos (mul_pos hD hβ6) (sub_pos.2 hγ4)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kbv2 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) hv2
  have kgv1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hv1
  have kagv1 := mul_pos (mul_pos (mul_pos hD hα4) (by linarith : (0:ℝ) < β1)) hv1
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, s0, s1, s2, s3, k19Qd_0, k19Qd_1, k19Qd_2, k19Qd_3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, s0, s1, s2, s3, k19Qd_0, k19Qd_1, k19Qd_2, k19Qd_3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k19Qd_inj {α4 β1 γ4 β6 γ6 : ℝ} (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) :
    ∀ i j, k19Qd α4 β1 γ4 β6 γ6 i = k19Qd α4 β1 γ4 β6 γ6 j → i = j := by
  intro i j h
  rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k19Qd_0, k19Qd_1, k19Qd_2, k19Qd_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
/-- `β1 > 1`: triangle `(a,c',b')` (a' inside) or quadrilateral `(a,c',a',b')` (a' outside) at `a - d`. -/
theorem k19_u1l_ad {a a' b b' c c' d : ℝ³} {α4 β1 γ4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ1 : 1 < β1)
    (hγ : γ4 = 1 - α4 + α4 * β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0)
    (hside : β1 * γ4 - β1 * γ6 - β6 * γ4 ≠ 0) : HasLexCell (V8 a a' b b' c c' d) := by
  have hγ4 : 1 < γ4 := by rw [hγ]; nlinarith [mul_pos hα4 (sub_pos.2 hβ1)]
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
  have Eb' : fpoint P Q R d (0, γ4, α4) = b' := by rw [k17f_fp, hb']; module
  have Ec' : fpoint P Q R d (β1, 0, 1) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hPR : ⟪P, R⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have hQR : ⟪Q, R⟫ = 0 := by rw [real_inner_comm]; exact hpr
  have hPQ : ⟪P, Q⟫ = 0 := hqr
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  refine ⟨R, hR0, ?_⟩
  rcases hside.lt_or_gt with hout | hin
  · -- a' outside: quadrilateral
    have hout' : 0 < β1 * γ6 + β6 * γ4 - β1 * γ4 := by linarith
    refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 4) (by norm_num) (k19Qd α4 β1 γ4 β6 γ6)
      (k19Qd_inj hα4 hα41 (by linarith) (by linarith)) ?_ [(1, 0), (0, 1)] (by simp) ?_ ?_ ?_
      (ρ1 := 1) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
    · intro i
      rcases k19_z4_cases i with rfl | rfl | rfl | rfl
      · rw [k19Qd_0, Ea]; simp [V8]
      · rw [k19Qd_1, Ec']; simp [V8]
      · rw [k19Qd_2, Ea']; simp [V8]
      · rw [k19Qd_3, Eb']; simp [V8]
    · intro v1 v2 hC D hD
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact (k19_qd_tsc hD hα4 hβ1 hγ4 hβ6 hγ6 hout' (by linarith) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (β1, 0, 1) ∨ y = fpoint P Q R d (β6, γ6, 0) ∨
          y = fpoint P Q R d (0, γ4, α4) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
          y = fpoint P Q R d (0, 1, 0) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      have hT : ∀ v1 v2 : ℝ, k18Cone [(1, 0), (0, 1)] v1 v2 → ∀ D : ℝ, 0 < D →
          ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
            TSc D (k19Qd α4 β1 γ4 β6 γ6 (i + 1) - k19Qd α4 β1 γ4 β6 γ6 i) (t - k19Qd α4 β1 γ4 β6 γ6 i)
              (v1, v2, 0) := by
        intro v1 v2 hC D hD
        have h1 := hC (1, 0) (by simp)
        have h2 := hC (0, 1) (by simp)
        simp only at h1 h2
        exact (k19_qd_tsc hD hα4 hβ1 hγ4 hβ6 hγ6 hout' (by linarith) (by linarith)).2
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by rw [k19Qd_0])).elim
      · exact (hyx 1 (by rw [k19Qd_1])).elim
      · exact (hyx 2 (by rw [k19Qd_2])).elim
      · exact (hyx 3 (by rw [k19Qd_3])).elim
      · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
      · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
      · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · intro v1 v2 hC hw
      have h1 := hC (1, 0) (by simp)
      simp only at h1
      obtain ⟨s0, s1, s2, s3, e0, e1, e2, e3⟩ := k19_z4
      have hac : LexLt (⟪fpoint P Q R d (k19Qd α4 β1 γ4 β6 γ6 0), R⟫,
          ⟪fpoint P Q R d (k19Qd α4 β1 γ4 β6 γ6 0), fcomb P Q R v1 v2 0⟫)
          (⟪fpoint P Q R d (k19Qd α4 β1 γ4 β6 γ6 1), R⟫,
          ⟪fpoint P Q R d (k19Qd α4 β1 γ4 β6 γ6 1), fcomb P Q R v1 v2 0⟫) := by
        right
        refine ⟨by simp only [k19Qd_0, k19Qd_1, hz, hPR, hQR]; ring, ?_⟩
        simp only [k19Qd_0, k19Qd_1, hwx, hPQ, hPR, hQR]
        nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < v1)) hPP]
      refine k19_lexUni_nb _ _ hw 1 ?_ ?_ ?_
      · rw [e1]; exact hac
      · rw [s1]; left; simp only [k19Qd_1, k19Qd_2, hz, hPR, hQR]; nlinarith
      · intro i hi
        rcases k19_z4_cases i with rfl | rfl | rfl | rfl
        · right; rw [s0]; exact hac
        · exact absurd rfl hi
        · left; rw [e2]; left; simp only [k19Qd_1, k19Qd_2, hz, hPR, hQR]; nlinarith
        · right; rw [s3]; left; simp only [k19Qd_0, k19Qd_3, hz, hPR, hQR]
          nlinarith [mul_pos (sub_pos.2 hα41) hRR]
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> (left; norm_num)
  · -- a' inside: triangle
    refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 3) (by norm_num) (k19Tri α4 β1 γ4)
      (k19Tri_inj (by linarith) (by linarith)) ?_ [(1, 0), (0, 1)] (by simp) ?_ ?_ ?_
      (ρ1 := 1) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
    · intro i
      rcases k19_z3_cases i with rfl | rfl | rfl
      · rw [k19Tri_0, Ea]; simp [V8]
      · rw [k19Tri_1, Ec']; simp [V8]
      · rw [k19Tri_2, Eb']; simp [V8]
    · intro v1 v2 hC D hD
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      exact (k19_tri_tsc hD hα4 hβ1 hγ4 hβ6 hγ6 hin (by linarith) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (β1, 0, 1) ∨ y = fpoint P Q R d (0, γ4, α4) ∨
          y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
          y = fpoint P Q R d (β6, γ6, 0) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      have hT : ∀ v1 v2 : ℝ, k18Cone [(1, 0), (0, 1)] v1 v2 → ∀ D : ℝ, 0 < D →
          ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0), (β6, γ6, 0)], ∀ i : ZMod 3,
            TSc D (k19Tri α4 β1 γ4 (i + 1) - k19Tri α4 β1 γ4 i) (t - k19Tri α4 β1 γ4 i) (v1, v2, 0) := by
        intro v1 v2 hC D hD
        have h1 := hC (1, 0) (by simp)
        have h2 := hC (0, 1) (by simp)
        simp only at h1 h2
        exact (k19_tri_tsc hD hα4 hβ1 hγ4 hβ6 hγ6 hin (by linarith) (by linarith)).2
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by rw [k19Tri_0])).elim
      · exact (hyx 1 (by rw [k19Tri_1])).elim
      · exact (hyx 2 (by rw [k19Tri_2])).elim
      · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
      · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
      · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
      · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · intro v1 v2 hC hw
      have h1 := hC (1, 0) (by simp)
      simp only at h1
      obtain ⟨s0, s1, s2, e0, e1, e2⟩ := k19_z3
      have hac : LexLt (⟪fpoint P Q R d (k19Tri α4 β1 γ4 0), R⟫,
          ⟪fpoint P Q R d (k19Tri α4 β1 γ4 0), fcomb P Q R v1 v2 0⟫)
          (⟪fpoint P Q R d (k19Tri α4 β1 γ4 1), R⟫,
          ⟪fpoint P Q R d (k19Tri α4 β1 γ4 1), fcomb P Q R v1 v2 0⟫) := by
        right
        refine ⟨by simp only [k19Tri_0, k19Tri_1, hz, hPR, hQR]; ring, ?_⟩
        simp only [k19Tri_0, k19Tri_1, hwx, hPQ, hPR, hQR]
        nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < β1) (by linarith : (0:ℝ) < v1)) hPP]
      refine k19_lexUni_nb _ _ hw 1 ?_ ?_ ?_
      · rw [e1]; exact hac
      · rw [s1]; left; simp only [k19Tri_1, k19Tri_2, hz, hPR, hQR]; nlinarith [mul_pos (sub_pos.2 hα41) hRR]
      · intro i hi
        rcases k19_z3_cases i with rfl | rfl | rfl
        · right; rw [s0]; exact hac
        · exact absurd rfl hi
        · left; rw [e2]; left; simp only [k19Tri_1, k19Tri_2, hz, hPR, hQR]
          nlinarith [mul_pos (sub_pos.2 hα41) hRR]
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> (left; norm_num)

/-- Frame of U1 at `α4 < 1`: `γ4 = 1 - α4 + α4 β1`, `pq = qr = 0`. -/
theorem k19_u1l_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h1 : ⟪a - c, d - b⟫ = 0) (h2 : ⟪a - d, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ α4 < 1 ∧ 0 < β1 ∧ γ4 = 1 - α4 + α4 * β1 ∧
      0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 ∧ ⟪a - d, b - d⟫ = 0 ∧ ⟪b - d, c - d⟫ = 0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, hαγ, hβ6, hγ6, hs, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_alpha4 hb'] at hα
  have hα1 : α4 < 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have hg4 : γ4 = 1 - α4 + α4 * β1 := by
    have := (planar_a_iff hdet hc' hb').1 hκ
    linarith
  have e2 : d - b = -(b - d) := by abel
  have hpq : ⟪a - d, b - d⟫ = 0 := by
    rw [e2, inner_neg_right] at h2; linarith
  have hqr : ⟪b - d, c - d⟫ = 0 := by
    have e : a - c = (a - d) - (c - d) := by abel
    rw [e, e2, inner_neg_right, inner_sub_left, hpq, real_inner_comm] at h1; linarith
  exact ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hα1, hβ1, hg4, hβ6, hγ6, hfa hfar, hs, hpq, hqr⟩

/-- **U1 tie at `α4 < 1`** (`k17gc_u1`'s leftover `⟪a-d,c-d⟫ = 0` with the strict `α4`-product): a cell unless
`β1 = 1` or `a'` lies on the screen line `c' b'` at the view `a - d`. -/
theorem k19_u1_lt {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (h1 : ⟪a - c, d - b⟫ = 0) (h2 : ⟪a - d, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ det3 (a - d) (c' - b) (c - d) = 0 ∨
      det3 (c' - a') (b' - a') (a - d) = 0 := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hα41, hβ1, hγ, hβ6, hγ6, hγ61, hs, hpq, hqr⟩ :=
    k19_u1l_frame W hT' hκ (k5z_far1 W hT' hnT) h1 h2 hα
  rcases lt_trichotomy β1 1 with hl | he | hg
  · exact Or.inl (k19_u1l_hex hdet hc' hb' ha' hα4 hα41 hβ1 hl hγ hβ6 hγ6 hγ61 hs hpq hqr hpr)
  · right; left; rw [det_beta1 hc', he, sub_self, zero_mul]
  · by_cases hside : β1 * γ4 - β1 * γ6 - β6 * γ4 = 0
    · right; right
      have e : det3 (c' - a') (b' - a') (a - d) =
          (β1 * γ4 - β1 * γ6 - β6 * γ4) * det3 (a - d) (b - d) (c - d) := by
        rw [hc', hb', ha']
        simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [e, hside, zero_mul]
    · exact Or.inl (k19_u1l_ad hdet hc' hb' ha' hα4 hα41 hg hγ hβ6 hγ6 hpq hqr hpr hside)

end C2
end Type08Sp
end Minimality
