module

public import Minimality.Type08S.C2K19E

@[expose] public section


/-!
# K19 / F: S1.6 at `⟪a-d,a-c'⟫ = 0` (L9): `K6t3LeftPc` with `pq = 0`

Pc frame (`α1 = α4 = β6 = 1`); `u = 0` gives `pr = m pq = 0` too (`m = 1-γ6`), so `p ⟂ q, r`.  View `d - b`, frame
`(c-d, a-d, d-b)`; depths relative to `d`: `a = d = 0`, `c = -qr`, `b' = -γ4 qr`, `b = -qq`, `c' = -β1 qq`,
`a' = -qq - γ6 qr`.  Two cells at `d - b`, both w-free on their whole cones (apart from the cone sign of `w(a)-w(d)`):
* hexagon X1 `(b,a',c,b',a,c')` (`k19HexY`, cone `v1, v2 < 0`): `qr < 0` (peak `c` or `b'`), or `qr > 0`, `γ4 < 1`,
  `z(b') > z(c')` (peak `a`; needs `β1 < 1`, from the Gale sign `κ_a = μ(γ4-β1) ≥ 0`, `μ > 0` by `κ_b > 0` off `T`);
* the S1.6b pentagon `(c,b',c',a,d)` (`k17gcPent6`, cone `v1, v2 > 0`, `w(a) > w(d)`): `qr > 0` and
  (`γ4 > 1` or `z(b') < z(c')`).
Leftovers: `qr = 0`, `⟪b'-c,d-b⟫ = 0` (γ4 = 1), `⟪b'-c',d-b⟫ = 0`.
Numerics (gsec, K17F pcu0 data, ties u = 0 and the literal, w ≥ 0): `qr < 0` ⟹ X1 845/845; `qr > 0` with the S1.6b
condition ⟹ S1.6b 349/349; `qr > 0` otherwise ⟹ X1 6/6 (all with `β1 < γ4`, as the Gale sign forces).
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

/-- Hexagon `(b,a',c,b',a,c')` in the frame `(c-d, a-d, d-b)`, `b' = (γ4,1,0)`. -/
def k19HexY (β1 γ4 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 0, -1) (γ6, 0, -β6) (1, 0, 0) (γ4, 1, 0) (0, 1, 0) (0, 1, -β1)

set_option maxHeartbeats 3200000 in
theorem k19_hexY_tsc {D β1 γ4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k19HexY β1 γ4 β6 γ6 (i + 1) - k19HexY β1 γ4 β6 γ6 i)
        (k19HexY β1 γ4 β6 γ6 j - k19HexY β1 γ4 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 6, TSc D (k19HexY β1 γ4 β6 γ6 (i + 1) - k19HexY β1 γ4 β6 γ6 i)
      ((0, 0, 0) - k19HexY β1 γ4 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have n1 : 0 < -v1 := by linarith
  have n2 : 0 < -v2 := by linarith
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kb := mul_pos hD hβ6
  have kb1 := mul_pos hD hβ1
  have kg4 := mul_pos hD hγ4
  have kbg4 := mul_pos (mul_pos hD hβ1) hγ4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD n1
  have kv2 := mul_pos hD n2
  have kgv1 := mul_pos (mul_pos hD hγ6) n1
  have kgv2 := mul_pos (mul_pos hD hγ6) n2
  have kbv2 := mul_pos (mul_pos hD hβ6) n2
  have ksv2 := mul_pos (mul_pos hD (sub_pos.2 hs)) n2
  have kb1v1 := mul_pos (mul_pos hD hβ1) n1
  have kb1v2 := mul_pos (mul_pos hD hβ1) n2
  have kbg4v2 := mul_pos (mul_pos (mul_pos hD hβ1) hγ4) n2
  have kg4v2 := mul_pos (mul_pos hD hγ4) n2
  have kbgv2 := mul_pos (mul_pos (mul_pos hD hβ1) hγ6) n2
  constructor
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k19HexY, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k19HexY, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k19HexY_inj {β1 γ4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) : ∀ i j, k19HexY β1 γ4 β6 γ6 i = k19HexY β1 γ4 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k19HexY, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h; done) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
/-- The two cells of S1.6 at `pq = pr = 0`, by the depth literals at `d - b`. -/
theorem k19_s16q_cells {a a' b b' c c' d : ℝ³} {β1 γ4 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hfacet : β1 * (1 - γ6) < γ4) (hβγ : β1 ≤ γ4)
    (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0)
    (hcase : ⟪b - d, c - d⟫ < 0 ∨
      (0 < ⟪b - d, c - d⟫ ∧ 0 < ⟪b' - c, d - b⟫ ∧ 0 < ⟪b' - c', d - b⟫) ∨
      (0 < ⟪b - d, c - d⟫ ∧ (⟪b' - c, d - b⟫ < 0 ∨ ⟪b' - c', d - b⟫ < 0))) :
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
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hPQ : ⟪P, Q⟫ = 0 := by rw [hP, hQ, real_inner_comm]; exact hpr
  have hPRe : ⟪P, R⟫ = -⟪b - d, c - d⟫ := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm]
  have hBC : ⟪b' - c, d - b⟫ = (γ4 - 1) * ⟪P, R⟫ := by
    have e : b' - c = (γ4 - 1) • P + Q := by rw [hb', hP, hQ]; module
    rw [e, inner_add_left, real_inner_smul_left, hQR, add_zero]
  have hBC' : ⟪b' - c', d - b⟫ = γ4 * ⟪P, R⟫ + β1 * ⟪R, R⟫ := by
    have e : b' - c' = γ4 • P + β1 • R := by rw [hb', hc', hP, hQ, hR]; module
    rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hm : 0 < 1 - γ6 := by linarith
  refine ⟨R, hR0, ?_⟩
  rcases hcase with hc | ⟨hc, h1, h2⟩ | ⟨hc, h12⟩
  · -- `qr < 0`: X1, peak `c` or `b'`
    have hPR : 0 < ⟪P, R⟫ := by rw [hPRe]; linarith
    refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k19HexY β1 γ4 1 γ6)
      (k19HexY_inj hβ1 hγ4 one_pos hγ6 hγ61) ?_ [(-1, 0), (0, -1)] (by simp) ?_ ?_ ?_
      (ρ1 := -1) (ρ2 := -1) (δ1 := 0) (δ2 := 0) ?_
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k19HexY, pc6_0, Eb]; simp [V8]
      · simp only [k19HexY, pc6_1, Ea']; simp [V8]
      · simp only [k19HexY, pc6_2, Ec]; simp [V8]
      · simp only [k19HexY, pc6_3, Eb']; simp [V8]
      · simp only [k19HexY, pc6_4, Ea]; simp [V8]
      · simp only [k19HexY, pc6_5, Ec']; simp [V8]
    · intro v1 v2 hC D hD
      have h1 := hC (-1, 0) (by simp)
      have h2 := hC (0, -1) (by simp)
      simp only at h1 h2
      exact (k19_hexY_tsc hD hβ1 hγ4 one_pos hγ6 hγ61 (by linarith) (by linarith) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (γ6, 0, -1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
          y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨
          y = fpoint P Q R d (0, 0, 0) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k19HexY, pc6_0])).elim
      · exact (hyx 1 (by simp only [k19HexY, pc6_1])).elim
      · exact (hyx 2 (by simp only [k19HexY, pc6_2])).elim
      · exact (hyx 3 (by simp only [k19HexY, pc6_3])).elim
      · exact (hyx 4 (by simp only [k19HexY, pc6_4])).elim
      · exact (hyx 5 (by simp only [k19HexY, pc6_5])).elim
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        have h1 := hC (-1, 0) (by simp)
        have h2 := hC (0, -1) (by simp)
        simp only at h1 h2
        exact (k19_hexY_tsc hD hβ1 hγ4 one_pos hγ6 hγ61 (by linarith) (by linarith) (by linarith)).2 i
    · intro v1 v2 hC hinj
      obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := k19_z6
      refine k19_lexUni_nb2 _ _ hinj 2 (by decide) ?_ ?_ ?_
      · rw [e2]; left; simp only [k19HexY, pc6_1, pc6_2, hz, hQR]; nlinarith [mul_pos hm hPR]
      · rw [f2, f3]; left; simp only [k19HexY, pc6_3, pc6_4, hz, hQR]; nlinarith [mul_pos hγ4 hPR]
      · intro i hi hi'
        rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
        · right; rw [f0]; left; simp only [k19HexY, pc6_0, pc6_1, hz, hQR]; nlinarith [mul_pos hγ6 hPR]
        · right; rw [f1]; left; simp only [k19HexY, pc6_1, pc6_2, hz, hQR]; nlinarith [mul_pos hm hPR]
        · exact absurd rfl hi
        · exact absurd rfl hi'
        · left; rw [e4]; left; simp only [k19HexY, pc6_3, pc6_4, hz, hQR]; nlinarith [mul_pos hγ4 hPR]
        · left; rw [e5]; left; simp only [k19HexY, pc6_4, pc6_5, hz, hQR]; nlinarith [mul_pos hβ1 hRR]
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> (left; norm_num)
  · -- `qr > 0`, `γ4 < 1`, `z(b') > z(c')`: X1, peak `a`
    have hPR : ⟪P, R⟫ < 0 := by rw [hPRe]; linarith
    rw [hBC] at h1
    rw [hBC'] at h2
    have hg1 : γ4 < 1 := by nlinarith
    have hb1 : β1 < 1 := by linarith
    refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k19HexY β1 γ4 1 γ6)
      (k19HexY_inj hβ1 hγ4 one_pos hγ6 hγ61) ?_ [(-1, 0), (0, -1)] (by simp) ?_ ?_ ?_
      (ρ1 := -1) (ρ2 := -1) (δ1 := 0) (δ2 := 0) ?_
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k19HexY, pc6_0, Eb]; simp [V8]
      · simp only [k19HexY, pc6_1, Ea']; simp [V8]
      · simp only [k19HexY, pc6_2, Ec]; simp [V8]
      · simp only [k19HexY, pc6_3, Eb']; simp [V8]
      · simp only [k19HexY, pc6_4, Ea]; simp [V8]
      · simp only [k19HexY, pc6_5, Ec']; simp [V8]
    · intro v1 v2 hC D hD
      have h1 := hC (-1, 0) (by simp)
      have h2 := hC (0, -1) (by simp)
      simp only at h1 h2
      exact (k19_hexY_tsc hD hβ1 hγ4 one_pos hγ6 hγ61 (by linarith) (by linarith) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (γ6, 0, -1) ∨ y = fpoint P Q R d (1, 0, 0) ∨
          y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨
          y = fpoint P Q R d (0, 0, 0) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k19HexY, pc6_0])).elim
      · exact (hyx 1 (by simp only [k19HexY, pc6_1])).elim
      · exact (hyx 2 (by simp only [k19HexY, pc6_2])).elim
      · exact (hyx 3 (by simp only [k19HexY, pc6_3])).elim
      · exact (hyx 4 (by simp only [k19HexY, pc6_4])).elim
      · exact (hyx 5 (by simp only [k19HexY, pc6_5])).elim
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        have h1 := hC (-1, 0) (by simp)
        have h2 := hC (0, -1) (by simp)
        simp only at h1 h2
        exact (k19_hexY_tsc hD hβ1 hγ4 one_pos hγ6 hγ61 (by linarith) (by linarith) (by linarith)).2 i
    · intro v1 v2 hC hinj
      obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := k19_z6
      refine k19_lexUni_nb _ _ hinj 4 ?_ ?_ ?_
      · rw [e4]; left; simp only [k19HexY, pc6_3, pc6_4, hz, hQR]; nlinarith [mul_pos hγ4 (neg_pos.2 hPR)]
      · rw [f4]; left; simp only [k19HexY, pc6_4, pc6_5, hz, hQR]; nlinarith [mul_pos hβ1 hRR]
      · intro i hi
        rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
        · left; rw [e0]; left; simp only [k19HexY, pc6_0, pc6_5, hz, hQR]
          nlinarith [mul_pos (sub_pos.2 hb1) hRR]
        · left; rw [e1]; left; simp only [k19HexY, pc6_0, pc6_1, hz, hQR]
          nlinarith [mul_pos hγ6 (neg_pos.2 hPR)]
        · right; rw [f2]; left; simp only [k19HexY, pc6_2, pc6_3, hz, hQR]
          nlinarith [mul_pos (sub_pos.2 hg1) (neg_pos.2 hPR)]
        · right; rw [f3]; left; simp only [k19HexY, pc6_3, pc6_4, hz, hQR]; nlinarith [mul_pos hγ4 (neg_pos.2 hPR)]
        · exact absurd rfl hi
        · left; rw [e5]; left; simp only [k19HexY, pc6_4, pc6_5, hz, hQR]; nlinarith [mul_pos hβ1 hRR]
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> (left; norm_num)
  · -- `qr > 0`, `z(b') < z(c)` or `z(b') < z(c')`: the S1.6b pentagon, peak `a`
    have hPR : ⟪P, R⟫ < 0 := by rw [hPRe]; linarith
    rw [hBC, hBC'] at h12
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
      have h1 := hC (1, 0) (by simp)
      have h2 := hC (0, 1) (by simp)
      simp only at h1 h2
      have hv2 : 0 < v2 := by linarith
      obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
      have hda : LexLt (⟪fpoint P Q R d (k17gcPent6 β1 γ4 4), R⟫,
          ⟪fpoint P Q R d (k17gcPent6 β1 γ4 4), fcomb P Q R v1 v2 0⟫)
          (⟪fpoint P Q R d (k17gcPent6 β1 γ4 3), R⟫,
          ⟪fpoint P Q R d (k17gcPent6 β1 γ4 3), fcomb P Q R v1 v2 0⟫) := by
        right
        refine ⟨by simp only [k17gcPent6, pc5_3, pc5_4, hz, hQR]; ring, ?_⟩
        simp only [k17gcPent6, pc5_3, pc5_4, hwx, hPQ, hQR]; nlinarith [mul_pos hv2 hQQ]
      refine k19_lexUni_nb _ _ hinj 3 ?_ ?_ ?_
      · rw [e3]; left; simp only [k17gcPent6, pc5_2, pc5_3, hz, hQR]; nlinarith [mul_pos hβ1 hRR]
      · rw [f3]; exact hda
      · intro i hi
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · left; rw [e0]; left; simp only [k17gcPent6, pc5_0, pc5_4, hz, hQR]; nlinarith
        · rcases h12 with h | h
          · left; rw [e1]; left; simp only [k17gcPent6, pc5_0, pc5_1, hz, hQR]; nlinarith
          · right; rw [f1]; left; simp only [k17gcPent6, pc5_1, pc5_2, hz, hQR]; nlinarith
        · right; rw [f2]; left; simp only [k17gcPent6, pc5_2, pc5_3, hz, hQR]; nlinarith [mul_pos hβ1 hRR]
        · exact absurd rfl hi
        · left; rw [e4]; exact hda
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> (left; norm_num)

/-- **S1.6 at `⟪a-d,a-c'⟫ = 0`** (`k17gc_s16`'s second disjunct): a cell, or one of the depth ties at `d - b`:
`⟪b-d,c-d⟫ = 0`, `⟪b'-c,d-b⟫ = 0`, `⟪b'-c',d-b⟫ = 0`. -/
theorem k19_s16_pq0 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftPc a a' b b' c c' d)
    (hZ : ⟪a - d, a - c'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪b - d, c - d⟫ = 0 ∨ ⟪b' - c, d - b⟫ = 0 ∨ ⟪b' - c', d - b⟫ = 0 := by
  obtain ⟨hPc, hu, -⟩ := h
  obtain ⟨β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, hfacet⟩ := k17gc_pc_frame W hPc
  obtain ⟨hT', hnT, -, -⟩ := hPc
  have e : ⟪a - d, a - c'⟫ = -β1 * ⟪a - d, b - d⟫ := by
    have : a - c' = (-β1) • (b - d) := by rw [hc']; module
    rw [this, real_inner_smul_right]
  have hpq : ⟪a - d, b - d⟫ = 0 := by
    rw [e] at hZ
    rcases mul_eq_zero.1 hZ with h1 | h1
    · linarith
    · exact h1
  have hpr : ⟪a - d, c - d⟫ = 0 := by
    have e1 : c - a' = (1 - γ6) • (c - d) - (b - d) := by rw [ha']; module
    rw [e1, inner_sub_left, real_inner_smul_left, real_inner_comm (a - d) (b - d), hpq,
      real_inner_comm (a - d) (c - d)] at hu
    have : (1 - γ6) * ⟪a - d, c - d⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exfalso; linarith
    · exact h1
  -- Gale: `κ_b > 0` (off `T`) gives `μ > 0`, then `κ_a ≥ 0` gives `β1 ≤ γ4`
  have hβγ : β1 ≤ γ4 := by
    obtain ⟨μ, h1, h2⟩ := gale_coords_gen W.G hdet hc' hb' ha' (by linarith)
    have hkb : 0 < galeD W.G.l W.G.m b b' := by
      rcases W.hκb.lt_or_eq with h | h
      · exact h
      · exact (hnT (k5z_kb0_Tp W hT' (k5z_planar_b_of_gale W.F W.G h.symm))).elim
    rw [h2] at hkb
    have hμ : 0 < μ := by
      have h3 : 0 < (1 : ℝ) * (1 - 1) + β1 * (1 - γ6) := by nlinarith
      exact pos_of_mul_pos_left hkb h3.le
    have hka := W.hκa
    rw [h1] at hka
    by_contra hh; push Not at hh
    nlinarith
  rcases lt_trichotomy ⟪b - d, c - d⟫ 0 with hn | h0 | hp
  · exact Or.inl (k19_s16q_cells hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hfacet hβγ hpq hpr (Or.inl hn))
  · exact Or.inr (Or.inl h0)
  · rcases lt_trichotomy ⟪b' - c, d - b⟫ 0 with h1 | h1 | h1
    · exact Or.inl (k19_s16q_cells hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hfacet hβγ hpq hpr
        (Or.inr (Or.inr ⟨hp, Or.inl h1⟩)))
    · exact Or.inr (Or.inr (Or.inl h1))
    · rcases lt_trichotomy ⟪b' - c', d - b⟫ 0 with h2 | h2 | h2
      · exact Or.inl (k19_s16q_cells hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hfacet hβγ hpq hpr
          (Or.inr (Or.inr ⟨hp, Or.inr h2⟩)))
      · exact Or.inr (Or.inr (Or.inr h2))
      · exact Or.inl (k19_s16q_cells hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hfacet hβγ hpq hpr
          (Or.inr (Or.inl ⟨hp, h1, h2⟩)))

end C2
end Type08Sp
end Minimality
