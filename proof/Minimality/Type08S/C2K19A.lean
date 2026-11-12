module

public import Minimality.Type08S.C2K17GC5
public import Minimality.Type08S.C2K18A

@[expose] public section


/-!
# K19 / A: the U3 tie `⟪a-d,a-c'⟫ = 0` (L8) by the two-cell tie lemma

U3 (`K14LeftPa` 3rd disjunct, `β1 > 1`): `α4 = 1`, `γ4 = β1`, tie `pq + (β1-1) qr = 0`.  On the literal's tie `pq = 0`
also `qr = 0`, so in the frame `(P,Q,R) = (c-d, a-d, d-b)` of U3b both `⟪P,R⟫ = ⟪Q,R⟫ = 0`: the face `Q_ac`
(`a,d,c,b'`) is a 4-plateau at the view `d - b`.  The tilt `w = g1 t1 + g2 t2` with `g = Gram(P,Q)·v` orders it.
* X1 hexagon `(a,d,b,a',c,b')` (screen: `b = d`, `c' = a`, `a'` on edge `d c`), cone `v1 > 0 > v2`: needs
  `w(a) > w(d)` (`m·v > 0`, `m = (⟪P,Q⟫, ⟪Q,Q⟫)`) and `g1 > 0`.
* U3b pentagon `(b',c',a,d,c)`, cone `v1, v2 > 0`: needs `w(a) < w(d)` (`m·v < 0`) and `g1 > 0`.
Shared ray `ρ = (1,0)`, `m·ρ = ⟪c-d,a-d⟫ = pr`: `k18_tie_two`.  Leftover `pq = qr = pr = 0`.
Numerics (gsec, exact Gram samples on the K17F pa3p data with both ties): `pr > 0` ⟹ X1 1200/1200,
`pr < 0` ⟹ U3b 1200/1200.
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

theorem k19_cone4 {a b a' b' a'' b'' v1 v2 : ℝ} {m : ℝ × ℝ}
    (h : k18Cone (m :: [(a, b), (a', b'), (a'', b'')]) v1 v2) :
    0 < m.1 * v1 + m.2 * v2 ∧ 0 < a * v1 + b * v2 ∧ 0 < a' * v1 + b' * v2 ∧ 0 < a'' * v1 + b'' * v2 :=
  ⟨h m List.mem_cons_self, h (a, b) (by simp), h (a', b') (by simp), h (a'', b'') (by simp)⟩

/-- Hexagon X1 of the U3 tie: `a (0,1,0), d 0, b (0,0,-1), a' (γ6,0,-β6), c (1,0,0), b' (β1,1,0)`. -/
def k19Hex3 (β1 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 1, 0) (0, 0, 0) (0, 0, -1) (γ6, 0, -β6) (1, 0, 0) (β1, 1, 0)

set_option maxHeartbeats 3200000 in
theorem k19_hex3_tsc {D β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k19Hex3 β1 β6 γ6 (i + 1) - k19Hex3 β1 β6 γ6 i) (k19Hex3 β1 β6 γ6 j - k19Hex3 β1 β6 γ6 i)
        (v1, v2, 0)) ∧
    (∀ i : ZMod 6, TSc D (k19Hex3 β1 β6 γ6 (i + 1) - k19Hex3 β1 β6 γ6 i) ((0, 1, -β1) - k19Hex3 β1 β6 γ6 i)
      (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have hb0 : 0 < β1 := by linarith
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kb := mul_pos hD hβ6
  have kb1 := mul_pos hD hb0
  have kb11 := mul_pos hD (sub_pos.2 hβ1)
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kbv2 := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  have ksv2 := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv2)
  have kb1v1 := mul_pos (mul_pos hD hb0) hv1
  have kb1v2 := mul_pos (mul_pos hD hb0) (neg_pos.2 hv2)
  have kbbv2 := mul_pos (mul_pos (mul_pos hD hb0) hb0) (neg_pos.2 hv2)
  constructor
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k19Hex3, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k19Hex3, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k19Hex3_inj {β1 β6 γ6 : ℝ} (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, k19Hex3 β1 β6 γ6 i = k19Hex3 β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k19Hex3, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
/-- **U3 on the tie** `pq = qr = 0` with `pr ≠ 0`: X1 hexagon or U3b pentagon at `d - b`. -/
theorem k19_u3_tie_cells {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ ≠ 0) :
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
  have hPQ : ⟪P, Q⟫ ≠ 0 := by rw [hP, hQ, real_inner_comm]; exact hpr
  set m : ℝ × ℝ := (⟪P, Q⟫, ⟪Q, Q⟫) with hm
  set g : ℝ × ℝ := (⟪P, P⟫, ⟪P, Q⟫) with hg
  -- cell 1: X1 hexagon, cone v1 > 0 > v2, needs m·v > 0 and g·v > 0
  have C1 : K18Cell (V8 a a' b b' c c' d) P Q R d (k18Cone (m :: [g, (1, 0), (0, -1)])) := by
    refine k18Cell_of (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k19Hex3 β1 β6 γ6)
      (k19Hex3_inj hβ1 hβ6 hγ6) ?_ _ ?_ ?_ ?_
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k19Hex3, pc6_0, Ea]; simp [V8]
      · simp only [k19Hex3, pc6_1, Ed]; simp [V8]
      · simp only [k19Hex3, pc6_2, Eb]; simp [V8]
      · simp only [k19Hex3, pc6_3, Ea']; simp [V8]
      · simp only [k19Hex3, pc6_4, Ec]; simp [V8]
      · simp only [k19Hex3, pc6_5, Eb']; simp [V8]
    · intro v1 v2 hC D hD
      obtain ⟨-, -, h1, h2⟩ := k19_cone4 hC
      exact (k19_hex3_tsc hD hβ1 hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
          y = fpoint P Q R d (γ6, 0, -β6) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (β1, 1, 0) ∨
          y = fpoint P Q R d (0, 1, -β1) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k19Hex3, pc6_0])).elim
      · exact (hyx 1 (by simp only [k19Hex3, pc6_1])).elim
      · exact (hyx 2 (by simp only [k19Hex3, pc6_2])).elim
      · exact (hyx 3 (by simp only [k19Hex3, pc6_3])).elim
      · exact (hyx 4 (by simp only [k19Hex3, pc6_4])).elim
      · exact (hyx 5 (by simp only [k19Hex3, pc6_5])).elim
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        obtain ⟨-, -, h1, h2⟩ := k19_cone4 hC
        exact (k19_hex3_tsc hD hβ1 hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).2 i
    · intro v1 v2 hC hw
      obtain ⟨hm0, hg0, -, -⟩ := k19_cone4 hC
      simp only [hm, hg] at hm0 hg0
      refine k17gc_lexUni6_a _ _ hw ?_ ?_ ?_ ?_
      · right
        refine ⟨by simp only [k19Hex3, pc6_0, pc6_1, hz, hQR, hPR]; ring, ?_⟩
        simp only [k19Hex3, pc6_0, pc6_1, hwx]; nlinarith
      · left; simp only [k19Hex3, pc6_1, pc6_2, hz, hQR, hPR]; nlinarith
      · right
        refine ⟨by simp only [k19Hex3, pc6_4, pc6_5, hz, hQR, hPR]; ring, ?_⟩
        simp only [k19Hex3, pc6_4, pc6_5, hwx, hQR, hPR]
        nlinarith [mul_pos (sub_pos.2 hβ1) hg0]
      · right; left; simp only [k19Hex3, pc6_3, pc6_4, hz, hQR, hPR]; nlinarith [mul_pos hβ6 hRR]
  -- cell 2: U3b pentagon (b',c',a,d,c), cone v1, v2 > 0, needs m·v < 0 and g·v > 0
  have C2 : K18Cell (V8 a a' b b' c c' d) P Q R d (k18Cone ((-m.1, -m.2) :: [g, (1, 0), (0, 1)])) := by
    refine k18Cell_of (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gcPentU3 β1)
      (k17gcPentU3_inj hβ1) ?_ _ ?_ ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17gcPentU3, pc5_0, Eb']; simp [V8]
      · simp only [k17gcPentU3, pc5_1, Ec']; simp [V8]
      · simp only [k17gcPentU3, pc5_2, Ea]; simp [V8]
      · simp only [k17gcPentU3, pc5_3, Ed]; simp [V8]
      · simp only [k17gcPentU3, pc5_4, Ec]; simp [V8]
    · intro v1 v2 hC D hD i j hi hj
      obtain ⟨-, -, h1, h2⟩ := k19_cone4 hC
      exact tsc_scale hD ((k17gc_pentU3_tsc hβ1 hβ6 hγ6 hγ61 (by linarith) (by linarith)).1 i j hi hj)
    · intro y hy hyx
      have hV : y = fpoint P Q R d (β1, 1, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨ y = fpoint P Q R d (0, 1, 0) ∨
          y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
          y = fpoint P Q R d (γ6, 0, -β6) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k17gcPentU3, pc5_0])).elim
      · exact (hyx 1 (by simp only [k17gcPentU3, pc5_1])).elim
      · exact (hyx 2 (by simp only [k17gcPentU3, pc5_2])).elim
      · exact (hyx 3 (by simp only [k17gcPentU3, pc5_3])).elim
      · exact (hyx 4 (by simp only [k17gcPentU3, pc5_4])).elim
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        obtain ⟨-, -, h1, h2⟩ := k19_cone4 hC
        exact tsc_scale hD ((k17gc_pentU3_tsc hβ1 hβ6 hγ6 hγ61 (by linarith) (by linarith)).2 _ (by simp) i)
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        obtain ⟨-, -, h1, h2⟩ := k19_cone4 hC
        exact tsc_scale hD ((k17gc_pentU3_tsc hβ1 hβ6 hγ6 hγ61 (by linarith) (by linarith)).2 _ (by simp) i)
    · intro v1 v2 hC hw
      obtain ⟨hm0, hg0, -, -⟩ := k19_cone4 hC
      simp only [hm, hg] at hm0 hg0
      refine lexUni5_top _ _ hw ?_ ?_ ?_
      · left; simp only [k17gcPentU3, pc5_0, pc5_1, hz, hQR, hPR]; nlinarith [mul_pos (by linarith : (0:ℝ) < β1) hRR]
      · right
        refine ⟨by simp only [k17gcPentU3, pc5_2, pc5_3, hz, hQR, hPR]; ring, ?_⟩
        simp only [k17gcPentU3, pc5_2, pc5_3, hwx]; nlinarith
      · right
        refine ⟨by simp only [k17gcPentU3, pc5_3, pc5_4, hz, hQR, hPR]; ring, ?_⟩
        simp only [k17gcPentU3, pc5_3, pc5_4, hwx]; nlinarith
  refine ⟨R, hR0, ?_⟩
  refine k18_tie_two C1 C2 (ρ1 := 1) (ρ2 := 0) (δ1 := 0) (δ2 := -1) (ε1 := 0) (ε2 := 1) ?_ ?_ ?_
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; simp only [hg]; linarith
    · left; norm_num
    · right; norm_num
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; simp only [hg]; linarith
    · left; norm_num
    · right; norm_num
  · simp only [hm]; simpa using hPQ

/-- **U3 tie** (`k17gc_u3`'s leftover `⟪a-d,a-c'⟫ = 0`): a cell unless `p, q, r` are pairwise orthogonal. -/
theorem k19_u3_tie {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (h0 : ⟪b' - c, d - b⟫ = 0) (hZ : ⟪a - d, a - c'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨
      (⟪a - d, b - d⟫ = 0 ∧ ⟪b - d, c - d⟫ = 0 ∧ ⟪a - d, c - d⟫ = 0) := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨β1, β6, γ6, hdet, hc', hb', ha', hβ1, hβ6, hγ6, hγ61, hs, htie⟩ :=
    k17gc_u3_frame W hT' hκ (k5z_far1 W hT' hnT) hα hβ h0
  have e : ⟪a - d, a - c'⟫ = -β1 * ⟪a - d, b - d⟫ := by
    have : a - c' = (-β1) • (b - d) := by rw [hc']; module
    rw [this, real_inner_smul_right]
  have hpq : ⟪a - d, b - d⟫ = 0 := by
    rw [e] at hZ
    rcases mul_eq_zero.1 hZ with h1 | h1
    · linarith
    · exact h1
  have hqr : ⟪b - d, c - d⟫ = 0 := by
    rw [hpq, zero_add] at htie
    rcases mul_eq_zero.1 htie with h1 | h1
    · linarith
    · exact h1
  by_cases hpr : ⟪a - d, c - d⟫ = 0
  · exact Or.inr ⟨hpq, hqr, hpr⟩
  · exact Or.inl (k19_u3_tie_cells hdet hc' hb' ha' hβ1 hβ6 hγ6 hγ61 hs hpq hqr hpr)

end C2
end Type08Sp
end Minimality
