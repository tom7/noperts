module

public import Minimality.Type08S.C2K17GC1
public import Minimality.Type08S.C2K18A

@[expose] public section


/-!
# K18 / E: the S1.5 tie `⟪a-d,a-c'⟫ = 0` (Pa(3), `α4 = β1 = 1`) by the two-cell tie lemma (L7)

Frame `(P,Q,R) = (c-d, a-d, d-b)` of `k17gc_s15_cells`.  On the tie `pq = 0` the depths at `d - b` tie `a = d` and
`c = b'` (`b' - c = a - d`), both broken by the same functional `m·v = w(a) - w(d) = v1 ⟪P,Q⟫ + v2 ⟪Q,Q⟫`.
The hexagon (S1.5a, cone `v1 > 0 > v2`) needs `m > 0`, the pentagon (S1.5b, cone `v1, v2 > 0`) needs `m < 0`;
the cones share the ray `ρ = (1,0)` and `m·ρ = ⟪c-d,a-d⟫ = pr`.  So `pr ≠ 0` gives a cell (`k18_tie_two`),
leftover `pq = pr = 0`.  Numerics (K18 census L7, 1,200 exact Gram samples): `pr > 0` ⟹ hexagon, `pr < 0` ⟹ pentagon,
612 + 588, no exception.
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

theorem k18_cone2 {a b v1 v2 : ℝ} {m : ℝ × ℝ} (h : k18Cone (m :: [(a, b)]) v1 v2) :
    0 < m.1 * v1 + m.2 * v2 ∧ 0 < a * v1 + b * v2 := by
  constructor
  · exact h m List.mem_cons_self
  · exact h (a, b) (by simp)

theorem k18_cone3 {a b a' b' v1 v2 : ℝ} {m : ℝ × ℝ} (h : k18Cone (m :: [(a, b), (a', b')]) v1 v2) :
    0 < m.1 * v1 + m.2 * v2 ∧ 0 < a * v1 + b * v2 ∧ 0 < a' * v1 + b' * v2 := by
  refine ⟨h m List.mem_cons_self, h (a, b) (by simp), h (a', b') (by simp)⟩

set_option maxHeartbeats 6400000 in
/-- **S1.5 on the tie** `pq = 0` with `pr ≠ 0`: hexagon or pentagon at `d - b` by the tilt side. -/
theorem k18_s15_tie_cells {a a' b b' c c' d : ℝ³} {β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ ≠ 0) :
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
  have Eb' : fpoint P Q R d (1, 1, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (0, 1, -1) = c' := by rw [k17gc_fp, hc', hQ, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17gc_r0 hΔ)
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hPQ : ⟪P, Q⟫ ≠ 0 := by rw [hP, hQ, real_inner_comm]; exact hpr
  set m : ℝ × ℝ := (⟪P, Q⟫, ⟪Q, Q⟫) with hm
  -- cell 1: hexagon (S1.5a), cone v1 > 0, v2 < 0, needs m·v > 0
  have C1 : K18Cell (V8 a a' b b' c c' d) P Q R d (k18Cone (m :: [(1, 0), (0, -1)])) := by
    refine k18Cell_of (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k17gcHex5 β6 γ6)
      (k17gcHex5_inj hβ6 hγ6) ?_ _ ?_ ?_ ?_
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k17gcHex5, pc6_0, Ea]; simp [V8]
      · simp only [k17gcHex5, pc6_1, Ed]; simp [V8]
      · simp only [k17gcHex5, pc6_2, Eb]; simp [V8]
      · simp only [k17gcHex5, pc6_3, Ea']; simp [V8]
      · simp only [k17gcHex5, pc6_4, Ec]; simp [V8]
      · simp only [k17gcHex5, pc6_5, Eb']; simp [V8]
    · intro v1 v2 hC D hD
      obtain ⟨-, h1, h2⟩ := k18_cone3 hC
      exact (k17gc_hex5_tsc hD hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
          y = fpoint P Q R d (γ6, 0, -β6) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, 1, 0) ∨
          y = fpoint P Q R d (0, 1, -1) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k17gcHex5, pc6_0])).elim
      · exact (hyx 1 (by simp only [k17gcHex5, pc6_1])).elim
      · exact (hyx 2 (by simp only [k17gcHex5, pc6_2])).elim
      · exact (hyx 3 (by simp only [k17gcHex5, pc6_3])).elim
      · exact (hyx 4 (by simp only [k17gcHex5, pc6_4])).elim
      · exact (hyx 5 (by simp only [k17gcHex5, pc6_5])).elim
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        obtain ⟨-, h1, h2⟩ := k18_cone3 hC
        exact (k17gc_hex5_tsc hD hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).2 i
    · intro v1 v2 hC hw
      obtain ⟨hm0, -, -⟩ := k18_cone3 hC
      simp only [hm] at hm0
      refine k17gc_lexUni6_a _ _ hw ?_ ?_ ?_ ?_
      · right
        refine ⟨by simp only [k17gcHex5, pc6_0, pc6_1, hz, hQR]; ring, ?_⟩
        simp only [k17gcHex5, pc6_0, pc6_1, hwx]; nlinarith
      · left; simp only [k17gcHex5, pc6_1, pc6_2, hz, hQR]; nlinarith
      · right
        refine ⟨by simp only [k17gcHex5, pc6_4, pc6_5, hz, hQR]; ring, ?_⟩
        simp only [k17gcHex5, pc6_4, pc6_5, hwx]; nlinarith
      · simp only [k17gcHex5, pc6_2, pc6_3, pc6_4, hz, LexLt]
        by_contra hh
        push Not at hh
        obtain ⟨⟨h2, -⟩, ⟨h4, -⟩⟩ := hh
        nlinarith [mul_le_mul_of_nonneg_left h4 hγ6.le, mul_le_mul_of_nonneg_left h2 (sub_pos.2 hγ61).le,
          mul_pos (sub_pos.2 hs) hRR]
  -- cell 2: pentagon (S1.5b), cone v1 > 0, v2 > 0, needs m·v < 0
  have C2 : K18Cell (V8 a a' b b' c c' d) P Q R d (k18Cone ((-m.1, -m.2) :: [(1, 0), (0, 1)])) := by
    refine k18Cell_of (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) k17gcPent5
      k17gcPent5_inj ?_ _ ?_ ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17gcPent5, pc5_0, Ec]; simp [V8]
      · simp only [k17gcPent5, pc5_1, Eb']; simp [V8]
      · simp only [k17gcPent5, pc5_2, Ec']; simp [V8]
      · simp only [k17gcPent5, pc5_3, Ea]; simp [V8]
      · simp only [k17gcPent5, pc5_4, Ed]; simp [V8]
    · intro v1 v2 hC D hD
      obtain ⟨-, h1, h2⟩ := k18_cone3 hC
      exact (k17gc_pent5_tsc hD hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, 1, 0) ∨ y = fpoint P Q R d (0, 1, -1) ∨
          y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
          y = fpoint P Q R d (γ6, 0, -β6) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k17gcPent5, pc5_0])).elim
      · exact (hyx 1 (by simp only [k17gcPent5, pc5_1])).elim
      · exact (hyx 2 (by simp only [k17gcPent5, pc5_2])).elim
      · exact (hyx 3 (by simp only [k17gcPent5, pc5_3])).elim
      · exact (hyx 4 (by simp only [k17gcPent5, pc5_4])).elim
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        obtain ⟨-, h1, h2⟩ := k18_cone3 hC
        exact (k17gc_pent5_tsc hD hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).2.1 i
      · refine ⟨_, rfl, fun v1 v2 hC D hD i => ?_⟩
        obtain ⟨-, h1, h2⟩ := k18_cone3 hC
        exact (k17gc_pent5_tsc hD hβ6 hγ6 hγ61 hs (by linarith) (by linarith)).2.2 i
    · intro v1 v2 hC hw
      obtain ⟨hm0, -, -⟩ := k18_cone3 hC
      simp only [hm] at hm0
      refine lexUni5_top _ _ hw ?_ ?_ ?_
      · right
        refine ⟨by simp only [k17gcPent5, pc5_0, pc5_1, hz, hQR]; ring, ?_⟩
        simp only [k17gcPent5, pc5_0, pc5_1, hwx]; nlinarith
      · left; simp only [k17gcPent5, pc5_2, pc5_3, hz, hQR]; nlinarith
      · right
        refine ⟨by simp only [k17gcPent5, pc5_3, pc5_4, hz, hQR]; ring, ?_⟩
        simp only [k17gcPent5, pc5_3, pc5_4, hwx]; nlinarith
  refine ⟨R, k17gc_r0 hΔ, ?_⟩
  refine k18_tie_two C1 C2 (ρ1 := 1) (ρ2 := 0) (δ1 := 0) (δ2 := -1) (ε1 := 0) (ε2 := 1) ?_ ?_ ?_
  · intro l hl
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; norm_num
    · right; norm_num
  · intro l hl
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; norm_num
    · right; norm_num
  · simp only [hm]; simpa using hPQ

/-- **S1.5 tie** (`K14LeftPa` 3rd disjunct, `β1 = 1` branch, on `⟪a-d,a-c'⟫ = 0`): a cell unless also
`⟪a-d,c-d⟫ = 0`. -/
theorem k18_s15_tie {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) (h0 : ⟪a - d, a - c'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ (⟪a - d, b - d⟫ = 0 ∧ ⟪a - d, c - d⟫ = 0) := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨β6, γ6, hdet, hc', hb', ha', hβ6, hγ6, hγ61, hs⟩ :=
    k17gc_pa3_frame W hT' hκ (k5z_far1 W hT' hnT) hα hβ
  have e : ⟪a - d, a - c'⟫ = -⟪a - d, b - d⟫ := by
    have : a - c' = -(b - d) := by rw [hc']; module
    rw [this, inner_neg_right]
  have hpq : ⟪a - d, b - d⟫ = 0 := by linarith
  by_cases hpr : ⟪a - d, c - d⟫ = 0
  · exact Or.inr ⟨hpq, hpr⟩
  · exact Or.inl (k18_s15_tie_cells hdet hc' hb' ha' hβ6 hγ6 hγ61 hs hpq hpr)

end C2
end Type08Sp
end Minimality
