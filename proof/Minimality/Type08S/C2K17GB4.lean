module

public import Minimality.Type08S.C2K17GB3

@[expose] public section


/-!
# K17GB / GB4: S1.4b (A41, `ζ(d,b) = 0`, `β6 = 1`, `ζ_{a-c'}(a,b') < 0 ⟺ pr < 0`): quad `(c',b',a',b)` at `d - b`,
frame `(a-d, c-d, d-b)`, tilt `(-1, -λ η)`, `η <= γ4 - 1`, `2 η rr' < -pr`.
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

open Classical in
theorem k17gb_uni4 (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hP : ∀ key : ZMod 4 → ℝ, (∀ i j, LexLt (z i, w i) (z j, w j) ↔ key i < key j) →
      ¬ (max (key 1) (key 3) < min (key 0) (key 2)) ∧ ¬ (max (key 0) (key 2) < min (key 1) (key 3))) :
    LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  obtain ⟨h1, h2⟩ := hP (fun i => M * z i + w i) hM
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  refine lexUni_four (fun _ => (0 : ℝ)) (fun i => M * z i + w i) (fun _ _ => rfl) ?_ h1 h2
  intro i j hij h
  apply hij
  by_contra hne
  have hne' : (z i, w i) ≠ (z j, w j) := fun h' =>
    hne (hinj i j (congrArg Prod.fst h') (congrArg Prod.snd h'))
  rcases lexLt_total hne' with h1 | h1
  · have := (hM i j).1 h1; linarith
  · have := (hM j i).1 h1; linarith

/-- 4-cycle `(c',b',a',b)` with `a' > b` (lex) and `c' < b'` or `a' < b'` (in `z`). -/
theorem k17gb_lex4b (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hab : LexLt (z 3, w 3) (z 2, w 2)) (hc : z 0 < z 1 ∨ z 2 < z 1) : LexUni z w := by
  refine k17gb_uni4 z w hinj (fun key hk => ?_)
  have k32 := (hk _ _).1 hab
  have hlt : key 0 < key 1 ∨ key 2 < key 1 := by
    rcases hc with h | h
    · exact Or.inl ((hk 0 1).1 (Or.inl h))
    · exact Or.inr ((hk 2 1).1 (Or.inl h))
  constructor
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    rcases hlt with h' | h' <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    linarith [h.1.2, h.2.2]

def k17gbY4b (α1 β1 γ4 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(α1, 0, -β1), (1, γ4, 0), (0, 1, -1), (0, 0, -1)]

theorem k17gbY4b_0 {α1 β1 γ4 : ℝ} : k17gbY4b α1 β1 γ4 0 = (α1, 0, -β1) := rfl
theorem k17gbY4b_1 {α1 β1 γ4 : ℝ} : k17gbY4b α1 β1 γ4 1 = (1, γ4, 0) := rfl
theorem k17gbY4b_2 {α1 β1 γ4 : ℝ} : k17gbY4b α1 β1 γ4 2 = (0, 1, -1) := rfl
theorem k17gbY4b_3 {α1 β1 γ4 : ℝ} : k17gbY4b α1 β1 γ4 3 = (0, 0, -1) := rfl

theorem k17gbY4b_inj {α1 β1 γ4 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 1 < γ4) :
    ∀ i j, k17gbY4b α1 β1 γ4 i = k17gbY4b α1 β1 γ4 j → i = j := by
  intro i j h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k17gbY4b_0, k17gbY4b_1, k17gbY4b_2, k17gbY4b_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
theorem k17gb_s14b_tsc {D α1 β1 γ4 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 1 < γ4)
    (hv1 : v1 < 0) (hv2 : v2 < 0) (hc : -v2 < (γ4 - 1) * (-v1)) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k17gbY4b α1 β1 γ4 (i + 1) - k17gbY4b α1 β1 γ4 i) (k17gbY4b α1 β1 γ4 j - k17gbY4b α1 β1 γ4 i)
        (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 0)], ∀ i : ZMod 4,
      TSc D (k17gbY4b α1 β1 γ4 (i + 1) - k17gbY4b α1 β1 γ4 i) (t - k17gbY4b α1 β1 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add_one
  have k1 := hD
  have ka := mul_pos hD (by linarith : (0:ℝ) < α1)
  have ka1 := mul_pos hD (sub_pos.2 hα1)
  have kg := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kg1 := mul_pos hD (sub_pos.2 hγ4)
  have kag := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < γ4)
  have ka1g := mul_pos (mul_pos hD (sub_pos.2 hα1)) (by linarith : (0:ℝ) < γ4)
  have kg1a1 := mul_pos (mul_pos hD (sub_pos.2 hγ4)) (sub_pos.2 hα1)
  have knv1 := mul_pos hD (neg_pos.2 hv1)
  have knv2 := mul_pos hD (neg_pos.2 hv2)
  have kanv2 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (neg_pos.2 hv2)
  have kbnv2 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv2)
  have kc := mul_pos hD (sub_pos.2 hc)
  constructor
  · intro i j h1 h2'
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gbY4b_0, k17gbY4b_1, k17gbY4b_2, k17gbY4b_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gbY4b_0, k17gbY4b_1, k17gbY4b_2, k17gbY4b_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 6400000 in
/-- **S1.4b cell**: `(c',b',a',b)` at `d - b`, frame `(a-d, c-d, d-b)`, tilt `(-1, -λ η)`. -/
theorem k17gb_s14b_cell {a a' b b' c c' d : ℝ³} {α1 β1 γ4 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hγ4 : 1 < γ4)
    (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := c - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by
      simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h]
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17gb_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gb_fp]; module
  have Eb : fpoint P Q R d (0, 0, -1) = b := by rw [k17gb_fp, hR]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17gb_fp, hQ]; module
  have Ea' : fpoint P Q R d (0, 1, -1) = a' := by rw [k17gb_fp, ha', hR, hQ]; module
  have Eb' : fpoint P Q R d (1, γ4, 0) = b' := by rw [k17gb_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (α1, 0, -β1) = c' := by rw [k17gb_fp, hc', hP, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm, hqr, neg_zero]
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17gb_r0 hΔ)
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hPQ : ⟪P, Q⟫ < 0 := hpr
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  obtain ⟨η0, hη0, hη0x⟩ := k8_eta (x := ⟪Q, Q⟫) (y := ⟪P, Q⟫) hPQ.ne
  rw [abs_of_pos hQQ, abs_of_neg hPQ] at hη0x
  obtain ⟨η, hη, hηle, hηg, hηQ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ γ4 - 1 ∧ η ≤ η0 ∧ η * ⟪Q, Q⟫ < -⟪P, Q⟫ := by
    refine ⟨min η0 (γ4 - 1), lt_min hη0 (by linarith), min_le_right _ _, min_le_left _ _, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left η0 (γ4 - 1)) hQQ.le, mul_pos hη0 hQQ]
  refine ⟨R, k17gb_r0 hΔ, ?_⟩
  refine k8_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 4) (by norm_num) (k17gbY4b α1 β1 γ4)
    (k17gbY4b_inj hα1 (by linarith) hγ4) (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -η)
    (by nlinarith) ?_ ?_ ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k17gbY4b_0, Ec']; simp [V8]
    · simp only [k17gbY4b_1, Eb']; simp [V8]
    · simp only [k17gbY4b_2, Ea']; simp [V8]
    · simp only [k17gbY4b_3, Eb]; simp [V8]
  · intro lam h0 h1 D hD
    exact (k17gb_s14b_tsc hD hα1 (by linarith) hγ4 (by nlinarith) (by nlinarith [mul_pos h0 hη])
      (by nlinarith [mul_pos h0 hη])).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (α1, 0, -β1) ∨ y = fpoint P Q R d (1, γ4, 0) ∨ y = fpoint P Q R d (0, 1, -1) ∨
        y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (0, 0, 0) := by
      rw [Ec', Eb', Ea', Eb, Ea, Ec, Ed]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gbY4b_0])).elim
    · exact (hyx 1 (by simp only [k17gbY4b_1])).elim
    · exact (hyx 2 (by simp only [k17gbY4b_2])).elim
    · exact (hyx 3 (by simp only [k17gbY4b_3])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s14b_tsc hD hα1 (by linarith) hγ4 (by nlinarith) (by nlinarith [mul_pos h0 hη])
        (by nlinarith [mul_pos h0 hη])).2 _ (by simp) i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s14b_tsc hD hα1 (by linarith) hγ4 (by nlinarith) (by nlinarith [mul_pos h0 hη])
        (by nlinarith [mul_pos h0 hη])).2 _ (by simp) i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s14b_tsc hD hα1 (by linarith) hγ4 (by nlinarith) (by nlinarith [mul_pos h0 hη])
        (by nlinarith [mul_pos h0 hη])).2 _ (by simp) i
  · intro lam h0 h1 w hw hinj
    refine k17gb_lex4b _ w hinj ?_ ?_
    · right
      refine ⟨?_, ?_⟩
      · simp only [k17gbY4b_2, k17gbY4b_3, hz, hQR]; ring
      · rw [hw, hw]
        simp only [k17gbY4b_2, k17gbY4b_3, hwx, hQR]
        nlinarith [mul_pos h0 hη, mul_pos (mul_pos h0 hη) hQQ, mul_pos (sub_pos.2 h1) (mul_pos hη hQQ)]
    · by_cases hX : ⟪P, R⟫ ≤ 0
      · left
        simp only [k17gbY4b_0, k17gbY4b_1, hz, hQR]
        nlinarith [mul_nonneg (sub_nonneg.2 hα1.le) (neg_nonneg.2 hX), mul_pos (by linarith : (0:ℝ) < β1) hRR]
      · push Not at hX
        right
        simp only [k17gbY4b_1, k17gbY4b_2, hz, hQR]
        nlinarith

/-- **S1.4b**: `K6tTaA41` (with `¬ T'`), `ζ(d,b) = 0`, `β6 = 1`: a lex cell unless `ζ_{a-c'}(a,b') ≥ 0`. -/
theorem k17gb_s14b {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K6tTaA41 a a' b b' c c' d) (hz : ⟪d - b, a - b'⟫ = 0)
    (hβ6 : det3 (a' - b) (c - d) (a - d) = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ 0 ≤ ⟪a - b', a - c'⟫ := by
  obtain ⟨α1, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hγ4, hβ6', hqr, hL⟩ :=
    k17gb_a41_frame W hT' h hz
  have h61 := k17gb_b61 hdet ha' hβ6
  subst h61
  by_cases hle : 0 ≤ ⟪a - b', a - c'⟫
  · exact Or.inr hle
  · push Not at hle
    left
    have hpr : ⟪a - d, c - d⟫ < 0 := by
      rw [hL] at hle
      by_contra hh; push Not at hh
      have : 0 < γ4 * (α1 - 1) := mul_pos (by linarith) (by linarith)
      nlinarith
    exact k17gb_s14b_cell hdet hc' hb' ha' hα1 hβ1 hγ4 hqr hpr

end C2
end Type08Sp
end Minimality
