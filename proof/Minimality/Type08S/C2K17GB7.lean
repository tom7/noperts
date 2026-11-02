module

public import Minimality.Type08S.C2K17GB6

@[expose] public section


/-!
# K17GB / GB7: S1.8b (TaC, `qr = pq = 0`, `ζ_{a-c'}(a,b') < 0`): quad `(a,b',a',c')` at `c' - b`, frame `(b-d, c-d, c'-b)`.
With `m = β1-1`, `κ = 1/α1`, `ρ = α4 κ` (planarity: `γ4 = 1 + ρ m`):
`a = (-mκ,0,κ)`, `b = (1,0,0)`, `c = (0,1,0)`, `c' = (1,0,1)`, `a' = (β6,1,0)`, `b' = (-ρm, 1+ρm, ρ)`.
Tilt cone `v2 > 0 ∧ v1 < (β6-1) v2`; tilt `(-1+λ, 1)`.  Depth: `z_{b'} < z_a < z_{c'}` (the first is the literal).
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

/-- ccw `a, c', a', b'`. -/
def k17gbY8b (m κ ρ β6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(-(m * κ), 0, κ), (1, 0, 1), (β6, 1, 0), (-(ρ * m), 1 + ρ * m, ρ)]

theorem k17gbY8b_0 {m κ ρ β6 : ℝ} : k17gbY8b m κ ρ β6 0 = (-(m * κ), 0, κ) := rfl
theorem k17gbY8b_1 {m κ ρ β6 : ℝ} : k17gbY8b m κ ρ β6 1 = (1, 0, 1) := rfl
theorem k17gbY8b_2 {m κ ρ β6 : ℝ} : k17gbY8b m κ ρ β6 2 = (β6, 1, 0) := rfl
theorem k17gbY8b_3 {m κ ρ β6 : ℝ} : k17gbY8b m κ ρ β6 3 = (-(ρ * m), 1 + ρ * m, ρ) := rfl

theorem k17gbY8b_inj {m κ ρ β6 : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hρ : 0 < ρ) (hβ6 : 1 < β6) :
    ∀ i j, k17gbY8b m κ ρ β6 i = k17gbY8b m κ ρ β6 j → i = j := by
  intro i j h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k17gbY8b_0, k17gbY8b_1, k17gbY8b_2, k17gbY8b_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; nlinarith [h.1, h.2.1, h.2.2, mul_pos hρ hm, mul_pos hm hκ]) | (exfalso; norm_num at h)

set_option maxHeartbeats 3200000 in
theorem k17gb_s18b_tsc {D m κ ρ β6 v1 v2 : ℝ} (hD : 0 < D) (hm : 0 < m) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hβ6 : 1 < β6) (hv2 : 0 < v2) (hc : v1 < (β6 - 1) * v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k17gbY8b m κ ρ β6 (i + 1) - k17gbY8b m κ ρ β6 i) (k17gbY8b m κ ρ β6 j - k17gbY8b m κ ρ β6 i)
        (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 0)], ∀ i : ZMod 4,
      TSc D (k17gbY8b m κ ρ β6 (i + 1) - k17gbY8b m κ ρ β6 i) (t - k17gbY8b m κ ρ β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add_one
  have hmk := mul_pos hm hκ
  have hrm := mul_pos hρ hm
  have k1 := hD
  have kmk := mul_pos hD hmk
  have krm := mul_pos hD hrm
  have kk := mul_pos hD hκ
  have kr := mul_pos hD hρ
  have km := mul_pos hD hm
  have kb6 := mul_pos hD (by linarith : (0:ℝ) < β6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have krmb := mul_pos (mul_pos hD hrm) (by linarith : (0:ℝ) < β6)
  have kbrm := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β6)) hrm
  have krmmk := mul_pos (mul_pos hD hrm) hmk
  have kv2 := mul_pos hD hv2
  have kv2k := mul_pos (mul_pos hD hv2) hκ
  have kv2mk := mul_pos (mul_pos hD hv2) hmk
  have kc := mul_pos hD (sub_pos.2 hc)
  constructor
  · intro i j h1 h2'
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gbY8b_0, k17gbY8b_1, k17gbY8b_2, k17gbY8b_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gbY8b_0, k17gbY8b_1, k17gbY8b_2, k17gbY8b_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

/-- 4-cycle `(a,c',a',b')`: `z_a < z_{c'}` and `z_{b'} < z_a`. -/
theorem k17gb_lex4c (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : z 0 < z 1) (h30 : z 3 < z 0) : LexUni z w := by
  refine k17gb_uni4 z w hinj (fun key hk => ?_)
  have k01 : key 0 < key 1 := (hk 0 1).1 (Or.inl h01)
  have k30 : key 3 < key 0 := (hk 3 0).1 (Or.inl h30)
  constructor
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    linarith [h.1.1]
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    linarith [h.1.2]

set_option maxHeartbeats 6400000 in
/-- **S1.8b cell**: `(a,b',a',c')` at `c' - b`, frame `(b-d, c-d, c'-b)`. -/
theorem k17gb_s18b_cell {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hα4 : 0 < α4)
    (hα41 : α4 < 1) (hγ4 : 1 < γ4) (hβ6 : 1 < β6) (hpl : α4 * (1 - β1) = α1 * (1 - γ4))
    (hqr : ⟪b - d, c - d⟫ = 0) (hpq : ⟪a - d, b - d⟫ = 0)
    (hL : γ4 * ⟪a - d, c - d⟫ - (1 - α4) * ⟪a - d, a - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m, hmdef⟩ : ∃ m, m = β1 - 1 := ⟨_, rfl⟩
  have hm : 0 < m := by linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = α1⁻¹ := ⟨_, rfl⟩
  have hκα : κ * α1 = 1 := by rw [hκdef]; exact inv_mul_cancel₀ (by linarith)
  have hκ : 0 < κ := by rw [hκdef]; exact inv_pos.2 (by linarith)
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = α4 * κ := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hα4 hκ
  have hγρ : γ4 = 1 + ρ * m := by
    rw [hρdef, hmdef]; linear_combination (-(γ4 - 1)) * hκα + κ * hpl
  have hαρ : α4 = ρ * α1 := by rw [hρdef]; linear_combination (-α4) * hκα
  have hRdef : c' - b = α1 • (a - d) + m • (b - d) := by rw [hc', hmdef]; module
  have hpq' : ⟪b - d, a - d⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have hΔ0 : det3 (b - d) (c - d) (c' - b) ≠ 0 := by
    have e : det3 (b - d) (c - d) (c' - b) = α1 * det3 (a - d) (b - d) (c - d) := by
      rw [hRdef]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (by linarith) hdet
  have hca : ⟪c', c' - b⟫ - ⟪a, c' - b⟫ = α1 * (α1 - 1) * ⟪a - d, a - d⟫ + β1 * m * ⟪b - d, b - d⟫ := by
    rw [← inner_sub_left, show c' - a = (α1 - 1) • (a - d) + β1 • (b - d) by rw [hc']; module, hRdef]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, hpq, hpq']
    rw [hmdef]; ring
  have hab : ⟪a, c' - b⟫ - ⟪b', c' - b⟫ = α1 * ((1 - α4) * ⟪a - d, a - d⟫ - γ4 * ⟪a - d, c - d⟫) := by
    have hqr' : ⟪c - d, b - d⟫ = 0 := by rw [real_inner_comm]; exact hqr
    rw [← inner_sub_left, show a - b' = (1 - α4) • (a - d) + (-γ4) • (c - d) by rw [hb']; module, hRdef]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, hpq, hpq', hqr, hqr']
    rw [real_inner_comm (c - d) (a - d)]
    ring
  have hpp : 0 < ⟪a - d, a - d⟫ := by
    apply real_inner_self_pos.2
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hqq : 0 < ⟪b - d, b - d⟫ := by
    apply real_inner_self_pos.2
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  set P := b - d with hP
  set Q := c - d with hQ
  set R := c' - b with hR
  have hΔ : det3 P Q R ≠ 0 := hΔ0
  have Ea : fpoint P Q R d (-(m * κ), 0, κ) = a := by
    rw [k17gb_fp, hRdef, hP]
    calc d + (-(m * κ)) • (b - d) + (0 : ℝ) • (c - d) + κ • (α1 • (a - d) + m • (b - d)) = d + (κ * α1) • (a - d) := by
          module
      _ = a := by rw [hκα, one_smul]; abel
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gb_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17gb_fp, hP]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17gb_fp, hQ]; module
  have Ea' : fpoint P Q R d (β6, 1, 0) = a' := by rw [k17gb_fp, ha', hP, hQ]; module
  have Ec' : fpoint P Q R d (1, 0, 1) = c' := by rw [k17gb_fp, hP, hR]; module
  have Eb' : fpoint P Q R d (-(ρ * m), 1 + ρ * m, ρ) = b' := by
    rw [k17gb_fp, hRdef, hP, hQ, hb', hγρ]
    calc d + (-(ρ * m)) • (b - d) + (1 + ρ * m) • (c - d) + ρ • (α1 • (a - d) + m • (b - d)) =
          d + (ρ * α1) • (a - d) + (1 + ρ * m) • (c - d) := by module
      _ = _ := by rw [← hαρ]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine ⟨R, k17gb_r0 hΔ, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 4) (by norm_num) (k17gbY8b m κ ρ β6)
    (k17gbY8b_inj hm hκ hρ hβ6) (u1 := -1) (u2 := 1) (t1 := 1) (t2 := 0) (by norm_num) ?_ ?_ ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k17gbY8b_0, Ea]; simp [V8]
    · simp only [k17gbY8b_1, Ec']; simp [V8]
    · simp only [k17gbY8b_2, Ea']; simp [V8]
    · simp only [k17gbY8b_3, Eb']; simp [V8]
  · intro lam h0 h1 D hD
    exact (k17gb_s18b_tsc hD hm hκ hρ hβ6 (by nlinarith) (by nlinarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (-(m * κ), 0, κ) ∨ y = fpoint P Q R d (1, 0, 1) ∨ y = fpoint P Q R d (β6, 1, 0) ∨
        y = fpoint P Q R d (-(ρ * m), 1 + ρ * m, ρ) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) := by
      rw [Ea, Ec', Ea', Eb', Eb, Ec, Ed]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gbY8b_0])).elim
    · exact (hyx 1 (by simp only [k17gbY8b_1])).elim
    · exact (hyx 2 (by simp only [k17gbY8b_2])).elim
    · exact (hyx 3 (by simp only [k17gbY8b_3])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s18b_tsc hD hm hκ hρ hβ6 (by nlinarith) (by nlinarith)).2 _ (by simp) i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s18b_tsc hD hm hκ hρ hβ6 (by nlinarith) (by nlinarith)).2 _ (by simp) i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17gb_s18b_tsc hD hm hκ hρ hβ6 (by nlinarith) (by nlinarith)).2 _ (by simp) i
  · intro w hw
    refine k17gb_lex4c _ w hw ?_ ?_
    · simp only [k17gbY8b_0, k17gbY8b_1, Ea, Ec']
      have := mul_pos (mul_pos (by linarith : (0:ℝ) < α1) (by linarith : (0:ℝ) < α1 - 1)) hpp
      have := mul_pos (mul_pos (by linarith : (0:ℝ) < β1) hm) hqq
      linarith
    · simp only [k17gbY8b_3, k17gbY8b_0, Eb', Ea]
      have := mul_pos (by linarith : (0:ℝ) < α1) (neg_pos.2 hL)
      nlinarith

/-- **S1.8b**: `K14TaC` (with `¬ T'`), `⟪a-d,b-d⟫ = 0`: a lex cell unless `ζ_{a-c'}(a,b') ≥ 0`. -/
theorem k17gb_s18b {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K14TaC a a' b b' c c' d) (hpq : ⟪a - d, b - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ 0 ≤ ⟪a - b', a - c'⟫ := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hα4, hα41, hγ4, hβ6, hpl, hqr, hL⟩ :=
    k17gb_tac_frame W hT' h hpq
  by_cases hle : 0 ≤ ⟪a - b', a - c'⟫
  · exact Or.inr hle
  · push Not at hle
    left
    refine k17gb_s18b_cell hdet hc' hb' ha' hα1 hβ1 hα4 hα41 hγ4 hβ6 hpl hqr hpq ?_
    rw [hL] at hle
    by_contra hh; push Not at hh
    have h1 : 0 < α1 - 1 := by linarith
    nlinarith [mul_nonneg h1.le hh]

end C2
end Type08Sp
end Minimality
