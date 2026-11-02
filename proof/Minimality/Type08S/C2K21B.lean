module

public import Minimality.Type08S.C2K21A

@[expose] public section


/-!
# K21 / B: Pa closed

* `k21_qd_tsc_tie`, `k21_u1l_ad_tie`: U1 at `α4 < 1`, `β1 > 1`, `a'` ON the screen line `c'b'` at the view `a - d`
  (`β1γ4 - β1γ6 - β6γ4 = 0`): the quadrilateral `(a,c',a',b')` of `k19_u1l_ad` still works on the whole cone
  `v1, v2 > 0`; the two tied tests (edge `c'a'` vs `b'`, edge `a'b'` vs `c'`) are decided by the tilt
  (`v1 (γ4 - (1-α4)γ6) + v2 (β1 - (1-α4)(β1-β6)) > 0`).
* `k21_pa_u1`: `K20LeftPa`'s collinear disjunct (`det3 (c'-a') (b'-a') (a-d) = 0`, `β1 ≠ 1`): a lex cell.
* `k21_pa_close`: every `K20LeftPa` point has a lex cell or is Rupert.
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

set_option maxHeartbeats 3200000 in
theorem k21_qd_tsc_tie {D α4 β1 γ4 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ1 : 1 < β1)
    (hγ4 : 1 < γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (htie : β1 * γ6 + β6 * γ4 - β1 * γ4 = 0)
    (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k19Qd α4 β1 γ4 β6 γ6 (i + 1) - k19Qd α4 β1 γ4 β6 γ6 i)
        (k19Qd α4 β1 γ4 β6 γ6 j - k19Qd α4 β1 γ4 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc D (k19Qd α4 β1 γ4 β6 γ6 (i + 1) - k19Qd α4 β1 γ4 β6 γ6 i) (t - k19Qd α4 β1 γ4 β6 γ6 i)
        (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, -, -, -, -⟩ := k19_z4
  have hb6 : β6 < β1 := by nlinarith
  have hc : 0 < β1 * γ6 + β6 - β1 := by nlinarith
  have hb : 0 < γ4 * (β6 - 1) + γ6 := by nlinarith
  have hA : 0 < γ4 - (1 - α4) * γ6 := by nlinarith
  have hB : 0 < β1 - (1 - α4) * (β1 - β6) := by nlinarith
  have k1 := hD
  have kb := mul_pos hD (by linarith : (0:ℝ) < β1)
  have kg := mul_pos hD (by linarith : (0:ℝ) < γ4)
  have kbg := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) (by linarith : (0:ℝ) < γ4)
  have kbg6 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) hγ6
  have kb6g := mul_pos (mul_pos hD hβ6) (by linarith : (0:ℝ) < γ4)
  have kc := mul_pos hD hc
  have khb := mul_pos hD hb
  have kg61 := mul_pos (mul_pos hD hγ6) (sub_pos.2 hβ1)
  have kb6g1 := mul_pos (mul_pos hD hβ6) (sub_pos.2 hγ4)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kbv2 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) hv2
  have kgv1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < γ4)) hv1
  have kagv1 := mul_pos (mul_pos (mul_pos hD hα4) (by linarith : (0:ℝ) < β1)) hv1
  have kA := mul_pos (mul_pos hD hA) hv1
  have kB := mul_pos (mul_pos hD hB) hv2
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
         | (right; refine ⟨?_, ?_⟩
            · first | ring1 | linear_combination D * htie | linear_combination -D * htie
            · nlinarith))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, s0, s1, s2, s3, k19Qd_0, k19Qd_1, k19Qd_2, k19Qd_3, Prod.fst_sub, Prod.snd_sub,
          Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 12800000 in
/-- `β1 > 1`, `a'` on the screen line `c'b'`: the quadrilateral `(a,c',a',b')` at `a - d`. -/
theorem k21_u1l_ad_tie {a a' b b' c c' d : ℝ³} {α4 β1 γ4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ1 : 1 < β1)
    (hγ : γ4 = 1 - α4 + α4 * β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0)
    (htie : β1 * γ6 + β6 * γ4 - β1 * γ4 = 0) : HasLexCell (V8 a a' b b' c c' d) := by
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
    exact (k21_qd_tsc_tie hD hα4 hα41 hβ1 hγ4 hβ6 hγ6 hγ61 htie (by linarith) (by linarith)).1
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
      exact (k21_qd_tsc_tie hD hα4 hα41 hβ1 hγ4 hβ6 hγ6 hγ61 htie (by linarith) (by linarith)).2
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

/-- `K20LeftPa`'s collinear disjunct at `β1 ≠ 1`: a lex cell. -/
theorem k21_pa_u1 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fLeftPa a a' b b' c c' d)
    (hpr : ⟪a - d, c - d⟫ = 0) (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ : det3 (a - d) (c' - b) (c - d) ≠ 0) (hcol : det3 (c' - a') (b' - a') (a - d) = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hctx, hL⟩ := h
  obtain ⟨hT', hnT, hκ, -⟩ := id hctx
  have hfar := k5z_far1 W hT' hnT
  -- `h1, h2` of U1 in every branch of `K14LeftPa`
  have hU : ⟪a - c, d - b⟫ = 0 ∧ ⟪a - d, d - b⟫ = 0 := by
    obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, -, -, -, -, -⟩ := norm08w_coordsTp W hT'
    have hg4 : α4 * (1 - β1) = 1 * (1 - γ4) := (planar_a_iff hdet hc' hb').1 hκ
    have hb1 : β1 ≠ 1 := by
      intro e; apply hβ; rw [det_beta1 hc', e, sub_self, zero_mul]
    have e2 : d - b = -(b - d) := by abel
    rcases hL with ⟨h1, h2, -⟩ | ⟨h0, -, -, hβ' | hpq⟩ | ⟨hα0, -⟩
    · exact ⟨h1, h2⟩
    · exact absurd ((mul_eq_zero.1 hβ').resolve_right hdet) hβ
    · have hpq' : ⟪a - d, b - d⟫ = 0 := by rw [e2, inner_neg_right] at hpq; linarith
      have hqr : ⟪b - d, c - d⟫ = 0 := by
        have e : b' - c = α4 • (a - d) + (γ4 - 1) • (c - d) := by rw [hb']; module
        rw [e, e2, inner_neg_right, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_comm (b - d) (c - d), hpq'] at h0
        have hne : γ4 - 1 ≠ 0 := by
          intro e; apply hb1
          have : α4 * (1 - β1) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · linarith
          · linarith
        have : (γ4 - 1) * ⟪b - d, c - d⟫ = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      refine ⟨?_, hpq⟩
      have e : a - c = (a - d) - (c - d) := by abel
      rw [e, e2, inner_neg_right, inner_sub_left, hpq', real_inner_comm (b - d) (c - d), hqr]; ring
    · rw [hα0, zero_mul] at hα; exact absurd hα (lt_irrefl 0)
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hα41, hβ1, hγ, hβ6, hγ6, hγ61, hs, hpq, hqr⟩ :=
    k19_u1l_frame W hT' hκ hfar hU.1 hU.2 hα
  rcases lt_trichotomy β1 1 with hl | he | hg
  · exact k19_u1l_hex hdet hc' hb' ha' hα4 hα41 hβ1 hl hγ hβ6 hγ6 hγ61 hs hpq hqr hpr
  · exact absurd (by rw [det_beta1 hc', he, sub_self, zero_mul]) hβ
  · have e : det3 (c' - a') (b' - a') (a - d) =
        (β1 * γ4 - β1 * γ6 - β6 * γ4) * det3 (a - d) (b - d) (c - d) := by
      rw [hc', hb', ha']
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e] at hcol
    have ht := (mul_eq_zero.1 hcol).resolve_right hdet
    exact k21_u1l_ad_tie hdet hc' hb' ha' hα4 hα41 hg hγ hβ6 hγ6 hγ61 hpq hqr hpr (by linarith)

/-- **Pa closed**: `K20LeftPa` has a lex cell or is Rupert. -/
theorem k21_pa_close {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K20LeftPa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨hL, hd⟩ := h
  have hb1 : ∀ _ : ⟪a - d, c - d⟫ = 0,
      det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 →
      HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) := by
    intro hpr hβ
    rcases k21_pa_pq W hL hβ with h3 | hpq
    · exact Or.inl h3
    · exact Or.inr (k21_pa_prism W hL.1 hβ hpq hpr)
  rcases hd with ⟨hpr, -, hβ⟩ | ⟨hpr, hα, hβ | hcol⟩ | ⟨hpr, -, hβ, -⟩
  · exact hb1 hpr (by rw [hβ, zero_mul])
  · exact hb1 hpr (by rw [hβ, zero_mul])
  · by_cases hβ : det3 (a - d) (c' - b) (c - d) = 0
    · exact hb1 hpr (by rw [hβ, zero_mul])
    · exact Or.inl (k21_pa_u1 W hL hpr hα hβ hcol)
  · exact hb1 hpr hβ

end C2
end Type08Sp
end Minimality
