module

public import Minimality.Type08S.C2K21B

@[expose] public section


/-!
# K21 / C: Ta closed

* `k21_s13_pent`: the S1.3 tie (`K17hTaA41` with `⟪a-d,a-c'⟫ = 0`, `β6 > 1`): `qr = pr = 0`, so the view `d - c`
  (`∥ a - b'`) sees the base plane `(d,a,b,c')` as a top plateau.  Pentagon `(a',c,b',a,c')` (frame `(a-d, b-d, d-c)`,
  coords `a' (0,β6,-1)`, `c (0,0,-1)`, `b' (1,0,-γ4)`, `a (1,0,0)`, `c' (α1,β1,0)`), cone `v1, v2 < 0`,
  `-β1 v1 + (α1-1) v2 > 0`, `⟪P,Q⟫ v1 + ⟪Q,Q⟫ v2 > 0` (ray `(-1,0)`, `δ = (0,-1)`; `⟪P,Q⟫ < 0` from the tie).  Peak `a`:
  `w(a) - w(c') = v2 ((1-α1)⟪P,Q⟫ - β1⟪Q,Q⟫) > 0` by strict Cauchy-Schwarz; `w(a') - w(c) = β6 (⟪P,Q⟫ v1 + ⟪Q,Q⟫ v2)`.
  Numerics (gsec, K17F taa41z data, ties ζ(d,b), ⟪a-b',a-c'⟫, ⟪a-d,a-c'⟫): this cell 1187/1187.
* `k21_ta_close`: `K20LeftTa` has a lex cell or is Rupert (B11: `k21_b11`; `β6 = 1`: `k20_s14`).
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

def k21Pent (α1 β1 γ4 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, β6, -1), (0, 0, -1), (1, 0, -γ4), (1, 0, 0), (α1, β1, 0)]

theorem k21Pent_0 : k21Pent α1 β1 γ4 β6 0 = (0, β6, -1) := rfl
theorem k21Pent_1 : k21Pent α1 β1 γ4 β6 1 = (0, 0, -1) := rfl
theorem k21Pent_2 : k21Pent α1 β1 γ4 β6 2 = (1, 0, -γ4) := rfl
theorem k21Pent_3 : k21Pent α1 β1 γ4 β6 3 = (1, 0, 0) := rfl
theorem k21Pent_4 : k21Pent α1 β1 γ4 β6 4 = (α1, β1, 0) := rfl

theorem k21Pent_inj {α1 β1 γ4 β6 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 0 < β6) :
    ∀ i j, k21Pent α1 β1 γ4 β6 i = k21Pent α1 β1 γ4 β6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k21Pent_0, k21Pent_1, k21Pent_2, k21Pent_3, k21Pent_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith) | (exfalso; norm_num at h)

set_option maxHeartbeats 6400000 in
theorem k21_pent_tsc {D α1 β1 γ4 β6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hγ4 : 0 < γ4)
    (hβ6 : 1 < β6) (hv1 : v1 < 0) (hv2 : v2 < 0) (hc : 0 < -β1 * v1 + (α1 - 1) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k21Pent α1 β1 γ4 β6 (i + 1) - k21Pent α1 β1 γ4 β6 i)
        (k21Pent α1 β1 γ4 β6 j - k21Pent α1 β1 γ4 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
      TSc D (k21Pent α1 β1 γ4 β6 (i + 1) - k21Pent α1 β1 γ4 β6 i) (t - k21Pent α1 β1 γ4 β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have n1 : 0 < -v1 := by linarith
  have n2 : 0 < -v2 := by linarith
  have k1 := hD
  have kb6 := mul_pos hD (by linarith : (0:ℝ) < β6)
  have kb1 := mul_pos hD hβ1
  have ka1b6 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β6)
  have ka1b6' := mul_pos (mul_pos hD (sub_pos.2 hα1)) (by linarith : (0:ℝ) < β6)
  have ka1 := mul_pos hD (sub_pos.2 hα1)
  have ka1b61 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (sub_pos.2 hβ6)
  have ka1b1 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) hβ1
  have kv1 := mul_pos hD n1
  have kv2 := mul_pos hD n2
  have kb6v1 := mul_pos kb6 n1
  have kgv2 := mul_pos (mul_pos hD hγ4) n2
  have kgv1 := mul_pos (mul_pos hD hγ4) n1
  have kgb6v1 := mul_pos (mul_pos (mul_pos hD hγ4) (by linarith : (0:ℝ) < β6)) n1
  have kgc := mul_pos (mul_pos hD hγ4) hc
  have kc := mul_pos hD hc
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, s0, s1, s2, s3, s4, k21Pent_0, k21Pent_1, k21Pent_2, k21Pent_3, k21Pent_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨?_, ?_⟩
            · ring1
            · nlinarith))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, s0, s1, s2, s3, s4, k21Pent_0, k21Pent_1, k21Pent_2, k21Pent_3, k21Pent_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨?_, ?_⟩
          · ring1
          · nlinarith))

set_option maxHeartbeats 12800000 in
/-- **S1.3 tie, `β6 > 1`**: the pentagon `(a',c,b',a,c')` at `d - c`. -/
theorem k21_s13_pent {a a' b b' c c' d : ℝ³} {α1 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hγ4 : 1 < γ4)
    (hβ6 : 1 < β6) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) (hL : ⟪a - d, a - c'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := b - d with hQ
  set R := d - c with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 P Q R := by simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h, neg_zero]
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17f_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (0, 1, 0) = b := by rw [k17f_fp, hQ]; module
  have Ec : fpoint P Q R d (0, 0, -1) = c := by rw [k17f_fp, hR]; module
  have Ea' : fpoint P Q R d (0, β6, -1) = a' := by rw [k17f_fp, ha', hR]; module
  have Eb' : fpoint P Q R d (1, 0, -γ4) = b' := by rw [k17f_fp, hb', hR]; module
  have Ec' : fpoint P Q R d (α1, β1, 0) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hR, ← neg_sub c d, inner_neg_right, hpr, neg_zero]
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hR, ← neg_sub c d, inner_neg_right, hqr, neg_zero]
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPP : 0 < ⟪P, P⟫ := real_inner_self_pos.2 hP0
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  -- the tie: `(1-α1) PP = β1 PQ`
  have hL' : (1 - α1) * ⟪P, P⟫ - β1 * ⟪P, Q⟫ = 0 := by
    have e : a - c' = (1 - α1) • P - β1 • Q := by rw [hc']; simp only [hP, hQ]; module
    rw [e, inner_sub_right, real_inner_smul_right, real_inner_smul_right] at hL; linarith
  have hPQ : ⟪P, Q⟫ < 0 := by nlinarith [mul_pos (sub_pos.2 hα1) hPP]
  have hcs : ⟪P, Q⟫ ^ 2 < ⟪Q, Q⟫ * ⟪P, P⟫ := by
    refine k18_cs_strict P Q hQ0 (fun t ht => hΔ ?_)
    have : P = t • Q := sub_eq_zero.1 ht
    rw [this]; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  have hkey : (1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, Q⟫ < 0 := by
    by_contra hh; push Not at hh
    have h1 : 0 ≤ ⟪P, P⟫ * ((1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, Q⟫) := mul_nonneg hPP.le hh
    have h2 : ⟪P, P⟫ * ((1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, Q⟫) = β1 * (⟪P, Q⟫ ^ 2 - ⟪Q, Q⟫ * ⟪P, P⟫) := by
      have : (1 - α1) * ⟪P, P⟫ = β1 * ⟪P, Q⟫ := by linarith
      linear_combination ⟪P, Q⟫ * this
    rw [h2] at h1
    nlinarith [mul_pos (by linarith : (0:ℝ) < β1) (sub_pos.2 hcs)]
  refine ⟨R, hR0, ?_⟩
  refine k18_cone_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k21Pent α1 β1 γ4 β6)
    (k21Pent_inj (by linarith) (by linarith) (by linarith)) ?_
    [(-1, 0), (0, -1), (-β1, α1 - 1), (⟪P, Q⟫, ⟪Q, Q⟫)] (by simp) ?_ ?_ ?_
    (ρ1 := -1) (ρ2 := 0) (δ1 := 0) (δ2 := -1) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k21Pent_0, Ea']; simp [V8]
    · rw [k21Pent_1, Ec]; simp [V8]
    · rw [k21Pent_2, Eb']; simp [V8]
    · rw [k21Pent_3, Ea]; simp [V8]
    · rw [k21Pent_4, Ec']; simp [V8]
  · intro v1 v2 hC D hD
    have h1 := hC (-1, 0) (by simp)
    have h2 := hC (0, -1) (by simp)
    have h3 := hC (-β1, α1 - 1) (by simp)
    simp only at h1 h2 h3
    exact (k21_pent_tsc hD hα1 (by linarith) (by linarith) hβ6 (by linarith) (by linarith) (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (0, β6, -1) ∨ y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (1, 0, -γ4) ∨
        y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (α1, β1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
        y = fpoint P Q R d (0, 1, 0) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(-1, 0), (0, -1), (-β1, α1 - 1), (⟪P, Q⟫, ⟪Q, Q⟫)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
          TSc D (k21Pent α1 β1 γ4 β6 (i + 1) - k21Pent α1 β1 γ4 β6 i) (t - k21Pent α1 β1 γ4 β6 i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h1 := hC (-1, 0) (by simp)
      have h2 := hC (0, -1) (by simp)
      have h3 := hC (-β1, α1 - 1) (by simp)
      simp only at h1 h2 h3
      exact (k21_pent_tsc hD hα1 (by linarith) (by linarith) hβ6 (by linarith) (by linarith) (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k21Pent_0])).elim
    · exact (hyx 1 (by rw [k21Pent_1])).elim
    · exact (hyx 2 (by rw [k21Pent_2])).elim
    · exact (hyx 3 (by rw [k21Pent_3])).elim
    · exact (hyx 4 (by rw [k21Pent_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
  · intro v1 v2 hC hw
    have h1 := hC (-1, 0) (by simp)
    have h2 := hC (0, -1) (by simp)
    have h4 := hC (⟪P, Q⟫, ⟪Q, Q⟫) (by simp)
    simp only at h1 h2 h4
    obtain ⟨m0, m1, m2, m3, m4, p0, p1, p2, p3, p4⟩ := k19_z5
    have hca : LexLt (⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 4), R⟫,
        ⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 4), fcomb P Q R v1 v2 0⟫)
        (⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 3), R⟫,
        ⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 3), fcomb P Q R v1 v2 0⟫) := by
      right
      refine ⟨by simp only [k21Pent_3, k21Pent_4, hz, hPR, hQR]; ring, ?_⟩
      simp only [k21Pent_3, k21Pent_4, hwx, hPR, hQR]
      nlinarith [mul_pos (by linarith : (0:ℝ) < -v2) (by linarith : (0:ℝ) < -((1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, Q⟫))]
    have hba : LexLt (⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 2), R⟫,
        ⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 2), fcomb P Q R v1 v2 0⟫)
        (⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 3), R⟫,
        ⟪fpoint P Q R d (k21Pent α1 β1 γ4 β6 3), fcomb P Q R v1 v2 0⟫) := by
      left; simp only [k21Pent_2, k21Pent_3, hz, hPR, hQR]; nlinarith [mul_pos (by linarith : (0:ℝ) < γ4) hRR]
    refine k19_lexUni_nb _ _ hw 3 ?_ ?_ ?_
    · rw [m3]; exact hba
    · rw [p3]; exact hca
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; rw [m0]; left; simp only [k21Pent_0, k21Pent_4, hz, hPR, hQR]; nlinarith
      · left; rw [m1]; right
        refine ⟨by simp only [k21Pent_0, k21Pent_1, hz, hPR, hQR]; ring, ?_⟩
        simp only [k21Pent_0, k21Pent_1, hwx, hPR, hQR]
        nlinarith [mul_pos (by linarith : (0:ℝ) < β6) h4]
      · right; rw [p2]; exact hba
      · exact absurd rfl hi
      · left; rw [m4]; exact hca
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · left; norm_num
    · right; norm_num
    · left; simp only; nlinarith
    · left; simp only; nlinarith

/-- **Ta closed**: `K20LeftTa` has a lex cell or is Rupert. -/
theorem k21_ta_close {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K20LeftTa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) := by
  rcases h with hB | ⟨hA, hL⟩
  · exact Or.inr (k21_b11 W hB)
  · obtain ⟨hctx, hA', hqr, h0⟩ := id hA
    have hT : IsT a' b c d := hctx.elim (fun h => h.1) (fun h => h.1)
    have hT' : ¬ IsT' a b c' d := hctx.elim (fun h => h.2.1) (fun h => h.2.1)
    have hz : ⟪d - b, a - b'⟫ = 0 := k17h_zeta_of_qr W hT hA'.2.2.2.1 hqr
    obtain ⟨α1, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hγ4, hβ6, hqr', hLL⟩ :=
      k17gb_a41_frame W hT' hA' hz
    have hpr : ⟪a - d, c - d⟫ = 0 := by
      rw [h0] at hLL
      have hpos : 0 < γ4 * (α1 - 1) := mul_pos (by linarith) (by linarith)
      rcases mul_eq_zero.1 hLL.symm with h | h
      · linarith
      · exact h
    rcases hβ6.eq_or_lt with he | hlt
    · subst he
      have hβ6d : det3 (a' - b) (c - d) (a - d) = 0 := by
        rw [ha']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
      exact Or.inr (k20_s14 W hT' hA' hz hβ6d h0)
    · exact Or.inl (k21_s13_pent hdet hc' hb' ha' hα1 hβ1 hγ4 hlt hqr' hpr hL)

end C2
end Type08Sp
end Minimality
