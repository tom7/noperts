module

public import Minimality.Type08S.C2K44R2

@[expose] public section

set_option maxHeartbeats 1000000

set_option maxHeartbeats 1600000
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

theorem k43b0_kb_lt {α1 β1 β6 s qq qr rr : ℝ} (hα : 1 < α1) (hβ : 1 < β1) (hb6 : 0 < β6)
    (hg1 : β1 - β6 < 1) (hqq : qr < qq) (hrr : qr < rr)
    (rel : α1 * s * (qq + rr - 2 * qr) = -(β1 - 1) * (qq * rr - qr ^ 2)) (hs : s < 0) :
    (α1 - 1) * s * (1 - β1) + β1 * (-β6 * qq + (1 - (β1 - β6)) * qr) < (α1 + β1 - 1) * s := by
  have hW : 0 < qq + rr - 2 * qr := by linarith
  have key : (-α1 * s - β6 * qq + (1 - (β1 - β6)) * qr) * (qq + rr - 2 * qr) =
      (qq - qr) * (((β1 - β6) - 1) * (rr - qr) - β6 * (qq - qr)) := by
    linear_combination (-1) * rel
  have hn : (qq - qr) * (((β1 - β6) - 1) * (rr - qr) - β6 * (qq - qr)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by nlinarith [mul_pos hb6 (sub_pos.2 hqq), mul_pos (sub_pos.2 hg1) (sub_pos.2 hrr)])
  have hX : -α1 * s - β6 * qq + (1 - (β1 - β6)) * qr < 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hh hW.le]
  nlinarith [mul_neg_of_pos_of_neg (show 0 < β1 by linarith) hX]

theorem k43b0_setup {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0) :
    ∃ (P Q R : ℝ³) (t κA : ℝ), det3 P Q R ≠ 0 ∧ 1 < α1 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ t < 0 ∧
      0 < κA ∧ κA = ⟪b' - a, c - a'⟫ ∧ t * κA = ⟪c' - a, c - a'⟫ ∧
      fpoint P Q R a (0, 0, 0) = a ∧ fpoint P Q R a (0, -β1, 0) = d ∧
      fpoint P Q R a (t, -(α1 + β1 - 1), -1) = b ∧ fpoint P Q R a (1, -(α1 + β1 - 1), 0) = c ∧
      fpoint P Q R a (β6 * t + γ6, -(α1 * β1), -β6) = a' ∧ fpoint P Q R a (t * β1, 0, -β1) = c' ∧
      fpoint P Q R a (β1, 0, 0) = b' ∧
      ⟪Q, R⟫ = 0 ∧
      (∃ e1 e2 : ℝ, ⟪P, R⟫ = e1 ∧ ⟪R, R⟫ = e2 ∧ e1 < 0 ∧ t * e1 - e2 < 0 ∧ e1 < β1 * (t * e1 - e2) ∧
        (1 - γ6) * e1 = β6 * (t * e1 - e2)) ∧
      ⟪a' - c, P⟫ < 0 ∧ ⟪a' - c, P⟫ * β1 = -κA ∧ ⟪a' - c, Q⟫ * β1 = ⟪a - d, b - d⟫ * (β1 - 1) ∧
      ⟪c' - a, c - a'⟫ < (α1 + β1 - 1) * ⟪a - d, b - d⟫ := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨m1, m2, m3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain rfl : γ6 = β1 - β6 := by linarith
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hb1 : β1 ≠ 0 := by linarith
  have hp0 : p ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hm1 : ⟪p, r⟫ = ⟪p, q⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hQR : ⟪q, r⟫ < ⟪q, q⟫ := by
    have e : c' - d = α1 • (p) + β1 • (q) := by rw [hc', hp, hq]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m2
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m2, h0, hqp, hrp]
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • (p) + β1 • (r) := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hβ1'.le (sub_nonneg.2 hh), m3, h0, hrq]
  have hs : ⟪p, q⟫ < 0 := by
    have hW : 0 < ⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫ := by linarith
    have h1 : 0 < (β1 - 1) * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) :=
      mul_pos (by linarith) hr2
    by_contra hh; push Not at hh
    have h2 : 0 ≤ α1 * ⟪p, q⟫ * (⟪q, q⟫ + ⟪r, r⟫ - 2 * ⟪q, r⟫) :=
      mul_nonneg (mul_nonneg hα1'.le hh) hW.le
    nlinarith [hr1]
  have hLe : (α1 - 1) * ⟪p, p⟫ + β1 * ⟪p, q⟫ = 0 := by
    have e : a - c' = (1 - α1) • (p) - β1 • (q) := by rw [hc', hp, hq]; module
    rw [e] at hL
    simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, hqp] at hL
    linarith
  have hα : 1 < α1 := by nlinarith
  have hD := hr2
  have hg1 : β1 - β6 < 1 := by
    by_contra hh; push Not at hh
    have := mul_nonneg (sub_nonneg.2 hh) (sub_nonneg.2 hRT.le)
    have h4 : 0 ≤ (β1 - 1) * (⟪p, p⟫ * ⟪q, r⟫ - ⟪p, q⟫ ^ 2) := mul_nonneg (by linarith) hM0
    have h5 : 0 ≤ ((β1 - β6) - 1) * (⟪r, r⟫ - ⟪q, r⟫) * ⟪p, p⟫ :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hpp.le
    linarith
  -- vectors
  have hA : c' - a = fcomb (p) (q) (r) (α1 - 1) β1 0 := by rw [hc', hp, hq]; simp only [fcomb]; module
  have hB : b' - a = fcomb (p) (q) (r) (α1 - 1) 0 β1 := by rw [hb', hp, hr]; simp only [fcomb]; module
  have hCv : c - a' = fcomb (p) (q) (r) 0 (-β6) (1 - (β1 - β6)) := by
    rw [ha', hq, hr]; simp only [fcomb]; module
  have hip := k28bq_ip p q r hm1
  -- κA, κB, t
  have hκA : ⟪b' - a, c - a'⟫ = k28bqBC α1 β1 β6 ⟪p, q⟫ ⟪q, r⟫ ⟪r, r⟫ := by
    rw [hB, hCv, hip]; unfold k28bqBC; ring
  have hκB : ⟪c' - a, c - a'⟫ = k28bqAC α1 β1 β6 ⟪p, q⟫ ⟪q, q⟫ ⟪q, r⟫ := by
    rw [hA, hCv, hip]; unfold k28bqAC; ring
  have hκpos := k28bq_kpos hpp hLe hβ1' hΛ
  set κA := k28bqBC α1 β1 β6 ⟪p, q⟫ ⟪q, r⟫ ⟪r, r⟫ with hκAdef
  set κB := k28bqAC α1 β1 β6 ⟪p, q⟫ ⟪q, q⟫ ⟪q, r⟫ with hκBdef
  have hκne : κA ≠ 0 := hκpos.ne'
  have ht : (κB / κA) * κA = κB := div_mul_cancel₀ _ hκne
  obtain ⟨_, htn, hf, htie, he1, he2⟩ := k28bq_real hα hβ hβ6' hγ6' hg1 hpp hs hLe hQR hRT hD hM0 hr1 hΛ ht
  generalize κB / κA = t at ht htn hf htie he1 he2
  -- frame
  have hip' := hip
  have hPR : ⟪fcomb p q r ((α1 - 1) / β1) 0 1, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ =
      (t * k28bqBB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪r, r⟫ - k28bqAB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, r⟫) / β1 ^ 2 := by
    rw [hip]; unfold k28bqBB k28bqAB; field_simp; ring
  have hRR : ⟪fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ =
      (t ^ 2 * k28bqBB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪r, r⟫ - 2 * t * k28bqAB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, r⟫ +
        k28bqAA α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, q⟫) / β1 ^ 2 := by
    rw [hip]; unfold k28bqBB k28bqAB k28bqAA; field_simp; ring
  have hQRz : ⟪fcomb p q r (1 / β1) 0 0, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ = 0 := by
    have e : ⟪fcomb p q r (1 / β1) 0 0, fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t⟫ =
        (t - 1) / β1 ^ 2 * ((α1 - 1) * ⟪p, p⟫ + β1 * ⟪p, q⟫) := by
      rw [hip]; field_simp; ring
    rw [e, hLe, mul_zero]
  have hPB : fcomb p q r ((α1 - 1) / β1) 0 1 = β1⁻¹ • (b' - a) := by
    rw [hB]; simp only [fcomb]; match_scalars <;> (field_simp; try ring)
  have hdetPQR : det3 (fcomb p q r ((α1 - 1) / β1) 0 1) (fcomb p q r (1 / β1) 0 0)
      (fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t) ≠ 0 := by
    rw [det3_coord]
    have : d3 ((α1 - 1) / β1) 0 1 (1 / β1) 0 0 ((t - 1) * (α1 - 1) / β1) (-1) t = -(1 / β1) := by
      simp only [d3]; ring
    rw [this]
    exact mul_ne_zero hdet (by simp [hb1])
  refine ⟨fcomb p q r ((α1 - 1) / β1) 0 1, fcomb p q r (1 / β1) 0 0,
    fcomb p q r ((t - 1) * (α1 - 1) / β1) (-1) t, t, κA, hdetPQR, hα, hβ6', hγ6', hg1, htn, hκpos,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hQRz, ?_, ?_, ?_, ?_, ?_⟩
  · exact hκA.symm
  · rw [hκB]; exact ht
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · rw [ha']; simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · rw [hc']; simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · rw [hb']; simp only [fpoint, fcomb]; match_scalars <;> field_simp <;> ring
  · set BBv := k28bqBB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪r, r⟫ with hBBv
    set ABv := k28bqAB α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, r⟫ with hABv
    set AAv := k28bqAA α1 β1 ⟪p, p⟫ ⟪p, q⟫ ⟪q, q⟫ with hAAv
    have hb2 : 0 < β1 ^ 2 := by positivity
    refine ⟨(t * BBv - ABv) / β1 ^ 2, (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2, hPR, hRR,
      div_neg_of_neg_of_pos he1 hb2, ?_, ?_, ?_⟩
    · have : t * ((t * BBv - ABv) / β1 ^ 2) - (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2 =
          (t * ABv - AAv) / β1 ^ 2 := by field_simp; ring
      rw [this]; exact div_neg_of_neg_of_pos hf hb2
    · have : t * ((t * BBv - ABv) / β1 ^ 2) - (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2 =
          (t * ABv - AAv) / β1 ^ 2 := by field_simp; ring
      rw [this, mul_div_assoc', div_lt_div_iff_of_pos_right hb2]; exact he2
    · have : t * ((t * BBv - ABv) / β1 ^ 2) - (t ^ 2 * BBv - 2 * t * ABv + AAv) / β1 ^ 2 =
          (t * ABv - AAv) / β1 ^ 2 := by field_simp; ring
      rw [this]
      field_simp
      linarith [htie]
  · rw [hPB, inner_smul_right]
    have : ⟪a' - c, b' - a⟫ = -κA := by
      rw [← neg_sub c a', inner_neg_left, real_inner_comm, hκA]
    rw [this]
    exact mul_neg_of_pos_of_neg (inv_pos.2 hβ1') (neg_lt_zero.2 hκpos)
  · rw [hPB, inner_smul_right]
    have : ⟪a' - c, b' - a⟫ = -κA := by
      rw [← neg_sub c a', inner_neg_left, real_inner_comm, hκA]
    rw [this]; field_simp
  · have e : a' - c = -(fcomb p q r 0 (-β6) (1 - (β1 - β6))) := by rw [← hCv]; abel
    rw [e, inner_neg_left, hip]; field_simp; ring
  · have e : ⟪c' - a, c - a'⟫ = (α1 - 1) * ⟪p, q⟫ * (1 - β1) + β1 * (-β6 * ⟪q, q⟫ + (1 - (β1 - β6)) * ⟪q, r⟫) := by
      rw [hA, hCv, hip]; ring
    rw [e]
    exact k43b0_kb_lt hα hβ hβ6' hg1 hQR hRT hr1 hs

set_option maxHeartbeats 3200000 in
theorem k43r2_tsc5z {α1 β1 β6 t v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (ht : t < 0) (hv2 : 0 < v2) (hZ : 0 < -(α1 + β1 - 1) * v1 + (β1 - 1) * v2)
    (hZ' : 0 < (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) * v1 + (β1 - β6) * (β1 - 1) * v2)
    (o1 : t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) = 0)
    (o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 ≤ 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k28bqCyc5 α1 β1 β6 t (i + 1) - k28bqCyc5 α1 β1 β6 t i)
        (k28bqCyc5 α1 β1 β6 t j - k28bqCyc5 α1 β1 β6 t i) (v1, v2, 0)) ∧
    (∀ x ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, -β1, 0)], ∀ i : ZMod 5,
      TSc 1 (k28bqCyc5 α1 β1 β6 t (i + 1) - k28bqCyc5 α1 β1 β6 t i)
        (x - k28bqCyc5 α1 β1 β6 t i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := k28bq_z5_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < α1 - 1 := by linarith
  have a0 : 0 < α1 := by linarith
  have b0 : 0 < β1 := by linarith
  have nt : 0 < -t := by linarith
  have p1 := mul_pos e1 e2
  have p2 := mul_pos a0 b0
  have p3 := mul_pos nt b0
  have p4 := mul_pos nt hb6
  have p5 := mul_pos nt hg6
  have p6 := mul_pos nt e1
  have p7 := mul_pos nt e2
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos p2 e1
  have p10 := mul_pos p2 e2
  constructor
  · intro i j h1 h2
    rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl <;>
      rcases k28bq_z5 j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k28bqCyc5_0, k28bqCyc5_1, k28bqCyc5_2, k28bqCyc5_3, k28bqCyc5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by linear_combination o1, by nlinarith [hZ', mul_pos hb6 hZ', mul_pos hg6 hZ', mul_pos nt hZ', mul_pos e1 hZ']⟩) | (right; refine ⟨by ring1, by nlinarith [mul_pos hb6 hZ]⟩) | (rcases o2.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith [mul_pos hb6 hZ]⟩)))
  · intro x hx i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;>
      rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k28bqCyc5_0, k28bqCyc5_1, k28bqCyc5_2, k28bqCyc5_3, k28bqCyc5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by linear_combination o1, by nlinarith [hZ', mul_pos hb6 hZ', mul_pos hg6 hZ', mul_pos nt hZ', mul_pos e1 hZ']⟩) | (right; refine ⟨by ring1, by nlinarith [mul_pos hb6 hZ]⟩) | (rcases o2.lt_or_eq with h | h; (left; nlinarith); (right; refine ⟨by linarith, by nlinarith [mul_pos hb6 hZ]⟩)))



set_option maxHeartbeats 25600000 in
theorem k43r2_B0 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hβ : 1 < β1) (hσ : β6 + γ6 = β1)
    (hL : ⟪a - c', a - d⟫ = 0)
    (hM0 : 0 ≤ ⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2)
    (hΛ : (β1 - 1) * (⟪a - d, a - d⟫ * ⟪b - d, c - d⟫ - ⟪a - d, b - d⟫ ^ 2) +
      (γ6 - 1) * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) * ⟪a - d, a - d⟫ < 0)
    (hori : k28bqOriCBA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫ = 0)
    (hori2 : 0 ≤ k28bqOriBCA α1 β1 β6 γ6 ⟪b' - a, c - a'⟫ ⟪c' - a, c - a'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨P, Q, R, t, κA, hdet, hα, hb6, hg6, hg1, ht, hκ, hκA, hκB, eA, eD, eB, eC, eA', eC', eB', hQR,
    ⟨e1, e2, hPR, hRR, he1, hf, hE, htie⟩, hl1, hm1v, hm2v, hkb⟩ := k43b0_setup hC hM hrel hβ hσ hL hM0 hΛ
  obtain rfl : γ6 = β1 - β6 := by linarith
  rw [← hκA, ← hκB] at hori hori2
  rw [k28bq_ori1] at hori
  rw [k28bq_ori2] at hori2
  have o1 : t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) = 0 := by
    have h0 : -κA * (t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6)) = 0 := hori
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact h
  have hCpos : 0 < α1 + β1 - 1 := by linarith
  have hA1 : 0 < α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6) := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (neg_nonneg.2 ht.le) (neg_nonneg.2 hh), mul_pos hCpos hg6]
  have hcone : (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) * ⟪a' - c, Q⟫ >
      (β1 - β6) * (β1 - 1) * ⟪a' - c, P⟫ := by
    have hb1p : 0 < β1 := by linarith
    have e1' : 0 < β1 - 1 := by linarith
    have hk : t * κA < (α1 + β1 - 1) * ⟪a - d, b - d⟫ := by rw [hκB]; exact hkb
    set A1 := α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6) with hA1def
    set sv := ⟪a - d, b - d⟫ with hsv
    set C := α1 + β1 - 1 with hCdef
    have h1 := mul_lt_mul_of_pos_right hk hA1
    have h2 : t * κA * A1 = -(C * (β1 - β6) * κA) := by linear_combination κA * o1
    have key : A1 * sv > -((β1 - β6) * κA) := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hCpos.le (sub_nonneg.2 hh)]
    have h3 := mul_lt_mul_of_pos_right key e1'
    have eq1 : β1 * ((β1 - β6) * (β1 - 1) * ⟪a' - c, P⟫) = -((β1 - β6) * (β1 - 1) * κA) := by
      linear_combination (β1 - β6) * (β1 - 1) * hm1v
    have eq2 : β1 * (A1 * ⟪a' - c, Q⟫) = A1 * sv * (β1 - 1) := by
      linear_combination A1 * hm2v
    by_contra hh; push Not at hh
    nlinarith [mul_le_mul_of_nonneg_left hh hb1p.le]
  have o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 ≤ 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos hκ hh]
  have hb1 : 0 < β1 := by linarith
  have hdep : ∀ x y z : ℝ, ⟪fpoint P Q R a (x, y, z), R⟫ = ⟪a, R⟫ + x * e1 + z * e2 := by
    intro x y z; rw [inner_fpoint, hQR, hPR, hRR]; ring
  have hR0 : R ≠ 0 := by
    intro h0; apply hdet; rw [h0]; simp [det3_expand]
  refine ⟨R, hR0, ?_⟩
  set L : List (ℝ × ℝ) := [(⟪a' - c, P⟫, ⟪a' - c, Q⟫), (0, 1), (-(α1 + β1 - 1), β1 - 1), (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6), (β1 - β6) * (β1 - 1))] with hLdef
  have hT : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < v2 := by
    intro v1 v2 hv
    have := hv (0, 1) (by simp [hLdef])
    simpa using this
  have hZ : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < -(α1 + β1 - 1) * v1 + (β1 - 1) * v2 := by
    intro v1 v2 hv
    have := hv (-(α1 + β1 - 1), β1 - 1) (by simp [hLdef])
    simpa using this
  have hZ' : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → 0 < (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) * v1 + (β1 - β6) * (β1 - 1) * v2 := by
    intro v1 v2 hv
    have := hv (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6), (β1 - β6) * (β1 - 1)) (by simp [hLdef])
    simpa using this
  have hsub : ∀ s u : ℝ × ℝ × ℝ, ⟪fpoint P Q R a s, R⟫ < ⟪fpoint P Q R a u, R⟫ → K25Step P Q R a L s u :=
    fun s u h => ⟨h.le, fun h' => absurd h' h.ne⟩
  have hF := hf
  have hb1' : 0 < β1 - 1 := by linarith
  have hp1 := mul_neg_of_pos_of_neg hb1' hF
  have hp2 := mul_neg_of_pos_of_neg hb1' he1
  obtain ⟨s0, hs0a, hs0b, hs0c⟩ : ∃ s0 : ℝ, 0 < s0 * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (β1 - β6) * (β1 - 1) ∧
      s0 * (-(α1 + β1 - 1)) + (β1 - 1) > 0 ∧ s0 * ⟪a' - c, P⟫ + ⟪a' - c, Q⟫ > 0 := by
    have hn1 : 0 < -⟪a' - c, P⟫ := neg_pos.2 hl1
    have hlo : -((β1 - β6) * (β1 - 1)) / (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) < (β1 - 1) / (α1 + β1 - 1) :=
      lt_trans (div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hg6 (by linarith))) hA1) (div_pos (by linarith) hCpos)
    have hlo2 : -((β1 - β6) * (β1 - 1)) / (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) < ⟪a' - c, Q⟫ / (-⟪a' - c, P⟫) := by
      rw [div_lt_div_iff₀ hA1 hn1]; nlinarith [hcone]
    obtain ⟨s0, h1, h2⟩ := exists_between (lt_min hlo hlo2)
    have h1' := (div_lt_iff₀ hA1).1 h1
    have h2a := (lt_div_iff₀ hCpos).1 (lt_of_lt_of_le h2 (min_le_left _ _))
    have h2b := (lt_div_iff₀ hn1).1 (lt_of_lt_of_le h2 (min_le_right _ _))
    refine ⟨s0, ?_, ?_, ?_⟩ <;> nlinarith
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R a hdet (k := 5) (by norm_num) (k28bqCyc5 α1 β1 β6 t)
    (k28bq_inj5 hα hβ hb6 hg6 ht) ?_ L (by simp [hLdef]) ?_ ?_
    (3 : ZMod 5) ?_ ?_ ?_ (ρ1 := s0) (ρ2 := 1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl
    · simp only [k28bqCyc5_0, eC]; simp [V8]
    · simp only [k28bqCyc5_1, eB']; simp [V8]
    · simp only [k28bqCyc5_2, eC']; simp [V8]
    · simp only [k28bqCyc5_3, eB]; simp [V8]
    · simp only [k28bqCyc5_4, eA']; simp [V8]
  · intro v1 v2 hv D hD i j h1 h2
    exact tsc_scale hD ((k43r2_tsc5z hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) (hZ' v1 v2 hv) o1 o2).1 i j h1 h2)
  · intro y hy hyx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    have hV : y = fpoint P Q R a (0, 0, 0) ∨ y = fpoint P Q R a (0, -β1, 0) ∨
        y = fpoint P Q R a (t, -(α1 + β1 - 1), -1) ∨ y = fpoint P Q R a (1, -(α1 + β1 - 1), 0) ∨
        y = fpoint P Q R a (β6 * t + (β1 - β6), -(α1 * β1), -β6) ∨ y = fpoint P Q R a (t * β1, 0, -β1) ∨
        y = fpoint P Q R a (β1, 0, 0) := by
      rw [eA, eD, eB, eC, eA', eC', eB']; tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc5z hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) (hZ' v1 v2 hv) o1 o2).2 _ (by simp) i)
    · refine ⟨_, rfl, fun v1 v2 hv D hD i => ?_⟩
      exact tsc_scale hD ((k43r2_tsc5z hα hβ hb6 hg6 hg1 ht (hT v1 v2 hv) (hZ v1 v2 hv) (hZ' v1 v2 hv) o1 o2).2 _ (by simp) i)
    · exact (hyx 3 (by rw [k28bqCyc5_3])).elim
    · exact (hyx 0 (by rw [k28bqCyc5_0])).elim
    · exact (hyx 4 (by rw [k28bqCyc5_4])).elim
    · exact (hyx 2 (by rw [k28bqCyc5_2])).elim
    · exact (hyx 1 (by rw [k28bqCyc5_1])).elim
  · -- hP1 : c' < b
    rw [show (3 : ZMod 5) - 1 = 2 by decide]
    refine hsub _ _ ?_
    simp only [k28bqCyc5_2, k28bqCyc5_3, hdep]
    nlinarith
  · rw [show (3 : ZMod 5) + 1 = 4 by decide]
    refine hsub _ _ ?_
    simp only [k28bqCyc5_4, k28bqCyc5_3, hdep]
    nlinarith
  · intro i hi
    rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl
    · left
      rw [show (0 : ZMod 5) - 1 = 4 by decide]
      refine ⟨?_, fun h => ?_⟩
      · simp only [k28bqCyc5_4, k28bqCyc5_0, hdep]
        nlinarith
      · intro v1 v2 hv
        have := hv (⟪a' - c, P⟫, ⟪a' - c, Q⟫) (by simp [hLdef])
        simp only [k28bqCyc5_4, k28bqCyc5_0, eA', eC]
        simpa using this
    · left
      rw [show (1 : ZMod 5) - 1 = 0 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc5_0, k28bqCyc5_1, hdep]
      nlinarith
    · right
      rw [show (2 : ZMod 5) + 1 = 3 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc5_2, k28bqCyc5_3, hdep]
      nlinarith
    · exact absurd rfl hi
    · left
      rw [show (4 : ZMod 5) - 1 = 3 by decide]
      refine hsub _ _ ?_
      simp only [k28bqCyc5_4, k28bqCyc5_3, hdep]
      nlinarith
  · intro l hl
    simp only [hLdef, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · left; simp; linarith
    · left; simp
    · left; simp; linarith
    · left; simp; linarith



end C2
end Type08Sp
end Minimality
