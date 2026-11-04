module

public import Minimality.Type08S.C2K28H5a1

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k28h5a_step_lt {p q r d : ℝ³} {L : List (ℝ × ℝ)} {s t : ℝ × ℝ × ℝ}
    (h : ⟪fpoint p q r d s, r⟫ < ⟪fpoint p q r d t, r⟫) : K25Step p q r d L s t :=
  ⟨h.le, fun e => absurd e h.ne⟩

set_option maxHeartbeats 12800000 in
/-- Type 08 M-stratum H5 residue, cell A (view `u0 = ⟨e,f⟩e - ⟨e,e⟩f`, `e = c'-a`, `f = b'-a`), side `S > 0`. -/
theorem k28h5_A {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6)
    (hS : 0 < ⟪c' - a, b' - a⟫)
    (hT : ⟪a - d, a - c'⟫ < 0)
    (hD2 : 0 < ⟪c' - a, b' - a⟫ * ⟪a - a', c' - a⟫ - ⟪c' - a, c' - a⟫ * ⟪a - a', b' - a⟫)
    (hrb : ∀ κ g : ℝ, κ = ⟪c' - a, b' - a⟫ / ⟪c' - a, c' - a⟫ → g = (α1 - 1) * (1 - κ) / β1 →
      0 < γ6 * g * (β1 - 1) + α1 * (β6 + γ6 * κ - 1)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  obtain ⟨⟨⟨⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, hl0⟩, hl1, hl2⟩, hl3, hl4⟩, -⟩ := h5
  obtain ⟨hM0, hM1, hM2⟩ := hM
  obtain ⟨p, hp⟩ : ∃ p : ℝ³, p = a - d := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ³, q = b - d := ⟨_, rfl⟩
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ³, r0 = c - d := ⟨_, rfl⟩
  have ha2 : a = d + p := by rw [hp]; abel
  have hb2 : b = d + q := by rw [hq]; abel
  have hc2 : c = d + r0 := by rw [hr0]; abel
  have hc'2 : c' = d + α1 • p + β1 • q := by rw [hc', hp, hq]
  have hb'2 : b' = d + α1 • p + β1 • r0 := by rw [hb', hp, hr0]
  have ha'2 : a' = d + β6 • q + γ6 • r0 := by rw [ha', hq, hr0]
  have hdet' : det3 p q r0 ≠ 0 := by rw [hp, hq, hr0]; exact hdet
  obtain ⟨e, he⟩ : ∃ e : ℝ³, e = c' - a := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℝ³, f = b' - a := ⟨_, rfl⟩
  have he' : e = (α1 - 1) • p + β1 • q := by rw [he, hc'2, ha2]; module
  have hf' : f = (α1 - 1) • p + β1 • r0 := by rw [hf, hb'2, ha2]; module
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = ⟪e, f⟫ := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F : ℝ, F = ⟪f, f⟫ := ⟨_, rfl⟩
  have hSpos : 0 < S := by rw [hSd, he, hf]; exact hS
  -- Gram facts
  have e1 : c' - d = α1 • p + β1 • q := by rw [hc'2]; abel
  have e2 : b - c = q - r0 := by rw [hb2, hc2]; abel
  rw [e1, e2] at hM1
  rw [← hp, e2] at hM0
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = ⟪q, q - r0⟫ := ⟨_, rfl⟩
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hM0, ← hwd] at hM1
  have hw : 0 < w := by
    by_contra hn; push Not at hn; nlinarith [mul_nonneg hβ1p.le (neg_nonneg.2 hn)]
  have hpq : ⟪p, q⟫ = ⟪p, r0⟫ := by rw [inner_sub_right] at hM0; linarith
  have c1 : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have c2 : ⟪r0, p⟫ = ⟪p, r0⟫ := real_inner_comm _ _
  have c3 : ⟪r0, q⟫ = ⟪q, r0⟫ := real_inner_comm _ _
  have hSE : S - E = -(β1 * β1 * w) := by
    rw [hSd, hEd, he', hf', hwd]
    simp only [inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right, c1, c2, c3]
    linear_combination (-(β1 * (α1 - 1))) * hpq
  have hdet2 : det3 p e r0 = β1 * det3 p q r0 := by
    rw [he']; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hene : e ≠ 0 := by
    intro h0
    have : det3 p e r0 = 0 := by rw [h0]; simp [det3_expand]
    rw [hdet2] at this
    exact hdet' ((mul_eq_zero.1 this).resolve_left hβ1p.ne')
  have hE0 : 0 < E := by rw [hEd]; exact real_inner_self_pos.2 hene
  obtain ⟨κ, hκd⟩ : ∃ κ : ℝ, κ = S / E := ⟨_, rfl⟩
  obtain ⟨g, hgd⟩ : ∃ g : ℝ, g = (α1 - 1) * (1 - κ) / β1 := ⟨_, rfl⟩
  obtain ⟨ζ, hζd⟩ : ∃ ζ : ℝ, ζ = 1 / (β1 * E) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκd]; positivity
  have hκ1 : κ < 1 := by
    rw [hκd, div_lt_one hE0]; nlinarith [mul_pos (mul_pos hβ1p hβ1p) hw]
  have hg : 0 < g := by
    rw [hgd]; exact div_pos (mul_pos (sub_pos.2 hα1) (sub_pos.2 hκ1)) hβ1p
  have hζ : 0 < ζ := by rw [hζd]; positivity
  have hBg : β1 * g = (α1 - 1) * (1 - κ) := by rw [hgd]; field_simp
  obtain ⟨u0, hu0⟩ : ∃ u0 : ℝ³, u0 = S • e - E • f := ⟨_, rfl⟩
  have key : u0 = ((α1 - 1) * (S - E)) • p + (β1 * S) • q + (-(β1 * E)) • r0 := by
    rw [hu0, he', hf']; module
  have hBE : β1 * E ≠ 0 := by positivity
  have hr0' : r0 = (-g) • p + κ • q + (-ζ) • u0 := by
    have hmain : (β1 * E) • r0 = (β1 * E) • ((-g) • p + κ • q + (-ζ) • u0) := by
      simp only [smul_add, smul_smul]
      have k1 : β1 * E * (-g) = (α1 - 1) * (S - E) := by rw [hgd, hκd]; field_simp; ring
      have k2 : β1 * E * κ = β1 * S := by rw [hκd]; field_simp
      have k3 : β1 * E * (-ζ) = -1 := by rw [hζd]; field_simp
      rw [k1, k2, k3]
      conv_rhs => rw [key]
      module
    have h2 := congrArg (fun x => (β1 * E)⁻¹ • x) hmain
    simp only [smul_smul, inv_mul_cancel₀ hBE, one_smul] at h2
    exact h2
  have Ea : fpoint p q u0 d (1, 0, 0) = a := by rw [k17f_fp, ha2]; module
  have Ed : fpoint p q u0 d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint p q u0 d (0, 1, 0) = b := by rw [k17f_fp, hb2]; module
  have Ec : fpoint p q u0 d (-g, κ, -ζ) = c := by rw [k17f_fp, hc2, hr0']; module
  have Ec' : fpoint p q u0 d (α1, β1, 0) = c' := by rw [k17f_fp, hc'2]; module
  have Ea' : fpoint p q u0 d (-(γ6 * g), β6 + γ6 * κ, -(γ6 * ζ)) = a' := by
    rw [k17f_fp, ha'2, hr0']; module
  have Eb' : fpoint p q u0 d (1 + (α1 - 1) * κ, β1 * κ, -(β1 * ζ)) = b' := by
    rw [k17f_fp, hb'2, hr0', show (1:ℝ) + (α1 - 1) * κ = α1 + β1 * (-g) by linarith [hBg]]; module
  have hΔ : det3 p q u0 ≠ 0 := by
    have : det3 p q u0 = (-(β1 * E)) * det3 p q r0 := by
      rw [key]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this]; exact mul_ne_zero (neg_ne_zero.2 hBE) hdet'
  have hu0ne : u0 ≠ 0 := k17f_r0 hΔ
  -- depths
  have hpe : ⟪p, f⟫ = ⟪p, e⟫ := by
    rw [hf', he']; simp only [inner_add_right, real_inner_smul_right]; rw [hpq]
  have hTpos : 0 < ⟪p, e⟫ := by
    have h' : a - c' = -e := by rw [he]; abel
    rw [← hp, h', inner_neg_right] at hT; linarith
  have hP : ⟪p, u0⟫ = ⟪p, e⟫ * (S - E) := by
    rw [hu0, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hpe]; ring
  have hPneg : ⟪p, u0⟫ < 0 := by
    rw [hP, hSE]; nlinarith [mul_pos (mul_pos (mul_pos hβ1p hβ1p) hw) hTpos]
  have hEu : ⟪e, u0⟫ = 0 := by
    rw [hu0, inner_sub_right, real_inner_smul_right, real_inner_smul_right, ← hEd, ← hSd]; ring
  have hFu : ⟪f, u0⟫ = S * S - E * F := by
    rw [hu0, inner_sub_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm e f, ← hSd, ← hFd]
  have hr0u : β1 * ⟪r0, u0⟫ = ⟪f, u0⟫ - (α1 - 1) * ⟪p, u0⟫ := by
    conv_rhs => rw [hf']
    simp only [inner_add_left, real_inner_smul_left]; ring
  have hqu : β1 * ⟪q, u0⟫ = ⟪e, u0⟫ - (α1 - 1) * ⟪p, u0⟫ := by
    conv_rhs => rw [he']
    simp only [inner_add_left, real_inner_smul_left]; ring
  have hCS : S * S ≤ E * F := by rw [hSd, hEd, hFd]; exact real_inner_mul_inner_self_le e f
  have dA : ⟪a, u0⟫ = ⟪d, u0⟫ + ⟪p, u0⟫ := by rw [ha2, inner_add_left]
  have dC : ⟪c, u0⟫ = ⟪d, u0⟫ + ⟪r0, u0⟫ := by rw [hc2, inner_add_left]
  have dA' : ⟪a', u0⟫ = ⟪d, u0⟫ + β6 * ⟪q, u0⟫ + γ6 * ⟪r0, u0⟫ := by
    rw [ha'2]; simp only [inner_add_left, real_inner_smul_left]
  have dC' : ⟪c', u0⟫ = ⟪d, u0⟫ + α1 * ⟪p, u0⟫ + β1 * ⟪q, u0⟫ := by
    rw [hc'2]; simp only [inner_add_left, real_inner_smul_left]
  have hdep1 : ⟪c', u0⟫ = ⟪a, u0⟫ := by
    rw [dC', dA]; rw [hEu] at hqu; linarith
  have hdep2 : ⟪a, u0⟫ < ⟪d, u0⟫ := by rw [dA]; linarith
  have hdep3 : ⟪a', u0⟫ < ⟪a, u0⟫ := by
    have hD2' : 0 < S * ⟪a - a', e⟫ - E * ⟪a - a', f⟫ := by rw [hSd, hEd, he, hf]; exact hD2
    have : ⟪a - a', u0⟫ = S * ⟪a - a', e⟫ - E * ⟪a - a', f⟫ := by
      rw [hu0, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    rw [inner_sub_left] at this; linarith
  have hs1 : 0 < β6 + γ6 - 1 := by linarith
  have hdep4 : ⟪c, u0⟫ < ⟪a', u0⟫ := by
    rw [hEu] at hqu
    have key3 : β1 * (β6 * ⟪q, u0⟫ + (γ6 - 1) * ⟪r0, u0⟫) =
        β6 * (-((α1 - 1) * ⟪p, u0⟫)) + (γ6 - 1) * (S * S - E * F - (α1 - 1) * ⟪p, u0⟫) := by
      rw [hFu] at hr0u
      linear_combination β6 * hqu + (γ6 - 1) * hr0u
    have hpos : 0 < β1 * (β6 * ⟪q, u0⟫ + (γ6 - 1) * ⟪r0, u0⟫) := by
      rw [key3]
      nlinarith [mul_pos (mul_pos (sub_pos.2 hα1) (neg_pos.2 hPneg)) hs1,
        mul_nonneg (sub_pos.2 hγ6).le (sub_nonneg.2 hCS)]
    have : 0 < β6 * ⟪q, u0⟫ + (γ6 - 1) * ⟪r0, u0⟫ := by
      by_contra hn; push Not at hn; nlinarith [mul_nonneg hβ1p.le (neg_nonneg.2 hn)]
    rw [dC, dA']; linarith
  -- cone and ray
  have hac : a - c' = -e := by rw [he]; abel
  have hv1 : ⟪a - c', p⟫ = -⟪p, e⟫ := by rw [hac, inner_neg_left, real_inner_comm]
  have hv2 : ⟪a - c', q⟫ = -⟪q, e⟫ := by rw [hac, inner_neg_left, real_inner_comm]
  have hEd2 : E = (α1 - 1) * ⟪p, e⟫ + β1 * ⟪q, e⟫ := by
    have h' : ⟪e, e⟫ = ⟪(α1 - 1) • p + β1 • q, e⟫ := by rw [← he']
    simp only [inner_add_left, real_inner_smul_left] at h'
    rw [hEd]; exact h'
  -- point equalities along the cycle
  have hY0 : fpoint p q u0 d (k28h5aY α1 β1 β6 γ6 g κ ζ 0) = a := by rw [k28h5aY_0]; exact Ea
  have hY1 : fpoint p q u0 d (k28h5aY α1 β1 β6 γ6 g κ ζ 1) = c' := by rw [k28h5aY_1]; exact Ec'
  have hY2 : fpoint p q u0 d (k28h5aY α1 β1 β6 γ6 g κ ζ 2) = a' := by rw [k28h5aY_2]; exact Ea'
  have hY3 : fpoint p q u0 d (k28h5aY α1 β1 β6 γ6 g κ ζ 3) = c := by rw [k28h5aY_3]; exact Ec
  have hY4 : fpoint p q u0 d (k28h5aY α1 β1 β6 γ6 g κ ζ 4) = d := by rw [k28h5aY_4]; exact Ed
  have hrb' := hrb κ g (by rw [hκd, hSd, hEd, he, hf]) hgd
  obtain ⟨m0, m1, m2, m3, m4, p0, p1, p2, p3, p4⟩ := k19_z5
  have step_c'a : K25Step p q u0 d [(⟪a - c', p⟫, ⟪a - c', q⟫), (-β1, α1 - 1)]
      (k28h5aY α1 β1 β6 γ6 g κ ζ 1) (k28h5aY α1 β1 β6 γ6 g κ ζ 0) := by
    refine ⟨?_, fun _ v1 v2 hv => ?_⟩
    · rw [hY1, hY0]; exact hdep1.le
    · rw [hY0, hY1]
      exact hv (⟪a - c', p⟫, ⟪a - c', q⟫) (by simp)
  refine ⟨u0, hu0ne, ?_⟩
  refine k25_tie_cell (V8 a a' b b' c c' d) p q u0 d hΔ (k := 5) (by norm_num)
    (k28h5aY α1 β1 β6 γ6 g κ ζ) (k28h5aY_inj hα1 hγ6p hγ6 hg hζ hκ hβ1) ?_
    [(⟪a - c', p⟫, ⟪a - c', q⟫), (-β1, α1 - 1)] (by simp) ?_ ?_ 4 ?_ ?_ ?_
    (ρ1 := -E - (1 - ⟪p, e⟫) * (α1 - 1)) (ρ2 := -(1 - ⟪p, e⟫) * β1) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [hY0]; simp [V8]
    · rw [hY1]; simp [V8]
    · rw [hY2]; simp [V8]
    · rw [hY3]; simp [V8]
    · rw [hY4]; simp [V8]
  · intro v1 v2 hC D hD
    have h2 := hC (-β1, α1 - 1) (by simp)
    simp only at h2
    exact (k28h5a_tsc hD hα1 hβ1 hβ6p hβ6 hγ6p hγ6 hσ hg hκ hκ1 hζ hrb' h2).1
  · intro y hy hyx
    have hV : y = fpoint p q u0 d (1, 0, 0) ∨ y = fpoint p q u0 d (α1, β1, 0) ∨
        y = fpoint p q u0 d (-(γ6 * g), β6 + γ6 * κ, -(γ6 * ζ)) ∨ y = fpoint p q u0 d (-g, κ, -ζ) ∨
        y = fpoint p q u0 d (0, 0, 0) ∨ y = fpoint p q u0 d (0, 1, 0) ∨
        y = fpoint p q u0 d (1 + (α1 - 1) * κ, β1 * κ, -(β1 * ζ)) := by
      rw [Ea, Ec', Ea', Ec, Ed, Eb, Eb']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT' : ∀ v1 v2 : ℝ, k18Cone [(⟪a - c', p⟫, ⟪a - c', q⟫), (-β1, α1 - 1)] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1 + (α1 - 1) * κ, β1 * κ, -(β1 * ζ))], ∀ i : ZMod 5,
          TSc D (k28h5aY α1 β1 β6 γ6 g κ ζ (i + 1) - k28h5aY α1 β1 β6 γ6 g κ ζ i)
            (t - k28h5aY α1 β1 β6 γ6 g κ ζ i) (v1, v2, 0) := by
      intro v1 v2 hC D hD
      have h2 := hC (-β1, α1 - 1) (by simp)
      simp only at h2
      exact (k28h5a_tsc hD hα1 hβ1 hβ6p hβ6 hγ6p hγ6 hσ hg hκ hκ1 hζ hrb' h2).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k28h5aY_0])).elim
    · exact (hyx 1 (by rw [k28h5aY_1])).elim
    · exact (hyx 2 (by rw [k28h5aY_2])).elim
    · exact (hyx 3 (by rw [k28h5aY_3])).elim
    · exact (hyx 4 (by rw [k28h5aY_4])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT' v1 v2 hC D hD _ (by simp) i⟩
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT' v1 v2 hC D hD _ (by simp) i⟩
  · rw [m4]
    exact k28h5a_step_lt (by rw [hY3, hY4]; linarith)
  · rw [p4]
    exact k28h5a_step_lt (by rw [hY0, hY4]; linarith)
  · intro i hi
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · left; rw [m0]; exact k28h5a_step_lt (by rw [hY0, hY4]; linarith)
    · left; rw [m1]; exact step_c'a
    · left; rw [m2]; exact k28h5a_step_lt (by rw [hY2, hY1]; linarith)
    · left; rw [m3]; exact k28h5a_step_lt (by rw [hY3, hY2]; linarith)
    · exact absurd rfl hi
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left
      simp only
      rw [hv1, hv2]
      have : -⟪p, e⟫ * (-E - (1 - ⟪p, e⟫) * (α1 - 1)) + -⟪q, e⟫ * (-(1 - ⟪p, e⟫) * β1) = E := by
        linear_combination (-(1 - ⟪p, e⟫)) * hEd2
      rw [this]; exact hE0
    · left
      simp only
      nlinarith [mul_pos hβ1p hE0]

end C2
end Type08Sp
end Minimality
