module

public import Mathlib

/-!
# Lemma MO (scaling vector of a positive definite matrix)

For every positive definite real `n × n` matrix `G` there is `v` with `v_a > 0` and
`v_a (G v)_a = 1` for all `a` (`exists_scaling_of_posDef`).  This is the matrix-scaling theorem
for positive definite matrices; in the corner frame it is the axis view `v` whose depth covector
is `1/v` (CORNER-SO-IDEAS-FABLE §2).

Proof: in the variables `v = exp u` the function
`g(u) = ½ vᵀ G v − Σ_a u_a` is continuous on `ℝⁿ` and coercive (`vᵀ G v ≥ μ Σ v_a²` with `μ > 0`
from compactness of the unit sphere), so it has a global minimum (a minimum over a large box that
beats every point outside the box).  Along the coordinate line `u + s e_a` the derivative at
`s = 0` is `v_a (G v)_a − 1` (symmetry of `G`), which vanishes at the minimum.
Uniqueness (strict convexity) is not needed and not proved.
-/

@[expose] public section

set_option autoImplicit false

open Finset Filter Topology Matrix

namespace Minimality
namespace CornerSnap

variable {ι : Type*} [Fintype ι]

/-- A positive definite real matrix dominates a positive multiple of the identity on all of
`ℝⁿ`: `μ Σ w_b² ≤ wᵀ G w`. -/
theorem PosDef.exists_quad_lower {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    ∃ μ > 0, ∀ w : ι → ℝ, μ * ∑ b, w b ^ 2 ≤ w ⬝ᵥ (G *ᵥ w) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun w => by simp⟩
  have hq : Continuous fun w : ι → ℝ => w ⬝ᵥ (G *ᵥ w) := by
    simp only [dotProduct, Matrix.mulVec]; fun_prop
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    (NormedSpace.sphere_nonempty).2 zero_le_one
  obtain ⟨w₀, hw₀, hmin⟩ :=
    (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hq.continuousOn
  have hpos : ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w) := fun w hw => by
    simpa using hG.dotProduct_mulVec_pos hw
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl; simp at hw₀
  set lam := w₀ ⬝ᵥ (G *ᵥ w₀) with hlam
  have hlam0 : 0 < lam := hpos w₀ hw₀ne
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨lam / Fintype.card ι, div_pos hlam0 hcard, fun w => ?_⟩
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  -- `wᵀ G w = ‖w‖² q(w/‖w‖) ≥ ‖w‖² λ`
  have hsc : w ⬝ᵥ (G *ᵥ w) = ‖w‖ ^ 2 * ((‖w‖⁻¹ • w) ⬝ᵥ (G *ᵥ (‖w‖⁻¹ • w))) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    field_simp
  have hsph : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [norm_smul, hn.ne']
  have h1 : lam ≤ (‖w‖⁻¹ • w) ⬝ᵥ (G *ᵥ (‖w‖⁻¹ • w)) := hmin hsph
  have h2 : ∑ b, w b ^ 2 ≤ Fintype.card ι * ‖w‖ ^ 2 := by
    have : ∀ b ∈ (univ : Finset ι), w b ^ 2 ≤ ‖w‖ ^ 2 := fun b _ => by
      have := norm_le_pi_norm w b
      rw [Real.norm_eq_abs] at this
      nlinarith [abs_nonneg (w b), sq_abs (w b)]
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  rw [hsc]
  calc lam / Fintype.card ι * ∑ b, w b ^ 2 ≤ lam / Fintype.card ι * (Fintype.card ι * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (div_pos hlam0 hcard).le
    _ = ‖w‖ ^ 2 * lam := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-- The potential `g(u) = ½ Σ_b e^{u_b} Σ_c G_bc e^{u_c} − Σ_b u_b`. -/
noncomputable def scalingPot (G : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ :=
  (∑ b, Real.exp (u b) * ∑ c, G b c * Real.exp (u c)) / 2 - ∑ b, u b

theorem continuous_scalingPot (G : Matrix ι ι ℝ) : Continuous (scalingPot G) := by
  unfold scalingPot; fun_prop

/-- The one-variable bound behind coercivity: `h(s) = μ/2 e^{2s} − s`. -/
theorem scaling_h_lower {μ : ℝ} (hμ : 0 < μ) (s : ℝ) :
    -(1 / (2 * μ)) ≤ μ / 2 * Real.exp s ^ 2 - s := by
  have he := Real.add_one_le_exp s
  have hpos := Real.exp_pos s
  rcases le_or_gt s 0 with hs | hs
  · have : 0 ≤ μ / 2 * Real.exp s ^ 2 := by positivity
    have : 0 ≤ 1 / (2 * μ) := by positivity
    linarith
  · have hsq : s ^ 2 ≤ Real.exp s ^ 2 := by nlinarith
    have key : -(1 / (2 * μ)) ≤ μ / 2 * s ^ 2 - s := by
      rw [neg_le_iff_add_nonneg]
      have : μ / 2 * s ^ 2 - s + 1 / (2 * μ) = (μ * s - 1) ^ 2 / (2 * μ) := by
        field_simp; ring
      have h0 : 0 ≤ (μ * s - 1) ^ 2 / (2 * μ) := by positivity
      linarith
    nlinarith

theorem scaling_h_large {μ T : ℝ} (hμ : 0 < μ) (hT : 1 ≤ T) {s : ℝ}
    (hs : s < -(T + 2 * (T + 1) / μ) ∨ T + 2 * (T + 1) / μ < s) :
    T < μ / 2 * Real.exp s ^ 2 - s := by
  have hpos := Real.exp_pos s
  have hR : 0 ≤ 2 * (T + 1) / μ := by positivity
  rcases hs with hs | hs
  · have : 0 ≤ μ / 2 * Real.exp s ^ 2 := by positivity
    linarith
  · have he := Real.add_one_le_exp s
    have hs0 : 0 < s := by linarith
    have hsq : s ^ 2 ≤ Real.exp s ^ 2 := by nlinarith
    have h2 : 2 * (T + 1) < μ * s := by
      have := (div_lt_iff₀ hμ).1 (show 2 * (T + 1) / μ < s by linarith)
      linarith
    have : T < μ / 2 * s ^ 2 - s := by nlinarith
    nlinarith

/-- `g(u) ≥ Σ_b (μ/2 e^{2u_b} − u_b)`. -/
theorem scalingPot_ge {G : Matrix ι ι ℝ} {μ : ℝ}
    (hμ : ∀ w : ι → ℝ, μ * ∑ b, w b ^ 2 ≤ w ⬝ᵥ (G *ᵥ w)) (u : ι → ℝ) :
    ∑ b, (μ / 2 * Real.exp (u b) ^ 2 - u b) ≤ scalingPot G u := by
  have h := hμ fun b => Real.exp (u b)
  simp only [dotProduct, Matrix.mulVec] at h
  unfold scalingPot
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have : μ / 2 * ∑ b, Real.exp (u b) ^ 2 = (μ * ∑ b, Real.exp (u b) ^ 2) / 2 := by ring
  rw [this]
  linarith

/-- `g` has a global minimum. -/
theorem exists_min_scalingPot {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    ∃ u : ι → ℝ, ∀ u', scalingPot G u ≤ scalingPot G u' := by
  classical
  obtain ⟨μ, hμ0, hμ⟩ := PosDef.exists_quad_lower hG
  set B := 1 / (2 * μ) with hB
  have hB0 : 0 ≤ B := by positivity
  set T := |scalingPot G 0| + Fintype.card ι * B + 1 with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ (Fintype.card ι : ℝ) * B := by positivity
    have := abs_nonneg (scalingPot G 0); linarith
  set R := T + 2 * (T + 1) / μ with hR
  have hR0 : 0 ≤ R := by have : 0 ≤ 2 * (T + 1) / μ := by positivity
                         linarith
  have hK : IsCompact (Set.Icc (fun _ : ι => -R) (fun _ => R)) := isCompact_Icc
  have h0K : (0 : ι → ℝ) ∈ Set.Icc (fun _ : ι => -R) (fun _ => R) :=
    ⟨fun _ => by simp only [Pi.zero_apply]; linarith, fun _ => by simpa using hR0⟩
  obtain ⟨u, huK, hmin⟩ := hK.exists_isMinOn ⟨0, h0K⟩ (continuous_scalingPot G).continuousOn
  refine ⟨u, fun u' => ?_⟩
  by_cases hu' : u' ∈ Set.Icc (fun _ : ι => -R) (fun _ => R)
  · exact hmin hu'
  · -- outside the box: some coordinate is large, and `g u' > g 0 ≥ g u`
    have hle0 : scalingPot G u ≤ scalingPot G 0 := hmin h0K
    obtain ⟨a, ha⟩ : ∃ a, u' a < -R ∨ R < u' a := by
      by_contra hcon
      push Not at hcon
      exact hu' ⟨fun a => (hcon a).1, fun a => (hcon a).2⟩
    have hla := scaling_h_large hμ0 hT1 ha
    have hrest : -(Fintype.card ι * B) ≤
        ∑ b ∈ univ.erase a, (μ / 2 * Real.exp (u' b) ^ 2 - u' b) := by
      have : ∑ b ∈ univ.erase a, (-B) ≤
          ∑ b ∈ univ.erase a, (μ / 2 * Real.exp (u' b) ^ 2 - u' b) :=
        Finset.sum_le_sum fun b _ => scaling_h_lower hμ0 (u' b)
      have hc : ((univ.erase a).card : ℝ) ≤ Fintype.card ι := by
        exact_mod_cast (Finset.card_erase_le).trans (le_of_eq (Finset.card_univ))
      simp only [Finset.sum_const, nsmul_eq_mul] at this
      nlinarith
    have hsum := Finset.add_sum_erase univ (fun b => μ / 2 * Real.exp (u' b) ^ 2 - u' b)
      (Finset.mem_univ a)
    have hge := scalingPot_ge hμ u'
    have := le_abs_self (scalingPot G 0)
    linarith

/-- **Lemma MO (scaling vector).**  Every positive definite real matrix `G` has a positive scaling
vector: `v_a > 0` and `v_a (G v)_a = 1` for all `a`.  Positive definiteness gives coercivity of
the potential; its symmetry part (`IsHermitian`) makes the gradient `G v − 1/v`. -/
theorem exists_scaling_of_posDef {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    ∃ v : ι → ℝ, (∀ a, 0 < v a) ∧ ∀ a, v a * (G *ᵥ v) a = 1 := by
  classical
  obtain ⟨u, hu⟩ := exists_min_scalingPot hG
  refine ⟨fun b => Real.exp (u b), fun b => Real.exp_pos _, fun a => ?_⟩
  have hsym : ∀ b c, G b c = G c b := fun b c => by
    have := hG.isHermitian.apply b c
    simpa using this.symm
  set δ : ι → ℝ := fun b => if b = a then 1 else 0 with hδ
  set φ : ℝ → ℝ := fun s => scalingPot G (fun b => u b + s * δ b) with hφ
  have hloc : IsLocalMin φ 0 := Filter.Eventually.of_forall fun s => by
    simp only [hφ, zero_mul, add_zero]; exact hu _
  -- derivative of each coordinate along the line
  have hF : ∀ b, HasDerivAt (fun s => Real.exp (u b + s * δ b)) (Real.exp (u b) * δ b) 0 := by
    intro b
    have h1 : HasDerivAt (fun s : ℝ => u b + s * δ b) (δ b) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ b)).const_add (u b)
    simpa using h1.exp
  have hD : HasDerivAt φ
      ((∑ b, (Real.exp (u b) * δ b * ∑ c, G b c * Real.exp (u c) +
        Real.exp (u b) * ∑ c, G b c * (Real.exp (u c) * δ c))) / 2 - ∑ b, δ b) 0 := by
    have hq : HasDerivAt (fun s => ∑ b, Real.exp (u b + s * δ b) *
        ∑ c, G b c * Real.exp (u c + s * δ c))
        (∑ b, (Real.exp (u b) * δ b * ∑ c, G b c * Real.exp (u c) +
          Real.exp (u b) * ∑ c, G b c * (Real.exp (u c) * δ c))) 0 := by
      have := HasDerivAt.fun_sum (u := univ) fun b _ =>
        (hF b).mul (HasDerivAt.fun_sum (u := univ) fun c _ => (hF c).const_mul (G b c))
      simpa using this
    have hl : HasDerivAt (fun s => ∑ b, (u b + s * δ b)) (∑ b, δ b) 0 := by
      have := HasDerivAt.fun_sum (u := univ) fun b _ =>
        (((hasDerivAt_id (0 : ℝ)).mul_const (δ b)).const_add (u b))
      simpa using this
    exact (hq.div_const 2).sub hl
  have h0 := hloc.hasDerivAt_eq_zero hD
  simp only [hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul, Finset.sum_add_distrib] at h0
  have hsw : ∑ x, Real.exp (u x) * (G x a * Real.exp (u a)) =
      Real.exp (u a) * ∑ c, G a c * Real.exp (u c) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by rw [hsym]; ring
  rw [hsw] at h0
  simp only [Matrix.mulVec, dotProduct]
  linarith

end CornerSnap
end Minimality
