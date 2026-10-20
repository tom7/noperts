module

public import Minimality.CycSeq

@[expose] public section

/-!
# The torque of a balanced force system does not depend on the view

Forces `f i` at shadow points `p i` with depths `z i`, balanced in force
(`∑ f i = 0`, E1) and in moment about horizontal axes (`∑ z i • f i = 0`,
E2): the torque `∑ p i × f i` is unchanged by `p i ↦ p i + z i • a + b`.
Changing the projection direction shears the shadow by exactly such a map,
so the torque can be computed in any view, e.g. in the view along the
segment between two of the corners, where those two collapse to one point
and contribute nothing (`sum_cross2_collapse`). See FEWER-FACES.md, the
rigidity-criterion TODO ("Shear lemma").
-/

namespace Minimality

/-- **Shear lemma.** -/
theorem sum_cross2_shear {ι : Type*} (s : Finset ι) (p f : ι → ℝ²) (z : ι → ℝ) (a b : ℝ²)
    (h1 : ∑ i ∈ s, f i = 0) (h2 : ∑ i ∈ s, z i • f i = 0) :
    ∑ i ∈ s, cross2 (p i + z i • a + b) (f i) = ∑ i ∈ s, cross2 (p i) (f i) := by
  have c : ∀ k : Fin 2, ∑ i ∈ s, f i k = 0 := fun k => by
    have := congrArg (fun v : ℝ² => v k) h1
    simpa [WithLp.ofLp_sum, Finset.sum_apply] using this
  have d : ∀ k : Fin 2, ∑ i ∈ s, z i * f i k = 0 := fun k => by
    have := congrArg (fun v : ℝ² => v k) h2
    simpa [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] using this
  have e : ∀ i, cross2 (p i + z i • a + b) (f i) = cross2 (p i) (f i) +
      (a 0 * (z i * f i 1) - a 1 * (z i * f i 0)) + (b 0 * f i 1 - b 1 * f i 0) := fun i => by
    simp only [cross2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, d 0, d 1, c 0, c 1]
  ring

/-- **The torque in the view along two corners.** Shearing by the direction
of the segment from corner `i₀` to corner `j₀` (depths differ) and moving
`i₀` to the origin puts both at the origin; the torque is unchanged. -/
theorem sum_cross2_collapse {ι : Type*} (s : Finset ι) (p f : ι → ℝ²) (z : ι → ℝ)
    (h1 : ∑ i ∈ s, f i = 0) (h2 : ∑ i ∈ s, z i • f i = 0) (i₀ j₀ : ι) (hz : z i₀ ≠ z j₀) :
    let a : ℝ² := -((z j₀ - z i₀)⁻¹ • (p j₀ - p i₀))
    let q : ι → ℝ² := fun i => p i + z i • a + (-(p i₀) - z i₀ • a)
    q i₀ = 0 ∧ q j₀ = 0 ∧ ∑ i ∈ s, cross2 (q i) (f i) = ∑ i ∈ s, cross2 (p i) (f i) := by
  intro a q
  have hd : z j₀ - z i₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  refine ⟨by simp [q], ?_, sum_cross2_shear s p f z a _ h1 h2⟩
  show p j₀ + z j₀ • a + (-(p i₀) - z i₀ • a) = 0
  have : p j₀ + z j₀ • a + (-(p i₀) - z i₀ • a) = (p j₀ - p i₀) + (z j₀ - z i₀) • a := by
    rw [sub_smul]; abel
  rw [this, smul_neg, smul_smul, mul_inv_cancel₀ hd, one_smul, add_neg_cancel]

/-- **Three-level rule** (FEWER-FACES-PROOFS.md, Proposition 8.3). Group
resultants `R k` at three depths `d k`, balanced in force (E1) and in moment
about horizontal axes (E2): they are parallel, `R₁ = (d₂ - d₀) • w`,
`R₂ = (d₀ - d₁) • w` with `w = (d₁ - d₂)⁻¹ • R₀`, and the torque of the
groups (resultants on lines through `q k`) is `(Σ (d_{k+1} - d_{k+2}) q k) × w`,
twice the signed area of the triangle of the points (depth, offset) up to the
factor `|w|²`. -/
theorem three_level_resultants (R₀ R₁ R₂ : ℝ²) (d₀ d₁ d₂ : ℝ) (hd : d₁ ≠ d₂)
    (h1 : R₀ + R₁ + R₂ = 0) (h2 : d₀ • R₀ + d₁ • R₁ + d₂ • R₂ = 0) :
    R₁ = (d₂ - d₀) • ((d₁ - d₂)⁻¹ • R₀) ∧ R₂ = (d₀ - d₁) • ((d₁ - d₂)⁻¹ • R₀) := by
  have hd' : d₁ - d₂ ≠ 0 := sub_ne_zero.mpr hd
  have c : ∀ k : Fin 2, R₀ k + R₁ k + R₂ k = 0 := fun k => by
    have := congrArg (fun v : ℝ² => v k) h1; simpa using this
  have e : ∀ k : Fin 2, d₀ * R₀ k + d₁ * R₁ k + d₂ * R₂ k = 0 := fun k => by
    have := congrArg (fun v : ℝ² => v k) h2; simpa using this
  constructor <;> ext k <;> simp only [PiLp.smul_apply, smul_eq_mul]
  · rw [show (d₂ - d₀) * ((d₁ - d₂)⁻¹ * R₀ k) = (d₂ - d₀) * R₀ k / (d₁ - d₂) by ring,
      eq_div_iff hd']
    linear_combination (-d₂) * c k + e k
  · rw [show (d₀ - d₁) * ((d₁ - d₂)⁻¹ * R₀ k) = (d₀ - d₁) * R₀ k / (d₁ - d₂) by ring,
      eq_div_iff hd']
    linear_combination d₁ * c k - e k

theorem three_level_torque (R₀ R₁ R₂ q₀ q₁ q₂ : ℝ²) (d₀ d₁ d₂ : ℝ) (hd : d₁ ≠ d₂)
    (h1 : R₀ + R₁ + R₂ = 0) (h2 : d₀ • R₀ + d₁ • R₁ + d₂ • R₂ = 0) :
    cross2 q₀ R₀ + cross2 q₁ R₁ + cross2 q₂ R₂ =
      cross2 ((d₁ - d₂) • q₀ + (d₂ - d₀) • q₁ + (d₀ - d₁) • q₂) ((d₁ - d₂)⁻¹ • R₀) := by
  obtain ⟨e1, e2⟩ := three_level_resultants R₀ R₁ R₂ d₀ d₁ d₂ hd h1 h2
  have hd' : d₁ - d₂ ≠ 0 := sub_ne_zero.mpr hd
  rw [e1, e2]
  simp only [cross2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

end Minimality

end
