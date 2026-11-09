module

public import Mathlib
public import MinimalityExtra

/-!
# Lemma VF: vertices over the boundary of a shadow
-/

@[expose] public section

namespace MinimalityExtra

open scoped RealInnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- If `z ≠ y` have the same projection along `u`, then `u` is a multiple of `z - y`. -/
private lemma vf_dir (u z y : ℝ³) (hne : z ≠ y)
    (h : z - (⟪z, u⟫ / ⟪u, u⟫) • u = y - (⟪y, u⟫ / ⟪u, u⟫) • u) :
    u ∈ Submodule.span ℝ {z - y} := by
  set s : ℝ := ⟪z, u⟫ / ⟪u, u⟫ - ⟪y, u⟫ / ⟪u, u⟫ with hs
  have h2 : z - y = s • u := by
    rw [hs]; linear_combination (norm := module) h
  have hs0 : s ≠ 0 := by
    intro h0; apply hne; rw [h0, zero_smul] at h2; exact sub_eq_zero.mp h2
  have : u = s⁻¹ • (z - y) := by rw [h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma vf_inner (n u x : ℝ³) (hn : ⟪n, u⟫ = 0) :
    ⟪n, x - (⟪x, u⟫ / ⟪u, u⟫) • u⟫ = ⟪n, x⟫ := by
  rw [inner_sub_right, inner_smul_right, hn]; simp

private lemma vf_lin (u x1 x2 : ℝ³) (s t : ℝ) :
    (s • x1 + t • x2) - (⟪s • x1 + t • x2, u⟫ / ⟪u, u⟫) • u =
      s • (x1 - (⟪x1, u⟫ / ⟪u, u⟫) • u) + t • (x2 - (⟪x2, u⟫ / ⟪u, u⟫) • u) := by
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  rw [add_div, mul_div_assoc, mul_div_assoc]
  module

theorem vertexOverBoundaryOnFaceAlongView : VertexOverBoundaryOnFaceAlongView := by
  intro V u n y hn0 hnu hy hsup hnot
  set K := convexHull ℝ (V : Set ℝ³) with hK
  set P : ℝ³ → ℝ³ := fun x => x - (⟪x, u⟫ / ⟪u, u⟫) • u with hP
  have hyK : y ∈ K := hy.1
  have hPn : ∀ x, ⟪n, P x⟫ = ⟪n, x⟫ := fun x => vf_inner n u x hnu
  -- the conclusion from a second point of the face over the same point
  have key : ∀ z ∈ K, ⟪n, z⟫ = ⟪n, y⟫ → z ≠ y → P z = P y →
      u ∈ vectorSpan ℝ {x ∈ K | ⟪n, x⟫ = ⟪n, y⟫} := by
    intro z hz hnz hne hPz
    have h1 : z - y ∈ vectorSpan ℝ {x ∈ K | ⟪n, x⟫ = ⟪n, y⟫} :=
      vsub_mem_vectorSpan ℝ (show z ∈ _ from ⟨hz, hnz⟩) (show y ∈ _ from ⟨hyK, rfl⟩)
    have h2 := vf_dir u z y hne hPz
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr h1 h2
  by_cases hc : P y ∈ (P '' K).extremePoints ℝ
  · -- another vertex lies over `P y`
    have h2 : ¬ ∀ y' ∈ K.extremePoints ℝ, P y' = P y → y' = y := fun h => hnot ⟨hc, h⟩
    push_neg at h2
    obtain ⟨y', hy', hPy', hne⟩ := h2
    refine key y' hy'.1 ?_ hne hPy'
    rw [← hPn y', hPy', hPn]
  · -- `P y` is not a corner of the shadow
    have hPy : P y ∈ P '' K := ⟨y, hyK, rfl⟩
    rw [mem_extremePoints] at hc
    push_neg at hc
    obtain ⟨a, ha, b, hb, hab, hne⟩ := hc hPy
    obtain ⟨x1, hx1, rfl⟩ := ha
    obtain ⟨x2, hx2, rfl⟩ := hb
    obtain ⟨s, t, hs, ht, hst, hseg⟩ := hab
    set z := s • x1 + t • x2 with hz
    have hzK : z ∈ K := (convex_convexHull ℝ _) hx1 hx2 hs.le ht.le hst
    have hPz : P z = P y := by
      rw [← hseg]; exact vf_lin u x1 x2 s t
    have hnz : ⟪n, z⟫ = ⟪n, y⟫ := by rw [← hPn z, hPz, hPn]
    have hne1 : z ≠ y := by
      intro hzy
      have hseg' : y ∈ openSegment ℝ x1 x2 := ⟨s, t, hs, ht, hst, by rw [← hzy]⟩
      have e1 := hy.2 hx1 hx2 hseg'
      have e2 := hy.2 hx2 hx1 (by rwa [openSegment_symm])
      exact hne (by rw [e1]) (by rw [e2])
    exact key z hzK hnz hne1 hPz

end MinimalityExtra
