module

public import Minimality.Generic.CayleyJetA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Polynomial

namespace Minimality

/-- Cayley vector `c(s)`. -/
noncomputable def cayleyJetC (c : Fin 3 → ℝ[X]) (s : ℝ) : ℝ³ := !₂[(c 0).eval s, (c 1).eval s, (c 2).eval s]
/-- Screen translation `τ(s)`. -/
noncomputable def cayleyJetT (τ : Fin 2 → ℝ[X]) (s : ℝ) : ℝ² := !₂[(τ 0).eval s, (τ 1).eval s]

/-- Numerator polynomial: `(1+|c|²)(⟪n, P(cayley c · v) + τ⟫ − h)` with `cayley c` the matrix of this library
(Cayley vector `c`, not `c/2`): `cayley c v = ((1-|c|²) v + 2 (c·v) c + 2 c × v)/(1+|c|²)`. -/
noncomputable def cayleyJetN (n : ℝ²) (h : ℝ) (c : Fin 3 → ℝ[X]) (τ : Fin 2 → ℝ[X]) (v : ℝ³) : ℝ[X] :=
  let cp : ℝ[X] := c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2
  let cd : ℝ[X] := C (v 0) * c 0 + C (v 1) * c 1 + C (v 2) * c 2
  let w0 : ℝ[X] := (1 - cp) * C (v 0) + 2 * cd * c 0 + 2 * (c 1 * C (v 2) - c 2 * C (v 1))
  let w1 : ℝ[X] := (1 - cp) * C (v 1) + 2 * cd * c 1 + 2 * (c 2 * C (v 0) - c 0 * C (v 2))
  C (n 0) * w0 + C (n 1) * w1 + (1 + cp) * (C (n 0) * τ 0 + C (n 1) * τ 1 - C h)

theorem cayleyJet_eval (n : ℝ²) (h : ℝ) (c : Fin 3 → ℝ[X]) (τ : Fin 2 → ℝ[X]) (v : ℝ³) (s : ℝ) :
    (cayleyJetN n h c τ v).eval s =
      cayleyDen (cayleyJetC c s) * (⟪n, proj_xy ((cayley (cayleyJetC c s)).toEuclideanLin v) + cayleyJetT τ s⟫ - h) := by
  have hd := (cayleyDen_pos (cayleyJetC c s)).ne'
  rw [cayley_apply]
  simp only [cayleyJetN, cayleyJetC, cayleyJetT, cayleyDen, crossMatrix, inner_add_right,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at *
  simp [proj_xy, PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail] at *
  field_simp
  ring

/-- **k-jet criterion.** Along the polynomial Cayley curve `c(s)` with screen offset `τ(s)`, if every
(vertex, edge) numerator has negative trailing coefficient, `V` is Rupert. -/
theorem isRupert_of_cayleyPolyJet (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (c : Fin 3 → ℝ[X]) (τ : Fin 2 → ℝ[X])
    (hlex : ∀ v ∈ V, ∀ e, (cayleyJetN (n e) (h e) c τ v).trailingCoeff < 0) :
    IsRupert V := by
  set S := proj_xy '' convexHull ℝ (V : Set ℝ³) with hSdef
  have hS : Convex ℝ S := by
    rw [hSdef, show (proj_xy : ℝ³ → ℝ²) = projL from rfl]
    exact (convex_convexHull ℝ _).linear_image projL
  have hopen : IsOpen {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} := by
    have : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} = ⋂ e, {y : ℝ² | ⟪n e, y⟫ < h e} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun e => isOpen_lt (by fun_prop) continuous_const
  have hU : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ interior S := interior_maximal hpoly hopen
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ v ∈ V, ∀ e,
      ⟪n e, cayleyJetT τ s + proj_xy ((cayley (cayleyJetC c s)).toEuclideanLin v)⟫ < h e := by
    rw [eventually_all_finset]
    intro v hv
    rw [eventually_all]
    intro e
    filter_upwards [cayleyJet_eventually_neg _ (hlex v hv e)] with s hs
    rw [cayleyJet_eval] at hs
    have hd := cayleyDen_pos (cayleyJetC c s)
    have : ⟪n e, proj_xy ((cayley (cayleyJetC c s)).toEuclideanLin v) + cayleyJetT τ s⟫ - h e < 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    rw [add_comm]; linarith
  obtain ⟨s, hs⟩ := hev.exists
  refine (isRupert_iff_shadows V).mpr ⟨cayley (cayleyJetC c s), cayley_mem_SO3 _,
    cayleyJetT τ s, 1, one_mem _, ?_⟩
  rw [outerShadow_one, innerShadow_convexHull]
  refine convexHull_min ?_ hS.interior
  rintro _ ⟨v, hv, rfl⟩
  exact hU (fun e => hs v hv e)

end Minimality
