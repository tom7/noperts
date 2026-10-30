module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.P2QQ1b
public import Minimality.VtxMain

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q2a: MF by limit: `N2_core_w`, `T4_core_w` (statements as in PQ0).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Abstract MF by limit: two families of 4-cycles continuous in the parameter, injective at the limit,
cyclic unimodal for one of them at the approximants (eventually, whenever both are injective) ⟹ at the limit. -/
theorem mf_by_limit (z : Bool → (Fin 6 → ℝ) → ZMod 4 → ℝ) (hc : ∀ j i, Continuous fun θ => z j θ i)
    {θ : Fin 6 → ℝ} {θs : ℕ → Fin 6 → ℝ} (hθs : Tendsto θs atTop (𝓝 θ))
    (hinj : ∀ j, Function.Injective (z j θ))
    (core : ∀ᶠ n in atTop, (∀ j, Function.Injective (z j (θs n))) → ∃ j, IsCyclicUnimodal (z j (θs n))) :
    ∃ j, IsCyclicUnimodal (z j θ) := by
  have hlim : ∀ j i, Tendsto (fun n => z j (θs n) i) atTop (𝓝 (z j θ i)) := fun j i =>
    ((hc j i).tendsto θ).comp hθs
  have evinj : ∀ j, ∀ᶠ n in atTop, Function.Injective (z j (θs n)) := by
    intro j
    have h1 : ∀ p : ZMod 4 × ZMod 4, ∀ᶠ n in atTop, p.1 ≠ p.2 → z j (θs n) p.1 ≠ z j (θs n) p.2 := by
      intro p
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun n h => absurd hp h
      · have hne : z j θ p.1 ≠ z j θ p.2 := fun e => hp (hinj j e)
        exact (((hlim j p.1).sub (hlim j p.2)).eventually_ne (sub_ne_zero.mpr hne)).mono fun n h _ => sub_ne_zero.mp h
    have h2 := eventually_all.mpr h1
    refine h2.mono fun n h a b hab => ?_
    by_contra hne
    exact h (a, b) hne hab
  have hall : ∀ᶠ n in atTop, (∀ j, Function.Injective (z j (θs n))) :=
    eventually_all.mpr evinj
  have hex : ∀ᶠ n in atTop, ∃ j, IsCyclicUnimodal (z j (θs n)) :=
    (core.and hall).mono fun n ⟨h, h'⟩ => h h'
  obtain ⟨j, hj⟩ := frequently_exists_of_finite hex.frequently
  refine ⟨j, isCyclicUnimodal_of_NWS4 (hinj j) ?_⟩
  exact nws4_of_tendsto (tendsto_pi_nhds.mpr (hlim j)) (hinj j) (hj.mono fun n h => nws4_of_cyclic h)

theorem depth_cont08 (i : Fin 3) (s j : Bool) (k : ZMod (test08 i s j).k) (o E₁ E₂ E₃ : ℝ³) :
    Continuous fun θ => (test08 i s j).depth (nfShape08 o E₁ E₂ E₃ θ) k := by
  have hn := continuous_nf08 o E₁ E₂ E₃
  have h1 : Continuous fun θ => nfShape08 o E₁ E₂ E₃ θ ((test08 i s j).lab k) :=
    (continuous_apply _).comp hn
  exact h1.inner ((covView_test08 i s j).1.comp hn)


theorem N2_core_w (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : Ineq08w θ) (h6 : 1 < θ 5) (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hinj : ∀ j, Function.Injective ((test08 0 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ))) :
    ∃ j, IsCyclicUnimodal ((test08 0 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
  obtain ⟨θs, hθs, hstr, -⟩ := exists_seq_strict θ hθ
  let z : Bool → (Fin 6 → ℝ) → ZMod 4 → ℝ := fun j θ' =>
    match j with
    | true => (test08 0 true true).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ')
    | false => (test08 0 true false).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ')
  have hc : ∀ j i, Continuous fun θ' => z j θ' i := by
    intro j i; cases j
    · exact depth_cont08 0 true false i _ _ _ _
    · exact depth_cont08 0 true true i _ _ _ _
  have c5 : Tendsto (fun n => θs n 5) atTop (𝓝 (θ 5)) := ((continuous_apply 5).tendsto θ).comp hθs
  have h := mf_by_limit z hc hθs (fun j => by cases j; exacts [hinj false, hinj true])
    ((hstr.and (c5.eventually (lt_mem_nhds h6))).mono fun n ⟨hs, h5⟩ hi => by
      obtain ⟨j, hj⟩ := N2_core o E₁ E₂ E₃ hE (θs n) hs h5 L hL (fun j => by
        cases j
        · exact hi false
        · exact hi true)
      exact ⟨j, by cases j <;> exact hj⟩)
  obtain ⟨j, hj⟩ := h
  exact ⟨j, by cases j <;> exact hj⟩

theorem T4_core_w (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : Ineq08w θ) (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hinj : ∀ j, Function.Injective ((test08 1 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ))) :
    ∃ j, IsCyclicUnimodal ((test08 1 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
  obtain ⟨θs, hθs, hstr, -⟩ := exists_seq_strict θ hθ
  let z : Bool → (Fin 6 → ℝ) → ZMod 4 → ℝ := fun j θ' =>
    match j with
    | true => (test08 1 true true).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ')
    | false => (test08 1 true false).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ')
  have hc : ∀ j i, Continuous fun θ' => z j θ' i := by
    intro j i; cases j
    · exact depth_cont08 1 true false i _ _ _ _
    · exact depth_cont08 1 true true i _ _ _ _
  have h := mf_by_limit z hc hθs (fun j => by cases j; exacts [hinj false, hinj true])
    (hstr.mono fun n hs hi => by
      obtain ⟨j, hj⟩ := T4_core o E₁ E₂ E₃ hE (θs n) hs L hL (fun j => by
        cases j
        · exact hi false
        · exact hi true)
      exact ⟨j, by cases j <;> exact hj⟩)
  obtain ⟨j, hj⟩ := h
  exact ⟨j, by cases j <;> exact hj⟩

end Type08Sp
end Minimality
