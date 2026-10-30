module

public import Minimality.Type08S.P2TDefs

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- A frequent limit of `NWS4` depth vectors at an injective limit is `NWS4`. -/
theorem nws4_of_tendsto {zs : ℕ → ZMod 4 → ℝ} {z : ZMod 4 → ℝ} (h : Tendsto zs atTop (𝓝 z))
    (hinj : Function.Injective z) (hn : ∃ᶠ n in atTop, NWS4 (zs n)) : NWS4 z := by
  have hev : ∀ᶠ n in atTop, ∀ i j : ZMod 4, i ≠ j → z j < z i → zs n j < zs n i := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun n h => absurd hij h
    by_cases hlt : z j < z i
    · exact (h.eventually ((isOpen_lt (continuous_apply j) (continuous_apply i)).mem_nhds (show z ∈ {w : ZMod 4 → ℝ | w j < w i} from hlt))).mono
        fun n hn _ _ => hn
    · exact Filter.Eventually.of_forall fun n h hh => absurd hh hlt
  obtain ⟨n, hn1, hn2⟩ := (hn.and_eventually hev).exists
  have back : ∀ i j : ZMod 4, i ≠ j → zs n i < zs n j → z i < z j := by
    intro i j hij hl
    by_contra hc
    have hne : z i ≠ z j := hinj.ne hij
    have : z j < z i := lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
    have := hn2 i j hij this
    linarith
  obtain ⟨h1, h2⟩ := hn1
  refine ⟨?_, ?_⟩
  · rcases h1 with k | k | k | k
    · exact Or.inl (back _ _ (by decide) k)
    · exact Or.inr (Or.inl (back _ _ (by decide) k))
    · exact Or.inr (Or.inr (Or.inl (back _ _ (by decide) k)))
    · exact Or.inr (Or.inr (Or.inr (back _ _ (by decide) k)))
  · rcases h2 with k | k | k | k
    · exact Or.inl (back _ _ (by decide) k)
    · exact Or.inr (Or.inl (back _ _ (by decide) k))
    · exact Or.inr (Or.inr (Or.inl (back _ _ (by decide) k)))
    · exact Or.inr (Or.inr (Or.inr (back _ _ (by decide) k)))

theorem inj_eventually {zs : ℕ → ZMod 4 → ℝ} {z : ZMod 4 → ℝ} (h : Tendsto zs atTop (𝓝 z))
    (hinj : Function.Injective z) : ∀ᶠ n in atTop, Function.Injective (zs n) := by
  have : ∀ᶠ n in atTop, ∀ i j : ZMod 4, i ≠ j → zs n i ≠ zs n j := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun n h => absurd hij h
    · have h1 := ((tendsto_pi_nhds.1 h i).sub (tendsto_pi_nhds.1 h j))
      have := h1.eventually_ne (sub_ne_zero.2 (hinj.ne hij))
      exact this.mono fun n hn _ => sub_ne_zero.1 hn
  exact this.mono fun n hn a b hab => by_contra fun hne => hn a b hne hab

theorem lim_unimodal {D : (Fin 6 → ℝ) → ZMod 4 → ℝ} (hc : Continuous D) {θs : ℕ → Fin 6 → ℝ}
    {θ : Fin 6 → ℝ} (hθs : Tendsto θs atTop (𝓝 θ)) (hinj : Function.Injective (D θ))
    (hf : ∃ᶠ n in atTop, IsCyclicUnimodal (D (θs n))) : IsCyclicUnimodal (D θ) :=
  isCyclicUnimodal_of_NWS4 hinj (nws4_of_tendsto ((hc.tendsto θ).comp hθs) hinj
    (hf.mono fun n h => nws_of_unimodal4 h))

/-- **MF for N2 at `θ 5 = 1`** (limit of `N2_core` from `θ 5 > 1`). -/
theorem N2_core_T (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (h5 : θ 5 = 1) (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hinj : ∀ j, Function.Injective ((test08 0 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ))) :
    ∃ j, IsCyclicUnimodal ((test08 0 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
  classical
  set θs : ℕ → Fin 6 → ℝ := fun n => θ + (1 / ((n : ℝ) + 1)) • (Pi.single 5 1 : Fin 6 → ℝ) with hθsdef
  have hθs : Tendsto θs atTop (𝓝 θ) := by
    have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • (Pi.single 5 1 : Fin 6 → ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (Pi.single 5 1 : Fin 6 → ℝ)
    simpa [hθsdef] using (tendsto_const_nhds (x := θ)).add h0
  have hθ5 : ∀ n, 1 < θs n 5 := by
    intro n
    simp only [hθsdef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, h5]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hineq : ∀ᶠ n in atTop, ∀ k, 0 < ineq08 (θs n) k := by
    rw [Filter.eventually_all]
    intro k
    exact (((continuous_ineq08 k).tendsto θ).comp hθs).eventually (lt_mem_nhds (hθ k))
  set x : (Fin 6 → ℝ) → Fin 7 → ℝ³ := fun θ' => nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ' with hx
  have hxc : ∀ m, Continuous fun θ' => x θ' m := fun m =>
    (continuous_apply m).comp (continuous_nf08 (L o) (L E₁) (L E₂) (L E₃))
  have hd : ∀ m p q : Fin 7, Continuous fun θ' => ⟪x θ' m, x θ' p - x θ' q⟫ := fun m p q =>
    (hxc m).inner ((hxc p).sub (hxc q))
  set D1 : (Fin 6 → ℝ) → ZMod 4 → ℝ := fun θ' =>
    quad ⟪x θ' 4, x θ' 4 - x θ' 1⟫ ⟪x θ' 2, x θ' 4 - x θ' 1⟫ ⟪x θ' 5, x θ' 4 - x θ' 1⟫
      ⟪x θ' 3, x θ' 4 - x θ' 1⟫ with hD1
  set D2 : (Fin 6 → ℝ) → ZMod 4 → ℝ := fun θ' =>
    quad ⟪x θ' 1, x θ' 4 - x θ' 1⟫ ⟪x θ' 2, x θ' 4 - x θ' 1⟫ ⟪x θ' 5, x θ' 4 - x θ' 1⟫
      ⟪x θ' 3, x θ' 4 - x θ' 1⟫ with hD2
  have quad_c : ∀ {f0 f1 f2 f3 : (Fin 6 → ℝ) → ℝ}, Continuous f0 → Continuous f1 → Continuous f2 →
      Continuous f3 → Continuous fun θ' => quad (f0 θ') (f1 θ') (f2 θ') (f3 θ') := by
    intro f0 f1 f2 f3 c0 c1 c2 c3
    refine continuous_pi fun i => ?_
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simpa [quad_0, quad_1, quad_2, quad_3]
  have hD1c : Continuous D1 := quad_c (hd 4 4 1) (hd 2 4 1) (hd 5 4 1) (hd 3 4 1)
  have hD2c : Continuous D2 := quad_c (hd 1 4 1) (hd 2 4 1) (hd 5 4 1) (hd 3 4 1)
  have e1 : ∀ θ', (test08 0 true true).depth (x θ') = D1 θ' := by
    intro θ'; funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have e2 : ∀ θ', (test08 0 true false).depth (x θ') = D2 θ' := by
    intro θ'; funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have hi1 : Function.Injective (D1 θ) := by have := hinj true; rwa [show nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ = x θ from rfl, e1] at this
  have hi2 : Function.Injective (D2 θ) := by have := hinj false; rwa [show nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ = x θ from rfl, e2] at this
  have hinjev : ∀ᶠ n in atTop, Function.Injective (D1 (θs n)) ∧ Function.Injective (D2 (θs n)) := by
    filter_upwards [inj_eventually ((hD1c.tendsto θ).comp hθs) hi1,
      inj_eventually ((hD2c.tendsto θ).comp hθs) hi2] with n h1 h2 using ⟨h1, h2⟩
  have hex : ∀ᶠ n in atTop, IsCyclicUnimodal (D1 (θs n)) ∨ IsCyclicUnimodal (D2 (θs n)) := by
    filter_upwards [hineq, hinjev] with n h1 h2
    have hi : ∀ j, Function.Injective ((test08 0 true j).depth
        (nfShape08 (L o) (L E₁) (L E₂) (L E₃) (θs n))) := by
      intro j; cases j
      · exact (e2 (θs n)).symm ▸ h2.2
      · exact (e1 (θs n)).symm ▸ h2.1
    obtain ⟨j, hj⟩ := N2_core o E₁ E₂ E₃ hE (θs n) h1 (hθ5 n) L hL hi
    cases j
    · right; rwa [e2] at hj
    · left; rwa [e1] at hj
  rcases Filter.frequently_or_distrib.1 hex.frequently with h | h
  · exact ⟨true, by rw [show nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ = x θ from rfl, e1]; exact lim_unimodal hD1c hθs hi1 h⟩
  · exact ⟨false, by rw [show nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ = x θ from rfl, e2]; exact lim_unimodal hD2c hθs hi2 h⟩

end Type08Sp
end Minimality

