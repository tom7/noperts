module

public import Minimality.ManyTies

@[expose] public section

/-!
# From an affine-invariant certificate cover to metric-freeness (`FEWER-FACES-PROOFS.md` §24.3)

Theorem 24.3 (`ManyTies.lean`) needs its two rims `X, X′` to be *metric-free*: at the depth
functionals `G u`, `G u′` of metrics `G` near `I` at which the labels of both rims have distinct
depths, `X` or `X′` is cyclically unimodal.  A type's certificate cover is stated for every
point set realizing the type; a linear image `M ∘ x` of a realization (`M` invertible) realizes
the same type, so it is certified, and its certificates at the views `c M u` have the depths
`⟪x i, G u⟫` with `G = Mᵀ M`.  This file proves, for an abstract finite family `Q` of labelled
certificates, that the cover gives metric-freeness along a curve of metrics, or else `x` is Rupert
(by the limit lemma `isRupert_of_tendsto_rimCert`).

* `WeakLeft`: the closed part of `RimCertAt.left` (it passes to limits).
* `metricFree_of_cover`: **the bridge**.  Hypotheses: the cover (`hApprox`: for small `ε` the
  linear image `M ε ∘ x` is a limit of shapes carrying one of the certificates `q`), the pair of
  certificate classes `P₁, P₂` of the two tests (rotations or reflections of the test rims at the
  same views), and the escape for all other certificates that survive in the limit
  (`hO`: no horizontal double normal at their view and distinct depths of their labels).
* `pair_contra`: the case of a certificate of a test: the limit rim is robustly unimodal.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Small lemmas -/

theorem IsRobustUnimodal.rot {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) (r : ZMod k) :
    IsRobustUnimodal (fun i => z (i + r)) where
  noPeaks B a b c d hab hbc hcd hdk h := by
    refine hz.noPeaks (B + r) a b c d hab hbc hcd hdk ?_
    simp only [show ∀ t : ℕ, B + (t : ZMod k) + r = B + r + (t : ZMod k) from fun t => by ring]
      at h
    exact h
  noTriple i j l hij hjl hil e1 e2 :=
    hz.noTriple (i + r) (j + r) (l + r) (fun h => hij (add_right_cancel h))
      (fun h => hjl (add_right_cancel h)) (fun h => hil (add_right_cancel h)) e1 e2
  noLevelRun B a b c d hab hbc hcd hdk e := by
    have := hz.noLevelRun (B + r) a b c d hab hbc hcd hdk (by
      simpa only [show ∀ t : ℕ, B + (t : ZMod k) + r = B + r + (t : ZMod k) from fun t => by ring]
        using e)
    simpa only [show ∀ t : ℕ, B + (t : ZMod k) + r = B + r + (t : ZMod k) from fun t => by ring]
      using this

/-- The closed part of `RimCertAt.left`: every point of `x` is weakly left of every side of the
labelled polygon.  It passes to limits of shapes carrying the certificate. -/
def WeakLeft {n k : ℕ} (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  ∀ (m : Fin n) (i : ZMod k), 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- The closed part of `RimCertAt` that passes to limits: all points weakly left of every side,
and every triple of labels in cyclic order is weakly counterclockwise. -/
def WeakRim {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  WeakLeft x u lab ∧ ∀ a b c : ZMod k, CycBetween a b c →
    0 ≤ det3 (x (lab b) - x (lab a)) (x (lab c) - x (lab a)) u

/-- The labels of a rim certificate are distinct (a strictly convex polygon). -/
theorem RimCertAt.injective_lab {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimCertAt x u lab) : Function.Injective lab := by
  have hz : ∀ a : ℝ³, det3 0 a u = 0 := fun a => by simp [det3_expand]
  have hz' : ∀ a : ℝ³, det3 a 0 u = 0 := fun a => by simp [det3_expand]
  intro i j hij
  by_contra hne
  by_cases hj : j = i + 1
  · subst hj
    have := h.cyc i (i - 1) (zmod_sub_one_ne h.three i) (zmod_sub_one_ne_add_one h.three i)
    rw [← hij, sub_self, hz] at this
    exact lt_irrefl _ this
  · have := h.cyc i j (Ne.symm hne) hj
    rw [hij, sub_self, hz'] at this
    exact lt_irrefl _ this

/-- **Same sign for the exact and the first-order depth difference** (genericity): if
`A = 0 → B ≠ 0`, then `A + εB + ε²C` and `A + εB` are nonzero of the same sign for small
`ε > 0`. -/
theorem eventually_pos_mul_quad {A B C : ℝ} (h : A = 0 → B ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (A + ε * B + ε ^ 2 * C) * (A + ε * B) := by
  by_cases hA : A = 0
  · subst hA
    have hB := h rfl
    have hc : Continuous fun ε : ℝ => B * (B + ε * C) := by fun_prop
    have h0 : 0 < B * (B + 0 * C) := by
      have := mul_self_pos.mpr hB
      simpa using this
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < B * (B + ε * C) :=
      (hc.continuousAt.eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev, self_mem_nhdsWithin] with ε h1 h2
    have h2' : 0 < ε := h2
    have : (0 + ε * B + ε ^ 2 * C) * (0 + ε * B) = ε ^ 2 * (B * (B + ε * C)) := by ring
    rw [this]
    positivity
  · have hc : Continuous fun ε : ℝ => (A + ε * B + ε ^ 2 * C) * (A + ε * B) := by fun_prop
    have h0 : 0 < (A + 0 * B + 0 ^ 2 * C) * (A + 0 * B) := by
      have := mul_self_pos.mpr hA
      simpa using this
    exact (hc.continuousAt.eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds

/-- **Order transfer for a second-order tilt**: for a good tilt `g` of the rim `X` at `u`, the
depths along `u + εg + ε²r` are injective for small `ε > 0`, and their strict order refines the
strict order of the depths along `u + εg`. -/
theorem eventually_order_tilt {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (u g r : ℝ³)
    (hg : GoodTilt X u g) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪X i, u + ε • g + ε ^ 2 • r⟫) ∧
      ∀ i j, ⟪X i, u + ε • g + ε ^ 2 • r⟫ < ⟪X j, u + ε • g + ε ^ 2 • r⟫ →
        ⟪X i, u + ε • g⟫ < ⟪X j, u + ε • g⟫ := by
  have hpair : ∀ q : ZMod k × ZMod k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), q.1 ≠ q.2 →
      0 < (⟪X q.1 - X q.2, u⟫ + ε * ⟪X q.1 - X q.2, g⟫ + ε ^ 2 * ⟪X q.1 - X q.2, r⟫) *
        (⟪X q.1 - X q.2, u⟫ + ε * ⟪X q.1 - X q.2, g⟫) := by
    intro q
    by_cases hq : q.1 = q.2
    · exact Eventually.of_forall fun _ h => absurd hq h
    · exact (eventually_pos_mul_quad (fun h => hg q.1 q.2 hq h)).mono fun _ h _ => h
  filter_upwards [eventually_all.2 hpair] with ε hε
  have e1 : ∀ i j, ⟪X i, u + ε • g + ε ^ 2 • r⟫ - ⟪X j, u + ε • g + ε ^ 2 • r⟫ =
      ⟪X i - X j, u⟫ + ε * ⟪X i - X j, g⟫ + ε ^ 2 * ⟪X i - X j, r⟫ := by
    intro i j
    simp only [inner_sub_left, inner_add_right, real_inner_smul_right]; ring
  have e2 : ∀ i j, ⟪X i, u + ε • g⟫ - ⟪X j, u + ε • g⟫ =
      ⟪X i - X j, u⟫ + ε * ⟪X i - X j, g⟫ := by
    intro i j
    simp only [inner_sub_left, inner_add_right, real_inner_smul_right]; ring
  constructor
  · intro i j hij
    by_contra hne
    have := hε (i, j) hne
    have h0 : ⟪X i - X j, u⟫ + ε * ⟪X i - X j, g⟫ + ε ^ 2 * ⟪X i - X j, r⟫ = 0 := by
      rw [← e1]; simp only at hij; rw [hij]; ring
    simp only at this
    rw [h0, zero_mul] at this
    exact lt_irrefl _ this
  · intro i j hlt
    by_cases hij : i = j
    · subst hij; exact absurd hlt (lt_irrefl _)
    · have hp := hε (i, j) hij
      simp only at hp
      rw [← e1, ← e2] at hp
      have h1 : ⟪X i, u + ε • g + ε ^ 2 • r⟫ - ⟪X j, u + ε • g + ε ^ 2 • r⟫ < 0 := by linarith
      have h2 : ⟪X i, u + ε • g⟫ - ⟪X j, u + ε • g⟫ < 0 := by
        by_contra h2
        push Not at h2
        nlinarith
      linarith

/-! ### A generic symmetric operator for a family of tests -/

/-- The symmetric operators of `ℝ³`, as a submodule of the continuous linear maps. -/
def SymOp : Submodule ℝ (ℝ³ →L[ℝ] ℝ³) where
  carrier := {H | ∀ a b, ⟪H a, b⟫ = ⟪a, H b⟫}
  add_mem' := fun {H K} hH hK a b => by
    simp only [add_apply, inner_add_left, inner_add_right, hH a b, hK a b]
  zero_mem' := fun a b => by simp
  smul_mem' := fun c H hH a b => by
    simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
      hH a b]

/-- **A generic symmetric operator realizes all tilts at once** (Lemma 24.2 for a family of tests).
If some symmetric `H₀` sends each view `u i` into the cone `Θ i` modulo `u i`
(`H₀ (u i) = d + c u i` with `d ∈ Θ i`), then so does a symmetric `H` that is good for every
rim: it separates every tied pair of labels of every rim `X i` at `u i`. -/
theorem exists_symm_good {ι : Type} [Finite ι] {k : ι → ℕ} [∀ i, NeZero (k i)]
    (X : ∀ i, ZMod (k i) → ℝ³) (u : ι → ℝ³) (hu : ∀ i, u i ≠ 0) (hX : ∀ i, Function.Injective (X i))
    (Θ : ι → Set ℝ³) (hΘ : ∀ i, ∃ U : Set ℝ³, IsOpen U ∧ Θ i = U ∩ {d | ⟪u i, d⟫ = 0})
    (H₀ : ℝ³ →L[ℝ] ℝ³) (hsym : H₀ ∈ SymOp) (hH₀ : ∀ i, ∃ d ∈ Θ i, ∃ c : ℝ, H₀ (u i) = d + c • u i) :
    ∃ H : ℝ³ →L[ℝ] ℝ³, H ∈ SymOp ∧ (∀ i, ∃ d ∈ Θ i, ∃ c : ℝ, H (u i) = d + c • u i) ∧
      ∀ i, GoodTilt (X i) (u i) (H (u i)) := by
  classical
  choose U hU hΘU using hΘ
  have huu : ∀ i, ⟪u i, u i⟫ ≠ 0 := fun i h => hu i (inner_self_eq_zero.mp h)
  let proj : ∀ i, SymOp → ℝ³ := fun i H => (H : ℝ³ →L[ℝ] ℝ³) (u i) -
    (⟪u i, (H : ℝ³ →L[ℝ] ℝ³) (u i)⟫ / ⟪u i, u i⟫) • u i
  have hproj : ∀ i, Continuous (proj i) := by
    intro i
    have h1 : Continuous fun H : SymOp => (H : ℝ³ →L[ℝ] ℝ³) (u i) :=
      (ContinuousLinearMap.apply ℝ ℝ³ (u i)).continuous.comp continuous_subtype_val
    simp only [proj]
    fun_prop
  let O : Set SymOp := {H | ∀ i, proj i H ∈ U i}
  have hO : IsOpen O := by
    have : O = ⋂ i, proj i ⁻¹' U i := by ext H; simp [O]
    rw [this]
    exact isOpen_iInter_of_finite fun i => (hU i).preimage (hproj i)
  have hperp : ∀ i H, ⟪u i, proj i H⟫ = 0 := by
    intro i H
    simp only [proj, inner_sub_right, real_inner_smul_right]
    rw [mul_comm, mul_div_cancel₀ _ (huu i), sub_self]
  have hmem : ∀ i H, proj i H ∈ U i → proj i H ∈ Θ i := fun i H h => by
    rw [hΘU i]; exact ⟨h, hperp i H⟩
  have hdec : ∀ (i : ι) (H : SymOp), (H : ℝ³ →L[ℝ] ℝ³) (u i) =
      proj i H + (⟪u i, (H : ℝ³ →L[ℝ] ℝ³) (u i)⟫ / ⟪u i, u i⟫) • u i := fun i H => by
    simp only [proj]; abel
  have hne : O.Nonempty := by
    refine ⟨⟨H₀, hsym⟩, fun i => ?_⟩
    obtain ⟨d, hd, c, hc⟩ := hH₀ i
    have hdU : d ∈ U i := by rw [hΘU i] at hd; exact hd.1
    have hdp : ⟪u i, d⟫ = 0 := by rw [hΘU i] at hd; exact hd.2
    have : proj i ⟨H₀, hsym⟩ = d := by
      simp only [proj, hc, inner_add_right, real_inner_smul_right, hdp, zero_add]
      rw [mul_div_assoc, div_self (huu i), mul_one, add_sub_cancel_right]
    rw [this]; exact hdU
  -- the functionals
  let J := {p : (Σ i, ZMod (k i) × ZMod (k i)) // p.2.1 ≠ p.2.2 ∧
    ⟪X p.1 p.2.1 - X p.1 p.2.2, u p.1⟫ = 0}
  let ℓ : J → SymOp →ₗ[ℝ] ℝ := fun p =>
    { toFun := fun H => ⟪X p.1.1 p.1.2.1 - X p.1.1 p.1.2.2, (H : ℝ³ →L[ℝ] ℝ³) (u p.1.1)⟫
      map_add' := fun H K => by simp [inner_add_right]
      map_smul' := fun c H => by simp [real_inner_smul_right] }
  have hℓ : ∀ p : J, ℓ p ≠ 0 := by
    intro p h0
    set a : ℝ³ := X p.1.1 p.1.2.1 - X p.1.1 p.1.2.2 with ha
    have ha0 : a ≠ 0 := sub_ne_zero.mpr fun e => p.2.1 (hX _ e)
    set uu := u p.1.1
    have hau : ⟪a, uu⟫ = 0 := p.2.2
    let S : ℝ³ →L[ℝ] ℝ³ := (innerSL ℝ a).smulRight uu + (innerSL ℝ uu).smulRight a
    have hS : ∀ x, S x = ⟪a, x⟫ • uu + ⟪uu, x⟫ • a := fun x => by simp [S]
    have hSsym : S ∈ SymOp := fun x y => by
      simp only [hS, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm uu x, real_inner_comm a x]
      ring
    have := LinearMap.congr_fun h0 ⟨S, hSsym⟩
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
    rw [← ha, hS, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at this
    have hau2 : ⟪a, u p.1.1⟫ = 0 := hau
    simp only [hau, hau2, mul_zero, zero_add] at this
    have h1 : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha0
    have h2 : 0 < ‖uu‖ ^ 2 := by
      have := norm_pos_iff.mpr (hu p.1.1)
      positivity
    nlinarith
  obtain ⟨H, hHO, hHne⟩ := exists_avoid_kernels ℓ hℓ hO hne
  refine ⟨H, H.2, fun i => ⟨proj i H, hmem i H (hHO i), _, hdec i H⟩, fun i a b hab htie => ?_⟩
  have := hHne ⟨⟨i, (a, b)⟩, hab, htie⟩
  simpa [ℓ] using this

/-! ### The case of a test certificate -/

/-- **A certificate of a test**: if shapes `Y s → M ε ∘ x` carry (frequently) the certificate
`q` whose labelled rim is, at the view `vw q x = lam • u`, a rotation or reflection of the rim
`X` of a test (`hP`), and the `Gm ε`-depths of `X` at `u` are distinct and refine the order of the
depths along `w`, then the depths of `X` along `w` are cyclically unimodal. -/
theorem pair_contra {n : ℕ} (x : Fin n → ℝ³) {Q : Type} (K : Q → ℕ) (lab : ∀ q, ZMod (K q) → Fin n)
    (vw : Q → (Fin n → ℝ³) → ℝ³)
    (hcont : ∀ q (z : Fin n → ℝ³) {ι : Type} {l : Filter ι} (xs : ι → Fin n → ℝ³),
      (∀ i, Tendsto (fun t => xs t i) l (𝓝 (z i))) →
        Tendsto (fun t => vw q (xs t)) l (𝓝 (vw q z)))
    (M Gm : ℝ → ℝ³ →L[ℝ] ℝ³) (hMG : ∀ ε a b, ⟪M ε a, M ε b⟫ = ⟪a, Gm ε b⟫)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (X : ZMod k → ℝ³) (u : ℝ³) (q : Q) (lam : ℝ)
    (hvq : vw q x = lam • u)
    (hP : ∀ w, (Function.Injective (fun i => ⟪X i, w⟫) →
        Function.Injective (fun i => ⟪x (lab q i), lam • w⟫)) ∧
      (IsRobustUnimodal (fun i => ⟪x (lab q i), lam • w⟫) → IsRobustUnimodal (fun i => ⟪X i, w⟫)))
    (ε : ℝ) (wε : ℝ³) (Y : ℕ → Fin n → ℝ³)
    (hY : ∀ i, Tendsto (fun s => Y s i) atTop (𝓝 (M ε (x i))))
    (hc : ∃ᶠ s in atTop, RimCertAt (Y s) (vw q (Y s)) (lab q))
    (c : ℝ) (hc0 : 0 < c) (hcε : vw q (fun i => M ε (x i)) = c • M ε (vw q x))
    (hGinj : Function.Injective (fun i => ⟪X i, Gm ε u⟫))
    (hord : ∀ i j, ⟪X i, Gm ε u⟫ < ⟪X j, Gm ε u⟫ → ⟪X i, wε⟫ < ⟪X j, wε⟫)
    (hWinj : Function.Injective (fun i => ⟪X i, wε⟫)) :
    IsCyclicUnimodal (fun i => ⟪X i, wε⟫) := by
  set w' : ℝ³ := c • Gm ε u with hw'
  have hz : ∀ i, ⟪M ε (x (lab q i)), vw q (fun i => M ε (x i))⟫ = ⟪x (lab q i), lam • w'⟫ := by
    intro i
    rw [hcε, hvq]
    simp only [hw', map_smul, real_inner_smul_right, hMG]
    ring
  have hinjw' : Function.Injective (fun i => ⟪X i, w'⟫) := by
    intro i j h
    apply hGinj
    simp only [hw', real_inner_smul_right] at h ⊢
    exact mul_left_cancel₀ hc0.ne' h
  have hzinj : Function.Injective (fun i => ⟪x (lab q i), lam • w'⟫) := (hP w').1 hinjw'
  have hlim : ∀ i, Tendsto (fun s => ⟪Y s (lab q i), vw q (Y s)⟫) atTop
      (𝓝 (⟪M ε (x (lab q i)), vw q (fun i => M ε (x i))⟫)) := fun i =>
    (hY (lab q i)).inner (hcont q _ Y hY)
  have hrob : IsRobustUnimodal (fun i => ⟪M ε (x (lab q i)), vw q (fun i => M ε (x i))⟫) := by
    refine isRobustUnimodal_of_tendsto_ties hlim
      (hc.mono fun s hs => ⟨hs.robust, fun i j hij => ?_⟩)
    have : i = j := hzinj (by simpa only [hz] using hij)
    rw [this]
  have hrobw : IsRobustUnimodal (fun i => ⟪x (lab q i), lam • w'⟫) := by
    simpa only [hz] using hrob
  have hX := (hP w').2 hrobw
  have e : (fun i => c⁻¹ * ⟪X i, w'⟫) = fun i => ⟪X i, Gm ε u⟫ := by
    funext i
    rw [hw', real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
  have hG : IsRobustUnimodal (fun i => ⟪X i, Gm ε u⟫) := by
    have := hX.smul (inv_pos.mpr hc0)
    rwa [e] at this
  exact hG.isCyclicUnimodal_of_order hk hord hWinj

/-! ### The bridge -/

/-- **The bridge: an affine-invariant cover gives metric-freeness along a curve of metrics.**

`x` is a shape and `Q` a finite family of labelled certificates `(lab q, vw q)` (the labels and
the view as a function of the shape).  `M ε` is a curve of linear maps with `Gm ε = (M ε)ᵀ M ε`
(`hMG`), `M ε → I`.  The cover (`hApprox`): for small `ε` the shape `M ε ∘ x` is a pointwise limit
of shapes `Y s`, frequently carrying a certificate of `Q`.  The views are equivariant
(`hequiv`: `vw q (M ∘ x) = c M (vw q x)`, `c > 0`) and continuous in the shape (`hcont`).

A finite family of tests `i : ι`: rims `X i` at views `u i`, with curves of depth functionals
`w i ε`; the certificates `P i q` of the test `i` are those whose labelled rims are rotations or
reflections of `X i` at multiples of `u i` (`hP`); `hord` says that the `Gm ε`-depths of `X i` at
`u i` are distinct and refine the order of the depths along `w i ε`.  Every certificate of no test
that survives in the limit (`WeakRim`) has no horizontal double normal at its view and distinct
depths of its labels (`hO`).

Then `x` is Rupert, or for small `ε`, if the depths of every rim `X i` along `w i ε` are distinct,
the depths of some rim are cyclically unimodal. -/
theorem metricFree_of_cover {n : ℕ} (x : Fin n → ℝ³)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    {Q : Type} [Finite Q] (K : Q → ℕ) [∀ q, NeZero (K q)] (lab : ∀ q, ZMod (K q) → Fin n)
    (vw : Q → (Fin n → ℝ³) → ℝ³)
    (hvw0 : ∀ q, vw q x = 0 → ∀ y, vw q y = 0)
    (hcont : ∀ q (z : Fin n → ℝ³) {ι : Type} {l : Filter ι} (xs : ι → Fin n → ℝ³),
      (∀ i, Tendsto (fun t => xs t i) l (𝓝 (z i))) →
        Tendsto (fun t => vw q (xs t)) l (𝓝 (vw q z)))
    (M Gm : ℝ → ℝ³ →L[ℝ] ℝ³) (hMG : ∀ ε a b, ⟪M ε a, M ε b⟫ = ⟪a, Gm ε b⟫)
    (hMx : ∀ i, Tendsto (fun ε => M ε (x i)) (𝓝[>] (0 : ℝ)) (𝓝 (x i)))
    (hApprox : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ Y : ℕ → Fin n → ℝ³,
      (∀ i, Tendsto (fun s => Y s i) atTop (𝓝 (M ε (x i)))) ∧
        ∃ᶠ s in atTop, ∃ q, RimCertAt (Y s) (vw q (Y s)) (lab q))
    (hequiv : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ q, ∃ c : ℝ, 0 < c ∧
      vw q (fun i => M ε (x i)) = c • M ε (vw q x))
    {ι : Type} [Finite ι] {k : ι → ℕ} [∀ i, NeZero (k i)] (hk : ∀ i, 3 ≤ k i)
    (X : ∀ i, ZMod (k i) → ℝ³) (u : ι → ℝ³) (w : ι → ℝ → ℝ³) (P : ι → Q → Prop)
    (hP : ∀ i q, P i q → ∃ lam : ℝ, vw q x = lam • u i ∧ ∀ w',
      (Function.Injective (fun j => ⟪X i j, w'⟫) →
        Function.Injective (fun j => ⟪x (lab q j), lam • w'⟫)) ∧
      (IsRobustUnimodal (fun j => ⟪x (lab q j), lam • w'⟫) →
        IsRobustUnimodal (fun j => ⟪X i j, w'⟫)))
    (hord : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun j => ⟪X i j, Gm ε (u i)⟫) ∧
      ∀ a b, ⟪X i a, Gm ε (u i)⟫ < ⟪X i b, Gm ε (u i)⟫ → ⟪X i a, w i ε⟫ < ⟪X i b, w i ε⟫)
    (hO : ∀ q, (∀ i, ¬ P i q) → vw q x ≠ 0 → Function.Injective (lab q) →
      WeakRim x (vw q x) (lab q) → NoHDNAt (univ.image x) (vw q x) ∧
        ∀ a b, lab q a ≠ lab q b → ⟪x (lab q a) - x (lab q b), vw q x⟫ ≠ 0) :
    IsRupert (univ.image x) ∨ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ i, Function.Injective (fun j => ⟪X i j, w i ε⟫)) →
        ∃ i, IsCyclicUnimodal (fun j => ⟪X i j, w i ε⟫) := by
  classical
  by_cases hR : IsRupert (univ.image x)
  · exact Or.inl hR
  right
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- the bad parameters
  have hbad : ∃ᶠ ε in 𝓝[>] (0 : ℝ), (∀ i, Function.Injective (fun j => ⟪X i j, w i ε⟫)) ∧
      ∀ i, ¬ IsCyclicUnimodal (fun j => ⟪X i j, w i ε⟫) :=
    hcon.mono fun ε h => by
      by_contra h'
      apply h
      intro h1
      by_contra h3
      push Not at h3
      exact h' ⟨h1, h3⟩
  -- the cover at each small ε
  let Rq : Q → ℝ → Prop := fun q ε => ∃ Y : ℕ → Fin n → ℝ³,
    (∀ i, Tendsto (fun s => Y s i) atTop (𝓝 (M ε (x i)))) ∧
      ∃ᶠ s in atTop, RimCertAt (Y s) (vw q (Y s)) (lab q)
  let Good : ℝ → Prop := fun ε => 0 < ε ∧
      (∀ q, ∃ c : ℝ, 0 < c ∧ vw q (fun i => M ε (x i)) = c • M ε (vw q x)) ∧
      ∀ i, Function.Injective (fun j => ⟪X i j, Gm ε (u i)⟫) ∧
        ∀ a b, ⟪X i a, Gm ε (u i)⟫ < ⟪X i b, Gm ε (u i)⟫ → ⟪X i a, w i ε⟫ < ⟪X i b, w i ε⟫
  have hgood : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Good ε ∧ ∃ q, Rq q ε := by
    have hord' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, Function.Injective (fun j => ⟪X i j, Gm ε (u i)⟫) ∧
      ∀ a b, ⟪X i a, Gm ε (u i)⟫ < ⟪X i b, Gm ε (u i)⟫ → ⟪X i a, w i ε⟫ < ⟪X i b, w i ε⟫ :=
      eventually_all.2 hord
    filter_upwards [self_mem_nhdsWithin, hApprox, hequiv, hord'] with ε h0 hA hE h1
    refine ⟨⟨h0, hE, h1⟩, ?_⟩
    obtain ⟨Y, hY, hc⟩ := hA
    obtain ⟨q, hq⟩ := frequently_exists_of_finite hc
    exact ⟨q, Y, hY, hq⟩
  have h1 : ∃ᶠ ε in 𝓝[>] (0 : ℝ), ∃ q, ((∀ i, Function.Injective (fun j => ⟪X i j, w i ε⟫)) ∧
      ∀ i, ¬ IsCyclicUnimodal (fun j => ⟪X i j, w i ε⟫)) ∧ Rq q ε ∧ Good ε :=
    (hbad.and_eventually hgood).mono fun ε ⟨hb, hg, q, hq⟩ => ⟨q, hb, hq, hg⟩
  obtain ⟨q, hq⟩ := frequently_exists_of_finite h1
  by_cases hp : ∃ i, P i q
  · obtain ⟨i, hpi⟩ := hp
    obtain ⟨ε, ⟨hb1, hb3⟩, ⟨Y, hY, hc⟩, h0, hE, ho⟩ := hq.exists
    obtain ⟨lam, hvq, hP'⟩ := hP i q hpi
    obtain ⟨c, hc0, hcε⟩ := hE q
    exact hb3 i (pair_contra x K lab vw hcont M Gm hMG (hk i) (X i) (u i) q lam hvq hP' ε (w i ε)
      Y hY hc c hc0 hcε (ho i).1 (ho i).2 (hb1 i))
  push Not at hp
  -- any other certificate passes to the limit
  have key : ∀ ε : ℝ, 0 < ε → ∃ y : Fin n → ℝ³, (∀ i, dist (y i) (M ε (x i)) < ε) ∧
      (Rq q ε → RimCertAt y (vw q y) (lab q)) := by
    intro ε hε
    by_cases hR' : Rq q ε
    · obtain ⟨Y, hY, hc⟩ := hR'
      have hclose : ∀ᶠ s in atTop, ∀ i, dist (Y s i) (M ε (x i)) < ε :=
        eventually_all.2 fun i => (Metric.tendsto_nhds.1 (hY i)) ε hε
      obtain ⟨s, hs1, hs2⟩ := (hc.and_eventually hclose).exists
      exact ⟨Y s, hs2, fun _ => hs1⟩
    · exact ⟨fun i => M ε (x i), fun i => by simpa using hε, fun h => absurd h hR'⟩
  choose! yf hyf using key
  have hxs : ∀ i, Tendsto (fun ε => yf ε i) (𝓝[>] (0 : ℝ)) (𝓝 (x i)) := by
    intro i
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (g := fun ε => ε + dist (M ε (x i)) (x i))
      (Eventually.of_forall fun _ => dist_nonneg) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have h1 := (hyf ε hε).1 i
      have h2 := dist_triangle (yf ε i) (M ε (x i)) (x i)
      linarith
    · have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      have := hid.add (tendsto_iff_dist_tendsto_zero.1 (hMx i))
      simpa using this
  have hcert : ∃ᶠ ε in 𝓝[>] (0 : ℝ), RimCertAt (yf ε) (vw q (yf ε)) (lab q) := by
    refine (hq.and_eventually self_mem_nhdsWithin).mono fun ε h => ?_
    obtain ⟨⟨-, hRq, -⟩, h0⟩ := h
    exact (hyf ε h0).2 hRq
  have hu : vw q x ≠ 0 := by
    intro h0
    obtain ⟨ε, hε⟩ := hcert.exists
    exact hε.ne_zero (hvw0 q h0 _)
  have hus := hcont q x yf hxs
  have hWL : WeakLeft x (vw q x) (lab q) := by
    intro m i
    refine le_of_tendsto_frequently tendsto_const_nhds
      (Tendsto.det3' (((hxs _).sub (hxs _))) (((hxs _).sub (hxs _))) hus) ?_
    exact hcert.mono fun ε h => h.left m i
  have hWC : ∀ a b c : ZMod (K q), CycBetween a b c →
      0 ≤ det3 (x (lab q b) - x (lab q a)) (x (lab q c) - x (lab q a)) (vw q x) :=
    fun a b c h => cyc_nonneg_of_tendsto hxs hus hcert h
  have hinjl : Function.Injective (lab q) := (hcert.exists.choose_spec).injective_lab
  obtain ⟨hnd, hdist⟩ := hO q hp hu hinjl ⟨hWL, hWC⟩
  refine hR (isRupert_of_tendsto_rimCert x hseg hsp (lab q) hu hnd yf (fun ε => vw q (yf ε))
    hxs hus (hcert.mono fun ε h => ⟨h, fun a b hab => ?_⟩))
  by_cases hl : lab q a = lab q b
  · rw [hl]
  · exact absurd (by rw [inner_sub_left, hab, sub_self] :
      ⟪x (lab q a) - x (lab q b), vw q x⟫ = 0) (hdist a b hl)

end Minimality

end
