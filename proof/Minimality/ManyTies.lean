module

public import Minimality.Sector
public import Minimality.FaceFive

@[expose] public section

/-!
# Several ties at metric-free certificates (`FEWER-FACES-PROOFS.md` §24.2, Theorem 24.3)

The limit route (`LimitRim.lean`, `LimitCert.lean`) breaks ties of the limit depths by approaching
`K` from both sides of one tie (Lemma 18.4, Corollary 18.5).  Theorem 24.3 allows any number of
ties: the ties of a labelled rim at the view `u` are broken by a *tilt* `d ⊥ u`, and a tilt is a
metric perturbation (Lemma 24.2), so a certificate that is unimodal at every metric near `G`
(*metric-free*) is unimodal at the tilted depths.

How the metrics enter.  The Lean `IsRupert` is Euclidean, so the metric `G' = I + δH` enters only
through the depth functional: the depth of `x` along the view `u` at `G'` is
`⟪G' u, x⟫ = ⟪w, x⟫` with `w = G' u`.  Metric-freeness of a labelled rim `X` at `u` is therefore
the hypothesis "for `w` near `u`, if `i ↦ ⟪X i, w⟫` is injective then it is cyclically unimodal".
For two tests the same metric serves both views, so the pair `(w, w') = (G' u, G' u')` is
*coupled*, `⟪w, u'⟫ = ⟪u, w'⟫`; this is the only constraint, and (for `u, u'` independent) every
coupled pair near `(u, u')` is of the form `(G' u, G' u')` with `G'` symmetric near `I`
(`exists_symm_clm`, Lemma 24.2).

* `isCyclicUnimodal_comp`: unimodality passes to cyclic subsequences (7.3 Step 3).
* `isRupert_of_tilted_unimodal_freq`: Corollary 8.0′ with the depth condition only for
  frequently many small tilts.
* `TiltTest`: a test (view `u`, labelled rim `X`, silhouette = cyclic subsequence `X ∘ σ`, open
  cone `Θ` of realizing tilts).
* **`isRupert_of_tiltTest_metricFree`** (24.3 (a), single test): any number of ties.
* **`isRupert_of_tiltTests_metricFree`** (24.3, two tests, depth form).
* `exists_symm_clm` (24.2): a symmetric `H` with prescribed `H u`, `H u'`.
* **`isRupert_of_tiltTests_metric`** (24.3, two tests, metric form).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Cyclic subsequences and scaling -/

/-! ### Corollary 8.0′ with a frequent depth condition -/

/-! ### Genericity -/

/-- `A + s B ≠ 0` for all small `s > 0`, provided `A = 0 → B ≠ 0`. -/
theorem eventually_affine_ne {A B : ℝ} (h : A = 0 → B ≠ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), A + s * B ≠ 0 := by
  by_cases hA : A = 0
  · subst hA
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa using ⟨ne_of_gt hs, h rfl⟩
  · have hc : Continuous fun s : ℝ => A + s * B := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hA)).filter_mono nhdsWithin_le_nhds

/-- **Avoiding finitely many hyperplanes in an open set.**  A nonempty open set of a real
topological vector space contains a point on which finitely many nonzero linear functionals are
all nonzero. -/
theorem exists_avoid_kernels {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] {ι : Type*} [Finite ι] (ℓ : ι → E →ₗ[ℝ] ℝ)
    (hℓ : ∀ i, ℓ i ≠ 0) {O : Set E} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ e ∈ O, ∀ i, ℓ i e ≠ 0 := by
  obtain ⟨e₀, he₀⟩ := hne
  have ha : ∃ a : E, ∀ i, ℓ i a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcov : ⋃ i, ((LinearMap.ker (ℓ i) : Submodule ℝ E) : Set E) = Set.univ := by
      refine Set.eq_univ_of_forall fun a => ?_
      obtain ⟨i, hi⟩ := hcon a
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
    exact hℓ i (LinearMap.ker_eq_top.mp hi)
  obtain ⟨a, ha⟩ := ha
  have hpath : Continuous fun s : ℝ => e₀ + s • a := by fun_prop
  have hO' : ∀ᶠ s in 𝓝[>] (0 : ℝ), e₀ + s • a ∈ O :=
    Eventually.filter_mono nhdsWithin_le_nhds
      ((hpath.continuousAt (x := 0)).preimage_mem_nhds (by simpa using hO.mem_nhds he₀))
  have hall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, ℓ i e₀ + s * ℓ i a ≠ 0 :=
    eventually_all.2 fun i => eventually_affine_ne fun _ => ha i
  obtain ⟨s, hs1, hs2⟩ := (hO'.and hall).exists
  exact ⟨e₀ + s • a, hs1, fun i => by simpa using hs2 i⟩

/-! ### Tilt tests -/

/-! ### Theorem 24.3 (a): a single test -/

/-! ### Theorem 24.3: two tests -/

/-! ### Lemma 24.2: a tilt is a metric perturbation -/

end Minimality

end
