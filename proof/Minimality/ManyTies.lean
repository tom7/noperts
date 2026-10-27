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

theorem IsCyclicUnimodal.smul_pos {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : IsCyclicUnimodal z)
    {c : ℝ} (hc : 0 < c) : IsCyclicUnimodal (fun i => c * z i) := by
  refine ⟨fun i j hij => hz.1 (mul_left_cancel₀ hc.ne' hij), ?_⟩
  simp only [mul_lt_mul_iff_right₀ hc]
  exact hz.2

/-- **Unimodality passes to cyclic subsequences** (Theorem 7.3, Step 3): an injective cyclic
subsequence of a cyclically unimodal sequence is cyclically unimodal. -/
theorem isCyclicUnimodal_comp {k k' : ℕ} [NeZero k] [NeZero k'] (hk' : 3 ≤ k')
    {z : ZMod k → ℝ} (hz : IsCyclicUnimodal z) (σ : ZMod k' → ZMod k)
    (hσi : Function.Injective σ) (hσ : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l)) :
    IsCyclicUnimodal (z ∘ σ) :=
  (hz.isRobustUnimodal.comp σ hσ).isCyclicUnimodal_of_order hk' (fun _ _ h => h)
    (hz.1.comp hσi)

/-! ### Corollary 8.0′ with a frequent depth condition -/

/-- **Corollary 8.0′ with frequently many tilts.**  As `isRupert_of_tilted_unimodal'` with `Q`
cyclic unimodality, but the depths `⟪x i, u₀ + ε v⟫` need be unimodal only for frequently many
small `ε > 0` (the determinant tests hold for all small `ε`, so one common `ε` exists). -/
theorem isRupert_of_tilted_unimodal_freq (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)
    (hQe : ∃ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal fun i => ⟪x i, u₀ + ε • v⟫) :
    IsRupert V := by
  classical
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • v ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • v := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hu₀)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hQε, ⟨h1, h2⟩, hw⟩ :=
    (hQe.and_eventually ((eventually_tilted_dets V u₀ v x hcyc hrest).and hne)).exists
  obtain ⟨R, hR, r, hr, hRw⟩ := exists_rotation_to_ez_pos _ hw
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRw (h1 i j hi hj)
  have hinj : Function.Injective x := fun i j hij => hp.injective (by simp only [hij])
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀ + ε • v⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀ + ε • v⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRw, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  refine isRupert_of_open_unimodal V hR x hxV hinj hp ?_ IsCyclicUnimodal
    isOpen_isCyclicUnimodal ?_ (fun z _ hQ => hQ)
  · intro y hy hyx i
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRw (h2 y hy hyx i)
  · simp only [hdepth]
    exact hQε.smul_pos (inv_pos.mpr hr)


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

/-- A tilt `g` is *good* for the labelled rim `X` at the view `u` if it separates every tied
pair of distinct labels: `⟪X i - X j, u⟫ = 0 → ⟪X i - X j, g⟫ ≠ 0` (the labels over one corner
differ in depth, so `X i - X j ∦ u`, and a generic `d` is good). -/
def GoodTilt {k : ℕ} (X : ZMod k → ℝ³) (u g : ℝ³) : Prop :=
  ∀ i j, i ≠ j → ⟪X i - X j, u⟫ = 0 → ⟪X i - X j, g⟫ ≠ 0

/-- **The depths at the tilted view are distinct** (Lemma 24.2, the genericity step): ties of `X`
at `u` are broken by a good tilt, so `i ↦ ⟪X i, u + ε g⟫` is injective for all small `ε > 0`. -/
theorem eventually_injective_depth {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {u g : ℝ³}
    (hg : GoodTilt X u g) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective fun i => ⟪X i, u + ε • g⟫ := by
  have hpair : ∀ q : ZMod k × ZMod k, q.1 ≠ q.2 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪X q.1 - X q.2, u⟫ + ε * ⟪X q.1 - X q.2, g⟫ ≠ 0 := by
    intro q hq
    exact eventually_affine_ne fun h => hg q.1 q.2 hq h
  have hall := eventually_all.2 fun q : ZMod k × ZMod k =>
    (by
      by_cases hq : q.1 = q.2
      · exact Eventually.of_forall fun _ _ => absurd hq ‹_›
      · exact (hpair q hq).mono fun _ h _ => h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), q.1 ≠ q.2 →
          ⟪X q.1 - X q.2, u⟫ + ε * ⟪X q.1 - X q.2, g⟫ ≠ 0)
  filter_upwards [hall] with ε hε i j hij
  by_contra hne
  apply hε (i, j) hne
  simp only [inner_sub_left]
  simp only [inner_add_right, real_inner_smul_right] at hij
  linarith

/-- Rescaling a tilted depth: for `1 + ε c > 0`,
`⟪x, u + (ε/(1+εc)) d⟫ = (1+εc)⁻¹ ⟪x, u + ε (d + c u)⟫`. -/
theorem inner_tilt_rescale (x u d : ℝ³) {ε c : ℝ} (h : 0 < 1 + ε * c) :
    ⟪x, u + (ε / (1 + ε * c)) • d⟫ = (1 + ε * c)⁻¹ * ⟪x, u + ε • (d + c • u)⟫ := by
  simp only [inner_add_right, real_inner_smul_right]
  field_simp
  ring

/-- Frequent unimodality at the tilts `u + ε (d + c u)` gives frequent unimodality at the tilts
`u + ε′ d` (the reparametrisation `ε′ = ε/(1+εc)` tends to `0` from above). -/
theorem frequently_unimodal_tilt {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (u d : ℝ³) (c : ℝ)
    (h : ∃ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal fun i => ⟪X i, u + ε • (d + c • u)⟫) :
    ∃ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal fun i => ⟪X i, u + ε • d⟫ := by
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 + ε * c := by
    have hc : Continuous fun ε : ℝ => 1 + ε * c := by fun_prop
    exact (hc.continuousAt.eventually (lt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds
  have hT : Tendsto (fun ε : ℝ => ε / (1 + ε * c)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun ε : ℝ => ε / (1 + ε * c)) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, hpos] with ε h1 h2
      exact div_pos h1 h2
  refine hT.frequently ?_
  refine (h.and_eventually hpos).mono fun ε ⟨hε, hp⟩ => ?_
  have e : (fun i => ⟪X i, u + (ε / (1 + ε * c)) • d⟫) =
      fun i => (1 + ε * c)⁻¹ * ⟪X i, u + ε • (d + c • u)⟫ :=
    funext fun i => inner_tilt_rescale _ _ _ hp
  rw [e]
  exact hε.smul_pos (inv_pos.mpr hp)


/-! ### Tilt tests -/

/-- **A tilt test** (the data of Theorem 24.3 for one test).  The view `u`, the labelled rim
`X` (distinct points of `V`), and a cyclic subsequence `X ∘ σ` of it (`σ` injective, keeping the
cyclic order of triples, at least three corners) that is the silhouette of `V` at the tilted view
`u + εd` for every `d` in the cone `Θ` of realizing tilts and small `ε > 0`: the determinant
tests hold in the limit form `TiltSign` (`D₀ > 0`, or `D₀ = 0` and `D₁ > 0`), which includes
(G1): every other point of `V` is strictly inside.  `Θ` is a nonempty open subset of `u^⊥`. -/
structure TiltTest (V : Finset ℝ³) (u : ℝ³) {k k' : ℕ} [NeZero k] [NeZero k']
    (X : ZMod k → ℝ³) (σ : ZMod k' → ZMod k) (Θ : Set ℝ³) : Prop where
  ne_zero : u ≠ 0
  three : 3 ≤ k'
  mem : ∀ i, X i ∈ V
  inj : Function.Injective X
  σinj : Function.Injective σ
  σcyc : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l)
  isOpen : ∃ U : Set ℝ³, IsOpen U ∧ Θ = U ∩ {d | ⟪u, d⟫ = 0}
  nonempty : Θ.Nonempty
  cyc : ∀ d ∈ Θ, ∀ i j, j ≠ i → j ≠ i + 1 →
    TiltSign (X (σ (i + 1)) - X (σ i)) (X (σ j) - X (σ i)) u d
  rest : ∀ d ∈ Θ, ∀ y ∈ V, (∀ j, y ≠ X (σ j)) → ∀ i,
    TiltSign (X (σ (i + 1)) - X (σ i)) (y - X (σ i)) u d

theorem TiltTest.perp {V : Finset ℝ³} {u : ℝ³} {k k' : ℕ} [NeZero k] [NeZero k']
    {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k} {Θ : Set ℝ³} (T : TiltTest V u X σ Θ) {d : ℝ³}
    (hd : d ∈ Θ) : ⟪u, d⟫ = 0 := by
  obtain ⟨U, -, rfl⟩ := T.isOpen
  exact hd.2

/-- **One tilt of a test is enough**: if the depths along the tilted views `u + εd` of the
labelled rim are cyclically unimodal for frequently many small `ε > 0`, then `V` is Rupert
(Theorem 7.5 via Corollary 8.0′, with Theorem 7.3 Step 3 for the cyclic subsequence). -/
theorem TiltTest.isRupert_of_freq {V : Finset ℝ³} {u : ℝ³} {k k' : ℕ} [NeZero k] [NeZero k']
    {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k} {Θ : Set ℝ³} (T : TiltTest V u X σ Θ) {d : ℝ³}
    (hd : d ∈ Θ) (h : ∃ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal fun i => ⟪X i, u + ε • d⟫) :
    IsRupert V :=
  isRupert_of_tilted_unimodal_freq V u d T.ne_zero T.three (fun i => X (σ i)) (fun i => T.mem _)
    (T.cyc d hd) (T.rest d hd)
    (h.mono fun _ hε => isCyclicUnimodal_comp T.three hε σ T.σinj T.σcyc)

/-- **Generic tilts exist** (24.3, proof): the cone of realizing tilts is open in `u^⊥`, and the
tilts that fail to separate a tied pair of labels lie on finitely many proper hyperplanes of
`u^⊥`. -/
theorem TiltTest.exists_good {V : Finset ℝ³} {u : ℝ³} {k k' : ℕ} [NeZero k] [NeZero k']
    {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k} {Θ : Set ℝ³} (T : TiltTest V u X σ Θ) :
    ∃ d ∈ Θ, GoodTilt X u d := by
  classical
  obtain ⟨U, hU, rfl⟩ := T.isOpen
  obtain ⟨d₀, hd₀⟩ := T.nonempty
  let E : Submodule ℝ ℝ³ := LinearMap.ker (innerₛₗ ℝ u)
  let ι := {q : ZMod k × ZMod k // q.1 ≠ q.2 ∧ ⟪X q.1 - X q.2, u⟫ = 0}
  let ℓ : ι → E →ₗ[ℝ] ℝ := fun q => (innerₛₗ ℝ (X q.1.1 - X q.1.2)).comp E.subtype
  have hℓ : ∀ q, ℓ q ≠ 0 := by
    intro q h0
    have hv : X q.1.1 - X q.1.2 ≠ 0 := sub_ne_zero.mpr (fun e => q.2.1 (T.inj e))
    have hmem : X q.1.1 - X q.1.2 ∈ E := by
      show ⟪u, X q.1.1 - X q.1.2⟫ = 0
      rw [real_inner_comm]; exact q.2.2
    have := LinearMap.congr_fun h0 ⟨_, hmem⟩
    simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply,
      LinearMap.zero_apply] at this
    exact hv (inner_self_eq_zero.mp this)
  obtain ⟨e, heO, hne⟩ := exists_avoid_kernels ℓ hℓ
    (O := {e : E | (e : ℝ³) ∈ U}) (hU.preimage continuous_subtype_val) ⟨⟨d₀, hd₀.2⟩, hd₀.1⟩
  refine ⟨e, ⟨heO, e.2⟩, fun i j hij htie => ?_⟩
  have := hne ⟨(i, j), hij, htie⟩
  simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply] at this
  exact this

/-! ### Theorem 24.3 (a): a single test -/

/-- **Theorem 24.3 (a), a single test with any number of ties** (the case `X′ = X`, no condition
on the views).  If the labelled rim `X` is metric-free at `u` (at every depth functional `w`
near `u`, i.e. every metric `G′` near `G` with `w = G′u`, distinct depths `⟪X i, w⟫` are cyclically
unimodal) and the test has a nonempty open cone of realizing tilts, then `V` is Rupert, however
many labels of `X` are tied at `u`. -/
theorem isRupert_of_tiltTest_metricFree {V : Finset ℝ³} {u : ℝ³} {k k' : ℕ} [NeZero k]
    [NeZero k'] {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k} {Θ : Set ℝ³}
    (T : TiltTest V u X σ Θ)
    (hMF : ∀ᶠ w in 𝓝 u, Function.Injective (fun i => ⟪X i, w⟫) →
      IsCyclicUnimodal fun i => ⟪X i, w⟫) : IsRupert V := by
  obtain ⟨d, hdΘ, hgood⟩ := T.exists_good
  have hw : Tendsto (fun ε : ℝ => u + ε • d) (𝓝[>] (0 : ℝ)) (𝓝 u) := by
    have hc : Continuous fun ε : ℝ => u + ε • d := by fun_prop
    simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  exact T.isRupert_of_freq hdΘ
    (((hw.eventually hMF).and (eventually_injective_depth hgood)).mono
      fun _ ⟨h1, h2⟩ => h1 h2).frequently


/-! ### Theorem 24.3: two tests -/

/-- The space of coupled tilt pairs `(d, d′)` of two views `u, u′`: `d ⊥ u`, `d′ ⊥ u′`, and
`⟪u′, d⟫ = ⟪u, d′⟫` when `⟪u, u′⟫ = 0` (Lemma 24.2: otherwise the constants `c, c′` absorb the
difference). -/
def pairSpace (u u' : ℝ³) : Submodule ℝ (ℝ³ × ℝ³) where
  carrier := {p | ⟪u, p.1⟫ = 0 ∧ ⟪u', p.2⟫ = 0 ∧ (⟪u, u'⟫ = 0 → ⟪u', p.1⟫ = ⟪u, p.2⟫)}
  add_mem' := by
    rintro p q ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨by simp [inner_add_right, a1, b1], by simp [inner_add_right, a2, b2], fun h => ?_⟩
    simp [inner_add_right, a3 h, b3 h]
  zero_mem' := by simp
  smul_mem' := by
    rintro c p ⟨a1, a2, a3⟩
    refine ⟨by simp [real_inner_smul_right, a1], by simp [real_inner_smul_right, a2],
      fun h => ?_⟩
    simp [real_inner_smul_right, a3 h]

theorem mem_pairSpace {u u' : ℝ³} {p : ℝ³ × ℝ³} :
    p ∈ pairSpace u u' ↔ ⟪u, p.1⟫ = 0 ∧ ⟪u', p.2⟫ = 0 ∧ (⟪u, u'⟫ = 0 → ⟪u', p.1⟫ = ⟪u, p.2⟫) :=
  Iff.rfl

/-- **Generic coupled tilts exist** (24.3, proof): a pair of realizing tilts `(d, d′)`, coupled
as in `pairSpace`, that separates every tied pair of labels of both rims. -/
theorem exists_good_pair {V : Finset ℝ³} {u u' : ℝ³} {k k' m m' : ℕ} [NeZero k] [NeZero k']
    [NeZero m] [NeZero m'] {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k} {Θ : Set ℝ³}
    {X' : ZMod m → ℝ³} {σ' : ZMod m' → ZMod m} {Θ' : Set ℝ³}
    (T : TiltTest V u X σ Θ) (T' : TiltTest V u' X' σ' Θ')
    (hcompat : ⟪u, u'⟫ = 0 → ∃ d ∈ Θ, ∃ d' ∈ Θ', ⟪u', d⟫ = ⟪u, d'⟫) :
    ∃ d ∈ Θ, ∃ d' ∈ Θ', (⟪u, u'⟫ = 0 → ⟪u', d⟫ = ⟪u, d'⟫) ∧
      GoodTilt X u d ∧ GoodTilt X' u' d' := by
  classical
  obtain ⟨U, hU, rfl⟩ := T.isOpen
  obtain ⟨U', hU', rfl⟩ := T'.isOpen
  have hne : ∃ p ∈ pairSpace u u', p.1 ∈ U ∧ p.2 ∈ U' := by
    by_cases ho : ⟪u, u'⟫ = 0
    · obtain ⟨d, hd, d', hd', h⟩ := hcompat ho
      exact ⟨(d, d'), ⟨hd.2, hd'.2, fun _ => h⟩, hd.1, hd'.1⟩
    · obtain ⟨d, hd⟩ := T.nonempty
      obtain ⟨d', hd'⟩ := T'.nonempty
      exact ⟨(d, d'), ⟨hd.2, hd'.2, fun h => absurd h ho⟩, hd.1, hd'.1⟩
  obtain ⟨p₀, hp₀, hp₀1, hp₀2⟩ := hne
  let E := pairSpace u u'
  let ι := {q : ZMod k × ZMod k // q.1 ≠ q.2 ∧ ⟪X q.1 - X q.2, u⟫ = 0} ⊕
    {q : ZMod m × ZMod m // q.1 ≠ q.2 ∧ ⟪X' q.1 - X' q.2, u'⟫ = 0}
  let ℓ : ι → E →ₗ[ℝ] ℝ := fun i => match i with
    | .inl q => ((innerₛₗ ℝ (X q.1.1 - X q.1.2)).comp (LinearMap.fst ℝ ℝ³ ℝ³)).comp E.subtype
    | .inr q => ((innerₛₗ ℝ (X' q.1.1 - X' q.1.2)).comp (LinearMap.snd ℝ ℝ³ ℝ³)).comp E.subtype
  have huu : ⟪u, u⟫ ≠ 0 := fun h => T.ne_zero (inner_self_eq_zero.mp h)
  have huu' : ⟪u', u'⟫ ≠ 0 := fun h => T'.ne_zero (inner_self_eq_zero.mp h)
  have hℓ : ∀ i, ℓ i ≠ 0 := by
    intro i h0
    match i with
    | .inl q =>
      have hv : X q.1.1 - X q.1.2 ≠ 0 := sub_ne_zero.mpr (fun e => q.2.1 (T.inj e))
      have hperp : ⟪u, X q.1.1 - X q.1.2⟫ = 0 := by rw [real_inner_comm]; exact q.2.2
      let t : ℝ := if ⟪u, u'⟫ = 0 then ⟪u', X q.1.1 - X q.1.2⟫ / ⟪u, u⟫ else 0
      have hmem : ((X q.1.1 - X q.1.2, t • u) : ℝ³ × ℝ³) ∈ E := by
        refine ⟨hperp, ?_, fun ho => ?_⟩
        · show ⟪u', t • u⟫ = 0
          rw [real_inner_smul_right]
          by_cases ho : ⟪u, u'⟫ = 0
          · rw [real_inner_comm, ho, mul_zero]
          · simp [t, ho]
        · show ⟪u', X q.1.1 - X q.1.2⟫ = ⟪u, t • u⟫
          rw [real_inner_smul_right]
          simp only [t, ho, if_true]
          field_simp
      have := LinearMap.congr_fun h0 ⟨_, hmem⟩
      simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply,
        LinearMap.fst_apply, LinearMap.zero_apply] at this
      exact hv (inner_self_eq_zero.mp this)
    | .inr q =>
      have hv : X' q.1.1 - X' q.1.2 ≠ 0 := sub_ne_zero.mpr (fun e => q.2.1 (T'.inj e))
      have hperp : ⟪u', X' q.1.1 - X' q.1.2⟫ = 0 := by rw [real_inner_comm]; exact q.2.2
      let t : ℝ := if ⟪u, u'⟫ = 0 then ⟪u, X' q.1.1 - X' q.1.2⟫ / ⟪u', u'⟫ else 0
      have hmem : ((t • u', X' q.1.1 - X' q.1.2) : ℝ³ × ℝ³) ∈ E := by
        refine ⟨?_, hperp, fun ho => ?_⟩
        · show ⟪u, t • u'⟫ = 0
          rw [real_inner_smul_right]
          by_cases ho : ⟪u, u'⟫ = 0
          · rw [ho, mul_zero]
          · simp [t, ho]
        · show ⟪u', t • u'⟫ = ⟪u, X' q.1.1 - X' q.1.2⟫
          rw [real_inner_smul_right]
          simp only [t, ho, if_true]
          field_simp
      have := LinearMap.congr_fun h0 ⟨_, hmem⟩
      simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply,
        LinearMap.snd_apply, LinearMap.zero_apply] at this
      exact hv (inner_self_eq_zero.mp this)
  obtain ⟨e, heO, hne⟩ := exists_avoid_kernels ℓ hℓ
    (O := {e : E | (e : ℝ³ × ℝ³).1 ∈ U ∧ (e : ℝ³ × ℝ³).2 ∈ U'})
    ((hU.preimage (continuous_fst.comp continuous_subtype_val)).inter
      (hU'.preimage (continuous_snd.comp continuous_subtype_val))) ⟨⟨p₀, hp₀⟩, hp₀1, hp₀2⟩
  obtain ⟨e1, e2, e3⟩ := e.2
  refine ⟨(e : ℝ³ × ℝ³).1, ⟨heO.1, e1⟩, (e : ℝ³ × ℝ³).2, ⟨heO.2, e2⟩, e3, ?_, ?_⟩
  · intro i j hij htie
    have := hne (.inl ⟨(i, j), hij, htie⟩)
    simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply,
      LinearMap.fst_apply] at this
    exact this
  · intro i j hij htie
    have := hne (.inr ⟨(i, j), hij, htie⟩)
    simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply,
      LinearMap.snd_apply] at this
    exact this


/-- **The compatibility condition from sign sets** (24.3, orthogonal case).  If `Θ′` is a cone
(closed under positive scaling; `Θ` need not be) and the sign sets of `⟪u′, d⟫` and
`⟪u, d′⟫` meet in a nonzero sign, then some pair of realizing tilts has `⟪u′, d⟫ = ⟪u, d′⟫`. -/
theorem compat_of_signs {u u' : ℝ³} {Θ Θ' : Set ℝ³}
    (hΘ' : ∀ d ∈ Θ', ∀ c : ℝ, 0 < c → c • d ∈ Θ')
    (h : ∃ d ∈ Θ, ∃ d' ∈ Θ', 0 < ⟪u', d⟫ * ⟪u, d'⟫) :
    ∃ d ∈ Θ, ∃ d' ∈ Θ', ⟪u', d⟫ = ⟪u, d'⟫ := by
  obtain ⟨d, hd, d', hd', hpos⟩ := h
  have hne : ⟪u', d⟫ ≠ 0 := fun e => by rw [e, zero_mul] at hpos; exact lt_irrefl _ hpos
  have hne' : ⟪u, d'⟫ ≠ 0 := fun e => by rw [e, mul_zero] at hpos; exact lt_irrefl _ hpos
  -- rescale `d′` by `c = ⟪u′, d⟫ / ⟪u, d′⟫ > 0`
  have hc : 0 < ⟪u', d⟫ / ⟪u, d'⟫ := by
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have : ⟪u, d'⟫ < 0 := by
        by_contra hh; push Not at hh; nlinarith
      exact div_pos_of_neg_of_neg h1 this
    · have : 0 < ⟪u, d'⟫ := by
        by_contra hh; push Not at hh; nlinarith
      exact div_pos h1 this
  refine ⟨d, hd, _, hΘ' d' hd' _ hc, ?_⟩
  rw [real_inner_smul_right]
  field_simp

/-- **Theorem 24.3, two tests, curve form** (the core).  Two tilt tests `T, T′` (views `u, u′`,
labelled rims `X, X′`, silhouettes the cyclic subsequences `X ∘ σ`, `X′ ∘ σ′` for every tilt in
the nonempty open cones `Θ ⊂ u^⊥`, `Θ′ ⊂ u′^⊥`), with compatible tilts: if `⟪u, u′⟫ = 0` then
some `d ∈ Θ`, `d′ ∈ Θ′` have `⟪u′, d⟫ = ⟪u, d′⟫` (from the sign sets of the cones meeting,
`compat_of_signs`; for `⟪u, u′⟫ ≠ 0` there is no condition).

Metric-freeness is used along the tilted depth functionals of Lemma 24.2,
`w = u + ε (d + c u)`, `w′ = u′ + ε d′` (the depths of `X`, `X′` along `u, u′` at the metric
`I + εH`, `Hu = d + cu`, `Hu′ = d′`): for every coupled choice `(d, d′, c)` of tilts, for all
small `ε > 0`, if both rims have distinct depths then `X` or `X′` is cyclically unimodal.

Conclusion: `V` is Rupert, with **any number of ties** on `X` and `X′` and any HDNs. -/
theorem isRupert_of_tiltTests_curve {V : Finset ℝ³} {u u' : ℝ³} {k k' m m' : ℕ}
    [NeZero k] [NeZero k'] [NeZero m] [NeZero m'] {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k}
    {Θ : Set ℝ³} {X' : ZMod m → ℝ³} {σ' : ZMod m' → ZMod m} {Θ' : Set ℝ³}
    (T : TiltTest V u X σ Θ) (T' : TiltTest V u' X' σ' Θ')
    (hcompat : ⟪u, u'⟫ = 0 → ∃ d ∈ Θ, ∃ d' ∈ Θ', ⟪u', d⟫ = ⟪u, d'⟫)
    (hMF : ∀ d ∈ Θ, ∀ d' ∈ Θ', ∀ c : ℝ, ⟪d, u'⟫ + c * ⟪u, u'⟫ = ⟪u, d'⟫ →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪X i, u + ε • (d + c • u)⟫) →
        Function.Injective (fun i => ⟪X' i, u' + ε • d'⟫) →
        IsCyclicUnimodal (fun i => ⟪X i, u + ε • (d + c • u)⟫) ∨
          IsCyclicUnimodal (fun i => ⟪X' i, u' + ε • d'⟫)) :
    IsRupert V := by
  obtain ⟨d, hdΘ, d', hdΘ', hcoup, hg, hg'⟩ := exists_good_pair T T' hcompat
  -- the constant `c` absorbing the coupling defect
  set c : ℝ := (⟪u, d'⟫ - ⟪u', d⟫) / ⟪u, u'⟫ with hc
  have hrel : ⟪d, u'⟫ + c * ⟪u, u'⟫ = ⟪u, d'⟫ := by
    by_cases ho : ⟪u, u'⟫ = 0
    · rw [real_inner_comm, hcoup ho, ho]; ring
    · rw [hc]; field_simp; rw [real_inner_comm]; ring
  have hgood : GoodTilt X u (d + c • u) := by
    intro i j hij hti
    have := hg i j hij hti
    simp only [inner_add_right, real_inner_smul_right, hti, mul_zero, add_zero]
    exact this
  have hall := (hMF d hdΘ d' hdΘ' c hrel).and
    ((eventually_injective_depth hgood).and (eventually_injective_depth hg'))
  have hall' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal (fun i => ⟪X i, u + ε • (d + c • u)⟫) ∨
      IsCyclicUnimodal (fun i => ⟪X' i, u' + ε • d'⟫) :=
    hall.mono fun _ ⟨h1, h2, h3⟩ => h1 h2 h3
  rcases frequently_or_distrib.mp hall'.frequently with h | h
  · exact T.isRupert_of_freq hdΘ (frequently_unimodal_tilt X u d c h)
  · exact T'.isRupert_of_freq hdΘ' h

/-- **Theorem 24.3, two tests, depth form.**  As `isRupert_of_tiltTests_curve`, with
metric-freeness stated for the depth functionals: for every coupled pair `(w, w′)` near
`(u, u′)` (`⟪w, u′⟫ = ⟪u, w′⟫`, which is the case `(w, w′) = (G′u, G′u′)` for a symmetric `G′`)
at which the labels of both rims have distinct depths, `X` or `X′` is cyclically unimodal. -/
theorem isRupert_of_tiltTests_metricFree {V : Finset ℝ³} {u u' : ℝ³} {k k' m m' : ℕ}
    [NeZero k] [NeZero k'] [NeZero m] [NeZero m'] {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k}
    {Θ : Set ℝ³} {X' : ZMod m → ℝ³} {σ' : ZMod m' → ZMod m} {Θ' : Set ℝ³}
    (T : TiltTest V u X σ Θ) (T' : TiltTest V u' X' σ' Θ')
    (hcompat : ⟪u, u'⟫ = 0 → ∃ d ∈ Θ, ∃ d' ∈ Θ', ⟪u', d⟫ = ⟪u, d'⟫)
    (hMF : ∀ᶠ p : ℝ³ × ℝ³ in 𝓝 (u, u'), ⟪p.1, u'⟫ = ⟪u, p.2⟫ →
      Function.Injective (fun i => ⟪X i, p.1⟫) → Function.Injective (fun i => ⟪X' i, p.2⟫) →
      IsCyclicUnimodal (fun i => ⟪X i, p.1⟫) ∨ IsCyclicUnimodal (fun i => ⟪X' i, p.2⟫)) :
    IsRupert V := by
  refine isRupert_of_tiltTests_curve T T' hcompat fun d _ d' _ c hrel => ?_
  let W : ℝ → ℝ³ × ℝ³ := fun ε => (u + ε • (d + c • u), u' + ε • d')
  have hW : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (u, u')) := by
    have hc' : Continuous W := by
      refine Continuous.prodMk ?_ ?_ <;> fun_prop
    simpa [W] using hc'.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  filter_upwards [hW.eventually hMF] with ε h1 h2 h3
  refine h1 ?_ h2 h3
  show ⟪u + ε • (d + c • u), u'⟫ = ⟪u, u' + ε • d'⟫
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [← hrel]

/-! ### Lemma 24.2: a tilt is a metric perturbation -/

theorem gram_ne_zero {u u' : ℝ³} (hu : u ≠ 0) (hind : ∀ t : ℝ, u' ≠ t • u) :
    ⟪u, u⟫ * ⟪u', u'⟫ - ⟪u, u'⟫ ^ 2 ≠ 0 := by
  intro hD
  have huu : ⟪u, u⟫ ≠ 0 := fun h => hu (inner_self_eq_zero.mp h)
  apply hind (⟪u, u'⟫ / ⟪u, u⟫)
  have : ⟪u' - (⟪u, u'⟫ / ⟪u, u⟫) • u, u' - (⟪u, u'⟫ / ⟪u, u⟫) • u⟫ = 0 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm u u']
    field_simp
    nlinarith [hD]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp this)

/-- **Lemma 24.2, the symmetric matrix.**  For views `u, u′` not proportional, vectors `A, B` with
`⟪u′, A⟫ = ⟪u, B⟫` are the images of `u, u′` under a symmetric operator `H`
(`H = [A B]U⁺ + (U⁺)ᵀ[A B]ᵀ − (U⁺)ᵀ M U⁺`, `U = [u u′]`, `M = Uᵀ[A B]`).  With
`A = d + c u`, `B = d′ + c′ u′` (`d ⊥ u`, `d′ ⊥ u′`) the metric `I + δH` (positive definite for
small `δ`) orders the depths along `u` by `(⟪u, x⟫, ⟪d, x⟫)` and along `u′` by
`(⟪u′, x⟫, ⟪d′, x⟫)`: `⟪x, (I + δH) u⟫ = (1 + δc) ⟪x, u⟫ + δ ⟪x, d⟫`. -/
theorem exists_symm_clm {u u' A B : ℝ³} (hu : u ≠ 0) (hind : ∀ t : ℝ, u' ≠ t • u)
    (h : ⟪u', A⟫ = ⟪u, B⟫) :
    ∃ H : ℝ³ →L[ℝ] ℝ³, (H : ℝ³ →ₗ[ℝ] ℝ³).IsSymmetric ∧ H u = A ∧ H u' = B := by
  have hD := gram_ne_zero hu hind
  set D : ℝ := ⟪u, u⟫ * ⟪u', u'⟫ - ⟪u, u'⟫ ^ 2 with hDdef
  -- dual vectors
  set a : ℝ³ := D⁻¹ • (⟪u', u'⟫ • u - ⟪u, u'⟫ • u') with ha
  set a' : ℝ³ := D⁻¹ • (⟪u, u⟫ • u' - ⟪u, u'⟫ • u) with ha'
  have e1 : ⟪a, u⟫ = 1 := by
    have hE : ⟪u', u'⟫ * ⟪u, u⟫ - ⟪u, u'⟫ * ⟪u', u⟫ = D := by
      rw [hDdef, real_inner_comm u' u]; ring
    rw [ha, real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hE]
    exact inv_mul_cancel₀ hD
  have e2 : ⟪a, u'⟫ = 0 := by
    rw [ha, real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm u' u]
    ring
  have e3 : ⟪a', u⟫ = 0 := by
    rw [ha', real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm u' u]
    ring
  have e4 : ⟪a', u'⟫ = 1 := by
    have hE : ⟪u, u⟫ * ⟪u', u'⟫ - ⟪u, u'⟫ * ⟪u, u'⟫ = D := by rw [hDdef]; ring
    rw [ha', real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hE]
    exact inv_mul_cancel₀ hD
  -- the operator
  let M11 := ⟪u, A⟫
  let M12 := ⟪u, B⟫
  let M22 := ⟪u', B⟫
  let H : ℝ³ →L[ℝ] ℝ³ :=
    (innerSL ℝ a).smulRight A + (innerSL ℝ a').smulRight B + (innerSL ℝ A).smulRight a +
    (innerSL ℝ B).smulRight a' - M11 • (innerSL ℝ a).smulRight a -
    M12 • (innerSL ℝ a').smulRight a - M12 • (innerSL ℝ a).smulRight a' -
    M22 • (innerSL ℝ a').smulRight a'
  have hH : ∀ x, H x = ⟪a, x⟫ • A + ⟪a', x⟫ • B + ⟪A, x⟫ • a + ⟪B, x⟫ • a' -
      (M11 * ⟪a, x⟫) • a - (M12 * ⟪a', x⟫) • a - (M12 * ⟪a, x⟫) • a' - (M22 * ⟪a', x⟫) • a' := by
    intro x
    simp only [H, sub_apply, add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      smul_smul]
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x y
    show ⟪H x, y⟫ = ⟪x, H y⟫
    rw [hH, hH]
    simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm A, real_inner_comm B, real_inner_comm a, real_inner_comm a',
      real_inner_comm x y]
    ring
  · rw [hH]
    have hAu : ⟪A, u⟫ = M11 := real_inner_comm _ _
    have hBu : ⟪B, u⟫ = M12 := real_inner_comm _ _
    rw [e1, e3, hAu, hBu]
    module
  · rw [hH]
    have hAu : ⟪A, u'⟫ = M12 := by rw [real_inner_comm]; exact h
    have hBu : ⟪B, u'⟫ = M22 := real_inner_comm _ _
    rw [e2, e4, hAu, hBu]
    module

/-- **Theorem 24.3 with Lemma 24.2, metric form.**  The views `u, u′` are not proportional, and the
pair of tilt tests is metric-free in the sense of the paper: for every symmetric `H` and all
small `δ > 0`, at the metric `G = I + δH` (the depth of `x` along `u` is `⟪x, G u⟫`, along `u′`
it is `⟪x, G u′⟫`), if both labelled rims have distinct depths then `X` or `X′` is cyclically
unimodal.  With compatible tilts (`hcompat`, from the sign sets by `compat_of_signs`), `V` is
Rupert with any number of ties on `X` and `X′`. -/
theorem isRupert_of_tiltTests_metric {V : Finset ℝ³} {u u' : ℝ³} {k k' m m' : ℕ}
    [NeZero k] [NeZero k'] [NeZero m] [NeZero m'] {X : ZMod k → ℝ³} {σ : ZMod k' → ZMod k}
    {Θ : Set ℝ³} {X' : ZMod m → ℝ³} {σ' : ZMod m' → ZMod m} {Θ' : Set ℝ³}
    (T : TiltTest V u X σ Θ) (T' : TiltTest V u' X' σ' Θ') (hind : ∀ t : ℝ, u' ≠ t • u)
    (hcompat : ⟪u, u'⟫ = 0 → ∃ d ∈ Θ, ∃ d' ∈ Θ', ⟪u', d⟫ = ⟪u, d'⟫)
    (hMF : ∀ H : ℝ³ →L[ℝ] ℝ³, (H : ℝ³ →ₗ[ℝ] ℝ³).IsSymmetric →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        Function.Injective (fun i => ⟪X i, ((1 : ℝ³ →L[ℝ] ℝ³) + δ • H) u⟫) →
        Function.Injective (fun i => ⟪X' i, ((1 : ℝ³ →L[ℝ] ℝ³) + δ • H) u'⟫) →
        IsCyclicUnimodal (fun i => ⟪X i, ((1 : ℝ³ →L[ℝ] ℝ³) + δ • H) u⟫) ∨
          IsCyclicUnimodal (fun i => ⟪X' i, ((1 : ℝ³ →L[ℝ] ℝ³) + δ • H) u'⟫)) :
    IsRupert V := by
  refine isRupert_of_tiltTests_curve T T' hcompat fun d _ d' _ c hrel => ?_
  obtain ⟨H, hsymm, hHu, hHu'⟩ := exists_symm_clm (A := d + c • u) (B := d') T.ne_zero hind (by
    simp only [inner_add_right, real_inner_smul_right]
    rw [← real_inner_comm d u'] at hrel
    rw [real_inner_comm u u']
    linarith)
  filter_upwards [hMF H hsymm] with δ hδ
  simpa [hHu, hHu'] using hδ

end Minimality

end
