module

public import Mathlib
public import Minimality.Type29Limit
public import Minimality.LimitRim
public import Minimality.Tilt
public import Minimality.Type16NF

@[expose] public section

/-!
# LimitSeq (generic, statements): finite-certificate limit theorem and tie restoration

Statements of the generic limit tools (all proved in this file); nothing here is type-specific.

* `LabTest n`: a labelled test = a view (function of the shape `y : Fin n → ℝ³`) and a cyclic label sequence.
* `isRupert_or_hdn_of_cert_seq` (proved): Lemma 18.2 + 16.27' for finitely many tests; the conclusion
  is "Rupert, or an HDN at the view of one of the tests", i.e. `NoHDNAt` is needed only at the
  certificate's view, not at all named views.
* `exists_L_prescribed_ties`: near the identity the unimodular linear maps `L` realize
  every small prescribed values of `k` independent tie functionals `⟪L d_t, L u_t⟫`, uniformly in
  small perturbations of `(d_t, u_t)`.  One statement serves tie *restoration* (values 0; ≤ 2 ties in
  the paper, any number in the lemma) and tie *refinement* (values of prescribed signs; Theorem 24.2).
* `exists_seq_restore_ties`: a generic sequence `θ_j → θ` with `P(θ_j) ≠ 0` and `L_j → 1`
  such that the ties of the limit hold at `L_j ∘ shape θ_j` (generalizes the one-tie shear of
  Type29Limit, `restore`).
* `isRupert_or_hdn_of_generic_cert`:
  the assembled "limit theorem": certificates at generic `L ∘ shape θ'` with the ties of `shape θ`
  give Rupert or an HDN at a certificate's view.

View covariance: a "view" `view : (Fin n → ℝ³) → ℝ³` is *covariant* if `view (L ∘ y) = L (view y)`
for every unimodular `L` (difference views, `planeLine` views, and their sign flips).  Then
`⟪L (y a - y b), view (L ∘ y)⟫ = ⟪L (y a - y b), L (view y)⟫ = ⟪(y a - y b), G (view y)⟫`, `G = Lᵀ L`.
-/

set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Labelled tests -/

/-- A labelled test: a view as a function of the shape and a cyclic label sequence. -/
structure LabTest (n : ℕ) where
  k : ℕ
  [hk : NeZero k]
  view : (Fin n → ℝ³) → ℝ³
  lab : ZMod k → Fin n

attribute [instance] LabTest.hk

/-- The test is certified at the shape `y`: a labelled rim certificate at its view. -/
def LabTest.Cert {n : ℕ} (T : LabTest n) (y : Fin n → ℝ³) : Prop :=
  RimCertAt y (T.view y) T.lab

/-- Corner depths of the test's rim at the shape `y`. -/
noncomputable def LabTest.depth {n : ℕ} (T : LabTest n) (y : Fin n → ℝ³) : ZMod T.k → ℝ :=
  fun i => ⟪y (T.lab i), T.view y⟫

/-- The sign flip of a test (the certificate may sit at `-u`). -/
def LabTest.neg {n : ℕ} (T : LabTest n) : LabTest n := { T with view := fun y => -T.view y }

/-- Apply a linear map to every point of a shape. -/
def mapShape {n : ℕ} (L : ℝ³ →L[ℝ] ℝ³) (y : Fin n → ℝ³) : Fin n → ℝ³ := fun i => L (y i)

/-- A covariant view: unimodular linear maps act on it. -/
def CovView {n : ℕ} (view : (Fin n → ℝ³) → ℝ³) : Prop :=
  Continuous view ∧ ∀ (L : ℝ³ →L[ℝ] ℝ³) (y : Fin n → ℝ³), LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
    view (mapShape L y) = L (view y)

/-! ### The finite-certificate limit theorem -/

/-- **Generic finite-certificate limit theorem (Lemma 18.2 + 16.27').**  Finitely many tests; shapes
`K j → x` (no point inside a segment, not coplanar), each test's view converging, and frequently some
test certified with the ties of the limit's rim preserved.  Then `x` is Rupert unless some test
(whose view is nonzero) has an HDN at its view in the limit. -/
theorem isRupert_or_hdn_of_cert_seq {n : ℕ} {ι : Type*} [Finite ι] (T : ι → LabTest n)
    (x : Fin n → ℝ³)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    (hview0 : ∀ c, (T c).view x ≠ 0)
    (K : ℕ → Fin n → ℝ³) (hK : ∀ m, Tendsto (fun j => K j m) atTop (𝓝 (x m)))
    (hview : ∀ c, Tendsto (fun j => (T c).view (K j)) atTop (𝓝 ((T c).view x)))
    (hc : ∃ᶠ j in atTop, ∃ c, (T c).Cert (K j) ∧
      ∀ i j' : ZMod (T c).k, ⟪x ((T c).lab i), (T c).view x⟫ = ⟪x ((T c).lab j'), (T c).view x⟫ →
        ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫) :
    IsRupert (univ.image x) ∨ ∃ c, ¬ NoHDNAt (univ.image x) ((T c).view x) := by
  obtain ⟨c, hcf⟩ := frequently_exists_of_finite hc
  by_cases hN : NoHDNAt (univ.image x) ((T c).view x)
  · exact Or.inl (isRupert_of_tendsto_rimCert x hseg hsp (T c).lab (hview0 c) hN
      K (fun j => (T c).view (K j)) hK (hview c) hcf)
  · exact Or.inr ⟨c, hN⟩

theorem exists_limit_rimCert_aux {n : ℕ} (x : Fin n → ℝ³)
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    {k : ℕ} [NeZero k] (lab : ZMod k → Fin n) {u : ℝ³} (hu : u ≠ 0)
    {ι : Type*} {l : Filter ι} (xs : ι → Fin n → ℝ³) (us : ι → ℝ³)
    (hxs : ∀ m, Tendsto (fun t => xs t m) l (𝓝 (x m))) (hus : Tendsto us l (𝓝 u))
    (hcert : ∃ᶠ t in l, RimCertAt (xs t) (us t) lab ∧
      ∀ i j, ⟪x (lab i), u⟫ = ⟪x (lab j), u⟫ → ⟪xs t (lab i), us t⟫ = ⟪xs t (lab j), us t⟫) :
    ∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod k), RimCertAt x u (lab ∘ σ) := by
  classical
  set X : ZMod k → ℝ³ := fun i => x (lab i) with hXdef
  have hc := hcert.mono fun _ h => h.1
  -- Lemma 18.2 at `K`
  have hW : ∀ a b c, CycBetween a b c → 0 ≤ det3 (X b - X a) (X c - X a) u :=
    fun a b c h => cyc_nonneg_of_tendsto hxs hus hc h
  have hS : ∀ m, SuppIn u X (x m) := fun m =>
    suppIn_of_tendsto hu hus (fun i => hxs (lab i)) (hxs m) (hc.mono fun t ht => ht.suppIn m)
  have hZ : IsRobustUnimodal (fun i => ⟪X i, u⟫) :=
    isRobustUnimodal_of_tendsto_ties (fun i => (hxs (lab i)).inner hus)
      (hcert.mono fun t ht => ⟨ht.1.robust, ht.2⟩)
  -- the frame at `K`
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  set P : ℝ³ → ℝ² := fun v => proj_xy (R.toEuclideanLin v) with hPdef
  have hPsub : ∀ a b, P a - P b = P (a - b) := fun a b => proj_rot_sub R a b
  have hPadd : ∀ a b, P (a + b) = P a + P b := fun a b => by
    simp only [hPdef, map_add, proj_xy_add']
  have hPsmul : ∀ (c : ℝ) a, P (c • a) = c • P a := fun c a => by
    simp only [hPdef, map_smul, proj_xy_smul']
  have hPu : P u = 0 := by
    simp only [hPdef, hRu, proj_xy_smul']
    have : proj_xy ez = 0 := by ext j; fin_cases j <;> simp [proj_xy, ez]
    rw [this, smul_zero]
  set p : ZMod k → ℝ² := fun i => P (X i) with hpdef
  have hW2 : ∀ a b c, CycBetween a b c → 0 ≤ cross2 (p b - p a) (p c - p a) := by
    intro a b c h
    have := hW a b c h
    rw [← cross2_proj_rot hR hRu, ← proj_rot_sub, ← proj_rot_sub] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hr
  -- every point projects into the hull of the labels
  have hhull : ∀ m, P (x m) ∈ convexHull ℝ (Set.range p) := by
    intro m
    by_contra hnot
    obtain ⟨f, c, hfz, hfC⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
      ((Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)).isClosed hnot
    have hf : ∀ z : ℝ², f z = ⟪!₂[f (EuclideanSpace.single 0 1), f (EuclideanSpace.single 1 1)],
        z⟫ := by
      intro z
      have hz : z = z 0 • EuclideanSpace.single 0 1 + z 1 • EuclideanSpace.single 1 1 := by
        ext j; fin_cases j <;> simp
      conv_lhs => rw [hz]
      rw [map_add, map_smul, map_smul]
      simp [PiLp.inner_apply, Fin.sum_univ_two, smul_eq_mul]
    obtain ⟨w, hwv, hwu, -⟩ := exists_lift_screen hR hRu
      (-!₂[f (EuclideanSpace.single 0 1), f (EuclideanSpace.single 1 1)])
    obtain ⟨i, hi⟩ := hS m w hwu
    rw [hwv, hwv, inner_neg_left, inner_neg_left, ← hf, ← hf] at hi
    have := hfC (p i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    simp only [hpdef, hXdef] at this hi
    linarith
  -- the labels are not on one line
  have hNC : ∃ a b c, cross2 (p b - p a) (p c - p a) ≠ 0 := by
    by_contra hcol
    push Not at hcol
    obtain ⟨i, j, l', m, hdet⟩ := hsp
    apply hdet
    -- a nonzero screen functional constant on the labels
    obtain ⟨ν, hν0, hν⟩ : ∃ ν : ℝ², ν ≠ 0 ∧ ∀ a, ⟪ν, p a - p 0⟫ = 0 := by
      by_cases hall : ∀ a, p a = p 0
      · refine ⟨EuclideanSpace.single 0 1, ?_, fun a => by rw [hall a, sub_self, inner_zero_right]⟩
        intro h0
        have := congrArg (fun z : ℝ² => z 0) h0
        simp at this
      push Not at hall
      obtain ⟨b, hb⟩ := hall
      refine ⟨!₂[-(p b - p 0) 1, (p b - p 0) 0], ?_, fun a => ?_⟩
      · intro h0
        apply hb
        have h0' := congrArg (fun z : ℝ² => z 0) h0
        have h1' := congrArg (fun z : ℝ² => z 1) h0
        simp at h0' h1'
        rw [← sub_eq_zero]
        ext j; fin_cases j <;> simp <;> linarith
      · rw [inner_rot_eq_cross2]; exact hcol 0 b a
    have hplane : ∀ z ∈ convexHull ℝ (Set.range p), ⟪ν, z - p 0⟫ = 0 := by
      intro z hz
      have hconv : Convex ℝ {z : ℝ² | ⟪ν, z - p 0⟫ = 0} := by
        have : {z : ℝ² | ⟪ν, z - p 0⟫ = 0} = {z : ℝ² | ⟪ν, z⟫ = ⟪ν, p 0⟫} := by
          ext z; simp only [Set.mem_setOf_eq, inner_sub_right, sub_eq_zero]
        rw [this]
        exact convex_hyperplane (innerₛₗ ℝ ν).isLinear _
      refine convexHull_min ?_ hconv hz
      rintro _ ⟨a, rfl⟩
      exact hν a
    obtain ⟨w, hwv, -, hw0⟩ := exists_lift_screen hR hRu ν
    have hperp : ∀ a b : Fin n, ⟪w, x b - x a⟫ = 0 := by
      intro a b
      have ha := hplane _ (hhull a)
      have hb := hplane _ (hhull b)
      have e : proj_xy (R.toEuclideanLin (x b - x a)) = (P (x b) - p 0) - (P (x a) - p 0) := by
        rw [← proj_rot_sub]; abel
      rw [hwv, e, inner_sub_right, ha, hb, sub_zero]
    exact det3_eq_zero_of_perp (hw0 hν0) (by rw [real_inner_comm]; exact hperp _ _)
      (by rw [real_inner_comm]; exact hperp _ _) (by rw [real_inner_comm]; exact hperp _ _)
  -- the corner rim
  obtain ⟨k', hk', σ, hσcyc, hq, hpin⟩ := exists_cornerRim p hW2 hNC
  have hhull' : ∀ m, P (x m) ∈ convexHull ℝ (Set.range (p ∘ σ)) := fun m =>
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hpin i) (convex_convexHull ℝ _) (hhull m)
  refine ⟨k', hk', σ, ?_⟩
  have hPd : ∀ a b : ℝ³, r * cross2 (P a) (P b) = det3 a b u := fun a b =>
    cross2_proj_rot hR hRu a b
  refine ⟨hq.1, fun i j hi hj => ?_, fun m i => ?_, hZ.comp σ hσcyc⟩
  · have := hq.2 i j hi hj
    simp only [Function.comp, hpdef, hXdef] at this ⊢
    rw [hPsub, hPsub] at this
    rw [← hPd]
    exact mul_pos hr this
  · have := hq.left_of_mem_convexHull i (hhull' m)
    simp only [Function.comp, hpdef, hXdef] at this ⊢
    rw [hPsub, hPsub] at this
    rw [← hPd]
    exact mul_nonneg hr.le this

theorem exists_limit_rimCert {n : ℕ} {ι : Type*} [Finite ι] (T : ι → LabTest n)
    (x : Fin n → ℝ³)
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    (hview0 : ∀ c, (T c).view x ≠ 0)
    (K : ℕ → Fin n → ℝ³) (hK : ∀ m, Tendsto (fun j => K j m) atTop (𝓝 (x m)))
    (hview : ∀ c, Tendsto (fun j => (T c).view (K j)) atTop (𝓝 ((T c).view x)))
    (c : ι) (hcf : ∃ᶠ j in atTop, (T c).Cert (K j) ∧
      ∀ i j' : ZMod (T c).k, ⟪x ((T c).lab i), (T c).view x⟫ = ⟪x ((T c).lab j'), (T c).view x⟫ →
        ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫) :
    ∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (T c).k),
      RimCertAt x ((T c).view x) ((T c).lab ∘ σ) :=
  exists_limit_rimCert_aux x hsp (T c).lab (hview0 c) K (fun j => (T c).view (K j)) hK (hview c) hcf

/-! ### Realizing prescribed tie values by unimodular maps -/

/-- Linear independence of the tie functionals `G ↦ ⟪d_t, G u_t⟫ + ⟪u_t, G d_t⟫` (the functional of
`G = Lᵀ L` on symmetric maps; Lemma 18.6 step 4 / 24.2). -/
def TieIndep {q : ℕ} (d u : Fin q → ℝ³) : Prop :=
  ∀ lam : Fin q → ℝ, (∀ G : ℝ³ →L[ℝ] ℝ³, ∑ t, lam t * (⟪d t, G (u t)⟫ + ⟪u t, G (d t)⟫) = 0) →
    lam = 0

/-! #### Proof of the core: open mapping for `L(K) = det(1+K)^(-1/3) • (1+K)` -/

noncomputable def detC (K : ℝ³ →L[ℝ] ℝ³) : ℝ := LinearMap.det (K : ℝ³ →ₗ[ℝ] ℝ³)

theorem contDiff_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiff ℝ 1 (fun M : ι → ι → ℝ => (Matrix.of M).det) := by
  simp_rw [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.mul contDiff_const ?_
  refine contDiff_prod fun i _ => ?_
  exact (contDiff_apply ℝ ℝ i).comp (contDiff_apply ℝ (ι → ℝ) (σ i))

theorem contDiff_detC : ContDiff ℝ 1 detC := by
  let b := Module.finBasis ℝ ℝ³
  let T : (ℝ³ →L[ℝ] ℝ³) →ₗ[ℝ] (Fin (Module.finrank ℝ ℝ³) → Fin (Module.finrank ℝ ℝ³) → ℝ) :=
    (LinearMap.toMatrix b b).toLinearMap ∘ₗ (ContinuousLinearMap.coeLM ℝ)
  have hT : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have h1 : ContDiff ℝ 1 T := (LinearMap.toContinuousLinearMap T).contDiff
  have h2 := contDiff_matrix_det.comp h1
  convert h2 using 1
  funext K
  have := LinearMap.det_toMatrix b (K : ℝ³ →ₗ[ℝ] ℝ³)
  simp only [detC, Function.comp, T, LinearMap.coe_comp, LinearEquiv.coe_coe, ContinuousLinearMap.coeLM_apply]
  rw [← this]; rfl

/-- The tie functionals as a linear map `(ℝ³ →L ℝ³) → ℝ^q`. -/
noncomputable def tieΦ {q : ℕ} (d u : Fin q → ℝ³) : (ℝ³ →L[ℝ] ℝ³) →ₗ[ℝ] (Fin q → ℝ) where
  toFun G t := ⟪d t, G (u t)⟫ + ⟪u t, G (d t)⟫
  map_add' G H := by funext t; simp [inner_add_right]; ring
  map_smul' c G := by funext t; simp [inner_smul_right]; ring

theorem tieΦ_surjective {q : ℕ} (d u : Fin q → ℝ³) (h : TieIndep d u) :
    Function.Surjective (tieΦ d u) := by
  rw [← LinearMap.dualMap_injective_iff]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have key : ∀ G, φ (tieΦ d u G) = 0 := fun G => by
    have := congrArg (fun ψ => ψ G) hφ
    simpa using this
  have hlam := h (fun t => φ (Pi.single t 1)) (by
    intro G
    have := key G
    have hx : tieΦ d u G = ∑ t, (tieΦ d u G t) • (Pi.single t (1:ℝ) : Fin q → ℝ) := by
      funext s; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [tieΦ]; ring)
  apply LinearMap.ext
  intro w
  have hx : w = ∑ t, (w t) • (Pi.single t (1:ℝ) : Fin q → ℝ) := by
    funext s; simp [Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  simp [congrFun hlam]


/-- Independence of the tie functionals is an open condition on `(d, u)` (finite-dimensional:
injectivity of a linear map `ℝ^q → (ℝ³ →L ℝ³)*` depending continuously on `(d, u)`). -/
theorem TieIndep.eventually {q : ℕ} {d u : Fin q → ℝ³} (h : TieIndep d u) :
    ∀ᶠ p in 𝓝 (d, u), TieIndep p.1 p.2 := by
  have hs := tieΦ_surjective d u h
  choose G hG using fun r : Fin q => hs (Pi.single r 1)
  let A : ((Fin q → ℝ³) × (Fin q → ℝ³)) → Matrix (Fin q) (Fin q) ℝ :=
    fun p t r => ⟪p.1 t, G r (p.2 t)⟫ + ⟪p.2 t, G r (p.1 t)⟫
  have hA0 : A (d, u) = 1 := by
    ext t r
    have := congrFun (hG r) t
    simp only [tieΦ, LinearMap.coe_mk, AddHom.coe_mk] at this
    simp only [A, this, Matrix.one_apply, Pi.single_apply]
  have hcont : Continuous fun p => (A p).det := by
    refine Continuous.matrix_det (continuous_pi fun t => continuous_pi fun r => ?_)
    have h1 : Continuous fun p : (Fin q → ℝ³) × (Fin q → ℝ³) => p.1 t := by fun_prop
    have h2 : Continuous fun p : (Fin q → ℝ³) × (Fin q → ℝ³) => p.2 t := by fun_prop
    exact (h1.inner ((G r).continuous.comp h2)).add (h2.inner ((G r).continuous.comp h1))
  have hne : ∀ᶠ p in 𝓝 (d, u), (A p).det ≠ 0 := by
    apply hcont.continuousAt.eventually_ne
    simp [hA0]
  refine hne.mono fun p hp lam hlam => ?_
  apply Matrix.eq_zero_of_vecMul_eq_zero hp
  funext r
  simpa [Matrix.vecMul, dotProduct, A] using hlam (G r)

/-- Unimodular normalization of `1 + K`: `lamC K = det(1+K)^(-1/3)`. -/
noncomputable def lamC (K : ℝ³ →L[ℝ] ℝ³) : ℝ := (detC (1 + K)) ^ (-(1/3 : ℝ))

noncomputable def Lm (K : ℝ³ →L[ℝ] ℝ³) : ℝ³ →L[ℝ] ℝ³ := lamC K • (1 + K)

theorem detC_one : detC (1 : ℝ³ →L[ℝ] ℝ³) = 1 := by simp [detC]

theorem lamC_zero : lamC 0 = 1 := by simp [lamC, detC_one]

theorem Lm_zero : Lm 0 = 1 := by simp [Lm, lamC_zero]

theorem contDiffAt_lamC : ContDiffAt ℝ 1 lamC 0 := by
  have h1 : ContDiffAt ℝ 1 (fun K : ℝ³ →L[ℝ] ℝ³ => detC (1 + K)) 0 :=
    (contDiff_detC.comp (contDiff_const.add contDiff_id)).contDiffAt
  exact h1.rpow_const_of_ne (by simp [detC_one])

theorem contDiffAt_Lm : ContDiffAt ℝ 1 Lm 0 := by
  unfold Lm
  exact contDiffAt_lamC.smul (contDiff_const.add contDiff_id).contDiffAt

theorem det_Lm {K : ℝ³ →L[ℝ] ℝ³} (h : 0 < detC (1 + K)) :
    LinearMap.det (Lm K : ℝ³ →ₗ[ℝ] ℝ³) = 1 := by
  have : (Lm K : ℝ³ →ₗ[ℝ] ℝ³) = lamC K • ((1 + K : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) := by
    ext x; simp [Lm]
  rw [this, LinearMap.det_smul, finrank_euclideanSpace_fin]
  have h2 : (lamC K) ^ 3 = (detC (1 + K))⁻¹ := by
    unfold lamC
    rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]
    norm_num [Real.rpow_neg_one]
  rw [h2]
  have : LinearMap.det ((1 + K : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) = detC (1 + K) := rfl
  rw [this]
  field_simp


theorem hasDerivAt_lamC_line (K : ℝ³ →L[ℝ] ℝ³) :
    ∃ l', HasDerivAt (fun s : ℝ => lamC (s • K)) l' 0 := by
  have hd : DifferentiableAt ℝ lamC 0 := contDiffAt_lamC.differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => s • K) ((1 : ℝ) • K) 0 := (hasDerivAt_id (0:ℝ)).smul_const K
  have h2 : HasFDerivAt lamC (fderiv ℝ lamC 0) ((0:ℝ) • K) := by
    have h0K : (0:ℝ) • K = 0 := by ext x; simp
    rw [h0K]; exact hd.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0:ℝ) h1
  exact ⟨_, h3⟩

theorem hasDerivAt_tie_line (d u : ℝ³) (h0 : ⟪d, u⟫ = 0) (K : ℝ³ →L[ℝ] ℝ³) :
    HasDerivAt (fun s : ℝ => ⟪Lm (s • K) d, Lm (s • K) u⟫) (⟪K d, u⟫ + ⟪d, K u⟫) 0 := by
  obtain ⟨l', hl⟩ := hasDerivAt_lamC_line K
  have hl2 : HasDerivAt (fun s : ℝ => lamC (s • K) * lamC (s • K)) _ 0 := hl.mul hl
  have hP : HasDerivAt (fun s : ℝ => ⟪d, u⟫ + s * (⟪K d, u⟫ + ⟪d, K u⟫) + s ^ 2 * ⟪K d, K u⟫)
      (⟪K d, u⟫ + ⟪d, K u⟫) 0 := by
    have a1 : HasDerivAt (fun s : ℝ => s * (⟪K d, u⟫ + ⟪d, K u⟫)) (⟪K d, u⟫ + ⟪d, K u⟫) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (⟪K d, u⟫ + ⟪d, K u⟫)
    have a2 : HasDerivAt (fun s : ℝ => s ^ 2 * ⟪K d, K u⟫) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0:ℝ))).mul_const ⟪K d, K u⟫
    have := ((hasDerivAt_const (0:ℝ) ⟪d, u⟫).add a1).add a2
    convert this using 1
    simp
  have hm := hl2.mul hP
  have hfun : (fun s : ℝ => ⟪Lm (s • K) d, Lm (s • K) u⟫) =
      fun s : ℝ => (lamC (s • K) * lamC (s • K)) *
        (⟪d, u⟫ + s * (⟪K d, u⟫ + ⟪d, K u⟫) + s ^ 2 * ⟪K d, K u⟫) := by
    funext s
    simp only [Lm, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, RCLike.conj_to_real]
    ring
  rw [hfun]
  convert hm using 1
  have h0K : (0:ℝ) • K = 0 := by ext x; simp
  simp [h0K, lamC_zero, h0]


set_option synthInstance.maxHeartbeats 200000 in
theorem exists_L_prescribed_ties_core {q : ℕ} (d u : Fin q → ℝ³) (h0 : ∀ t, ⟪d t, u t⟫ = 0)
    (hind : TieIndep d u) :
    ∀ ν > 0, ∃ η > 0, ∀ (d' u' : Fin q → ℝ³) (c : Fin q → ℝ),
      (∀ t, ‖d' t - d t‖ < η ∧ ‖u' t - u t‖ < η ∧ |c t| < η) →
      ∃ L : ℝ³ →L[ℝ] ℝ³, ‖L - 1‖ < ν ∧ LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 ∧
        ∀ t, ⟪L (d' t), L (u' t)⟫ = c t := by
  intro ν hν
  let X := (ℝ³ →L[ℝ] ℝ³) × ((Fin q → ℝ³) × (Fin q → ℝ³))
  let x0 : X := (0, (d, u))
  let tieF : X → (Fin q → ℝ) := fun x t => ⟪Lm x.1 (x.2.1 t), Lm x.1 (x.2.2 t)⟫
  have hLm : ContDiffAt ℝ 1 (fun x : X => Lm x.1) x0 :=
    contDiffAt_Lm.comp x0 (contDiff_fst.contDiffAt)
  have hCD : ContDiffAt ℝ 1 tieF x0 := by
    refine contDiffAt_pi.2 fun t => ?_
    have e1 : ContDiff ℝ 1 (fun x : X => x.2.1 t) :=
      (contDiff_apply ℝ ℝ³ t).comp (contDiff_fst.comp contDiff_snd)
    have e2 : ContDiff ℝ 1 (fun x : X => x.2.2 t) :=
      (contDiff_apply ℝ ℝ³ t).comp (contDiff_snd.comp contDiff_snd)
    exact (hLm.clm_apply e1.contDiffAt).inner ℝ (hLm.clm_apply e2.contDiffAt)
  set D1 : X →L[ℝ] (Fin q → ℝ) := fderiv ℝ tieF x0 with hD1def
  have hD1 : HasStrictFDerivAt tieF D1 x0 := hCD.hasStrictFDerivAt one_ne_zero
  let Fm : X → (Fin q → ℝ) × ((Fin q → ℝ³) × (Fin q → ℝ³)) := fun x => (tieF x, x.2)
  let D' : X →L[ℝ] (Fin q → ℝ) × ((Fin q → ℝ³) × (Fin q → ℝ³)) :=
    D1.prod (ContinuousLinearMap.snd ℝ (ℝ³ →L[ℝ] ℝ³) ((Fin q → ℝ³) × (Fin q → ℝ³)))
  have hF : HasStrictFDerivAt Fm D' x0 :=
    hD1.prodMk (ContinuousLinearMap.snd ℝ (ℝ³ →L[ℝ] ℝ³)
      ((Fin q → ℝ³) × (Fin q → ℝ³))).hasStrictFDerivAt
  -- derivative along K
  have hline : ∀ (K : ℝ³ →L[ℝ] ℝ³) t, D1 (K, 0) t = ⟪K (d t), u t⟫ + ⟪d t, K (u t)⟫ := by
    intro K t
    have hγ : HasDerivAt (fun s : ℝ => ((s • K, (d, u)) : X)) ((K, 0) : X) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).smul_const K).prodMk (hasDerivAt_const (0:ℝ) (d, u))
      simpa using this
    have h1 : HasFDerivAt tieF D1 (((0:ℝ) • K, (d, u)) : X) := by
      have h0K : (0:ℝ) • K = 0 := by ext x; simp
      rw [h0K]; exact hD1.hasFDerivAt
    have h2 := h1.comp_hasDerivAt (0:ℝ) hγ
    have h3 := (hasDerivAt_pi.1 h2) t
    exact h3.unique (hasDerivAt_tie_line (d t) (u t) (h0 t) K)
  have hsurj : D'.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨w, a, b⟩
    obtain ⟨K, hK⟩ := tieΦ_surjective d u hind (w - D1 (0, (a, b)))
    have hKK : D1 (K, 0) = w - D1 (0, (a, b)) := by
      funext t
      rw [hline K t]
      have := congrFun hK t
      simp only [tieΦ, LinearMap.coe_mk, AddHom.coe_mk] at this
      have e := real_inner_comm (K (d t)) (u t)
      linarith [this]
    have hsplit : ((K, (a, b)) : X) = (K, 0) + (0, (a, b)) := by simp
    refine ⟨(K, (a, b)), Prod.ext ?_ rfl⟩
    show D1 (K, (a, b)) = w
    rw [hsplit, map_add, hKK]; abel
  haveI : CompleteSpace X := by unfold X; infer_instance
  have hmap := hF.map_nhds_eq_of_surj hsurj
  -- the neighbourhood N of x0
  have hdet0 : ContinuousAt (fun x : X => detC (1 + x.1)) x0 :=
    (contDiff_detC.continuous.comp (continuous_const.add continuous_fst)).continuousAt
  have hLc : ContinuousAt (fun x : X => Lm x.1) x0 := hLm.continuousAt
  have hN : {x : X | ‖Lm x.1 - 1‖ < ν ∧ 0 < detC (1 + x.1)} ∈ 𝓝 x0 := by
    refine Filter.inter_mem ?_ ?_
    · have : ∀ᶠ x in 𝓝 x0, dist (Lm x.1) 1 < ν := by
        have h := hLc.tendsto
        have h0' : Lm x0.1 = 1 := Lm_zero
        rw [h0'] at h
        exact h.eventually (Metric.ball_mem_nhds _ hν)
      exact this.mono (fun x hx => by rw [dist_eq_norm] at hx; exact hx)
    · have : detC (1 + x0.1) = 1 := by simp [x0, detC_one]
      exact hdet0.eventually (lt_mem_nhds (by show (0:ℝ) < detC (1 + x0.1); rw [this]; norm_num))
  have himg := (Filter.image_mem_map hN : Fm '' _ ∈ Filter.map Fm (𝓝 x0))
  rw [hmap] at himg
  have hFx0 : Fm x0 = (0, (d, u)) := by
    simp only [Fm, tieF, x0, Lm_zero]
    ext t <;> simp [h0 t]
  rw [hFx0] at himg
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 himg
  refine ⟨η, hη, ?_⟩
  intro d' u' c hc
  have hmem : ((c, (d', u')) : (Fin q → ℝ) × ((Fin q → ℝ³) × (Fin q → ℝ³))) ∈ Metric.ball (0, (d, u)) η := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [dist_pi_lt_iff hη]; intro t; simpa [Real.dist_eq] using (hc t).2.2
    · rw [Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ?_⟩
      · rw [dist_pi_lt_iff hη]; intro t; simpa [dist_eq_norm] using (hc t).1
      · rw [dist_pi_lt_iff hη]; intro t; simpa [dist_eq_norm] using (hc t).2.1
  obtain ⟨x, ⟨hx1, hx2⟩, hxF⟩ := hball hmem
  have hx3 : x.2 = (d', u') := congrArg Prod.snd hxF
  have hx4 : tieF x = c := congrArg Prod.fst hxF
  refine ⟨Lm x.1, by simpa using hx1, det_Lm hx2, fun t => ?_⟩
  have := congrFun hx4 t
  simp only [tieF, hx3] at this
  exact this

/-- **Core (open mapping for tie values).**  If `⟪d_t, u_t⟫ = 0` and the tie functionals are
independent, then for every `ν > 0` there is `η > 0` such that for all `(d', u')` within `η` of `(d, u)`
and all target values `c` with `|c_t| < η`, some unimodular `L` with `‖L - 1‖ < ν` has
`⟪L d'_t, L u'_t⟫ = c_t` for all t.  (Proof: open mapping theorem (`HasStrictFDerivAt.map_nhds_eq_of_surj`) for the map
`(K, d', u') ↦ (tie values, d', u')` with `L(K) = det(1+K)^(-1/3) • (1+K)`; the derivative in `K` is `K ↦ (f_t(K))_t`, surjective by `TieIndep`.  Original sketch: implicit function theorem for the map
`(s, d', u') ↦ (⟪L(s) d'_t, L(s) u'_t⟫)_t`, `L(s)` a product of shears `y ↦ y + s_i ⟪e_i, y⟫ b_i`,
`e_i ⊥ b_i`, which span `sl₃`; the derivative at `s = 0` pairs `(e b^T)` with the traceless
symmetric tie matrices, and tracelessness is automatic from `⟪d_t, u_t⟫ = 0`.) -/
theorem exists_L_prescribed_ties {q : ℕ} (d u : Fin q → ℝ³) (h0 : ∀ t, ⟪d t, u t⟫ = 0)
    (hind : TieIndep d u) :
    ∀ ν > 0, ∃ η > 0, ∀ (d' u' : Fin q → ℝ³) (c : Fin q → ℝ),
      (∀ t, ‖d' t - d t‖ < η ∧ ‖u' t - u t‖ < η ∧ |c t| < η) →
      ∃ L : ℝ³ →L[ℝ] ℝ³, ‖L - 1‖ < ν ∧ LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 ∧
        ∀ t, ⟪L (d' t), L (u' t)⟫ = c t := by
  exact exists_L_prescribed_ties_core d u h0 hind

/-- **Restoring ties along a generic sequence** (generalizes `exists_certSeq29`'s shear step; the
paper has ≤ 2 ties, the statement allows any independent list).  The `q` ties are
`⟪y (ab t).1 - y (ab t).2, view t y⟫ = 0` for covariant views; they hold at the limit shape
`shape θ` and are independent there.  Then there are `θs j → θ` off the zero set of `P` and unimodular
`L j → 1` such that the ties hold at `mapShape (L j) (shape (θs j))`. -/
theorem exists_seq_restore_ties {m n q : ℕ} (shape : (Fin m → ℝ) → Fin n → ℝ³)
    (hshape : Continuous shape) (P : MvPolynomial (Fin m) ℝ) (hP : P ≠ 0) (θ : Fin m → ℝ)
    (ab : Fin q → Fin n × Fin n) (view : Fin q → (Fin n → ℝ³) → ℝ³) (hview : ∀ t, CovView (view t))
    (hties : ∀ t, ⟪shape θ (ab t).1 - shape θ (ab t).2, view t (shape θ)⟫ = 0)
    (hind : TieIndep (fun t => shape θ (ab t).1 - shape θ (ab t).2) (fun t => view t (shape θ))) :
    ∃ (θs : ℕ → Fin m → ℝ) (L : ℕ → ℝ³ →L[ℝ] ℝ³),
      Tendsto θs atTop (𝓝 θ) ∧ Tendsto L atTop (𝓝 1) ∧ (∀ j, MvPolynomial.eval (θs j) P ≠ 0) ∧
      (∀ j, LinearMap.det (L j : ℝ³ →ₗ[ℝ] ℝ³) = 1) ∧
      ∀ j t, ⟪mapShape (L j) (shape (θs j)) (ab t).1 - mapShape (L j) (shape (θs j)) (ab t).2,
        view t (mapShape (L j) (shape (θs j)))⟫ = 0 := by
  obtain ⟨θs, hθs, hPθ⟩ := exists_seq_eval_ne_zero_fin hP θ
  let dd : (Fin m → ℝ) → Fin q → ℝ³ := fun θ' t => shape θ' (ab t).1 - shape θ' (ab t).2
  let uu : (Fin m → ℝ) → Fin q → ℝ³ := fun θ' t => view t (shape θ')
  have hdd : Continuous dd := by
    refine continuous_pi fun t => ?_
    exact ((continuous_apply (ab t).1).comp hshape).sub ((continuous_apply (ab t).2).comp hshape)
  have huu : Continuous uu := continuous_pi fun t => (hview t).1.comp hshape
  have hcore := exists_L_prescribed_ties (dd θ) (uu θ) hties hind
  have key : ∀ j : ℕ, ∃ n ≥ j, ∃ L : ℝ³ →L[ℝ] ℝ³, ‖L - 1‖ < 1 / ((j : ℝ) + 1) ∧
      LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 ∧ ∀ t, ⟪L (dd (θs n) t), L (uu (θs n) t)⟫ = 0 := by
    intro j
    obtain ⟨η, hη, hL⟩ := hcore (1 / ((j : ℝ) + 1)) (by positivity)
    have h1 : ∀ᶠ n in atTop, dd (θs n) ∈ Metric.ball (dd θ) η :=
      ((hdd.tendsto θ).comp hθs).eventually (Metric.ball_mem_nhds _ hη)
    have h2 : ∀ᶠ n in atTop, uu (θs n) ∈ Metric.ball (uu θ) η :=
      ((huu.tendsto θ).comp hθs).eventually (Metric.ball_mem_nhds _ hη)
    obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and (eventually_ge_atTop j))).exists
    rw [Metric.mem_ball, dist_pi_lt_iff hη] at hn1 hn2
    obtain ⟨L, hL1, hL2, hL3⟩ := hL (dd (θs n)) (uu (θs n)) (fun _ => 0) (fun t => by
      refine ⟨?_, ?_, by simpa using hη⟩
      · simpa [dist_eq_norm] using hn1 t
      · simpa [dist_eq_norm] using hn2 t)
    exact ⟨n, hn3, L, hL1, hL2, hL3⟩
  choose n hn L hL1 hL2 hL3 using key
  refine ⟨fun j => θs (n j), L, hθs.comp (tendsto_atTop_mono hn tendsto_id), ?_, fun j => hPθ _,
    hL2, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => (hL1 j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro j t
    have hc := (hview t).2 (L j) (shape (θs (n j))) (hL2 j)
    simp only [mapShape]
    rw [hc, ← map_sub]
    exact hL3 j t

/-! ### The assembled limit theorem -/

/-- **Limit theorem for a generic certificate** (what G3' uses).  `x = shape θ` is a limit of
`mapShape L (shape θ')`, `P θ' ≠ 0`, `L` unimodular near `1`, that preserve the listed ties
(`ties t = (a, b, view)`, covariant views, independent at `x`).  If every such shape carries a
certified test of the finite family `T`, and the listed ties include every tie of every test's rim
at the limit, then `x` is Rupert unless some test's view carries an HDN at the limit.

Proof: `exists_seq_restore_ties`, then `hcert` along the sequence, `frequently_exists_of_finite`,
`isRupert_or_hdn_of_cert_seq` (the tie-preservation hypothesis for the rim is `hcover`). -/
theorem isRupert_or_hdn_of_generic_cert {m n q : ℕ} {ι : Type*} [Finite ι]
    (shape : (Fin m → ℝ) → Fin n → ℝ³) (hshape : Continuous shape)
    (P : MvPolynomial (Fin m) ℝ) (hP : P ≠ 0) (θ : Fin m → ℝ)
    (T : ι → LabTest n) (hT : ∀ c, CovView (T c).view)
    (hseg : ∀ i j m' : Fin n, shape θ m' ≠ shape θ i → shape θ m' ≠ shape θ j →
      ∀ s : ℝ, 0 < s → s < 1 → shape θ m' ≠ shape θ i + s • (shape θ j - shape θ i))
    (hsp : ∃ i j l m' : Fin n,
      det3 (shape θ j - shape θ i) (shape θ l - shape θ i) (shape θ m' - shape θ i) ≠ 0)
    (hview0 : ∀ c, (T c).view (shape θ) ≠ 0)
    (ties : Fin q → ι × Fin n × Fin n)
    (hties : ∀ t, ⟪shape θ (ties t).2.1 - shape θ (ties t).2.2, (T (ties t).1).view (shape θ)⟫ = 0)
    (hind : TieIndep (fun t => shape θ (ties t).2.1 - shape θ (ties t).2.2)
      (fun t => (T (ties t).1).view (shape θ)))
    -- every tie of every test's rim at the limit follows from the listed ties, at any shape
    (hcover : ∀ y : Fin n → ℝ³, (∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (T (ties t).1).view y⟫ = 0) →
      ∀ c (i j : ZMod (T c).k),
        ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j), (T c).view (shape θ)⟫ →
        ⟪y ((T c).lab i), (T c).view y⟫ = ⟪y ((T c).lab j), (T c).view y⟫)
    -- generic certificates (the geometry; MF + R2T inside)
    (hcert : ∀ᶠ p in 𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³)), MvPolynomial.eval p.1 P ≠ 0 →
      LinearMap.det (p.2 : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      -- the listed ties stay independent at `p` (open condition, `TieIndep.eventually`)
      TieIndep (fun t => mapShape p.2 (shape p.1) (ties t).2.1 - mapShape p.2 (shape p.1) (ties t).2.2)
        (fun t => (T (ties t).1).view (mapShape p.2 (shape p.1))) →
      -- no new rim ties: a tie of a rim at `p` is a tie of the limit (closed condition; the proof
      -- of this theorem gets it eventually along the sequence from continuity)
      (∀ c (i j : ZMod (T c).k),
        ⟪mapShape p.2 (shape p.1) ((T c).lab i), (T c).view (mapShape p.2 (shape p.1))⟫ =
          ⟪mapShape p.2 (shape p.1) ((T c).lab j), (T c).view (mapShape p.2 (shape p.1))⟫ →
        ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j), (T c).view (shape θ)⟫) →
      (∀ t, ⟪mapShape p.2 (shape p.1) (ties t).2.1 - mapShape p.2 (shape p.1) (ties t).2.2,
        (T (ties t).1).view (mapShape p.2 (shape p.1))⟫ = 0) →
      ∃ c, (T c).Cert (mapShape p.2 (shape p.1))) :
    IsRupert (univ.image (shape θ)) ∨ ∃ c, ¬ NoHDNAt (univ.image (shape θ)) ((T c).view (shape θ)) := by
  obtain ⟨θs, L, hθs, hL, hPs, hdet, hrest⟩ := exists_seq_restore_ties shape hshape P hP θ
    (fun t => (ties t).2) (fun t => (T (ties t).1).view) (fun t => hT _) hties hind
  let K : ℕ → Fin n → ℝ³ := fun j => mapShape (L j) (shape (θs j))
  have hev : Continuous (fun p : (ℝ³ →L[ℝ] ℝ³) × ℝ³ => p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have hKt : ∀ i, Tendsto (fun j => K j i) atTop (𝓝 (shape θ i)) := by
    intro i
    have h1 : Tendsto (fun j => shape (θs j) i) atTop (𝓝 (shape θ i)) :=
      ((continuous_apply i).comp hshape |>.tendsto θ).comp hθs
    have := (hev.tendsto (1, shape θ i)).comp (hL.prodMk_nhds h1)
    exact this
  have hvt : ∀ c, Tendsto (fun j => (T c).view (K j)) atTop (𝓝 ((T c).view (shape θ))) := by
    intro c
    have h1 : Tendsto (fun j => (T c).view (shape (θs j))) atTop (𝓝 ((T c).view (shape θ))) :=
      (((hT c).1.comp hshape).tendsto θ).comp hθs
    have := (hev.tendsto (1, (T c).view (shape θ))).comp (hL.prodMk_nhds h1)
    exact Tendsto.congr (fun j => ((hT c).2 (L j) (shape (θs j)) (hdet j)).symm) this
  have hpt : Tendsto (fun j => (θs j, L j)) atTop (𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³))) :=
    hθs.prodMk_nhds hL
  have hcert' := hpt.eventually hcert
  -- independence along the sequence
  have hdv : Tendsto (fun j => ((fun t => K j (ties t).2.1 - K j (ties t).2.2),
      (fun t => (T (ties t).1).view (K j)))) atTop
      (𝓝 ((fun t => shape θ (ties t).2.1 - shape θ (ties t).2.2),
        (fun t => (T (ties t).1).view (shape θ)))) := by
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_pi_nhds.2 fun t => (hKt _).sub (hKt _)
    · exact tendsto_pi_nhds.2 fun t => hvt _
  have hind' := hdv.eventually hind.eventually
  -- no new rim ties along the sequence
  have hnew : ∀ᶠ j in atTop, ∀ c (i j' : ZMod (T c).k),
      ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫ →
      ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫ := by
    rw [Filter.eventually_all]; intro c
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j'
    by_cases h : ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ =
        ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫
    · exact Filter.Eventually.of_forall fun _ _ => h
    · have t1 := Tendsto.inner' (hKt ((T c).lab i)) (hvt c)
      have t2 := Tendsto.inner' (hKt ((T c).lab j')) (hvt c)
      have := (t1.sub t2).eventually_ne (sub_ne_zero.2 h)
      exact this.mono fun j hj heq => absurd (sub_eq_zero.2 heq) hj
  have hfreq : ∃ᶠ j in atTop, ∃ c, (T c).Cert (K j) ∧
      ∀ i j' : ZMod (T c).k, ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ =
        ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫ →
        ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫ := by
    refine ((hcert'.and (hind'.and hnew)).frequently).mono ?_
    rintro j ⟨hc, hi, hn⟩
    have hties' := hrest j
    obtain ⟨c, hcC⟩ := hc (hPs j) (hdet j) hi hn hties'
    exact ⟨c, hcC, fun i j' h => hcover (K j) hties' c i j' h⟩
  exact isRupert_or_hdn_of_cert_seq T (shape θ) hseg hsp hview0 K hKt hvt hfreq

end Minimality
