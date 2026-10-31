module

public import Minimality.OctAxis
public import Minimality.Type16Rims
public import Minimality.Type29K3
public import Minimality.RimCertLift
public import Minimality.Generic.TwoTie

@[expose] public section

/-!
# Two quad rims at two views: a robust rim from the sign product (generic)

The sign-product route to Lemma R2T's hypothesis `MF` (`robust_corner_rim_of_MF`): for two quad
rims `(d₀ e₀ d₁ e₁)` at a view `u` and `(f₀ g₀ f₁ g₁)` at a view `v` whose diagonals meet along both
views and whose four-determinant product is negative (`not_both_depthSep_gen`), the two rims are
never both depth-separated at any det-1 image of the shape (`mf_of_not_both_depthSep`); hence one of
them is robustly unimodal under at most two independent ties (`robust_rim_of_pair_signs`).  The
supporting lemmas: equivariance of `det3`, `galeD`, `axisView`, `SegMeet` under linear maps,
`hcover` from `OneTieAt` (`hcover_of_oneTieAt`), scalings of the views, and the independence
predicate `IndepF` of the tied pairs at two views.  No type-specific content.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter Noperts

/-! ### Linear maps (moved from `Type16Metric`) -/

/-- The determinant of a linear map of `ℝ³`, as the triple product of the images of the
standard basis. -/
noncomputable def detMap (M : ℝ³ →L[ℝ] ℝ³) : ℝ :=
  det3 (M (EuclideanSpace.single 0 1)) (M (EuclideanSpace.single 1 1))
    (M (EuclideanSpace.single 2 1))

theorem map_coord (M : ℝ³ →L[ℝ] ℝ³) (a : ℝ³) (j : Fin 3) :
    (M a) j = a 0 * (M (EuclideanSpace.single 0 1)) j + a 1 * (M (EuclideanSpace.single 1 1)) j +
      a 2 * (M (EuclideanSpace.single 2 1)) j := by
  have ha : a = a 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      a 1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
      a 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [ha]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem det3_map (M : ℝ³ →L[ℝ] ℝ³) (a b c : ℝ³) :
    det3 (M a) (M b) (M c) = detMap M * det3 a b c := by
  simp only [detMap, det3_expand, map_coord M a, map_coord M b, map_coord M c]
  ring

theorem planeLine_map (M : ℝ³ →L[ℝ] ℝ³) (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) :
    planeLine (M p₀) (M p₁) (M p₂) (M q₀) (M q₁) (M q₂) =
      detMap M • M (planeLine p₀ p₁ p₂ q₀ q₁ q₂) := by
  rw [planeLine, planeLine, ← map_sub M p₁ p₀, ← map_sub M p₂ p₀, ← map_sub M q₂ q₀,
    ← map_sub M q₁ q₀, det3_map, det3_map]
  simp only [map_sub, map_smul, smul_sub, smul_smul]

theorem robust_mul_ne_zero {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) {c : ℝ}
    (hc : c ≠ 0) : IsRobustUnimodal (fun i => c * z i) := by
  rcases lt_or_gt_of_ne hc with h | h
  · have := (hz.smul (neg_pos.mpr h)).neg
    convert this using 2 with i
    ring
  · exact hz.smul h

theorem detMap_eq_det (L : ℝ³ →L[ℝ] ℝ³) : detMap L = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp only [detMap, det3_expand, LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply]
  ring

/-- `det3` is multiplied by `det L`. -/
theorem det3_map_det (L : ℝ³ →L[ℝ] ℝ³) (u v w : ℝ³) :
    det3 (L u) (L v) (L w) = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) * det3 u v w := by
  rw [det3_map, detMap_eq_det]

/-! ### Gale data and axis views are equivariant (transport by precomposition with `L⁻¹`) -/

/-- Precompose a functional with `L⁻¹`. -/
noncomputable def precompInv (L : ℝ³ →L[ℝ] ℝ³) (h : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) ≠ 0)
    (l : ℝ³ → ℝ) : ℝ³ → ℝ := fun y => l ((LinearMap.equivOfDetNeZero _ h).symm y)

theorem precompInv_apply (L : ℝ³ →L[ℝ] ℝ³) (h : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) ≠ 0)
    (l : ℝ³ → ℝ) (s : ℝ³) : precompInv L h l (L s) = l s := by
  have : (LinearMap.equivOfDetNeZero _ h).symm (L s) = s :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp [precompInv, this]

theorem galeD_map {l m l' m' : ℝ³ → ℝ} (L : ℝ³ →L[ℝ] ℝ³) (hl : ∀ s, l' (L s) = l s)
    (hm : ∀ s, m' (L s) = m s) (s t : ℝ³) : galeD l' m' (L s) (L t) = galeD l m s t := by
  simp only [galeD, hl, hm]

/-- `axisView` is equivariant: the view of the mapped octahedron is the image of the view. -/
theorem axisView_map {l m l' m' : ℝ³ → ℝ} (L : ℝ³ →L[ℝ] ℝ³) (hl : ∀ s, l' (L s) = l s)
    (hm : ∀ s, m' (L s) = m s) (a a' b c : ℝ³) :
    axisView l' m' (L a) (L a') (L b) (L c) = L (axisView l m a a' b c) := by
  simp only [axisView, galeD_map L hl hm, map_add, map_smul, map_sub]

/-- Gale data transports to the mapped points. -/
noncomputable def galeDataMap {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (L : ℝ³ →L[ℝ] ℝ³)
    (h : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) ≠ 0) : GaleData (L a) (L a') (L b) (L b') (L c) (L c') where
  l := precompInv L h G.l
  m := precompInv L h G.m
  hl := ⟨by simp only [precompInv_apply]; exact G.hl.sum, by
    simp only [precompInv_apply, ← map_smul, ← map_add]; rw [G.hl.vsum, map_zero]⟩
  hm := ⟨by simp only [precompInv_apply]; exact G.hm.sum, by
    simp only [precompInv_apply, ← map_smul, ← map_add]; rw [G.hm.vsum, map_zero]⟩
  indep := by simp only [precompInv_apply]; exact G.indep

theorem segMeet_map {d₀ d₁ e₀ e₁ u : ℝ³} (L : ℝ³ →L[ℝ] ℝ³) (h : SegMeet d₀ d₁ e₀ e₁ u) :
    SegMeet (L d₀) (L d₁) (L e₀) (L e₁) (L u) := by
  obtain ⟨s, t, μ, hs, hs1, ht, ht1, e⟩ := h
  refine ⟨s, t, μ, hs, hs1, ht, ht1, ?_⟩
  have := congrArg L e
  simpa [map_sub, map_add, map_smul] using this

/-- `SegMeet` is invariant under replacing the view by a nonzero multiple (used to pass from
`axisView = lam * vtxView21` to `vtxView21`). -/
theorem segMeet_smul {d₀ d₁ e₀ e₁ u : ℝ³} {lam : ℝ} (hl : lam ≠ 0)
    (h : SegMeet d₀ d₁ e₀ e₁ (lam • u)) : SegMeet d₀ d₁ e₀ e₁ u := by
  obtain ⟨s, t, μ, hs, hs1, ht, ht1, e⟩ := h
  exact ⟨s, t, μ * lam, hs, hs1, ht, ht1, by rw [e, mul_smul]⟩

theorem quad_smul (l a b c d : ℝ) :
    quad (l * a) (l * b) (l * c) (l * d) = fun i => l * quad a b c d i := by
  funext i; fin_cases i <;> rfl

theorem nodup_of_injective_quad {x y z w : ℝ} (h : Function.Injective (quad x y z w)) :
    [x, y, z, w].Nodup := by
  have e := fun i j (hij : (i : ZMod 4) ≠ j) (hxy : quad x y z w i = quad x y z w j) => hij (h hxy)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true]
  exact ⟨⟨fun hx => e 0 1 (by decide) (by simpa [quad] using hx), fun hx => e 0 2 (by decide) (by simpa [quad] using hx),
    fun hx => e 0 3 (by decide) (by simpa [quad] using hx)⟩, ⟨fun hx => e 1 2 (by decide) (by simpa [quad] using hx),
    fun hx => e 1 3 (by decide) (by simpa [quad] using hx)⟩, ⟨fun hx => e 2 3 (by decide) (by simpa [quad] using hx), not_false⟩⟩

/-! ### The core for two quads with non-shared diagonals -/

/-- `not_both_depthSep_map` for 8 points (`not_both_depthSep_gen`). -/
theorem not_both_depthSep_map {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ u v : ℝ³} (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hdet : det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀) *
      (det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀)) < 0)
    (m1u : SegMeet d₀ d₁ e₀ e₁ u) (m1v : SegMeet d₀ d₁ e₀ e₁ v)
    (m2v : SegMeet f₀ f₁ g₀ g₁ v) (m2u : SegMeet f₀ f₁ g₀ g₁ u) :
    ¬ (DepthSep (L d₀) (L d₁) (L e₀) (L e₁) (L u) ∧ DepthSep (L f₀) (L f₁) (L g₀) (L g₁) (L v)) := by
  rintro ⟨h1, h2⟩
  refine not_both_depthSep_gen h1 h2 (segMeet_map L m1u) (segMeet_map L m1v)
    (segMeet_map L m2v) (segMeet_map L m2u) ?_
  simp only [← map_sub, det3_map_det, hL, one_mul]
  exact hdet

theorem mf_of_not_both_depthSep {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ u v : ℝ³} (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hdet : det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀) *
      (det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀)) < 0)
    (m1u : SegMeet d₀ d₁ e₀ e₁ u) (m1v : SegMeet d₀ d₁ e₀ e₁ v)
    (m2v : SegMeet f₀ f₁ g₀ g₁ v) (m2u : SegMeet f₀ f₁ g₀ g₁ u)
    (i1 : Function.Injective (quad ⟪L d₀, L u⟫ ⟪L e₀, L u⟫ ⟪L d₁, L u⟫ ⟪L e₁, L u⟫))
    (i2 : Function.Injective (quad ⟪L f₀, L v⟫ ⟪L g₀, L v⟫ ⟪L f₁, L v⟫ ⟪L g₁, L v⟫)) :
    IsCyclicUnimodal (quad ⟪L d₀, L u⟫ ⟪L e₀, L u⟫ ⟪L d₁, L u⟫ ⟪L e₁, L u⟫) ∨
    IsCyclicUnimodal (quad ⟪L f₀, L v⟫ ⟪L g₀, L v⟫ ⟪L f₁, L v⟫ ⟪L g₁, L v⟫) := by
  by_contra hn
  push Not at hn
  have s1 : DepthSep (L d₀) (L d₁) (L e₀) (L e₁) (L u) := by
    by_contra hc; exact hn.1 (quad_unimodal hc (nodup_of_injective_quad i1))
  have s2 : DepthSep (L f₀) (L f₁) (L g₀) (L g₁) (L v) := by
    by_contra hc; exact hn.2 (quad_unimodal hc (nodup_of_injective_quad i2))
  exact not_both_depthSep_map L hL hdet m1u m1v m2v m2u ⟨s1, s2⟩

theorem depth_quad_map {n : ℕ} {f : (Fin n → ℝ³) → ℝ³} (hf : CovView f) (L : ℝ³ →L[ℝ] ℝ³) (y : Fin n → ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1) (p q r s : Fin n) :
    (LabTest.quad f p q r s).depth (mapShape L y) =
      quad ⟪L (y p), L (f y)⟫ ⟪L (y q), L (f y)⟫ ⟪L (y r), L (f y)⟫ ⟪L (y s), L (f y)⟫ := by
  rw [← hf.2 L y hL]
  funext i
  fin_cases i <;> rfl

theorem depth_quad {n : ℕ} (f : (Fin n → ℝ³) → ℝ³) (y : Fin n → ℝ³) (p q r s : Fin n) :
    (LabTest.quad f p q r s).depth y = quad ⟪y p, f y⟫ ⟪y q, f y⟫ ⟪y r, f y⟫ ⟪y s, f y⟫ := by
  funext i; fin_cases i <;> rfl

/-- Two single quad tests: `(d₀,e₀,d₁,e₁)` at `fu`, `(f₀,g₀,f₁,g₁)` at `fv`. -/
noncomputable def pairGroup {n : ℕ} (fu fv : (Fin n → ℝ³) → ℝ³) (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin n) :
    Bool → ViewGroup n
  | true => .single (LabTest.quad fu d₀ e₀ d₁ e₁)
  | false => .single (LabTest.quad fv f₀ g₀ f₁ g₁)

theorem robust_rim_of_pair_signs (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7) (y : Fin 7 → ℝ³)
    (hdet : det3 (fu y) (y d₁ - y d₀) (y e₁ - y e₀) * det3 (fv y) (y d₁ - y d₀) (y e₁ - y e₀) *
      (det3 (fu y) (y f₁ - y f₀) (y g₁ - y g₀) * det3 (fv y) (y f₁ - y f₀) (y g₁ - y g₀)) < 0)
    (m1u : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fu y)) (m1v : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fv y))
    (m2v : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fv y)) (m2u : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fu y))
    (hinj : ∀ e, ∀ T ∈ (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, Function.Injective T.lab)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2,
      (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y))
    (hcover : ∀ e, ∀ T ∈ (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, ∀ i j : ZMod T.k,
      T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = e ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j)) :
    IsRobustUnimodal (quad ⟪y d₀, fu y⟫ ⟪y e₀, fu y⟫ ⟪y d₁, fu y⟫ ⟪y e₁, fu y⟫) ∨
    IsRobustUnimodal (quad ⟪y f₀, fv y⟫ ⟪y g₀, fv y⟫ ⟪y f₁, fv y⟫ ⟪y g₁, fv y⟫) := by
  have hcov : ∀ e, CovView (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).view := by
    intro e; cases e
    · exact hfv
    · exact hfu
  have hMF : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ e, ∀ T ∈ (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ e, ∃ T ∈ (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, IsCyclicUnimodal (T.depth (mapShape L y)) := by
    refine Filter.Eventually.of_forall fun L hL hi => ?_
    have i1 := hi true (LabTest.quad fu d₀ e₀ d₁ e₁) (by simp [pairGroup, ViewGroup.tests])
    have i2 := hi false (LabTest.quad fv f₀ g₀ f₁ g₁) (by simp [pairGroup, ViewGroup.tests])
    rw [depth_quad_map hfu L y hL] at i1
    rw [depth_quad_map hfv L y hL] at i2
    rcases mf_of_not_both_depthSep (d₀ := y d₀) (d₁ := y d₁) (e₀ := y e₀) (e₁ := y e₁) (f₀ := y f₀) (f₁ := y f₁)
      (g₀ := y g₀) (g₁ := y g₁) L hL hdet m1u m1v m2v m2u i1 i2 with h | h
    · exact ⟨true, LabTest.quad fu d₀ e₀ d₁ e₁, by simp [pairGroup, ViewGroup.tests], by
        rw [depth_quad_map hfu L y hL]; exact h⟩
    · exact ⟨false, LabTest.quad fv f₀ g₀ f₁ g₁, by simp [pairGroup, ViewGroup.tests], by
        rw [depth_quad_map hfv L y hL]; exact h⟩
  have := robust_corner_rim_of_MF (n := 7) (q := q) (A := Bool) y (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁)
    hcov (fun e => by cases e <;> simp [pairGroup, ViewGroup.Ordered])
    (fun e T h => by cases e <;> simp [pairGroup] at h <;> subst h <;> simp [LabTest.quad])
    hinj hq ties hties hind hcover hMF
  rcases this with ⟨e, T, hT, hr⟩ | ⟨e, hs⟩
  · cases e
    · simp [pairGroup, ViewGroup.tests] at hT; subst hT; right
      rwa [depth_quad] at hr
    · simp [pairGroup, ViewGroup.tests] at hT; subst hT; left
      rwa [depth_quad] at hr
  · cases e <;> simp [pairGroup, ViewGroup.Straddle] at hs

theorem tieIndep_smul {q : ℕ} {d u : Fin q → ℝ³} (h : TieIndep d u) {c : Fin q → ℝ}
    (hc : ∀ t, c t ≠ 0) : TieIndep d (fun t => c t • u t) := by
  intro lam hl
  have h0 := h (fun t => lam t * c t) (fun G => by
    rw [← hl G]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [map_smul, real_inner_smul_right, real_inner_smul_left]
    ring)
  funext t
  have := congrFun h0 t
  exact (mul_eq_zero.mp this).resolve_right (hc t)

theorem tieIndep_ne_zero {q : ℕ} {d u : Fin q → ℝ³} (h : TieIndep d u) (t : Fin q) : d t ≠ 0 := by
  intro h0
  have := h (Pi.single t 1) (fun G => by
    rw [Finset.sum_eq_single t]
    · simp [h0]
    · intro t' _ ht'; simp [Pi.single_apply, ht']
    · simp)
  have := congrFun this t
  simp at this

/-- **Independence of the tied pairs at two views** (vacuous if either view has no tie). -/
def IndepF (K : Finset ℝ³) (u v : ℝ³) : Prop :=
  ∀ p ∈ K, ∀ p' ∈ K, p ≠ p' → ⟪p, u⟫ = ⟪p', u⟫ →
    ∀ r ∈ K, ∀ r' ∈ K, r ≠ r' → ⟪r, v⟫ = ⟪r', v⟫ → TieIndep ![p - p', r - r'] ![u, v]

theorem IndepF.smul {K : Finset ℝ³} {u v : ℝ³} (h : IndepF K u v) {c c' : ℝ} (hc : c ≠ 0)
    (hc' : c' ≠ 0) : IndepF K (c • u) (c' • v) := by
  intro p hp p' hp' hpp e r hr r' hr' hrr e'
  simp only [real_inner_smul_right] at e e'
  have := tieIndep_smul (h p hp p' hp' hpp (mul_left_cancel₀ hc e) r hr r' hr' hrr
    (mul_left_cancel₀ hc' e')) (c := ![c, c']) (by
      intro t; fin_cases t
      · exact hc
      · exact hc')
  convert this using 1
  funext t; fin_cases t <;> rfl

/-- No tie at one of the views: nothing to be independent. -/
theorem IndepF.of_noTie {K : Finset ℝ³} {u v : ℝ³} (h : NoTieAt K u ∨ NoTieAt K v) :
    IndepF K u v := by
  intro p hp p' hp' hpp e r hr r' hr' hrr e'
  rcases h with h | h
  · exact absurd e (h p hp p' hp' hpp)
  · exact absurd e' (h r hr r' hr' hrr)

/-! ### `hcover` from `OneTieAt`, for any family of single tests -/

theorem hcover_of_oneTieAt (g : Bool → ViewGroup 7)
    (hTv : ∀ a, ∀ T ∈ (g a).tests, T.view = (g a).view)
    (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (o : ∀ a, OneTieAt (Finset.univ.image y) ((g a).view y))
    {q : ℕ} (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (g (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2) (fun t => (g (ties t).1).view y))
    (hex : ∀ a, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (g a).view y⟫ = ⟪y j, (g a).view y⟫) →
      ∃ t, (ties t).1 = a)
    (hlab : ∀ a, ∀ T ∈ (g a).tests, Function.Injective T.lab) :
    ∀ a, ∀ T ∈ (g a).tests, ∀ i j : ZMod T.k, T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = a ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j) := by
  intro a T hT i j hij
  by_cases hl : T.lab i = T.lab j
  · rw [hl]; exact Relation.EqvGen.refl _
  have hd : ⟪y (T.lab i), (g a).view y⟫ = ⟪y (T.lab j), (g a).view y⟫ := by
    have := hij; simp only [LabTest.depth, hTv a T hT] at this; exact this
  obtain ⟨t, ht⟩ := hex a ⟨_, _, hl, hd⟩
  have hne : y (ties t).2.1 - y (ties t).2.2 ≠ 0 := tieIndep_ne_zero hind t
  have hrr : (ties t).2.1 ≠ (ties t).2.2 := fun e => hne (by rw [e, sub_self])
  have hv := hties t
  rw [ht] at hv
  have hv' : ⟪y (ties t).2.1, (g a).view y⟫ = ⟪y (ties t).2.2, (g a).view y⟫ := by
    rwa [inner_sub_left, sub_eq_zero] at hv
  have mem : ∀ k, y k ∈ Finset.univ.image y := fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  rcases o a _ (mem _) _ (mem _) _ (mem _) _ (mem _) (fun e => hl (hyinj e)) (fun e => hrr (hyinj e))
    hd hv' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have := hyinj e1; have := hyinj e2
    refine Relation.EqvGen.rel _ _ ⟨t, ht, ?_⟩
    ext <;> simp [*]
  · have h1 := hyinj e1; have h2 := hyinj e2
    refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨t, ht, ?_⟩)
    ext <;> simp [*]

theorem lab_inj_quad4 {a b c d : Fin 7} (n : [a, b, c, d].Nodup) :
    Function.Injective (fun i : ZMod 4 => ![a, b, c, d] i) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at n
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := n
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all)

theorem pairGroup_hTv {n : ℕ} (fu fv : (Fin n → ℝ³) → ℝ³) (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin n) :
    ∀ a, ∀ T ∈ (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).tests, T.view = (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).view := by
  intro a T hT
  cases a <;> simp [pairGroup, ViewGroup.tests] at hT <;> subst hT <;> rfl

theorem pairGroup_lab_inj (fu fv : (Fin 7 → ℝ³) → ℝ³) {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7}
    (n1 : [d₀, e₀, d₁, e₁].Nodup) (n2 : [f₀, g₀, f₁, g₁].Nodup) :
    ∀ a, ∀ T ∈ (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).tests, Function.Injective T.lab := by
  intro a T hT
  cases a <;> simp [pairGroup, ViewGroup.tests] at hT <;> subst hT
  · exact lab_inj_quad4 n2
  · exact lab_inj_quad4 n1

/-! ### Scalings of the views and two independent ties -/

theorem robust_quad_smul (y : Fin 7 → ℝ³) {u w : ℝ³} {l : ℝ} (hl : l ≠ 0) (hu : u = l • w)
    (p q r s : Fin 7) (h : IsRobustUnimodal (quad ⟪y p, w⟫ ⟪y q, w⟫ ⟪y r, w⟫ ⟪y s, w⟫)) :
    IsRobustUnimodal (quad ⟪y p, u⟫ ⟪y q, u⟫ ⟪y r, u⟫ ⟪y s, u⟫) := by
  have e : quad ⟪y p, u⟫ ⟪y q, u⟫ ⟪y r, u⟫ ⟪y s, u⟫ =
      fun i => l * quad ⟪y p, w⟫ ⟪y q, w⟫ ⟪y r, w⟫ ⟪y s, w⟫ i := by
    rw [← quad_smul, hu]; simp only [real_inner_smul_right]
  rw [e]; exact robust_mul_ne_zero h hl

/-- Two tied pairs, one at each of two views, independent: `IndepF` and no `NoTieAt` give them. -/
theorem exists_ties_of_indepF {y : Fin 7 → ℝ³} {u v : ℝ³} (hI : IndepF (Finset.univ.image y) u v)
    (h : ¬ (NoTieAt (Finset.univ.image y) u ∨ NoTieAt (Finset.univ.image y) v)) :
    ∃ i j k l : Fin 7, ⟪y i - y j, u⟫ = 0 ∧ ⟪y k - y l, v⟫ = 0 ∧
      TieIndep ![y i - y j, y k - y l] ![u, v] := by
  rw [not_or] at h
  obtain ⟨hn1, hn2⟩ := h
  simp only [NoTieAt, not_forall] at hn1 hn2
  obtain ⟨p, hp, p', hp', hpp, hpe⟩ := hn1
  obtain ⟨r, hr, r', hr', hrr, hre⟩ := hn2
  have hpe : ⟪p, u⟫ = ⟪p', u⟫ := not_not.mp hpe
  have hre : ⟪r, v⟫ = ⟪r', v⟫ := not_not.mp hre
  have hind' := hI p hp p' hp' hpp hpe r hr r' hr' hrr hre
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp'
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hr'
  exact ⟨i, j, k, l, by rw [inner_sub_left, hpe, sub_self], by rw [inner_sub_left, hre, sub_self],
    hind'⟩

/-- The two listed ties (one at the view of `true`, one at the view of `false`). -/
theorem exists_listed_ties {y : Fin 7 → ℝ³} (g : Bool → ViewGroup 7) {fu fv : (Fin 7 → ℝ³) → ℝ³}
    (hgt : (g true).view y = fu y) (hgf : (g false).view y = fv y) {i j k l : Fin 7}
    (e1 : ⟪y i - y j, fu y⟫ = 0) (e2 : ⟪y k - y l, fv y⟫ = 0)
    (hI : TieIndep ![y i - y j, y k - y l] ![fu y, fv y]) :
    ∃ ties : Fin 2 → Bool × Fin 7 × Fin 7,
      (∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (g (ties t).1).view y⟫ = 0) ∧
      TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2) (fun t => (g (ties t).1).view y) ∧
      ∀ a, ∃ t, (ties t).1 = a := by
  let ties : Fin 2 → Bool × Fin 7 × Fin 7 := ![(true, i, j), (false, k, l)]
  refine ⟨ties, ?_, ?_, ?_⟩
  · intro t; fin_cases t
    · show ⟪y i - y j, (g true).view y⟫ = 0
      rw [hgt]; exact e1
    · show ⟪y k - y l, (g false).view y⟫ = 0
      rw [hgf]; exact e2
  · have k1 : (fun t => y (ties t).2.1 - y (ties t).2.2) = ![y i - y j, y k - y l] := by
      funext t; fin_cases t <;> rfl
    have k2 : (fun t => (g (ties t).1).view y) = ![fu y, fv y] := by
      funext t; fin_cases t
      · exact hgt
      · exact hgf
    rw [k1, k2]; exact hI
  · intro a; cases a
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- `hdet_smul` for two different pairs of vectors. -/
theorem hdet_smul {u v p q r s : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (h : det3 (l1 • u) p q * det3 (l2 • v) p q * (det3 (l1 • u) r s * det3 (l2 • v) r s) < 0) :
    det3 u p q * det3 v p q * (det3 u r s * det3 v r s) < 0 := by
  have sm : ∀ (l : ℝ) (w a b : ℝ³), det3 (l • w) a b = l * det3 w a b := by
    intro l w a b; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  have e : det3 (l1 • u) p q * det3 (l2 • v) p q * (det3 (l1 • u) r s * det3 (l2 • v) r s) =
      (l1 * l1 * l2 * l2) * (det3 u p q * det3 v p q * (det3 u r s * det3 v r s)) := by
    simp only [sm]; ring
  rw [e] at h
  have : 0 < l1 * l1 * l2 * l2 := by
    nlinarith [mul_pos (mul_self_pos.2 hl1) (mul_self_pos.2 hl2)]
  exact neg_of_mul_neg_right h this.le

end Minimality
