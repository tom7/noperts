module

public import Minimality.Type29CertTie
public import Minimality.Type21F2Weak

@[expose] public section

/-!
# Type 29: the pair cores with a tie at both views, the tied pairs independent

The sign-product route of type 21 (`cert_type21_F2_weak`, `b5b_core`, `robust_corner_rim_of_MF`)
for the five pairs of `pairViewsGO29` (`P14`, `P11`, `{Xa, T2}`, `P13`, `B2`): `pair_core_ie` and
`shared_core_ie` replace `pair_core` / `shared_core`, taking `IndepF` of the two views in place
of the hypothesis `NoTieAt u ∨ NoTieAt v`.  The covariance of the named views (`covView_view29`) is
here, upstream of the pair certificates.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter Noperts Finset

theorem tendsto_view29 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : View29) :
    Tendsto (fun n => view29 (K n) v) l (𝓝 (view29 x v)) := by
  rcases v with ⟨i, j⟩ | t
  · exact (hK j).sub (hK i)
  · exact tendsto_planeLine (hK _) (hK _) (hK _) (hK _) (hK _) (hK _)

theorem detMap_eq29 (L : ℝ³ →L[ℝ] ℝ³) : detMap L = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp only [detMap, det3_expand, LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply]
  ring

theorem covView_view29 (v : View29) : CovView (fun y : Fin 7 → ℝ³ => view29 y v) := by
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun y => ?_
    exact tendsto_view29 (fun m => (continuous_apply m).tendsto y) v
  · intro L y hL
    have hd : detMap L = 1 := by rw [detMap_eq29]; exact hL
    rcases v with ⟨i, j⟩ | t
    · show L (y j) - L (y i) = L (y j - y i)
      rw [map_sub]
    · show planeLine (L (y _)) (L (y _)) (L (y _)) (L (y _)) (L (y _)) (L (y _)) = _
      rw [planeLine_map, hd, one_smul]
      rfl


/-- Generic shared-diagonal pair group: quads `(b,d,b',c)` at view `fu` and `(b,a',b',a)` at `fv`. -/
noncomputable def b6_g {n : ℕ} (fu fv : (Fin n → ℝ³) → ℝ³) (b b' c d a a' : Fin n) : Bool → ViewGroup n
  | true => .single (LabTest.quad fu b d b' c)
  | false => .single (LabTest.quad fv b a' b' a)

theorem b6_depth {n : ℕ} {f : (Fin n → ℝ³) → ℝ³} (hf : CovView f) (L : ℝ³ →L[ℝ] ℝ³) (y : Fin n → ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1) (p q r s : Fin n) :
    (LabTest.quad f p q r s).depth (mapShape L y) =
      quad ⟪L (y p), L (f y)⟫ ⟪L (y q), L (f y)⟫ ⟪L (y r), L (f y)⟫ ⟪L (y s), L (f y)⟫ := by
  rw [← hf.2 L y hL]
  funext i
  fin_cases i <;> rfl

theorem b6_depth0 {n : ℕ} (f : (Fin n → ℝ³) → ℝ³) (y : Fin n → ℝ³) (p q r s : Fin n) :
    (LabTest.quad f p q r s).depth y = quad ⟪y p, f y⟫ ⟪y q, f y⟫ ⟪y r, f y⟫ ⟪y s, f y⟫ := by
  funext i; fin_cases i <;> rfl

/-- **Analogue of `b5b_F2_robust` for a shared-diagonal pair of type-29 views.** -/
theorem b6_pair_robust (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (b b' c d a a' : Fin 7) (y : Fin 7 → ℝ³)
    (hdet : det3 (fu y) (y b' - y b) (y c - y d) * det3 (fv y) (y b' - y b) (y c - y d) *
      (det3 (fu y) (y b' - y b) (y a - y a') * det3 (fv y) (y b' - y b) (y a - y a')) < 0)
    (m1u : SegMeet (y b) (y b') (y d) (y c) (fu y)) (m1v : SegMeet (y b) (y b') (y d) (y c) (fv y))
    (m2v : SegMeet (y b) (y b') (y a') (y a) (fv y)) (m2u : SegMeet (y b) (y b') (y a') (y a) (fu y))
    (hinj : ∀ e, ∀ T ∈ (b6_g fu fv b b' c d a a' e).tests, Function.Injective T.lab)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (b6_g fu fv b b' c d a a' (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b6_g fu fv b b' c d a a' (ties t).1).view y))
    (hcover : ∀ e, ∀ T ∈ (b6_g fu fv b b' c d a a' e).tests, ∀ i j : ZMod T.k,
      T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = e ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j)) :
    IsRobustUnimodal (quad ⟪y b, fu y⟫ ⟪y d, fu y⟫ ⟪y b', fu y⟫ ⟪y c, fu y⟫) ∨
    IsRobustUnimodal (quad ⟪y b, fv y⟫ ⟪y a', fv y⟫ ⟪y b', fv y⟫ ⟪y a, fv y⟫) := by
  have hcov : ∀ e, CovView (b6_g fu fv b b' c d a a' e).view := by
    intro e; cases e
    · exact hfv
    · exact hfu
  have hMF : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ e, ∀ T ∈ (b6_g fu fv b b' c d a a' e).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ e, ∃ T ∈ (b6_g fu fv b b' c d a a' e).tests, IsCyclicUnimodal (T.depth (mapShape L y)) := by
    refine Filter.Eventually.of_forall fun L hL hi => ?_
    have i1 := hi true (LabTest.quad fu b d b' c) (by simp [b6_g, ViewGroup.tests])
    have i2 := hi false (LabTest.quad fv b a' b' a) (by simp [b6_g, ViewGroup.tests])
    rw [b6_depth hfu L y hL] at i1
    rw [b6_depth hfv L y hL] at i2
    -- the fu/fv views are covariant: `L (fu y) = fu (mapShape L y)`; the proof only needs `L`-images
    rcases b5b_MF (b := y b) (b' := y b') (c := y c) (d := y d) (a := y a) (a' := y a') L hL
      hdet m1u m1v m2v m2u i1 i2 with h | h
    · exact ⟨true, LabTest.quad fu b d b' c, by simp [b6_g, ViewGroup.tests], by rw [b6_depth hfu L y hL]; exact h⟩
    · exact ⟨false, LabTest.quad fv b a' b' a, by simp [b6_g, ViewGroup.tests], by rw [b6_depth hfv L y hL]; exact h⟩
  have := robust_corner_rim_of_MF (n := 7) (q := q) (A := Bool) y (b6_g fu fv b b' c d a a') hcov
    (fun e => by cases e <;> simp [b6_g, ViewGroup.Ordered])
    (fun e T h => by cases e <;> simp [b6_g] at h <;> subst h <;> simp [LabTest.quad])
    hinj hq ties hties hind hcover hMF
  rcases this with ⟨e, T, hT, hr⟩ | ⟨e, hs⟩
  · cases e
    · simp [b6_g, ViewGroup.tests] at hT; subst hT; right
      rwa [b6_depth0] at hr
    · simp [b6_g, ViewGroup.tests] at hT; subst hT; left
      rwa [b6_depth0] at hr
  · cases e <;> simp [b6_g, ViewGroup.Straddle] at hs


/-! ### The core for two quads with non-shared diagonals -/

/-- `b5b_core` for 8 points (`not_both_depthSep_gen`). -/
theorem b6_core_gen {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ u v : ℝ³} (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hdet : det3 u (d₁ - d₀) (e₁ - e₀) * det3 v (d₁ - d₀) (e₁ - e₀) *
      (det3 u (f₁ - f₀) (g₁ - g₀) * det3 v (f₁ - f₀) (g₁ - g₀)) < 0)
    (m1u : SegMeet d₀ d₁ e₀ e₁ u) (m1v : SegMeet d₀ d₁ e₀ e₁ v)
    (m2v : SegMeet f₀ f₁ g₀ g₁ v) (m2u : SegMeet f₀ f₁ g₀ g₁ u) :
    ¬ (DepthSep (L d₀) (L d₁) (L e₀) (L e₁) (L u) ∧ DepthSep (L f₀) (L f₁) (L g₀) (L g₁) (L v)) := by
  rintro ⟨h1, h2⟩
  refine not_both_depthSep_gen h1 h2 (b5b_segMeet_map L m1u) (b5b_segMeet_map L m1v)
    (b5b_segMeet_map L m2v) (b5b_segMeet_map L m2u) ?_
  simp only [← map_sub, b5b_det3_map, hL, one_mul]
  exact hdet

theorem b6_MF_gen {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ u v : ℝ³} (L : ℝ³ →L[ℝ] ℝ³)
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
    by_contra hc; exact hn.1 (quad_unimodal hc (b5b_nodup_of_inj i1))
  have s2 : DepthSep (L f₀) (L f₁) (L g₀) (L g₁) (L v) := by
    by_contra hc; exact hn.2 (quad_unimodal hc (b5b_nodup_of_inj i2))
  exact b6_core_gen L hL hdet m1u m1v m2v m2u ⟨s1, s2⟩

/-- Two single quad tests: `(d₀,e₀,d₁,e₁)` at `fu`, `(f₀,g₀,f₁,g₁)` at `fv`. -/
noncomputable def b6_h {n : ℕ} (fu fv : (Fin n → ℝ³) → ℝ³) (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin n) :
    Bool → ViewGroup n
  | true => .single (LabTest.quad fu d₀ e₀ d₁ e₁)
  | false => .single (LabTest.quad fv f₀ g₀ f₁ g₁)

theorem b6_pair_robust_gen (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7) (y : Fin 7 → ℝ³)
    (hdet : det3 (fu y) (y d₁ - y d₀) (y e₁ - y e₀) * det3 (fv y) (y d₁ - y d₀) (y e₁ - y e₀) *
      (det3 (fu y) (y f₁ - y f₀) (y g₁ - y g₀) * det3 (fv y) (y f₁ - y f₀) (y g₁ - y g₀)) < 0)
    (m1u : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fu y)) (m1v : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fv y))
    (m2v : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fv y)) (m2u : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fu y))
    (hinj : ∀ e, ∀ T ∈ (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, Function.Injective T.lab)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2,
      (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y))
    (hcover : ∀ e, ∀ T ∈ (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, ∀ i j : ZMod T.k,
      T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = e ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j)) :
    IsRobustUnimodal (quad ⟪y d₀, fu y⟫ ⟪y e₀, fu y⟫ ⟪y d₁, fu y⟫ ⟪y e₁, fu y⟫) ∨
    IsRobustUnimodal (quad ⟪y f₀, fv y⟫ ⟪y g₀, fv y⟫ ⟪y f₁, fv y⟫ ⟪y g₁, fv y⟫) := by
  have hcov : ∀ e, CovView (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).view := by
    intro e; cases e
    · exact hfv
    · exact hfu
  have hMF : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ e, ∀ T ∈ (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ e, ∃ T ∈ (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ e).tests, IsCyclicUnimodal (T.depth (mapShape L y)) := by
    refine Filter.Eventually.of_forall fun L hL hi => ?_
    have i1 := hi true (LabTest.quad fu d₀ e₀ d₁ e₁) (by simp [b6_h, ViewGroup.tests])
    have i2 := hi false (LabTest.quad fv f₀ g₀ f₁ g₁) (by simp [b6_h, ViewGroup.tests])
    rw [b6_depth hfu L y hL] at i1
    rw [b6_depth hfv L y hL] at i2
    rcases b6_MF_gen (d₀ := y d₀) (d₁ := y d₁) (e₀ := y e₀) (e₁ := y e₁) (f₀ := y f₀) (f₁ := y f₁)
      (g₀ := y g₀) (g₁ := y g₁) L hL hdet m1u m1v m2v m2u i1 i2 with h | h
    · exact ⟨true, LabTest.quad fu d₀ e₀ d₁ e₁, by simp [b6_h, ViewGroup.tests], by
        rw [b6_depth hfu L y hL]; exact h⟩
    · exact ⟨false, LabTest.quad fv f₀ g₀ f₁ g₁, by simp [b6_h, ViewGroup.tests], by
        rw [b6_depth hfv L y hL]; exact h⟩
  have := robust_corner_rim_of_MF (n := 7) (q := q) (A := Bool) y (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁)
    hcov (fun e => by cases e <;> simp [b6_h, ViewGroup.Ordered])
    (fun e T h => by cases e <;> simp [b6_h] at h <;> subst h <;> simp [LabTest.quad])
    hinj hq ties hties hind hcover hMF
  rcases this with ⟨e, T, hT, hr⟩ | ⟨e, hs⟩
  · cases e
    · simp [b6_h, ViewGroup.tests] at hT; subst hT; right
      rwa [b6_depth0] at hr
    · simp [b6_h, ViewGroup.tests] at hT; subst hT; left
      rwa [b6_depth0] at hr
  · cases e <;> simp [b6_h, ViewGroup.Straddle] at hs

/-! ### `hcover` from `OneTieAt`, for any family of single tests -/

theorem b6_hcover {n : ℕ} (g : Bool → ViewGroup 7)
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
  have hne : y (ties t).2.1 - y (ties t).2.2 ≠ 0 := b5b_indep_ne hind t
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

theorem b6_lab_inj4 {a b c d : Fin 7} (n : [a, b, c, d].Nodup) :
    Function.Injective (fun i : ZMod 4 => ![a, b, c, d] i) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at n
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := n
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all)

theorem b6_hTv {n : ℕ} (fu fv : (Fin n → ℝ³) → ℝ³) (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin n) :
    ∀ a, ∀ T ∈ (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).tests, T.view = (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).view := by
  intro a T hT
  cases a <;> simp [b6_h, ViewGroup.tests] at hT <;> subst hT <;> rfl

theorem b6_hinj_h (fu fv : (Fin 7 → ℝ³) → ℝ³) {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7}
    (n1 : [d₀, e₀, d₁, e₁].Nodup) (n2 : [f₀, g₀, f₁, g₁].Nodup) :
    ∀ a, ∀ T ∈ (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).tests, Function.Injective T.lab := by
  intro a T hT
  cases a <;> simp [b6_h, ViewGroup.tests] at hT <;> subst hT
  · exact b6_lab_inj4 n2
  · exact b6_lab_inj4 n1


/-! ### Scalings of the views and two independent ties -/

theorem b6_robust_smul (y : Fin 7 → ℝ³) {u w : ℝ³} {l : ℝ} (hl : l ≠ 0) (hu : u = l • w)
    (p q r s : Fin 7) (h : IsRobustUnimodal (quad ⟪y p, w⟫ ⟪y q, w⟫ ⟪y r, w⟫ ⟪y s, w⟫)) :
    IsRobustUnimodal (quad ⟪y p, u⟫ ⟪y q, u⟫ ⟪y r, u⟫ ⟪y s, u⟫) := by
  have e : quad ⟪y p, u⟫ ⟪y q, u⟫ ⟪y r, u⟫ ⟪y s, u⟫ =
      fun i => l * quad ⟪y p, w⟫ ⟪y q, w⟫ ⟪y r, w⟫ ⟪y s, w⟫ i := by
    rw [← b5b_quad_smul, hu]; simp only [real_inner_smul_right]
  rw [e]; exact robust_mul_ne_zero h hl

/-- Two tied pairs, one at each of two views, independent: `IndepF` and no `NoTieAt` give them. -/
theorem b6_extract {y : Fin 7 → ℝ³} {u v : ℝ³} (hI : IndepF (univ.image y) u v)
    (h : ¬ (NoTieAt (univ.image y) u ∨ NoTieAt (univ.image y) v)) :
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
  obtain ⟨i, -, rfl⟩ := mem_image.mp hp
  obtain ⟨j, -, rfl⟩ := mem_image.mp hp'
  obtain ⟨k, -, rfl⟩ := mem_image.mp hr
  obtain ⟨l, -, rfl⟩ := mem_image.mp hr'
  exact ⟨i, j, k, l, by rw [inner_sub_left, hpe, sub_self], by rw [inner_sub_left, hre, sub_self],
    hind'⟩

/-- The two listed ties (one at the view of `true`, one at the view of `false`). -/
theorem b6_two_ties {y : Fin 7 → ℝ³} (g : Bool → ViewGroup 7) {fu fv : (Fin 7 → ℝ³) → ℝ³}
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

/-! ### `pair_core` / `shared_core` with listed ties -/

/-- `b5b_hdet_smul` for two different pairs of vectors. -/
theorem b6_hdet_smul2 {u v p q r s : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
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

/-- **`pair_core` without `hno`** (labels in a shape `y`; the views `u = l₁ fu(y)`, `v = l₂ fv(y)`
are nonzero multiples of covariant views).  The tie hypothesis is replaced by the listed ties
(`q ≤ 2`, independent) with `hex` (a view with a tied pair has a listed tie). -/
theorem pair_core_weak (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7)
    (n1 : [d₀, e₀, d₁, e₁].Nodup) (n2 : [f₀, g₀, f₁, g₁].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) u) (m1v : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) v)
    (m2u : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) u) (m2v : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) v)
    (hS2 : det3 (y g₀ - y f₀) (y f₁ - y f₀) (y g₁ - y g₀) ≠ 0)
    (hp1 : 0 < det3 u (y d₁ - y d₀) (y e₁ - y e₀) * det3 v (y d₁ - y d₀) (y e₁ - y e₀))
    (hn2 : det3 u (y f₁ - y f₀) (y g₁ - y g₀) * det3 v (y f₁ - y f₀) (y g₁ - y g₀) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2,
      (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y))
    (hex : ∀ a, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).view y⟫ =
        ⟪y j, (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).view y⟫) → ∃ t, (ties t).1 = a) :
    IsRobustUnimodal (quad ⟪y f₀, v⟫ ⟪y g₀, v⟫ ⟪y f₁, v⟫ ⟪y g₁, v⟫) ∨
      (IsRobustUnimodal (quad ⟪y d₀, u⟫ ⟪y e₀, u⟫ ⟪y d₁, u⟫ ⟪y e₁, u⟫) ∧ ⟪u, v⟫ ≤ 0) := by
  by_cases hR2 : IsRobustUnimodal (quad ⟪y f₀, v⟫ ⟪y g₀, v⟫ ⟪y f₁, v⟫ ⟪y g₁, v⟫)
  · exact Or.inl hR2
  right
  have hinj := b6_hinj_h fu fv n1 n2
  have hcov := b6_hcover (n := 7) (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁)
    (b6_hTv fu fv _ _ _ _ _ _ _ _) y hyinj
    (fun a => by cases a; exact o2; exact o1) ties hties hind hex hinj
  have hdet := mul_neg_of_pos_of_neg hp1 hn2
  have hdet' : det3 (fu y) (y d₁ - y d₀) (y e₁ - y e₀) * det3 (fv y) (y d₁ - y d₀) (y e₁ - y e₀) *
      (det3 (fu y) (y f₁ - y f₀) (y g₁ - y g₀) * det3 (fv y) (y f₁ - y f₀) (y g₁ - y g₀)) < 0 :=
    b6_hdet_smul2 hl1 hl2 (by rw [← hu, ← hv]; exact hdet)
  have m1u' : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fu y) :=
    b5b_segMeet_smul hl1 (by rw [← hu]; exact m1u)
  have m1v' : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fv y) :=
    b5b_segMeet_smul hl2 (by rw [← hv]; exact m1v)
  have m2u' : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fu y) :=
    b5b_segMeet_smul hl1 (by rw [← hu]; exact m2u)
  have m2v' : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fv y) :=
    b5b_segMeet_smul hl2 (by rw [← hv]; exact m2v)
  have R := b6_pair_robust_gen fu fv hfu hfv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ y hdet' m1u' m1v' m2v' m2u'
    hinj hq ties hties hind hcov
  rcases R with R1 | R2
  swap
  · exact absurd (b6_robust_smul y hl2 hv _ _ _ _ R2) hR2
  refine ⟨b6_robust_smul y hl1 hu _ _ _ _ R1, ?_⟩
  have mem : ∀ k, y k ∈ Finset.univ.image y :=
    fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  have o2v : OneTieAt (univ.image y) v := o2.of_eq_smul hv hl2
  have W2 := weakSep_of_not_robust (o2v.oneTie4 (mem f₀) (mem g₀) (mem f₁) (mem g₁)
    (List.nodup4_img hyinj n2)) hR2
  by_contra hpos
  push Not at hpos
  have hne : ⟪v, u⟫ ≠ 0 := by rw [real_inner_comm]; exact hpos.ne'
  have B := weakSep_det_sign (a' := y f₀) (a := y f₁) (b := y g₀) (b' := y g₁) (u := v) (v := u)
    W2.symm m2v m2u hne hS2
  rw [real_inner_comm] at B
  nlinarith [mul_pos hpos (neg_pos.mpr hn2), mul_comm (det3 u (y f₁ - y f₀) (y g₁ - y g₀))
    (det3 v (y f₁ - y f₀) (y g₁ - y g₀))]

/-- **`pair_core` with independent ties at both views**: `NoTieAt u ∨ NoTieAt v` is replaced by
`IndepF` of the two views (`hI`; vacuous if a view has no tie).  `u, v` are nonzero multiples of
the views `fu y`, `fv y`. -/
theorem pair_core_ie (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7)
    (n1 : [d₀, e₀, d₁, e₁].Nodup) (n2 : [f₀, g₀, f₁, g₁].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) u) (m1v : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) v)
    (m2u : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) u) (m2v : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) v)
    (hS1 : det3 (y e₀ - y d₀) (y d₁ - y d₀) (y e₁ - y e₀) ≠ 0)
    (hS2 : det3 (y g₀ - y f₀) (y f₁ - y f₀) (y g₁ - y g₀) ≠ 0)
    (hp1 : 0 < det3 u (y d₁ - y d₀) (y e₁ - y e₀) * det3 v (y d₁ - y d₀) (y e₁ - y e₀))
    (hn2 : det3 u (y f₁ - y f₀) (y g₁ - y g₀) * det3 v (y f₁ - y f₀) (y g₁ - y g₀) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    (hI : IndepF (univ.image y) (fu y) (fv y)) :
    IsRobustUnimodal (quad ⟪y f₀, v⟫ ⟪y g₀, v⟫ ⟪y f₁, v⟫ ⟪y g₁, v⟫) ∨
      (IsRobustUnimodal (quad ⟪y d₀, u⟫ ⟪y e₀, u⟫ ⟪y d₁, u⟫ ⟪y e₁, u⟫) ∧ ⟪u, v⟫ ≤ 0) := by
  have mem : ∀ k, y k ∈ Finset.univ.image y :=
    fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  by_cases hno : NoTieAt (univ.image y) (fu y) ∨ NoTieAt (univ.image y) (fv y)
  · exact pair_core (mem d₀) (mem d₁) (mem e₀) (mem e₁) (mem f₀) (mem f₁) (mem g₀) (mem g₁)
      (List.nodup4_img hyinj n1) (List.nodup4_img hyinj n2) m1u m1v m2u m2v hS1 hS2 hp1 hn2
      (o1.of_eq_smul hu hl1) (o2.of_eq_smul hv hl2)
      (hno.imp (·.of_eq_smul hu hl1) (·.of_eq_smul hv hl2))
  · obtain ⟨i, j, k, l, e1, e2, hind'⟩ := b6_extract hI hno
    obtain ⟨ties, hties, hind, hex⟩ :=
      b6_two_ties (b6_h fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁) rfl rfl e1 e2 hind'
    exact pair_core_weak y hyinj fu fv hfu hfv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ n1 n2 hl1 hl2 hu hv
      m1u m1v m2u m2v hS2 hp1 hn2 o1 o2 (q := 2) le_rfl ties hties hind (fun a _ => hex a)

/-- **`shared_core` without `hno`** (labels in a shape; `hS1`, `hS2` are not needed). -/
theorem shared_core_weak (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (a' a b b' c c' : Fin 7)
    (n1 : [a', b, a, b'].Nodup) (n2 : [a', c', a, c].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y a') (y a) (y b) (y b') u) (m1v : SegMeet (y a') (y a) (y b) (y b') v)
    (m2u : SegMeet (y a') (y a) (y c) (y c') u) (m2v : SegMeet (y a') (y a) (y c) (y c') v)
    (hdet : det3 u (y a - y a') (y b' - y b) * det3 v (y a - y a') (y b' - y b) *
      (det3 u (y a - y a') (y c' - y c) * det3 v (y a - y a') (y c' - y c)) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2,
      (b6_g fu fv a' a b' b c c' (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b6_g fu fv a' a b' b c c' (ties t).1).view y))
    (hex : ∀ e, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (b6_g fu fv a' a b' b c c' e).view y⟫ =
        ⟪y j, (b6_g fu fv a' a b' b c c' e).view y⟫) → ∃ t, (ties t).1 = e) :
    IsRobustUnimodal (quad ⟪y a', u⟫ ⟪y b, u⟫ ⟪y a, u⟫ ⟪y b', u⟫) ∨
      IsRobustUnimodal (quad ⟪y a', v⟫ ⟪y c', v⟫ ⟪y a, v⟫ ⟪y c, v⟫) := by
  have hinj : ∀ e, ∀ T ∈ (b6_g fu fv a' a b' b c c' e).tests, Function.Injective T.lab := by
    intro e T hT
    cases e <;> simp [b6_g, ViewGroup.tests] at hT <;> subst hT
    · exact b6_lab_inj4 n2
    · exact b6_lab_inj4 n1
  have hTv : ∀ e, ∀ T ∈ (b6_g fu fv a' a b' b c c' e).tests,
      T.view = (b6_g fu fv a' a b' b c c' e).view := by
    intro e T hT
    cases e <;> simp [b6_g, ViewGroup.tests] at hT <;> subst hT <;> rfl
  have hcov := b6_hcover (n := 7) (b6_g fu fv a' a b' b c c') hTv y hyinj
    (fun a => by cases a; exact o2; exact o1) ties hties hind hex hinj
  have hdet0 : det3 (fu y) (y a - y a') (y b' - y b) * det3 (fv y) (y a - y a') (y b' - y b) *
      (det3 (fu y) (y a - y a') (y c' - y c) * det3 (fv y) (y a - y a') (y c' - y c)) < 0 :=
    b5b_hdet_smul hl1 hl2 (by rw [← hu, ← hv]; exact hdet)
  have hflip : ∀ w P A B : ℝ³, det3 w P (A - B) = - det3 w P (B - A) := by
    intro w P A B; unfold det3; rw [← inner_neg_right, neg_sub]
  have hdet' : det3 (fu y) (y a - y a') (y b' - y b) * det3 (fv y) (y a - y a') (y b' - y b) *
      (det3 (fu y) (y a - y a') (y c - y c') * det3 (fv y) (y a - y a') (y c - y c')) < 0 := by
    rw [hflip (fu y) (y a - y a') (y c) (y c'), hflip (fv y) (y a - y a') (y c) (y c'), neg_mul_neg]
    exact hdet0
  have m1u' : SegMeet (y a') (y a) (y b) (y b') (fu y) :=
    b5b_segMeet_smul hl1 (by rw [← hu]; exact m1u)
  have m1v' : SegMeet (y a') (y a) (y b) (y b') (fv y) :=
    b5b_segMeet_smul hl2 (by rw [← hv]; exact m1v)
  have m2u' : SegMeet (y a') (y a) (y c) (y c') (fu y) :=
    b5b_segMeet_smul hl1 (by rw [← hu]; exact m2u)
  have m2v' : SegMeet (y a') (y a) (y c) (y c') (fv y) :=
    b5b_segMeet_smul hl2 (by rw [← hv]; exact m2v)
  rcases b6_pair_robust fu fv hfu hfv a' a b' b c c' y hdet' m1u' m1v' m2v'.swap_e m2u'.swap_e hinj
    hq ties hties hind hcov with R | R
  · exact Or.inl (b6_robust_smul y hl1 hu _ _ _ _ R)
  · exact Or.inr (b6_robust_smul y hl2 hv _ _ _ _ R)

/-- **`shared_core` with independent ties at both views** (see `pair_core_ie`). -/
theorem shared_core_ie (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (a' a b b' c c' : Fin 7)
    (n1 : [a', b, a, b'].Nodup) (n2 : [a', c', a, c].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y a') (y a) (y b) (y b') u) (m1v : SegMeet (y a') (y a) (y b) (y b') v)
    (m2u : SegMeet (y a') (y a) (y c) (y c') u) (m2v : SegMeet (y a') (y a) (y c) (y c') v)
    (hS1 : det3 (y b - y a') (y a - y a') (y b' - y b) ≠ 0)
    (hS2 : det3 (y c - y a') (y a - y a') (y c' - y c) ≠ 0)
    (hdet : det3 u (y a - y a') (y b' - y b) * det3 v (y a - y a') (y b' - y b) *
      (det3 u (y a - y a') (y c' - y c) * det3 v (y a - y a') (y c' - y c)) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    (hI : IndepF (univ.image y) (fu y) (fv y)) :
    IsRobustUnimodal (quad ⟪y a', u⟫ ⟪y b, u⟫ ⟪y a, u⟫ ⟪y b', u⟫) ∨
      IsRobustUnimodal (quad ⟪y a', v⟫ ⟪y c', v⟫ ⟪y a, v⟫ ⟪y c, v⟫) := by
  have mem : ∀ k, y k ∈ Finset.univ.image y :=
    fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  by_cases hno : NoTieAt (univ.image y) (fu y) ∨ NoTieAt (univ.image y) (fv y)
  · exact shared_core (mem a') (mem a) (mem b) (mem b') (mem c) (mem c')
      (List.nodup4_img hyinj n1) (List.nodup4_img hyinj n2) m1u m1v m2u m2v hS1 hS2 hdet
      (o1.of_eq_smul hu hl1) (o2.of_eq_smul hv hl2)
      (hno.imp (·.of_eq_smul hu hl1) (·.of_eq_smul hv hl2))
  · obtain ⟨i, j, k, l, e1, e2, hind'⟩ := b6_extract hI hno
    obtain ⟨ties, hties, hind, hex⟩ :=
      b6_two_ties (b6_g fu fv a' a b' b c c') rfl rfl e1 e2 hind'
    exact shared_core_weak y hyinj fu fv hfu hfv a' a b b' c c' n1 n2 hl1 hl2 hu hv
      m1u m1v m2u m2v hdet o1 o2 (q := 2) le_rfl ties hties hind (fun a _ => hex a)

end Minimality

end
