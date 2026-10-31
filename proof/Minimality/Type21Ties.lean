module

public import Minimality.Cases
public import Minimality.Type21Metric
public import Minimality.Type21Vtx
public import Minimality.Type16Vtx
public import Minimality.Generic.LimitSeq

@[expose] public section

/-!
# Type 21 with several independent ties (package B2)

`OneTie21` (at most one tie) is replaced by `TwoTie21`: independent generating ties (`TieGen21`) and
the tie hypotheses of the cover `cert21_of_generic` stated at `x` itself (`CoverTie21`: `TieSeg`,
`OneTieAt` at the eight vertex views, `hY`, `hF`).  The ties are restored along an approximating
sequence (`exists_seq_restore_ties`); every tie of `K n` is a tie of `x`, so `CoverTie21` passes
from `x` to `K n`, and the cover applies.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **`hY` of the cover** (at `y`): if `a, b` tie at a vertex view of `T1`, no tie along `a - b`. -/
def HY21 (y : Fin 7 → ℝ³) : Prop :=
  (⟪y 0, vtxView21 y 0⟫ = ⟪y 4, vtxView21 y 0⟫ → NoTieAt (univ.image y) (y 0 - y 4)) ∧
  (⟪y 4, vtxView21 y 1⟫ = ⟪y 0, vtxView21 y 1⟫ → NoTieAt (univ.image y) (y 4 - y 0)) ∧
  (⟪y 5, vtxView21 y 2⟫ = ⟪y 3, vtxView21 y 2⟫ → NoTieAt (univ.image y) (y 5 - y 3)) ∧
  (⟪y 3, vtxView21 y 3⟫ = ⟪y 5, vtxView21 y 3⟫ → NoTieAt (univ.image y) (y 3 - y 5))

/-- **`hF` of the cover** (at `y`): a tie at no more than one of the two views of an F2 pair. -/
def HF21 (y : Fin 7 → ℝ³) : Prop :=
  (NoTieAt (univ.image y) (vtxView21 y 1) ∨ NoTieAt (univ.image y) (vtxView21 y 4)) ∧
  (NoTieAt (univ.image y) (vtxView21 y 0) ∨ NoTieAt (univ.image y) (vtxView21 y 5)) ∧
  (NoTieAt (univ.image y) (vtxView21 y 3) ∨ NoTieAt (univ.image y) (vtxView21 y 6)) ∧
  (NoTieAt (univ.image y) (vtxView21 y 2) ∨ NoTieAt (univ.image y) (vtxView21 y 7))

/-- **The tie hypotheses of `cert21_of_generic`**: at most one tied pair at each segment view and at
each vertex crossing, `hY`, `hF`. -/
def CoverTie21 (y : Fin 7 → ℝ³) : Prop :=
  TieSeg (univ.image y) ∧ (∀ t, OneTieAt (univ.image y) (vtxView21 y t)) ∧ HY21 y ∧ HF21 y

/-- A listed tie: a named view and a pair of labels. -/
abbrev Tie21 : Type := ((Fin 7 × Fin 7) ⊕ Fin 8) × Fin 7 × Fin 7

/-- The listed tie holds at the shape `y`. -/
def TieHolds21 (y : Fin 7 → ℝ³) (τ : Tie21) : Prop :=
  ⟪y τ.2.1 - y τ.2.2, view21 y τ.1⟫ = 0

/-- **Independent ties generating every tie of `x` at the named views.** -/
def TieGen21 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (q : ℕ) (τ : Fin q → Tie21), (∀ t, TieHolds21 x (τ t)) ∧
    TieIndep (fun t => x (τ t).2.1 - x (τ t).2.2) (fun t => view21 x (τ t).1) ∧
    ∀ y : Fin 7 → ℝ³, (∀ t, TieHolds21 y (τ t)) →
      ∀ w a b, TieInst21 x w a b → ⟪y a - y b, view21 y w⟫ = 0

/-- **The tie hypothesis of B2** (replaces `OneTie21`). -/
def TwoTie21 (x : Fin 7 → ℝ³) : Prop := TieGen21 x ∧ CoverTie21 x

/-- **The interface of the limit lemmas**: a sequence of certified shapes converging to `x` that
keeps every tie of `x` at the named views. -/
def CertSeq21 (x : Fin 7 → ℝ³) : Prop :=
  ∃ K : ℕ → Fin 7 → ℝ³, (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
    ∃ᶠ n in atTop, CertX21 (K n) ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0

theorem detMap_eq21 (L : ℝ³ →L[ℝ] ℝ³) : detMap L = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp only [detMap, det3_expand, LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply]
  ring

/-- The named views are covariant. -/
theorem covView_view21 (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    CovView (fun y : Fin 7 → ℝ³ => view21 y v) := by
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun y => ?_
    exact tendsto_view21 (fun m => (continuous_apply m).tendsto y) v
  · intro L y hL
    have hd : detMap L = 1 := by rw [detMap_eq21]; exact hL
    obtain ⟨c, hc, e⟩ := view21_map L y v
    show view21 (fun l => L (y l)) v = L (view21 y v)
    rw [e]
    rcases hc with rfl | rfl
    · rw [one_smul]
    · rw [hd, one_smul]

/-- **At most one tied pair at a view whose ties are ties of `x`'s view.** -/
theorem oneTieAt_transfer {x y : Fin 7 → ℝ³} (hinj : Function.Injective x) {u u' : ℝ³}
    (hx : OneTieAt (univ.image x) u)
    (hsub : ∀ a b, a ≠ b → ⟪y a - y b, u'⟫ = 0 → ⟪x a - x b, u⟫ = 0) :
    OneTieAt (univ.image y) u' := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  obtain ⟨a', -, rfl⟩ := mem_image.mp hs'
  obtain ⟨b', -, rfl⟩ := mem_image.mp ht'
  have hab : a ≠ b := fun h => hst (by rw [h])
  have hab' : a' ≠ b' := fun h => hst' (by rw [h])
  have t1 := hsub a b hab (by rw [inner_sub_left, e1, sub_self])
  have t2 := hsub a' b' hab' (by rw [inner_sub_left, e2, sub_self])
  have t1' : ⟪x a, u⟫ = ⟪x b, u⟫ := by
    rw [inner_sub_left, sub_eq_zero] at t1; exact t1
  have t2' : ⟪x a', u⟫ = ⟪x b', u⟫ := by
    rw [inner_sub_left, sub_eq_zero] at t2; exact t2
  rcases hx _ (mem_image_of_mem x (mem_univ a)) _ (mem_image_of_mem x (mem_univ b)) _
    (mem_image_of_mem x (mem_univ a')) _ (mem_image_of_mem x (mem_univ b'))
    (fun h => hab (hinj h)) (fun h => hab' (hinj h)) t1' t2' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [hinj h1], by rw [hinj h2]⟩
  · exact Or.inr ⟨by rw [hinj h1], by rw [hinj h2]⟩

/-- **No tie at a view whose ties are ties of a tie-free view of `x`.** -/
theorem noTieAt_transfer {x y : Fin 7 → ℝ³} (hinj : Function.Injective x) {u u' : ℝ³}
    (hx : NoTieAt (univ.image x) u)
    (hsub : ∀ a b, a ≠ b → ⟪y a - y b, u'⟫ = 0 → ⟪x a - x b, u⟫ = 0) :
    NoTieAt (univ.image y) u' := by
  intro s hs t ht hst e
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  have hab : a ≠ b := fun h => hst (by rw [h])
  have t1 := hsub a b hab (by rw [inner_sub_left, e, sub_self])
  rw [inner_sub_left, sub_eq_zero] at t1
  exact hx _ (mem_image_of_mem x (mem_univ a)) _ (mem_image_of_mem x (mem_univ b))
    (fun h => hab (hinj h)) t1

/-- **`CoverTie21` passes from `x` to a shape whose ties at the named views are ties of `x`.** -/
theorem coverTie21_of_sub {x y : Fin 7 → ℝ³} (hinj : Function.Injective x)
    (hsub : ∀ v a b, a ≠ b → view21 y v ≠ 0 → ⟪y a - y b, view21 y v⟫ = 0 →
      ⟪x a - x b, view21 x v⟫ = 0)
    (hv : ∀ t, vtxView21 y t ≠ 0) (hw : ∀ i j, i ≠ j → y i - y j ≠ 0)
    (h : CoverTie21 x) : CoverTie21 y := by
  obtain ⟨hseg, hvt, ⟨hY0, hY1, hY2, hY3⟩, ⟨hF1, hF2, hF3, hF4⟩⟩ := h
  have prem : ∀ (t : Fin 8) (a b : Fin 7), a ≠ b → ⟪y a, vtxView21 y t⟫ = ⟪y b, vtxView21 y t⟫ →
      ⟪x a, vtxView21 x t⟫ = ⟪x b, vtxView21 x t⟫ := by
    intro t a b hab e
    have := hsub (.inr t) a b hab (hv t) (by
      show ⟪y a - y b, vtxView21 y t⟫ = 0
      rw [inner_sub_left, e, sub_self])
    have : ⟪x a - x b, vtxView21 x t⟫ = 0 := this
    rwa [inner_sub_left, sub_eq_zero] at this
  have seg : ∀ a b : Fin 7, a ≠ b → NoTieAt (univ.image x) (x a - x b) →
      NoTieAt (univ.image y) (y a - y b) := fun a b hab hn =>
    noTieAt_transfer hinj hn fun c d hcd e =>
      hsub (.inl (b, a)) c d hcd (hw a b hab) e
  have vtx : ∀ t : Fin 8, NoTieAt (univ.image x) (vtxView21 x t) →
      NoTieAt (univ.image y) (vtxView21 y t) := fun t hn =>
    noTieAt_transfer hinj hn fun c d hcd e => hsub (.inr t) c d hcd (hv t) e
  refine ⟨⟨fun v hv' w hw' hvw => ?_⟩, fun t => ?_,
    ⟨fun e => seg 0 4 (by decide) (hY0 (prem 0 0 4 (by decide) e)),
      fun e => seg 4 0 (by decide) (hY1 (prem 1 4 0 (by decide) e)),
      fun e => seg 5 3 (by decide) (hY2 (prem 2 5 3 (by decide) e)),
      fun e => seg 3 5 (by decide) (hY3 (prem 3 3 5 (by decide) e))⟩,
    ⟨hF1.imp (vtx 1) (vtx 4), hF2.imp (vtx 0) (vtx 5), hF3.imp (vtx 3) (vtx 6),
      hF4.imp (vtx 2) (vtx 7)⟩⟩
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hv'
    obtain ⟨j, -, rfl⟩ := mem_image.mp hw'
    have hij : i ≠ j := fun e => hvw (by rw [e])
    exact oneTieAt_transfer hinj (hseg.tie (x i) (mem_image_of_mem x (mem_univ i)) (x j)
      (mem_image_of_mem x (mem_univ j)) (hinj.ne hij)) fun a b hab e =>
      hsub (.inl (i, j)) a b hab (hw j i (Ne.symm hij)) e
  · exact oneTieAt_transfer hinj (hvt t) fun a b hab e => hsub (.inr t) a b hab (hv t) e

/-- **The approximating sequence with several ties** (generalizes `exists_certSeq21`): restore the
listed ties by `exists_seq_restore_ties`, `K n = nfShape21 (L n o) … (θs n)`; eventually the facet
inequalities and the named views are nonzero, every tie of `K n` is a tie of `x`
(`eventually_ties21`), so `CoverTie21` passes from `x` to `K n`; the cover `cert21_of_generic`; the
ties of `x` hold at `K n` by `TieGen21`. -/
theorem exists_certSeq21_ties {x : Fin 7 → ℝ³} (T : Facets21 x) (h : TwoTie21 x) :
    CertSeq21 x := by
  classical
  obtain ⟨⟨q, τ, hτ, hind, hgen⟩, hcov⟩ := h
  set θ₀ := theta21 x with hθ₀
  have hx : x = nfShape21 (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) θ₀ := T.eq_nfShape
  set o := x 2 with ho
  set E₁ := x 0 - x 2 with hE₁
  set E₂ := x 3 - x 2 with hE₂
  set E₃ := x 6 - x 2 with hE₃
  have hxs : nfShape21 o E₁ E₂ E₃ θ₀ = x := hx.symm
  have hshape : Continuous (fun θ => nfShape21 o E₁ E₂ E₃ θ) :=
    continuous_pi fun i => continuous_iff_continuousAt.2 fun θ =>
      tendsto_nfShape21 (o := fun _ : (Fin 7 → ℝ) => o) (E₁ := fun _ => E₁)
        (E₂ := fun _ => E₂) (E₃ := fun _ => E₃) tendsto_const_nhds tendsto_const_nhds
        tendsto_const_nhds tendsto_const_nhds tendsto_id i
  obtain ⟨θs, L, hθs, hL, hPs, hdet, hrest⟩ := exists_seq_restore_ties
    (fun θ => nfShape21 o E₁ E₂ E₃ θ) hshape genPoly21 genPoly21_ne_zero θ₀
    (fun t => (τ t).2) (fun t => fun y => view21 y (τ t).1) (fun t => covView_view21 _)
    (fun t => by simp only [hxs]; exact hτ t) (by simp only [hxs]; exact hind)
  set K : ℕ → Fin 7 → ℝ³ := fun j => mapShape (L j) (nfShape21 o E₁ E₂ E₃ (θs j)) with hKdef
  have hKe : ∀ n, K n = nfShape21 (L n o) (L n E₁) (L n E₂) (L n E₃) (θs n) := fun n =>
    map_nfShape21 (L n) o E₁ E₂ E₃ (θs n)
  have hev : Continuous (fun p : (ℝ³ →L[ℝ] ℝ³) × ℝ³ => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)) := by
    intro i
    have h1 : Tendsto (fun j => nfShape21 o E₁ E₂ E₃ (θs j) i) atTop
        (𝓝 (nfShape21 o E₁ E₂ E₃ θ₀ i)) :=
      ((continuous_apply i).comp hshape |>.tendsto θ₀).comp hθs
    have := (hev.tendsto (1, nfShape21 o E₁ E₂ E₃ θ₀ i)).comp (hL.prodMk_nhds h1)
    rw [hxs] at this
    exact this
  obtain ⟨κ, hκ, hneg⟩ := T.exists_kappa
  have hfac : ∀ᶠ n in atTop, ∀ f i, i ∉ facS f → fac21 κ (K n) f (K n i) < 0 := by
    refine eventually_all.mpr fun f => eventually_all.mpr fun i => ?_
    by_cases hi : i ∈ facS f
    · exact Eventually.of_forall fun _ h => absurd hi h
    · have hlim : Tendsto (fun n => fac21 κ (K n) f (K n i)) atTop
          (𝓝 (fac21 κ x f (x i))) := by
        simp only [fac21, detAff_apply]
        exact (Tendsto.det3' ((hK _).sub (hK _)) ((hK _).sub (hK _))
          ((hK _).sub (hK _))).const_mul _
      exact (hlim.eventually (gt_mem_nhds (hneg f i hi))).mono fun n hn _ => hn
  have hvtx : ∀ᶠ n in atTop, ∀ t, vtxView21 (K n) t ≠ 0 :=
    eventually_all.mpr fun t => (tendsto_view21 hK (.inr t)).eventually_ne (T.vtxView21_ne_zero t)
  have hsegs : ∀ᶠ n in atTop, ∀ i j : Fin 7, i ≠ j → K n i - K n j ≠ 0 :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · exact (((hK i).sub (hK j)).eventually_ne (sub_ne_zero.mpr (T.inj.ne hij))).mono
          fun n hn _ => hn
  refine ⟨K, hK, Eventually.frequently ?_⟩
  filter_upwards [eventually_ties21 hK, hfac, hvtx, hsegs] with n hs hf hv hw
  have hties : ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 :=
    fun w a b hw' => hgen (K n) (fun t => hrest n t) w a b hw'
  refine ⟨?_, hties⟩
  have hD : det3 (L n E₁) (L n E₂) (L n E₃) ≠ 0 := by
    rw [det3_map, detMap_eq21, hdet n, one_mul]; exact T.det_ne
  have hg : gen21 (θs n) ≠ 0 := by have := hPs n; rwa [eval_genPoly21] at this
  have hcovK : CoverTie21 (K n) := by
    refine coverTie21_of_sub T.inj (fun w a b hab hwv h' => hs w a b h') hv hw hcov
  obtain ⟨hgt, hvt, hY, hF⟩ := hcovK
  exact cert21_of_generic (hKe n) hD hg hκ hf hgt hvt hY hF
/-- **Type 21 outside the HDN set and codimension 2, with several independent ties**: a copy of
`isRupert_type21_limit_facets_codim2_of` whose tie hypothesis is `OneTie21 x ∨ TwoTie21 x`. -/
theorem isRupert_type21_limit_facets_codim2_of' (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hQ : (NoHDNAt (univ.image x) (x 6 - x 0) ∨
        QGenAff21 x fD fC 0 3 4 5 6 {0, 4, 6} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 6 - x 4) ∨ QGenAff21 x fD fG 4 5 0 3 6 {0, 4, 6} {2, 3, 4, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 5) ∨ QGenAff21 x fH fC 5 4 3 0 2 {2, 3, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 3) ∨ QGenAff21 x fH fG 3 0 5 4 2 {2, 3, 5} {2, 3, 4, 6}))
    (h5 : (NoHDNAt (univ.image x) (x 5 - x 0) ∨
        Q5GenAff21 x fB fC 0 3 1 6 2 5 4 {0, 1, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 3 - x 4) ∨
        Q5GenAff21 x fE fG 4 5 1 6 2 3 0 {1, 3, 4} {2, 3, 4, 6}))
    (h26 : NoHDNAt (univ.image x) (x 2 - x 6) ∨ R26GenAff21 x fC fG)
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hVq : ∀ K : ℕ → Fin 7 → ℝ³, (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) →
      (∃ᶠ n in atTop, CertD21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) →
      IsRupert (univ.image x))
    (hV : HDNOrG1Aff (univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      HDNOrG1Aff (univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : OneTie21 x ∨ TwoTie21 x) : IsRupert (univ.image x) := by
  let T := Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  obtain ⟨K, hK, hc⟩ : CertSeq21 x := htie.elim (exists_certSeq21 T) (exists_certSeq21_ties T)
  have hsplit : (∃ᶠ n in atTop, CertP21 UsedX21 (K n) ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
      (∃ᶠ n in atTop, CertQ21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
      (∃ᶠ n in atTop, CertW21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
      ∃ᶠ n in atTop, CertD21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 := by
    have : ∃ᶠ n in atTop, (CertP21 UsedX21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
        ((CertQ21 (K n) ∧ ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
        ((CertW21 (K n) ∧ ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) ∨
        (CertD21 (K n) ∧ ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0))) :=
      hc.mono fun n ⟨h, ht⟩ =>
        h.elim (fun h => Or.inl ⟨h, ht⟩) (fun h => Or.inr (h.elim (fun h => Or.inl ⟨h, ht⟩)
          (fun h => Or.inr (h.elim (fun h => Or.inl ⟨h, ht⟩) (fun h => Or.inr ⟨h, ht⟩)))))
    rcases frequently_or_distrib.mp this with h | h
    · exact Or.inl h
    rcases frequently_or_distrib.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (frequently_or_distrib.mp h))
  rcases hsplit with h | h | h | h
  · -- the certificates without data
    have hE' : ∀ e : Fin 6, HDNOrG1Edge (univ.image x) (x (triEdge21 e).1)
        (x (triEdge21 e).2.1) (x (triEdge21 e).2.2.1) (x (triEdge21 e).2.2.2) := by
      obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hEd
      intro e; fin_cases e
      exacts [e0, e1, e2, e3, e4, e5]
    refine isRupert_of_cert_seq21_sec T (P := UsedX21) (fun v hu hv => ?_) K hK h
    rcases v with ⟨i, j⟩ | t
    · have hmem := edgeX21_tri _ hu.1 hu.2.1 hu.2.2
      obtain ⟨e, he⟩ := triEdgeSet21_mem i j hmem
      rcases hE' e with h | h
      · left
        rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2]; exact h
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2, ← neg_sub]; exact h.neg
      · exact Or.inr ⟨e, he, h⟩
    · obtain ⟨V5, V6, V7, V8⟩ := hV
      have hu' : 4 ≤ t.val := hu
      fin_cases t
      · exact absurd hu' (by decide)
      · exact absurd hu' (by decide)
      · exact absurd hu' (by decide)
      · exact absurd hu' (by decide)
      · rcases V5 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fE hE (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl rfl, h⟩
      · rcases V6 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fB hB (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr (Or.inl rfl), h⟩
      · rcases V7 _ hv (affine_planeLine_perp fH hH (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fE hE (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)), h⟩
      · rcases V8 _ hv (affine_planeLine_perp fH hH (by decide) (by decide) (by decide))
          (affine_planeLine_perp' fB hB (by decide) (by decide) (by decide)) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr (Or.inr (Or.inr rfl)), h⟩
  · -- the certificates of tier Q at `06`, `46`, `25`, `23`
    obtain ⟨Q1, Q2, Q3, Q4⟩ := hQ
    have gen : ∀ {fT fQ : ℝ³ →ᵃ[ℝ] ℝ} {ST SQ : Finset (Fin 7)}
        (hT : ∀ i, (i ∈ ST → fT (x i) = 0) ∧ (i ∉ ST → fT (x i) < 0))
        (hQ : ∀ i, (i ∈ SQ → fQ (x i) = 0) ∧ (i ∉ SQ → fQ (x i) < 0)) {P P' R R' C' : Fin 7},
        NoHDNAt (univ.image x) (x C' - x P) ∨ QGenAff21 x fT fQ P P' R R' C' ST SQ →
        NoHDNAt (univ.image x) (x C' - x P) ∨
          QGen21 x (Face16.ofAffine fT hT).N (Face16.ofAffine fQ hQ).N P P' R R' C' ST SQ :=
      fun hT hQ _ _ _ _ _ h => h.imp_right fun h' =>
        h' _ _ (fun y => (Face16.ofAffine_inner _ hT y).symm)
          (fun y => (Face16.ofAffine_inner _ hQ y).symm)
    simp only [CertQ21, or_and_right] at h
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_qEdge21_or T T.f046 T.f0256 T.f2346 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hD hC Q1)
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_qEdge21_or T T.f046 T.f2346 T.f0256 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hD hG Q2)
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_qEdge21_or T T.f235 T.f0256 T.f2346 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hH hC Q3)
    · exact isRupert_qEdge21_or T T.f235 T.f2346 T.f0256 (by decide) (by decide) (by decide)
        (by decide) K hK h (gen hH hG Q4)
  · -- the certificates at `05`, `34`, `26`
    obtain ⟨Q5, Q6⟩ := h5
    have gen : ∀ {fT fQ : ℝ³ →ᵃ[ℝ] ℝ} {ST SQ : Finset (Fin 7)}
        (hT : ∀ i, (i ∈ ST → fT (x i) = 0) ∧ (i ∉ ST → fT (x i) < 0))
        (hQ : ∀ i, (i ∈ SQ → fQ (x i) = 0) ∧ (i ∉ SQ → fQ (x i) < 0))
        {P P' R R' D C' Q' : Fin 7},
        NoHDNAt (univ.image x) (x C' - x P) ∨ Q5GenAff21 x fT fQ P P' R R' D C' Q' ST SQ →
        NoHDNAt (univ.image x) (x C' - x P) ∨
          Q5Gen21 x (Face16.ofAffine fT hT).N (Face16.ofAffine fQ hQ).N P P' R R' D C' Q' ST SQ :=
      fun hT hQ _ _ _ _ _ _ _ h => h.imp_right fun h' =>
        h' _ _ (fun y => (Face16.ofAffine_inner _ hT y).symm)
          (fun y => (Face16.ofAffine_inner _ hQ y).symm)
    simp only [CertW21, or_and_right] at h
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_q5Edge21_or T T.f015 T.f0256 (P := 0) (C' := 5) (by decide) (by decide)
        (by decide) K hK h (gen hB hC Q5)
    rcases frequently_or_distrib.mp h with h | h
    · exact isRupert_q5Edge21_or T T.f134 T.f2346 (P := 4) (C' := 3) (by decide) (by decide)
        (by decide) K hK h (gen hE hG Q6)
    · rcases h26 with h26 | h26
      swap
      · exact isRupert_ridge21 T K hK (h.mono fun n hn => hn.1)
          (h26 _ _ (fun y => (Face16.ofAffine_inner _ hC y).symm)
            (fun y => (Face16.ofAffine_inner _ hG y).symm))
      refine isRupert_of_cert_seq21 T (P := fun v => v = .inl (6, 2) ∨ v = .inl (2, 6)) ?_ K hK
        (h.mono fun n hn => ⟨?_, hn.2⟩)
      · rintro v (rfl | rfl) -
        · exact h26
        · show NoHDNAt _ (x 6 - x 2)
          rw [← neg_sub]; exact h26.neg
      · rcases hn.1 with h | h
        · exact ⟨_, ⟨.inl (6, 2), Or.inl rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩
        · exact ⟨_, ⟨.inl (2, 6), Or.inr rfl, 1, one_ne_zero, (one_smul _ _).symm⟩, h.rimCert⟩
  · -- the four vertex lines with a quadrilateral
    exact hVq K hK h

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 2048 in
/-- `isRupert_type21_limit_facets_codim2` with `OneTie21 x ∨ TwoTie21 x`. -/
theorem isRupert_type21_limit_facets_codim2' (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hQ : (NoHDNAt (univ.image x) (x 6 - x 0) ∨
        QGenAff21 x fD fC 0 3 4 5 6 {0, 4, 6} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 6 - x 4) ∨ QGenAff21 x fD fG 4 5 0 3 6 {0, 4, 6} {2, 3, 4, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 5) ∨ QGenAff21 x fH fC 5 4 3 0 2 {2, 3, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 3) ∨ QGenAff21 x fH fG 3 0 5 4 2 {2, 3, 5} {2, 3, 4, 6}))
    (h5 : (NoHDNAt (univ.image x) (x 5 - x 0) ∨
        Q5GenAff21 x fB fC 0 3 1 6 2 5 4 {0, 1, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 3 - x 4) ∨
        Q5GenAff21 x fE fG 4 5 1 6 2 3 0 {1, 3, 4} {2, 3, 4, 6}))
    (h26 : NoHDNAt (univ.image x) (x 2 - x 6) ∨ R26GenAff21 x fC fG)
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hVq : HDNOrVtx21Aff x fC fA {0, 2, 5, 6} {0, 1, 4} 0 1 3 2 ∧
      HDNOrVtx21Aff x fG fA {2, 3, 4, 6} {0, 1, 4} 4 1 5 2 ∧
      HDNOrVtx21Aff x fC fF {0, 2, 5, 6} {1, 3, 5} 5 1 4 6 ∧
      HDNOrVtx21Aff x fG fF {2, 3, 4, 6} {1, 3, 5} 3 1 0 6)
    (hV : HDNOrG1Aff (univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      HDNOrG1Aff (univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : OneTie21 x ∨ TwoTie21 x) : IsRupert (univ.image x) := by
  let T := Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  refine isRupert_type21_limit_facets_codim2_of' x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF
    hG hH hQ h5 h26 hEd (fun K hK h => ?_) hV htie
  obtain ⟨V0, V1, V2, V3⟩ := hVq
  have h' : ∃ᶠ n in atTop, ∃ t : Fin 8, (t.val < 4 ∧ ∃ c : ℝ, c ≠ 0 ∧
      VtxDat21 (K n) t (c • vtxView21 (K n) t)) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 :=
    h.mono fun n ⟨⟨t, ht, hc⟩, hties⟩ => ⟨t, ⟨ht, hc⟩, hties⟩
  obtain ⟨t, hft⟩ := frequently_exists_of_finite h'
  obtain ⟨n₀, ⟨htv, -⟩, -⟩ := hft.exists
  -- without a horizontal double normal at the named view: Lemma 18.2
  have plain : NoHDNAt (univ.image x) (vtxView21 x t) → IsRupert (univ.image x) := fun hnd =>
    isRupert_of_cert_seq21 T (P := fun v => v = .inr t) (fun v hv _ => by subst hv; exact hnd) K
      hK (hft.mono fun n ⟨⟨_, c, hc, hd⟩, hties⟩ =>
        ⟨⟨_, ⟨.inr t, rfl, c, hc, rfl⟩, hd.rimCert htv⟩, hties⟩)
  have norm : ∀ {v a c b h w n : Fin 7} {t' : Fin 8},
      (∀ y u, VtxDat21 y t u = LineDat21 y v a c b h w n u (vtxView21 y t')) →
      ∃ᶠ k in atTop, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        LineDat21 (K k) v a c b h w n (ε • vtxView21 (K k) t) (vtxView21 (K k) t') :=
    fun e => hft.mono fun n ⟨⟨_, c, hc, hd⟩, _⟩ => LineDat21.norm hc (by rw [← e]; exact hd)
  fin_cases t
  · -- `014/0256` at `0`: `T1` and `σ1`'s `V`
    rcases V0 (vtxView21 x 0) (T.vtxView21_ne_zero 0)
      (affine_planeLine_perp' fC hC (by decide) (by decide) (by decide))
      (affine_planeLine_perp fA hA (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f014 T.f0256 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f014 T.f0256 T.f015 T.f046 (v := 0) (a := 2) (c := 3) (b := 1)
      (h := 5) (w := 6) (n := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 0) p2 p1
      (T.vtxView21_ne_zero 5) _ _ (tendsto_view21 hK (.inr 0)) (tendsto_view21 hK (.inr 5)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hC y).symm) hoff
  · -- `014/2346` at `4`: `σ1`'s `T1` and `V`
    rcases V1 (vtxView21 x 1) (T.vtxView21_ne_zero 1)
      (affine_planeLine_perp' fG hG (by decide) (by decide) (by decide))
      (affine_planeLine_perp fA hA (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f014 T.f2346 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f014 T.f2346 T.f134 T.f046 (v := 4) (a := 2) (c := 5) (b := 1)
      (h := 3) (w := 6) (n := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 1) p2 p1
      (T.vtxView21_ne_zero 4) _ _ (tendsto_view21 hK (.inr 1)) (tendsto_view21 hK (.inr 4)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hG y).symm) hoff
  · -- `135/0256` at `5`: `σ2`'s `T1` and `σ2σ1`'s `V`
    rcases V2 (vtxView21 x 2) (T.vtxView21_ne_zero 2)
      (affine_planeLine_perp' fC hC (by decide) (by decide) (by decide))
      (affine_planeLine_perp fF hF (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f135 T.f0256 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f135 T.f0256 T.f015 T.f235 (v := 5) (a := 6) (c := 4) (b := 1)
      (h := 0) (w := 2) (n := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 2) p2 p1
      (T.vtxView21_ne_zero 7) _ _ (tendsto_view21 hK (.inr 2)) (tendsto_view21 hK (.inr 7)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hC y).symm) hoff
  · -- `135/2346` at `3`: `σ2σ1`'s `T1` and `σ2`'s `V`
    rcases V3 (vtxView21 x 3) (T.vtxView21_ne_zero 3)
      (affine_planeLine_perp' fG hG (by decide) (by decide) (by decide))
      (affine_planeLine_perp fF hF (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f135 T.f2346 3 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f135 T.f2346 T.f134 T.f235 (v := 3) (a := 6) (c := 0) (b := 1)
      (h := 4) (w := 2) (n := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 3) p2 p1
      (T.vtxView21_ne_zero 6) _ _ (tendsto_view21 hK (.inr 3)) (tendsto_view21 hK (.inr 6)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hG y).symm) hoff
  all_goals exact absurd htv (by decide)

end Minimality

/-- **Type 21 outside codimension 2, with several independent ties** (`not_type21_of_isNopert_codim2`
with `htie : OneTie21 x ∨ TwoTie21 x`). -/
theorem not_type21_of_isNopert_ties (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hQ : (Minimality.NoHDNAt (Finset.univ.image x) (x 6 - x 0) ∨
        Minimality.QGenAff21 x fD fC 0 3 4 5 6 {0, 4, 6} {0, 2, 5, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 6 - x 4) ∨
        Minimality.QGenAff21 x fD fG 4 5 0 3 6 {0, 4, 6} {2, 3, 4, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 5) ∨
        Minimality.QGenAff21 x fH fC 5 4 3 0 2 {2, 3, 5} {0, 2, 5, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 3) ∨
        Minimality.QGenAff21 x fH fG 3 0 5 4 2 {2, 3, 5} {2, 3, 4, 6}))
    (h5 : (Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 0) ∨
        Minimality.Q5GenAff21 x fB fC 0 3 1 6 2 5 4 {0, 1, 5} {0, 2, 5, 6}) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 3 - x 4) ∨
        Minimality.Q5GenAff21 x fE fG 4 5 1 6 2 3 0 {1, 3, 4} {2, 3, 4, 6}))
    (h26 : Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 6) ∨
      Minimality.R26GenAff21 x fC fG)
    (hEd : Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hVq : Minimality.HDNOrVtx21Aff x fC fA {0, 2, 5, 6} {0, 1, 4} 0 1 3 2 ∧
      Minimality.HDNOrVtx21Aff x fG fA {2, 3, 4, 6} {0, 1, 4} 4 1 5 2 ∧
      Minimality.HDNOrVtx21Aff x fC fF {0, 2, 5, 6} {1, 3, 5} 5 1 4 6 ∧
      Minimality.HDNOrVtx21Aff x fG fF {2, 3, 4, 6} {1, 3, 5} 3 1 0 6)
    (hV : Minimality.HDNOrG1Aff (Finset.univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : Minimality.OneTie21 x ∨ Minimality.TwoTie21 x) : False :=
  h.2 (Minimality.isRupert_type21_limit_facets_codim2' x hx fA fB fC fD fE fF fG fH hA hB hC hD
    hE hF hG hH hQ h5 h26 hEd hVq hV htie)
