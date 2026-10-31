module

public import Minimality.Type29Codim2
public import Minimality.Type16Metric
public import Minimality.Type21Ties
public import Minimality.Generic.LimitSeq

@[expose] public section

/-!
# Type 29, classes K3 and K4, with several independent ties (package B3)

`OneTieGlobal29` (at most one tie) is replaced by `TwoTie29`: independent generating ties
(`TieGen29`) and the cover's own tie hypothesis `Tie29` (at most one tied pair at each named view,
independent ties at the two views of each combined pair, `IndepF`) for `x` and for `x ∘ σ`.  The ties are restored along an
approximating sequence (`exists_seq_restore_ties`); the cover at the sequence needs only `Tie29`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- A listed tie: a named view and a pair of labels. -/
abbrev Tie29L : Type := View29 × Fin 7 × Fin 7

/-- The listed tie holds at the shape `y`. -/
def TieHolds29 (y : Fin 7 → ℝ³) (τ : Tie29L) : Prop :=
  ⟪y τ.2.1 - y τ.2.2, view29 y τ.1⟫ = 0

/-- **Independent ties generating every tie of `x`** at the named views (as `TieGen16`). -/
def TieGen29 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (q : ℕ) (τ : Fin q → Tie29L), (∀ t, TieHolds29 x (τ t)) ∧
    TieIndep (fun t => x (τ t).2.1 - x (τ t).2.2) (fun t => view29 x (τ t).1) ∧
    ∀ y : Fin 7 → ℝ³, (∀ t, TieHolds29 y (τ t)) →
      ∀ w a b, TieInst29 x w a b → ⟪y a - y b, view29 y w⟫ = 0

/-- **The tie hypothesis of B3** (replaces `OneTieGlobal29`): independent generating ties and the
cover's tie condition `Tie29` at `x` and at its `σ`-image. -/
def TwoTie29 (x : Fin 7 → ℝ³) : Prop :=
  TieGen29 x ∧ Tie29 x ∧ Tie29 (x ∘ sigma29)

theorem map_nfShape29 (M : ℝ³ →L[ℝ] ℝ³) (o E₁ E₂ E₃ : ℝ³) (θ : Fin 8 → ℝ) :
    (fun i => M (nfShape29 o E₁ E₂ E₃ θ i)) = nfShape29 (M o) (M E₁) (M E₂) (M E₃) θ := by
  funext i; fin_cases i <;> exact map_nfP M o E₁ E₂ E₃ _ _ _

/-- **At most one tied pair at a view whose ties are ties of `x`'s view.** -/
theorem oneTieAt_of_sub29 {x y : Fin 7 → ℝ³} (hinj : Function.Injective x) {u u' : ℝ³}
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

/-- **`Tie29` passes to a shape whose ties at the named views are ties of `x`**
(and whose pairs `pairViewsGO29` satisfy `IndepF`, which does not pass pointwise). -/
theorem tie29_of_sub {x y : Fin 7 → ℝ³} (hx : Function.Injective x) (ht : Tie29 x)
    (hne : ∀ v, view29 y v ≠ 0 → view29 x v ≠ 0)
    (hsub : ∀ v a b, a ≠ b → view29 y v ≠ 0 → ⟪y a - y b, view29 y v⟫ = 0 →
      ⟪x a - x b, view29 x v⟫ = 0)
    (hI : ∀ p ∈ pairViewsGO29, view29 y p.1 ≠ 0 → view29 y p.2 ≠ 0 →
      IndepF (univ.image y) (view29 y p.1) (view29 y p.2)) : Tie29 y where
  one := fun v hv =>
    oneTieAt_of_sub29 hx (ht.one v (hne v hv)) (fun a b hab h => hsub v a b hab hv h)
  indep := hI

/-! ### `σ`-invariance -/

theorem tieHolds29_sigma (y : Fin 7 → ℝ³) (v : View29) (s t : Fin 7) :
    TieHolds29 (y ∘ sigma29) (sigmaV29 v, sigma29 s, sigma29 t) ↔ TieHolds29 y (v, s, t) := by
  obtain ⟨c, hc, hv⟩ := view29_sigma y (sigmaV29 v)
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  unfold TieHolds29
  simp only [Function.comp_apply, sigma29_sigma29, hv, sigmaV29_sigmaV29, real_inner_smul_right,
    mul_eq_zero, hc0, false_or]

theorem TieGen29.sigma {x : Fin 7 → ℝ³} (h : TieGen29 x) : TieGen29 (x ∘ sigma29) := by
  obtain ⟨q, τ, hτ, hind, hgen⟩ := h
  refine ⟨q, fun t => (sigmaV29 (τ t).1, sigma29 (τ t).2.1, sigma29 (τ t).2.2), ?_, ?_, ?_⟩
  · intro t
    exact (tieHolds29_sigma x (τ t).1 (τ t).2.1 (τ t).2.2).2 (hτ t)
  · have hc : ∀ t, ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        view29 (x ∘ sigma29) (sigmaV29 (τ t).1) = c • view29 x (τ t).1 := by
      intro t
      obtain ⟨c, hc, hv⟩ := view29_sigma x (sigmaV29 (τ t).1)
      exact ⟨c, hc, by rw [hv, sigmaV29_sigmaV29]⟩
    choose c hc hcv using hc
    intro lam hl
    have hc0 : ∀ t, c t ≠ 0 := fun t => by rcases hc t with h | h <;> rw [h] <;> norm_num
    have h2 : (fun t => lam t * c t) = 0 := by
      refine hind _ fun G => ?_
      have := hl G
      simp only [Function.comp_apply, sigma29_sigma29, hcv, map_smul, real_inner_smul_right,
        real_inner_smul_left] at this
      rw [← this]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    funext t
    have := congrFun h2 t
    simp only [Pi.zero_apply, mul_eq_zero, hc0 t, or_false] at this ⊢
    exact this
  · intro y hy w a b hw
    have hy' : ∀ t, TieHolds29 (y ∘ sigma29) (τ t) := by
      intro t
      have := (tieHolds29_sigma y (sigmaV29 (τ t).1) (sigma29 (τ t).2.1)
        (sigma29 (τ t).2.2)).2 (hy t)
      simpa [sigmaV29_sigmaV29, sigma29_sigma29] using this
    have h1 := hgen (y ∘ sigma29) hy' (sigmaV29 w) (sigma29 a) (sigma29 b)
      ((TieInst29.sigma_iff x w a b).mp hw)
    exact (tieHolds29_sigma y w a b).1 h1


theorem TwoTie29.sigma {x : Fin 7 → ℝ³} (h : TwoTie29 x) : TwoTie29 (x ∘ sigma29) := by
  obtain ⟨g, t1, t2⟩ := h
  refine ⟨g.sigma, t2, ?_⟩
  have e : (x ∘ sigma29) ∘ sigma29 = x := by
    funext i; simp [Function.comp_apply, sigma29_sigma29]
  rw [e]; exact t1

/-- **The approximating sequence with its parameters and several ties**
(`exists_certSeq29_params` with `TwoTie29`): restore the listed ties by `exists_seq_restore_ties`,
`K n = nfShape29 (L n N.o) … (θs n)`; eventually the inequalities and the class, and every tie of
`K n` is a tie of `x` (`eventually_ties29`), so `Tie29` passes from `x` to `K n`; the cover; the
ties of `x` hold at `K n` by `TieGen29`. -/
theorem exists_certSeq29_params_ties {x : Fin 7 → ℝ³} (N : NF29 x) (h : TwoTie29 x)
    (hcls : (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) ∨
      (0 < N.a2 ∧ 0 < N.b0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)) :
    ∃ (K : ℕ → Fin 7 → ℝ³) (θs : ℕ → Fin 8 → ℝ),
      (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
      Tendsto θs atTop (𝓝 ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t]) ∧
      ∃ᶠ n in atTop, Cert29 (K n) ∧
        (∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0) ∧
        ∃ Nn : NF29 (K n), ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n := by
  classical
  obtain ⟨⟨q, τ, hτ, hind, hgen⟩, htie, -⟩ := h
  set θ₀ : Fin 8 → ℝ := ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t] with hθ₀
  have hx : x = nfShape29 N.o N.E₁ N.E₂ N.E₃ θ₀ := N.eq_nfShape29
  have hxs : nfShape29 N.o N.E₁ N.E₂ N.E₃ θ₀ = x := hx.symm
  have hshape : Continuous (fun θ => nfShape29 N.o N.E₁ N.E₂ N.E₃ θ) :=
    continuous_pi fun i => continuous_iff_continuousAt.2 fun θ =>
      tendsto_nfShape29 (o := fun _ : (Fin 8 → ℝ) => N.o) (E₁ := fun _ => N.E₁)
        (E₂ := fun _ => N.E₂) (E₃ := fun _ => N.E₃) tendsto_const_nhds tendsto_const_nhds
        tendsto_const_nhds tendsto_const_nhds tendsto_id i
  obtain ⟨θs, L, hθs, hL, hPs, hdet, hrest⟩ := exists_seq_restore_ties
    (fun θ => nfShape29 N.o N.E₁ N.E₂ N.E₃ θ) hshape genPoly29 genPoly29_ne_zero θ₀
    (fun t => (τ t).2) (fun t => fun y => view29 y (τ t).1) (fun t => covView_view29 _)
    (fun t => by simp only [hxs]; exact hτ t) (by simp only [hxs]; exact hind)
  set K : ℕ → Fin 7 → ℝ³ := fun n =>
    nfShape29 (L n N.o) (L n N.E₁) (L n N.E₂) (L n N.E₃) (θs n) with hKdef
  have hKm : ∀ n, K n = mapShape (L n) (nfShape29 N.o N.E₁ N.E₂ N.E₃ (θs n)) := fun n =>
    (map_nfShape29 (L n) N.o N.E₁ N.E₂ N.E₃ (θs n)).symm
  have hev : Continuous (fun p : (ℝ³ →L[ℝ] ℝ³) × ℝ³ => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)) := by
    intro i
    have h1 : Tendsto (fun j => nfShape29 N.o N.E₁ N.E₂ N.E₃ (θs j) i) atTop
        (𝓝 (nfShape29 N.o N.E₁ N.E₂ N.E₃ θ₀ i)) :=
      ((continuous_apply i).comp hshape |>.tendsto θ₀).comp hθs
    have := (hev.tendsto (1, nfShape29 N.o N.E₁ N.E₂ N.E₃ θ₀ i)).comp (hL.prodMk_nhds h1)
    rw [hxs] at this
    have e : ∀ n, K n i = L n (nfShape29 N.o N.E₁ N.E₂ N.E₃ (θs n) i) := fun n => by
      rw [hKm n]; rfl
    simp only [e]
    exact this
  have hineq : ∀ᶠ n in atTop, ∀ k, 0 < ineq29 (θs n) k :=
    eventually_all.mpr fun k =>
      (((continuous_ineq29 k).tendsto θ₀).comp hθs).eventually (lt_mem_nhds (N.ineq k))
  have hcl : ∀ᶠ n in atTop, (θs n 3 < 0 ∧ 0 < θs n 1 ∧ 0 < vpoly29 (θs n)) ∨
      (0 < θs n 3 ∧ 0 < θs n 1 ∧ vpoly29 (θs n) < 0) := by
    have c3 : Tendsto (fun n => θs n 3) atTop (𝓝 N.a2) :=
      ((continuous_apply 3).tendsto θ₀).comp hθs
    have c1 : Tendsto (fun n => θs n 1) atTop (𝓝 N.b0) :=
      ((continuous_apply 1).tendsto θ₀).comp hθs
    have cv : Tendsto (fun n => vpoly29 (θs n)) atTop
        (𝓝 (N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))) :=
      (continuous_vpoly29.tendsto θ₀).comp hθs
    rcases hcls with ⟨h3, h1, hv⟩ | ⟨h3, h1, hv⟩
    · filter_upwards [c3.eventually (gt_mem_nhds h3), c1.eventually (lt_mem_nhds h1),
        cv.eventually (lt_mem_nhds hv)] with n a b c
      exact Or.inl ⟨a, b, c⟩
    · filter_upwards [c3.eventually (lt_mem_nhds h3), c1.eventually (lt_mem_nhds h1),
        cv.eventually (gt_mem_nhds hv)] with n a b c
      exact Or.inr ⟨a, b, c⟩
  have hind4 : ∀ p : View29 × View29, ∀ᶠ n in atTop, p ∈ pairViewsGO29 → view29 x p.1 ≠ 0 →
      view29 x p.2 ≠ 0 → ∀ i j k l : Fin 7, i ≠ j → k ≠ l → ⟪x i - x j, view29 x p.1⟫ = 0 →
        ⟪x k - x l, view29 x p.2⟫ = 0 →
        TieIndep ![K n i - K n j, K n k - K n l] ![view29 (K n) p.1, view29 (K n) p.2] := by
    intro p
    by_cases h : p ∈ pairViewsGO29 ∧ view29 x p.1 ≠ 0 ∧ view29 x p.2 ≠ 0
    · obtain ⟨hp, h1, h2⟩ := h
      filter_upwards [eventually_indepF hK (tendsto_view29 hK p.1) (tendsto_view29 hK p.2) N.inj
        (htie.indep p hp h1 h2)] with n hn _ _ _ using hn
    · exact Eventually.of_forall fun n hp h1 h2 => absurd ⟨hp, h1, h2⟩ h
  refine ⟨K, θs, hK, hθs, Eventually.frequently ?_⟩
  filter_upwards [hineq, hcl, eventually_ties29 hK, eventually_all.mpr hind4] with n hn hc hs hI
  have hties : ∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0 := by
    intro w a b hw
    refine hgen (K n) (fun t => ?_) w a b hw
    have := hrest n t
    rw [← hKm n] at this
    exact this
  have hD : det3 (L n N.E₁) (L n N.E₂) (L n N.E₃) ≠ 0 := by
    rw [det3_map, detMap_eq_det, hdet n, one_mul]; exact N.hD
  set Nn := NF29.ofParams (L n N.o) (L n N.E₁) (L n N.E₂) (L n N.E₃) (θs n) hD hn with hNn
  refine ⟨?_, hties, Nn, by funext i; fin_cases i <;> rfl⟩
  have hg := hPs n
  rw [eval_genPoly29] at hg
  have hsubK : ∀ v a b, a ≠ b → view29 (K n) v ≠ 0 → ⟪K n a - K n b, view29 (K n) v⟫ = 0 →
      ⟪x a - x b, view29 x v⟫ = 0 := fun v a b _ _ h => hs v a b h
  have hne : ∀ v, view29 (K n) v ≠ 0 → view29 x v ≠ 0 := by
    intro v hv
    refine N.view29_ne_zero v ?_
    rintro i rfl
    exact hv (by simp [view29])
  have hIK : ∀ p ∈ pairViewsGO29, view29 (K n) p.1 ≠ 0 → view29 (K n) p.2 ≠ 0 →
      IndepF (univ.image (K n)) (view29 (K n) p.1) (view29 (K n) p.2) := fun p hp h1 h2 =>
    indepF_of_sub (x := x) (y := K n) (fun a b _ h => hs p.1 a b h) (fun a b _ h => hs p.2 a b h)
      (hI p hp (hne p.1 h1) (hne p.2 h2))
  have T29 : Tie29 (K n) := tie29_of_sub N.inj htie hne hsubK hIK
  rcases hc with ⟨h3, h1, hv⟩ | ⟨h3, h1, hv⟩
  · exact Nn.cert29_K3a_all h3 h1 hv (Nn.k3Poly_of_gen hg) (Nn.k3C1Poly_of_gen hg) T29
  · exact Nn.cert29_K4a_all h3 h1 hv (Nn.k4Poly_of_gen hg) (Nn.k4C1Poly_of_gen hg) T29

/-- `exists_certSeq29_params` for either tie hypothesis. -/
theorem exists_certSeq29_params' {x : Fin 7 → ℝ³} (N : NF29 x)
    (htie : OneTieGlobal29 x ∨ TwoTie29 x)
    (hcls : (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) ∨
      (0 < N.a2 ∧ 0 < N.b0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)) :
    ∃ (K : ℕ → Fin 7 → ℝ³) (θs : ℕ → Fin 8 → ℝ),
      (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
      Tendsto θs atTop (𝓝 ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t]) ∧
      ∃ᶠ n in atTop, Cert29 (K n) ∧
        (∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0) ∧
        ∃ Nn : NF29 (K n), ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n :=
  htie.elim (fun h => exists_certSeq29_params N h hcls)
    (fun h => exists_certSeq29_params_ties N h hcls)

/-- `isRupert_type29_limit_hdn` with either tie hypothesis. -/
theorem isRupert_type29_limit_hdn' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hcls : (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) ∨
      (0 < N.a2 ∧ 0 < N.b0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0))
    (H : ∀ ℓ : Lab29, ℓ.Ok → Cond29 N ℓ) (htie : OneTieGlobal29 x ∨ TwoTie29 x) :
    IsRupert (univ.image x) := by
  obtain ⟨K, θs, hK, hθs, hc⟩ := exists_certSeq29_params' N htie hcls
  exact isRupert_of_cert_seq29_hdn N K hK θs hθs H hc

theorem NF29.isRupert_K3a_codim2' {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))
    (htie : OneTieGlobal29 x ∨ TwoTie29 x) (hH : HDN29K3 N) : IsRupert (univ.image x) :=
  isRupert_type29_limit_hdn' N (Or.inl ⟨ha2, hb0, hV⟩) hH htie

theorem NF29.isRupert_K4a_codim2' {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)
    (htie : OneTieGlobal29 x ∨ TwoTie29 x) (hH : HDN29K4 N) : IsRupert (univ.image x) :=
  isRupert_type29_limit_hdn' N (Or.inr ⟨ha2, hb0, hV⟩) hH htie

theorem NF29.isRupert_K3b_codim2' {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : N.b0 < 0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)
    (htie : OneTieGlobal29 x ∨ TwoTie29 x) (hH : HDN29K3 N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K3a_codim2' N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith)
    (htie.imp OneTieGlobal29.sigma TwoTie29.sigma) hH
  rwa [image_sigma29] at h

theorem NF29.isRupert_K4b_codim2' {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))
    (htie : OneTieGlobal29 x ∨ TwoTie29 x) (hH : HDN29K4 N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K4a_codim2' N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith)
    (htie.imp OneTieGlobal29.sigma TwoTie29.sigma) hH
  rwa [image_sigma29] at h


end Minimality

end
