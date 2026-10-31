module

public import Minimality.Cases
public import Minimality.Type16Edge2
public import Minimality.Type16Metric
public import Minimality.Generic.LimitSeq
public import Minimality.Generic.PairR2T
public import Minimality.Generic.NamedViews

@[expose] public section

/-!
# Type 16 with several independent ties (package B1a)

`OneTie16` (at most one tie) is replaced by `TwoTie16`: independent generating ties (`TieGen16`),
at most one tied pair at each segment view (`TieSeg`) and at `v_A`, `σ v_A` (`VA16`).  The ties
are restored along an approximating sequence (`exists_seq_restore_ties`); the cover at the
sequence needs only `TieSeg` and `VA16` (`cert16_nfShape_tieSeg`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **At most one tied pair at the two vertex views of Lemma 19.5's pentagon** (`v_A` and its
`σ`-image): the `Views` hypothesis of `NF16.cert_nf`.  The other four vertex views are free. -/
def VA16 (x : Fin 7 → ℝ³) : Prop :=
  (view16 x (.inr 1) ≠ 0 → OneTieAt (univ.image x) (view16 x (.inr 1))) ∧
  (view16 x (.inr 4) ≠ 0 → OneTieAt (univ.image x) (view16 x (.inr 4)))

/-- A listed tie: a named view and a pair of labels. -/
abbrev Tie16 : Type := ((Fin 7 × Fin 7) ⊕ Fin 6) × Fin 7 × Fin 7

/-- The listed tie holds at the shape `y`. -/
def TieHolds16 (y : Fin 7 → ℝ³) (τ : Tie16) : Prop :=
  ⟪y τ.2.1 - y τ.2.2, view16 y τ.1⟫ = 0

/-- **Independent ties generating every tie of `x` at the named views**: finitely many ties of
`x`, independent as metric functionals (`TieIndep`), such that at every shape where they hold,
every tie of `x` at a named view holds.  Fails only for dependent tie functionals. -/
def TieGen16 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (q : ℕ) (τ : Fin q → Tie16), (∀ t, TieHolds16 x (τ t)) ∧
    TieIndep (fun t => x (τ t).2.1 - x (τ t).2.2) (fun t => view16 x (τ t).1) ∧
    ∀ y : Fin 7 → ℝ³, (∀ t, TieHolds16 y (τ t)) →
      ∀ w a b, TieInst16 x w a b → ⟪y a - y b, view16 y w⟫ = 0

/-- **The tie hypothesis of B1a** (replaces `OneTie16`): independent generating ties, at most one
tied pair at each segment view (`TieSeg`), at most one tied pair at `v_A` and `σ v_A`. -/
def TwoTie16 (x : Fin 7 → ℝ³) : Prop :=
  TieGen16 x ∧ TieSeg (univ.image x) ∧ VA16 x

/-- **The interface of the limit lemmas**: a sequence of certified shapes converging to `x` that
keeps every tie of `x` at the named views. -/
def CertSeq16 (x : Fin 7 → ℝ³) : Prop :=
  ∃ K : ℕ → Fin 7 → ℝ³, (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
    ∃ᶠ n in atTop, Cert16 (K n) ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0

/-- **The cover with ties** (`cert16_nfShape` without `NoTies16`): a normal-form shape off
`genPoly16` with at most one tied pair at each segment view and at `v_A`, `σ v_A` is certified. -/
theorem cert16_nfShape_tieSeg (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (hD : det3 E₁ E₂ E₃ ≠ 0)
    (hn : ∀ k, 0 < ineq16 θ k) (hg : MvPolynomial.eval θ genPoly16 ≠ 0)
    (hgt : TieSeg (univ.image (nfShape o E₁ E₂ E₃ θ))) (hvA : VA16 (nfShape o E₁ E₂ E₃ θ)) :
    Cert16 (nfShape o E₁ E₂ E₃ θ) := by
  set Nn := NF16.ofParams o E₁ E₂ E₃ θ hD hn with hNn
  rw [eval_genPoly16, mul_ne_zero_iff, mul_ne_zero_iff] at hg
  obtain ⟨⟨g1, g2⟩, g3⟩ := hg
  have G : NF16.Gen Nn := NF16.Gen.ofFactors Nn g1
  have Gσ : NF16.Gen Nn.sigma := NF16.Gen.ofFactors Nn.sigma g2
  have hR : Nn.R1 ≠ 0 ∧ Nn.R2 ≠ 0 := by
    simp only [rFactors, mul_ne_zero_iff] at g3; exact g3
  have W : NF16.Views Nn := by
    refine ⟨fun hne => ?_⟩
    have e := NF16.vtxView16_vA Nn
    have hD' : -Nn.D ≠ 0 := neg_ne_zero.mpr Nn.hD
    have hv1 : view16 (nfShape o E₁ E₂ E₃ θ) (.inr 1) ≠ 0 := by
      show vtxView16 _ 1 ≠ 0
      rw [e]; exact smul_ne_zero hD' hne
    have e2 : Nn.vA = (-Nn.D)⁻¹ • view16 (nfShape o E₁ E₂ E₃ θ) (.inr 1) := by
      show _ = _ • vtxView16 _ 1
      rw [e, smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [e2]
    exact (hvA.1 hv1).smul (inv_ne_zero hD')
  have Wσ : NF16.Views Nn.sigma := by
    refine ⟨fun hne => ?_⟩
    have e := NF16.vtxView16_vA Nn.sigma
    rw [vtxView16_sigma] at e
    have hD' : -Nn.sigma.D ≠ 0 := neg_ne_zero.mpr Nn.sigma.hD
    have hv4 : view16 (nfShape o E₁ E₂ E₃ θ) (.inr 4) ≠ 0 := by
      show vtxView16 _ 4 ≠ 0
      rw [show (4 : Fin 6) = 1 + 3 from rfl, e]; exact smul_ne_zero hD' hne
    have e2 : Nn.sigma.vA = (-Nn.sigma.D)⁻¹ • view16 (nfShape o E₁ E₂ E₃ θ) (.inr 4) := by
      show _ = _ • vtxView16 _ 4
      rw [show (4 : Fin 6) = 1 + 3 from rfl, e, smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [e2, image_sigma16]
    exact (hvA.2 hv4).smul (inv_ne_zero hD')
  exact NF16.cert_nf Nn G Gσ W Wσ hR.1 hR.2 hgt

/-- The named views are covariant (segments: linear; vertex crossings: `planeLine_map`, factor
`det = 1`). -/
theorem view16_eq_namedView : view16 = namedView vtx16 := by
  funext x v; rcases v with _ | _ <;> rfl

theorem covView_view16 (v : (Fin 7 × Fin 7) ⊕ Fin 6) :
    CovView (fun y : Fin 7 → ℝ³ => view16 y v) :=
  by rw [view16_eq_namedView]; exact covView_namedView vtx16 v

/-- **At most one tied pair at a named view of a shape whose ties are ties of `x`.** -/
theorem oneTieAt_of_sub {x y : Fin 7 → ℝ³} (hinj : Function.Injective x)
    (v : (Fin 7 × Fin 7) ⊕ Fin 6) (hx : OneTieAt (univ.image x) (view16 x v))
    (hsub : ∀ a b, a ≠ b → ⟪y a - y b, view16 y v⟫ = 0 → ⟪x a - x b, view16 x v⟫ = 0) :
    OneTieAt (univ.image y) (view16 y v) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  obtain ⟨a', -, rfl⟩ := mem_image.mp hs'
  obtain ⟨b', -, rfl⟩ := mem_image.mp ht'
  have hab : a ≠ b := fun h => hst (by rw [h])
  have hab' : a' ≠ b' := fun h => hst' (by rw [h])
  have t1 := hsub a b hab (by rw [inner_sub_left, e1, sub_self])
  have t2 := hsub a' b' hab' (by rw [inner_sub_left, e2, sub_self])
  have t1' : ⟪x a, view16 x v⟫ = ⟪x b, view16 x v⟫ := by
    rw [inner_sub_left, sub_eq_zero] at t1; exact t1
  have t2' : ⟪x a', view16 x v⟫ = ⟪x b', view16 x v⟫ := by
    rw [inner_sub_left, sub_eq_zero] at t2; exact t2
  rcases hx _ (mem_image_of_mem x (mem_univ a)) _ (mem_image_of_mem x (mem_univ b)) _
    (mem_image_of_mem x (mem_univ a')) _ (mem_image_of_mem x (mem_univ b'))
    (fun h => hab (hinj h)) (fun h => hab' (hinj h)) t1' t2' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [hinj h1], by rw [hinj h2]⟩
  · exact Or.inr ⟨by rw [hinj h1], by rw [hinj h2]⟩

/-- **The approximating sequence with several ties** (generalizes `exists_certSeq16`): restore the
listed ties by `exists_seq_restore_ties`, `K n = nfShape (L n N.o) … (θs n)`; eventually `ineq16`,
every tie of `K n` is a tie of `x` (`eventually_ties`), so `TieSeg` and `VA16` pass from `x` to
`K n`; the cover `cert16_nfShape_tieSeg`; the ties of `x` hold at `K n` by `TieGen16`. -/
theorem exists_certSeq16_ties {x : Fin 7 → ℝ³} (T : Type16 x) (h : TwoTie16 x) : CertSeq16 x := by
  classical
  obtain ⟨⟨q, τ, hτ, hind, hgen⟩, hseg, hvA⟩ := h
  set N := T.toNF with hNdef
  set θ₀ : Fin 7 → ℝ := ![N.a, N.b, N.g, N.d, N.p, N.q, N.r] with hθ₀
  have hx : x = nfShape N.o N.E₁ N.E₂ N.E₃ θ₀ := N.eq_nfShape
  have hxs : nfShape N.o N.E₁ N.E₂ N.E₃ θ₀ = x := hx.symm
  have hshape : Continuous (fun θ => nfShape N.o N.E₁ N.E₂ N.E₃ θ) :=
    continuous_pi fun i => continuous_iff_continuousAt.2 fun θ =>
      tendsto_nfShape (o := fun _ : (Fin 7 → ℝ) => N.o) (E₁ := fun _ => N.E₁)
        (E₂ := fun _ => N.E₂) (E₃ := fun _ => N.E₃) tendsto_const_nhds tendsto_const_nhds
        tendsto_const_nhds tendsto_const_nhds tendsto_id i
  obtain ⟨θs, L, hθs, hL, hPs, hdet, hrest⟩ := exists_seq_restore_ties
    (fun θ => nfShape N.o N.E₁ N.E₂ N.E₃ θ) hshape genPoly16 genPoly16_ne_zero θ₀
    (fun t => (τ t).2) (fun t => fun y => view16 y (τ t).1) (fun t => covView_view16 _)
    (fun t => by simp only [hxs]; exact hτ t) (by simp only [hxs]; exact hind)
  set K : ℕ → Fin 7 → ℝ³ := fun j => mapShape (L j) (nfShape N.o N.E₁ N.E₂ N.E₃ (θs j)) with hKdef
  have hKe : ∀ n, K n = nfShape (L n N.o) (L n N.E₁) (L n N.E₂) (L n N.E₃) (θs n) := fun n =>
    map_nfShape (L n) N.o N.E₁ N.E₂ N.E₃ (θs n)
  have hev : Continuous (fun p : (ℝ³ →L[ℝ] ℝ³) × ℝ³ => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)) := by
    intro i
    have h1 : Tendsto (fun j => nfShape N.o N.E₁ N.E₂ N.E₃ (θs j) i) atTop
        (𝓝 (nfShape N.o N.E₁ N.E₂ N.E₃ θ₀ i)) :=
      ((continuous_apply i).comp hshape |>.tendsto θ₀).comp hθs
    have := (hev.tendsto (1, nfShape N.o N.E₁ N.E₂ N.E₃ θ₀ i)).comp (hL.prodMk_nhds h1)
    rw [hxs] at this
    exact this
  have hineq : ∀ᶠ n in atTop, ∀ k, 0 < ineq16 (θs n) k :=
    eventually_all.mpr fun k =>
      (((continuous_ineq16 k).tendsto θ₀).comp hθs).eventually (lt_mem_nhds (N.ineq k))
  refine ⟨K, hK, Eventually.frequently ?_⟩
  filter_upwards [hineq, eventually_ties hK] with n hn hs
  have hties : ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
    fun w a b hw => hgen (K n) (fun t => hrest n t) w a b hw
  refine ⟨?_, hties⟩
  have hD : det3 (L n N.E₁) (L n N.E₂) (L n N.E₃) ≠ 0 := by
    rw [det3_map, detMap_eq_det, hdet n, one_mul]; exact N.hD
  have hSeg : TieSeg (univ.image (K n)) := by
    refine ⟨fun v hv w hw hvw => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    obtain ⟨j, -, rfl⟩ := mem_image.mp hw
    have hij : i ≠ j := fun e => hvw (by rw [e])
    exact oneTieAt_of_sub T.inj (y := K n) (.inl (i, j))
      (hseg.tie (x i) (mem_image_of_mem x (mem_univ i)) (x j) (mem_image_of_mem x (mem_univ j))
        (T.inj.ne hij)) (fun a b _ => hs (.inl (i, j)) a b)
  have hVA : VA16 (K n) := by
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact oneTieAt_of_sub T.inj (y := K n) (.inr 1)
        (hvA.1 (T.view16_ne_zero _ (by simp))) (fun a b _ => hs (.inr 1) a b)
    · exact oneTieAt_of_sub T.inj (y := K n) (.inr 4)
        (hvA.2 (T.view16_ne_zero _ (by simp))) (fun a b _ => hs (.inr 4) a b)
  have key := cert16_nfShape_tieSeg (L n N.o) (L n N.E₁) (L n N.E₂) (L n N.E₃) (θs n) hD hn
    (hPs n) (by rwa [← hKe]) (by rwa [← hKe])
  rwa [← hKe] at key

/-- **Theorem 19.8 with several independent ties** (`isRupert_type16_limit` with `TwoTie16`). -/
theorem isRupert_type16_limit_ties {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v))
    (h : TwoTie16 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := exists_certSeq16_ties T h
  exact isRupert_of_cert_seq T hnd K hK hc

/-- `isRupert_type16_limit_edge` from any certified sequence (the skeleton's route). -/
theorem isRupert_type16_limit_edge_seq {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v ∈ usedViews16, view16 x v ≠ 0 →
      NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v ∨ EdgeOK16 T v)
    (hs : CertSeq16 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := hs
  exact isRupert_of_cert_seq_edge T hnd K hK hc

/-- **Theorem 19.8 with Proposition 22.2 and §22, from the facets, with ties**: a copy of
`isRupert_type16_limit_facets_edge` whose tie hypothesis is `OneTie16 x ∨ TwoTie16 x`. -/
theorem isRupert_type16_limit_facets_edge' (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (q35 : NoHDNAt (univ.image x) (x 5 - x 3) ∨ Gen35Aff x fA fB)
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 6) (x 3) (x 4) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 5) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 2) (x 4) (x 0) (x 5))
    (hQ : (NoHDNAt (univ.image x) (x 2 - x 0) ∨
        EdgeGenAff x fA fC 0 2 {0, 2, 3, 5} {0, 2, 4} 3 4 6) ∧
      (NoHDNAt (univ.image x) (x 1 - x 6) ∨
        EdgeGenAff x fB fG 6 1 {1, 3, 5, 6} {1, 4, 6} 3 4 0) ∧
      (NoHDNAt (univ.image x) (x 5 - x 1) ∨
        EdgeGenAff x fB fF 1 5 {1, 3, 5, 6} {1, 4, 5} 3 4 0) ∧
      (NoHDNAt (univ.image x) (x 5 - x 2) ∨
        EdgeGenAff x fA fH 2 5 {0, 2, 3, 5} {2, 4, 5} 3 4 6) ∧
      (NoHDNAt (univ.image x) (x 3 - x 0) ∨
        EdgeGenAff x fD fA 0 3 {0, 3, 6} {0, 2, 3, 5} 6 2 4) ∧
      (NoHDNAt (univ.image x) (x 6 - x 3) ∨
        EdgeGenAff x fD fB 3 6 {0, 3, 6} {1, 3, 5, 6} 0 1 4))
    (hV : HDNOrG1Aff (univ.image x) fE fF (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) ∧
      HDNOrG1Aff (univ.image x) fD fG (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) ∧
      HDNOrVtxGenAff (univ.image x) fA fE (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) ∧
      HDNOrG1Aff (univ.image x) fE fH (x 6) (x 4) (x 0) (x 2) (x 4) (x 5) ∧
      HDNOrG1Aff (univ.image x) fD fC (x 6) (x 3) (x 0) (x 2) (x 4) (x 0) ∧
      HDNOrVtxGenAff (univ.image x) fB fE (({1, 3, 5, 6} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x))
    (htie : OneTie16 x ∨ TwoTie16 x) : IsRupert (univ.image x) := by
  let T : Type16 x := ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC,
    Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF, Face16.ofAffine fG hG,
    Face16.ofAffine fH hH⟩
  obtain ⟨q02, q16, q15, q25, q03, q36⟩ := hQ
  have g02 : EdgeGenAff x fA fC 0 2 {0, 2, 3, 5} {0, 2, 4} 3 4 6 → Gen02 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fA hA y).symm)
      (fun y => (Face16.ofAffine_inner fC hC y).symm), h.2⟩
  have g16 : EdgeGenAff x fB fG 6 1 {1, 3, 5, 6} {1, 4, 6} 3 4 0 → Gen16 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fB hB y).symm)
      (fun y => (Face16.ofAffine_inner fG hG y).symm), h.2⟩
  have g15 : EdgeGenAff x fB fF 1 5 {1, 3, 5, 6} {1, 4, 5} 3 4 0 → Gen15 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fB hB y).symm)
      (fun y => (Face16.ofAffine_inner fF hF y).symm), h.2⟩
  have g25 : EdgeGenAff x fA fH 2 5 {0, 2, 3, 5} {2, 4, 5} 3 4 6 → Gen25 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fA hA y).symm)
      (fun y => (Face16.ofAffine_inner fH hH y).symm), h.2⟩
  have g03 : EdgeGenAff x fD fA 0 3 {0, 3, 6} {0, 2, 3, 5} 6 2 4 → Gen03 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fD hD y).symm)
      (fun y => (Face16.ofAffine_inner fA hA y).symm), h.2⟩
  have g36 : EdgeGenAff x fD fB 3 6 {0, 3, 6} {1, 3, 5, 6} 0 1 4 → Gen36 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fD hD y).symm)
      (fun y => (Face16.ofAffine_inner fB hB y).symm), h.2⟩
  have g35 : Gen35Aff x fA fB → Gen35 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fB hB y).symm)
      (fun y => (Face16.ofAffine_inner fA hA y).symm), h.2⟩
  refine isRupert_type16_limit_edge_seq T (fun v hused hv => ?_)
    (htie.elim (fun h => exists_certSeq16 T h) (fun h => exists_certSeq16_ties T h))
  rcases v with ⟨i, j⟩ | t
  · rcases usedSeg16_cases i j hused with p | p | p | p | p | p | p | p | p | p
    · exact tri_alt16 T 1 p hEd.1
    · exact tri_alt16 T 2 p hEd.2.1
    · exact tri_alt16 T 3 p hEd.2.2
    · exact quad_alt16 T p q02 fun h => Or.inl ⟨p, g02 h⟩
    · exact quad_alt16 T p q16 fun h =>
        Or.inr (Or.inl ⟨p.trans (Finset.pair_comm _ _), g16 h⟩)
    · exact quad_alt16 T p q15 fun h => Or.inr (Or.inr (Or.inl ⟨p, g15 h⟩))
    · exact quad_alt16 T p q25 fun h => Or.inr (Or.inr (Or.inr (Or.inl ⟨p, g25 h⟩)))
    · exact quad_alt16 T p q03 fun h =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, g03 h⟩))))
    · exact quad_alt16 T p q36 fun h =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, g36 h⟩)))))
    · exact quad_alt16 T p q35 fun h =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, g35 h⟩)))))
  · obtain ⟨V1, V2, V3, V4, V5, V6⟩ := hV
    fin_cases t
    · rcases V1 _ hv (affine_planeLine_perp fE hE (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fF hF (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inl rfl, h⟩)
    · rcases V2 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fG hG (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), h⟩)
    · rcases V3 _ hv (affine_planeLine_perp fA hA (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fE hE (by decide) (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h _ (fun y => (Face16.ofAffine_inner fA hA y).symm)⟩))
    · rcases V4 _ hv (affine_planeLine_perp fE hE (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fH hH (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), h⟩)
    · rcases V5 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fC hC (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr rfl)), h⟩)
    · rcases V6 _ hv (affine_planeLine_perp fB hB (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fE hE (by decide) (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h _ (fun y => (Face16.ofAffine_inner fB hB y).symm)⟩))

end Minimality

theorem not_type16_of_isNopert_ties (x : Fin 7 → ℝ³) (h : IsNopert (Finset.univ.image x))
    (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (h35 : Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 3) ∨ Minimality.Gen35Aff x fA fB)
    (hEd : Minimality.HDNOrG1Edge (Finset.univ.image x) (x 0) (x 6) (x 3) (x 4) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 1) (x 4) (x 5) (x 6) ∧
      Minimality.HDNOrG1Edge (Finset.univ.image x) (x 2) (x 4) (x 0) (x 5))
    (hQ : (Minimality.NoHDNAt (Finset.univ.image x) (x 2 - x 0) ∨
        Minimality.EdgeGenAff x fA fC 0 2 {0, 2, 3, 5} {0, 2, 4} 3 4 6) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 1 - x 6) ∨
        Minimality.EdgeGenAff x fB fG 6 1 {1, 3, 5, 6} {1, 4, 6} 3 4 0) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 1) ∨
        Minimality.EdgeGenAff x fB fF 1 5 {1, 3, 5, 6} {1, 4, 5} 3 4 0) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 5 - x 2) ∨
        Minimality.EdgeGenAff x fA fH 2 5 {0, 2, 3, 5} {2, 4, 5} 3 4 6) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 3 - x 0) ∨
        Minimality.EdgeGenAff x fD fA 0 3 {0, 3, 6} {0, 2, 3, 5} 6 2 4) ∧
      (Minimality.NoHDNAt (Finset.univ.image x) (x 6 - x 3) ∨
        Minimality.EdgeGenAff x fD fB 3 6 {0, 3, 6} {1, 3, 5, 6} 0 1 4))
    (hV : Minimality.HDNOrG1Aff (Finset.univ.image x) fE fF (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fG (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) ∧
      Minimality.HDNOrVtxGenAff (Finset.univ.image x) fA fE
        (({0, 2, 3, 5} : Finset (Fin 7)).image x) (({0, 4, 6} : Finset (Fin 7)).image x) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fE fH (x 6) (x 4) (x 0) (x 2) (x 4) (x 5) ∧
      Minimality.HDNOrG1Aff (Finset.univ.image x) fD fC (x 6) (x 3) (x 0) (x 2) (x 4) (x 0) ∧
      Minimality.HDNOrVtxGenAff (Finset.univ.image x) fB fE
        (({1, 3, 5, 6} : Finset (Fin 7)).image x) (({0, 4, 6} : Finset (Fin 7)).image x))
    (htie : Minimality.OneTie16 x ∨ Minimality.TwoTie16 x) : False :=
  h.2 (Minimality.isRupert_type16_limit_facets_edge' x hx fA fB fC fD fE fF fG fH hA hB hC hD hE
    hF hG hH h35 hEd hQ hV htie)
