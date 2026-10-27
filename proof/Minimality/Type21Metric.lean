module

public import Minimality.Type21Limit
public import Minimality.Type16Metric

@[expose] public section

/-!
# Type 21 with several ties: linear images and the metric bridge (`FEWER-FACES-PROOFS.md` §24.3)

The analogue of `Type16Metric.lean` for type 21.  The cover at a generic normal-form shape
(`cert21_of_generic`) needs the type's sign conditions (polynomial in the parameters, `genPoly21`),
the negativity of the facet functions, and ties only at the named views; a linear image `M ∘ y` of
a normal-form shape is a normal-form shape with the same parameters, its facet functions are those
of `y` rescaled by `det M`, and its ties are broken by a generic small perturbation of `M`.

* `view21_map`, `NoTies21`, `cert21_nfShape21`: the named views are equivariant; a normal-form
  shape without ties at the named views and with its facet functions negative is certified.
* `exists_certSeq21_map`: for every invertible `M`, `M ∘ x` is a pointwise limit of certified
  shapes (**the cover is affine-invariant**).
* `Q21`, `TwoView21`, `isRupert_type21_twoView`: Theorem 24.3 for type 21 from the bridge
  `metricFree_of_cover`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Named views under linear maps -/

theorem view21_map (M : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    ∃ c : ℝ, (c = 1 ∨ c = detMap M) ∧ view21 (fun l => M (y l)) v = c • M (view21 y v) := by
  rcases v with ⟨i, j⟩ | t
  · exact ⟨1, Or.inl rfl, by rw [one_smul]; simp [view21]⟩
  · exact ⟨detMap M, Or.inr rfl, planeLine_map M _ _ _ _ _ _⟩

theorem map_nfShape21 (M : ℝ³ →L[ℝ] ℝ³) (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) :
    (fun i => M (nfShape21 o E₁ E₂ E₃ θ i)) = nfShape21 (M o) (M E₁) (M E₂) (M E₃) θ := by
  funext i; exact map_nfP M o E₁ E₂ E₃ _ _ _

/-- The facet functions of a linear image are those of the shape, rescaled by `det M`. -/
theorem fac21_map (N : ℝ³ →L[ℝ] ℝ³) (hN : detMap N ≠ 0) (κ : Fin 8 → ℝ) (y : Fin 7 → ℝ³)
    (f : Fin 8) (i : Fin 7) :
    fac21 (fun f => κ f / detMap N) (fun j => N (y j)) f (N (y i)) = fac21 κ y f (y i) := by
  simp only [fac21, detAff_apply]
  rw [← map_sub, ← map_sub, ← map_sub, det3_map]
  field_simp

/-! ### Shapes without ties are certified -/

/-- No two points of `y` have equal depth along a nonzero named view. -/
def NoTies21 (y : Fin 7 → ℝ³) : Prop :=
  ∀ v a b, a ≠ b → view21 y v ≠ 0 → ⟪y a - y b, view21 y v⟫ ≠ 0

theorem oneTieAt_of_noTies21 {y : Fin 7 → ℝ³} (h : NoTies21 y) (v : (Fin 7 × Fin 7) ⊕ Fin 8)
    (hv : view21 y v ≠ 0) : OneTieAt (univ.image y) (view21 y v) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  have hab : a ≠ b := fun h => hst (by rw [h])
  exact absurd (by rw [inner_sub_left, e1, sub_self]) (h v a b hab hv)

theorem noTieAt_of_noTies21 {y : Fin 7 → ℝ³} (h : NoTies21 y) (v : (Fin 7 × Fin 7) ⊕ Fin 8)
    (hv : view21 y v ≠ 0) : NoTieAt (univ.image y) (view21 y v) := by
  intro s hs t ht hst e
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  have hab : a ≠ b := fun h => hst (by rw [h])
  exact h v a b hab hv (by rw [inner_sub_left, e, sub_self])

/-- **A normal-form shape of type 21 without ties at the named views, with negative facet
functions, is certified** (`cert21_of_generic`, whose tie hypotheses hold vacuously). -/
theorem cert21_nfShape21 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (hD : det3 E₁ E₂ E₃ ≠ 0)
    (hg : gen21 θ ≠ 0) {κ : Fin 8 → ℝ} (hκ : ∀ f, κ f ≠ 0)
    (hneg : ∀ f i, i ∉ facS f → fac21 κ (nfShape21 o E₁ E₂ E₃ θ) f (nfShape21 o E₁ E₂ E₃ θ i) < 0)
    (hnt : NoTies21 (nfShape21 o E₁ E₂ E₃ θ)) (hvtx : ∀ t, vtxView21 (nfShape21 o E₁ E₂ E₃ θ) t ≠ 0)
    (hinj : Function.Injective (nfShape21 o E₁ E₂ E₃ θ)) : Cert21 (nfShape21 o E₁ E₂ E₃ θ) := by
  set y := nfShape21 o E₁ E₂ E₃ θ with hy
  have hgt : TieSeg (univ.image y) := by
    refine ⟨fun v hv w hw hvw => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    obtain ⟨j, -, rfl⟩ := mem_image.mp hw
    exact oneTieAt_of_noTies21 hnt (.inl (i, j)) (sub_ne_zero.mpr (Ne.symm hvw))
  have hY : ∀ a b : Fin 7, a ≠ b → NoTieAt (univ.image y) (y a - y b) := fun a b hab =>
    noTieAt_of_noTies21 hnt (.inl (b, a)) (sub_ne_zero.mpr (hinj.ne hab))
  refine (cert21_of_generic (y := y) hy hD hg hκ hneg hgt
    (fun t => oneTieAt_of_noTies21 hnt (.inr t) (hvtx t))
    ⟨fun _ => hY 0 4 (by decide), fun _ => hY 4 0 (by decide), fun _ => hY 5 3 (by decide),
      fun _ => hY 3 5 (by decide)⟩
    ⟨Or.inl (noTieAt_of_noTies21 hnt (.inr 1) (hvtx 1)),
      Or.inl (noTieAt_of_noTies21 hnt (.inr 0) (hvtx 0)),
      Or.inl (noTieAt_of_noTies21 hnt (.inr 3) (hvtx 3)),
      Or.inl (noTieAt_of_noTies21 hnt (.inr 2) (hvtx 2))⟩).toCert21

/-- **The cover is affine-invariant** (bridge input for type 21): for an invertible linear map `M`,
the shape `M ∘ x` of a type-21 shape is a pointwise limit of certified shapes
`((1 + t S) M) ∘ y_s`, with `y_s` normal-form shapes off the special positions of the cover
(`genPoly21`) and `t S` a small generic perturbation of the metric that leaves no tie at the named
views. -/
theorem exists_certSeq21_map {x : Fin 7 → ℝ³} (T : Facets21 x) (M : ℝ³ →L[ℝ] ℝ³)
    (hMinj : ∀ a, M a = 0 → a = 0)
    (hD : det3 (M (x 0 - x 2)) (M (x 3 - x 2)) (M (x 6 - x 2)) ≠ 0) :
    ∃ Y : ℕ → Fin 7 → ℝ³, (∀ i, Tendsto (fun s => Y s i) atTop (𝓝 (M (x i)))) ∧
      ∀ᶠ s in atTop, Cert21 (Y s) := by
  classical
  set θ₀ := theta21 x with hθ₀
  have hx : x = nfShape21 (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) θ₀ := T.eq_nfShape
  set o := x 2 with ho
  set E₁ := x 0 - x 2 with hE₁
  set E₂ := x 3 - x 2 with hE₂
  set E₃ := x 6 - x 2 with hE₃
  obtain ⟨θs, hθs, hgen⟩ := exists_seq_eval_ne_zero genPoly21_ne_zero θ₀
  set Y0 : ℕ → Fin 7 → ℝ³ := fun s => nfShape21 o E₁ E₂ E₃ (θs s) with hY0
  have hY0t : ∀ i, Tendsto (fun s => Y0 s i) atTop (𝓝 (x i)) := by
    intro m
    have := tendsto_nfShape21 (o := fun _ : ℕ => o) (E₁ := fun _ => E₁) (E₂ := fun _ => E₂)
      (E₃ := fun _ => E₃) tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
      tendsto_const_nhds hθs m
    rw [← hx] at this; exact this
  obtain ⟨κ, hκ, hneg⟩ := T.exists_kappa
  have hfac : ∀ᶠ s in atTop, ∀ f i, i ∉ facS f → fac21 κ (Y0 s) f (Y0 s i) < 0 := by
    refine eventually_all.mpr fun f => eventually_all.mpr fun i => ?_
    by_cases hi : i ∈ facS f
    · exact Eventually.of_forall fun _ h => absurd hi h
    · have hlim : Tendsto (fun s => fac21 κ (Y0 s) f (Y0 s i)) atTop (𝓝 (fac21 κ x f (x i))) := by
        simp only [fac21, detAff_apply]
        exact (Tendsto.det3' ((hY0t _).sub (hY0t _)) ((hY0t _).sub (hY0t _))
          ((hY0t _).sub (hY0t _))).const_mul _
      exact (hlim.eventually (gt_mem_nhds (hneg f i hi))).mono fun n hn _ => hn
  have hvtx : ∀ᶠ s in atTop, ∀ t, vtxView21 (Y0 s) t ≠ 0 :=
    eventually_all.mpr fun t =>
      (tendsto_view21 hY0t (.inr t)).eventually_ne (T.vtxView21_ne_zero t)
  have hinj : ∀ s, Function.Injective (Y0 s) := fun s =>
    nfShape21_inj T.det_ne (by have := hgen s; rwa [eval_genPoly21] at this)
  -- the perturbations
  have key : ∀ s : ℕ, ∃ (S : ℝ³ →L[ℝ] ℝ³) (t : ℝ), 0 < t ∧ t * ‖S‖ < 1 / ((s : ℝ) + 1) ∧
      (((∀ f i, i ∉ facS f → fac21 κ (Y0 s) f (Y0 s i) < 0) ∧ ∀ t', vtxView21 (Y0 s) t' ≠ 0) →
        Cert21 (fun i => ((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) (Y0 s i))) := by
    intro s
    have hs0 : (0 : ℝ) < 1 / ((s : ℝ) + 1) := by positivity
    by_cases hn : (∀ f i, i ∉ facS f → fac21 κ (Y0 s) f (Y0 s i) < 0) ∧
        ∀ t', vtxView21 (Y0 s) t' ≠ 0
    · let ι := {p : ((Fin 7 × Fin 7) ⊕ Fin 8) × Fin 7 × Fin 7 //
        p.2.1 ≠ p.2.2 ∧ view21 (Y0 s) p.1 ≠ 0}
      have ha : ∀ p : ι, M (Y0 s p.1.2.1 - Y0 s p.1.2.2) ≠ 0 := fun p h =>
        sub_ne_zero.mpr ((hinj s).ne p.2.1) (hMinj _ h)
      have hb : ∀ p : ι, M (view21 (Y0 s) p.1.1) ≠ 0 := fun p h => p.2.2 (hMinj _ h)
      obtain ⟨S, hS⟩ := exists_noTie_dir (fun p : ι => M (Y0 s p.1.2.1 - Y0 s p.1.2.2))
        (fun p : ι => M (view21 (Y0 s) p.1.1)) ha hb
      have hT : ∀ v : ℝ³, Tendsto (fun t : ℝ => M v + t • S (M v)) (𝓝 0) (𝓝 (M v)) := by
        intro v
        have : Continuous fun t : ℝ => M v + t • S (M v) := by fun_prop
        simpa using this.tendsto 0
      have hdet : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          det3 (((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) E₁)
            (((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) E₂)
            (((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) E₃) ≠ 0 := by
        have := Tendsto.det3' (hT E₁) (hT E₂) (hT E₃)
        exact ((this.eventually_ne hD).filter_mono nhdsWithin_le_nhds).mono fun t ht => by
          simpa using ht
      have hsz : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * ‖S‖ < 1 / ((s : ℝ) + 1) := by
        have hc : Continuous fun t : ℝ => t * ‖S‖ := by fun_prop
        exact (hc.continuousAt.eventually (gt_mem_nhds (by simpa using hs0))).filter_mono
          nhdsWithin_le_nhds
      have hvt : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ t' : Fin 8,
          M (vtxView21 (Y0 s) t') + t • S (M (vtxView21 (Y0 s) t')) ≠ 0 :=
        eventually_all.2 fun t' =>
          ((hT (vtxView21 (Y0 s) t')).eventually_ne
            (fun h => hMinj _ h |> hn.2 t')).filter_mono nhdsWithin_le_nhds
      have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := self_mem_nhdsWithin
      obtain ⟨t, ht0, htd, hts, htv, htS⟩ :=
        (hpos.and (hdet.and (hsz.and (hvt.and hS)))).exists
      refine ⟨S, t, ht0, hts, fun _ => ?_⟩
      set Nt : ℝ³ →L[ℝ] ℝ³ := (ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M with hNt
      have hNtv : ∀ v, Nt v = M v + t • S (M v) := fun v => by simp [hNt]
      have hDt : detMap Nt ≠ 0 := by
        intro h0
        apply htd
        rw [det3_map, h0, zero_mul]
      have hg : gen21 (θs s) ≠ 0 := by have := hgen s; rwa [eval_genPoly21] at this
      rw [show (fun i => Nt (Y0 s i)) = nfShape21 (Nt o) (Nt E₁) (Nt E₂) (Nt E₃) (θs s) from
        map_nfShape21 Nt o E₁ E₂ E₃ (θs s)]
      refine cert21_nfShape21 _ _ _ _ _ htd hg (κ := fun f => κ f / detMap Nt)
        (fun f => div_ne_zero (hκ f) hDt) ?_ ?_ ?_ ?_
      · intro f i hi
        rw [← map_nfShape21 Nt o E₁ E₂ E₃ (θs s), fac21_map Nt hDt κ (Y0 s) f i]
        exact hn.1 f i hi
      · rw [← map_nfShape21 Nt o E₁ E₂ E₃ (θs s)]
        intro v a b hab hv
        obtain ⟨c, -, hc⟩ := view21_map Nt (Y0 s) v
        rw [hc] at hv ⊢
        have hc0 : c ≠ 0 := left_ne_zero_of_smul hv
        have hv0 : view21 (Y0 s) v ≠ 0 := fun h => hv (by rw [h, map_zero, smul_zero])
        have := htS ⟨(v, a, b), hab, hv0⟩
        have e1 : Nt (Y0 s a) - Nt (Y0 s b) =
            M (Y0 s a - Y0 s b) + t • S (M (Y0 s a - Y0 s b)) := by
          rw [← map_sub, hNtv]
        rw [real_inner_smul_right, e1, hNtv (view21 (Y0 s) v)]
        exact mul_ne_zero hc0 this
      · rw [← map_nfShape21 Nt o E₁ E₂ E₃ (θs s)]
        intro t'
        have e : vtxView21 (fun i => Nt (Y0 s i)) t' = detMap Nt • Nt (vtxView21 (Y0 s) t') :=
          planeLine_map Nt _ _ _ _ _ _
        rw [e, hNtv]
        exact smul_ne_zero hDt (htv t')
      · rw [← map_nfShape21 Nt o E₁ E₂ E₃ (θs s)]
        intro i j hij
        have h0 : M (Y0 s i - Y0 s j) + t • S (M (Y0 s i - Y0 s j)) = 0 := by
          rw [← hNtv, map_sub]; exact sub_eq_zero.mpr hij
        set w : ℝ³ := M (Y0 s i - Y0 s j) with hw
        have hlt : t * ‖S‖ < 1 := lt_of_lt_of_le hts (by
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
          linarith)
        have e : w = -(t • S w) := eq_neg_of_add_eq_zero_left h0
        have h1 : ‖w‖ ≤ t * ‖S‖ * ‖w‖ := by
          calc ‖w‖ = ‖t • S w‖ := by
                have := congrArg norm e
                rwa [norm_neg] at this
            _ = t * ‖S w‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
            _ ≤ t * (‖S‖ * ‖w‖) := mul_le_mul_of_nonneg_left (S.le_opNorm _) ht0.le
            _ = t * ‖S‖ * ‖w‖ := by ring
        have h2 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
        exact (hinj s) (sub_eq_zero.mp (hMinj _ (norm_eq_zero.mp h2)))
    · exact ⟨0, 1, one_pos, by simpa using hs0, fun h => absurd h hn⟩
  choose S t ht0 hts hcert using key
  refine ⟨fun s i => ((ContinuousLinearMap.id ℝ ℝ³ + t s • S s).comp M) (Y0 s i), fun i => ?_,
    (hfac.and hvtx).mono fun s hs => hcert s hs⟩
  have h1 : Tendsto (fun s => M (Y0 s i)) atTop (𝓝 (M (x i))) :=
    (M.continuous.tendsto _).comp (hY0t i)
  have h2 : Tendsto (fun s => t s • S s (M (Y0 s i))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun s : ℕ => 1 / ((s : ℝ) + 1) * ‖M (Y0 s i)‖) atTop (𝓝 (0 * ‖M (x i)‖)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul (h1.norm)
    rw [zero_mul] at hb
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hb
    calc ‖t s • S s (M (Y0 s i))‖ = t s * ‖S s (M (Y0 s i))‖ := by
          rw [norm_smul, Real.norm_of_nonneg (ht0 s).le]
      _ ≤ t s * (‖S s‖ * ‖M (Y0 s i)‖) :=
          mul_le_mul_of_nonneg_left ((S s).le_opNorm _) (ht0 s).le
      _ = (t s * ‖S s‖) * ‖M (Y0 s i)‖ := by ring
      _ ≤ 1 / ((s : ℝ) + 1) * ‖M (Y0 s i)‖ :=
          mul_le_mul_of_nonneg_right (hts s).le (norm_nonneg _)
  have := h1.add h2
  rw [add_zero] at this
  simpa using this

/-! ### The certificates of type 21 as a finite family -/

/-- A labelled certificate index at a used view: a named view of the cover (`UsedV21`), a sign, and
a labelled rim (`CertL21`). -/
abbrev Q21 : Type :=
  {q : ((Fin 7 × Fin 7) ⊕ Fin 8) × Bool × Rim16 // UsedV21 q.1}

/-- The named view of a certificate index. -/
def Q21.v (q : Q21) : (Fin 7 × Fin 7) ⊕ Fin 8 := q.1.1

/-- The sign of a certificate index. -/
def Q21.e (q : Q21) : Bool := q.1.2.1

/-- The number of corners of the rim of `q`. -/
def Q21.K (q : Q21) : ℕ := (Lab16 q.1.2.2).1

/-- The labels of the rim of `q`. -/
def Q21.lab (q : Q21) : ZMod q.K → Fin 7 := (Lab16 q.1.2.2).2

/-- The view of `q` as a function of the shape. -/
noncomputable def Q21.vw (q : Q21) (y : Fin 7 → ℝ³) : ℝ³ := sgnB q.e • view21 y q.v

theorem Q21.K_three (q : Q21) : 3 ≤ q.K := by
  obtain ⟨⟨v, e, L | L | L⟩, hq⟩ := q <;> simp [Q21.K, Lab16]

instance (q : Q21) : NeZero q.K :=
  ⟨by have := q.K_three; omega⟩

theorem certL21_iff (y : Fin 7 → ℝ³) (q : Q21) :
    CertL21 y q.v q.e q.1.2.2 ↔ RimCertAt y (q.vw y) q.lab := by
  obtain ⟨⟨v, e, L | L | L⟩, hq⟩ := q <;> exact Iff.rfl

theorem Q21.vw_eq_zero {x : Fin 7 → ℝ³} (T : Facets21 x) (q : Q21) (h : q.vw x = 0)
    (y : Fin 7 → ℝ³) : q.vw y = 0 := by
  have hs := sgnB_ne_zero q.e
  simp only [Q21.vw] at h ⊢
  have h0 : view21 x q.v = 0 := by
    rcases smul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hs
    · exact h1
  rcases hv : q.v with ⟨i, j⟩ | t
  · rw [hv] at h0
    by_cases hij : i = j
    · subst hij; simp [view21]
    · exact absurd h0 (T.view21_ne_zero (.inl (i, j)) (fun l e' => hij (by
        simp only [Sum.inl.injEq, Prod.mk.injEq] at e'; rw [e'.1, e'.2])))
  · rw [hv] at h0
    exact absurd h0 (T.view21_ne_zero (.inr t) (fun l e' => by cases e'))

/-- The certificate `q` has a rim that is a rotation or reflection of the rim `lab₁`, at a
multiple of the view `u₁`. -/
def RimMatch21 (x : Fin 7 → ℝ³) (u₁ : ℝ³) {k₁ : ℕ} (lab₁ : ZMod k₁ → Fin 7) (q : Q21) : Prop :=
  (∃ lam : ℝ, lam ≠ 0 ∧ q.vw x = lam • u₁) ∧ q.K = k₁ ∧ ∃ r : ℤ,
    (∀ n : ℤ, q.lab (n : ZMod q.K) = lab₁ ((n + r : ℤ) : ZMod k₁)) ∨
    (∀ n : ℤ, q.lab (n : ZMod q.K) = lab₁ ((r - n : ℤ) : ZMod k₁))

theorem RimMatch21.pair {x : Fin 7 → ℝ³} {u₁ : ℝ³} {k₁ : ℕ} [NeZero k₁] {lab₁ : ZMod k₁ → Fin 7}
    {q : Q21} (h : RimMatch21 x u₁ lab₁ q) :
    ∃ lam : ℝ, q.vw x = lam • u₁ ∧ ∀ w : ℝ³,
      (Function.Injective (fun i => ⟪x (lab₁ i), w⟫) →
        Function.Injective (fun i => ⟪x (q.lab i), lam • w⟫)) ∧
      (IsRobustUnimodal (fun i => ⟪x (q.lab i), lam • w⟫) →
        IsRobustUnimodal (fun i => ⟪x (lab₁ i), w⟫)) := by
  obtain ⟨⟨lam, hlam, hv⟩, hk, r, hr⟩ := h
  refine ⟨lam, hv, ?_⟩
  subst hk
  intro w
  refine equiv_aux (fun i => ⟪x (q.lab i), lam • w⟫) (fun i => ⟪x (lab₁ i), w⟫) r lam hlam ?_
  rcases hr with h | h
  · left; intro n; simp only [h, real_inner_smul_right]
  · right; intro n; simp only [h, real_inner_smul_right]

/-! ### Two views with ties -/

/-- **Two tilt tests at certificates of the cover** (Theorem 24.3 for type 21).  `q₁, q₂` are
labelled certificate indices (a named view, a sign, a labelled rim of 3, 4 or 5 corners) whose
rims `x ∘ q.lab` at the views `q.vw x` are tilt tests (`TiltTest`: the silhouette at the tilted
views is a cyclic subsequence of the rim, for a nonempty open cone `Θ` of tilts), the views are
not proportional, and the cones are compatible (`compat_of_signs`) if the views are orthogonal.
Every other certificate of the cover that survives in the limit (`WeakRim`: distinct labels, all
points weakly left of its polygon, labels weakly counterclockwise) has no horizontal double normal
at its limit view and distinct depths of its labels.  Rotations and reflections of the two rims at
the same views belong to the tests. -/
def TwoView21 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (q₁ q₂ : Q21) (Θ₁ Θ₂ : Set ℝ³) (k₁ k₂ : ℕ) (_ : NeZero k₁) (_ : NeZero k₂)
    (σ₁ : ZMod k₁ → ZMod q₁.K) (σ₂ : ZMod k₂ → ZMod q₂.K),
    TiltTest (univ.image x) (q₁.vw x) (fun i => x (q₁.lab i)) σ₁ Θ₁ ∧
    TiltTest (univ.image x) (q₂.vw x) (fun i => x (q₂.lab i)) σ₂ Θ₂ ∧
    (∀ t : ℝ, q₂.vw x ≠ t • q₁.vw x) ∧
    (⟪q₁.vw x, q₂.vw x⟫ = 0 → ∃ d ∈ Θ₁, ∃ d' ∈ Θ₂, ⟪q₂.vw x, d⟫ = ⟪q₁.vw x, d'⟫) ∧
    ∀ q : Q21, ¬ RimMatch21 x (q₁.vw x) q₁.lab q → ¬ RimMatch21 x (q₂.vw x) q₂.lab q →
      q.vw x ≠ 0 → Function.Injective q.lab → WeakRim x (q.vw x) q.lab →
        NoHDNAt (univ.image x) (q.vw x) ∧
          ∀ i j, q.lab i ≠ q.lab j → ⟪x (q.lab i) - x (q.lab j), q.vw x⟫ ≠ 0

/-- **Type 21 with two ties at two certificates** (Theorem 24.3 with the cover, the bridge
`metricFree_of_cover`).  A type-21 shape with `TwoView21` is Rupert: the two tilt tests are
metric-free along the curve `I + (ε/2) H` because the cover is affine-invariant
(`exists_certSeq21_map`), or else the limit lemma makes the shape Rupert directly. -/
theorem isRupert_type21_twoView {x : Fin 7 → ℝ³} (T : Facets21 x) (P : TwoView21 x) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨q₁, q₂, Θ, Θ', k₁, k₂, i₁, i₂, σ, σ', T1, T2, hind, hcompat, hO⟩ := P
  set u : ℝ³ := q₁.vw x with hu
  set u' : ℝ³ := q₂.vw x with hu'
  set X : ZMod q₁.K → ℝ³ := fun i => x (q₁.lab i) with hX
  set X' : ZMod q₂.K → ℝ³ := fun i => x (q₂.lab i) with hX'
  obtain ⟨d, hdΘ, d', hdΘ', hcoup, hg, hg'⟩ := exists_good_pair T1 T2 hcompat
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
  obtain ⟨H, hsymm, hHu, hHu'⟩ := exists_symm_clm (A := d + c • u) (B := d') T1.ne_zero hind (by
    simp only [inner_add_right, real_inner_smul_right]
    rw [← real_inner_comm d u'] at hrel
    rw [real_inner_comm u u']
    linarith)
  -- the curve of metrics
  set M : ℝ → ℝ³ →L[ℝ] ℝ³ := fun ε => ContinuousLinearMap.id ℝ ℝ³ + (ε / 2) • H with hM
  set Gm : ℝ → ℝ³ →L[ℝ] ℝ³ := fun ε => (M ε).comp (M ε) with hGm
  have hMv : ∀ ε v, M ε v = v + (ε / 2) • H v := fun ε v => by simp [hM]
  have hGv : ∀ ε v, Gm ε v = M ε (M ε v) := fun ε v => rfl
  have hMG : ∀ ε a b, ⟪M ε a, M ε b⟫ = ⟪a, Gm ε b⟫ := by
    intro ε a b
    rw [hMv, hMv, hGv, hMv, hMv]
    exact curve_inner H hsymm ε a b
  have hMt : ∀ v : ℝ³, Tendsto (fun ε => M ε v) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    intro v
    have hc' : Continuous fun ε : ℝ => v + (ε / 2) • H v := by fun_prop
    simpa [hMv] using hc'.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  have hdetpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < detMap (M ε) := by
    have h := Tendsto.det3' (hMt (EuclideanSpace.single 0 1)) (hMt (EuclideanSpace.single 1 1))
      (hMt (EuclideanSpace.single 2 1))
    have h1 : det3 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
        (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
        = 1 := detMap_one
    rw [h1] at h
    exact h.eventually (lt_mem_nhds one_pos)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε / 2 * ‖H‖ < 1 := by
    have hc' : Continuous fun ε : ℝ => ε / 2 * ‖H‖ := by fun_prop
    exact (hc'.continuousAt.eventually (gt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds
  have hMinj : ∀ ε, ε / 2 * ‖H‖ < 1 → 0 < ε → ∀ a, M ε a = 0 → a = 0 := by
    intro ε hε hε0 a ha
    rw [hMv] at ha
    have e : a = -((ε / 2) • H a) := eq_neg_of_add_eq_zero_left ha
    have h1 : ‖a‖ ≤ ε / 2 * ‖H‖ * ‖a‖ := by
      calc ‖a‖ = ‖(ε / 2) • H a‖ := by
            have := congrArg norm e
            rwa [norm_neg] at this
        _ = ε / 2 * ‖H a‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        _ ≤ ε / 2 * (‖H‖ * ‖a‖) := mul_le_mul_of_nonneg_left (H.le_opNorm a) (by positivity)
        _ = ε / 2 * ‖H‖ * ‖a‖ := by ring
    have : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
    exact norm_eq_zero.mp this
  -- the generic bridge
  have hmain := metricFree_of_cover x T.noSeg ⟨2, 0, 3, 6, T.det_ne⟩ (Q := Q21) Q21.K Q21.lab
    Q21.vw (fun q h y => Q21.vw_eq_zero T q h y)
    (fun q z ι l xs h => (tendsto_view21 h q.v).const_smul _) M Gm hMG (fun i => hMt (x i))
    (by
      have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε := self_mem_nhdsWithin
      filter_upwards [hdetpos, hsmall, hpos] with ε hd hs hε0
      obtain ⟨Y, hY, hc'⟩ := exists_certSeq21_map T (M ε) (hMinj ε hs hε0) (by
        rw [det3_map]; exact mul_ne_zero hd.ne' T.det_ne)
      refine ⟨Y, hY, (hc'.frequently).mono fun s hs' => ?_⟩
      obtain ⟨v, e, L, hv, hL⟩ := CertP21.exists_certL hs'
      exact ⟨⟨(v, e, L), hv⟩, (certL21_iff (Y s) ⟨(v, e, L), hv⟩).1 hL⟩)
    (by
      filter_upwards [hdetpos] with ε hd q
      obtain ⟨c0, hc0, hv⟩ := view21_map (M ε) x q.v
      have hc0' : 0 < c0 := by
        rcases hc0 with rfl | rfl
        · exact one_pos
        · exact hd
      refine ⟨c0, hc0', ?_⟩
      simp only [Q21.vw, hv, map_smul, smul_comm (sgnB q.e) c0])
    (k₁ := q₁.K) (k₂ := q₂.K) q₁.K_three q₂.K_three X X' u u' (fun ε => u + ε • (d + c • u))
    (fun ε => u' + ε • d') (RimMatch21 x u q₁.lab) (RimMatch21 x u' q₂.lab)
    (fun q h => h.pair) (fun q h => h.pair)
    (by
      have hGu : ∀ ε, Gm ε u = u + ε • (d + c • u) + ε ^ 2 • ((1 / 4 : ℝ) • H (d + c • u)) := by
        intro ε
        rw [hGv, hMv, hMv, map_add, map_smul, hHu]
        module
      simp only [hGu]
      exact eventually_order_tilt X u (d + c • u) ((1 / 4 : ℝ) • H (d + c • u)) hgood)
    (by
      have hGu : ∀ ε, Gm ε u' = u' + ε • d' + ε ^ 2 • ((1 / 4 : ℝ) • H d') := by
        intro ε
        rw [hGv, hMv, hMv, map_add, map_smul, hHu']
        module
      simp only [hGu]
      exact eventually_order_tilt X' u' d' ((1 / 4 : ℝ) • H d') hg')
    hO
  rcases hmain with hR | hMF
  · exact hR
  have hall := hMF.and ((eventually_injective_depth hgood).and (eventually_injective_depth hg'))
  have hall' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsCyclicUnimodal (fun i => ⟪X i, u + ε • (d + c • u)⟫) ∨
        IsCyclicUnimodal (fun i => ⟪X' i, u' + ε • d'⟫) :=
    hall.mono fun _ ⟨h1, h2, h3⟩ => h1 h2 h3
  rcases frequently_or_distrib.mp hall'.frequently with h | h
  · exact T1.isRupert_of_freq hdΘ (frequently_unimodal_tilt X u d c h)
  · exact T2.isRupert_of_freq hdΘ' h


/-- **Theorem 24.3 for type 21 from the facets**: seven points labelled so that `014, 015, 0256,
046, 134, 135, 2346, 235` are facets (functionals negative off them) with `TwoView21` are
Rupert. -/
theorem isRupert_type21_twoView_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    (P : TwoView21 x) : IsRupert (univ.image x) :=
  isRupert_type21_twoView (Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH)
    P

end Minimality

end
