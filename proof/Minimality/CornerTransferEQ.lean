module

public import Mathlib
public import Minimality.RimCellConv
public import Minimality.CornerEQCert
public import Minimality.CornerTransfer
public import Minimality.Type21SilB

/-!
# The EQ adapter: an EQ certificate gives a corner leaf at its own apex

Source: `notes/LIFT-TRANSFER-DESIGN.md`, build step 6.  Namespace `Minimality.CornerEQ`.

An EQ certificate `L` over the shape `Y` (apex `0 ∈ Y`, frame `E`, `det E > 0`, obtuse Gram matrix,
Lemma D conditions on `certMatrix L`) has a leaf `i` with `((Eᵀ E) σ_i) ⬝ᵥ ρ_i < 0`.  Its Rupert view is
an open-cell point `q` with cyclically unimodal depths (`exists_unimodal_of_conv_pair_closure`), which is
a lex cell of the Euclidean point set `p + E Y` (`lexCell_of_frameCell`, base view `E q`, tilt `0`).  If
the rim avoids the apex (`(L i).y j ≠ 0`) the lex cell has rim in `O = p + E (Y \ {0})` avoiding `p`, i.e.
`CornerLeaf O z p` (`cornerLeaf_of_eq_cert`).

* `exists_unimodal_of_conv_pair(_closure)`: the open-cell unimodal view inside `isRupert_of_conv_pair(_closure)`
  (the proof of `RimCellConv` repeated up to its last line, so that `RimCellConv` stays untouched).
* `exists_neg_leaf`: a positive pairing gives a leaf with `(G σ) ⬝ᵥ ρ < 0`.
* `lexCell_of_frameCell`: frame cell with unimodal depths to `LexCell` (translation by `p`).
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix Filter Topology MeasureTheory
open Minimality.RimCell
open scoped RealInnerProductSpace

@[expose] public section

/-- The open-cell unimodal view of `isRupert_of_conv_pair`: a point `q` of the cell `A` whose depths
`((Eᵀ E) q) ⬝ᵥ y i` are cyclically unimodal. -/
theorem exists_unimodal_of_conv_pair {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {A : Set (Fin 3 → ℝ)} (hA : A ⊆ cellSet Y y)
    {p c : Fin 3 → ℝ} (hp : p ∈ interior A) (hc : c ∈ convSet y)
    (hperp : ((Eᵀ * E) *ᵥ c) ⬝ᵥ p = 0) :
    ∃ q ∈ cellSet Y y, IsCyclicUnimodal (fun i => ((Eᵀ * E) *ᵥ q) ⬝ᵥ y i) := by
  set G := Eᵀ * E with hG
  have hpA : p ∈ cellSet Y y := hA (interior_subset hp)
  have hp0 : p ≠ 0 := ne_zero_of_edge hk y p (edge_of_cell hy hyY hpA)
  have hden : 0 < (G *ᵥ p) ⬝ᵥ p := gram_pos E hE hp0
  let f : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun q => c - (((G *ᵥ c) ⬝ᵥ q) / ((G *ᵥ q) ⬝ᵥ q)) • q
  have hfc : ContinuousAt f p := by
    have : ContinuousAt (fun q : Fin 3 → ℝ => ((G *ᵥ c) ⬝ᵥ q) / ((G *ᵥ q) ⬝ᵥ q)) p := by
      refine ContinuousAt.div ?_ ?_ hden.ne'
      · refine Continuous.continuousAt ?_
        show Continuous fun q : Fin 3 → ℝ => (G *ᵥ c) ⬝ᵥ q
        simp only [dotProduct]; fun_prop
      · refine Continuous.continuousAt ?_
        simp only [dotProduct, Matrix.mulVec]; fun_prop
    exact continuousAt_const.sub (this.smul continuousAt_id)
  have hfp : f p = c := by
    simp only [f]; rw [hperp]; simp
  have ev1 : ∀ᶠ q in 𝓝 p, f q ∈ convSet y := by
    refine hfc.eventually_mem ?_
    rw [hfp]; exact (isOpen_convSet y).mem_nhds hc
  have ev2 : ∀ᶠ q in 𝓝 p, q ∈ interior A := isOpen_interior.mem_nhds hp
  obtain ⟨U, hUs, hUo, hpU⟩ := mem_nhds_iff.mp (ev1.and ev2)
  have hpos : 0 < volume U := hUo.measure_pos volume ⟨p, hpU⟩
  have hnull : volume (⋃ (ij : {ij : ZMod k × ZMod k // ij.1 ≠ ij.2}),
      {c : Fin 3 → ℝ | (G *ᵥ c) ⬝ᵥ y ij.1.1 = (G *ᵥ c) ⬝ᵥ y ij.1.2}) = 0 := by
    refine (measure_iUnion_null fun ij => ?_)
    exact volume_tie_eq_zero E hE _ _ (fun h => ij.2 (hy h))
  obtain ⟨q, hqU, hqn⟩ : ∃ q ∈ U, q ∉ ⋃ (ij : {ij : ZMod k × ZMod k // ij.1 ≠ ij.2}),
      {c : Fin 3 → ℝ | (G *ᵥ c) ⬝ᵥ y ij.1.1 = (G *ᵥ c) ⬝ᵥ y ij.1.2} := by
    by_contra hcon
    push Not at hcon
    have : volume U ≤ 0 := hnull ▸ measure_mono (fun c hc => hcon c hc)
    exact absurd hpos (not_lt.mpr this)
  obtain ⟨hqc, hqA⟩ := hUs hqU
  have hqA' : q ∈ cellSet Y y := hA (interior_subset hqA)
  have hq0 : q ≠ 0 := ne_zero_of_edge hk y q (edge_of_cell hy hyY hqA')
  have hqq : 0 < (G *ᵥ q) ⬝ᵥ q := gram_pos E hE hq0
  have hinj : Function.Injective fun i : ZMod k => (G *ᵥ q) ⬝ᵥ y i := by
    intro i j hij
    by_contra hne
    exact hqn (Set.mem_iUnion.mpr ⟨⟨(i, j), hne⟩, hij⟩)
  -- all triples are positive along `f q`
  have htri := strict_of_conv_path hk y q (f q) (edge_of_cell hy hyY hqA') hqc
  have hperp' : (G *ᵥ f q) ⬝ᵥ q = 0 := by
    simp only [f, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul]
    rw [dotProduct_comm (G *ᵥ c) q, div_mul_cancel₀ _ hqq.ne']
    ring
  have hcell' : ∀ i : ZMod k, ∀ v ∈ (Finset.univ.image y), v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, f q]).det := by
    intro i v hv h1 h2
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
    exact htri i (i + 1) j (cycBetween_succ hk i j (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h])))
  have hz := isCyclicUnimodal_perp hk E hE y hy (Finset.univ.image y)
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) (f q) hcell' q hperp' hinj
  exact ⟨q, hqA', hz⟩

/-- The open-cell unimodal view of `isRupert_of_conv_pair_closure` (the checkable form). -/
theorem exists_unimodal_of_conv_pair_closure {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {ρ σ : Fin 3 → ℝ} (hρ : ρ ∈ closure (cellSet Y y))
    (hσ : σ ∈ closure (convSet y)) (hneg : ((Eᵀ * E) *ᵥ σ) ⬝ᵥ ρ < 0) :
    ∃ q ∈ cellSet Y y, IsCyclicUnimodal (fun i => ((Eᵀ * E) *ᵥ q) ⬝ᵥ y i) := by
  set G := Eᵀ * E with hG
  let F : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ := fun z => (G *ᵥ z.2) ⬝ᵥ z.1
  have hF : Continuous F := by
    simp only [F, dotProduct, Matrix.mulVec]; fun_prop
  have hmem : (ρ, σ) ∈ closure (cellSet Y y ×ˢ convSet y) := by
    rw [closure_prod_eq]; exact ⟨hρ, hσ⟩
  obtain ⟨z, hzF, hz⟩ := mem_closure_iff.mp hmem _ (isOpen_Iio.preimage hF) hneg
  have hz1 : z.1 ∈ cellSet Y y := hz.1
  have hz2 : z.2 ∈ convSet y := hz.2
  have hz10 : z.1 ≠ 0 := ne_zero_of_edge hk y _ (edge_of_cell hy hyY hz1)
  have hz1c : z.1 ∈ convSet y := cellSet_subset_convSet hk hy hyY hz1
  let g : ℝ → ℝ := fun t => (G *ᵥ ((1 - t) • z.2 + t • z.1)) ⬝ᵥ z.1
  have hg : Continuous g := by
    simp only [g, dotProduct, Matrix.mulVec]; fun_prop
  have hg0 : g 0 < 0 := by simpa [g, F] using hzF
  have hg1 : 0 < g 1 := by
    simpa [g] using gram_pos E hE hz10
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (zero_le_one) hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (g 0) (g 1) from ⟨hg0.le, hg1.le⟩)
  exact exists_unimodal_of_conv_pair hk E hE y hy Y hyY (subset_refl _)
    (by rw [(isOpen_cellSet Y y).interior_eq]; exact hz1) (convSet_combo y hz2 hz1c ht.1 ht.2) hgt

/-- A positive pairing `∑ S_ab G_ab` of the certificate matrix with a symmetric `G` gives a leaf with
`(G σ_i) ⬝ᵥ ρ_i < 0`. -/
theorem exists_neg_leaf {Y : Finset (Fin 3 → ℝ)} {ι : Type*} [Fintype ι] (L : ι → EQLeaf Y)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hsym : ∀ a b, G a b = G b a)
    (hpos : 0 < ∑ a, ∑ b, certMatrix L a b * G a b) : ∃ i, (G *ᵥ (L i).σ) ⬝ᵥ (L i).ρ < 0 := by
  rw [pairing_certMatrix L G hsym] at hpos
  obtain ⟨i, hi⟩ : ∃ i, (L i).lam * ((G *ᵥ (L i).σ) ⬝ᵥ (L i).ρ) < 0 := by
    by_contra hc
    push Not at hc
    have := sum_nonneg fun i (_ : i ∈ (univ : Finset ι)) => hc i
    linarith
  refine ⟨i, ?_⟩
  by_contra hc
  push Not at hc
  exact absurd hi (not_lt.2 (mul_nonneg (L i).hlam hc))

theorem zmod_succ_ne {k : ℕ} (hk : 3 ≤ k) (i : ZMod k) : i + 1 ≠ i := by
  have : Fact (1 < k) := ⟨by omega⟩
  intro h
  exact one_ne_zero (add_eq_left.1 h)

/-- **A frame cell with unimodal depths is a lex cell** of the Euclidean point set `p + E Y`: base view
`E q`, tilt `0` (all tests are strict), rim `p + E (y i)`. -/
theorem lexCell_of_frameCell {k : ℕ} [NeZero k] (hk : 3 ≤ k) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (hE : 0 < E.det) (p : ℝ³) (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y)
    (Y : Finset (Fin 3 → ℝ)) (hyY : ∀ i, y i ∈ Y) {q : Fin 3 → ℝ} (hq : q ∈ cellSet Y y)
    (hz : IsCyclicUnimodal (fun i => ((Eᵀ * E) *ᵥ q) ⬝ᵥ y i)) :
    LexCell (Y.image fun w => p + emb E w) (emb E q) 0 (fun i => p + emb E (y i)) := by
  have hrow : ∀ i : ZMod k, ∀ w ∈ Y, w ≠ y i → w ≠ y (i + 1) →
      TiltSign ((p + emb E (y (i + 1))) - (p + emb E (y i))) ((p + emb E w) - (p + emb E (y i)))
        (emb E q) 0 := by
    intro i w hw h1 h2
    refine Or.inl ?_
    rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, ← emb_sub, ← emb_sub, det3_emb]
    exact mul_pos hE (hq i w hw h1 h2)
  refine ⟨hk, fun i => Finset.mem_image.2 ⟨y i, hyY i, rfl⟩, ?_, ?_, ?_⟩
  · intro i j h1 h2
    exact hrow i (y j) (hyY j) (fun h => h1 (hy h)) (fun h => h2 (hy h))
  · intro w hw hwj i
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
    refine hrow i w' hw' (fun h => hwj i (by rw [h])) (fun h => hwj (i + 1) (by rw [h]))
  · set d : ZMod k → ℝ := fun i => ((Eᵀ * E) *ᵥ q) ⬝ᵥ y i with hd
    have hzd : (fun i => ⟪p + emb E (y i), emb E q⟫) = fun i => ⟪p, emb E q⟫ + d i := by
      funext i
      rw [inner_add_left, inner_emb]
    have hw0 : (fun i => ⟪p + emb E (y i), (0 : ℝ³)⟫) = fun _ => 0 := by
      funext i; exact inner_zero_right _
    rw [hzd, hw0]
    have hdi : ∀ i j, d i = d j → i = j := fun i j h => hz.1 h
    have hU : H21.Uni (fun i => ⟪p, emb E q⟫ + d i) := by
      refine ⟨fun i h => ?_, ?_⟩
      · exact zmod_succ_ne hk i (hdi _ _ (add_left_cancel h)).symm
      · refine Eq.trans (congrArg Finset.card ?_) hz.2
        exact Finset.filter_congr fun i _ => by simp only [add_lt_add_iff_left]
    exact H21.lexUni_of_uni hU _ (fun i j h _ => hdi i j (add_left_cancel h))

/-- **The EQ adapter.**  An EQ certificate for the shape `Y` (apex `0 ∈ Y`, frame `E`) whose leaves all avoid
the apex gives a corner leaf of the Euclidean set `insert p O`, `O = p + E (Y \ {0})`, at its own apex `p`.
The leaf is a lex cell (branch (L) of `CornerLeaf`); `hrim` is what records that the rim avoids the apex. -/
theorem cornerLeaf_of_eq_cert {Y : Finset (Fin 3 → ℝ)} {ι : Type*} [Fintype ι] (L : ι → EQLeaf Y)
    (hSd : ∀ a, 0 < certMatrix L a a)
    (hSo : ∀ a b, a ≠ b → certMatrix L a b < √(certMatrix L a a) * √(certMatrix L b b))
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) (hGo : ∀ a b, a ≠ b → (Eᵀ * E) a b ≤ 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ Y) (hrim : ∀ i j, (L i).y j ≠ 0) (p : ℝ³) (z : Fin 3 → ℝ³) :
    CornerLeaf ((Y.erase 0).image fun w => p + emb E w) z p := by
  obtain ⟨i, hi⟩ := exists_neg_leaf L (Eᵀ * E) (gram_symm E)
    (pairing_pos_of_psd_obtuse _ _ hSd hSo (gram_psd E) (gram_ne_zero E hE) hGo)
  have : NeZero (L i).k := ⟨by have := (L i).hk; omega⟩
  obtain ⟨q, hq, hz⟩ := exists_unimodal_of_conv_pair_closure (L i).hk E hE (L i).y (L i).hy Y
    (L i).hyY (L i).hρ (L i).hσ hi
  have hq0 : q ≠ 0 := ne_zero_of_edge (L i).hk _ _ (edge_of_cell (L i).hy (L i).hyY hq)
  have hlex := lexCell_of_frameCell (L i).hk E hE p (L i).y (L i).hy Y (L i).hyY hq hz
  have hE0 : E.det ≠ 0 := hE.ne'
  have hid : (Y.image fun w => p + emb E w) =
      insert p ((Y.erase 0).image fun w => p + emb E w) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hw0 : w = 0
      · left; subst hw0; ext j; simp [emb_apply]
      · exact Or.inr ⟨w, ⟨hw0, hw⟩, rfl⟩
    · rintro (rfl | ⟨w, ⟨-, hw⟩, rfl⟩)
      · exact ⟨0, h0, by ext j; simp [emb_apply]⟩
      · exact ⟨w, hw, rfl⟩
  refine Or.inl ⟨emb E q, 0, (L i).k, inferInstance, fun j => p + emb E ((L i).y j), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hq0 (emb_injective hE0 (by rw [h]; ext j; simp [emb_apply]))
  · intro j
    exact Finset.mem_image.2 ⟨(L i).y j, Finset.mem_erase.2 ⟨hrim i j, (L i).hyY j⟩, rfl⟩
  · intro j h
    refine hrim i j (emb_injective hE0 ?_)
    have : emb E ((L i).y j) = 0 := by simpa using h
    rw [this]; ext l; simp [emb_apply]
  · rw [← hid]; exact hlex

end

end Minimality.CornerEQ
