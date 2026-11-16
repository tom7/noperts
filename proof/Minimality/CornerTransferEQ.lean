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

* `exists_unimodal_of_conv_pair(_closure)` (now in `RimCellConv`, namespace `Minimality.RimCell`): the
  open-cell unimodal view inside `isRupert_of_conv_pair(_closure)`.
* `exists_neg_leaf` (now in `CornerEQCert`): a positive pairing gives a leaf with `(G σ) ⬝ᵥ ρ < 0`.
* `lexCell_of_frameCell`: frame cell with unimodal depths to `LexCell` (translation by `p`).
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix Filter Topology MeasureTheory
open Minimality.RimCell
open scoped RealInnerProductSpace

@[expose] public section

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
