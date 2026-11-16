module

public import Mathlib
public import Minimality.RimCellConv
public import Minimality.CornerEQCert
public import Minimality.CornerTransfer
public import Minimality.CornerTransferEQ
public import Minimality.RimCellPerp

/-!
# Lemma RSI (roof-strip) and Lemma RSI-sub

Source: `notes/ROOF-CASETREE.md` sections 1, 2.1, 2.2, 7.  Namespace `Minimality.CornerRSI`.

* `cornerLeaf_of_pair`: a closed-cell point `ρ`, a closed-convSet point `σ` with negative pairing give a
  `CornerLeaf` at the apex (generic form of the tail of `cornerLeaf_of_eq_cert`).
* `rsi_pairing`: the pairing `σᵀ G ρ = -(G_aa ρ_a)` for `σ = -f_a`: every other term has `G_ia = 0` or `ρ_i = 0`.
* `cornerLeaf_of_rsi`: **Lemma RSI**.  Roof (`G_ab = G_ac = 0`, `ρ_a > 0`) and the W1 variant
  (`G_ab = 0`, `ρ_c = 0`) are the same hypothesis `∀ i ≠ a, G_ia = 0 ∨ ρ_i = 0`.
* `neg_mem_closure_convSet_of_subseq`: **Lemma RSI-sub**.
-/

set_option autoImplicit false

namespace Minimality.CornerRSI

open Finset Matrix
open Minimality.RimCell Minimality.CornerEQ
open scoped RealInnerProductSpace

@[expose] public section

/-- A closed-cell point and a closed-`convSet` point with negative pairing give a corner leaf at the apex
`p = p + E 0` (`0 ∈ Y`) of `p + E Y`; `hrim` records that the rim avoids the apex. -/
theorem cornerLeaf_of_pair {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Y : Finset (Fin 3 → ℝ)}
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (hyY : ∀ i, y i ∈ Y)
    (hrim : ∀ j, y j ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (h0 : (0 : Fin 3 → ℝ) ∈ Y) {ρ σ : Fin 3 → ℝ} (hρ : ρ ∈ closure (cellSet Y y))
    (hσ : σ ∈ closure (convSet y)) (hneg : ((Eᵀ * E) *ᵥ σ) ⬝ᵥ ρ < 0) (p : ℝ³) (z : Fin 3 → ℝ³) :
    CornerLeaf ((Y.erase 0).image fun w => p + emb E w) z p := by
  obtain ⟨q, hq, hz⟩ := exists_unimodal_of_conv_pair_closure hk E hE y hy Y hyY hρ hσ hneg
  have hq0 : q ≠ 0 := ne_zero_of_edge hk _ _ (edge_of_cell hy hyY hq)
  have hlex := lexCell_of_frameCell hk E hE p y hy Y hyY hq hz
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
  refine Or.inl ⟨emb E q, 0, k, inferInstance, fun j => p + emb E (y j), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hq0 (emb_injective hE0 (by rw [h]; ext j; simp [emb_apply]))
  · intro j
    exact Finset.mem_image.2 ⟨y j, Finset.mem_erase.2 ⟨hrim j, hyY j⟩, rfl⟩
  · intro j h
    refine hrim j (emb_injective hE0 ?_)
    have : emb E (y j) = 0 := by simpa using h
    rw [this]; ext l; simp [emb_apply]
  · rw [← hid]; exact hlex

/-- The RSI pairing: for `σ = -f_a` (minus the unit vector `a`) the pairing is `-(G_aa ρ_a)` when every
other term vanishes (`G_ia = 0` or `ρ_i = 0`), hence negative for `ρ_a > 0`. -/
theorem rsi_pairing (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) (a : Fin 3) (ρ : Fin 3 → ℝ)
    (hρa : 0 < ρ a) (hz : ∀ i, i ≠ a → (Eᵀ * E) i a = 0 ∨ ρ i = 0) :
    ((Eᵀ * E) *ᵥ (-(Pi.single a 1 : Fin 3 → ℝ))) ⬝ᵥ ρ < 0 := by
  have hGa : 0 < (Eᵀ * E) a a := by
    have := gram_pos E hE (x := Pi.single a 1) (by
      intro h; have := congrFun h a; simp at this)
    simpa [Matrix.mulVec_single, dotProduct_single] using this
  have hs : ((Eᵀ * E) *ᵥ (Pi.single a 1 : Fin 3 → ℝ)) ⬝ᵥ ρ = (Eᵀ * E) a a * ρ a := by
    rw [Matrix.mulVec_single_one, dotProduct, Finset.sum_eq_single a]
    · simp
    · intro i _ hi
      rcases hz i hi with h | h <;> simp [h]
    · simp
  rw [Matrix.mulVec_neg, neg_dotProduct, hs]
  exact neg_neg_of_pos (mul_pos hGa hρa)

/-- **Lemma RSI** (corner-leaf form).  `y` is the rim of a cell of `Y` (apex `0 ∈ Y` off the rim),
`ρ ∈ cl (cellSet Y y)` (e.g. a cell point in the interior of the cone `C(x')`), `-f_a ∈ cl (convSet y)`,
`ρ_a > 0`, and every other term of the pairing dies: `G_ia = 0` (roof: `G_ab = G_ac = 0`) or `ρ_i = 0`
(W1: `G_ab = 0`, `ρ_c = 0`).  Then `p + E Y` has a corner leaf at the apex; by `cornerLeaf_lift` at every
apex `x₆ ≤ x'`. -/
theorem cornerLeaf_of_rsi {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Y : Finset (Fin 3 → ℝ)}
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (hyY : ∀ i, y i ∈ Y)
    (hrim : ∀ j, y j ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (h0 : (0 : Fin 3 → ℝ) ∈ Y) (a : Fin 3) {ρ : Fin 3 → ℝ} (hρ : ρ ∈ closure (cellSet Y y))
    (hσ : -(Pi.single a 1 : Fin 3 → ℝ) ∈ closure (convSet y)) (hρa : 0 < ρ a)
    (hz : ∀ i, i ≠ a → (Eᵀ * E) i a = 0 ∨ ρ i = 0) (p : ℝ³) (z : Fin 3 → ℝ³) :
    CornerLeaf ((Y.erase 0).image fun w => p + emb E w) z p :=
  cornerLeaf_of_pair hk y hy hyY hrim E hE h0 hρ hσ (rsi_pairing E hE a ρ hρa hz) p z

/-- Lemma RSI, plain form: `E Y` is Rupert (no apex bookkeeping). -/
theorem isRupert_of_rsi {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Y : Finset (Fin 3 → ℝ)}
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (hyY : ∀ i, y i ∈ Y)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) (a : Fin 3) {ρ : Fin 3 → ℝ}
    (hρ : ρ ∈ closure (cellSet Y y))
    (hσ : -(Pi.single a 1 : Fin 3 → ℝ) ∈ closure (convSet y)) (hρa : 0 < ρ a)
    (hz : ∀ i, i ≠ a → (Eᵀ * E) i a = 0 ∨ ρ i = 0) :
    IsRupert (Y.image (emb E)) :=
  isRupert_of_conv_pair_closure hk E hE y hy Y hyY hρ hσ (rsi_pairing E hE a ρ hρa hz)

/-- **Lemma RSI-sub.**  Let `w` be the corner rim (strictly convex along some `p₀`), `D` a set of views in
`convSet w` accumulating at `f` (the pushed corner views `f_a + ε d`), and `y` a rim with `rev y` a cyclic
subsequence of `w` (`y i = w (σ (-i))`, `σ` preserving cyclic order).  Then `-f ∈ cl (convSet y)`. -/
theorem neg_mem_closure_convSet_of_subseq {k m : ℕ} [NeZero k] [NeZero m] (hk : 3 ≤ k) (hm : 3 ≤ m)
    (w : ZMod m → Fin 3 → ℝ) (p₀ : Fin 3 → ℝ)
    (hp : ∀ i j : ZMod m, j ≠ i → j ≠ i + 1 → 0 < omega p₀ (w (i + 1) - w i) (w j - w i))
    (σ : ZMod k → ZMod m) (hσ : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l))
    (y : ZMod k → Fin 3 → ℝ) (hy : ∀ i, y i = w (σ (-i)))
    (D : Set (Fin 3 → ℝ)) (hD : D ⊆ convSet w) {f : Fin 3 → ℝ} (hf : f ∈ closure D) :
    -f ∈ closure (convSet y) := by
  have key : ∀ v ∈ D, -v ∈ convSet y := by
    intro v hv i
    have h := strict_of_conv_path hm w p₀ v hp (hD hv)
    obtain ⟨j, hj⟩ : ∃ j : ZMod k, j = -i - 2 := ⟨_, rfl⟩
    have e0 : -i = j + 2 := by rw [hj]; ring
    have e1 : -(i + 1) = j + 1 := by rw [hj]; ring
    have e2 : -(i + 2) = j := by rw [hj]; ring
    have hc := hσ _ _ _ (cycBetween_succ hk j (j + 2) (two_ne hk j).1 (two_ne hk j).2)
    have h1 := h _ _ _ hc
    rw [hy (i + 1), hy (i + 2), hy i, e0, e1, e2]
    have hid : omega (-v) (w (σ (j + 1)) - w (σ (j + 2))) (w (σ j) - w (σ (j + 2))) =
        omega v (w (σ (j + 1)) - w (σ j)) (w (σ (j + 2)) - w (σ j)) := by
      simp only [omega, Matrix.det_fin_three]
      simp
      ring
    rw [hid]; exact h1
  have : -f ∈ closure (Neg.neg '' D) :=
    image_closure_subset_closure_image continuous_neg ⟨f, hf, rfl⟩
  exact closure_mono (by rintro _ ⟨v, hv, rfl⟩; exact key v hv) this

end

end Minimality.CornerRSI
