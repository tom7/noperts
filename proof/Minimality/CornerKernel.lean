module

public import Mathlib
public import Minimality.CornerEQCert
public import Minimality.CornerTransferEQ
public import Minimality.CornerRSI

/-!
# PSD certificate, Cycle Lemma and Kernel Lemma (metric-free EQ certificates)

Source: `notes/RESIDUE-DESIGN.md` sections 3-4, `notes/lean-staged/CYCLE-LEMMA-SPEC.md`.
Write `g u v = ((Eᵀ E) u) ⬝ v`.  Each lemma finds a rim, a closed-cell point `ρ` and a closed-`convSet`
point `σ` with `g σ ρ < 0`, hence a Rupert shape (`isRupert_of_conv_pair_closure`) or a corner leaf
(`cornerLeaf_of_pair`).

* `isRupert_of_eq_cert_psd`, `cornerLeaf_of_eq_cert_psd`: the EQ certificate matrix `S` only positive
  SEMIdefinite and nonzero (`pairing_pos_of_cert_psd`: `E S Eᵀ` is PSD, nonzero by invertibility of `E`,
  so its trace `∑ S_ab (EᵀE)_ab` is positive).  No obtuseness.
* `isRupert_of_cycle`, `cornerLeaf_of_cycle`: points `r_i` with `r_(i+1) - r_i ∈ closure Conv(y_i)`,
  not all equal: `∑ g s_i r_i = -(1/2) ∑ g s_i s_i < 0`.
* `isRupert_of_kernel`, `cornerLeaf_of_kernel`: two rims, common closed-cell points `ρ_i`, vectors `w_j`
  with `w_j ∈ cl Conv(y)`, `-w_j ∈ cl Conv(y')`, and a nonzero common `t`: else all `g w_j ρ_i = 0`
  and `g t t = 0`.
Hypotheses: `NeZero` of the lengths is derived from `3 ≤ k`, so not assumed (the spec's `[NeZero k]` dropped).
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix
open Minimality.RimCell
open scoped RealInnerProductSpace

@[expose] public section

section PSD

variable {Y : Finset (Fin 3 → ℝ)} {ι : Type*} [Fintype ι]

theorem pairing_pos_of_cert_psd (L : ι → EQLeaf Y) (hS : (certMatrix L).PosSemidef)
    (hS0 : certMatrix L ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    0 < ∑ a, ∑ b, certMatrix L a b * (Eᵀ * E) a b := by
  have hP : (E * certMatrix L * Eᴴ).PosSemidef := hS.mul_mul_conjTranspose_same E
  have hU : IsUnit E := Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2 hE.ne')
  have hM : E * certMatrix L * Eᴴ ≠ 0 := by
    intro h
    apply hS0
    have h1 : E⁻¹ * (E * certMatrix L * Eᴴ) * (Eᴴ)⁻¹ = certMatrix L := by
      have hU' : IsUnit Eᴴ := by
        rw [Matrix.isUnit_iff_isUnit_det] at hU ⊢
        simpa [Matrix.det_conjTranspose] using hU
      calc _ = (E⁻¹ * E) * certMatrix L * (Eᴴ * (Eᴴ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
            Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU')]
          simp
    rw [← h1, h]; simp
  have htr : 0 < (E * certMatrix L * Eᴴ).trace := by
    refine lt_of_le_of_ne hP.trace_nonneg fun h => hM ?_
    exact (hP.trace_eq_zero_iff.1 h.symm)
  have : (E * certMatrix L * Eᴴ).trace = ∑ a, ∑ b, certMatrix L a b * (Eᵀ * E) a b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
    ring
  rwa [this] at htr

/-- **PSD certificate.**  `certMatrix L` positive semidefinite and nonzero: every `E` with `det E > 0`
gives a Rupert `E Y`.  (The tf2 certificates `S = w q qᵀ` have this form.) -/
theorem isRupert_of_eq_cert_psd (L : ι → EQLeaf Y) (hS : (certMatrix L).PosSemidef)
    (hS0 : certMatrix L ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    IsRupert (Y.image (emb E)) :=
  isRupert_of_neg_leaf L E hE (pairing_pos_of_cert_psd L hS hS0 E hE)

theorem cornerLeaf_of_eq_cert_psd (L : ι → EQLeaf Y) (hS : (certMatrix L).PosSemidef)
    (hS0 : certMatrix L ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (h0 : (0 : Fin 3 → ℝ) ∈ Y) (hrim : ∀ i j, (L i).y j ≠ 0) (p : ℝ³) (z : Fin 3 → ℝ³) :
    CornerLeaf ((Y.erase 0).image fun w => p + emb E w) z p := by
  obtain ⟨i, hi⟩ := exists_neg_leaf L (Eᵀ * E) (gram_symm E) (pairing_pos_of_cert_psd L hS hS0 E hE)
  have : NeZero (L i).k := ⟨by have := (L i).hk; omega⟩
  exact Minimality.CornerRSI.cornerLeaf_of_pair (L i).hk (L i).y (L i).hy (L i).hyY (hrim i) E hE h0
    (L i).hρ (L i).hσ hi p z

end PSD

section Common

theorem gram_form_symm (E : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    ((Eᵀ * E) *ᵥ u) ⬝ᵥ v = ((Eᵀ * E) *ᵥ v) ⬝ᵥ u := by
  simp only [dotProduct, mulVec, Fin.sum_univ_three]
  rw [gram_symm E 1 0, gram_symm E 2 0, gram_symm E 2 1]
  ring

end Common

section Cycle

/-- A node of a cycle certificate: a rim `y` of `Y` and a point `r` of its closed cell. -/
structure CycleNode (Y : Finset (Fin 3 → ℝ)) where
  k : ℕ
  hk : 3 ≤ k
  y : ZMod k → Fin 3 → ℝ
  hy : Function.Injective y
  hyY : ∀ j, y j ∈ Y
  r : Fin 3 → ℝ
  hr : r ∈ closure (cellSet Y y)

variable {Y : Finset (Fin 3 → ℝ)}

theorem cycle_core {m : ℕ} [NeZero m] (r : ZMod m → Fin 3 → ℝ)
    (hne : ∃ i, r (i + 1) ≠ r i) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    ∃ i, ((Eᵀ * E) *ᵥ (r (i + 1) - r i)) ⬝ᵥ r i < 0 := by
  set g : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun u v => ((Eᵀ * E) *ᵥ u) ⬝ᵥ v with hg
  have hsym : ∀ u v, g u v = g v u := fun u v => gram_form_symm E u v
  have hsub : ∀ u v w, g (u - v) w = g u w - g v w := by
    intro u v w; simp [hg, Matrix.mulVec_sub, sub_dotProduct]
  have hsub2 : ∀ u v w, g w (u - v) = g w u - g w v := by
    intro u v w; rw [hsym, hsub, hsym u, hsym v]
  by_contra hc
  push Not at hc
  have hid : ∀ i, 2 * g (r (i + 1) - r i) (r i) + g (r (i + 1) - r i) (r (i + 1) - r i)
      = g (r (i + 1)) (r (i + 1)) - g (r i) (r i) := by
    intro i
    rw [hsub2, hsub, hsub]
    have := hsym (r i) (r (i + 1))
    linarith
  have htel : ∑ i : ZMod m, (g (r (i + 1)) (r (i + 1)) - g (r i) (r i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have := Equiv.sum_comp (Equiv.addRight (1 : ZMod m)) (fun i => g (r i) (r i))
    simp only [Equiv.coe_addRight] at this
    linarith
  obtain ⟨i0, hi0⟩ := hne
  have hpos : 0 < g (r (i0 + 1) - r i0) (r (i0 + 1) - r i0) := gram_pos E hE (sub_ne_zero.2 hi0)
  have hnn : ∀ i ∈ (univ : Finset (ZMod m)),
      0 ≤ g (r (i + 1) - r i) (r (i + 1) - r i) := by
    intro i _
    by_cases h : r (i + 1) - r i = 0
    · simp [hg, h]
    · exact (gram_pos E hE h).le
  have h1 := Finset.single_le_sum hnn (mem_univ i0)
  have h2 : ∑ i : ZMod m, g (r (i + 1) - r i) (r (i + 1) - r i)
      = - 2 * ∑ i : ZMod m, g (r (i + 1) - r i) (r i) := by
    have : ∀ i, g (r (i + 1) - r i) (r (i + 1) - r i)
        = (g (r (i + 1)) (r (i + 1)) - g (r i) (r i)) - 2 * g (r (i + 1) - r i) (r i) := by
      intro i; linarith [hid i]
    simp only [this, Finset.sum_sub_distrib, htel, ← Finset.mul_sum]; ring
  have h3 : 0 ≤ ∑ i : ZMod m, g (r (i + 1) - r i) (r i) :=
    Finset.sum_nonneg fun i _ => hc i
  linarith

/-- **Cycle Lemma.**  Rims with closed-cell points `r_i` and `r_(i+1) - r_i ∈ cl Conv(y_i)` around a
cycle, the `r_i` not all equal: Rupert for every `E` with `det E > 0`. -/
theorem isRupert_of_cycle {m : ℕ} [NeZero m] (N : ZMod m → CycleNode Y)
    (hσ : ∀ i, (N (i + 1)).r - (N i).r ∈ closure (convSet (N i).y))
    (hne : ∃ i, (N (i + 1)).r ≠ (N i).r) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    IsRupert (Y.image (emb E)) := by
  obtain ⟨i, hi⟩ := cycle_core (fun i => (N i).r) hne E hE
  have : NeZero (N i).k := ⟨by have := (N i).hk; omega⟩
  exact isRupert_of_conv_pair_closure (N i).hk E hE (N i).y (N i).hy Y (N i).hyY (N i).hr (hσ i) hi

theorem cornerLeaf_of_cycle {m : ℕ} [NeZero m] (N : ZMod m → CycleNode Y)
    (hσ : ∀ i, (N (i + 1)).r - (N i).r ∈ closure (convSet (N i).y))
    (hne : ∃ i, (N (i + 1)).r ≠ (N i).r) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (h0 : (0 : Fin 3 → ℝ) ∈ Y) (hrim : ∀ i j, (N i).y j ≠ 0) (p : ℝ³) (z : Fin 3 → ℝ³) :
    CornerLeaf ((Y.erase 0).image fun w => p + emb E w) z p := by
  obtain ⟨i, hi⟩ := cycle_core (fun i => (N i).r) hne E hE
  have : NeZero (N i).k := ⟨by have := (N i).hk; omega⟩
  exact Minimality.CornerRSI.cornerLeaf_of_pair (N i).hk (N i).y (N i).hy (N i).hyY (hrim i) E hE h0
    (N i).hr (hσ i) hi p z

end Cycle

section Kernel

theorem kernel_core {p q : ℕ} (ρ : Fin p → Fin 3 → ℝ) (w : Fin q → Fin 3 → ℝ)
    (a : Fin p → ℝ) (b : Fin q → ℝ) (ht : ∑ i, a i • ρ i = ∑ j, b j • w j)
    (ht0 : ∑ i, a i • ρ i ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    ∃ i j, ((Eᵀ * E) *ᵥ w j) ⬝ᵥ ρ i < 0 ∨ ((Eᵀ * E) *ᵥ (-w j)) ⬝ᵥ ρ i < 0 := by
  by_contra hc
  push Not at hc
  have h0 : ∀ i j, ((Eᵀ * E) *ᵥ w j) ⬝ᵥ ρ i = 0 := by
    intro i j
    obtain ⟨h1, h2⟩ := hc i j
    rw [Matrix.mulVec_neg, neg_dotProduct] at h2
    linarith
  have hz : ((Eᵀ * E) *ᵥ (∑ j, b j • w j)) ⬝ᵥ (∑ i, a i • ρ i) = 0 := by
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp [smul_dotProduct, dotProduct_smul, h0 i j]
  rw [← ht] at hz
  exact (gram_pos E hE ht0).ne' (by simpa using hz)

/-- **Kernel Lemma.**  Two rims `y`, `y'`, points `ρ_i` in both closed cells, vectors `w_j` with
`w_j ∈ cl Conv(y)`, `-w_j ∈ cl Conv(y')`, and a nonzero common combination
`t = ∑ a_i ρ_i = ∑ b_j w_j`: Rupert for every `E` with `det E > 0`. -/
theorem isRupert_of_kernel {Y : Finset (Fin 3 → ℝ)} {k k' p q : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k')
    (y : ZMod k → Fin 3 → ℝ) (y' : ZMod k' → Fin 3 → ℝ)
    (hy : Function.Injective y) (hyY : ∀ i, y i ∈ Y)
    (hy' : Function.Injective y') (hyY' : ∀ i, y' i ∈ Y)
    (ρ : Fin p → Fin 3 → ℝ) (hρ : ∀ i, ρ i ∈ closure (cellSet Y y))
    (hρ' : ∀ i, ρ i ∈ closure (cellSet Y y'))
    (w : Fin q → Fin 3 → ℝ) (hw : ∀ j, w j ∈ closure (convSet y))
    (hw' : ∀ j, -w j ∈ closure (convSet y'))
    (a : Fin p → ℝ) (b : Fin q → ℝ) (ht : ∑ i, a i • ρ i = ∑ j, b j • w j)
    (ht0 : ∑ i, a i • ρ i ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) :
    IsRupert (Y.image (emb E)) := by
  have : NeZero k := ⟨by omega⟩
  have : NeZero k' := ⟨by omega⟩
  obtain ⟨i, j, h | h⟩ := kernel_core ρ w a b ht ht0 E hE
  · exact isRupert_of_conv_pair_closure hk E hE y hy Y hyY (hρ i) (hw j) h
  · exact isRupert_of_conv_pair_closure hk' E hE y' hy' Y hyY' (hρ' i) (hw' j) h

theorem cornerLeaf_of_kernel {Y : Finset (Fin 3 → ℝ)} {k k' p q : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k')
    (y : ZMod k → Fin 3 → ℝ) (y' : ZMod k' → Fin 3 → ℝ)
    (hy : Function.Injective y) (hyY : ∀ i, y i ∈ Y)
    (hy' : Function.Injective y') (hyY' : ∀ i, y' i ∈ Y)
    (hrim : ∀ j, y j ≠ 0) (hrim' : ∀ j, y' j ≠ 0)
    (ρ : Fin p → Fin 3 → ℝ) (hρ : ∀ i, ρ i ∈ closure (cellSet Y y))
    (hρ' : ∀ i, ρ i ∈ closure (cellSet Y y'))
    (w : Fin q → Fin 3 → ℝ) (hw : ∀ j, w j ∈ closure (convSet y))
    (hw' : ∀ j, -w j ∈ closure (convSet y'))
    (a : Fin p → ℝ) (b : Fin q → ℝ) (ht : ∑ i, a i • ρ i = ∑ j, b j • w j)
    (ht0 : ∑ i, a i • ρ i ≠ 0) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (h0 : (0 : Fin 3 → ℝ) ∈ Y) (pt : ℝ³) (z : Fin 3 → ℝ³) :
    CornerLeaf ((Y.erase 0).image fun w => pt + emb E w) z pt := by
  have : NeZero k := ⟨by omega⟩
  have : NeZero k' := ⟨by omega⟩
  obtain ⟨i, j, h | h⟩ := kernel_core ρ w a b ht ht0 E hE
  · exact Minimality.CornerRSI.cornerLeaf_of_pair hk y hy hyY hrim E hE h0 (hρ i) (hw j) h pt z
  · exact Minimality.CornerRSI.cornerLeaf_of_pair hk' y' hy' hyY' hrim' E hE h0 (hρ' i) (hw' j) h pt z

end Kernel

end

end Minimality.CornerEQ
