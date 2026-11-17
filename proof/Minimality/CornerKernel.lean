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


section FacePair

variable {Y : Finset (Fin 3 → ℝ)}

theorem omega_smul_left (a : ℝ) (b x z : Fin 3 → ℝ) : omega (a • b) x z = a * omega b x z := by
  simp only [omega, Matrix.det_fin_three]; simp; ring

theorem omega_add_left (a b x z : Fin 3 → ℝ) : omega (a + b) x z = omega a x z + omega b x z := by
  simp only [omega, Matrix.det_fin_three]; simp; ring

/-- `closure (convSet y)` is closed under addition (`convSet` is an open convex cone). -/
theorem closure_convSet_add {k : ℕ} (y : ZMod k → Fin 3 → ℝ) {u v : Fin 3 → ℝ}
    (hu : u ∈ closure (convSet y)) (hv : v ∈ closure (convSet y)) : u + v ∈ closure (convSet y) := by
  have hmem : (u, v) ∈ closure (convSet y ×ˢ convSet y) := by
    rw [closure_prod_eq]; exact ⟨hu, hv⟩
  have hc : Continuous fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => z.1 + z.2 := by fun_prop
  have h1 := image_closure_subset_closure_image hc ⟨_, hmem, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ i
  show 0 < omega (a + b) _ _
  rw [omega_add_left]
  exact add_pos (ha i) (hb i)

/-- `closure (convSet y)` is closed under nonnegative scaling. -/
theorem closure_convSet_smul {k : ℕ} (y : ZMod k → Fin 3 → ℝ) {u : Fin 3 → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hu : u ∈ closure (convSet y)) : c • u ∈ closure (convSet y) := by
  have hmem : (c, u) ∈ closure (Set.Ioi (0 : ℝ) ×ˢ convSet y) := by
    rw [closure_prod_eq, closure_Ioi]; exact ⟨hc, hu⟩
  have hct : Continuous fun z : ℝ × (Fin 3 → ℝ) => z.1 • z.2 := by fun_prop
  have h1 := image_closure_subset_closure_image hct ⟨_, hmem, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ i
  have ha' : (0 : ℝ) < a := ha
  show 0 < omega (a • b) _ _
  rw [omega_smul_left]; exact mul_pos ha' (hb i)

/-- The two-leaf certificate of Lemma E2: `(ρ, -(μρ + cρ'))` on rim `y` and `(ρ', ρ)` on rim `y'` have
certificate matrix `μ ρ ρᵀ`. -/
noncomputable def facePairLeaves {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k')
    (y : ZMod k → Fin 3 → ℝ) (y' : ZMod k' → Fin 3 → ℝ)
    (hy : Function.Injective y) (hyY : ∀ j, y j ∈ Y)
    (hy' : Function.Injective y') (hyY' : ∀ j, y' j ∈ Y)
    (ρ ρ' : Fin 3 → ℝ) (μ c : ℝ) (hc : 0 ≤ c)
    (hρ : ρ ∈ closure (cellSet Y y)) (hρ' : ρ' ∈ closure (cellSet Y y'))
    (hσ : -(μ • ρ + c • ρ') ∈ closure (convSet y)) (hσ' : ρ ∈ closure (convSet y')) :
    Fin 2 → EQLeaf Y :=
  ![⟨k, hk, y, hy, hyY, ρ, -(μ • ρ + c • ρ'), hρ, hσ, 1, zero_le_one⟩,
    ⟨k', hk', y', hy', hyY', ρ', ρ, hρ', hσ', c, hc⟩]

theorem certMatrix_facePair {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k')
    (y : ZMod k → Fin 3 → ℝ) (y' : ZMod k' → Fin 3 → ℝ)
    (hy : Function.Injective y) (hyY : ∀ j, y j ∈ Y)
    (hy' : Function.Injective y') (hyY' : ∀ j, y' j ∈ Y)
    (ρ ρ' : Fin 3 → ℝ) (μ c : ℝ) (hc : 0 ≤ c)
    (hρ : ρ ∈ closure (cellSet Y y)) (hρ' : ρ' ∈ closure (cellSet Y y'))
    (hσ : -(μ • ρ + c • ρ') ∈ closure (convSet y)) (hσ' : ρ ∈ closure (convSet y')) :
    certMatrix (facePairLeaves hk hk' y y' hy hyY hy' hyY' ρ ρ' μ c hc hρ hρ' hσ hσ') =
      μ • Matrix.vecMulVec ρ ρ := by
  ext a b
  simp only [certMatrix, facePairLeaves, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem facePair_psd {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k')
    (y : ZMod k → Fin 3 → ℝ) (y' : ZMod k' → Fin 3 → ℝ)
    (hy : Function.Injective y) (hyY : ∀ j, y j ∈ Y)
    (hy' : Function.Injective y') (hyY' : ∀ j, y' j ∈ Y)
    (ρ ρ' : Fin 3 → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc : 0 ≤ c) (hρ0 : ρ ≠ 0)
    (hρ : ρ ∈ closure (cellSet Y y)) (hρ' : ρ' ∈ closure (cellSet Y y'))
    (hσ : -(μ • ρ + c • ρ') ∈ closure (convSet y)) (hσ' : ρ ∈ closure (convSet y')) :
    (certMatrix (facePairLeaves hk hk' y y' hy hyY hy' hyY' ρ ρ' μ c hc hρ hρ' hσ hσ')).PosSemidef ∧
    certMatrix (facePairLeaves hk hk' y y' hy hyY hy' hyY' ρ ρ' μ c hc hρ hρ' hσ hσ') ≠ 0 := by
  rw [certMatrix_facePair]
  refine ⟨?_, ?_⟩
  · have := (Matrix.posSemidef_vecMulVec_self_star (R := ℝ) ρ)
    simpa using this.smul hμ.le
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, ρ i ≠ 0 := by
      by_contra hh; push Not at hh; exact hρ0 (funext hh)
    have := congrFun (congrFun h i) i
    simp [Matrix.vecMulVec_apply] at this
    rcases this with h | h
    · exact hμ.ne' h
    · exact hi h

/-- **Lemma E2 (face-pair certificate).**  Rims `y`, `y'`, closed-cell points `ρ`, `ρ'`, with
`-(μρ + cρ') ∈ cl Conv(y)` and `ρ ∈ cl Conv(y')` (`μ > 0`, `c ≥ 0`, `ρ ≠ 0`): Rupert for every `E` with
`det E > 0`.  The two EQ pairs `(ρ, -(μρ + cρ'))`, `(ρ', ρ)` weighted `1`, `c` have certificate matrix
`μ ρ ρᵀ`, PSD and nonzero.  Nothing beyond the section 7 signature is dropped: all hypotheses are used
(`hc` for the weight `c`, `hρ'` for the second leaf's cell, `hμ`, `hρ0` for nonzero). -/
theorem isRupert_of_face_pair {Y : Finset (Fin 3 → ℝ)} {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k')
    (y : ZMod k → Fin 3 → ℝ) (y' : ZMod k' → Fin 3 → ℝ)
    (hy : Function.Injective y) (hyY : ∀ j, y j ∈ Y)
    (hy' : Function.Injective y') (hyY' : ∀ j, y' j ∈ Y)
    (ρ ρ' : Fin 3 → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc : 0 ≤ c) (hρ0 : ρ ≠ 0)
    (hρ : ρ ∈ closure (cellSet Y y)) (hρ' : ρ' ∈ closure (cellSet Y y'))
    (hσ : -(μ • ρ + c • ρ') ∈ closure (convSet y)) (hσ' : ρ ∈ closure (convSet y'))
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) : IsRupert (Y.image (emb E)) := by
  obtain ⟨h1, h2⟩ := facePair_psd hk hk' y y' hy hyY hy' hyY' ρ ρ' μ c hμ hc hρ0 hρ hρ' hσ hσ'
  exact isRupert_of_eq_cert_psd _ h1 h2 E hE

/-- Corner-leaf form of `isRupert_of_face_pair`; additionally both rims avoid the apex `0 ∈ Y`. -/
theorem cornerLeaf_of_face_pair {Y : Finset (Fin 3 → ℝ)} {k k' : ℕ} (hk : 3 ≤ k) (hk' : 3 ≤ k')
    (y : ZMod k → Fin 3 → ℝ) (y' : ZMod k' → Fin 3 → ℝ)
    (hy : Function.Injective y) (hyY : ∀ j, y j ∈ Y)
    (hy' : Function.Injective y') (hyY' : ∀ j, y' j ∈ Y)
    (hrim : ∀ j, y j ≠ 0) (hrim' : ∀ j, y' j ≠ 0)
    (ρ ρ' : Fin 3 → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc : 0 ≤ c) (hρ0 : ρ ≠ 0)
    (hρ : ρ ∈ closure (cellSet Y y)) (hρ' : ρ' ∈ closure (cellSet Y y'))
    (hσ : -(μ • ρ + c • ρ') ∈ closure (convSet y)) (hσ' : ρ ∈ closure (convSet y'))
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (h0 : (0 : Fin 3 → ℝ) ∈ Y) (p : ℝ³) (z : Fin 3 → ℝ³) :
    CornerLeaf ((Y.erase 0).image fun w => p + emb E w) z p := by
  obtain ⟨h1, h2⟩ := facePair_psd hk hk' y y' hy hyY hy' hyY' ρ ρ' μ c hμ hc hρ0 hρ hρ' hσ hσ'
  refine cornerLeaf_of_eq_cert_psd _ h1 h2 E hE h0 ?_ p z
  intro i j
  fin_cases i
  · exact hrim j
  · exact hrim' j

end FacePair

end

end Minimality.CornerEQ
