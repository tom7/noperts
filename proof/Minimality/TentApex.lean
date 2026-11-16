module

public import Mathlib
public import Minimality.RimCellConv

/-!
# Tent apex, steps L1 and L2: the x*-frame normal form and the rim of each cell of `Z`

Source: `notes/ROOF-PROOF-OPUS2.md`, sections 1, 2.1 and 2.5 (Lean plan, steps L1 and L2).
Namespace `Minimality.TentApex`.

Take the tent apex `x*` as origin and the three frame vertices `x_3, x_4, x_5` of the tent base `T` as the
frame; points are written in frame coordinates (so `x_a = e_a`).  The base `O` has the vertices `0, 1, 2`
(beyond `T`) and `3, 4, 5` (on `T`); the apex is vertex `6`.  Vertex `0 = (a0, 0, g0)`,
`1 = (0, b1, g1)`, `2 = (a2, b2, 0)`, since `x*` lies on the planes `X_3, X_4, X_5` of the side facets.

* `Frame`: the hypotheses of section 1 (positive coordinates, beyond `T`, the facets `P = 124`,
  `Q = 0123`, `R = 015` of `O` given by outward covectors `nP, nQ, nR` and constants `dP, dQ, dR`, with
  the other vertices of `O` strictly beneath).  No metric (Gram matrix) enters in L1 or L2.
* **L1.** `Frame.dP_pos`, `dQ_pos`, `dR_pos` (`x*` is strictly beneath `P, Q, R`), the six facing covectors
  `nP_eq` ... (`nu_P = d_P ((1 - b2)/a2, 1, (1 - b1)/g1)` and so on) and `Frame.planar`.
* **L2.** For each of the six sign vectors of `P, Q, R` on `Z` (views `q > 0`), `q` lies in the open cell
  `cellSet F.Y rim` of the rim polygon: `cell_Q`, `cell_P`, `cell_R`, `cell_PQ`, `cell_RQ`, `cell_PQR`.
  These are the `hcell` hypotheses of `Minimality.RimCell.isRupert_of_conv_pair` and
  `lexCell_of_frameCell`, with the point set `F.Y` of the frame coordinates of all seven vertices.

Proof of L2: one generic edge lemma (`edge_det_pos`).  For a rim edge `a -> b` between a back facet `F`
and a front facet `G`, with `nF x nG = kappa (b - a)`, `kappa > 0`:
`kappa det(b - a, v - a, q) = (dG - nG v) (nF q) + (dF - nF v) (- nG q)`, and both terms are `>= 0`.
-/

set_option autoImplicit false

namespace Minimality.TentApex

open Matrix Finset
open Minimality.RimCell

@[expose] public section

/-- The normal form of section 1.  Frame coordinates: `x* = 0`, `x_a = e_a`; the vertices of `O` are
`0 = (a0,0,g0)`, `1 = (0,b1,g1)`, `2 = (a2,b2,0)`, `3,4,5 = e_3, e_4, e_5`.  Facets `P = 124`, `Q = 0123`,
`R = 015` of `O`: outward covectors `nP, nQ, nR` with `n_F . y = d_F` on `F` and `< d_F` on the other
vertices of `O`.  (The facets `T = 345` and `X_a` need no data: `T` is only used through the beyond-`T`
inequalities, and the `X_a` are the coordinate planes.) -/
structure Frame where
  a0 : ℝ
  g0 : ℝ
  b1 : ℝ
  g1 : ℝ
  a2 : ℝ
  b2 : ℝ
  nP : Fin 3 → ℝ
  nQ : Fin 3 → ℝ
  nR : Fin 3 → ℝ
  dP : ℝ
  dQ : ℝ
  dR : ℝ
  ha0 : 0 < a0
  hg0 : 0 < g0
  hb1 : 0 < b1
  hg1 : 0 < g1
  ha2 : 0 < a2
  hb2 : 0 < b2
  /-- Vertices `0, 1, 2` lie beyond `T = {y_3 + y_4 + y_5 = 1}`. -/
  hT0 : 1 < a0 + g0
  hT1 : 1 < b1 + g1
  hT2 : 1 < a2 + b2
  -- Q = 0123 (planar quad); 4, 5 strictly beneath
  hQ3 : nQ 0 = dQ
  hQ0 : a0 * nQ 0 + g0 * nQ 2 = dQ
  hQ1 : b1 * nQ 1 + g1 * nQ 2 = dQ
  hQ2 : a2 * nQ 0 + b2 * nQ 1 = dQ
  hQ4 : nQ 1 < dQ
  hQ5 : nQ 2 < dQ
  -- P = 124; 0, 3, 5 strictly beneath
  hP4 : nP 1 = dP
  hP1 : b1 * nP 1 + g1 * nP 2 = dP
  hP2 : a2 * nP 0 + b2 * nP 1 = dP
  hP0 : a0 * nP 0 + g0 * nP 2 < dP
  hP3 : nP 0 < dP
  hP5 : nP 2 < dP
  -- R = 015; 2, 3, 4 strictly beneath
  hR5 : nR 2 = dR
  hR0 : a0 * nR 0 + g0 * nR 2 = dR
  hR1 : b1 * nR 1 + g1 * nR 2 = dR
  hR2 : a2 * nR 0 + b2 * nR 1 < dR
  hR3 : nR 0 < dR
  hR4 : nR 1 < dR

namespace Frame

variable (F : Frame)

/-! ### L1: `x*` is strictly beneath `P`, `Q`, `R` -/

theorem dQ_pos : 0 < F.dQ := by
  by_contra h
  push Not at h
  have h0 := F.hQ0
  rw [F.hQ3] at h0
  nlinarith [mul_lt_mul_of_pos_left F.hQ5 F.hg0,
    mul_nonneg (sub_nonneg.2 F.hT0.le) (neg_nonneg.2 h)]

theorem dP_pos : 0 < F.dP := by
  by_contra h
  push Not at h
  have h0 := F.hP1
  rw [F.hP4] at h0
  nlinarith [mul_lt_mul_of_pos_left F.hP5 F.hg1,
    mul_nonneg (sub_nonneg.2 F.hT1.le) (neg_nonneg.2 h)]

theorem dR_pos : 0 < F.dR := by
  by_contra h
  push Not at h
  have h0 := F.hR0
  rw [F.hR5] at h0
  nlinarith [mul_lt_mul_of_pos_left F.hR3 F.ha0,
    mul_nonneg (sub_nonneg.2 F.hT0.le) (neg_nonneg.2 h)]

/-- The facing covector of `Q`: `nu_Q = d_Q (1, (1 - a2)/b2, (1 - a0)/g0)`. -/
theorem nQ_eq : F.nQ = ![F.dQ, F.dQ * ((1 - F.a2) / F.b2), F.dQ * ((1 - F.a0) / F.g0)] := by
  have e2 := F.hQ2
  have e0 := F.hQ0
  rw [F.hQ3] at e2 e0
  have h1 : F.nQ 1 = F.dQ * ((1 - F.a2) / F.b2) := by
    field_simp [F.hb2.ne']; linarith
  have h2 : F.nQ 2 = F.dQ * ((1 - F.a0) / F.g0) := by
    field_simp [F.hg0.ne']; linarith
  ext i; fin_cases i <;> simp [F.hQ3, h1, h2]

/-- The facing covector of `P`: `nu_P = d_P ((1 - b2)/a2, 1, (1 - b1)/g1)`. -/
theorem nP_eq : F.nP = ![F.dP * ((1 - F.b2) / F.a2), F.dP, F.dP * ((1 - F.b1) / F.g1)] := by
  have e2 := F.hP2
  have e1 := F.hP1
  rw [F.hP4] at e2 e1
  have h0 : F.nP 0 = F.dP * ((1 - F.b2) / F.a2) := by
    field_simp [F.ha2.ne']; linarith
  have h2 : F.nP 2 = F.dP * ((1 - F.b1) / F.g1) := by
    field_simp [F.hg1.ne']; linarith
  ext i; fin_cases i <;> simp [F.hP4, h0, h2]

/-- The facing covector of `R`: `nu_R = d_R ((1 - g0)/a0, (1 - g1)/b1, 1)`. -/
theorem nR_eq : F.nR = ![F.dR * ((1 - F.g0) / F.a0), F.dR * ((1 - F.g1) / F.b1), F.dR] := by
  have e0 := F.hR0
  have e1 := F.hR1
  rw [F.hR5] at e0 e1
  have h0 : F.nR 0 = F.dR * ((1 - F.g0) / F.a0) := by
    field_simp [F.ha0.ne']; linarith
  have h1 : F.nR 1 = F.dR * ((1 - F.g1) / F.b1) := by
    field_simp [F.hb1.ne']; linarith
  ext i; fin_cases i <;> simp [F.hR5, h0, h1]

/-- Planarity of `Q`: `(1 - a2) b1 / b2 + (1 - a0) g1 / g0 = 1`. -/
theorem planar : (1 - F.a2) * F.b1 / F.b2 + (1 - F.a0) * F.g1 / F.g0 = 1 := by
  have h := F.hQ1
  rw [F.nQ_eq] at h
  have := F.dQ_pos
  simp at h
  field_simp at h ⊢
  nlinarith [h]

/-! ### L2: the facet table -/

/-- The seven vertices in frame coordinates: `0, 1, 2` (cap), `3, 4, 5` (frame, `= e_a`), `6 = x*`. -/
def pt : Fin 7 → Fin 3 → ℝ :=
  ![![F.a0, 0, F.g0], ![0, F.b1, F.g1], ![F.a2, F.b2, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![0, 0, 0]]

/-- The six facets of `conv (insert x* O)` meeting `Z`, as outward covectors: `0 = P, 1 = Q, 2 = R`,
`3, 4, 5 = X_3, X_4, X_5` (covector `-e_a`, constant `0`). -/
def nu : Fin 6 → Fin 3 → ℝ := ![F.nP, F.nQ, F.nR, ![-1, 0, 0], ![0, -1, 0], ![0, 0, -1]]

/-- The constants `d_F` of the six facets. -/
def dd : Fin 6 → ℝ := ![F.dP, F.dQ, F.dR, 0, 0, 0]

/-- The set of frame coordinates of the vertices of `insert x* O`. -/
noncomputable def Y : Finset (Fin 3 → ℝ) := by classical exact Finset.univ.image F.pt

end Frame

/-- Vertices of each facet: `P = 124`, `Q = 0123`, `R = 015`, `X_3 = 1456`, `X_4 = 0356`, `X_5 = 2346`. -/
def incL : Fin 6 → List (Fin 7) :=
  ![[1, 2, 4], [0, 1, 2, 3], [0, 1, 5], [1, 4, 5, 6], [0, 3, 5, 6], [2, 3, 4, 6]]

/-- Facet `f` contains vertex `j`. -/
def inc (f : Fin 6) (j : Fin 7) : Bool := decide (j ∈ incL f)

namespace Frame

variable (F : Frame)

theorem facet_eq (f : Fin 6) (j : Fin 7) (h : inc f j = true) : F.nu f ⬝ᵥ F.pt j = F.dd f := by
  have := F.dP_pos; have := F.dQ_pos; have := F.dR_pos
  fin_cases f <;> fin_cases j <;>
    simp [inc, incL, nu, pt, dd, dotProduct, Fin.sum_univ_three] at h ⊢ <;>
    linarith [F.hQ0, F.hQ1, F.hQ2, F.hQ3, F.hP1, F.hP2, F.hP4, F.hR0, F.hR1, F.hR5]

theorem facet_lt (f : Fin 6) (j : Fin 7) (h : inc f j = false) : F.nu f ⬝ᵥ F.pt j < F.dd f := by
  have := F.dP_pos; have := F.dQ_pos; have := F.dR_pos
  fin_cases f <;> fin_cases j <;>
    simp [inc, incL, nu, pt, dd, dotProduct, Fin.sum_univ_three] at h ⊢ <;>
    linarith [F.hQ4, F.hQ5, F.hP0, F.hP3, F.hP5, F.hR2, F.hR3, F.hR4, F.ha0, F.hg0, F.hb1, F.hg1,
      F.ha2, F.hb2]

theorem facet_le (f : Fin 6) (j : Fin 7) : F.nu f ⬝ᵥ F.pt j ≤ F.dd f := by
  cases h : inc f j
  · exact (F.facet_lt f j h).le
  · exact (F.facet_eq f j h).le

end Frame

/-! ### The generic edge lemma -/

/-- **Edge lemma.**  A rim edge `a -> b` between a back facet `(nF, dF)` and a front facet `(nG, dG)`
with `nF x nG = kappa (b - a)`, `kappa > 0`, has every vertex `v` that is weakly beneath both facets and
strictly beneath one of them strictly on the left, at every view `q` with `nF q > 0 > nG q`:
`kappa det(b - a, v - a, q) = (dG - nG v) (nF q) + (dF - nF v) (-(nG q))`.  (`b` enters only through
`hc`: it lies on both facets because `nF x nG` is orthogonal to `nF` and `nG`.) -/
theorem edge_det_pos {nF nG a b v q : Fin 3 → ℝ} {dF dG κ : ℝ}
    (hκ : 0 < κ) (hc : nF ⨯₃ nG = κ • (b - a))
    (hFa : nF ⬝ᵥ a = dF) (hGa : nG ⬝ᵥ a = dG)
    (hFv : nF ⬝ᵥ v ≤ dF) (hGv : nG ⬝ᵥ v ≤ dG) (hs : nF ⬝ᵥ v < dF ∨ nG ⬝ᵥ v < dG)
    (hqF : 0 < nF ⬝ᵥ q) (hqG : nG ⬝ᵥ q < 0) :
    0 < (Matrix.of ![b - a, v - a, q]).det := by
  have key : κ * (Matrix.of ![b - a, v - a, q]).det
      = (dG - nG ⬝ᵥ v) * (nF ⬝ᵥ q) + (dF - nF ⬝ᵥ v) * (-(nG ⬝ᵥ q)) := by
    have c0 := congrFun hc 0
    have c1 := congrFun hc 1
    have c2 := congrFun hc 2
    simp [cross_apply] at c0 c1 c2
    rw [← hFa, ← hGa]
    simp only [Matrix.det_fin_three, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (-((v 1 - a 1) * q 2 - (v 2 - a 2) * q 1)) * c0
      + ((v 0 - a 0) * q 2 - (v 2 - a 2) * q 0) * c1
      + (-((v 0 - a 0) * q 1 - (v 1 - a 1) * q 0)) * c2
  have h1 : 0 ≤ (dG - nG ⬝ᵥ v) * (nF ⬝ᵥ q) := mul_nonneg (sub_nonneg.2 hGv) hqF.le
  have h2 : 0 ≤ (dF - nF ⬝ᵥ v) * (-(nG ⬝ᵥ q)) :=
    mul_nonneg (sub_nonneg.2 hFv) (neg_nonneg.2 hqG.le)
  have h3 : 0 < (dG - nG ⬝ᵥ v) * (nF ⬝ᵥ q) + (dF - nF ⬝ᵥ v) * (-(nG ⬝ᵥ q)) := by
    rcases hs with h | h
    · have := mul_pos (sub_pos.2 h) (neg_pos.2 hqG); linarith
    · have := mul_pos (sub_pos.2 h) hqF; linarith
  by_contra hneg
  push Not at hneg
  nlinarith [mul_nonneg hκ.le (neg_nonneg.2 hneg)]

/-- A vector orthogonal to `nF` and `nG` is parallel to `nF x nG`. -/
theorem cross_par {nF nG d : Fin 3 → ℝ} (hF : nF ⬝ᵥ d = 0) (hG : nG ⬝ᵥ d = 0) (c : Fin 3)
    (hd : d c ≠ 0) : nF ⨯₃ nG = ((nF ⨯₃ nG) c / d c) • d := by
  have e : (nF ⨯₃ nG) ⨯₃ d = 0 := by
    rw [cross_cross_eq_smul_sub_smul, hF, hG]; simp
  have e0 := congrFun e 0
  have e1 := congrFun e 1
  have e2 := congrFun e 2
  simp [cross_apply] at e0 e1 e2
  ext i
  fin_cases i <;> fin_cases c <;> simp [cross_apply] at hd ⊢ <;> field_simp <;> linarith

namespace Frame

variable (F : Frame)

/-- The edge `a -> b` of the facets `f`, `g` has `nu f x nu g = kappa (b - a)` with `kappa > 0`
(`f` is the back facet, `g` the front facet, `a -> b` counterclockwise). -/
def Kap (f g : Fin 6) (a b : Fin 7) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ F.nu f ⨯₃ F.nu g = κ • (F.pt b - F.pt a)

theorem Kap.swap {F : Frame} {f g : Fin 6} {a b : Fin 7} (h : F.Kap f g a b) : F.Kap g f b a := by
  obtain ⟨κ, hκ, hc⟩ := h
  refine ⟨κ, hκ, ?_⟩
  rw [← cross_anticomm, hc]
  ext i; simp; ring

theorem kap_of_comp (f g : Fin 6) (a b : Fin 7) (c : Fin 3)
    (hfa : inc f a = true) (hfb : inc f b = true) (hga : inc g a = true) (hgb : inc g b = true)
    (hd : F.pt b c - F.pt a c ≠ 0)
    (hpos : 0 < (F.nu f ⨯₃ F.nu g) c / (F.pt b c - F.pt a c)) : F.Kap f g a b := by
  refine ⟨_, hpos, ?_⟩
  have h1 : F.nu f ⬝ᵥ (F.pt b - F.pt a) = 0 := by
    rw [dotProduct_sub, F.facet_eq f a hfa, F.facet_eq f b hfb, sub_self]
  have h2 : F.nu g ⬝ᵥ (F.pt b - F.pt a) = 0 := by
    rw [dotProduct_sub, F.facet_eq g a hga, F.facet_eq g b hgb, sub_self]
  exact cross_par h1 h2 c hd

end Frame

namespace Frame

variable (F : Frame)

/-! ### The ten rim edges -/

theorem kap_QX5 : F.Kap 1 5 3 2 := by
  refine F.kap_of_comp 1 5 3 2 1 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.hb2.ne'
  · rw [F.hQ3]; exact div_pos F.dQ_pos F.hb2

theorem kap_QP : F.Kap 1 0 2 1 := by
  refine F.kap_of_comp 1 0 2 1 0 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.ha2.ne'
  · have e1 : F.b2 * F.nQ 1 = F.dQ * (1 - F.a2) := by
      have := F.hQ2; rw [F.hQ3] at this; linarith
    have e2 : F.g1 * F.nP 2 = F.dP * (1 - F.b1) := by
      have := F.hP1; rw [F.hP4] at this; linarith
    have e3 : F.g1 * F.nQ 2 = F.dQ - F.b1 * F.nQ 1 := by linarith [F.hQ1]
    have key : F.b2 * F.g1 * (F.nQ 2 * F.nP 1 - F.nQ 1 * F.nP 2)
        = F.dQ * F.dP * (F.a2 + F.b2 - 1) := by
      linear_combination (F.b2 * F.nP 1) * e3 + (-F.dP * (1 - F.b1) - F.b1 * F.nP 1) * e1
        + (-(F.b2 * F.nQ 1)) * e2 + F.dQ * (F.b2 - F.b1 * (1 - F.a2)) * F.hP4
    have hpos : 0 < F.nQ 2 * F.nP 1 - F.nQ 1 * F.nP 2 := by
      by_contra h
      push Not at h
      have := F.dQ_pos; have := F.dP_pos
      nlinarith [mul_nonneg (mul_pos F.hb2 F.hg1).le (neg_nonneg.2 h),
        mul_pos (mul_pos F.dQ_pos F.dP_pos) (by linarith [F.hT2] : 0 < F.a2 + F.b2 - 1)]
    exact div_pos_of_neg_of_neg (by linarith) (by linarith [F.ha2])

theorem kap_QR : F.Kap 1 2 1 0 := by
  refine F.kap_of_comp 1 2 1 0 0 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.ha0.ne'
  · have A1 : F.g0 * F.nQ 2 = F.dQ * (1 - F.a0) := by
      have := F.hQ0; rw [F.hQ3] at this; linarith
    have A2 : F.b1 * F.nR 1 = F.dR * (1 - F.g1) := by
      have := F.hR1; rw [F.hR5] at this; linarith
    have key : F.g0 * F.b1 * (F.nQ 1 * F.nR 2 - F.nQ 2 * F.nR 1)
        = F.dQ * F.dR * (F.a0 + F.g0 - 1) := by
      linear_combination (F.g0 * F.nR 2) * F.hQ1 + (-F.b1 * F.nR 1 - F.g1 * F.nR 2) * A1
        + (-F.dQ * (1 - F.a0)) * A2 + (F.g0 * F.dQ - F.g1 * F.dQ * (1 - F.a0)) * F.hR5
    have hpos : 0 < F.nQ 1 * F.nR 2 - F.nQ 2 * F.nR 1 := by
      by_contra h
      push Not at h
      have h1 : 0 < F.dQ * F.dR * (F.a0 + F.g0 - 1) :=
        mul_pos (mul_pos F.dQ_pos F.dR_pos) (by linarith [F.hT0])
      nlinarith [mul_nonneg (mul_pos F.hg0 F.hb1).le (neg_nonneg.2 h)]
    exact div_pos hpos F.ha0

theorem kap_QX4 : F.Kap 1 4 0 3 := by
  refine F.kap_of_comp 1 4 0 3 2 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.hg0.ne'
  · rw [F.hQ3]; exact div_pos F.dQ_pos F.hg0

theorem kap_PX5 : F.Kap 0 5 2 4 := by
  refine F.kap_of_comp 0 5 2 4 0 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.ha2.ne'
  · rw [F.hP4]; exact div_pos F.dP_pos F.ha2

theorem kap_PX3 : F.Kap 0 3 4 1 := by
  refine F.kap_of_comp 0 3 4 1 2 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.hg1.ne'
  · rw [F.hP4]; exact div_pos F.dP_pos F.hg1

theorem kap_RX3 : F.Kap 2 3 1 5 := by
  refine F.kap_of_comp 2 3 1 5 1 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.hb1.ne'
  · rw [F.hR5]; exact div_pos F.dR_pos F.hb1

theorem kap_RX4 : F.Kap 2 4 5 0 := by
  refine F.kap_of_comp 2 4 5 0 0 (by decide) (by decide) (by decide) (by decide) ?_ ?_ <;>
    simp [pt, nu, cross_apply]
  · exact F.ha0.ne'
  · rw [F.hR5]; exact div_pos F.dR_pos F.ha0

end Frame
namespace Frame

variable (F : Frame)

theorem pt_mem_Y (j : Fin 7) : F.pt j ∈ F.Y := by
  simp [Frame.Y]

/-! ### From facings to the rim cell -/

/-- **Rim cell from facings.**  Let `r` be a cyclic list of vertices, `bk i` and `fr i` the back and front
facet of the rim edge `r i -> r (i+1)`, with the `Kap` orientation data.  If the view `q` has every `bk i`
back (`nu . q > 0`) and every `fr i` front, then `q` lies in the open rim cell of `F.pt ∘ r` over all
seven vertices.  All index conditions are decidable. -/
theorem rim_cell {k : ℕ} [NeZero k] (r : ZMod k → Fin 7) (bk fr : ZMod k → Fin 6)
    (q : Fin 3 → ℝ)
    (hinc : ∀ i, inc (bk i) (r i) = true ∧ inc (bk i) (r (i + 1)) = true ∧
      inc (fr i) (r i) = true ∧ inc (fr i) (r (i + 1)) = true)
    (hstr : ∀ i j, j ≠ r i → j ≠ r (i + 1) → inc (bk i) j = false ∨ inc (fr i) j = false)
    (hkap : ∀ i, F.Kap (bk i) (fr i) (r i) (r (i + 1)))
    (hqb : ∀ i, 0 < F.nu (bk i) ⬝ᵥ q) (hqf : ∀ i, F.nu (fr i) ⬝ᵥ q < 0) :
    q ∈ cellSet F.Y (fun i => F.pt (r i)) := by
  intro i v hv h1 h2
  simp only [Frame.Y, Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨j, rfl⟩ := hv
  obtain ⟨κ, hκ, hc⟩ := hkap i
  obtain ⟨hb1, hb2, hf1, hf2⟩ := hinc i
  have hs : F.nu (bk i) ⬝ᵥ F.pt j < F.dd (bk i) ∨ F.nu (fr i) ⬝ᵥ F.pt j < F.dd (fr i) := by
    rcases hstr i j (fun h => h1 (h ▸ rfl)) (fun h => h2 (h ▸ rfl)) with h | h
    · exact Or.inl (F.facet_lt _ _ h)
    · exact Or.inr (F.facet_lt _ _ h)
  exact edge_det_pos hκ hc (F.facet_eq _ _ hb1) (F.facet_eq _ _ hf1) (F.facet_le _ _)
    (F.facet_le _ _) hs (hqb i) (hqf i)

theorem dot_X3 (q : Fin 3 → ℝ) : F.nu 3 ⬝ᵥ q = -q 0 := by simp [nu, dotProduct, Fin.sum_univ_three]
theorem dot_X4 (q : Fin 3 → ℝ) : F.nu 4 ⬝ᵥ q = -q 1 := by simp [nu, dotProduct, Fin.sum_univ_three]
theorem dot_X5 (q : Fin 3 → ℝ) : F.nu 5 ⬝ᵥ q = -q 2 := by simp [nu, dotProduct, Fin.sum_univ_three]

/-! ### The six rims -/

/-- Rim of `{Q}`: `3 2 1 0`. -/
def rimQ : ZMod 4 → Fin 7 := ![3, 2, 1, 0]
/-- Rim of `{P}`: `1 2 4`. -/
def rimP : ZMod 3 → Fin 7 := ![1, 2, 4]
/-- Rim of `{R}`: `0 1 5`. -/
def rimR : ZMod 3 → Fin 7 := ![0, 1, 5]
/-- Rim of `{P, Q}`: `4 1 0 3 2`. -/
def rimPQ : ZMod 5 → Fin 7 := ![4, 1, 0, 3, 2]
/-- Rim of `{R, Q}`: `5 0 3 2 1`. -/
def rimRQ : ZMod 5 → Fin 7 := ![5, 0, 3, 2, 1]
/-- Rim of `{P, Q, R}` (the crown): `4 1 5 0 3 2`. -/
def rimPQR : ZMod 6 → Fin 7 := ![4, 1, 5, 0, 3, 2]

/-- A tactic-free closing step for the facing hypotheses `hqb`, `hqf`. -/
theorem facing_X {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) :
    F.nu 3 ⬝ᵥ q < 0 ∧ F.nu 4 ⬝ᵥ q < 0 ∧ F.nu 5 ⬝ᵥ q < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [F.dot_X3]; linarith [hq 0]
  · rw [F.dot_X4]; linarith [hq 1]
  · rw [F.dot_X5]; linarith [hq 2]

/-- Cell `{Q}` (back set `{Q}`): the rim `3 2 1 0`. -/
theorem cell_Q {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hQ : 0 < F.nQ ⬝ᵥ q) (hP : F.nP ⬝ᵥ q < 0)
    (hR : F.nR ⬝ᵥ q < 0) : q ∈ cellSet F.Y (fun i => F.pt (rimQ i)) := by
  obtain ⟨x3, x4, x5⟩ := F.facing_X hq
  refine F.rim_cell rimQ ![1, 1, 1, 1] ![5, 0, 2, 4] q (by decide) (by decide) ?_ ?_ ?_
  · intro i; fin_cases i
    · exact F.kap_QX5
    · exact F.kap_QP
    · exact F.kap_QR
    · exact F.kap_QX4
  · intro i; fin_cases i <;> exact hQ
  · intro i; fin_cases i <;> first | exact x5 | exact hP | exact hR | exact x4

/-- Cell `{P}`: the rim `1 2 4`.  (`R` need not be front: the rim edges of `P` meet only `Q`, `X_3`, `X_5`.) -/
theorem cell_P {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hP : 0 < F.nP ⬝ᵥ q) (hQ : F.nQ ⬝ᵥ q < 0) : q ∈ cellSet F.Y (fun i => F.pt (rimP i)) := by
  obtain ⟨x3, x4, x5⟩ := F.facing_X hq
  refine F.rim_cell rimP ![0, 0, 0] ![1, 5, 3] q (by decide) (by decide) ?_ ?_ ?_
  · intro i; fin_cases i
    · exact F.kap_QP.swap
    · exact F.kap_PX5
    · exact F.kap_PX3
  · intro i; fin_cases i <;> exact hP
  · intro i; fin_cases i <;> first | exact hQ | exact x5 | exact x3

/-- Cell `{R}`: the rim `0 1 5`.  (`P` need not be front.) -/
theorem cell_R {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hR : 0 < F.nR ⬝ᵥ q) (hQ : F.nQ ⬝ᵥ q < 0) : q ∈ cellSet F.Y (fun i => F.pt (rimR i)) := by
  obtain ⟨x3, x4, x5⟩ := F.facing_X hq
  refine F.rim_cell rimR ![2, 2, 2] ![1, 3, 4] q (by decide) (by decide) ?_ ?_ ?_
  · intro i; fin_cases i
    · exact F.kap_QR.swap
    · exact F.kap_RX3
    · exact F.kap_RX4
  · intro i; fin_cases i <;> exact hR
  · intro i; fin_cases i <;> first | exact hQ | exact x3 | exact x4

/-- Cell `{P, Q}`: the rim `4 1 0 3 2`. -/
theorem cell_PQ {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hP : 0 < F.nP ⬝ᵥ q) (hQ : 0 < F.nQ ⬝ᵥ q)
    (hR : F.nR ⬝ᵥ q < 0) : q ∈ cellSet F.Y (fun i => F.pt (rimPQ i)) := by
  obtain ⟨x3, x4, x5⟩ := F.facing_X hq
  refine F.rim_cell rimPQ ![0, 1, 1, 1, 0] ![3, 2, 4, 5, 5] q (by decide) (by decide) ?_ ?_ ?_
  · intro i; fin_cases i
    · exact F.kap_PX3
    · exact F.kap_QR
    · exact F.kap_QX4
    · exact F.kap_QX5
    · exact F.kap_PX5
  · intro i; fin_cases i <;> first | exact hP | exact hQ
  · intro i; fin_cases i <;> first | exact x3 | exact hR | exact x4 | exact x5

/-- Cell `{R, Q}`: the rim `5 0 3 2 1`. -/
theorem cell_RQ {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hR : 0 < F.nR ⬝ᵥ q) (hQ : 0 < F.nQ ⬝ᵥ q)
    (hP : F.nP ⬝ᵥ q < 0) : q ∈ cellSet F.Y (fun i => F.pt (rimRQ i)) := by
  obtain ⟨x3, x4, x5⟩ := F.facing_X hq
  refine F.rim_cell rimRQ ![2, 1, 1, 1, 2] ![4, 4, 5, 0, 3] q (by decide) (by decide) ?_ ?_ ?_
  · intro i; fin_cases i
    · exact F.kap_RX4
    · exact F.kap_QX4
    · exact F.kap_QX5
    · exact F.kap_QP
    · exact F.kap_RX3
  · intro i; fin_cases i <;> first | exact hR | exact hQ
  · intro i; fin_cases i <;> first | exact x4 | exact x5 | exact hP | exact x3

/-- Cell `{P, Q, R}` (the crown): the rim `4 1 5 0 3 2`. -/
theorem cell_PQR {q : Fin 3 → ℝ} (hq : ∀ i, 0 < q i) (hP : 0 < F.nP ⬝ᵥ q) (hQ : 0 < F.nQ ⬝ᵥ q)
    (hR : 0 < F.nR ⬝ᵥ q) : q ∈ cellSet F.Y (fun i => F.pt (rimPQR i)) := by
  obtain ⟨x3, x4, x5⟩ := F.facing_X hq
  refine F.rim_cell rimPQR ![0, 2, 2, 1, 1, 0] ![3, 3, 4, 4, 5, 5] q (by decide) (by decide) ?_ ?_ ?_
  · intro i; fin_cases i
    · exact F.kap_PX3
    · exact F.kap_RX3
    · exact F.kap_RX4
    · exact F.kap_QX4
    · exact F.kap_QX5
    · exact F.kap_PX5
  · intro i; fin_cases i <;> first | exact hP | exact hQ | exact hR
  · intro i; fin_cases i <;> first | exact x3 | exact x4 | exact x5

end Frame

/-- The hypotheses of `Frame` are consistent (a shape with all angles free):
`x* = 0`, `a0 = 1/2, g0 = 9/10, b1 = 3/4, g1 = 21/20, a2 = 1/2, b2 = 9/10`. -/
noncomputable example : Frame where
  a0 := 1 / 2
  g0 := 9 / 10
  b1 := 3 / 4
  g1 := 21 / 20
  a2 := 1 / 2
  b2 := 9 / 10
  nP := ![1 / 5, 1, 5 / 21]
  nQ := ![1, 5 / 9, 5 / 9]
  nR := ![1 / 5, -1 / 15, 1]
  dP := 1
  dQ := 1
  dR := 1
  ha0 := by norm_num
  hg0 := by norm_num
  hb1 := by norm_num
  hg1 := by norm_num
  ha2 := by norm_num
  hb2 := by norm_num
  hT0 := by norm_num
  hT1 := by norm_num
  hT2 := by norm_num
  hQ3 := by norm_num
  hQ0 := by norm_num
  hQ1 := by norm_num
  hQ2 := by norm_num
  hQ4 := by norm_num
  hQ5 := by norm_num
  hP4 := by norm_num
  hP1 := by norm_num
  hP2 := by norm_num
  hP0 := by norm_num
  hP3 := by norm_num
  hP5 := by norm_num
  hR5 := by norm_num
  hR0 := by norm_num
  hR1 := by norm_num
  hR2 := by norm_num
  hR3 := by norm_num
  hR4 := by norm_num

end

end Minimality.TentApex
