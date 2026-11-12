module

public import Minimality.Type24SAT.FrameInst24
public import Minimality.SilS0XC

@[expose] public section

/-!
# Type 24, layer L1: the tree's facet structure gives `Convex24`, `QuadD` and the frame sign `hdet`

`s0x_S24` is the facet family of type 24 (`A..I = 0..8`, the order of `Sem24.faces`), and an
`F : S0xFac 9 s0x_S24 y` (the generic machinery of `Minimality.SilS0XC`, as `s0x_fac29` for type 29) on `y : Fin 7 → ℝ³`
is nine affine functionals vanishing on the facet's vertices and negative at the others.  `ext y : ℕ → ℝ³` is the
`ℕ`-indexed configuration of Sem24.

The structure fixes the combinatorics but not the orientation: `Convex24 (ext y)` holds exactly for the orientation of
the labelled reference shape (the mirror image has all `cv` negative).  The chirality hypothesis is the single bracket
`[0126] < 0`, `det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0` (the cap facet `012` against `6`, `sig 0 = 1`); the other
eight orientations follow along a spanning tree of the facet adjacency (`step`), as the Ori chain of Type16SAT.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality Minimality.H21

/-- Facet vertex sets of type 24, `A..I = 0..8` (the order of `faces`). -/
def s0x_S24 : Fin 9 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 1, 6}, {0, 2, 5}, {0, 3, 4, 5}, {0, 4, 6}, {1, 2, 6}, {2, 3, 5}, {2, 3, 6}, {3, 4, 6}]

/-- The `ℕ`-indexed configuration of Sem24. -/
def ext (y : Fin 7 → ℝ³) (i : Nat) : ℝ³ := y (Fin.ofNat 7 i)

theorem s24_mem : ∀ (t : Fin 9) (v : Fin 7), v ∈ s0x_S24 t ↔ v.val ∈ faces.getD t.val [] := by decide
theorem s24_off : ∀ t : Fin 9, ∃ j i : Fin 7, j ∈ s0x_S24 t ∧ i ∉ s0x_S24 t := by decide +kernel

/-- First, second, third vertex of facet `t` as elements of `Fin 7`. -/
def fA (t : Fin 9) : Fin 7 := (Fin.ofNat 7 (fa t.val))
def fB (t : Fin 9) : Fin 7 := (Fin.ofNat 7 (fb t.val))
def fC (t : Fin 9) : Fin 7 := (Fin.ofNat 7 (fc' t.val))
theorem fABC_mem : ∀ t : Fin 9, fA t ∈ s0x_S24 t ∧ fB t ∈ s0x_S24 t ∧ fC t ∈ s0x_S24 t := by decide

section
variable {y : Fin 7 → ℝ³}

/-- Orientation of the triple `p q r` of facet `t` against its normal. -/
noncomputable def Ar (F : S0xFac 9 s0x_S24 y) (t : Fin 9) (p q r : Fin 7) : ℝ :=
  det3 (y q - y p) (y r - y p) (F.N t)

macro "ar_eq" : tactic => `(tactic| (simp only [Ar, det3_expand, PiLp.sub_apply]; ring))

theorem det_perp' (u v w N : ℝ³) (hu : ⟪N, u⟫ = 0) (hv : ⟪N, v⟫ = 0) :
    det3 u v w * ⟪N, N⟫ = det3 u v N * ⟪N, w⟫ := by
  have e : ∀ a b : ℝ³, ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    intro a b
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
  simp only [e, det3_expand] at hu hv ⊢
  linear_combination ((u 0 * N 1 * w 2 - u 0 * N 2 * w 1 - u 1 * N 0 * w 2 + u 1 * N 2 * w 0 + u 2 * N 0 * w 1 - u 2 * N 1 * w 0)) * hv - ((v 0 * N 1 * w 2 - v 0 * N 2 * w 1 - v 1 * N 0 * w 2 + v 1 * N 2 * w 0 + v 2 * N 0 * w 1 - v 2 * N 1 * w 0)) * hu

theorem nn24 (F : S0xFac 9 s0x_S24 y) (t : Fin 9) : 0 < ⟪F.N t, F.N t⟫ := by
  obtain ⟨j, i, hj, hi⟩ := s24_off t
  have h := F.neg t i hi
  have h0 := F.zero t j hj
  have : ⟪F.N t, y j - y i⟫ = F.f t (y j) - F.f t (y i) := (F.hN t _ _).symm
  refine real_inner_self_pos.mpr fun h0' => ?_
  rw [h0'] at this
  simp at this
  linarith

/-- On a facet, the vectors between its points are orthogonal to its normal. -/
theorem perp24 (F : S0xFac 9 s0x_S24 y) (t : Fin 9) (i j : Fin 7) (hi : i ∈ s0x_S24 t) (hj : j ∈ s0x_S24 t) :
    ⟪F.N t, y i - y j⟫ = 0 := by
  rw [F.inner_sub, F.zero t i hi, F.zero t j hj]; ring

/-- Off the facet: `⟪N, x p - x s⟫ > 0`. -/
theorem off24 (F : S0xFac 9 s0x_S24 y) (t : Fin 9) (p s : Fin 7) (hp : p ∈ s0x_S24 t) (hs : s ∉ s0x_S24 t) :
    0 < ⟪F.N t, y p - y s⟫ := by
  rw [F.inner_sub, F.zero t p hp]; have := F.neg t s hs; linarith

/-- A triple of a facet and a point off it: `Ar * ⟪N, x p - x s⟫ = - |N|² * [p q r s]`. -/
theorem brk_id24 (F : S0xFac 9 s0x_S24 y) (T : Fin 9) (p q r s : Fin 7) (hp : p ∈ s0x_S24 T) (hq : q ∈ s0x_S24 T)
    (hr : r ∈ s0x_S24 T) :
    Ar F T p q r * ⟪F.N T, y p - y s⟫ =
      - ⟪F.N T, F.N T⟫ * det3 (y q - y p) (y r - y p) (y s - y p) := by
  have := det_perp' (y q - y p) (y r - y p) (y s - y p) (F.N T) (perp24 F T q p hq hp) (perp24 F T r p hr hp)
  have e : ⟪F.N T, y s - y p⟫ = - ⟪F.N T, y p - y s⟫ := by rw [← inner_neg_right, neg_sub]
  rw [e] at this
  unfold Ar
  linarith

/-- Two facets through the edge `p q`, `r` on `T`, `r'` on `S`, each off the other: the orientations are opposite. -/
theorem adj24 (F : S0xFac 9 s0x_S24 y) (T S : Fin 9) (p q r r' : Fin 7)
    (hp : p ∈ s0x_S24 T) (hq : q ∈ s0x_S24 T) (hr : r ∈ s0x_S24 T)
    (hp' : p ∈ s0x_S24 S) (hq' : q ∈ s0x_S24 S) (hr' : r' ∈ s0x_S24 S)
    (hns : r' ∉ s0x_S24 T) (hnr : r ∉ s0x_S24 S) (ε : ℝ) (h : 0 < ε * Ar F T p q r) :
    0 < -ε * Ar F S p q r' := by
  have nT := nn24 F T
  have nS := nn24 F S
  have i1 := brk_id24 F T p q r r' hp hq hr
  have i2 := brk_id24 F S p q r' r hp' hq' hr'
  have f1 := off24 F T p r' hp hns
  have f2 := off24 F S p r hp' hnr
  have sw : det3 (y q - y p) (y r' - y p) (y r - y p) = - det3 (y q - y p) (y r - y p) (y r' - y p) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- B := [p q r r'] satisfies  ε B < 0  (from T) and then the sign of Ar_S
  set B := det3 (y q - y p) (y r - y p) (y r' - y p) with hB
  have h1 : 0 < ε * Ar F T p q r * ⟪F.N T, y p - y r'⟫ := mul_pos h f1
  have e1 : ε * Ar F T p q r * ⟪F.N T, y p - y r'⟫ = ⟪F.N T, F.N T⟫ * (-ε * B) := by
    calc _ = ε * (Ar F T p q r * ⟪F.N T, y p - y r'⟫) := by ring
      _ = _ := by rw [i1]; ring
  rw [e1] at h1
  have hB' : 0 < -ε * B := by
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos nT.le (not_lt.mp hc)
    linarith
  rw [sw] at i2
  -- i2 : Ar_S * f2 = -|N_S|² * (-B) = |N_S|² B ;  want  -ε Ar_S > 0
  have h2 : 0 < (-ε * Ar F S p q r') * ⟪F.N S, y p - y r⟫ := by
    have : (-ε * Ar F S p q r') * ⟪F.N S, y p - y r⟫ = ⟪F.N S, F.N S⟫ * (-ε * B) := by
      calc _ = -ε * (Ar F S p q r' * ⟪F.N S, y p - y r⟫) := by ring
        _ = _ := by rw [i2]; ring
    rw [this]; exact mul_pos nS hB'
  exact pos_of_mul_pos_left h2 f2.le

/-- One step of the orientation chain: from `0 < σT * Ar_T(abc)` to `0 < σS * Ar_S(a'b'c')`. -/
theorem step24 (F : S0xFac 9 s0x_S24 y) (T S : Fin 9) (p q r r' a b c a' b' c' : Fin 7)
    (hp : p ∈ s0x_S24 T) (hq : q ∈ s0x_S24 T) (hr : r ∈ s0x_S24 T)
    (hp' : p ∈ s0x_S24 S) (hq' : q ∈ s0x_S24 S) (hr' : r' ∈ s0x_S24 S)
    (hns : r' ∉ s0x_S24 T) (hnr : r ∉ s0x_S24 S) (σT σS δ1 δ2 ε : ℝ)
    (hT : 0 < σT * Ar F T a b c) (e1 : Ar F T p q r = δ1 * Ar F T a b c) (e2 : Ar F S a' b' c' = δ2 * Ar F S p q r')
    (hε : ε * δ1 = σT) (hσ : σS * δ2 = -ε) : 0 < σS * Ar F S a' b' c' := by
  have h : 0 < ε * Ar F T p q r := by rw [e1, ← mul_assoc, hε]; exact hT
  have := adj24 F T S p q r r' hp hq hr hp' hq' hr' hns hnr ε h
  rw [e2, ← mul_assoc, hσ]; exact this


/-- The chirality bracket `[0126] < 0` gives the orientation of the cap facet `012`. -/
theorem ori0 (F : S0xFac 9 s0x_S24 y) (h : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0) :
    0 < (1 : ℝ) * Ar F 0 0 1 2 := by
  have i := brk_id24 F 0 0 1 2 6 (by decide) (by decide) (by decide)
  have f := off24 F 0 0 6 (by decide) (by decide)
  have n := nn24 F 0
  have : 0 < Ar F 0 0 1 2 * ⟪F.N 0, y 0 - y 6⟫ := by rw [i]; nlinarith
  rw [one_mul]; exact pos_of_mul_pos_left this f.le

theorem ori24_aux (F : S0xFac 9 s0x_S24 y) (h : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0) :
    0 < (1:ℝ) * Ar F 0 0 1 2 ∧ 0 < (-1:ℝ) * Ar F 1 0 1 6 ∧ 0 < (1:ℝ) * Ar F 2 0 2 5 ∧ 0 < (1:ℝ) * Ar F 3 0 3 4 ∧
    0 < (1:ℝ) * Ar F 4 0 4 6 ∧ 0 < (-1:ℝ) * Ar F 5 1 2 6 ∧ 0 < (1:ℝ) * Ar F 6 2 3 5 ∧ 0 < (-1:ℝ) * Ar F 7 2 3 6 ∧
    0 < (-1:ℝ) * Ar F 8 3 4 6 := by
  have c0 := ori0 F h

  have c1 : 0 < (-1:ℝ) * Ar F 1 0 1 6 :=
    step24 F 0 1 0 1 2 6 0 1 2 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (-1) (1) (1) (1) c0 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c2 : 0 < (1:ℝ) * Ar F 2 0 2 5 :=
    step24 F 0 2 0 2 1 5 0 1 2 0 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (1) (-1) (1) (-1) c0 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c5 : 0 < (-1:ℝ) * Ar F 5 1 2 6 :=
    step24 F 0 5 1 2 0 6 0 1 2 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (-1) (1) (1) (1) c0 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c4 : 0 < (1:ℝ) * Ar F 4 0 4 6 :=
    step24 F 1 4 0 6 1 4 0 1 6 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (1) (-1) (-1) (1) c1 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c3 : 0 < (1:ℝ) * Ar F 3 0 3 4 :=
    step24 F 4 3 0 4 6 3 0 4 6 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (1) (1) (-1) (1) c4 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c8 : 0 < (-1:ℝ) * Ar F 8 3 4 6 :=
    step24 F 3 8 3 4 0 6 0 3 4 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (-1) (1) (1) (1) c3 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c6 : 0 < (1:ℝ) * Ar F 6 2 3 5 :=
    step24 F 2 6 2 5 0 3 0 2 5 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (1) (1) (-1) (1) c2 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c7 : 0 < (-1:ℝ) * Ar F 7 2 3 6 :=
    step24 F 6 7 2 3 5 6 2 3 5 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (-1) (1) (1) (1) c6 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩


theorem fABC_vals : ∀ t : Fin 9, fA t = ![0, 0, 0, 0, 0, 1, 2, 2, 3] t ∧ fB t = ![1, 1, 2, 3, 4, 2, 3, 3, 4] t ∧
    fC t = ![2, 6, 5, 4, 6, 6, 5, 6, 6] t := by decide
theorem sig_vals : ∀ t : Fin 9, ((sig t.val : Int) : ℝ) = ![1, -1, 1, 1, 1, -1, 1, -1, -1] t := by
  intro t; fin_cases t <;> norm_num [sig, sigs]

/-- **The orientation chain**: all nine orientations, from the chirality bracket. -/
theorem ori24 (F : S0xFac 9 s0x_S24 y) (h : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0) (t : Fin 9) :
    0 < ((sig t.val : Int) : ℝ) * Ar F t (fA t) (fB t) (fC t) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := ori24_aux F h
  rw [sig_vals t, (fABC_vals t).1, (fABC_vals t).2.1, (fABC_vals t).2.2]
  fin_cases t
  exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8]

theorem ext_ofNat (y : Fin 7 → ℝ³) (v : Fin 7) : ext y v.val = y v := by
  unfold ext; congr 1; exact Fin.ext (by simp [Fin.ofNat])

theorem inner_cross_det3 (a b c : ℝ³) : ⟪cross a b, c⟫ = det3 a b c := by
  rw [inner_eq_dot, toV3_cross, det3_eq_det]; rfl

theorem cv_ext (y : Fin 7 → ℝ³) (t : Fin 9) (v : Fin 7) :
    cv (ext y) t.val v.val = -((sig t.val : Int) : ℝ) * det3 (y (fB t) - y (fA t)) (y (fC t) - y (fA t)) (y v - y (fA t)) := by
  unfold cv nrm
  rw [inner_smul_left, ext_ofNat, inner_cross_det3]
  simp only [conj_trivial]
  have a : ext y (fa t.val) = y (fA t) := rfl
  have b : ext y (fb t.val) = y (fB t) := rfl
  have c : ext y (fc' t.val) = y (fC t) := rfl
  rw [a, b, c]; ring

/-- **Convexity**: every vertex off a facet has positive `cv`. -/
theorem cv_pos24 (F : S0xFac 9 s0x_S24 y) (h : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0) (t : Fin 9) (v : Fin 7)
    (hv : v ∉ s0x_S24 t) : 0 < cv (ext y) t.val v.val := by
  obtain ⟨hA, hB, hC⟩ := fABC_mem t
  have i := brk_id24 F t (fA t) (fB t) (fC t) v hA hB hC
  have o := ori24 F h t
  have f := off24 F t (fA t) v hA hv
  have n := nn24 F t
  rw [cv_ext]
  have : 0 < ⟪F.N t, F.N t⟫ * (-((sig t.val : Int) : ℝ) * det3 (y (fB t) - y (fA t)) (y (fC t) - y (fA t)) (y v - y (fA t))) := by
    have e : ⟪F.N t, F.N t⟫ * (-((sig t.val : Int) : ℝ) * det3 (y (fB t) - y (fA t)) (y (fC t) - y (fA t)) (y v - y (fA t)))
        = ((sig t.val : Int) : ℝ) * Ar F t (fA t) (fB t) (fC t) * ⟪F.N t, y (fA t) - y v⟫ := by
      linear_combination (-((sig t.val : Int) : ℝ)) * i
    rw [e]; exact mul_pos o f
  exact pos_of_mul_pos_right this n.le

/-- **`Convex24` from the facets** and the chirality bracket `[0126] < 0`. -/
theorem convex24_of_fac (F : S0xFac 9 s0x_S24 y) (h : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) < 0) :
    Convex24 (ext y) := by
  intro p hp
  have key : ∀ p ∈ cvList, ∃ (t : Fin 9) (v : Fin 7), p = (t.val, v.val) ∧ v ∉ s0x_S24 t := by decide +kernel
  obtain ⟨t, v, rfl, hv⟩ := key p hp
  exact cv_pos24 F h t v hv

/-- **`QuadD` from the facets**: the quadrilateral `0345` lies in a plane. -/
theorem quadD_of_fac (F : S0xFac 9 s0x_S24 y) : QuadD (ext y) := by
  have n := nn24 F 3
  have e := det_perp' (y 3 - y 0) (y 4 - y 0) (y 5 - y 0) (F.N 3) (perp24 F 3 3 0 (by decide) (by decide))
    (perp24 F 3 4 0 (by decide) (by decide))
  rw [perp24 F 3 5 0 (by decide) (by decide), mul_zero] at e
  show det3 (y 3 - y 0) (y 4 - y 0) (y 5 - y 0) = 0
  exact (mul_eq_zero.mp e).resolve_right n.ne'

end


/-- **The frame sign of F24c from convexity alone**: `cv_{C,3} > 0` (facet `C = 025`, vertex `3`) is
`det (x3 - x0, x5 - x0, x2 - x0) > 0` (`sig 2 = 1`, `nrm 2 = (x2 - x0) x (x5 - x0)`). -/
theorem hdet24 (x : Nat → ℝ³) (hC : Convex24 x) :
    0 < V3.det (V3.sub (pt x 3) (pt x 0)) (V3.sub (pt x 5) (pt x 0)) (V3.sub (pt x 2) (pt x 0)) := by
  have h := hC (2, 3) (by decide)
  simp only at h
  rw [cv_eq_cv3] at h
  simp only [cv3, nrm3, fa_2, fb_2, fc_2, sg_2, V3.smul, V3.cr, V3.dot, V3.sub, V3.det] at h ⊢
  push_cast at h
  linarith

end Minimality.T24.SAT
