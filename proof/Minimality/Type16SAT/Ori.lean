module

public import Minimality.Type16SAT.Ent

@[expose] public section

/-!
# L3, SAT part 5: forced signs, layer 2 (facets), the orientation chain

`FacOK g` is what a type 16 shape gives: `⟪N t, x i - x j⟫` is `0` for two points of facet `t` and
positive for `i` in the facet, `j` outside.  `Ar g T p q r` is the orientation of the triple `p q r`
of facet `T` against its normal, `Bq g a b c d` the bracket.  The chain: from the chirality
`0 < Bq g 3 0 5 6` (the bracket [3056]), the 14 orientations of triples in facets and 28 brackets are forced by
`brk_fwd`/`brk_rev` (two facets through a common bracket).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- Facet vertex sets as lists. -/
def FSl : List (List Nat) :=
  [[0,2,3,5],[1,3,5,6],[0,2,4],[0,3,6],[0,4,6],[1,4,5],[1,4,6],[2,4,5]]

/-- Facet `t` contains point `i`. -/
def inF (t i : Nat) : Bool := (FSl.getD t []).contains i

/-- Orientation of the triple `p q r` of facet `T` against its normal. -/
noncomputable def Ar (g : Geo) (T p q r : Nat) : ℝ := det3 (g.x q - g.x p) (g.x r - g.x p) (g.N T)
/-- The bracket of four points. -/
noncomputable def Bq (g : Geo) (a b c d : Nat) : ℝ :=
  det3 (g.x b - g.x a) (g.x c - g.x a) (g.x d - g.x a)

/-- The facts a shape with these eight facets gives about the normals and the points. -/
structure FacOK (g : Geo) : Prop where
  zero : ∀ t i j, inF t i = true → inF t j = true → ⟪g.N t, g.x i - g.x j⟫ = 0
  pos : ∀ t i j, j < 7 → inF t i = true → inF t j = false → 0 < ⟪g.N t, g.x i - g.x j⟫

macro "bq_eq" : tactic => `(tactic| (simp only [Bq, Ar, det3_expand, PiLp.sub_apply]; ring))

/-- Every facet normal has positive norm. -/
theorem FacOK.nn {g : Geo} (hF : FacOK g) (t : Nat) (ht : t < 8) : 0 < ⟪g.N t, g.N t⟫ := by
  have : ∃ i < 7, ∃ j < 7, inF t i = true ∧ inF t j = false := by
    revert t; decide
  obtain ⟨i, hi, j, hj, h1, h2⟩ := this
  have := hF.pos t i j hj h1 h2
  refine real_inner_self_pos.mpr fun h0 => ?_
  rw [h0] at this
  simp at this

/-- A triple of a facet and a point off it: `Ar * ⟪N, x p - x s⟫ = - |N|² * Bq`. -/
theorem brk_id {g : Geo} (hF : FacOK g) (T p q r s : Nat) (hp : inF T p = true) (hq : inF T q = true)
    (hr : inF T r = true) :
    Ar g T p q r * ⟪g.N T, g.x p - g.x s⟫ = - ⟪g.N T, g.N T⟫ * Bq g p q r s := by
  have hu : ⟪g.N T, g.x q - g.x p⟫ = 0 := by
    have := hF.zero T q p hq hp; exact this
  have hv : ⟪g.N T, g.x r - g.x p⟫ = 0 := hF.zero T r p hr hp
  have := det_perp _ _ (g.x s - g.x p) (g.N T) hu hv
  have e : ⟪g.N T, g.x s - g.x p⟫ = - ⟪g.N T, g.x p - g.x s⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [e] at this
  unfold Ar Bq
  linarith

/-- Forward: an orientation fact gives the bracket sign with any point off the facet. -/
theorem brk_fwd {g : Geo} (hF : FacOK g) (T p q r s : Nat) (hp : inF T p = true) (hq : inF T q = true)
    (hr : inF T r = true) (hs : s < 7) (hns : inF T s = false) (ε : ℝ) (h : 0 < ε * Ar g T p q r) :
    0 < -ε * Bq g p q r s := by
  have hT : T < 8 := by
    by_contra hc
    have e : FSl.getD T [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [FSl]; omega)]; rfl
    have hp' : (FSl.getD T []).contains p = true := hp
    rw [e] at hp'
    simp at hp'
  have F := hF.pos T p s hs hp hns
  have n := hF.nn T hT
  have id := brk_id hF T p q r s hp hq hr
  have : 0 < ε * Ar g T p q r * ⟪g.N T, g.x p - g.x s⟫ := mul_pos h F
  have e : ε * Ar g T p q r * ⟪g.N T, g.x p - g.x s⟫ = ⟪g.N T, g.N T⟫ * (-ε * Bq g p q r s) := by
    calc _ = ε * (Ar g T p q r * ⟪g.N T, g.x p - g.x s⟫) := by ring
      _ = _ := by rw [id]; ring
  rw [e] at this
  by_contra hc
  have := mul_nonpos_of_nonneg_of_nonpos n.le (not_lt.mp hc)
  linarith

/-- Reverse: a bracket sign with a point off the facet gives the orientation of the facet triple. -/
theorem brk_rev {g : Geo} (hF : FacOK g) (T p q r s : Nat) (hp : inF T p = true) (hq : inF T q = true)
    (hr : inF T r = true) (hs : s < 7) (hns : inF T s = false) (ε : ℝ) (h : 0 < ε * Bq g p q r s) :
    0 < -ε * Ar g T p q r := by
  have hT : T < 8 := by
    by_contra hc
    have e : FSl.getD T [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [FSl]; omega)]; rfl
    have hp' : (FSl.getD T []).contains p = true := hp
    rw [e] at hp'
    simp at hp'
  have F := hF.pos T p s hs hp hns
  have n := hF.nn T hT
  have id := brk_id hF T p q r s hp hq hr
  by_contra hc
  have h1 : 0 ≤ ε * Ar g T p q r := by linarith [not_lt.mp hc]
  have h2 : 0 ≤ ε * Ar g T p q r * ⟪g.N T, g.x p - g.x s⟫ := mul_nonneg h1 F.le
  have e : ε * Ar g T p q r * ⟪g.N T, g.x p - g.x s⟫ = ⟪g.N T, g.N T⟫ * (-ε * Bq g p q r s) := by
    calc _ = ε * (Ar g T p q r * ⟪g.N T, g.x p - g.x s⟫) := by ring
      _ = _ := by rw [id]; ring
  rw [e] at h2
  have := mul_pos n h
  nlinarith

/-- The orientations of the triples of facets (sorted), as the chain derives them from the chirality. -/
def oriTab : List ((Nat × Nat × Nat × Nat) × Int) :=
  [((0,0,2,3),-1), ((0,0,2,5),-1), ((0,0,3,5),1), ((0,2,3,5),1), ((1,1,3,5),-1), ((1,1,3,6),1), ((1,1,5,6),1), ((1,3,5,6),-1), ((2,0,2,4),1), ((3,0,3,6),-1), ((4,0,4,6),1), ((5,1,4,5),1), ((6,1,4,6),-1), ((7,2,4,5),-1)]

/-- The six orderings of a triple, with the sign of the permutation. -/
def perms6 (e : (Nat × Nat × Nat × Nat) × Int) : List ((Nat × Nat × Nat × Nat) × Int) :=
  match e with
  | ((T, p, q, r), s) =>
    [((T,p,q,r),s), ((T,q,r,p),s), ((T,r,p,q),s), ((T,q,p,r),-s), ((T,p,r,q),-s), ((T,r,q,p),-s)]

/-- The orientation facts, for all orderings of the 14 triples. -/
def OriOK (g : Geo) : Prop :=
  ∀ e ∈ oriTab, ∀ k ∈ perms6 e, 0 < (k.2 : ℝ) * Ar g k.1.1 k.1.2.1 k.1.2.2.1 k.1.2.2.2

/-- Permuting a triple keeps its orientation up to the sign of the permutation. -/
theorem perms6_sound (g : Geo) (T p q r : Nat) (s : Int) (h : 0 < (s : ℝ) * Ar g T p q r) :
    ∀ k ∈ perms6 ((T, p, q, r), s), 0 < (k.2 : ℝ) * Ar g k.1.1 k.1.2.1 k.1.2.2.1 k.1.2.2.2 := by
  have e1 : Ar g T q r p = Ar g T p q r := by bq_eq
  have e2 : Ar g T r p q = Ar g T p q r := by bq_eq
  have e3 : Ar g T q p r = - Ar g T p q r := by bq_eq
  have e4 : Ar g T p r q = - Ar g T p q r := by bq_eq
  have e5 : Ar g T r q p = - Ar g T p q r := by bq_eq
  intro k hk
  simp only [perms6, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5] <;>
    push_cast <;> linarith

set_option maxHeartbeats 0 in
/-- **The orientation chain**: the chirality `0 < Bq g 3 0 5 6` ([3056]) forces all 14 orientations (generated by `mkori16.py 3 0 5 6`). -/
theorem oriOK_of_chir {g : Geo} (hF : FacOK g) (hchir : 0 < Bq g 3 0 5 6) : OriOK g := by
  have B_0_3_5_6 : 0 < (-1:ℝ) * Bq g 0 3 5 6 := by
      have e : Bq g 3 0 5 6 = (-1:ℝ) * Bq g 0 3 5 6 := by bq_eq
      linarith [hchir, e]
  have O_0_0_3_5 : 0 < (1:ℝ) * Ar g 0 0 3 5 := by
      have e : Bq g 0 3 5 6 = (1:ℝ) * Bq g 0 3 5 6 := by bq_eq
      have := brk_rev hF 0 0 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) (by rw [e]; linarith [B_0_3_5_6])
      linarith
  have O_1_3_5_6 : 0 < (-1:ℝ) * Ar g 1 3 5 6 := by
      have e : Bq g 3 5 6 0 = (-1:ℝ) * Bq g 0 3 5 6 := by bq_eq
      have := brk_rev hF 1 3 5 6 0 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) (by rw [e]; linarith [B_0_3_5_6])
      linarith
  have O_3_0_3_6 : 0 < (-1:ℝ) * Ar g 3 0 3 6 := by
      have e : Bq g 0 3 6 5 = (-1:ℝ) * Bq g 0 3 5 6 := by bq_eq
      have := brk_rev hF 3 0 3 6 5 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) (by rw [e]; linarith [B_0_3_5_6])
      linarith
  have B_0_1_3_5 : 0 < (-1:ℝ) * Bq g 0 1 3 5 := by
      have e : Bq g 0 3 5 1 = (1:ℝ) * Bq g 0 1 3 5 := by bq_eq
      have := brk_fwd hF 0 0 3 5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_0_0_3_5
      rw [e] at this
      linarith
  have B_0_3_4_5 : 0 < (1:ℝ) * Bq g 0 3 4 5 := by
      have e : Bq g 0 3 5 4 = (-1:ℝ) * Bq g 0 3 4 5 := by bq_eq
      have := brk_fwd hF 0 0 3 5 4 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_0_0_3_5
      rw [e] at this
      linarith
  have B_2_3_5_6 : 0 < (-1:ℝ) * Bq g 2 3 5 6 := by
      have e : Bq g 3 5 6 2 = (-1:ℝ) * Bq g 2 3 5 6 := by bq_eq
      have := brk_fwd hF 1 3 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_1_3_5_6
      rw [e] at this
      linarith
  have B_3_4_5_6 : 0 < (1:ℝ) * Bq g 3 4 5 6 := by
      have e : Bq g 3 5 6 4 = (1:ℝ) * Bq g 3 4 5 6 := by bq_eq
      have := brk_fwd hF 1 3 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_1_3_5_6
      rw [e] at this
      linarith
  have B_0_1_3_6 : 0 < (1:ℝ) * Bq g 0 1 3 6 := by
      have e : Bq g 0 3 6 1 = (1:ℝ) * Bq g 0 1 3 6 := by bq_eq
      have := brk_fwd hF 3 0 3 6 1 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_3_0_3_6
      rw [e] at this
      linarith
  have B_0_2_3_6 : 0 < (1:ℝ) * Bq g 0 2 3 6 := by
      have e : Bq g 0 3 6 2 = (1:ℝ) * Bq g 0 2 3 6 := by bq_eq
      have := brk_fwd hF 3 0 3 6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_3_0_3_6
      rw [e] at this
      linarith
  have B_0_3_4_6 : 0 < (-1:ℝ) * Bq g 0 3 4 6 := by
      have e : Bq g 0 3 6 4 = (-1:ℝ) * Bq g 0 3 4 6 := by bq_eq
      have := brk_fwd hF 3 0 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_3_0_3_6
      rw [e] at this
      linarith
  have O_0_0_2_3 : 0 < (-1:ℝ) * Ar g 0 0 2 3 := by
      have e : Bq g 0 2 3 6 = (1:ℝ) * Bq g 0 2 3 6 := by bq_eq
      have := brk_rev hF 0 0 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) (by rw [e]; linarith [B_0_2_3_6])
      linarith
  have O_0_2_3_5 : 0 < (1:ℝ) * Ar g 0 2 3 5 := by
      have e : Bq g 2 3 5 6 = (1:ℝ) * Bq g 2 3 5 6 := by bq_eq
      have := brk_rev hF 0 2 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) (by rw [e]; linarith [B_2_3_5_6])
      linarith
  have O_1_1_3_5 : 0 < (-1:ℝ) * Ar g 1 1 3 5 := by
      have e : Bq g 1 3 5 0 = (-1:ℝ) * Bq g 0 1 3 5 := by bq_eq
      have := brk_rev hF 1 1 3 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) (by rw [e]; linarith [B_0_1_3_5])
      linarith
  have O_1_1_3_6 : 0 < (1:ℝ) * Ar g 1 1 3 6 := by
      have e : Bq g 1 3 6 0 = (-1:ℝ) * Bq g 0 1 3 6 := by bq_eq
      have := brk_rev hF 1 1 3 6 0 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) (by rw [e]; linarith [B_0_1_3_6])
      linarith
  have O_4_0_4_6 : 0 < (1:ℝ) * Ar g 4 0 4 6 := by
      have e : Bq g 0 4 6 3 = (1:ℝ) * Bq g 0 3 4 6 := by bq_eq
      have := brk_rev hF 4 0 4 6 3 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) (by rw [e]; linarith [B_0_3_4_6])
      linarith
  have B_0_1_2_3 : 0 < (1:ℝ) * Bq g 0 1 2 3 := by
      have e : Bq g 0 2 3 1 = (1:ℝ) * Bq g 0 1 2 3 := by bq_eq
      have := brk_fwd hF 0 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_0_0_2_3
      rw [e] at this
      linarith
  have B_0_2_3_4 : 0 < (1:ℝ) * Bq g 0 2 3 4 := by
      have e : Bq g 0 2 3 4 = (1:ℝ) * Bq g 0 2 3 4 := by bq_eq
      have := brk_fwd hF 0 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_0_0_2_3
      rw [e] at this
      linarith
  have B_1_2_3_5 : 0 < (1:ℝ) * Bq g 1 2 3 5 := by
      have e : Bq g 2 3 5 1 = (-1:ℝ) * Bq g 1 2 3 5 := by bq_eq
      have := brk_fwd hF 0 2 3 5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_0_2_3_5
      rw [e] at this
      linarith
  have B_2_3_4_5 : 0 < (1:ℝ) * Bq g 2 3 4 5 := by
      have e : Bq g 2 3 5 4 = (-1:ℝ) * Bq g 2 3 4 5 := by bq_eq
      have := brk_fwd hF 0 2 3 5 4 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_0_2_3_5
      rw [e] at this
      linarith
  have B_1_3_4_5 : 0 < (-1:ℝ) * Bq g 1 3 4 5 := by
      have e : Bq g 1 3 5 4 = (-1:ℝ) * Bq g 1 3 4 5 := by bq_eq
      have := brk_fwd hF 1 1 3 5 4 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_1_1_3_5
      rw [e] at this
      linarith
  have B_1_2_3_6 : 0 < (-1:ℝ) * Bq g 1 2 3 6 := by
      have e : Bq g 1 3 6 2 = (1:ℝ) * Bq g 1 2 3 6 := by bq_eq
      have := brk_fwd hF 1 1 3 6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_1_1_3_6
      rw [e] at this
      linarith
  have B_1_3_4_6 : 0 < (1:ℝ) * Bq g 1 3 4 6 := by
      have e : Bq g 1 3 6 4 = (-1:ℝ) * Bq g 1 3 4 6 := by bq_eq
      have := brk_fwd hF 1 1 3 6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_1_1_3_6
      rw [e] at this
      linarith
  have B_0_1_4_6 : 0 < (-1:ℝ) * Bq g 0 1 4 6 := by
      have e : Bq g 0 4 6 1 = (1:ℝ) * Bq g 0 1 4 6 := by bq_eq
      have := brk_fwd hF 4 0 4 6 1 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_4_0_4_6
      rw [e] at this
      linarith
  have B_0_2_4_6 : 0 < (-1:ℝ) * Bq g 0 2 4 6 := by
      have e : Bq g 0 4 6 2 = (1:ℝ) * Bq g 0 2 4 6 := by bq_eq
      have := brk_fwd hF 4 0 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_4_0_4_6
      rw [e] at this
      linarith
  have B_0_4_5_6 : 0 < (1:ℝ) * Bq g 0 4 5 6 := by
      have e : Bq g 0 4 6 5 = (-1:ℝ) * Bq g 0 4 5 6 := by bq_eq
      have := brk_fwd hF 4 0 4 6 5 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_4_0_4_6
      rw [e] at this
      linarith
  have O_2_0_2_4 : 0 < (1:ℝ) * Ar g 2 0 2 4 := by
      have e : Bq g 0 2 4 3 = (-1:ℝ) * Bq g 0 2 3 4 := by bq_eq
      have := brk_rev hF 2 0 2 4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) (by rw [e]; linarith [B_0_2_3_4])
      linarith
  have O_5_1_4_5 : 0 < (1:ℝ) * Ar g 5 1 4 5 := by
      have e : Bq g 1 4 5 3 = (1:ℝ) * Bq g 1 3 4 5 := by bq_eq
      have := brk_rev hF 5 1 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) (by rw [e]; linarith [B_1_3_4_5])
      linarith
  have O_6_1_4_6 : 0 < (-1:ℝ) * Ar g 6 1 4 6 := by
      have e : Bq g 1 4 6 0 = (-1:ℝ) * Bq g 0 1 4 6 := by bq_eq
      have := brk_rev hF 6 1 4 6 0 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) (by rw [e]; linarith [B_0_1_4_6])
      linarith
  have O_7_2_4_5 : 0 < (-1:ℝ) * Ar g 7 2 4 5 := by
      have e : Bq g 2 4 5 3 = (1:ℝ) * Bq g 2 3 4 5 := by bq_eq
      have := brk_rev hF 7 2 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) (by rw [e]; linarith [B_2_3_4_5])
      linarith
  have B_0_1_2_4 : 0 < (-1:ℝ) * Bq g 0 1 2 4 := by
      have e : Bq g 0 2 4 1 = (1:ℝ) * Bq g 0 1 2 4 := by bq_eq
      have := brk_fwd hF 2 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_2_0_2_4
      rw [e] at this
      linarith
  have B_0_2_4_5 : 0 < (-1:ℝ) * Bq g 0 2 4 5 := by
      have e : Bq g 0 2 4 5 = (1:ℝ) * Bq g 0 2 4 5 := by bq_eq
      have := brk_fwd hF 2 0 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_2_0_2_4
      rw [e] at this
      linarith
  have B_0_1_4_5 : 0 < (1:ℝ) * Bq g 0 1 4 5 := by
      have e : Bq g 1 4 5 0 = (-1:ℝ) * Bq g 0 1 4 5 := by bq_eq
      have := brk_fwd hF 5 1 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_5_1_4_5
      rw [e] at this
      linarith
  have B_1_2_4_5 : 0 < (-1:ℝ) * Bq g 1 2 4 5 := by
      have e : Bq g 1 4 5 2 = (1:ℝ) * Bq g 1 2 4 5 := by bq_eq
      have := brk_fwd hF 5 1 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_5_1_4_5
      rw [e] at this
      linarith
  have B_1_4_5_6 : 0 < (-1:ℝ) * Bq g 1 4 5 6 := by
      have e : Bq g 1 4 5 6 = (1:ℝ) * Bq g 1 4 5 6 := by bq_eq
      have := brk_fwd hF 5 1 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_5_1_4_5
      rw [e] at this
      linarith
  have B_1_2_4_6 : 0 < (1:ℝ) * Bq g 1 2 4 6 := by
      have e : Bq g 1 4 6 2 = (1:ℝ) * Bq g 1 2 4 6 := by bq_eq
      have := brk_fwd hF 6 1 4 6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_6_1_4_6
      rw [e] at this
      linarith
  have B_2_4_5_6 : 0 < (1:ℝ) * Bq g 2 4 5 6 := by
      have e : Bq g 2 4 5 6 = (1:ℝ) * Bq g 2 4 5 6 := by bq_eq
      have := brk_fwd hF 7 2 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_7_2_4_5
      rw [e] at this
      linarith
  have O_0_0_2_5 : 0 < (-1:ℝ) * Ar g 0 0 2 5 := by
      have e : Bq g 0 2 5 4 = (-1:ℝ) * Bq g 0 2 4 5 := by bq_eq
      have := brk_rev hF 0 0 2 5 4 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) (by rw [e]; linarith [B_0_2_4_5])
      linarith
  have O_1_1_5_6 : 0 < (1:ℝ) * Ar g 1 1 5 6 := by
      have e : Bq g 1 5 6 4 = (1:ℝ) * Bq g 1 4 5 6 := by bq_eq
      have := brk_rev hF 1 1 5 6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) (by rw [e]; linarith [B_1_4_5_6])
      linarith
  have B_0_1_2_5 : 0 < (1:ℝ) * Bq g 0 1 2 5 := by
      have e : Bq g 0 2 5 1 = (1:ℝ) * Bq g 0 1 2 5 := by bq_eq
      have := brk_fwd hF 0 0 2 5 1 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_0_0_2_5
      rw [e] at this
      linarith
  have B_0_2_5_6 : 0 < (1:ℝ) * Bq g 0 2 5 6 := by
      have e : Bq g 0 2 5 6 = (1:ℝ) * Bq g 0 2 5 6 := by bq_eq
      have := brk_fwd hF 0 0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (-1:ℝ) O_0_0_2_5
      rw [e] at this
      linarith
  have B_0_1_5_6 : 0 < (1:ℝ) * Bq g 0 1 5 6 := by
      have e : Bq g 1 5 6 0 = (-1:ℝ) * Bq g 0 1 5 6 := by bq_eq
      have := brk_fwd hF 1 1 5 6 0 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_1_1_5_6
      rw [e] at this
      linarith
  have B_1_2_5_6 : 0 < (-1:ℝ) * Bq g 1 2 5 6 := by
      have e : Bq g 1 5 6 2 = (1:ℝ) * Bq g 1 2 5 6 := by bq_eq
      have := brk_fwd hF 1 1 5 6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (1:ℝ) O_1_1_5_6
      rw [e] at this
      linarith
  intro e he
  simp only [oriTab, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine perms6_sound g _ _ _ _ _ ?_ <;> push_cast <;> assumption

end Minimality.H16.SAT
