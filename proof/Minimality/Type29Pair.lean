module

public import Minimality.Type29Single
public import Minimality.PSVC

@[expose] public section

/-!
# Type 29: two-view (pair) closures of the hole (PAIR29)

Instances of `PSVC.pair_closure` on the shapes of the type-29 hole that no SINGLE29 cell (and
neither `E01Hyp` nor `E24Hyp`) covers. Found by the pair census over all 630 pairs of the 36
facet-pair lines with the actual circuit signs (`pair29.cc`, PAIR29). Each instance: a list `P`
of vertices, at each view the facings on the rim and decomposition facets (`sw`), the tope rims
`R`, the decompositions `E` (edge, edge-on triangle or quad facet via `tri_coords`, corner 6 via
`corner_coords`), the signed circuits `D` (each non-facet circuit through ONE `PlaneSide`
hypothesis), the bad orders `B2` at the second view, and the two kernel checks `check1`,
`check2`. Generic statement `lexAny_pairN` (facings, plane sides, distinct depths at both views
on `P` => `Gen.LexAny F`) and the normal form `lexAny29_pairN` (class facts in place of the
plane sides that `NF29` decides, view `lv29 N X Y` for a non-edge line).

* `pair1`: views `cross N124 N346` and `x 5 - x 6` (K1a, `N.a2 < 0`).
* `pair3`: views `cross N015 N356` and `x 4 - x 6` (K1b, `N.b0 < 0`), the sigma image of `pair1`.
* `pair4`: the single edge view `x 3 - x 6` (line F346xF356) with the quad rim 1-4-6-5 and the
  facet-forced quad circuit only (an SVC-type closure that SINGLE29 did not select).
* `pair6`: the single view `cross N015 N023`, closed with SELF (the decompositions in the
  edge-on triangles 015 and 023 are negative at their own order) and no circuit.
* `pair2`, `pair5`: in `Type29Pair2.lean`, `Type29Pair5.lean` (seven points; the kernel checks are
  split by the lowest point of the order, `perms7_split`).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

/-! ### Splitting a kernel check over the orders -/

/-- Split a Boolean check over all orders of `l` by the first element. -/
theorem all_perms_split {α : Type*} [DecidableEq α] (l : List α) (hl : l ≠ []) (f : List α → Bool)
    (h : ∀ a ∈ l, ((l.erase a).permutations'.all fun L => f (a :: L)) = true) :
    l.permutations'.all f = true := by
  rw [List.all_eq_true]
  intro L hL
  rw [List.mem_permutations'] at hL
  cases L with
  | nil => exact absurd hL.symm.eq_nil hl
  | cons a L' =>
    have ha : a ∈ l := hL.subset (by simp)
    have h2 : List.Perm L' (l.erase a) := (hL.trans (List.perm_cons_erase ha)).cons_inv
    exact List.all_eq_true.mp (h a ha) L' (List.mem_permutations'.mpr h2)

/-- `all_perms_split` for the orders of `Fin 7`. -/
theorem perms7_split (f : List (Fin 7) → Bool)
    (h : ∀ a : Fin 7, (((List.finRange 7).erase a).permutations'.all fun L => f (a :: L)) = true) :
    (List.finRange 7).permutations'.all f = true :=
  all_perms_split _ (by decide) f (fun a _ => h a)

/-! ### Pair instance `pair1`: F124xF346 + F1456xF356 (rep K1aG_78, census cover 157) -/

def pair1_P : Fin 6 → Fin 7 := ![1, 2, 3, 4, 5, 6]
def pair1_s0 : Fin 6 → SignType := ![1, -1, 1, -1, -1, 0]  -- circuit 0+-+--0

theorem pair1_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 2 3 5 1 4) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair1_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair1_s0 i := by
  have hP : Function.Injective (fun i => x (pair1_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair1_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F pair1_P mu hsum hdep 4 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F pair1_P mu hsum hdep 5 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r2 := facet_pair F pair1_P mu hsum hdep 6 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (pair1_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 3) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v1 v2 v3 v4 v5 : SignType, v3 = -v5 → v2 = -v3 → v1 = -v5 → v1 = -v4 →
     v1 = pair1_s0 0 * pair1_s0 4 * v5 ∧ v2 = pair1_s0 1 * pair1_s0 4 * v5 ∧ v3 = pair1_s0 2 * pair1_s0 4 * v5 ∧ v4 = pair1_s0 3 * pair1_s0 4 * v5 ∧ v5 = pair1_s0 4 * pair1_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne pair1_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair1_s0 5 * pair1_s0 4 * b) _

def pair1_D : List (Fin 6 → SignType) := [pair1_s0]
-- view w1 (line F124xF346), facings -+--0+-0+
def pair1_swA : Fin 9 → SignType := ![-1, 1, 1, 1, 0, 1, -1, 0, 1]
def pair1_RA : List (SVC.Rim 9 6) :=
  []
def pair1_EA : List (List (Fin 6 × Fin 6)) :=
  [triDec pair1_swA 1 0 3 6 0,
   triDec pair1_swA 5 2 3 5 8]
-- view x 5 - x 6 (line F1456xF356), facings ++++-0--0
def pair1_swB : Fin 9 → SignType := ![1, 1, 1, 1, -1, 0, -1, -1, 0]
def pair1_RB : List (SVC.Rim 9 6) :=
  [{ k := 4, c := ![0, 1, 2, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![0, 0, 0, 0, 0, -1, 0, 0, -1] },
   { k := 5, c := ![0, 1, 2, 5, 3], U := {0, 2, 5, 8}, Dn := {4, 6, 7},
     sd := ![0, 0, 0, 0, 0, 1, 0, 0, 1] }]
def pair1_EB : List (List (Fin 6 × Fin 6)) :=
  [[(4, 5)],
   triDec pair1_swB 3 0 5 7 4]
def pair1_B2 : List (List (Fin 6)) :=
  [[0, 3, 2, 1, 5, 4],
   [0, 3, 2, 5, 1, 4],
   [0, 3, 2, 5, 4, 1],
   [1, 5, 4, 2, 3, 0],
   [2, 3, 0, 1, 5, 4],
   [2, 3, 0, 5, 1, 4],
   [2, 3, 0, 5, 4, 1],
   [2, 3, 5, 0, 1, 4],
   [2, 3, 5, 0, 4, 1],
   [3, 0, 2, 1, 5, 4],
   [3, 0, 2, 5, 1, 4],
   [3, 0, 2, 5, 4, 1],
   [3, 2, 0, 1, 5, 4],
   [3, 2, 0, 5, 1, 4],
   [3, 2, 0, 5, 4, 1],
   [3, 2, 5, 0, 1, 4],
   [3, 2, 5, 0, 4, 1],
   [5, 1, 4, 2, 3, 0],
   [5, 4, 1, 2, 3, 0]]

theorem pair1_check2 : check2 s0x_S29 pair1_P pair1_swB [] pair1_D pair1_EB pair1_RB pair1_B2 = true := by
  decide +kernel

theorem pair1_check1 : check1 s0x_S29 pair1_P pair1_swA [] pair1_D pair1_EA pair1_EB pair1_RA pair1_B2 = true := by
  decide +kernel

/-- **Pair `w1` + `x 5 - x 6` (lines F124xF346, F1456xF356)**, `PSVC.pair_closure`. -/
theorem lexAny_pair1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 4, w1⟫ = 0) (hw1Y : ⟪F.N 7, w1⟫ = 0)
    (hA012 : ⟪F.N 0, w1⟫ < 0)
    (hA1456 : 0 < ⟪F.N 5, w1⟫)
    (hA234 : ⟪F.N 6, w1⟫ < 0)
    (hA356 : 0 < ⟪F.N 8, w1⟫)
    (hB012 : 0 < ⟪F.N 0, x 5 - x 6⟫)
    (hB023 : 0 < ⟪F.N 2, x 5 - x 6⟫)
    (hB124 : ⟪F.N 4, x 5 - x 6⟫ < 0)
    (hB234 : ⟪F.N 6, x 5 - x 6⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 1 4)
    (hgen1 : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫)
    (hgen2 : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair1_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_neg hA012
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_pos hA1456
    · exact sign_neg hA234
    · exact sign_eq_zero_iff.mpr hw1Y
    · exact sign_pos hA356
  have hT1 : ∀ ρ ∈ pair1_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair1_EA, DecOK x pair1_P (w1) d := by
    intro d hd
    simp only [pair1_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair1_P pair1_swA 4 6 0 0 3 1 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1X
        (hs1 6 (by decide)) (hs1 0 (by decide))
    · exact decOK_tri F pair1_P pair1_swA 7 5 8 2 3 5 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1Y
        (hs1 5 (by decide)) (hs1 8 (by decide))
  have hf1 : ∀ ij ∈ ([] : List (Fin 6 × Fin 6)), ⟪x (pair1_P ij.2), w1⟫ < ⟪x (pair1_P ij.1), w1⟫ := (by simp)
  have hR1 := hR_two F pair1_swA pair1_RA 4 7 4 3 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hs2 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 5 - x 6⟫ = pair1_swB t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hB012
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos hB023
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg hB124
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg hB234
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 8 (by decide) (by decide))
  have hT2 : ∀ ρ ∈ pair1_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair1_EB, DecOK x pair1_P (x 5 - x 6) d := by
    intro d hd
    simp only [pair1_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair1_P 4 5
    · exact decOK_tri F pair1_P pair1_swB 5 7 4 0 5 3 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 5 - x 6) (edge_zero F 5 (by decide) (by decide))
        (hs2 7 (by decide)) (hs2 4 (by decide))
  have hf2 : ∀ ij ∈ ([] : List (Fin 6 × Fin 6)), ⟪x (pair1_P ij.2), x 5 - x 6⟫ < ⟪x (pair1_P ij.1), x 5 - x 6⟫ := (by simp)
  have hR2 := hR_two F pair1_swB pair1_RB 5 8 5 3 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hP : ∀ i, pair1_P i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective pair1_P := by decide
  have hD : ∀ s ∈ pair1_D, ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair1_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs
    simp only [pair1_D, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact pair1_dep0 F hS0
  exact pair_closure F pair1_P (w1) (x 5 - x 6) pair1_swA pair1_swB pair1_RA pair1_RB
    (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) (fun ρ hρ t ht => hs2 t (hT2 ρ hρ t ht)) hR1 hR2
    _ _ hf1 hf2 pair1_D hD pair1_EA pair1_EB hE1 hE2
    (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij)) (fun i j hij => hgen2 _ (hP i) _ (hP j) (hPi.ne hij))
    pair1_B2 pair1_check1 pair1_check2

/-! ### Pair instance `pair3`: F015xF356 + F1456xF346 (rep K1b_0, census cover 41) -/

def pair3_P : Fin 6 → Fin 7 := ![0, 1, 3, 4, 5, 6]
def pair3_s0 : Fin 6 → SignType := ![1, -1, -1, 1, 1, 0]  -- circuit +-0-++0

theorem pair3_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : PlaneSide x 1 3 4 0 5 < 0) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair3_s0 i := by
  have hP : Function.Injective (fun i => x (pair3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair3_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F pair3_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F pair3_P mu hsum hdep 3 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r2 := facet_pair F pair3_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_opp (plane_rel0 (fun i => x (pair3_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 4) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v0 v1 v3 v4 v5 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = v5 →
     v0 = pair3_s0 0 * pair3_s0 4 * v5 ∧ v1 = pair3_s0 1 * pair3_s0 4 * v5 ∧ v3 = pair3_s0 2 * pair3_s0 4 * v5 ∧ v4 = pair3_s0 3 * pair3_s0 4 * v5 ∧ v5 = pair3_s0 4 * pair3_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne pair3_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair3_s0 5 * pair3_s0 4 * b) _

def pair3_D : List (Fin 6 → SignType) := [pair3_s0]
-- view w1 (line F015xF356), facings +0++----0
def pair3_swA : Fin 9 → SignType := ![1, 0, 1, 1, 1, -1, 1, -1, 0]
def pair3_RA : List (SVC.Rim 9 6) :=
  []
def pair3_EA : List (List (Fin 6 × Fin 6)) :=
  [triDec pair3_swA 0 1 4 3 0,
   triDec pair3_swA 5 2 4 5 7]
-- view x 4 - x 6 (line F1456xF346), facings +-+-+0+0-
def pair3_swB : Fin 9 → SignType := ![1, -1, 1, -1, 1, 0, 1, 0, -1]
def pair3_RB : List (SVC.Rim 9 6) :=
  [{ k := 4, c := ![0, 1, 3, 2], U := {0, 2, 4, 6}, Dn := {1, 3, 5, 7},
     sd := ![0, 0, 0, 0, 0, -1, 0, -1, 0] },
   { k := 5, c := ![0, 1, 4, 5, 2], U := {0, 2, 5, 7}, Dn := {1, 3, 8},
     sd := ![0, 0, 0, 0, 0, 1, 0, 1, 0] }]
def pair3_EB : List (List (Fin 6 × Fin 6)) :=
  [[(3, 5)],
   triDec pair3_swB 4 5 1 1 8]
def pair3_B2 : List (List (Fin 6)) :=
  [[0, 5, 3, 2, 4, 1],
   [1, 4, 2, 0, 5, 3],
   [1, 4, 2, 5, 0, 3],
   [1, 4, 2, 5, 3, 0],
   [2, 4, 1, 0, 5, 3],
   [2, 4, 1, 5, 0, 3],
   [2, 4, 1, 5, 3, 0],
   [2, 4, 5, 1, 0, 3],
   [2, 4, 5, 1, 3, 0],
   [4, 1, 2, 0, 5, 3],
   [4, 1, 2, 5, 0, 3],
   [4, 1, 2, 5, 3, 0],
   [4, 2, 1, 0, 5, 3],
   [4, 2, 1, 5, 0, 3],
   [4, 2, 1, 5, 3, 0],
   [4, 2, 5, 1, 0, 3],
   [4, 2, 5, 1, 3, 0],
   [5, 0, 3, 2, 4, 1],
   [5, 3, 0, 2, 4, 1]]

theorem pair3_check2 : check2 s0x_S29 pair3_P pair3_swB [] pair3_D pair3_EB pair3_RB pair3_B2 = true := by
  decide +kernel

theorem pair3_check1 : check1 s0x_S29 pair3_P pair3_swA [] pair3_D pair3_EA pair3_EB pair3_RA pair3_B2 = true := by
  decide +kernel

/-- **Pair `w1` + `x 4 - x 6` (lines F015xF356, F1456xF346)**, `PSVC.pair_closure`. -/
theorem lexAny_pair3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 1, w1⟫ = 0) (hw1Y : ⟪F.N 8, w1⟫ = 0)
    (hA012 : 0 < ⟪F.N 0, w1⟫)
    (hA035 : 0 < ⟪F.N 3, w1⟫)
    (hA1456 : ⟪F.N 5, w1⟫ < 0)
    (hA346 : ⟪F.N 7, w1⟫ < 0)
    (hB012 : 0 < ⟪F.N 0, x 4 - x 6⟫)
    (hB015 : ⟪F.N 1, x 4 - x 6⟫ < 0)
    (hB023 : 0 < ⟪F.N 2, x 4 - x 6⟫)
    (hB035 : ⟪F.N 3, x 4 - x 6⟫ < 0)
    (hS0 : PlaneSide x 1 3 4 0 5 < 0)
    (hgen1 : ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫)
    (hgen2 : ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 4 - x 6⟫ ≠ ⟪x j, x 4 - x 6⟫) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 3, 5, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair3_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hA012
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_pos hA035
    · exact sign_neg hA1456
    · exact sign_neg hA346
    · exact sign_eq_zero_iff.mpr hw1Y
  have hT1 : ∀ ρ ∈ pair3_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 3, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair3_EA, DecOK x pair3_P (w1) d := by
    intro d hd
    simp only [pair3_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair3_P pair3_swA 1 3 0 1 4 0 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1X
        (hs1 3 (by decide)) (hs1 0 (by decide))
    · exact decOK_tri F pair3_P pair3_swA 8 5 7 2 4 5 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1Y
        (hs1 5 (by decide)) (hs1 7 (by decide))
  have hf1 : ∀ ij ∈ ([] : List (Fin 6 × Fin 6)), ⟪x (pair3_P ij.2), w1⟫ < ⟪x (pair3_P ij.1), w1⟫ := (by simp)
  have hR1 := hR_two F pair3_swA pair3_RA 1 8 5 3 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hs2 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 4 - x 6⟫ = pair3_swB t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hB012
    · exact sign_neg hB015
    · exact sign_pos hB023
    · exact sign_neg hB035
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_pos (edge_pos F 6 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 7 (by decide) (by decide))
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hT2 : ∀ ρ ∈ pair3_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair3_EB, DecOK x pair3_P (x 4 - x 6) d := by
    intro d hd
    simp only [pair3_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair3_P 3 5
    · exact decOK_tri F pair3_P pair3_swB 5 1 8 5 1 4 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 4 - x 6) (edge_zero F 5 (by decide) (by decide))
        (hs2 1 (by decide)) (hs2 8 (by decide))
  have hf2 : ∀ ij ∈ ([] : List (Fin 6 × Fin 6)), ⟪x (pair3_P ij.2), x 4 - x 6⟫ < ⟪x (pair3_P ij.1), x 4 - x 6⟫ := (by simp)
  have hR2 := hR_two F pair3_swB pair3_RB 5 7 4 3 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hP : ∀ i, pair3_P i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective pair3_P := by decide
  have hD : ∀ s ∈ pair3_D, ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs
    simp only [pair3_D, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact pair3_dep0 F hS0
  exact pair_closure F pair3_P (w1) (x 4 - x 6) pair3_swA pair3_swB pair3_RA pair3_RB
    (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) (fun ρ hρ t ht => hs2 t (hT2 ρ hρ t ht)) hR1 hR2
    _ _ hf1 hf2 pair3_D hD pair3_EA pair3_EB hE1 hE2
    (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij)) (fun i j hij => hgen2 _ (hP i) _ (hP j) (hPi.ne hij))
    pair3_B2 pair3_check1 pair3_check2

/-! ### Pair instance `pair4`: single view F346xF356 (rep K1aG_49, census cover 33) -/

def pair4_P : Fin 5 → Fin 7 := ![0, 1, 4, 5, 6]
def pair4_s0 : Fin 5 → SignType := ![0, 1, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)

theorem pair4_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair4_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair4_s0 i := by
  have hP : Function.Injective (fun i => x (pair4_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair4_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F pair4_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F pair4_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F pair4_P mu hsum hdep 4 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F pair4_P mu hsum hdep 7 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F pair4_P mu hsum hdep 8 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = pair4_s0 0 * pair4_s0 4 * v6 ∧ v1 = pair4_s0 1 * pair4_s0 4 * v6 ∧ v4 = pair4_s0 2 * pair4_s0 4 * v6 ∧ v5 = pair4_s0 3 * pair4_s0 4 * v6 ∧ v6 = pair4_s0 4 * pair4_s0 4 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne pair4_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def pair4_D : List (Fin 5 → SignType) := [pair4_s0]
-- view x 3 - x 6 (line F346xF356), facings +++++-+00
def pair4_swA : Fin 9 → SignType := ![1, 1, 1, 1, 1, -1, 1, 0, 0]
def pair4_RA : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![1, 2, 4, 3], U := {1, 4, 7, 8}, Dn := {5},
     sd := ![0, 0, 0, 0, 0, 0, 0, 1, 1] }]
def pair4_EA : List (List (Fin 5 × Fin 5)) :=
  []
def pair4_B2 : List (List (Fin 5)) :=
  []

theorem pair4_check2 : check2 s0x_S29 pair4_P pair4_swA [] pair4_D pair4_EA pair4_RA pair4_B2 = true := by
  decide +kernel

theorem pair4_check1 : check1 s0x_S29 pair4_P pair4_swA [] pair4_D pair4_EA pair4_EA pair4_RA pair4_B2 = true := by
  decide +kernel

/-- **Single view `x 3 - x 6` (line F346xF356)**, `PSVC.pair_closure`. -/
theorem lexAny_pair4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hA015 : 0 < ⟪F.N 1, x 3 - x 6⟫)
    (hA124 : 0 < ⟪F.N 4, x 3 - x 6⟫)
    (hgen1 : ∀ i ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({1, 4, 5, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 3 - x 6⟫ = pair4_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hA015
    · exact sign_pos hA124
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 7 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 8 (by decide) (by decide))
  have hT1 : ∀ ρ ∈ pair4_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 4, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair4_EA, DecOK x pair4_P (x 3 - x 6) d := by
    simp [pair4_EA]
  have hf1 : ∀ ij ∈ ([] : List (Fin 5 × Fin 5)), ⟪x (pair4_P ij.2), x 3 - x 6⟫ < ⟪x (pair4_P ij.1), x 3 - x 6⟫ := (by simp)
  have hR1 := hR_two F pair4_swA pair4_RA 7 8 3 5 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hP : ∀ i, pair4_P i ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective pair4_P := by decide
  have hD : ∀ s ∈ pair4_D, ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair4_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs
    simp only [pair4_D, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact pair4_dep0 F
  exact pair_closure F pair4_P (x 3 - x 6) (x 3 - x 6) pair4_swA pair4_swA pair4_RA pair4_RA
    (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) hR1 hR1
    _ _ hf1 hf1 pair4_D hD pair4_EA pair4_EA hE1 hE1
    (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij)) (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij))
    pair4_B2 pair4_check1 pair4_check2

/-! ### Pair instance `pair6`: single view F015xF023 (rep K1aN_572, census cover 22) -/

def pair6_P : Fin 5 → Fin 7 := ![0, 1, 2, 3, 5]

def pair6_D : List (Fin 5 → SignType) := []
-- view w1 (line F015xF023), facings +00------
def pair6_swA : Fin 9 → SignType := ![1, 0, 0, -1, -1, -1, -1, 1, 1]
def pair6_RA : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 2, 1, 4], U := {0, 1}, Dn := {2, 3, 4, 5},
     sd := ![0, 1, -1, 0, 0, 0, 0, 0, 0] },
   { k := 4, c := ![0, 1, 2, 3], U := {0, 2}, Dn := {1, 3, 4, 6},
     sd := ![0, -1, 1, 0, 0, 0, 0, 0, 0] }]
def pair6_EA : List (List (Fin 5 × Fin 5)) :=
  [triDec pair6_swA 4 0 1 5 3,
   triDec pair6_swA 3 0 2 6 3]
def pair6_B2 : List (List (Fin 5)) :=
  []

theorem pair6_check2 : check2 s0x_S29 pair6_P pair6_swA [] pair6_D pair6_EA pair6_RA pair6_B2 = true := by
  decide +kernel

theorem pair6_check1 : check1 s0x_S29 pair6_P pair6_swA [] pair6_D pair6_EA pair6_EA pair6_RA pair6_B2 = true := by
  decide +kernel

/-- **Single view `w1` with SELF (line F015xF023)**, `PSVC.pair_closure`. -/
theorem lexAny_pair6 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 1, w1⟫ = 0) (hw1Y : ⟪F.N 2, w1⟫ = 0)
    (hA012 : 0 < ⟪F.N 0, w1⟫)
    (hA035 : ⟪F.N 3, w1⟫ < 0)
    (hA124 : ⟪F.N 4, w1⟫ < 0)
    (hA1456 : ⟪F.N 5, w1⟫ < 0)
    (hA234 : ⟪F.N 6, w1⟫ < 0)
    (hgen1 : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair6_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hA012
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_eq_zero_iff.mpr hw1Y
    · exact sign_neg hA035
    · exact sign_neg hA124
    · exact sign_neg hA1456
    · exact sign_neg hA234
  have hT1 : ∀ ρ ∈ pair6_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair6_EA, DecOK x pair6_P (w1) d := by
    intro d hd
    simp only [pair6_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair6_P pair6_swA 1 5 3 0 1 4 2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1X
        (hs1 5 (by decide)) (hs1 3 (by decide))
    · exact decOK_tri F pair6_P pair6_swA 2 6 3 0 2 3 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1Y
        (hs1 6 (by decide)) (hs1 3 (by decide))
  have hf1 : ∀ ij ∈ ([] : List (Fin 5 × Fin 5)), ⟪x (pair6_P ij.2), w1⟫ < ⟪x (pair6_P ij.1), w1⟫ := (by simp)
  have hR1 := hR_two F pair6_swA pair6_RA 1 2 0 2 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hP : ∀ i, pair6_P i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective pair6_P := by decide
  have hD : ∀ s ∈ pair6_D, ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair6_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    simp [pair6_D]
  exact pair_closure F pair6_P (w1) (w1) pair6_swA pair6_swA pair6_RA pair6_RA
    (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) hR1 hR1
    _ _ hf1 hf1 pair6_D hD pair6_EA pair6_EA hE1 hE1
    (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij)) (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij))
    pair6_B2 pair6_check1 pair6_check2

/-! ### Normal form `NF29` -/

/-- **NF29 form of `lexAny_pair1`**. -/
theorem lexAny29_pair1 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.a2 < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 0, lv29 N 4 7⟫ < 0)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 5, lv29 N 4 7⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 6, lv29 N 4 7⟫ < 0)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 8, lv29 N 4 7⟫)
    (h6 : 0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫)
    (h7 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫)
    (h8 : ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0)
    (h9 : ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0)
    (h10 : (∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, lv29 N 4 7⟫ ≠ ⟪x j, lv29 N 4 7⟫))
    (h11 : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_pair1 _ (lv29 N 4 7) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h2 h3 h4 h5 h6 h7 h8 h9 (ps23514_pos N h1) h10 h11

/-- **NF29 form of `lexAny_pair3`**. -/
theorem lexAny29_pair3 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 0, lv29 N 1 8⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 3, lv29 N 1 8⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 5, lv29 N 1 8⟫ < 0)
    (h5 : ⟪(s0x_fac29 N.facets).N 7, lv29 N 1 8⟫ < 0)
    (h6 : 0 < ⟪(s0x_fac29 N.facets).N 0, x 4 - x 6⟫)
    (h7 : ⟪(s0x_fac29 N.facets).N 1, x 4 - x 6⟫ < 0)
    (h8 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 4 - x 6⟫)
    (h9 : ⟪(s0x_fac29 N.facets).N 3, x 4 - x 6⟫ < 0)
    (h10 : (∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, lv29 N 1 8⟫ ≠ ⟪x j, lv29 N 1 8⟫))
    (h11 : ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 4 - x 6⟫ ≠ ⟪x j, x 4 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_pair3 _ (lv29 N 1 8) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h2 h3 h4 h5 h6 h7 h8 h9 (ps13405_neg N h1) h10 h11

/-- **NF29 form of `lexAny_pair4`**. -/
theorem lexAny29_pair4 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < ⟪(s0x_fac29 N.facets).N 1, x 3 - x 6⟫)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 4, x 3 - x 6⟫)
    (h3 : ∀ i ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_pair4 _ h1 h2 h3

/-- **NF29 form of `lexAny_pair6`**. -/
theorem lexAny29_pair6 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < ⟪(s0x_fac29 N.facets).N 0, lv29 N 1 2⟫)
    (h2 : ⟪(s0x_fac29 N.facets).N 3, lv29 N 1 2⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 4, lv29 N 1 2⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 5, lv29 N 1 2⟫ < 0)
    (h5 : ⟪(s0x_fac29 N.facets).N 6, lv29 N 1 2⟫ < 0)
    (h6 : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, lv29 N 1 2⟫ ≠ ⟪x j, lv29 N 1 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_pair6 _ (lv29 N 1 2) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h1 h2 h3 h4 h5 h6

end Minimality.PL29
