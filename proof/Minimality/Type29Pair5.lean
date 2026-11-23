module

public import Minimality.Type29Pair

@[expose] public section

/-!
# Type 29: pair instance `pair5` (PAIR29)

Views `cross N035 N346` and `x 1 - x 4` (lines F035xF346, F124xF1456), K1a. Seven points: both
kernel checks are split by the lowest point of the order (`perms7_split`, `Type29Pair.lean`).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

/-! ### Pair instance `pair5`: F035xF346 + F124xF1456 (rep K1aN_324, census cover 27) -/

def pair5_P : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6]
def pair5_s0 : Fin 7 → SignType := ![1, -1, 0, -1, 1, -1, 0]  -- circuit +-0-+-0
def pair5_s1 : Fin 7 → SignType := ![0, 1, -1, 1, 1, 0, -1]  -- circuit 0+-++0-

theorem pair5_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5) :
    ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair5_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair5_s0 i := by
  have hP : Function.Injective (fun i => x (pair5_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair5_P hP ({0, 1, 3, 4, 5} : Finset (Fin 7)) (by decide)
  have r0 := facet_pair F pair5_P mu hsum hdep 1 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F pair5_P mu hsum hdep 3 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r2 := facet_pair F pair5_P mu hsum hdep 5 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (pair5_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 5) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v0 v1 v3 v4 v5 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = -v5 →
     v0 = pair5_s0 0 * pair5_s0 5 * v5 ∧ v1 = pair5_s0 1 * pair5_s0 5 * v5 ∧ v3 = pair5_s0 3 * pair5_s0 5 * v5 ∧ v4 = pair5_s0 4 * pair5_s0 5 * v5 ∧ v5 = pair5_s0 5 * pair5_s0 5 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne pair5_s0 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair5_s0 2 * pair5_s0 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair5_s0 6 * pair5_s0 5 * b) _

theorem pair5_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS1 : PlaneSide x 2 3 6 1 4 < 0) :
    ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair5_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair5_s1 i := by
  have hP : Function.Injective (fun i => x (pair5_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair5_P hP ({1, 2, 3, 4, 6} : Finset (Fin 7)) (by decide)
  have r0 := facet_pair F pair5_P mu hsum hdep 4 (i := 3) (j := 6) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    )
  have r1 := facet_pair F pair5_P mu hsum hdep 5 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r2 := facet_pair F pair5_P mu hsum hdep 6 (i := 1) (j := 6) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    )
  have r3 := facet_pair F pair5_P mu hsum hdep 7 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    )
  have r4 := (sign_rel_opp (plane_rel0 (fun i => x (pair5_P i)) mu hsum hdep (x 3 - x 2) (x 6 - x 2) (x 2) (i := 1) (j := 4) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 2) (x 6 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 6 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    · left; show det3 (x 3 - x 2) (x 6 - x 2) (x 6 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS1)
  have key : ∀ v1 v2 v3 v4 v6 : SignType, v3 = -v6 → v2 = -v3 → v1 = -v6 → v1 = -v2 → v1 = v4 →
     v1 = pair5_s1 1 * pair5_s1 6 * v6 ∧ v2 = pair5_s1 2 * pair5_s1 6 * v6 ∧ v3 = pair5_s1 3 * pair5_s1 6 * v6 ∧ v4 = pair5_s1 4 * pair5_s1 6 * v6 ∧ v6 = pair5_s1 6 * pair5_s1 6 * v6 := by decide
  have hk := key (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 6)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne pair5_s1 6 (by decide) (fun i => ?_)
  fin_cases i
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair5_s1 0 * pair5_s1 6 * b) _
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair5_s1 5 * pair5_s1 6 * b) _
  · exact hk.2.2.2.2

def pair5_D : List (Fin 7 → SignType) := [pair5_s0, pair5_s1]
-- view w1 (line F035xF346), facings +-+0+-+0-
def pair5_swA : Fin 9 → SignType := ![1, -1, 1, 0, 1, -1, 1, 0, -1]
def pair5_RA : List (SVC.Rim 9 7) :=
  [{ k := 4, c := ![0, 1, 4, 3], U := {0, 2, 4, 6}, Dn := {1, 3, 5, 7},
     sd := ![0, 0, 0, -1, 0, 0, 0, -1, 0] }]
def pair5_EA : List (List (Fin 7 × Fin 7)) :=
  [triDec pair5_swA 5 0 3 8 1,
   triDec pair5_swA 6 3 4 5 8]
-- view x 1 - x 4 (line F124xF1456), facings ++++00--+
def pair5_swB : Fin 9 → SignType := ![1, 1, 1, 1, 0, 0, -1, -1, 1]
def pair5_RB : List (SVC.Rim 9 7) :=
  [{ k := 4, c := ![2, 3, 6, 4], U := {2, 4, 5, 8}, Dn := {6, 7},
     sd := ![0, 0, 0, 0, 1, 1, 0, 0, 0] }]
def pair5_EB : List (List (Fin 7 × Fin 7)) :=
  [[(1, 4)],
   triDec pair5_swB 5 6 1 1 8]
def pair5_B2 : List (List (Fin 7)) :=
  [[0, 3, 4, 2, 1, 5, 6],
   [0, 3, 4, 2, 1, 6, 5],
   [0, 3, 4, 2, 6, 1, 5],
   [0, 3, 4, 2, 6, 5, 1],
   [0, 3, 4, 6, 1, 2, 5],
   [0, 3, 4, 6, 1, 5, 2],
   [0, 3, 4, 6, 2, 1, 5],
   [0, 3, 4, 6, 2, 5, 1],
   [0, 3, 4, 6, 5, 1, 2],
   [0, 3, 4, 6, 5, 2, 1],
   [3, 0, 4, 2, 1, 5, 6],
   [3, 0, 4, 2, 1, 6, 5],
   [3, 0, 4, 2, 6, 1, 5],
   [3, 0, 4, 2, 6, 5, 1],
   [3, 0, 4, 6, 1, 2, 5],
   [3, 0, 4, 6, 1, 5, 2],
   [3, 0, 4, 6, 2, 1, 5],
   [3, 0, 4, 6, 2, 5, 1],
   [3, 0, 4, 6, 5, 1, 2],
   [3, 0, 4, 6, 5, 2, 1],
   [3, 4, 0, 2, 1, 5, 6],
   [3, 4, 0, 2, 1, 6, 5],
   [3, 4, 0, 2, 6, 1, 5],
   [3, 4, 0, 2, 6, 5, 1],
   [3, 4, 0, 6, 1, 2, 5],
   [3, 4, 0, 6, 1, 5, 2],
   [3, 4, 0, 6, 2, 1, 5],
   [3, 4, 0, 6, 2, 5, 1],
   [3, 4, 0, 6, 5, 1, 2],
   [3, 4, 0, 6, 5, 2, 1],
   [3, 4, 2, 0, 1, 5, 6],
   [3, 4, 2, 0, 1, 6, 5],
   [3, 4, 2, 0, 6, 1, 5],
   [3, 4, 2, 0, 6, 5, 1],
   [3, 4, 2, 1, 0, 5, 6],
   [3, 4, 2, 1, 0, 6, 5],
   [3, 4, 2, 1, 5, 0, 6],
   [3, 4, 2, 1, 5, 6, 0],
   [3, 4, 2, 1, 6, 0, 5],
   [3, 4, 2, 1, 6, 5, 0],
   [3, 4, 2, 6, 0, 1, 5],
   [3, 4, 2, 6, 0, 5, 1],
   [3, 4, 2, 6, 1, 0, 5],
   [3, 4, 2, 6, 1, 5, 0],
   [3, 4, 2, 6, 5, 0, 1],
   [3, 4, 2, 6, 5, 1, 0],
   [3, 4, 6, 0, 1, 2, 5],
   [3, 4, 6, 0, 1, 5, 2],
   [3, 4, 6, 0, 2, 1, 5],
   [3, 4, 6, 0, 2, 5, 1],
   [3, 4, 6, 0, 5, 1, 2],
   [3, 4, 6, 0, 5, 2, 1],
   [3, 4, 6, 1, 0, 2, 5],
   [3, 4, 6, 1, 0, 5, 2],
   [3, 4, 6, 1, 2, 0, 5],
   [3, 4, 6, 1, 2, 5, 0],
   [3, 4, 6, 1, 5, 0, 2],
   [3, 4, 6, 1, 5, 2, 0],
   [3, 4, 6, 2, 0, 1, 5],
   [3, 4, 6, 2, 0, 5, 1],
   [3, 4, 6, 2, 1, 0, 5],
   [3, 4, 6, 2, 1, 5, 0],
   [3, 4, 6, 2, 5, 0, 1],
   [3, 4, 6, 2, 5, 1, 0],
   [3, 4, 6, 5, 0, 1, 2],
   [3, 4, 6, 5, 0, 2, 1],
   [3, 4, 6, 5, 1, 0, 2],
   [3, 4, 6, 5, 1, 2, 0],
   [3, 4, 6, 5, 2, 0, 1],
   [3, 4, 6, 5, 2, 1, 0],
   [4, 3, 0, 2, 1, 5, 6],
   [4, 3, 0, 2, 1, 6, 5],
   [4, 3, 0, 2, 6, 1, 5],
   [4, 3, 0, 2, 6, 5, 1],
   [4, 3, 0, 6, 1, 2, 5],
   [4, 3, 0, 6, 1, 5, 2],
   [4, 3, 0, 6, 2, 1, 5],
   [4, 3, 0, 6, 2, 5, 1],
   [4, 3, 0, 6, 5, 1, 2],
   [4, 3, 0, 6, 5, 2, 1],
   [4, 3, 2, 0, 1, 5, 6],
   [4, 3, 2, 0, 1, 6, 5],
   [4, 3, 2, 0, 6, 1, 5],
   [4, 3, 2, 0, 6, 5, 1],
   [4, 3, 2, 1, 0, 5, 6],
   [4, 3, 2, 1, 0, 6, 5],
   [4, 3, 2, 1, 5, 0, 6],
   [4, 3, 2, 1, 5, 6, 0],
   [4, 3, 2, 1, 6, 0, 5],
   [4, 3, 2, 1, 6, 5, 0],
   [4, 3, 2, 6, 0, 1, 5],
   [4, 3, 2, 6, 0, 5, 1],
   [4, 3, 2, 6, 1, 0, 5],
   [4, 3, 2, 6, 1, 5, 0],
   [4, 3, 2, 6, 5, 0, 1],
   [4, 3, 2, 6, 5, 1, 0],
   [4, 3, 6, 0, 1, 2, 5],
   [4, 3, 6, 0, 1, 5, 2],
   [4, 3, 6, 0, 2, 1, 5],
   [4, 3, 6, 0, 2, 5, 1],
   [4, 3, 6, 0, 5, 1, 2],
   [4, 3, 6, 0, 5, 2, 1],
   [4, 3, 6, 1, 0, 2, 5],
   [4, 3, 6, 1, 0, 5, 2],
   [4, 3, 6, 1, 2, 0, 5],
   [4, 3, 6, 1, 2, 5, 0],
   [4, 3, 6, 1, 5, 0, 2],
   [4, 3, 6, 1, 5, 2, 0],
   [4, 3, 6, 2, 0, 1, 5],
   [4, 3, 6, 2, 0, 5, 1],
   [4, 3, 6, 2, 1, 0, 5],
   [4, 3, 6, 2, 1, 5, 0],
   [4, 3, 6, 2, 5, 0, 1],
   [4, 3, 6, 2, 5, 1, 0],
   [4, 3, 6, 5, 0, 1, 2],
   [4, 3, 6, 5, 0, 2, 1],
   [4, 3, 6, 5, 1, 0, 2],
   [4, 3, 6, 5, 1, 2, 0],
   [4, 3, 6, 5, 2, 0, 1],
   [4, 3, 6, 5, 2, 1, 0]]

theorem pair5_c2_0 : (((List.finRange 7).erase 0).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EB (0 :: L) || pair5_RB.any (fun ρ => SVC.rimOK ρ (0 :: L)) ||
      pair5_B2.contains (0 :: L)) = true := by
  decide +kernel

theorem pair5_c2_1 : (((List.finRange 7).erase 1).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EB (1 :: L) || pair5_RB.any (fun ρ => SVC.rimOK ρ (1 :: L)) ||
      pair5_B2.contains (1 :: L)) = true := by
  decide +kernel

theorem pair5_c2_2 : (((List.finRange 7).erase 2).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EB (2 :: L) || pair5_RB.any (fun ρ => SVC.rimOK ρ (2 :: L)) ||
      pair5_B2.contains (2 :: L)) = true := by
  decide +kernel

theorem pair5_c2_3 : (((List.finRange 7).erase 3).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EB (3 :: L) || pair5_RB.any (fun ρ => SVC.rimOK ρ (3 :: L)) ||
      pair5_B2.contains (3 :: L)) = true := by
  decide +kernel

theorem pair5_c2_4 : (((List.finRange 7).erase 4).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EB (4 :: L) || pair5_RB.any (fun ρ => SVC.rimOK ρ (4 :: L)) ||
      pair5_B2.contains (4 :: L)) = true := by
  decide +kernel

theorem pair5_c2_5 : (((List.finRange 7).erase 5).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EB (5 :: L) || pair5_RB.any (fun ρ => SVC.rimOK ρ (5 :: L)) ||
      pair5_B2.contains (5 :: L)) = true := by
  decide +kernel

theorem pair5_c2_6 : (((List.finRange 7).erase 6).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EB (6 :: L) || pair5_RB.any (fun ρ => SVC.rimOK ρ (6 :: L)) ||
      pair5_B2.contains (6 :: L)) = true := by
  decide +kernel

theorem pair5_check2 : check2 s0x_S29 pair5_P pair5_swB [] pair5_D pair5_EB pair5_RB pair5_B2 = true := by
  simp only [check2, Bool.and_eq_true]
  refine ⟨by decide +kernel, perms7_split _ (fun a => ?_)⟩
  fin_cases a
  · exact pair5_c2_0
  · exact pair5_c2_1
  · exact pair5_c2_2
  · exact pair5_c2_3
  · exact pair5_c2_4
  · exact pair5_c2_5
  · exact pair5_c2_6

theorem pair5_c1_0 : (((List.finRange 7).erase 0).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EA (0 :: L) || pair5_RA.any (fun ρ => SVC.rimOK ρ (0 :: L)) ||
      pair5_B2.all (gramBad pair5_EA pair5_EB (0 :: L))) = true := by
  decide +kernel

theorem pair5_c1_1 : (((List.finRange 7).erase 1).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EA (1 :: L) || pair5_RA.any (fun ρ => SVC.rimOK ρ (1 :: L)) ||
      pair5_B2.all (gramBad pair5_EA pair5_EB (1 :: L))) = true := by
  decide +kernel

theorem pair5_c1_2 : (((List.finRange 7).erase 2).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EA (2 :: L) || pair5_RA.any (fun ρ => SVC.rimOK ρ (2 :: L)) ||
      pair5_B2.all (gramBad pair5_EA pair5_EB (2 :: L))) = true := by
  decide +kernel

theorem pair5_c1_3 : (((List.finRange 7).erase 3).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EA (3 :: L) || pair5_RA.any (fun ρ => SVC.rimOK ρ (3 :: L)) ||
      pair5_B2.all (gramBad pair5_EA pair5_EB (3 :: L))) = true := by
  decide +kernel

theorem pair5_c1_4 : (((List.finRange 7).erase 4).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EA (4 :: L) || pair5_RA.any (fun ρ => SVC.rimOK ρ (4 :: L)) ||
      pair5_B2.all (gramBad pair5_EA pair5_EB (4 :: L))) = true := by
  decide +kernel

theorem pair5_c1_5 : (((List.finRange 7).erase 5).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EA (5 :: L) || pair5_RA.any (fun ρ => SVC.rimOK ρ (5 :: L)) ||
      pair5_B2.all (gramBad pair5_EA pair5_EB (5 :: L))) = true := by
  decide +kernel

theorem pair5_c1_6 : (((List.finRange 7).erase 6).permutations'.all fun L =>
    exclOK [] pair5_D pair5_EA (6 :: L) || pair5_RA.any (fun ρ => SVC.rimOK ρ (6 :: L)) ||
      pair5_B2.all (gramBad pair5_EA pair5_EB (6 :: L))) = true := by
  decide +kernel

theorem pair5_check1 : check1 s0x_S29 pair5_P pair5_swA [] pair5_D pair5_EA pair5_EB pair5_RA pair5_B2 = true := by
  simp only [check1, Bool.and_eq_true]
  refine ⟨by decide +kernel, perms7_split _ (fun a => ?_)⟩
  fin_cases a
  · exact pair5_c1_0
  · exact pair5_c1_1
  · exact pair5_c1_2
  · exact pair5_c1_3
  · exact pair5_c1_4
  · exact pair5_c1_5
  · exact pair5_c1_6

/-- **Pair `w1` + `x 1 - x 4` (lines F035xF346, F124xF1456)**, `PSVC.pair_closure`. -/
theorem lexAny_pair5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w1 : ℝ³) (hw1X : ⟪F.N 3, w1⟫ = 0) (hw1Y : ⟪F.N 7, w1⟫ = 0)
    (hA012 : 0 < ⟪F.N 0, w1⟫)
    (hA015 : ⟪F.N 1, w1⟫ < 0)
    (hA023 : 0 < ⟪F.N 2, w1⟫)
    (hA124 : 0 < ⟪F.N 4, w1⟫)
    (hA1456 : ⟪F.N 5, w1⟫ < 0)
    (hA234 : 0 < ⟪F.N 6, w1⟫)
    (hA356 : ⟪F.N 8, w1⟫ < 0)
    (hB023 : 0 < ⟪F.N 2, x 1 - x 4⟫)
    (hB356 : 0 < ⟪F.N 8, x 1 - x 4⟫)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5)
    (hS1 : PlaneSide x 2 3 6 1 4 < 0)
    (hgen1 : ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫)
    (hgen2 : ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, w1⟫ = pair5_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos hA012
    · exact sign_neg hA015
    · exact sign_pos hA023
    · exact sign_eq_zero_iff.mpr hw1X
    · exact sign_pos hA124
    · exact sign_neg hA1456
    · exact sign_pos hA234
    · exact sign_eq_zero_iff.mpr hw1Y
    · exact sign_neg hA356
  have hT1 : ∀ ρ ∈ pair5_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair5_EA, DecOK x pair5_P (w1) d := by
    intro d hd
    simp only [pair5_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_tri F pair5_P pair5_swA 3 8 1 0 3 5 1 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1X
        (hs1 8 (by decide)) (hs1 1 (by decide))
    · exact decOK_tri F pair5_P pair5_swA 7 5 8 3 4 6 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (w1) hw1Y
        (hs1 5 (by decide)) (hs1 8 (by decide))
  have hf1 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair5_P ij.2), w1⟫ < ⟪x (pair5_P ij.1), w1⟫ := (by simp)
  have hR1 := hR_two F pair5_swA pair5_RA 3 7 3 4 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hs2 : ∀ t ∈ ({1, 2, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 1 - x 4⟫ = pair5_swB t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos hB023
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_pos hB356
  have hT2 : ∀ ρ ∈ pair5_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 2, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair5_EB, DecOK x pair5_P (x 1 - x 4) d := by
    intro d hd
    simp only [pair5_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair5_P 1 4
    · exact decOK_tri F pair5_P pair5_swB 5 1 8 6 1 5 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 1 - x 4) (edge_zero F 5 (by decide) (by decide))
        (hs2 1 (by decide)) (hs2 8 (by decide))
  have hf2 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair5_P ij.2), x 1 - x 4⟫ < ⟪x (pair5_P ij.1), x 1 - x 4⟫ := (by simp)
  have hR2 := hR_two F pair5_swB pair5_RB 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hP : ∀ i, pair5_P i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective pair5_P := by decide
  have hD : ∀ s ∈ pair5_D, ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair5_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs
    simp only [pair5_D, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact pair5_dep0 F hS0
    · exact pair5_dep1 F hS1
  exact pair_closure F pair5_P (w1) (x 1 - x 4) pair5_swA pair5_swB pair5_RA pair5_RB
    (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) (fun ρ hρ t ht => hs2 t (hT2 ρ hρ t ht)) hR1 hR2
    _ _ hf1 hf2 pair5_D hD pair5_EA pair5_EB hE1 hE2
    (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij)) (fun i j hij => hgen2 _ (hP i) _ (hP j) (hPi.ne hij))
    pair5_B2 pair5_check1 pair5_check2

/-! ### Normal form `NF29` -/

/-- **NF29 form of `lexAny_pair5`**. -/
theorem lexAny29_pair5 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 0, lv29 N 3 7⟫)
    (h3 : ⟪(s0x_fac29 N.facets).N 1, lv29 N 3 7⟫ < 0)
    (h4 : 0 < ⟪(s0x_fac29 N.facets).N 2, lv29 N 3 7⟫)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 4, lv29 N 3 7⟫)
    (h6 : ⟪(s0x_fac29 N.facets).N 5, lv29 N 3 7⟫ < 0)
    (h7 : 0 < ⟪(s0x_fac29 N.facets).N 6, lv29 N 3 7⟫)
    (h8 : ⟪(s0x_fac29 N.facets).N 8, lv29 N 3 7⟫ < 0)
    (h9 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫)
    (h10 : 0 < ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫)
    (h11 : PlaneSide x 2 3 6 1 4 < 0)
    (h12 : (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, lv29 N 3 7⟫ ≠ ⟪x j, lv29 N 3 7⟫))
    (h13 : ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_pair5 _ (lv29 N 3 7) (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h2 h3 h4 h5 h6 h7 h8 h9 h10 (ps13405_pos N h1) h11 h12 h13

end Minimality.PL29
