module

public import Minimality.Type29Pair

@[expose] public section

/-!
# Type 29: pair instance `pair2` (PAIR29)

Views `x 1 - x 2` (line F012xF124) and `x 5 - x 6` (line F1456xF356), K1a with `N.V < 0`, three
genuine plane-side conditions. Seven points: both kernel checks are split by the lowest point of
the order (`perms7_split`, `Type29Pair.lean`).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

/-! ### Pair instance `pair2`: F012xF124 + F1456xF356 (rep K1aG_49, census cover 116) -/

def pair2_P : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6]
def pair2_s0 : Fin 7 → SignType := ![1, -1, -1, 0, 1, -1, 0]  -- circuit +--0+-0
def pair2_s1 : Fin 7 → SignType := ![1, -1, -1, 0, 0, -1, 1]  -- circuit +--00-+
def pair2_s2 : Fin 7 → SignType := ![0, 1, -1, 1, 0, -1, -1]  -- circuit 0+-+0--

theorem pair2_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 2 4 5 0 1) :
    ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair2_s0 i := by
  have hP : Function.Injective (fun i => x (pair2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair2_P hP ({0, 1, 2, 4, 5} : Finset (Fin 7)) (by decide)
  have r0 := facet_pair F pair2_P mu hsum hdep 0 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F pair2_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r2 := facet_pair F pair2_P mu hsum hdep 4 (i := 0) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r3 := facet_pair F pair2_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_same (plane_rel0 (fun i => x (pair2_P i)) mu hsum hdep (x 4 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 4 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v0 v1 v2 v4 v5 : SignType, v4 = -v5 → v2 = -v4 → v0 = -v5 → v0 = -v2 → v0 = -v1 →
     v0 = pair2_s0 0 * pair2_s0 5 * v5 ∧ v1 = pair2_s0 1 * pair2_s0 5 * v5 ∧ v2 = pair2_s0 2 * pair2_s0 5 * v5 ∧ v4 = pair2_s0 4 * pair2_s0 5 * v5 ∧ v5 = pair2_s0 5 * pair2_s0 5 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne pair2_s0 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair2_s0 3 * pair2_s0 5 * b) _
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair2_s0 6 * pair2_s0 5 * b) _

theorem pair2_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS1 : 0 < PlaneSide x 2 5 6 0 1) :
    ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair2_s1 i := by
  have hP : Function.Injective (fun i => x (pair2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair2_P hP ({0, 1, 2, 5, 6} : Finset (Fin 7)) (by decide)
  have r0 := facet_pair F pair2_P mu hsum hdep 0 (i := 5) (j := 6) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F pair2_P mu hsum hdep 1 (i := 2) (j := 6) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F pair2_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (pair2_P i)) mu hsum hdep (x 5 - x 2) (x 6 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 5 - x 2) (x 6 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    · right; exact hz _ (by decide)
    · left; show det3 (x 5 - x 2) (x 6 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 5 - x 2) (x 6 - x 2) (x 6 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS1)
  have key : ∀ v0 v1 v2 v5 v6 : SignType, v5 = -v6 → v2 = -v6 → v0 = -v2 → v0 = -v1 →
     v0 = pair2_s1 0 * pair2_s1 6 * v6 ∧ v1 = pair2_s1 1 * pair2_s1 6 * v6 ∧ v2 = pair2_s1 2 * pair2_s1 6 * v6 ∧ v5 = pair2_s1 5 * pair2_s1 6 * v6 ∧ v6 = pair2_s1 6 * pair2_s1 6 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 5)) (SignType.sign (mu 6)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne pair2_s1 6 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair2_s1 3 * pair2_s1 6 * b) _
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair2_s1 4 * pair2_s1 6 * b) _
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem pair2_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS2 : 0 < PlaneSide x 2 3 6 1 5)
    (hS3 : 0 < PlaneSide x 2 3 5 1 6) :
    ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = pair2_s2 i := by
  have hP : Function.Injective (fun i => x (pair2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep pair2_P hP ({1, 2, 3, 5, 6} : Finset (Fin 7)) (by decide)
  have r0 := facet_pair F pair2_P mu hsum hdep 5 (i := 2) (j := 3) (by decide) (by decide) (by decide)
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
  have r1 := facet_pair F pair2_P mu hsum hdep 8 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    )
  have r2 := (sign_rel_same (plane_rel0 (fun i => x (pair2_P i)) mu hsum hdep (x 3 - x 2) (x 6 - x 2) (x 2) (i := 1) (j := 5) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 2) (x 6 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 6 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 6 - x 2) (x 6 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS2)
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (pair2_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 1) (j := 6) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    )) hS3)
  have key : ∀ v1 v2 v3 v5 v6 : SignType, v2 = -v3 → v1 = -v2 → v1 = -v5 → v1 = -v6 →
     v1 = pair2_s2 1 * pair2_s2 6 * v6 ∧ v2 = pair2_s2 2 * pair2_s2 6 * v6 ∧ v3 = pair2_s2 3 * pair2_s2 6 * v6 ∧ v5 = pair2_s2 5 * pair2_s2 6 * v6 ∧ v6 = pair2_s2 6 * pair2_s2 6 * v6 := by decide
  have hk := key (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 5)) (SignType.sign (mu 6)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne pair2_s2 6 (by decide) (fun i => ?_)
  fin_cases i
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair2_s2 0 * pair2_s2 6 * b) _
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = pair2_s2 4 * pair2_s2 6 * b) _
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def pair2_D : List (Fin 7 → SignType) := [pair2_s0, pair2_s1, pair2_s2]
-- view x 1 - x 2 (line F012xF124), facings 0+--0+---
def pair2_swA : Fin 9 → SignType := ![0, 1, 1, -1, 0, 1, 1, -1, -1]
def pair2_RA : List (SVC.Rim 9 7) :=
  [{ k := 5, c := ![0, 1, 4, 6, 5], U := {1, 5}, Dn := {0, 3, 4, 7, 8},
     sd := ![-1, 0, 0, 0, -1, 0, 0, 0, 0] }]
def pair2_EA : List (List (Fin 7 × Fin 7)) :=
  [[(1, 2)]]
-- view x 5 - x 6 (line F1456xF356), facings ++++-0--0
def pair2_swB : Fin 9 → SignType := ![1, 1, 1, 1, -1, 0, -1, -1, 0]
def pair2_RB : List (SVC.Rim 9 7) :=
  [{ k := 4, c := ![1, 2, 3, 5], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![0, 0, 0, 0, 0, -1, 0, 0, -1] }]
def pair2_EB : List (List (Fin 7 × Fin 7)) :=
  [[(5, 6)],
   triDec pair2_swB 4 1 6 7 4]
def pair2_B2 : List (List (Fin 7)) :=
  [[0, 1, 4, 6, 3, 2, 5],
   [0, 1, 4, 6, 3, 5, 2],
   [1, 0, 4, 6, 3, 2, 5],
   [1, 0, 4, 6, 3, 5, 2],
   [1, 4, 0, 6, 3, 2, 5],
   [1, 4, 0, 6, 3, 5, 2],
   [1, 4, 6, 0, 3, 2, 5],
   [1, 4, 6, 0, 3, 5, 2],
   [1, 4, 6, 3, 0, 2, 5],
   [1, 4, 6, 3, 0, 5, 2],
   [1, 4, 6, 3, 2, 0, 5],
   [1, 4, 6, 3, 2, 5, 0],
   [1, 4, 6, 3, 5, 0, 2],
   [1, 4, 6, 3, 5, 2, 0],
   [3, 4, 6, 1, 0, 2, 5],
   [3, 4, 6, 1, 0, 5, 2],
   [3, 4, 6, 1, 2, 0, 5],
   [3, 4, 6, 1, 2, 5, 0],
   [3, 4, 6, 1, 5, 0, 2],
   [3, 4, 6, 1, 5, 2, 0],
   [3, 6, 4, 1, 0, 2, 5],
   [3, 6, 4, 1, 0, 5, 2],
   [3, 6, 4, 1, 2, 0, 5],
   [3, 6, 4, 1, 2, 5, 0],
   [3, 6, 4, 1, 5, 0, 2],
   [3, 6, 4, 1, 5, 2, 0],
   [4, 1, 0, 6, 3, 2, 5],
   [4, 1, 0, 6, 3, 5, 2],
   [4, 1, 6, 0, 3, 2, 5],
   [4, 1, 6, 0, 3, 5, 2],
   [4, 1, 6, 3, 0, 2, 5],
   [4, 1, 6, 3, 0, 5, 2],
   [4, 1, 6, 3, 2, 0, 5],
   [4, 1, 6, 3, 2, 5, 0],
   [4, 1, 6, 3, 5, 0, 2],
   [4, 1, 6, 3, 5, 2, 0],
   [4, 3, 6, 1, 0, 2, 5],
   [4, 3, 6, 1, 0, 5, 2],
   [4, 3, 6, 1, 2, 0, 5],
   [4, 3, 6, 1, 2, 5, 0],
   [4, 3, 6, 1, 5, 0, 2],
   [4, 3, 6, 1, 5, 2, 0],
   [4, 6, 1, 0, 3, 2, 5],
   [4, 6, 1, 0, 3, 5, 2],
   [4, 6, 1, 3, 0, 2, 5],
   [4, 6, 1, 3, 0, 5, 2],
   [4, 6, 1, 3, 2, 0, 5],
   [4, 6, 1, 3, 2, 5, 0],
   [4, 6, 1, 3, 5, 0, 2],
   [4, 6, 1, 3, 5, 2, 0],
   [4, 6, 3, 1, 0, 2, 5],
   [4, 6, 3, 1, 0, 5, 2],
   [4, 6, 3, 1, 2, 0, 5],
   [4, 6, 3, 1, 2, 5, 0],
   [4, 6, 3, 1, 5, 0, 2],
   [4, 6, 3, 1, 5, 2, 0],
   [6, 3, 4, 1, 0, 2, 5],
   [6, 3, 4, 1, 0, 5, 2],
   [6, 3, 4, 1, 2, 0, 5],
   [6, 3, 4, 1, 2, 5, 0],
   [6, 3, 4, 1, 5, 0, 2],
   [6, 3, 4, 1, 5, 2, 0],
   [6, 4, 1, 0, 3, 2, 5],
   [6, 4, 1, 0, 3, 5, 2],
   [6, 4, 1, 3, 0, 2, 5],
   [6, 4, 1, 3, 0, 5, 2],
   [6, 4, 1, 3, 2, 0, 5],
   [6, 4, 1, 3, 2, 5, 0],
   [6, 4, 1, 3, 5, 0, 2],
   [6, 4, 1, 3, 5, 2, 0],
   [6, 4, 3, 1, 0, 2, 5],
   [6, 4, 3, 1, 0, 5, 2],
   [6, 4, 3, 1, 2, 0, 5],
   [6, 4, 3, 1, 2, 5, 0],
   [6, 4, 3, 1, 5, 0, 2],
   [6, 4, 3, 1, 5, 2, 0]]

theorem pair2_c2_0 : (((List.finRange 7).erase 0).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EB (0 :: L) || pair2_RB.any (fun ρ => SVC.rimOK ρ (0 :: L)) ||
      pair2_B2.contains (0 :: L)) = true := by
  decide +kernel

theorem pair2_c2_1 : (((List.finRange 7).erase 1).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EB (1 :: L) || pair2_RB.any (fun ρ => SVC.rimOK ρ (1 :: L)) ||
      pair2_B2.contains (1 :: L)) = true := by
  decide +kernel

theorem pair2_c2_2 : (((List.finRange 7).erase 2).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EB (2 :: L) || pair2_RB.any (fun ρ => SVC.rimOK ρ (2 :: L)) ||
      pair2_B2.contains (2 :: L)) = true := by
  decide +kernel

theorem pair2_c2_3 : (((List.finRange 7).erase 3).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EB (3 :: L) || pair2_RB.any (fun ρ => SVC.rimOK ρ (3 :: L)) ||
      pair2_B2.contains (3 :: L)) = true := by
  decide +kernel

theorem pair2_c2_4 : (((List.finRange 7).erase 4).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EB (4 :: L) || pair2_RB.any (fun ρ => SVC.rimOK ρ (4 :: L)) ||
      pair2_B2.contains (4 :: L)) = true := by
  decide +kernel

theorem pair2_c2_5 : (((List.finRange 7).erase 5).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EB (5 :: L) || pair2_RB.any (fun ρ => SVC.rimOK ρ (5 :: L)) ||
      pair2_B2.contains (5 :: L)) = true := by
  decide +kernel

theorem pair2_c2_6 : (((List.finRange 7).erase 6).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EB (6 :: L) || pair2_RB.any (fun ρ => SVC.rimOK ρ (6 :: L)) ||
      pair2_B2.contains (6 :: L)) = true := by
  decide +kernel

theorem pair2_check2 : check2 s0x_S29 pair2_P pair2_swB [] pair2_D pair2_EB pair2_RB pair2_B2 = true := by
  simp only [check2, Bool.and_eq_true]
  refine ⟨by decide +kernel, perms7_split _ (fun a => ?_)⟩
  fin_cases a
  · exact pair2_c2_0
  · exact pair2_c2_1
  · exact pair2_c2_2
  · exact pair2_c2_3
  · exact pair2_c2_4
  · exact pair2_c2_5
  · exact pair2_c2_6

theorem pair2_c1_0 : (((List.finRange 7).erase 0).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EA (0 :: L) || pair2_RA.any (fun ρ => SVC.rimOK ρ (0 :: L)) ||
      pair2_B2.all (gramBad pair2_EA pair2_EB (0 :: L))) = true := by
  decide +kernel

theorem pair2_c1_1 : (((List.finRange 7).erase 1).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EA (1 :: L) || pair2_RA.any (fun ρ => SVC.rimOK ρ (1 :: L)) ||
      pair2_B2.all (gramBad pair2_EA pair2_EB (1 :: L))) = true := by
  decide +kernel

theorem pair2_c1_2 : (((List.finRange 7).erase 2).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EA (2 :: L) || pair2_RA.any (fun ρ => SVC.rimOK ρ (2 :: L)) ||
      pair2_B2.all (gramBad pair2_EA pair2_EB (2 :: L))) = true := by
  decide +kernel

theorem pair2_c1_3 : (((List.finRange 7).erase 3).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EA (3 :: L) || pair2_RA.any (fun ρ => SVC.rimOK ρ (3 :: L)) ||
      pair2_B2.all (gramBad pair2_EA pair2_EB (3 :: L))) = true := by
  decide +kernel

theorem pair2_c1_4 : (((List.finRange 7).erase 4).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EA (4 :: L) || pair2_RA.any (fun ρ => SVC.rimOK ρ (4 :: L)) ||
      pair2_B2.all (gramBad pair2_EA pair2_EB (4 :: L))) = true := by
  decide +kernel

theorem pair2_c1_5 : (((List.finRange 7).erase 5).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EA (5 :: L) || pair2_RA.any (fun ρ => SVC.rimOK ρ (5 :: L)) ||
      pair2_B2.all (gramBad pair2_EA pair2_EB (5 :: L))) = true := by
  decide +kernel

theorem pair2_c1_6 : (((List.finRange 7).erase 6).permutations'.all fun L =>
    exclOK [] pair2_D pair2_EA (6 :: L) || pair2_RA.any (fun ρ => SVC.rimOK ρ (6 :: L)) ||
      pair2_B2.all (gramBad pair2_EA pair2_EB (6 :: L))) = true := by
  decide +kernel

theorem pair2_check1 : check1 s0x_S29 pair2_P pair2_swA [] pair2_D pair2_EA pair2_EB pair2_RA pair2_B2 = true := by
  simp only [check1, Bool.and_eq_true]
  refine ⟨by decide +kernel, perms7_split _ (fun a => ?_)⟩
  fin_cases a
  · exact pair2_c1_0
  · exact pair2_c1_1
  · exact pair2_c1_2
  · exact pair2_c1_3
  · exact pair2_c1_4
  · exact pair2_c1_5
  · exact pair2_c1_6

/-- **Pair `x 1 - x 2` + `x 5 - x 6` (lines F012xF124, F1456xF356)**, `PSVC.pair_closure`. -/
theorem lexAny_pair2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hA035 : ⟪F.N 3, x 1 - x 2⟫ < 0)
    (hA346 : ⟪F.N 7, x 1 - x 2⟫ < 0)
    (hA356 : ⟪F.N 8, x 1 - x 2⟫ < 0)
    (hB012 : 0 < ⟪F.N 0, x 5 - x 6⟫)
    (hB023 : 0 < ⟪F.N 2, x 5 - x 6⟫)
    (hB124 : ⟪F.N 4, x 5 - x 6⟫ < 0)
    (hB234 : ⟪F.N 6, x 5 - x 6⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 4 5 0 1)
    (hS1 : 0 < PlaneSide x 2 5 6 0 1)
    (hS2 : 0 < PlaneSide x 2 3 6 1 5)
    (hS3 : 0 < PlaneSide x 2 3 5 1 6)
    (hgen1 : ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫)
    (hgen2 : ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫) :
    Gen.LexAny F := by
  have hs1 : ∀ t ∈ ({0, 1, 3, 4, 5, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 1 - x 2⟫ = pair2_swA t := by
    intro t ht
    fin_cases t <;> simp at ht
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_neg hA035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_pos (edge_pos F 5 (by decide) (by decide))
    · exact sign_neg hA346
    · exact sign_neg hA356
  have hT1 : ∀ ρ ∈ pair2_RA, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 3, 4, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hE1 : ∀ d ∈ pair2_EA, DecOK x pair2_P (x 1 - x 2) d := by
    intro d hd
    simp only [pair2_EA, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact decOK_edge x pair2_P 1 2
  have hf1 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair2_P ij.2), x 1 - x 2⟫ < ⟪x (pair2_P ij.1), x 1 - x 2⟫ := (by simp)
  have hR1 := hR_two F pair2_swA pair2_RA 0 4 1 4 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hs2 : ∀ t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)), SignType.sign ⟪F.N t, x 5 - x 6⟫ = pair2_swB t := by
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
  have hT2 : ∀ ρ ∈ pair2_RB, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hE2 : ∀ d ∈ pair2_EB, DecOK x pair2_P (x 5 - x 6) d := by
    intro d hd
    simp only [pair2_EB, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact decOK_edge x pair2_P 5 6
    · exact decOK_tri F pair2_P pair2_swB 5 7 4 1 6 4 0 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x 5 - x 6) (edge_zero F 5 (by decide) (by decide))
        (hs2 7 (by decide)) (hs2 4 (by decide))
  have hf2 : ∀ ij ∈ ([] : List (Fin 7 × Fin 7)), ⟪x (pair2_P ij.2), x 5 - x 6⟫ < ⟪x (pair2_P ij.1), x 5 - x 6⟫ := (by simp)
  have hR2 := hR_two F pair2_swB pair2_RB 5 8 5 3 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hP : ∀ i, pair2_P i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective pair2_P := by decide
  have hD : ∀ s ∈ pair2_D, ∃ mu : Fin 7 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (pair2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i := by
    intro s hs
    simp only [pair2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact pair2_dep0 F hS0
    · exact pair2_dep1 F hS1
    · exact pair2_dep2 F hS2 hS3
  exact pair_closure F pair2_P (x 1 - x 2) (x 5 - x 6) pair2_swA pair2_swB pair2_RA pair2_RB
    (fun ρ hρ t ht => hs1 t (hT1 ρ hρ t ht)) (fun ρ hρ t ht => hs2 t (hT2 ρ hρ t ht)) hR1 hR2
    _ _ hf1 hf2 pair2_D hD pair2_EA pair2_EB hE1 hE2
    (fun i j hij => hgen1 _ (hP i) _ (hP j) (hPi.ne hij)) (fun i j hij => hgen2 _ (hP i) _ (hP j) (hPi.ne hij))
    pair2_B2 pair2_check1 pair2_check2

/-! ### Normal form `NF29` -/

/-- **NF29 form of `lexAny_pair2`**. -/
theorem lexAny29_pair2 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.V < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 1 - x 2⟫ < 0)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 0, x 5 - x 6⟫)
    (h6 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 5 - x 6⟫)
    (h7 : ⟪(s0x_fac29 N.facets).N 4, x 5 - x 6⟫ < 0)
    (h8 : ⟪(s0x_fac29 N.facets).N 6, x 5 - x 6⟫ < 0)
    (h9 : 0 < PlaneSide x 2 5 6 0 1)
    (h10 : 0 < PlaneSide x 2 3 6 1 5)
    (h11 : 0 < PlaneSide x 2 3 5 1 6)
    (h12 : (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫))
    (h13 : ∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 5 - x 6⟫ ≠ ⟪x j, x 5 - x 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_pair2 _ h2 h3 h4 h5 h6 h7 h8 (ps24501_pos N h1) h9 h10 h11 h12 h13

end Minimality.PL29
