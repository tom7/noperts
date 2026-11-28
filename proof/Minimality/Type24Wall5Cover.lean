module

public import Minimality.Type24Wall3Cover
public import Minimality.Type24OffOB1DW3

/-!
# Wall5Cover: six more walls (`0164.0345`, `0164.346`, `A2.025`, `A2.346`, `B2.025`, `B2.346`) carry a certificate or a letter condition

nopert229 notes/P126-MECHANISM.md (addendum WALL5).  Step 4 of the structural cover route.  The E5ADV adversary found three
points (`t1_1e-2_nb548_k0_e1e-02`, `w15_0_0`, `w7_11_6`) on which all five wall letter conditions `A236E`, `P126E`,
`Cp236E`, `C0536E`, `C016E` hold on both sides although `cells28` closes them; their certificates sit on these walls
(`cell0164` of `Type24GapLemmas2`: `0345` and `346`; the `T_2` cells `A2`, `B2`: `025` and `346`).  Six more instances of the
generic wall theorem `wall_cert_or_E` of `Type24P126Cover` (any `Cell24`, any `CellWall`; no `OB1`, no `CbarIn`).

Each segment `[E0, E1]` is the arc of the circle of views with the wall facet edge-on between two edge directions of the wall
facet that contains the open wall of the cell (tightest such arc over the pool data); the facet forms that are not automatic on
the arc are in `fac`, the automatic ones are proved from `F.zero` / `F.neg` (`comb_pos` / `comb_neg`).  Rim orientation `ρ`
of an open cell: the sign of a scalar `s` read off the facet `016` (in front, through three rim vertices): `s0164 x =
det3(x₁ - x₀, x₆ - x₀, x₀ - x₂)` for `cell0164` and `sT2 x = det3(x₁ - x₆, x₀ - x₆, x₆ - x₂)` for `A2` and `B2`
(`rho_of_perp`).  On the `346` wall of `B2` the rim vertices `3, 4, 6` project to a line, so the rim determinants there
vanish; this does not matter, only the pushed (open cell) view needs `hrim`.  Then the narrowed open Prop `CellCoverEmptyE10`
(all eleven letter conditions on `x` and on the twin) and its chain (with `OSpec.OpenSpecialQ`).

Deciding test (nopert229 tools/genleaves/runs/wall5/, a literal transcription, CELL=0164a|0164b|A2a|A2b|B2a|B2b): see
notes/P126-MECHANISM.md, addendum WALL5.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## The rim scalars -/

/-- `det(x₁ - x₀, x₆ - x₀, x₀ - x₂)`: the rim orientation scalar of `cell0164`. -/
noncomputable def s0164 (x : Fin 7 → ℝ³) : ℝ := Split.det3 (x 1 - x 0) (x 6 - x 0) (x 0 - x 2)

/-- `det(x₁ - x₆, x₀ - x₆, x₆ - x₂)`: the rim orientation scalar of `A2` and `B2`. -/
noncomputable def sT2 (x : Fin 7 → ℝ³) : ℝ := Split.det3 (x 1 - x 6) (x 0 - x 6) (x 6 - x 2)

/-- **Rim sign of `0164`:** `ρ s0164 x > 0` on the open cell (facet `016` in front; the rim edge `0 → 1`, vertex `6`). -/
theorem cell0164_rho (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F cell0164.U (univ \ cell0164.U) w) {ρ : ℝ}
    (hrim : ∀ i j : ZMod cell0164.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cell0164.r (i + 1)) - x (cell0164.r i)) (x (cell0164.r j) - x (cell0164.r i)) w) :
    0 < ρ * s0164 x := by
  have l : 0 < ρ * Split.det3 (x 1 - x 0) (x 6 - x 0) w := hrim 0 2 (by decide) (by decide)
  have h1 := hcell.1 1 (by decide)
  have hq : 0 < ⟪F.N 1, x 0 - x 2⟫ := by
    rw [F.inner_sub, F.zero 1 0 (by decide)]; linarith [F.neg 1 2 (by decide)]
  exact rho_of_perp (N := F.N 1) (by rw [F.inner_sub, F.zero 1 1 (by decide), F.zero 1 0 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 1 6 (by decide), F.zero 1 0 (by decide)]; ring) l (mul_pos h1 hq)

/-- **Rim sign of `A2`:** `ρ sT2 x > 0` on the open cell (facet `016` in front; the rim edge `6 → 1`, vertex `0`). -/
theorem cellA2_rho5 (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F cellA2.U (univ \ cellA2.U) w) {ρ : ℝ}
    (hrim : ∀ i j : ZMod cellA2.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cellA2.r (i + 1)) - x (cellA2.r i)) (x (cellA2.r j) - x (cellA2.r i)) w) :
    0 < ρ * sT2 x := by
  have l : 0 < ρ * Split.det3 (x 1 - x 6) (x 0 - x 6) w := hrim 3 0 (by decide) (by decide)
  have h1 := hcell.1 1 (by decide)
  have hq : 0 < ⟪F.N 1, x 6 - x 2⟫ := by
    rw [F.inner_sub, F.zero 1 6 (by decide)]; linarith [F.neg 1 2 (by decide)]
  exact rho_of_perp (N := F.N 1) (by rw [F.inner_sub, F.zero 1 1 (by decide), F.zero 1 6 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 1 0 (by decide), F.zero 1 6 (by decide)]; ring) l (mul_pos h1 hq)

/-- **Rim sign of `B2`:** `ρ sT2 x > 0` on the open cell (facet `016` in front; the rim edge `6 → 1`, vertex `0`). -/
theorem cellB2_rho6 (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F cellB2.U (univ \ cellB2.U) w) {ρ : ℝ}
    (hrim : ∀ i j : ZMod cellB2.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cellB2.r (i + 1)) - x (cellB2.r i)) (x (cellB2.r j) - x (cellB2.r i)) w) :
    0 < ρ * sT2 x := by
  have l : 0 < ρ * Split.det3 (x 1 - x 6) (x 0 - x 6) w := hrim 4 0 (by decide) (by decide)
  have h1 := hcell.1 1 (by decide)
  have hq : 0 < ⟪F.N 1, x 6 - x 2⟫ := by
    rw [F.inner_sub, F.zero 1 6 (by decide)]; linarith [F.neg 1 2 (by decide)]
  exact rho_of_perp (N := F.N 1) (by rw [F.inner_sub, F.zero 1 1 (by decide), F.zero 1 6 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 1 0 (by decide), F.zero 1 6 (by decide)]; ring) l (mul_pos h1 hq)

/-! ## The six walls -/

/-- **The `0345` wall of `0164`:** segment `[x₄ - x₃, x₀ - x₅]` (facet `0345` edge-on), facet forms `-N 012, N 016, -N 025, -N 126, -N 236, -N 346`; `046, 235` are automatic; push `x₁ - x₀`. -/
noncomputable def c0164aWall (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 where
  n := 6
  E0 := x 4 - x 3
  E1 := x 0 - x 5
  v := x 1 - x 0
  fac := ![-F.N 0, F.N 1, -F.N 2, -F.N 5, -F.N 7, -F.N 8]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 4 - x 3) + l • (x 0 - x 5)⟫ =
        (1 - l) * (F.f t (x 4) - F.f t (x 3)) + l * (F.f t (x 0) - F.f t (x 5)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f0 : 0 < ⟪-F.N 0, (1 - l) • (x 4 - x 3) + l • (x 0 - x 5)⟫ := hf 0
    rw [inner_neg_left] at f0
    have f1 : 0 < ⟪F.N 1, (1 - l) • (x 4 - x 3) + l • (x 0 - x 5)⟫ := hf 1
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 4 - x 3) + l • (x 0 - x 5)⟫ := hf 2
    rw [inner_neg_left] at f2
    have f5 : 0 < ⟪-F.N 5, (1 - l) • (x 4 - x 3) + l • (x 0 - x 5)⟫ := hf 3
    rw [inner_neg_left] at f5
    have f7 : 0 < ⟪-F.N 7, (1 - l) • (x 4 - x 3) + l • (x 0 - x 5)⟫ := hf 4
    rw [inner_neg_left] at f7
    have f8 : 0 < ⟪-F.N 8, (1 - l) • (x 4 - x 3) + l • (x 0 - x 5)⟫ := hf 5
    rw [inner_neg_left] at f8
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({1, 4} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl
      · -- facet 016 (letter)
        exact Or.inl f1
      · -- facet 046 (automatic)
        left
        have z0 := F.zero 4 0 (by decide)
        have z3 := F.neg 4 3 (by decide)
        have z4 := F.zero 4 4 (by decide)
        have z5 := F.neg 4 5 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
    · have ht' : t ∉ ({1, 4} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 2 ∨ t = 3 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- facet 012 (letter)
        exact Or.inl (by linarith)
      · -- facet 025 (letter)
        exact Or.inl (by linarith)
      · -- wall facet 0345
        right
        refine ⟨?_, ?_⟩
        · have z0 := F.zero 3 0 (by decide); have z3 := F.zero 3 3 (by decide); have z4 := F.zero 3 4 (by decide); have z5 := F.zero 3 5 (by decide)
          rw [hNr, z0, z3, z4, z5]; ring
        · have z0 := F.zero 3 0 (by decide); have z1 := F.neg 3 1 (by decide)
          rw [F.inner_sub]; linarith
      · -- facet 126 (letter)
        exact Or.inl (by linarith)
      · -- facet 235 (automatic)
        left
        have z0 := F.neg 6 0 (by decide)
        have z3 := F.zero 6 3 (by decide)
        have z4 := F.neg 6 4 (by decide)
        have z5 := F.zero 6 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 236 (letter)
        exact Or.inl (by linarith)
      · -- facet 346 (letter)
        exact Or.inl (by linarith)

/-- **The `346` wall of `0164`:** segment `[x₆ - x₃, x₄ - x₃]` (facet `346` edge-on), facet forms `-N 012, N 016, -N 025, -N 126`; `0345, 046, 235, 236` are automatic; push `x₀ - x₃`. -/
noncomputable def c0164bWall (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 where
  n := 4
  E0 := x 6 - x 3
  E1 := x 4 - x 3
  v := x 0 - x 3
  fac := ![-F.N 0, F.N 1, -F.N 2, -F.N 5]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 6 - x 3) + l • (x 4 - x 3)⟫ =
        (1 - l) * (F.f t (x 6) - F.f t (x 3)) + l * (F.f t (x 4) - F.f t (x 3)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f0 : 0 < ⟪-F.N 0, (1 - l) • (x 6 - x 3) + l • (x 4 - x 3)⟫ := hf 0
    rw [inner_neg_left] at f0
    have f1 : 0 < ⟪F.N 1, (1 - l) • (x 6 - x 3) + l • (x 4 - x 3)⟫ := hf 1
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 6 - x 3) + l • (x 4 - x 3)⟫ := hf 2
    rw [inner_neg_left] at f2
    have f5 : 0 < ⟪-F.N 5, (1 - l) • (x 6 - x 3) + l • (x 4 - x 3)⟫ := hf 3
    rw [inner_neg_left] at f5
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({1, 4} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl
      · -- facet 016 (letter)
        exact Or.inl f1
      · -- facet 046 (automatic)
        left
        have z3 := F.neg 4 3 (by decide)
        have z4 := F.zero 4 4 (by decide)
        have z6 := F.zero 4 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
    · have ht' : t ∉ ({1, 4} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 2 ∨ t = 3 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- facet 012 (letter)
        exact Or.inl (by linarith)
      · -- facet 025 (letter)
        exact Or.inl (by linarith)
      · -- facet 0345 (automatic)
        left
        have z3 := F.zero 3 3 (by decide)
        have z4 := F.zero 3 4 (by decide)
        have z6 := F.neg 3 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 126 (letter)
        exact Or.inl (by linarith)
      · -- facet 235 (automatic)
        left
        have z3 := F.zero 6 3 (by decide)
        have z4 := F.neg 6 4 (by decide)
        have z6 := F.neg 6 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 236 (automatic)
        left
        have z3 := F.zero 7 3 (by decide)
        have z4 := F.neg 7 4 (by decide)
        have z6 := F.zero 7 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- wall facet 346
        right
        refine ⟨?_, ?_⟩
        · have z3 := F.zero 8 3 (by decide); have z4 := F.zero 8 4 (by decide); have z6 := F.zero 8 6 (by decide)
          rw [hNr, z3, z4, z6]; ring
        · have z0 := F.neg 8 0 (by decide); have z3 := F.zero 8 3 (by decide)
          rw [F.inner_sub]; linarith

/-- **The `025` wall of `A2`:** segment `[x₅ - x₂, x₀ - x₂]` (facet `025` edge-on), facet forms `N 016, N 046, N 346`; `012, 0345, 126, 235, 236` are automatic; push `x₁ - x₀`. -/
noncomputable def cA2aWall (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 where
  n := 3
  E0 := x 5 - x 2
  E1 := x 0 - x 2
  v := x 1 - x 0
  fac := ![F.N 1, F.N 4, F.N 8]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ =
        (1 - l) * (F.f t (x 5) - F.f t (x 2)) + l * (F.f t (x 0) - F.f t (x 2)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f1 : 0 < ⟪F.N 1, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ := hf 0
    have f4 : 0 < ⟪F.N 4, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ := hf 1
    have f8 : 0 < ⟪F.N 8, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ := hf 2
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · -- facet 016 (letter)
        exact Or.inl f1
      · -- facet 0345 (automatic)
        left
        have z0 := F.zero 3 0 (by decide)
        have z2 := F.neg 3 2 (by decide)
        have z5 := F.zero 3 5 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 046 (letter)
        exact Or.inl f4
      · -- facet 346 (letter)
        exact Or.inl f8
    · have ht' : t ∉ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl
      · -- facet 012 (automatic)
        left
        have z0 := F.zero 0 0 (by decide)
        have z2 := F.zero 0 2 (by decide)
        have z5 := F.neg 0 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- wall facet 025
        right
        refine ⟨?_, ?_⟩
        · have z0 := F.zero 2 0 (by decide); have z2 := F.zero 2 2 (by decide); have z5 := F.zero 2 5 (by decide)
          rw [hNr, z0, z2, z5]; ring
        · have z0 := F.zero 2 0 (by decide); have z1 := F.neg 2 1 (by decide)
          rw [F.inner_sub]; linarith
      · -- facet 126 (automatic)
        left
        have z0 := F.neg 5 0 (by decide)
        have z2 := F.zero 5 2 (by decide)
        have z5 := F.neg 5 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 235 (automatic)
        left
        have z0 := F.neg 6 0 (by decide)
        have z2 := F.zero 6 2 (by decide)
        have z5 := F.zero 6 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- facet 236 (automatic)
        left
        have z0 := F.neg 7 0 (by decide)
        have z2 := F.zero 7 2 (by decide)
        have z5 := F.neg 7 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))

/-- **The `346` wall of `A2`:** segment `[x₄ - x₃, x₄ - x₆]` (facet `346` edge-on, in front), facet forms `-N 012, N 016, -N 025, -N 126, -N 235`; `0345, 046, 236` are automatic; push `x₃ - x₀`. -/
noncomputable def cA2bWall (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 where
  n := 5
  E0 := x 4 - x 3
  E1 := x 4 - x 6
  v := x 3 - x 0
  fac := ![-F.N 0, F.N 1, -F.N 2, -F.N 5, -F.N 6]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ =
        (1 - l) * (F.f t (x 4) - F.f t (x 3)) + l * (F.f t (x 4) - F.f t (x 6)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f0 : 0 < ⟪-F.N 0, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 0
    rw [inner_neg_left] at f0
    have f1 : 0 < ⟪F.N 1, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 1
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 2
    rw [inner_neg_left] at f2
    have f5 : 0 < ⟪-F.N 5, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 3
    rw [inner_neg_left] at f5
    have f6 : 0 < ⟪-F.N 6, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 4
    rw [inner_neg_left] at f6
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · -- facet 016 (letter)
        exact Or.inl f1
      · -- facet 0345 (automatic)
        left
        have z3 := F.zero 3 3 (by decide)
        have z4 := F.zero 3 4 (by decide)
        have z6 := F.neg 3 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- facet 046 (automatic)
        left
        have z3 := F.neg 4 3 (by decide)
        have z4 := F.zero 4 4 (by decide)
        have z6 := F.zero 4 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- wall facet 346
        right
        refine ⟨?_, ?_⟩
        · have z3 := F.zero 8 3 (by decide); have z4 := F.zero 8 4 (by decide); have z6 := F.zero 8 6 (by decide)
          rw [hNr, z3, z4, z6]; ring
        · have z0 := F.neg 8 0 (by decide); have z3 := F.zero 8 3 (by decide)
          rw [F.inner_sub]; linarith
    · have ht' : t ∉ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl
      · -- facet 012 (letter)
        exact Or.inl (by linarith)
      · -- facet 025 (letter)
        exact Or.inl (by linarith)
      · -- facet 126 (letter)
        exact Or.inl (by linarith)
      · -- facet 235 (letter)
        exact Or.inl (by linarith)
      · -- facet 236 (automatic)
        left
        have z3 := F.zero 7 3 (by decide)
        have z4 := F.neg 7 4 (by decide)
        have z6 := F.zero 7 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))

/-- **The `025` wall of `B2`:** segment `[x₅ - x₂, x₀ - x₂]` (facet `025` edge-on), facet forms `N 016, N 046, -N 346`; `012, 0345, 126, 235, 236` are automatic; push `x₁ - x₀`. -/
noncomputable def cB2aWall (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 where
  n := 3
  E0 := x 5 - x 2
  E1 := x 0 - x 2
  v := x 1 - x 0
  fac := ![F.N 1, F.N 4, -F.N 8]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ =
        (1 - l) * (F.f t (x 5) - F.f t (x 2)) + l * (F.f t (x 0) - F.f t (x 2)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f1 : 0 < ⟪F.N 1, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ := hf 0
    have f4 : 0 < ⟪F.N 4, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ := hf 1
    have f8 : 0 < ⟪-F.N 8, (1 - l) • (x 5 - x 2) + l • (x 0 - x 2)⟫ := hf 2
    rw [inner_neg_left] at f8
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({1, 3, 4} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl
      · -- facet 016 (letter)
        exact Or.inl f1
      · -- facet 0345 (automatic)
        left
        have z0 := F.zero 3 0 (by decide)
        have z2 := F.neg 3 2 (by decide)
        have z5 := F.zero 3 5 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 046 (letter)
        exact Or.inl f4
    · have ht' : t ∉ ({1, 3, 4} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl
      · -- facet 012 (automatic)
        left
        have z0 := F.zero 0 0 (by decide)
        have z2 := F.zero 0 2 (by decide)
        have z5 := F.neg 0 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- wall facet 025
        right
        refine ⟨?_, ?_⟩
        · have z0 := F.zero 2 0 (by decide); have z2 := F.zero 2 2 (by decide); have z5 := F.zero 2 5 (by decide)
          rw [hNr, z0, z2, z5]; ring
        · have z0 := F.zero 2 0 (by decide); have z1 := F.neg 2 1 (by decide)
          rw [F.inner_sub]; linarith
      · -- facet 126 (automatic)
        left
        have z0 := F.neg 5 0 (by decide)
        have z2 := F.zero 5 2 (by decide)
        have z5 := F.neg 5 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 235 (automatic)
        left
        have z0 := F.neg 6 0 (by decide)
        have z2 := F.zero 6 2 (by decide)
        have z5 := F.zero 6 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- facet 236 (automatic)
        left
        have z0 := F.neg 7 0 (by decide)
        have z2 := F.zero 7 2 (by decide)
        have z5 := F.neg 7 5 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 346 (letter)
        exact Or.inl (by linarith)

/-- **The `346` wall of `B2`:** segment `[x₄ - x₃, x₄ - x₆]` (facet `346` edge-on, behind), facet forms `-N 012, N 016, -N 025, -N 126, -N 235`; `0345, 046, 236` are automatic; push `x₀ - x₃`. -/
noncomputable def cB2bWall (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 where
  n := 5
  E0 := x 4 - x 3
  E1 := x 4 - x 6
  v := x 0 - x 3
  fac := ![-F.N 0, F.N 1, -F.N 2, -F.N 5, -F.N 6]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ =
        (1 - l) * (F.f t (x 4) - F.f t (x 3)) + l * (F.f t (x 4) - F.f t (x 6)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f0 : 0 < ⟪-F.N 0, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 0
    rw [inner_neg_left] at f0
    have f1 : 0 < ⟪F.N 1, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 1
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 2
    rw [inner_neg_left] at f2
    have f5 : 0 < ⟪-F.N 5, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 3
    rw [inner_neg_left] at f5
    have f6 : 0 < ⟪-F.N 6, (1 - l) • (x 4 - x 3) + l • (x 4 - x 6)⟫ := hf 4
    rw [inner_neg_left] at f6
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({1, 3, 4} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl
      · -- facet 016 (letter)
        exact Or.inl f1
      · -- facet 0345 (automatic)
        left
        have z3 := F.zero 3 3 (by decide)
        have z4 := F.zero 3 4 (by decide)
        have z6 := F.neg 3 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- facet 046 (automatic)
        left
        have z3 := F.neg 4 3 (by decide)
        have z4 := F.zero 4 4 (by decide)
        have z6 := F.zero 4 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
    · have ht' : t ∉ ({1, 3, 4} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl
      · -- facet 012 (letter)
        exact Or.inl (by linarith)
      · -- facet 025 (letter)
        exact Or.inl (by linarith)
      · -- facet 126 (letter)
        exact Or.inl (by linarith)
      · -- facet 235 (letter)
        exact Or.inl (by linarith)
      · -- facet 236 (automatic)
        left
        have z3 := F.zero 7 3 (by decide)
        have z4 := F.neg 7 4 (by decide)
        have z6 := F.zero 7 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- wall facet 346
        right
        refine ⟨?_, ?_⟩
        · have z3 := F.zero 8 3 (by decide); have z4 := F.zero 8 4 (by decide); have z6 := F.zero 8 6 (by decide)
          rw [hNr, z3, z4, z6]; ring
        · have z0 := F.neg 8 0 (by decide); have z3 := F.zero 8 3 (by decide)
          rw [F.inner_sub]; linarith

/-! ## The letter conditions and the cert-or-E theorems -/

/-- **`C0164aE`**: no strict `RobUni` or apex system of the rim `0.1.6.4` anywhere on the open wall of `c0164aWall`. -/
def C0164aE (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cell0164 (c0164aWall F) (s0164 x)

/-- **`C0164bE`**: no strict `RobUni` or apex system of the rim `0.1.6.4` anywhere on the open wall of `c0164bWall`. -/
def C0164bE (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cell0164 (c0164bWall F) (s0164 x)

/-- **`CA2aE`**: no strict `RobUni` or apex system of the rim `0.5.3.6.1` anywhere on the open wall of `cA2aWall`. -/
def CA2aE (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cellA2 (cA2aWall F) (sT2 x)

/-- **`CA2bE`**: no strict `RobUni` or apex system of the rim `0.5.3.6.1` anywhere on the open wall of `cA2bWall`. -/
def CA2bE (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cellA2 (cA2bWall F) (sT2 x)

/-- **`CB2aE`**: no strict `RobUni` or apex system of the rim `0.5.3.4.6.1` anywhere on the open wall of `cB2aWall`. -/
def CB2aE (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cellB2 (cB2aWall F) (sT2 x)

/-- **`CB2bE`**: no strict `RobUni` or apex system of the rim `0.5.3.4.6.1` anywhere on the open wall of `cB2bWall`. -/
def CB2bE (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cellB2 (cB2bWall F) (sT2 x)

/-- A view next to the wall `c0164aWall` carries `RobUni` or a strict apex certificate, or `C0164aE x F`. -/
theorem c0164a_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ C0164aE x F :=
  wall_cert_or_E F cell0164 (c0164aWall F) (fun _ hc _ _ hrim => cell0164_rho F hc hrim)

/-- A view next to the wall `c0164bWall` carries `RobUni` or a strict apex certificate, or `C0164bE x F`. -/
theorem c0164b_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ C0164bE x F :=
  wall_cert_or_E F cell0164 (c0164bWall F) (fun _ hc _ _ hrim => cell0164_rho F hc hrim)

/-- A view next to the wall `cA2aWall` carries `RobUni` or a strict apex certificate, or `CA2aE x F`. -/
theorem ca2a_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ CA2aE x F :=
  wall_cert_or_E F cellA2 (cA2aWall F) (fun _ hc _ _ hrim => cellA2_rho5 F hc hrim)

/-- A view next to the wall `cA2bWall` carries `RobUni` or a strict apex certificate, or `CA2bE x F`. -/
theorem ca2b_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ CA2bE x F :=
  wall_cert_or_E F cellA2 (cA2bWall F) (fun _ hc _ _ hrim => cellA2_rho5 F hc hrim)

/-- A view next to the wall `cB2aWall` carries `RobUni` or a strict apex certificate, or `CB2aE x F`. -/
theorem cb2a_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ CB2aE x F :=
  wall_cert_or_E F cellB2 (cB2aWall F) (fun _ hc _ _ hrim => cellB2_rho6 F hc hrim)

/-- A view next to the wall `cB2bWall` carries `RobUni` or a strict apex certificate, or `CB2bE x F`. -/
theorem cb2b_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ CB2bE x F :=
  wall_cert_or_E F cellB2 (cB2bWall F) (fun _ hc _ _ hrim => cellB2_rho6 F hc hrim)

/-- Hole fact: at a hole point, `C0164aE x F` holds. -/
theorem holeLeaf_c0164aE {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : C0164aE x F :=
  ((c0164a_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Twin hole fact for `C0164aE`. -/
theorem holeLeaf_c0164aE_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    C0164aE (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases c0164a_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-- Hole fact: at a hole point, `C0164bE x F` holds. -/
theorem holeLeaf_c0164bE {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : C0164bE x F :=
  ((c0164b_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Twin hole fact for `C0164bE`. -/
theorem holeLeaf_c0164bE_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    C0164bE (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases c0164b_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-- Hole fact: at a hole point, `CA2aE x F` holds. -/
theorem holeLeaf_ca2aE {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : CA2aE x F :=
  ((ca2a_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Twin hole fact for `CA2aE`. -/
theorem holeLeaf_ca2aE_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    CA2aE (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases ca2a_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-- Hole fact: at a hole point, `CA2bE x F` holds. -/
theorem holeLeaf_ca2bE {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : CA2bE x F :=
  ((ca2b_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Twin hole fact for `CA2bE`. -/
theorem holeLeaf_ca2bE_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    CA2bE (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases ca2b_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-- Hole fact: at a hole point, `CB2aE x F` holds. -/
theorem holeLeaf_cb2aE {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : CB2aE x F :=
  ((cb2a_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Twin hole fact for `CB2aE`. -/
theorem holeLeaf_cb2aE_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    CB2aE (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases cb2a_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-- Hole fact: at a hole point, `CB2bE x F` holds. -/
theorem holeLeaf_cb2bE {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : CB2bE x F :=
  ((cb2b_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Twin hole fact for `CB2bE`. -/
theorem holeLeaf_cb2bE_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    CB2bE (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases cb2b_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-! ## The narrowed open Prop -/

/-- **[OPEN] `CellCoverEmptyE10 L`**: on `CbarIn`, `OB1`, with the five letter conditions of `CellCoverEmptyE4` and the six
new ones (`C0164aE`, `C0164bE`, `CA2aE`, `CA2bE`, `CB2aE`, `CB2bE`) on `x` and on the twin, the point is not in the
cell-cover residue of `L`. -/
def CellCoverEmptyE10 (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → A236E x F →
    A236E (x ∘ Sym.pi24) (Sym.sym24 F) → P126E x F → P126E (x ∘ Sym.pi24) (Sym.sym24 F) →
    Cp236E x F → Cp236E (x ∘ Sym.pi24) (Sym.sym24 F) → C0536E x F → C0536E (x ∘ Sym.pi24) (Sym.sym24 F) →
    C016E x F → C016E (x ∘ Sym.pi24) (Sym.sym24 F) →
    C0164aE x F → C0164aE (x ∘ Sym.pi24) (Sym.sym24 F) → C0164bE x F → C0164bE (x ∘ Sym.pi24) (Sym.sym24 F) → CA2aE x F → CA2aE (x ∘ Sym.pi24) (Sym.sym24 F) → CA2bE x F → CA2bE (x ∘ Sym.pi24) (Sym.sym24 F) → CB2aE x F → CB2aE (x ∘ Sym.pi24) (Sym.sym24 F) → CB2bE x F → CB2bE (x ∘ Sym.pi24) (Sym.sym24 F) →
    ¬ CellCoverResidue L x F

/-- The previous open Prop implies the narrower one. -/
theorem cellCoverEmptyE10_of_E4 {L : List Cell24} (h : CellCoverEmptyE4 L) : CellCoverEmptyE10 L :=
  fun x F hC hO hA hA' hP hP' h1 h1' h2 h2' h3 h3' _ _ _ _ _ _ _ _ _ _ _ _ => h x F hC hO hA hA' hP hP' h1 h1' h2 h2' h3 h3'

/-- `CellCoverEmptyE10 L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmptyE10 {L : List Cell24} (hN : CellCoverEmptyE10 L) (x : Fin 7 → ℝ³)
    (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_a236E h hO) (holeLeaf_a236E_twin h hO) (holeLeaf_p126E h) (holeLeaf_p126E_twin h)
    (holeLeaf_cp236E h) (holeLeaf_cp236E_twin h) (holeLeaf_c0536E h) (holeLeaf_c0536E_twin h)
    (holeLeaf_c016E h) (holeLeaf_c016E_twin h)
    (holeLeaf_c0164aE h) (holeLeaf_c0164aE_twin h) (holeLeaf_c0164bE h) (holeLeaf_c0164bE_twin h) (holeLeaf_ca2aE h) (holeLeaf_ca2aE_twin h) (holeLeaf_ca2bE h) (holeLeaf_ca2bE_twin h) (holeLeaf_cb2aE h) (holeLeaf_cb2aE_twin h) (holeLeaf_cb2bE h) (holeLeaf_cb2bE_twin h)
    (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmptyE10 L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmptyE10 {L : List Cell24} (hN : CellCoverEmptyE10 L) : OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_cellCoverEmptyE10 hN x F hO (holeLeaf_of_holeFull hF)

/-- [PROVED] `CellCoverEmptyE10 L` and `OSpec.OpenSpecialQ` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyE10_Q {L : List Cell24} (hN : CellCoverEmptyE10 L)
    (hS : OSpec.OpenSpecialQ) : Open24Rupert :=
  OSpec.open24Rupert_of_split_Q (openOB1_of_cellCoverEmptyE10 hN) hS

/-- [PROVED] Headline chain: `CellCoverEmptyE10 cells28` and `OSpec.OpenSpecialQ` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyE10_28_Q (hN : CellCoverEmptyE10 cells28) (hS : OSpec.OpenSpecialQ) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE10_Q hN hS

end Minimality.T24.Cell
