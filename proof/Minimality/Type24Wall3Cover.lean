module

public import Minimality.Type24P126Cover

/-!
# Wall3Cover: the walls `C'.236`, `0536.046`, `C.016` carry a certificate unless their letter conditions hold

nopert229 notes/P126-MECHANISM.md (section 4: the triple `C'.236 + c0536.046 + C.016` covers the 81 sampled points left
by `A236E` and `P126E`).  Step 3 of the structural cover route: three more instances of the generic wall theorem
`wall_cert_or_E` of `Type24P126Cover` (any `Cell24`, any `CellWall`; no `OB1`, no `CbarIn`).

For each wall, the segment `[E0, E1]` is the unique arc of the circle of views with the wall facet edge-on whose
facet signs are compatible with the cell (between two edge directions of the wall facet); the facet forms that are not
automatic on the arc are listed in `fac` and the automatic ones are proved from `F.zero` / `F.neg`:

* `C'.236`: cell `cellC'` (rim `0.5.2.6`, facets `0345, 046, 235, 236, 346` in front), wall `236` edge-on,
  `E0 = x₃ - x₂`, `E1 = x₃ - x₆`, push `x₃ - x₁`, forms `-N 012, -N 016, -N 025, N 046`.
* `0536.046`: cell `cell0536` (rim `0.6.3.5`, facets `0345, 046, 346` in front), wall `046` edge-on,
  `E0 = x₄ - x₀`, `E1 = x₄ - x₆`, push `x₀ - x₁`, forms `-N 012, -N 025, -N 126, -N 235, -N 236`.
* `C.016`: cell `cellC` (rim `0.5.2.3.6`, facets `0345, 046, 235, 346` in front), wall `016` edge-on,
  `E0 = x₀ - x₁`, `E1 = x₆ - x₁`, push `x₂ - x₁`, forms `-N 025, N 0345, N 235, -N 236, N 346`.

The rim orientation `ρ` of the open cell is the sign of a scalar `s` read off a facet through three rim vertices
(`rho_of_perp`: `det3 a b w ⟪N, q⟫ = det3 a b q ⟪N, w⟫` for `a, b ⊥ N`): `sA x = det3(x₅ - x₀, x₂ - x₀, x₆ - x₀)` for
`C'` and `C` (facet `025` behind), `sB x = det3(x₀ - x₃, x₅ - x₃, x₆ - x₃)` for `0536` (facet `0345` in front).  The
`π_24` twin is the same statement for `x ∘ π_24`.  Then the narrowed open Prop `CellCoverEmptyE4` (`A236E`, `P126E` and
the three new letter conditions on `x` and on the twin) and its chain.

Deciding test (nopert229 tools/genleaves/runs/wall3/, a literal transcription of the pieces, CELL=Cp|c0536|C): see
notes/P126-MECHANISM.md, addendum.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## Generic helpers -/

/-- A convex combination of two nonnegative numbers, one of them positive, is positive. -/
theorem comb_pos {l A B : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : 0 < A ∨ 0 < B) :
    0 < (1 - l) * A + l * B := by
  rcases h with h | h
  · nlinarith [mul_pos (sub_pos.2 hl1) h, mul_nonneg hl0.le hB]
  · nlinarith [mul_pos hl0 h, mul_nonneg (sub_pos.2 hl1).le hA]

/-- A convex combination of two nonpositive numbers, one of them negative, is negative. -/
theorem comb_neg {l A B : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hA : A ≤ 0) (hB : B ≤ 0) (h : A < 0 ∨ B < 0) :
    (1 - l) * A + l * B < 0 := by
  rcases h with h | h
  · nlinarith [mul_pos (sub_pos.2 hl1) (neg_pos.2 h), mul_nonneg hl0.le (neg_nonneg.2 hB)]
  · nlinarith [mul_pos hl0 (neg_pos.2 h), mul_nonneg (sub_pos.2 hl1).le (neg_nonneg.2 hA)]

/-- **The rim sign from a facet through three rim vertices:** if `N ⊥ a, b`, the rim determinant `ρ det3 a b w` is
positive and `⟪N, w⟫ ⟪N, q⟫ > 0`, then `ρ det3 a b q > 0`. -/
theorem rho_of_perp {N a b q w : ℝ³} {ρ : ℝ} (ha : ⟪N, a⟫ = 0) (hb : ⟪N, b⟫ = 0)
    (hl : 0 < ρ * Split.det3 a b w) (hP : 0 < ⟪N, w⟫ * ⟪N, q⟫) : 0 < ρ * Split.det3 a b q := by
  have key := det3_mul_inner_of_perp N a b q w ha hb
  have hq : 0 < ⟪N, q⟫ ^ 2 := by
    have : ⟪N, q⟫ ≠ 0 := by rintro h; rw [h, mul_zero] at hP; exact lt_irrefl _ hP
    positivity
  have h1 : 0 < (ρ * Split.det3 a b q) * (⟪N, w⟫ * ⟪N, q⟫) := by
    have : (ρ * Split.det3 a b q) * (⟪N, w⟫ * ⟪N, q⟫) = (ρ * Split.det3 a b w) * ⟪N, q⟫ ^ 2 := by
      have e : Split.det3 a b q * ⟪N, w⟫ = Split.det3 a b w * ⟪N, q⟫ := key.symm
      calc (ρ * Split.det3 a b q) * (⟪N, w⟫ * ⟪N, q⟫) = ρ * (Split.det3 a b q * ⟪N, w⟫) * ⟪N, q⟫ := by ring
        _ = (ρ * Split.det3 a b w) * ⟪N, q⟫ ^ 2 := by rw [e]; ring
    rw [this]; exact mul_pos hl hq
  exact pos_of_mul_pos_left h1 hP.le

/-- The same with `⟪N, w⟫ ⟪N, q⟫ < 0`: then `ρ det3 a b q < 0`. -/
theorem rho_of_perp_neg {N a b q w : ℝ³} {ρ : ℝ} (ha : ⟪N, a⟫ = 0) (hb : ⟪N, b⟫ = 0)
    (hl : 0 < ρ * Split.det3 a b w) (hP : ⟪N, w⟫ * ⟪N, q⟫ < 0) : ρ * Split.det3 a b q < 0 := by
  have h := rho_of_perp (q := -q) ha hb hl (by rw [inner_neg_right]; linarith)
  have e : Split.det3 a b (-q) = -Split.det3 a b q := by simp only [Split.det3, PiLp.neg_apply]; ring
  rw [e] at h; linarith

/-! ## The rim scalars -/

/-- `det(x₅ - x₀, x₂ - x₀, x₆ - x₀)`: the rim orientation scalar of `C'` and `C`. -/
noncomputable def sA (x : Fin 7 → ℝ³) : ℝ := Split.det3 (x 5 - x 0) (x 2 - x 0) (x 6 - x 0)

/-- `det(x₀ - x₃, x₅ - x₃, x₆ - x₃)`: the rim orientation scalar of `0536`. -/
noncomputable def sB (x : Fin 7 → ℝ³) : ℝ := Split.det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3)

/-- **Rim sign of `C'`:** `ρ sA x > 0` on the open cell (facet `025` behind; the rim edge `0 → 5`, vertex `2`). -/
theorem cellCp_rho (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F cellC'.U (univ \ cellC'.U) w) {ρ : ℝ}
    (hrim : ∀ i j : ZMod cellC'.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cellC'.r (i + 1)) - x (cellC'.r i)) (x (cellC'.r j) - x (cellC'.r i)) w) :
    0 < ρ * sA x := by
  have l : 0 < ρ * Split.det3 (x 5 - x 0) (x 2 - x 0) w := hrim 0 2 (by decide) (by decide)
  have h2 := hcell.2 2 (by decide)
  have hq : ⟪F.N 2, x 6 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 2 0 (by decide)]; simpa using F.neg 2 6 (by decide)
  exact rho_of_perp (N := F.N 2) (by rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 0 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 2 2 (by decide), F.zero 2 0 (by decide)]; ring) l (mul_pos_of_neg_of_neg h2 hq)

/-- **Rim sign of `C`:** `ρ sA x > 0` on the open cell (facet `025` behind; the rim edge `0 → 5`, vertex `2`). -/
theorem cellC_rho (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F cellC.U (univ \ cellC.U) w) {ρ : ℝ}
    (hrim : ∀ i j : ZMod cellC.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cellC.r (i + 1)) - x (cellC.r i)) (x (cellC.r j) - x (cellC.r i)) w) :
    0 < ρ * sA x := by
  have l : 0 < ρ * Split.det3 (x 5 - x 0) (x 2 - x 0) w := hrim 0 2 (by decide) (by decide)
  have h2 := hcell.2 2 (by decide)
  have hq : ⟪F.N 2, x 6 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 2 0 (by decide)]; simpa using F.neg 2 6 (by decide)
  exact rho_of_perp (N := F.N 2) (by rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 0 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 2 2 (by decide), F.zero 2 0 (by decide)]; ring) l (mul_pos_of_neg_of_neg h2 hq)

/-- **Rim sign of `0536`:** `ρ sB x > 0` on the open cell (facet `0345` in front; the rim edge `3 → 5`, vertex `0`). -/
theorem cell0536_rho (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F cell0536.U (univ \ cell0536.U) w) {ρ : ℝ}
    (hrim : ∀ i j : ZMod cell0536.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cell0536.r (i + 1)) - x (cell0536.r i)) (x (cell0536.r j) - x (cell0536.r i)) w) :
    0 < ρ * sB x := by
  have l : 0 < ρ * Split.det3 (x 5 - x 3) (x 0 - x 3) w := hrim 2 0 (by decide) (by decide)
  have h3 := hcell.1 3 (by decide)
  have hq : ⟪F.N 3, x 6 - x 3⟫ < 0 := by
    rw [F.inner_sub, F.zero 3 3 (by decide)]; simpa using F.neg 3 6 (by decide)
  have := rho_of_perp_neg (N := F.N 3) (by rw [F.inner_sub, F.zero 3 5 (by decide), F.zero 3 3 (by decide)]; ring)
    (by rw [F.inner_sub, F.zero 3 0 (by decide), F.zero 3 3 (by decide)]; ring) l (mul_neg_of_pos_of_neg h3 hq)
  have e : Split.det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3) = -Split.det3 (x 5 - x 3) (x 0 - x 3) (x 6 - x 3) := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  rw [sB, e]; linarith

/-! ## The three walls -/

/-- **The `236` wall of `C'`:** the segment `[x₃ - x₂, x₃ - x₆]` (facet `236` edge-on), facet forms
`-N 012, -N 016, -N 025, N 046`; `0345, 235, 346` in front and `126` behind are automatic; push `x₃ - x₁`. -/
noncomputable def cp236Wall (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' where
  n := 4
  E0 := x 3 - x 2
  E1 := x 3 - x 6
  v := x 3 - x 1
  fac := ![-F.N 0, -F.N 1, -F.N 2, F.N 4]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 3 - x 2) + l • (x 3 - x 6)⟫ =
        (1 - l) * (F.f t (x 3) - F.f t (x 2)) + l * (F.f t (x 3) - F.f t (x 6)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f0 : 0 < ⟪-F.N 0, (1 - l) • (x 3 - x 2) + l • (x 3 - x 6)⟫ := hf 0
    rw [inner_neg_left] at f0
    have f1 : 0 < ⟪-F.N 1, (1 - l) • (x 3 - x 2) + l • (x 3 - x 6)⟫ := hf 1
    rw [inner_neg_left] at f1
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 3 - x 2) + l • (x 3 - x 6)⟫ := hf 2
    rw [inner_neg_left] at f2
    have f4 : 0 < ⟪F.N 4, (1 - l) • (x 3 - x 2) + l • (x 3 - x 6)⟫ := hf 3
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({3, 4, 6, 7, 8} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl | rfl | rfl
      · -- facet 0345
        left
        have z2 := F.neg 3 2 (by decide)
        have z3 := F.zero 3 3 (by decide)
        have z6 := F.neg 3 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 046
        exact Or.inl f4
      · -- facet 235
        left
        have z2 := F.zero 6 2 (by decide)
        have z3 := F.zero 6 3 (by decide)
        have z6 := F.neg 6 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- facet 236
        right
        refine ⟨?_, ?_⟩
        · have z2 := F.zero 7 2 (by decide)
          have z3 := F.zero 7 3 (by decide)
          have z6 := F.zero 7 6 (by decide)
          rw [hNr, z2, z3, z6]; ring
        · have z1 := F.neg 7 1 (by decide)
          have z3 := F.zero 7 3 (by decide)
          rw [F.inner_sub]; linarith
      · -- facet 346
        left
        have z2 := F.neg 8 2 (by decide)
        have z3 := F.zero 8 3 (by decide)
        have z6 := F.zero 8 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
    · have ht' : t ∉ ({3, 4, 6, 7, 8} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 5 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl
      · -- facet 012
        exact Or.inl (by linarith)
      · -- facet 016
        exact Or.inl (by linarith)
      · -- facet 025
        exact Or.inl (by linarith)
      · -- facet 126
        left
        have z2 := F.zero 5 2 (by decide)
        have z3 := F.neg 5 3 (by decide)
        have z6 := F.zero 5 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))

/-- **The `046` wall of `0536`:** the segment `[x₄ - x₀, x₄ - x₆]` (facet `046` edge-on), facet forms
`-N 012, -N 025, -N 126, -N 235, -N 236`; `016` behind, `0345, 346` in front are automatic; push `x₀ - x₁`. -/
noncomputable def c0536Wall (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 where
  n := 5
  E0 := x 4 - x 0
  E1 := x 4 - x 6
  v := x 0 - x 1
  fac := ![-F.N 0, -F.N 2, -F.N 5, -F.N 6, -F.N 7]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 4 - x 0) + l • (x 4 - x 6)⟫ =
        (1 - l) * (F.f t (x 4) - F.f t (x 0)) + l * (F.f t (x 4) - F.f t (x 6)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f0 : 0 < ⟪-F.N 0, (1 - l) • (x 4 - x 0) + l • (x 4 - x 6)⟫ := hf 0
    rw [inner_neg_left] at f0
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 4 - x 0) + l • (x 4 - x 6)⟫ := hf 1
    rw [inner_neg_left] at f2
    have f5 : 0 < ⟪-F.N 5, (1 - l) • (x 4 - x 0) + l • (x 4 - x 6)⟫ := hf 2
    rw [inner_neg_left] at f5
    have f6 : 0 < ⟪-F.N 6, (1 - l) • (x 4 - x 0) + l • (x 4 - x 6)⟫ := hf 3
    rw [inner_neg_left] at f6
    have f7 : 0 < ⟪-F.N 7, (1 - l) • (x 4 - x 0) + l • (x 4 - x 6)⟫ := hf 4
    rw [inner_neg_left] at f7
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({3, 4, 8} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl
      · -- facet 0345
        left
        have z0 := F.zero 3 0 (by decide)
        have z4 := F.zero 3 4 (by decide)
        have z6 := F.neg 3 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- facet 046
        right
        refine ⟨?_, ?_⟩
        · have z0 := F.zero 4 0 (by decide)
          have z4 := F.zero 4 4 (by decide)
          have z6 := F.zero 4 6 (by decide)
          rw [hNr, z0, z4, z6]; ring
        · have z0 := F.zero 4 0 (by decide)
          have z1 := F.neg 4 1 (by decide)
          rw [F.inner_sub]; linarith
      · -- facet 346
        left
        have z0 := F.neg 8 0 (by decide)
        have z4 := F.zero 8 4 (by decide)
        have z6 := F.zero 8 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
    · have ht' : t ∉ ({3, 4, 8} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl
      · -- facet 012
        exact Or.inl (by linarith)
      · -- facet 016
        left
        have z0 := F.zero 1 0 (by decide)
        have z4 := F.neg 1 4 (by decide)
        have z6 := F.zero 1 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 025
        exact Or.inl (by linarith)
      · -- facet 126
        exact Or.inl (by linarith)
      · -- facet 235
        exact Or.inl (by linarith)
      · -- facet 236
        exact Or.inl (by linarith)

/-- **The `016` wall of `C`:** the segment `[x₀ - x₁, x₆ - x₁]` (facet `016` edge-on), facet forms
`-N 025, N 0345, N 235, -N 236, N 346`; `012` behind, `046` in front, `126` behind are automatic; push `x₂ - x₁`. -/
noncomputable def c016Wall (F : S0xFac 9 s0x_S24 x) : CellWall F cellC where
  n := 5
  E0 := x 0 - x 1
  E1 := x 6 - x 1
  v := x 2 - x 1
  fac := ![-F.N 2, F.N 3, F.N 6, -F.N 7, F.N 8]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 0 - x 1) + l • (x 6 - x 1)⟫ =
        (1 - l) * (F.f t (x 0) - F.f t (x 1)) + l * (F.f t (x 6) - F.f t (x 1)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 0 - x 1) + l • (x 6 - x 1)⟫ := hf 0
    rw [inner_neg_left] at f2
    have f3 : 0 < ⟪F.N 3, (1 - l) • (x 0 - x 1) + l • (x 6 - x 1)⟫ := hf 1
    have f6 : 0 < ⟪F.N 6, (1 - l) • (x 0 - x 1) + l • (x 6 - x 1)⟫ := hf 2
    have f7 : 0 < ⟪-F.N 7, (1 - l) • (x 0 - x 1) + l • (x 6 - x 1)⟫ := hf 3
    rw [inner_neg_left] at f7
    have f8 : 0 < ⟪F.N 8, (1 - l) • (x 0 - x 1) + l • (x 6 - x 1)⟫ := hf 4
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({3, 4, 6, 8} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · -- facet 0345
        exact Or.inl f3
      · -- facet 046
        left
        have z0 := F.zero 4 0 (by decide)
        have z1 := F.neg 4 1 (by decide)
        have z6 := F.zero 4 6 (by decide)
        rw [hNr]; exact comb_pos hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 235
        exact Or.inl f6
      · -- facet 346
        exact Or.inl f8
    · have ht' : t ∉ ({3, 4, 6, 8} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 5 ∨ t = 7 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl
      · -- facet 012
        left
        have z0 := F.zero 0 0 (by decide)
        have z1 := F.zero 0 1 (by decide)
        have z6 := F.neg 0 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inr (by linarith))
      · -- facet 016
        right
        refine ⟨?_, ?_⟩
        · have z0 := F.zero 1 0 (by decide)
          have z1 := F.zero 1 1 (by decide)
          have z6 := F.zero 1 6 (by decide)
          rw [hNr, z0, z1, z6]; ring
        · have z1 := F.zero 1 1 (by decide)
          have z2 := F.neg 1 2 (by decide)
          rw [F.inner_sub]; linarith
      · -- facet 025
        exact Or.inl (by linarith)
      · -- facet 126
        left
        have z0 := F.neg 5 0 (by decide)
        have z1 := F.zero 5 1 (by decide)
        have z6 := F.zero 5 6 (by decide)
        rw [hNr]; exact comb_neg hl0 hl1 (by linarith) (by linarith) (Or.inl (by linarith))
      · -- facet 236
        exact Or.inl (by linarith)

/-! ## The letter conditions and the cert-or-E theorems -/

/-- **`Cp236E`**: no strict `RobUni` or apex system of the rim `0.5.2.6` anywhere on the open `236` wall of `C'`. -/
def Cp236E (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cellC' (cp236Wall F) (sA x)

/-- **`C0536E`**: no strict `RobUni` or apex system of the rim `0.6.3.5` anywhere on the open `046` wall of `0536`. -/
def C0536E (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cell0536 (c0536Wall F) (sB x)

/-- **`C016E`**: no strict `RobUni` or apex system of the rim `0.5.2.3.6` anywhere on the open `016` wall of `C`. -/
def C016E (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cellC (c016Wall F) (sA x)

/-- A view next to the `236` wall of `C'` carries `RobUni` or a strict apex certificate, or `Cp236E x F`. -/
theorem cp236_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ Cp236E x F :=
  wall_cert_or_E F cellC' (cp236Wall F) (fun _ hc _ _ hrim => cellCp_rho F hc hrim)

/-- A view next to the `046` wall of `0536` carries `RobUni` or a strict apex certificate, or `C0536E x F`. -/
theorem c0536_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ C0536E x F :=
  wall_cert_or_E F cell0536 (c0536Wall F) (fun _ hc _ _ hrim => cell0536_rho F hc hrim)

/-- A view next to the `016` wall of `C` carries `RobUni` or a strict apex certificate, or `C016E x F`. -/
theorem c016_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ C016E x F :=
  wall_cert_or_E F cellC (c016Wall F) (fun _ hc _ _ hrim => cellC_rho F hc hrim)

/-- Hole fact: at a hole point, `Cp236E x F` holds. -/
theorem holeLeaf_cp236E {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : Cp236E x F :=
  ((cp236_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Hole fact: at a hole point, `C0536E x F` holds. -/
theorem holeLeaf_c0536E {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : C0536E x F :=
  ((c0536_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Hole fact: at a hole point, `C016E x F` holds. -/
theorem holeLeaf_c016E {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : C016E x F :=
  ((c016_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Twin hole fact for `Cp236E`. -/
theorem holeLeaf_cp236E_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    Cp236E (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases cp236_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-- Twin hole fact for `C0536E`. -/
theorem holeLeaf_c0536E_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    C0536E (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases c0536_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-- Twin hole fact for `C016E`. -/
theorem holeLeaf_c016E_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    C016E (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases c016_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-! ## The narrowed open Prop -/

/-- **[OPEN] `CellCoverEmptyE4 L`**: on `CbarIn`, `OB1`, with `A236E`, `P126E`, `Cp236E`, `C0536E`, `C016E` on `x` and on
the twin, the point is not in the cell-cover residue of `L`. -/
def CellCoverEmptyE4 (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → A236E x F →
    A236E (x ∘ Sym.pi24) (Sym.sym24 F) → P126E x F → P126E (x ∘ Sym.pi24) (Sym.sym24 F) →
    Cp236E x F → Cp236E (x ∘ Sym.pi24) (Sym.sym24 F) → C0536E x F → C0536E (x ∘ Sym.pi24) (Sym.sym24 F) →
    C016E x F → C016E (x ∘ Sym.pi24) (Sym.sym24 F) → ¬ CellCoverResidue L x F

/-- The previous open Prop implies the narrower one. -/
theorem cellCoverEmptyE4_of_EP {L : List Cell24} (h : CellCoverEmptyEP L) : CellCoverEmptyE4 L :=
  fun x F hC hO hA hA' hP hP' _ _ _ _ _ _ => h x F hC hO hA hA' hP hP'

/-- `CellCoverEmptyE4 L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmptyE4 {L : List Cell24} (hN : CellCoverEmptyE4 L) (x : Fin 7 → ℝ³)
    (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_a236E h hO) (holeLeaf_a236E_twin h hO) (holeLeaf_p126E h) (holeLeaf_p126E_twin h)
    (holeLeaf_cp236E h) (holeLeaf_cp236E_twin h) (holeLeaf_c0536E h) (holeLeaf_c0536E_twin h)
    (holeLeaf_c016E h) (holeLeaf_c016E_twin h) (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmptyE4 L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmptyE4 {L : List Cell24} (hN : CellCoverEmptyE4 L) : OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_cellCoverEmptyE4 hN x F hO (holeLeaf_of_holeFull hF)

/-- [PROVED] `CellCoverEmptyE4 L` and `OSpec.OpenSpecialO` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyE4_O {L : List Cell24} (hN : CellCoverEmptyE4 L)
    (hS : OSpec.OpenSpecialO) : Open24Rupert :=
  OSpec.open24Rupert_of_split_O (openOB1_of_cellCoverEmptyE4 hN) hS

/-- [PROVED] Headline chain: `CellCoverEmptyE4 cells28` and `OSpec.OpenSpecialO` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_O (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialO) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_O hN hS

end Minimality.T24.Cell
