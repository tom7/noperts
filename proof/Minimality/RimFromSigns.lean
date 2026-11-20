module

public import Minimality.FaceChordLeaf
public import Minimality.Quad05Leaf

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21

namespace Minimality.RimFromSigns

/-- **V1 (algebraic identity): ridge separation identity for two adjacent facets.**
Along a shared edge `x Q - x P` of facets `t` and `t'`, the projection
`det3 (x Q - x P) (y - x P) u` is proportional to `⟪F.N t', u⟫ * F.f t y - ⟪F.N t, u⟫ * F.f t' y`. -/
theorem det3_ridge_facets {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t t' : Fin nf) (P Q : Fin N) (hP : P ∈ S t ∧ P ∈ S t')
    (hQ : Q ∈ S t ∧ Q ∈ S t') (u : ℝ³) (hu_cross : cross u (x Q - x P) ≠ 0)
    (hl : ⟪F.N t', u⟫ • F.N t - ⟪F.N t, u⟫ • F.N t' ≠ 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y : ℝ³,
      det3 (x Q - x P) (y - x P) u = κ * (⟪F.N t', u⟫ * F.f t y - ⟪F.N t, u⟫ * F.f t' y) := by
  sorry

/-- **V1 edge-on variant: chord edge separation identity for an edge-on facet.**
When facet `t` is edge-on (`⟪F.N t, u⟫ = 0`), its normal `F.N t` is orthogonal
to both `u` and `x Q - x P`. If `cross u (x Q - x P) ≠ 0` and `F.N t ≠ 0`,
then `det3 (x Q - x P) (y - x P) u` is proportional to `F.f t y`. -/
theorem det3_edgeOn_facet {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) (P Q : Fin N) (hP : P ∈ S t) (hQ : Q ∈ S t)
    (u : ℝ³) (hnu : ⟪F.N t, u⟫ = 0) (hu_cross : cross u (x Q - x P) ≠ 0)
    (hN0 : F.N t ≠ 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y : ℝ³,
      det3 (x Q - x P) (y - x P) u = κ * F.f t y := by
  sorry

/-- **V1 sign corollary: uniform strict sign off the edge.**
Across a ridge edge `P → Q` between opposite-facing facets `t` (down) and `t'` (up),
every vertex `y` not on both facets has the exact same strict orientation sign. -/
theorem det3_sign_ridge {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t t' : Fin nf) (P Q : Fin N) (hP : P ∈ S t ∧ P ∈ S t')
    (hQ : Q ∈ S t ∧ Q ∈ S t') (u : ℝ³) (h_opp : ⟪F.N t, u⟫ < 0 ∧ 0 < ⟪F.N t', u⟫)
    (hu_cross : cross u (x Q - x P) ≠ 0)
    (hl : ⟪F.N t', u⟫ • F.N t - ⟪F.N t, u⟫ • F.N t' ≠ 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ y : Fin N, (y ∉ S t ∨ y ∉ S t') →
      0 < σ * det3 (x Q - x P) (x y - x P) u := by
  sorry

/-- **V1 edge-on sign corollary: uniform strict sign off an edge-on facet.** -/
theorem det3_sign_edgeOn {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) (P Q : Fin N) (hP : P ∈ S t) (hQ : Q ∈ S t)
    (u : ℝ³) (hnu : ⟪F.N t, u⟫ = 0) (hu_cross : cross u (x Q - x P) ≠ 0)
    (hN0 : F.N t ≠ 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ y : Fin N, y ∉ S t →
      0 < σ * det3 (x Q - x P) (x y - x P) u := by
  sorry

end Minimality.RimFromSigns

namespace Minimality.T24.RimFromSigns
open Minimality.T24.SAT Minimality.RimFromSigns

/-- **V2 (type 24, Lemma R): rim convexity and vertex 1 inside from sign pattern S*.**
At view `u` with facet 3 (`0345`) edge-on (`⟪F.N 3, u⟫ = 0`) and the sign pattern S*
(negative on facets 0, 1, 2, 4, 5; positive on facets 6, 7, 8), the quad rim `6 4 5 2`
is strictly convex (`hcyc`) and vertex 1 projects strictly inside (`h1`) for some `ρ ≠ 0`. -/
theorem lemmaR_quad_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN0 : ⟪F.N 0, u⟫ < 0) (hN1 : ⟪F.N 1, u⟫ < 0) (hN2 : ⟪F.N 2, u⟫ < 0)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN5 : ⟪F.N 5, u⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u⟫) (hN7 : 0 < ⟪F.N 7, u⟫) (hN8 : 0 < ⟪F.N 8, u⟫)
    (hN3_ne : F.N 3 ≠ 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 4) (x 5) (x 2) (i + 1) - quad (x 6) (x 4) (x 5) (x 2) i)
          (quad (x 6) (x 4) (x 5) (x 2) j - quad (x 6) (x 4) (x 5) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 4) (x 5) (x 2) (i + 1) - quad (x 6) (x 4) (x 5) (x 2) i)
          (x 1 - quad (x 6) (x 4) (x 5) (x 2) i) u) := by
  sorry

end Minimality.T24.RimFromSigns
