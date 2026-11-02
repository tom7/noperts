module

public import Minimality.Type21SilE

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

/-- Facet vertex sets, indexed `A..H = 0..7`: `014, 015, 0256, 046, 134, 135, 2346, 235`. -/
def h21S : Fin 8 → Finset (Fin 7) :=
  ![{0, 1, 4}, {0, 1, 5}, {0, 2, 5, 6}, {0, 4, 6}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4, 6}, {2, 3, 5}]

/-- The eight facets of type 21 as an indexed family. -/
structure Fac8 (x : Fin 7 → ℝ³) where
  f : Fin 8 → ℝ³ → ℝ
  N : Fin 8 → ℝ³
  hN : ∀ t y z, f t y - f t z = ⟪N t, y - z⟫
  zero : ∀ t, ∀ i ∈ h21S t, f t (x i) = 0
  neg : ∀ t, ∀ i ∉ h21S t, f t (x i) < 0

noncomputable def fac8 {x : Fin 7 → ℝ³} (T : Facets21 x) : Fac8 x where
  f := ![T.f014.f, T.f015.f, T.f0256.f, T.f046.f, T.f134.f, T.f135.f, T.f2346.f, T.f235.f]
  N := ![T.f014.N, T.f015.N, T.f0256.N, T.f046.N, T.f134.N, T.f135.N, T.f2346.N, T.f235.N]
  hN t := by
    fin_cases t
    exacts [T.f014.hN, T.f015.hN, T.f0256.hN, T.f046.hN, T.f134.hN, T.f135.hN, T.f2346.hN,
      T.f235.hN]
  zero t := by
    fin_cases t
    exacts [T.f014.zero, T.f015.zero, T.f0256.zero, T.f046.zero, T.f134.zero, T.f135.zero,
      T.f2346.zero, T.f235.zero]
  neg t := by
    fin_cases t
    exacts [T.f014.neg, T.f015.neg, T.f0256.neg, T.f046.neg, T.f134.neg, T.f135.neg,
      T.f2346.neg, T.f235.neg]

variable {x : Fin 7 → ℝ³}

theorem Fac8.le (F : Fac8 x) (t : Fin 8) (m : Fin 7) : F.f t (x m) ≤ 0 := by
  by_cases h : m ∈ h21S t
  · rw [F.zero t m h]
  · exact (F.neg t m h).le

/-- Facing up: `j` in the facet, `i` not. -/
theorem Fac8.up (F : Fac8 x) (t : Fin 8) {i j : Fin 7} (hj : j ∈ h21S t) (hi : i ∉ h21S t) :
    0 < F.f t (x j) - F.f t (x i) := by
  rw [F.zero t j hj]; linarith [F.neg t i hi]

/-- Facing down: `i` in the facet, `j` not. -/
theorem Fac8.dn (F : Fac8 x) (t : Fin 8) {i j : Fin 7} (hi : i ∈ h21S t) (hj : j ∉ h21S t) :
    F.f t (x j) - F.f t (x i) < 0 := by
  rw [F.zero t i hi]; linarith [F.neg t j hj]

/-- Build the silhouette data from facet indices `ea` (up), `eb` (down) per edge, at the segment
view `u₀ = x j - x i` (facings given as `f(x j) - f(x i)` signs). -/
noncomputable def Fac8.sil {k : ℕ} (F : Fac8 x) (c : ZMod k → Fin 7) (ea eb : ZMod k → Fin 8)
    (i0 j0 : Fin 7)
    (h0 : ∀ i, c i ∈ h21S (ea i) ∧ c i ∈ h21S (eb i))
    (h1 : ∀ i, c (i + 1) ∈ h21S (ea i) ∧ c (i + 1) ∈ h21S (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ h21S (ea i) ∨ m ∉ h21S (eb i))
    (hup : ∀ i, 0 < F.f (ea i) (x j0) - F.f (ea i) (x i0))
    (hdn : ∀ i, F.f (eb i) (x j0) - F.f (eb i) (x i0) < 0) :
    SilData k x c (x j0 - x i0) where
  A i := F.N (ea i)
  B i := F.N (eb i)
  fA i := F.f (ea i)
  fB i := F.f (eb i)
  hA i := F.hN (ea i)
  hB i := F.hN (eb i)
  zA0 i := F.zero _ _ (h0 i).1
  zA1 i := F.zero _ _ (h1 i).1
  zB0 i := F.zero _ _ (h0 i).2
  zB1 i := F.zero _ _ (h1 i).2
  nA i m := F.le _ m
  nB i m := F.le _ m
  strict i m a b := by
    rcases hs i m a b with h | h
    · exact Or.inl (F.neg _ _ h)
    · exact Or.inr (F.neg _ _ h)
  up i := by rw [← F.hN]; exact hup i
  dn i := by rw [← F.hN]; exact hdn i

/-- **The leaf shape**: a silhouette cycle `c` on `ZMod k` at the segment view `x j0 - x i0`. -/
theorem leaf_gen {k : ℕ} [NeZero k] (T : Facets21 x) (hk : 3 ≤ k) (c : ZMod k → Fin 7)
    (hc : Function.Injective c) (ea eb : ZMod k → Fin 8) (i0 j0 : Fin 7)
    (h0 : ∀ i, c i ∈ h21S (ea i) ∧ c i ∈ h21S (eb i))
    (h1 : ∀ i, c (i + 1) ∈ h21S (ea i) ∧ c (i + 1) ∈ h21S (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ h21S (ea i) ∨ m ∉ h21S (eb i))
    (hup : ∀ i, 0 < (fac8 T).f (ea i) (x j0) - (fac8 T).f (ea i) (x i0))
    (hdn : ∀ i, (fac8 T).f (eb i) (x j0) - (fac8 T).f (eb i) (x i0) < 0)
    (hU : Uni (fun i => ⟪x (c i), x j0 - x i0⟫)) :
    IsRupert (univ.image x) :=
  h21_sil_isRupert hk T.inj hc ((fac8 T).sil c ea eb i0 j0 h0 h1 hs hup hdn) hU

end H21
end Minimality
