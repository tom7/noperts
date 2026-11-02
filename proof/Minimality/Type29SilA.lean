module

public import Minimality.Type21SilH
public import Minimality.Type29Faces

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H29S
open Minimality.H21

/-- Facet vertex sets, `A..I = 0..8`: `012, 015, 023, 035, 124, 1456, 234, 346, 356`. -/
def h29s_S : Fin 9 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 1, 5}, {0, 2, 3}, {0, 3, 5}, {1, 2, 4}, {1, 4, 5, 6}, {2, 3, 4}, {3, 4, 6},
    {3, 5, 6}]

/-- The nine facets of type 29 as an indexed family. -/
structure Fac9 (x : Fin 7 → ℝ³) where
  f : Fin 9 → ℝ³ → ℝ
  N : Fin 9 → ℝ³
  hN : ∀ t y z, f t y - f t z = ⟪N t, y - z⟫
  zero : ∀ t, ∀ i ∈ h29s_S t, f t (x i) = 0
  neg : ∀ t, ∀ i ∉ h29s_S t, f t (x i) < 0

noncomputable def h29s_fac9 {x : Fin 7 → ℝ³} (T : Facets29 x) : Fac9 x where
  f := ![T.f012.f, T.f015.f, T.f023.f, T.f035.f, T.f124.f, T.f1456.f, T.f234.f, T.f346.f,
    T.f356.f]
  N := ![T.f012.N, T.f015.N, T.f023.N, T.f035.N, T.f124.N, T.f1456.N, T.f234.N, T.f346.N,
    T.f356.N]
  hN t := by
    fin_cases t
    exacts [T.f012.hN, T.f015.hN, T.f023.hN, T.f035.hN, T.f124.hN, T.f1456.hN, T.f234.hN,
      T.f346.hN, T.f356.hN]
  zero t := by
    fin_cases t
    exacts [T.f012.zero, T.f015.zero, T.f023.zero, T.f035.zero, T.f124.zero, T.f1456.zero,
      T.f234.zero, T.f346.zero, T.f356.zero]
  neg t := by
    fin_cases t
    exacts [T.f012.neg, T.f015.neg, T.f023.neg, T.f035.neg, T.f124.neg, T.f1456.neg,
      T.f234.neg, T.f346.neg, T.f356.neg]

variable {x : Fin 7 → ℝ³}

theorem Fac9.le (F : Fac9 x) (t : Fin 9) (m : Fin 7) : F.f t (x m) ≤ 0 := by
  by_cases h : m ∈ h29s_S t
  · rw [F.zero t m h]
  · exact (F.neg t m h).le

theorem Fac9.up (F : Fac9 x) (t : Fin 9) {i j : Fin 7} (hj : j ∈ h29s_S t) (hi : i ∉ h29s_S t) :
    0 < F.f t (x j) - F.f t (x i) := by
  rw [F.zero t j hj]; linarith [F.neg t i hi]

theorem Fac9.dn (F : Fac9 x) (t : Fin 9) {i j : Fin 7} (hi : i ∈ h29s_S t) (hj : j ∉ h29s_S t) :
    F.f t (x j) - F.f t (x i) < 0 := by
  rw [F.zero t i hi]; linarith [F.neg t j hj]

noncomputable def Fac9.sil {k : ℕ} (F : Fac9 x) (c : ZMod k → Fin 7) (ea eb : ZMod k → Fin 9)
    (i0 j0 : Fin 7)
    (h0 : ∀ i, c i ∈ h29s_S (ea i) ∧ c i ∈ h29s_S (eb i))
    (h1 : ∀ i, c (i + 1) ∈ h29s_S (ea i) ∧ c (i + 1) ∈ h29s_S (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ h29s_S (ea i) ∨ m ∉ h29s_S (eb i))
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

/-- The leaf shape: a silhouette cycle `c` on `ZMod k` at the segment view `x j0 - x i0`. -/
theorem h29s_leaf_gen {k : ℕ} [NeZero k] (T : Facets29 x) (hk : 3 ≤ k) (c : ZMod k → Fin 7)
    (hc : Function.Injective c) (ea eb : ZMod k → Fin 9) (i0 j0 : Fin 7)
    (h0 : ∀ i, c i ∈ h29s_S (ea i) ∧ c i ∈ h29s_S (eb i))
    (h1 : ∀ i, c (i + 1) ∈ h29s_S (ea i) ∧ c (i + 1) ∈ h29s_S (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ h29s_S (ea i) ∨ m ∉ h29s_S (eb i))
    (hup : ∀ i, 0 < (h29s_fac9 T).f (ea i) (x j0) - (h29s_fac9 T).f (ea i) (x i0))
    (hdn : ∀ i, (h29s_fac9 T).f (eb i) (x j0) - (h29s_fac9 T).f (eb i) (x i0) < 0)
    (hU : Uni (fun i => ⟪x (c i), x j0 - x i0⟫)) :
    IsRupert (univ.image x) :=
  h21_sil_isRupert hk T.inj hc ((h29s_fac9 T).sil c ea eb i0 j0 h0 h1 hs hup hdn) hU

end H29S
end Minimality
