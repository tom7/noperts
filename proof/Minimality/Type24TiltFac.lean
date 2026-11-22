module

public import Minimality.M4jType24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Finset Filter Topology
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT

/-!
# Tilting vertex 2

Moving vertex `2` by `ε d` keeps every facet through `2` planar (they are triangles `012, 025, 126, 235, 236`):
rotate the facet `t` about its fixed edge inside a neighbour `parT t` that contains the edge but not `2`.
The result is an `S0xFac` of the moved point set `xs x d ε`, whose edge direction `x 2 - x 1` is `b + ε d`.
Facts about the other six vertices (all `FrontOf` facts of the 6-rim) at the direction `b + ε d` are then
the facts at the edge direction of the tilted solid.
-/

namespace Minimality.T24.A19.Tilt

/-- Neighbour facet containing the fixed edge of a facet through vertex 2 and not containing 2. -/
def parT : Fin 9 → Fin 9 := ![1, 1, 3, 3, 4, 1, 3, 8, 8]

/-- The solid with vertex 2 moved by `ε d`. -/
noncomputable def xs (x : Fin 7 → ℝ³) (d : ℝ³) (ε : ℝ) : Fin 7 → ℝ³ := Function.update x 2 (x 2 + ε • d)

theorem parT_ok : ∀ t : Fin 9, (2 : Fin 7) ∈ s0x_S24 t →
    (2 : Fin 7) ∉ s0x_S24 (parT t) ∧ ∀ i : Fin 7, i ∈ s0x_S24 t → i ≠ 2 → i ∈ s0x_S24 (parT t) := by decide

noncomputable def muT {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d : ℝ³) (ε : ℝ) (t : Fin 9) : ℝ :=
  if (2 : Fin 7) ∈ s0x_S24 t then -(F.f t (x 2 + ε • d)) / F.f (parT t) (x 2 + ε • d) else 0

theorem F_eval {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (y : ℝ³) :
    F.f t y = F.f t 0 + ⟪F.N t, y⟫ := by
  have := F.hN t y 0
  simp only [sub_zero] at this
  linarith

theorem F_cont {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Continuous (F.f t) := by
  have : F.f t = fun y => F.f t 0 + ⟪F.N t, y⟫ := funext (F_eval F t)
  rw [this]; fun_prop

/-- Build the tilted `S0xFac` from the strict inequalities at one `ε`. -/
noncomputable def tiltFac {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d : ℝ³) (ε : ℝ)
    (hden : ∀ t : Fin 9, (2 : Fin 7) ∈ s0x_S24 t → F.f (parT t) (x 2 + ε • d) ≠ 0)
    (hneg : ∀ (t : Fin 9) (i : Fin 7), i ∉ s0x_S24 t →
      F.f t (xs x d ε i) + muT F d ε t * F.f (parT t) (xs x d ε i) < 0) :
    S0xFac 9 s0x_S24 (xs x d ε) where
  f t y := F.f t y + muT F d ε t * F.f (parT t) y
  N t := F.N t + muT F d ε t • F.N (parT t)
  hN := by
    intro t y z
    simp only [inner_add_left, inner_smul_left, conj_trivial, ← F.hN]
    ring
  zero := by
    intro t i hi
    by_cases h2 : (2 : Fin 7) ∈ s0x_S24 t
    · by_cases hi2 : i = 2
      · subst hi2
        simp only [xs, Function.update_self, muT, h2, ↓reduceIte]
        field_simp [hden t h2]
        ring
      · have hp := (parT_ok t h2).2 i hi hi2
        simp only [xs, Function.update_of_ne hi2]
        rw [F.zero t i hi, F.zero (parT t) i hp]; ring
    · have hi2 : i ≠ 2 := fun h => h2 (h ▸ hi)
      simp only [xs, Function.update_of_ne hi2, muT, h2, ↓reduceIte, F.zero t i hi]; ring
  neg := hneg

/-- All strict inequalities hold for small `ε`. -/
theorem tilt_eventually {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (d : ℝ³) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      (∀ t : Fin 9, (2 : Fin 7) ∈ s0x_S24 t → F.f (parT t) (x 2 + ε • d) ≠ 0) ∧
      (∀ (t : Fin 9) (i : Fin 7), i ∉ s0x_S24 t →
        F.f t (xs x d ε i) + muT F d ε t * F.f (parT t) (xs x d ε i) < 0) := by
  have hxs : ∀ i, Continuous fun ε : ℝ => xs x d ε i := by
    intro i
    by_cases hi : i = 2
    · subst hi; simp only [xs, Function.update_self]; fun_prop
    · simp only [xs, Function.update_of_ne hi]; fun_prop
  have hxs2 : Continuous fun ε : ℝ => x 2 + ε • d := by fun_prop
  have hden0 : ∀ t : Fin 9, (2 : Fin 7) ∈ s0x_S24 t → F.f (parT t) (x 2) < 0 := by
    intro t ht
    exact F.neg _ _ (parT_ok t ht).1
  have hmu : ∀ t : Fin 9, ContinuousAt (fun ε : ℝ => muT F d ε t) 0 := by
    intro t
    by_cases h2 : (2 : Fin 7) ∈ s0x_S24 t
    · simp only [muT, h2, ↓reduceIte]
      refine ContinuousAt.div ?_ ?_ ?_
      · exact ((F_cont F t).comp hxs2).neg.continuousAt
      · exact ((F_cont F _).comp hxs2).continuousAt
      · simpa using (hden0 t h2).ne
    · simp only [muT, h2, ↓reduceIte]; exact continuousAt_const
  have hmu0 : ∀ t : Fin 9, muT F d 0 t = 0 := by
    intro t
    by_cases h2 : (2 : Fin 7) ∈ s0x_S24 t
    · simp only [muT, h2, ↓reduceIte, zero_smul, add_zero, F.zero t 2 h2, neg_zero, zero_div]
    · simp only [muT, h2, ↓reduceIte]
  refine Filter.Eventually.and ?_ ?_
  · rw [Filter.eventually_all]
    intro t
    by_cases h2 : (2 : Fin 7) ∈ s0x_S24 t
    · have hc : ContinuousAt (fun ε : ℝ => F.f (parT t) (x 2 + ε • d)) 0 :=
        ((F_cont F _).comp hxs2).continuousAt
      have : ∀ᶠ ε in 𝓝 (0 : ℝ), F.f (parT t) (x 2 + ε • d) < 0 :=
        hc.eventually (gt_mem_nhds (by simpa using hden0 t h2))
      exact this.mono fun ε h _ => h.ne
    · exact Filter.Eventually.of_forall fun ε h => absurd h h2
  · rw [Filter.eventually_all]; intro t
    rw [Filter.eventually_all]; intro i
    by_cases hi : i ∈ s0x_S24 t
    · exact Filter.Eventually.of_forall fun ε h => absurd hi h
    · have hc : ContinuousAt (fun ε : ℝ => F.f t (xs x d ε i) + muT F d ε t * F.f (parT t) (xs x d ε i)) 0 :=
        (((F_cont F t).comp (hxs i)).continuousAt).add
          ((hmu t).mul (((F_cont F _).comp (hxs i)).continuousAt))
      have h0 : F.f t (xs x d 0 i) + muT F d 0 t * F.f (parT t) (xs x d 0 i) < 0 := by
        have : xs x d 0 i = x i := by
          by_cases hi2 : i = 2
          · subst hi2; simp [xs]
          · simp [xs, Function.update_of_ne hi2]
        rw [this, hmu0 t, zero_mul, add_zero]; exact F.neg t i hi
      exact (hc.eventually (gt_mem_nhds h0)).mono fun ε h _ => h

end Minimality.T24.A19.Tilt
