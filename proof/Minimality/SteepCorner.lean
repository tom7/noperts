module

public import Mathlib
public import Minimality.TurningLemma
public import Minimality.DepthSeparated

@[expose] public section

/-!
# The Steep Overhung Corner (SOC), tilted-view form

Turning Lemma (`turning_lemma`) + Theorem 8.10 (`isRupert_of_depthSeparatedView`).

`steep_chain_rupert`: at the view of a rotation `R`, the silhouette `x : ZMod k → ℝ³` is a strictly
convex ccw polygon (every other point of `V` strictly inside), the depths are injective, an arc
`x l, …, x (l + m)` has strictly unimodal depths and lies strictly above all other rim depths, and
the arc turns by at least `π` (`cross2 (p l - p (l-1)) (p (l+m+1) - p (l+m)) ≤ 0`, "steep"): then `V`
is Rupert, provided there is no horizontal double normal.

`steep_overhung_corner`: the corner instance, rim `c, J, D 0, …, D (r-1), M` as `ZMod (r+3)` with
`c = 0`, `J = 1`, `D i = 2 + i`, `M = r + 2`; deep chain above `c, J, M`.

Gap to the edge-view form of the note (CORNER24ECV §2, SOC): the rim, hin, hp and the depth data are
hypotheses at the tilted view `u = g + ε w`; deriving them from the cube-corner coordinates at the
edge view `g` (stability under the tilt, `K` hiding in the corner angle) is not done here.  `hz` and
`hnd` are the genericity choices of `w`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
namespace Minimality

theorem steep_chain_rupert (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : Function.Injective fun i => (R.toEuclideanLin (x i)) 2)
    (l : ZMod k) (m : ℕ) (hm : m < k)
    (hU : ∃ t, t ≤ m ∧
      (∀ s : ℕ, s < t → (R.toEuclideanLin (x (l + (s : ZMod k)))) 2 <
        (R.toEuclideanLin (x (l + ((s + 1 : ℕ) : ZMod k)))) 2) ∧
      ∀ s : ℕ, t ≤ s → s < m → (R.toEuclideanLin (x (l + ((s + 1 : ℕ) : ZMod k)))) 2 <
        (R.toEuclideanLin (x (l + (s : ZMod k)))) 2)
    (hS : ∀ s : ℕ, s ≤ m → ∀ r : ℕ, m < r → r < k →
      (R.toEuclideanLin (x (l + (r : ZMod k)))) 2 < (R.toEuclideanLin (x (l + (s : ZMod k)))) 2)
    (hT : cross2 (proj_xy (R.toEuclideanLin (x l)) - proj_xy (R.toEuclideanLin (x (l - 1))))
      (proj_xy (R.toEuclideanLin (x (l + (m : ZMod k) + 1))) -
        proj_xy (R.toEuclideanLin (x (l + (m : ZMod k))))) ≤ 0)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  obtain ⟨a, c, hds, -⟩ := turning_lemma _ _ hp hz l m hm hU hS hT
  exact isRupert_of_depthSeparatedView V R hR x hxV hp hin hds hnd

theorem steep_overhung_corner (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    (r : ℕ) (hr : 1 ≤ r) (x : ZMod (r + 3) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : Function.Injective fun i => (R.toEuclideanLin (x i)) 2)
    (hU : ∃ t, t ≤ r - 1 ∧
      (∀ s : ℕ, s < t → (R.toEuclideanLin (x (2 + (s : ZMod (r + 3))))) 2 <
        (R.toEuclideanLin (x (2 + ((s + 1 : ℕ) : ZMod (r + 3))))) 2) ∧
      ∀ s : ℕ, t ≤ s → s < r - 1 → (R.toEuclideanLin (x (2 + ((s + 1 : ℕ) : ZMod (r + 3))))) 2 <
        (R.toEuclideanLin (x (2 + (s : ZMod (r + 3))))) 2)
    (hdeep : ∀ s : ℕ, s < r →
      (R.toEuclideanLin (x 0)) 2 < (R.toEuclideanLin (x (2 + (s : ZMod (r + 3))))) 2 ∧
      (R.toEuclideanLin (x 1)) 2 < (R.toEuclideanLin (x (2 + (s : ZMod (r + 3))))) 2 ∧
      (R.toEuclideanLin (x ((r : ZMod (r + 3)) + 2))) 2 <
        (R.toEuclideanLin (x (2 + (s : ZMod (r + 3))))) 2)
    (hturn : cross2
      (proj_xy (R.toEuclideanLin (x 2)) - proj_xy (R.toEuclideanLin (x 1)))
      (proj_xy (R.toEuclideanLin (x ((r : ZMod (r + 3)) + 2))) -
        proj_xy (R.toEuclideanLin (x ((r : ZMod (r + 3)) + 1)))) ≤ 0)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  have h0 : ((r + 3 : ℕ) : ZMod (r + 3)) = 0 := ZMod.natCast_self _
  have h0' : (r : ZMod (r + 3)) + 3 = 0 := by exact_mod_cast h0
  refine steep_chain_rupert V R hR x hxV hp hin hz 2 (r - 1) (by omega) hU ?_ ?_ hnd
  · intro s hs r' hr' hr'k
    obtain ⟨h1, h2, h3⟩ := hdeep s (by omega)
    have : r' = r ∨ r' = r + 1 ∨ r' = r + 2 := by omega
    rcases this with h | h | h
    · have e : (2 : ZMod (r + 3)) + ((r' : ℕ) : ZMod (r + 3)) = (r : ZMod (r + 3)) + 2 := by
        rw [h]; ring
      rw [e]; exact h3
    · have e : (2 : ZMod (r + 3)) + ((r' : ℕ) : ZMod (r + 3)) = 0 := by
        rw [h]; push_cast; linear_combination h0'
      rw [e]; exact h1
    · have e : (2 : ZMod (r + 3)) + ((r' : ℕ) : ZMod (r + 3)) = 1 := by
        rw [h]; push_cast; linear_combination h0'
      rw [e]; exact h2
  · have e1 : (2 : ZMod (r + 3)) - 1 = 1 := by ring
    have e2 : (2 : ZMod (r + 3)) + ((r - 1 : ℕ) : ZMod (r + 3)) = (r : ZMod (r + 3)) + 1 := by
      rw [Nat.cast_sub hr]; push_cast; ring
    rw [e1, e2, show (r : ZMod (r + 3)) + 1 + 1 = (r : ZMod (r + 3)) + 2 by ring]
    exact hturn

end Minimality
