module

public import Mathlib
public import Minimality.HiddenCap
public import Minimality.SplitRows

/-!
# The Hidden-Cap reduction, part (iv): the cap vertex imposes no row

Let `v` be a point and `a, b, c ∈ O` with `e_a = a - v`, `e_b = b - v`, `e_c = c - v`
independent, and let `u = c_a e_a + c_b e_b + c_c e_c` with `c_a, c_b, c_c` all positive or
all negative (a view in `C = ± int cone (e_a, e_b, e_c)`).  Then, with no obtuseness:

* `exists_mem_hull_add_smul`: `v + t u` lies in the triangle `conv {a, b, c}` for some `t`, so
  every linear map `f` killing `u` (a projection along `u`) has `f v ∈ f '' conv O`, and
  `image_convexHull_insert_of_mem` gives `π_u (conv (insert v O)) = π_u (conv O)`: the cap does not
  change the shadow, and `v` is a rim vertex of no shadow of `insert v O` (`hiddenAt_of_cone`).
* `det3_pos_triangle_of_cone`: the projected point `v` lies strictly inside the projected
  triangle of `a, b, c` (a triangle of `O`), in the `det3` form of `TiltCert`.
* `freeAt_insert_of_cone`: `FreeAt O u → FreeAt (insert v O) u`.  The first-order system of
  `insert v O` has no row at `v`: its `TiltCert` is the strict-triangle alternative.

Only the direction "`O` free implies `K` free" is stated: it is the one that makes `K` Rupert
(`Minimality.Split.FreeAt.isRupert`).
-/

@[expose] public section

set_option autoImplicit false

namespace Minimality.Split

open scoped RealInnerProductSpace
open Finset

/-- The four determinants of the cone view, in terms of `D = det (e_a, e_b, e_c)`. -/
theorem det3_cone (v a b c : ℝ³) (ca cb cc : ℝ) :
    det3 (b - a) (v - a) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        cc * det3 (a - v) (b - v) (c - v) ∧
    det3 (c - b) (v - b) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        ca * det3 (a - v) (b - v) (c - v) ∧
    det3 (a - c) (v - c) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        cb * det3 (a - v) (b - v) (c - v) ∧
    det3 (b - a) (c - a) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        (ca + cb + cc) * det3 (a - v) (b - v) (c - v) ∧
    det3 (c - a) (v - a) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        -(cb * det3 (a - v) (b - v) (c - v)) ∧
    det3 (b - c) (v - c) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        -(ca * det3 (a - v) (b - v) (c - v)) ∧
    det3 (a - b) (v - b) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        -(cc * det3 (a - v) (b - v) (c - v)) ∧
    det3 (c - a) (b - a) (ca • (a - v) + cb • (b - v) + cc • (c - v)) =
        -((ca + cb + cc) * det3 (a - v) (b - v) (c - v)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> ring

/-- The projected point `v` lies strictly inside the projected triangle of two orderings of
`a, b, c`, one of which is positively oriented (`TiltCert`'s triangle alternative). -/
theorem det3_pos_triangle_of_cone (v a b c : ℝ³) (ca cb cc : ℝ)
    (hD : det3 (a - v) (b - v) (c - v) ≠ 0)
    (hc : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0)) :
    let u := ca • (a - v) + cb • (b - v) + cc • (c - v)
    (0 < det3 (b - a) (c - a) u ∧ 0 < det3 (b - a) (v - a) u ∧ 0 < det3 (c - b) (v - b) u ∧
      0 < det3 (a - c) (v - c) u) ∨
    (0 < det3 (c - a) (b - a) u ∧ 0 < det3 (c - a) (v - a) u ∧ 0 < det3 (b - c) (v - c) u ∧
      0 < det3 (a - b) (v - b) u) := by
  intro u
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := det3_cone v a b c ca cb cc
  rw [h1, h2, h3, h4]
  rw [h5, h6, h7, h8]
  rcases lt_or_gt_of_ne hD with hn | hp <;> rcases hc with ⟨x, y, z⟩ | ⟨x, y, z⟩
  · right
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · left
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · left
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · right
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **Hidden-Cap (iv), freedom.**  At a cone view `u` of the three edges `e_a, e_b, e_c` of `v`
(to `a, b, c ∈ O`, independent), `v` imposes no row: if `O` is first-order free at `u`, then so is
`insert v O`.  (The coefficients are all positive
or all negative.) -/
theorem freeAt_insert_of_cone (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hD : det3 (a - v) (b - v) (c - v) ≠ 0) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0))
    (hfree : FreeAt O (ca • (a - v) + cb • (b - v) + cc • (c - v))) :
    FreeAt (insert v O) (ca • (a - v) + cb • (b - v) + cc • (c - v)) := by
  obtain ⟨ω, τ, h⟩ := hfree
  refine ⟨ω, τ, fun y hy => ?_⟩
  rcases Finset.mem_insert.1 hy with rfl | hyO
  · right
    rcases det3_pos_triangle_of_cone y a b c ca cb cc hD hs with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩
    · exact ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, c,
        Finset.mem_insert_of_mem hc, t1, t2, t3, t4⟩
    · exact ⟨a, Finset.mem_insert_of_mem ha, c, Finset.mem_insert_of_mem hc, b,
        Finset.mem_insert_of_mem hb, t1, t2, t3, t4⟩
  · rcases h y hyO with ⟨y₀, h0, y₁, h1, t⟩ | ⟨p, hp, q, hq, r, hr, t⟩
    · exact Or.inl ⟨y₀, Finset.mem_insert_of_mem h0, y₁, Finset.mem_insert_of_mem h1, t⟩
    · exact Or.inr ⟨p, Finset.mem_insert_of_mem hp, q, Finset.mem_insert_of_mem hq, r,
        Finset.mem_insert_of_mem hr, t⟩

/-- The point `v + (1 / (c_a + c_b + c_c)) • u` lies in the triangle `conv {a, b, c}`. -/
theorem exists_mem_hull_add_smul (v a b c : ℝ³) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0)) :
    v + (1 / (ca + cb + cc)) • (ca • (a - v) + cb • (b - v) + cc • (c - v)) ∈
      convexHull ℝ {a, b, c} := by
  have hne : ca + cb + cc ≠ 0 := by rcases hs with ⟨x, y, z⟩ | ⟨x, y, z⟩ <;> intro h <;> linarith
  have hw : ∀ k, 0 ≤ ![ca, cb, cc] k / (ca + cb + cc) := by
    intro k
    rcases hs with ⟨x, y, z⟩ | ⟨x, y, z⟩
    · fin_cases k <;> simp <;> positivity
    · fin_cases k <;> simp <;> exact div_nonneg_of_nonpos (by linarith) (by linarith)
  have hsum : ∑ k, ![ca, cb, cc] k / (ca + cb + cc) = 1 := by
    simp [Fin.sum_univ_three, ← add_div, div_self hne]
  have hmem := (convex_convexHull ℝ ({a, b, c} : Set ℝ³)).sum_mem (t := Finset.univ)
    (w := fun k => ![ca, cb, cc] k / (ca + cb + cc)) (z := ![a, b, c])
    (fun k _ => hw k) hsum (fun k _ => subset_convexHull ℝ _ (by fin_cases k <;> simp))
  convert hmem using 1
  ext i
  simp [Fin.sum_univ_three]
  field_simp
  ring

/-- A linear map that sends a point `v` into the image of the hull of `O` leaves the image of the
hull unchanged when `v` is added. -/
theorem image_convexHull_insert_of_mem {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : ℝ³ →ₗ[ℝ] F) (O : Set ℝ³) (v : ℝ³) (h : f v ∈ f '' convexHull ℝ O) :
    f '' convexHull ℝ (insert v O) = f '' convexHull ℝ O := by
  apply Set.Subset.antisymm
  · rw [LinearMap.image_convexHull, LinearMap.image_convexHull]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rw [Set.image_insert_eq]
    refine Set.insert_subset ?_ (subset_convexHull ℝ _)
    rwa [LinearMap.image_convexHull] at h
  · exact Set.image_mono (convexHull_mono (Set.subset_insert _ _))

/-- **Hidden-Cap (iv), shadow.**  At a cone view `u`, every projection `f` along `u` (a linear map
with `f u = 0`) has the same image of the hull of `insert v O` as of `O`. -/
theorem image_hull_insert_of_cone {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : ℝ³ →ₗ[ℝ] F) (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (ca cb cc : ℝ) (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0))
    (hf : f (ca • (a - v) + cb • (b - v) + cc • (c - v)) = 0) :
    f '' convexHull ℝ (insert v (O : Set ℝ³)) = f '' convexHull ℝ (O : Set ℝ³) := by
  apply image_convexHull_insert_of_mem
  refine ⟨_, convexHull_mono ?_ (exists_mem_hull_add_smul v a b c ca cb cc hs), ?_⟩
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> simpa
  · rw [map_add, map_smul, hf, smul_zero, add_zero]

end Minimality.Split
