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

open scoped RealInnerProductSpace Topology
open Finset Filter

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

/-! ### Converse of Hidden-Cap (iv) (`freeAt_of_insert_of_cone`) -/

private theorem det3_plucker (p q a b u : ℝ³) :
    det3 p q u * det3 a b u = det3 p a u * det3 q b u - det3 p b u * det3 q a u := by
  simp only [det3]; ring

private theorem det3_tri_bary (p q v x r u : ℝ³) :
    det3 (v - q) (x - q) u * det3 (p - x) r u +
      det3 (p - v) (x - v) u * det3 (q - x) r u +
      det3 (q - p) (x - p) u * det3 (v - x) r u = 0 := by
  simp only [det3, PiLp.sub_apply]; ring

private theorem exists_delta_det3_ne (S : Finset (ℝ³ × ℝ³)) (u : ℝ³)
    (hS : ∀ p ∈ S, cross (p.2 - p.1) u ≠ 0) :
    ∃ δ : ℝ³, ∀ p ∈ S, det3 (p.2 - p.1) δ u ≠ 0 := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ⟩ := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    by_cases ha0 : det3 (a.2 - a.1) δ u ≠ 0
    · exact ⟨δ, fun p hp => by
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact ha0
        · exact hδ p hp'⟩
    · push_neg at ha0
      set n := cross (a.2 - a.1) u
      have hn : n ≠ 0 := hS a (Finset.mem_insert_self a s)
      have hnn : det3 (a.2 - a.1) n u ≠ 0 := by
        have h1 : det3 (a.2 - a.1) n u = -⟪n, n⟫ := by
          simp only [n, det3, cross_apply_zero, cross_apply_one, cross_apply_two,
            PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
          ring
        rw [h1, neg_ne_zero, inner_self_ne_zero]
        exact hn
      have hev : ∀ᶠ ε : ℝ in Filter.atTop, ∀ p ∈ s, det3 (p.2 - p.1) (δ + ε • n) u ≠ 0 := by
        rw [Finset.eventually_all]
        intro p hp
        have hp0 := hδ p hp
        have hlin : ∀ ε : ℝ, det3 (p.2 - p.1) (δ + ε • n) u =
            det3 (p.2 - p.1) δ u + ε * det3 (p.2 - p.1) n u := fun ε => by
          simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        by_cases hpn : det3 (p.2 - p.1) n u = 0
        · filter_upwards with ε; rw [hlin, hpn, mul_zero, add_zero]; exact hp0
        · filter_upwards [Filter.eventually_gt_atTop (|det3 (p.2 - p.1) δ u| / |det3 (p.2 - p.1) n u|)]
            with ε hε
          rw [hlin]
          intro heq
          have h1 : |ε| * |det3 (p.2 - p.1) n u| = |det3 (p.2 - p.1) δ u| := by
            have : ε * det3 (p.2 - p.1) n u = -det3 (p.2 - p.1) δ u := by linarith
            rw [← abs_mul, this, abs_neg]
          have h2 : |det3 (p.2 - p.1) δ u| / |det3 (p.2 - p.1) n u| < ε := hε
          have h3 : |det3 (p.2 - p.1) δ u| < ε * |det3 (p.2 - p.1) n u| :=
            (div_lt_iff₀ (abs_pos.mpr hpn)).mp h2
          have h4 : 0 ≤ ε := le_trans (div_nonneg (abs_nonneg _) (abs_nonneg _)) h2.le
          rw [abs_of_nonneg h4] at h1
          linarith
      obtain ⟨ε, hεs, hε0⟩ := (hev.and (Filter.eventually_gt_atTop (0 : ℝ))).exists
      refine ⟨δ + ε • n, fun p hp => ?_⟩
      rcases Finset.mem_insert.mp hp with hp_eq | hp'
      · rw [hp_eq]
        have hlin : det3 (a.2 - a.1) (δ + ε • n) u =
            det3 (a.2 - a.1) δ u + ε * det3 (a.2 - a.1) n u := by
          simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        rw [hlin, ha0, zero_add]
        exact mul_ne_zero hε0.ne' hnn
      · exact hεs p hp'

private theorem wedge_of_pos_comb (S : Finset ℝ³) (w : ℝ³ → ℝ) (m u : ℝ³)
    (hw : ∀ s ∈ S, 0 < w s)
    (hsum : ∀ z : ℝ³, ∑ s ∈ S, w s * det3 s z u = 0)
    (hne : ∀ s ∈ S, det3 s m u ≠ 0)
    (hnoncol : ∃ s₁ ∈ S, ∃ s₂ ∈ S, det3 s₁ s₂ u ≠ 0) :
    ∃ y₀ ∈ S, ∃ y₁ ∈ S, 0 < det3 y₁ y₀ u ∧ 0 < det3 y₁ m u ∧ 0 < det3 m y₀ u := by
  classical
  set Spos := S.filter (fun s => 0 < det3 s m u)
  set Sneg := S.filter (fun s => det3 s m u < 0)
  have hSpos_ne : Spos.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ s ∈ S, det3 s m u < 0 := fun s hs => by
      rcases lt_or_gt_of_ne (hne s hs) with h | h
      · exact h
      · exfalso
        have : s ∈ Spos := Finset.mem_filter.mpr ⟨hs, h⟩
        rw [hemp] at this; exact Finset.notMem_empty s this
    obtain ⟨s₁, hs₁, -, -, _⟩ := hnoncol
    have hlt : ∑ s ∈ S, w s * det3 s m u < 0 :=
      Finset.sum_neg (fun s hs => mul_neg_of_pos_of_neg (hw s hs) (hall s hs)) ⟨s₁, hs₁⟩
    linarith [hsum m]
  have hSneg_ne : Sneg.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ s ∈ S, 0 < det3 s m u := fun s hs => by
      rcases lt_or_gt_of_ne (hne s hs) with h | h
      · exfalso
        have : s ∈ Sneg := Finset.mem_filter.mpr ⟨hs, h⟩
        rw [hemp] at this; exact Finset.notMem_empty s this
      · exact h
    obtain ⟨s₁, hs₁, -, -, _⟩ := hnoncol
    have hgt : 0 < ∑ s ∈ S, w s * det3 s m u :=
      Finset.sum_pos (fun s hs => mul_pos (hw s hs) (hall s hs)) ⟨s₁, hs₁⟩
    linarith [hsum m]
  by_contra hnowedge
  push_neg at hnowedge
  obtain ⟨s₀, hs₀⟩ := hSpos_ne
  have hs₀_S : s₀ ∈ S := (Finset.mem_filter.mp hs₀).1
  have hs₀_pos : 0 < det3 s₀ m u := (Finset.mem_filter.mp hs₀).2
  let α : ℝ³ → ℝ := fun s => det3 s s₀ u
  let β : ℝ³ → ℝ := fun s => det3 s m u
  have hrel : ∀ y₁ ∈ Spos, ∀ y₀ ∈ Sneg, -α y₁ / β y₁ ≤ α y₀ / (-β y₀) := by
    intro y₁ hy₁ y₀ hy₀
    have hy₁S : y₁ ∈ S := (Finset.mem_filter.mp hy₁).1
    have hβ₁ : 0 < β y₁ := (Finset.mem_filter.mp hy₁).2
    have hy₀S : y₀ ∈ S := (Finset.mem_filter.mp hy₀).1
    have hβ₀ : β y₀ < 0 := (Finset.mem_filter.mp hy₀).2
    have hm₀ : 0 < det3 m y₀ u := by
      have : det3 m y₀ u = -det3 y₀ m u := by simp only [det3]; ring
      linarith
    have hle : det3 y₁ y₀ u ≤ 0 := by
      by_contra hlt
      exact absurd hm₀ (not_lt.mpr (hnowedge y₀ hy₀S y₁ hy₁S (not_le.mp hlt) hβ₁))
    have hpl : det3 y₁ y₀ u * β s₀ = α y₁ * β y₀ - β y₁ * α y₀ :=
      det3_plucker y₁ y₀ s₀ m u
    have hprod : α y₁ * β y₀ - β y₁ * α y₀ ≤ 0 := by
      rw [← hpl]
      exact mul_nonpos_of_nonpos_of_nonneg hle hs₀_pos.le
    rw [div_le_div_iff₀ hβ₁ (neg_pos.mpr hβ₀)]
    nlinarith
  set vals := Spos.image (fun y₁ => -α y₁ / β y₁)
  have hvals_ne : vals.Nonempty := Finset.Nonempty.image ⟨s₀, hs₀⟩ _
  set c := vals.max' hvals_ne
  have hc_ge : ∀ s ∈ S, 0 ≤ α s + c * β s := by
    intro s hs
    rcases lt_or_gt_of_ne (hne s hs) with hneg | hpos
    · have hs_neg : s ∈ Sneg := Finset.mem_filter.mpr ⟨hs, hneg⟩
      have hmin : c ≤ α s / (-β s) := by
        rw [Finset.max'_le_iff]
        intro v hv
        obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hv
        exact hrel y₁ hy₁ s hs_neg
      have h1 : c * (-β s) ≤ α s := (le_div_iff₀ (neg_pos.mpr hneg)).mp hmin
      linarith
    · have hs_pos : s ∈ Spos := Finset.mem_filter.mpr ⟨hs, hpos⟩
      have hmax : -α s / β s ≤ c := Finset.le_max' vals _ (Finset.mem_image_of_mem _ hs_pos)
      have h1 : -α s ≤ c * β s := (div_le_iff₀ hpos).mp hmax
      linarith
  have hsum_comb : ∑ s ∈ S, w s * (α s + c * β s) = 0 := by
    simp only [mul_add, Finset.sum_add_distrib]
    have h1 : ∑ s ∈ S, w s * α s = 0 := hsum s₀
    have h2 : ∑ s ∈ S, w s * (c * β s) = c * ∑ s ∈ S, w s * β s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by ring
    rw [h1, h2, hsum m, mul_zero, add_zero]
  have hzero : ∀ s ∈ S, α s + c * β s = 0 := fun s hs => by
    have hnonneg : ∀ t ∈ S, 0 ≤ w t * (α t + c * β t) :=
      fun t ht => mul_nonneg (hw t ht).le (hc_ge t ht)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_comb s hs
    exact (mul_eq_zero.mp h0).resolve_left (hw s hs).ne'
  obtain ⟨s₁, hs₁, s₂, hs₂, hdet⟩ := hnoncol
  have hpl := det3_plucker s₁ s₂ s₀ m u
  have hs₁0 := hzero s₁ hs₁
  have hs₂0 := hzero s₂ hs₂
  have heq0 : det3 s₁ s₂ u * β s₀ = 0 := by
    rw [hpl]
    change α s₁ * β s₂ - β s₁ * α s₂ = 0
    linear_combination β s₂ * hs₁0 - β s₁ * hs₂0
  exact hdet ((mul_eq_zero.mp heq0).resolve_right hs₀_pos.ne')

private theorem tiltCert_wedge_replace (O : Finset ℝ³) (v a b c : ℝ³)
    (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0))
    (u : ℝ³) (hu : u = ca • (a - v) + cb • (b - v) + cc • (c - v)) (ω τ x : ℝ³)
    (hne : ∀ y ∈ O, cross (y - x) u ≠ 0 → det3 (y - x) (cross ω x + τ) u ≠ 0)
    (y₀ : ℝ³) (hy₀ : y₀ ∈ O)
    (hdet : 0 < det3 (v - x) (y₀ - x) u)
    (hm1 : 0 < det3 (v - x) (cross ω x + τ) u)
    (hm0 : 0 < det3 (x - y₀) (cross ω x + τ) u) :
    TiltCert O u ω τ x := by
  left
  set m := cross ω x + τ
  have hne_c : ca + cb + cc ≠ 0 := by rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
  have hcomb : ∀ z : ℝ³, (ca + cb + cc) * det3 (v - x) z u =
      ca * det3 (a - x) z u + cb * det3 (b - x) z u + cc * det3 (c - x) z u := fun z => by
    have hv : (ca + cb + cc) • (v - x) =
        ca • (a - x) + cb • (b - x) + cc • (c - x) - (ca • (a - v) + cb • (b - v) + cc • (c - v)) := by
      module
    have h0 : det3 ((ca + cb + cc) • (v - x)) z u =
        det3 (ca • (a - x) + cb • (b - x) + cc • (c - x) - (ca • (a - v) + cb • (b - v) + cc • (c - v))) z u := by
      rw [hv]
    have hu0 : det3 (ca • (a - v) + cb • (b - v) + cc • (c - v)) z u = 0 := by
      rw [← hu]; simp only [det3]; ring
    simp only [det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 hu0 ⊢
    linarith
  have hcase : ∀ (k : ℝ) (la lb lc : ℝ), 0 < la → 0 < lb → 0 < lc →
      (∀ z : ℝ³, det3 (v - x) z u = la * det3 (a - x) z u + lb * det3 (b - x) z u + lc * det3 (c - x) z u) →
      ∃ y₀' ∈ O, ∃ y₁' ∈ O, 0 < det3 (y₁' - x) (y₀' - x) u ∧ 0 < det3 (y₁' - x) m u ∧ 0 < det3 (x - y₀') m u := by
    intro _ la lb lc hla hlb hlc hform
    by_cases ha_both : 0 < det3 (a - x) (y₀ - x) u ∧ 0 < det3 (a - x) m u
    · exact ⟨y₀, hy₀, a, ha, ha_both.1, ha_both.2, hm0⟩
    by_cases hb_both : 0 < det3 (b - x) (y₀ - x) u ∧ 0 < det3 (b - x) m u
    · exact ⟨y₀, hy₀, b, hb, hb_both.1, hb_both.2, hm0⟩
    by_cases hc_both : 0 < det3 (c - x) (y₀ - x) u ∧ 0 < det3 (c - x) m u
    · exact ⟨y₀, hy₀, c, hc, hc_both.1, hc_both.2, hm0⟩
    have hm_pos : 0 < det3 m (y₀ - x) u := by
      have : det3 (x - y₀) m u = det3 m (y₀ - x) u := by simp only [det3, PiLp.sub_apply]; ring
      linarith
    have hex_p : ∃ p ∈ ({a, b, c} : Finset ℝ³), 0 < det3 (p - x) m u ∧ det3 (p - x) (y₀ - x) u ≤ 0 := by
      by_contra hno
      push_neg at hno
      have ha1 : det3 (a - x) m u ≤ 0 := by
        by_contra h; exact ha_both ⟨hno a (by simp) (not_le.mp h), not_le.mp h⟩
      have hb1 : det3 (b - x) m u ≤ 0 := by
        by_contra h; exact hb_both ⟨hno b (by simp) (not_le.mp h), not_le.mp h⟩
      have hc1 : det3 (c - x) m u ≤ 0 := by
        by_contra h; exact hc_both ⟨hno c (by simp) (not_le.mp h), not_le.mp h⟩
      have := hform m
      nlinarith
    have hex_q : ∃ q ∈ ({a, b, c} : Finset ℝ³), det3 (q - x) m u ≤ 0 ∧ 0 < det3 (q - x) (y₀ - x) u := by
      by_contra hno
      push_neg at hno
      have ha1 : det3 (a - x) (y₀ - x) u ≤ 0 := by
        by_contra h
        have hpos := not_le.mp h
        by_cases hm : 0 < det3 (a - x) m u
        · exact ha_both ⟨hpos, hm⟩
        · exact absurd (hno a (by simp) (not_lt.mp hm)) (not_le.mpr hpos)
      have hb1 : det3 (b - x) (y₀ - x) u ≤ 0 := by
        by_contra h
        have hpos := not_le.mp h
        by_cases hm : 0 < det3 (b - x) m u
        · exact hb_both ⟨hpos, hm⟩
        · exact absurd (hno b (by simp) (not_lt.mp hm)) (not_le.mpr hpos)
      have hc1 : det3 (c - x) (y₀ - x) u ≤ 0 := by
        by_contra h
        have hpos := not_le.mp h
        by_cases hm : 0 < det3 (c - x) m u
        · exact hc_both ⟨hpos, hm⟩
        · exact absurd (hno c (by simp) (not_lt.mp hm)) (not_le.mpr hpos)
      have := hform (y₀ - x)
      nlinarith
    obtain ⟨q₀, hq₀_mem, hq₀_m, hq₀_y⟩ := hex_q
    have hq_m_lt : ∀ q ∈ ({a, b, c} : Finset ℝ³), 0 < det3 (q - x) (y₀ - x) u → det3 (q - x) m u < 0 := by
      intro q hq_mem hq_y
      have hqO : q ∈ O := by
        rcases Finset.mem_insert.mp hq_mem with rfl | h1
        · exact ha
        · rcases Finset.mem_insert.mp h1 with rfl | h2
          · exact hb
          · exact Finset.mem_singleton.mp h2 ▸ hc
      have hq_m : det3 (q - x) m u ≤ 0 := by
        by_contra h
        have hpos : 0 < det3 (q - x) m u := not_le.mp h
        rcases Finset.mem_insert.mp hq_mem with rfl | h1
        · exact ha_both ⟨hq_y, hpos⟩
        · rcases Finset.mem_insert.mp h1 with rfl | h2
          · exact hb_both ⟨hq_y, hpos⟩
          · exact (Finset.mem_singleton.mp h2 ▸ hc_both) ⟨hq_y, hpos⟩
      have hq_cross : cross (q - x) u ≠ 0 := by
        intro h0
        have : det3 (q - x) (y₀ - x) u = 0 := by
          have : det3 (q - x) (y₀ - x) u = -⟪cross (q - x) u, y₀ - x⟫ := by
            simp only [det3, cross_apply_zero, cross_apply_one, cross_apply_two,
              PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
              PiLp.sub_apply]; ring
          rw [this, h0, inner_zero_left, neg_zero]
        linarith
      exact lt_of_le_of_ne hq_m (hne q hqO hq_cross)
    by_cases hw : ∃ p ∈ ({a, b, c} : Finset ℝ³), ∃ q ∈ ({a, b, c} : Finset ℝ³),
        0 < det3 (p - x) m u ∧ 0 < det3 (q - x) (y₀ - x) u ∧ 0 < det3 (p - x) (q - x) u
    · obtain ⟨p, hp_mem, q, hq_mem, hp_m, hq_y, hpq⟩ := hw
      have hpO : p ∈ O := by rcases Finset.mem_insert.mp hp_mem with rfl | h1 <;> [exact ha; rcases Finset.mem_insert.mp h1 with rfl | h2 <;> [exact hb; exact Finset.mem_singleton.mp h2 ▸ hc]]
      have hqO : q ∈ O := by rcases Finset.mem_insert.mp hq_mem with rfl | h1 <;> [exact ha; rcases Finset.mem_insert.mp h1 with rfl | h2 <;> [exact hb; exact Finset.mem_singleton.mp h2 ▸ hc]]
      have hq_lt := hq_m_lt q hq_mem hq_y
      have hxm_q : 0 < det3 (x - q) m u := by
        have : det3 (x - q) m u = -det3 (q - x) m u := by simp only [det3, PiLp.sub_apply]; ring
        linarith
      exact ⟨q, hqO, p, hpO, hpq, hp_m, hxm_q⟩
    · exfalso
      push_neg at hw
      let SQ := ({a, b, c} : Finset ℝ³).filter (fun s => 0 < det3 (s - x) (y₀ - x) u)
      have hSQ_ne : SQ.Nonempty := ⟨q₀, Finset.mem_filter.mpr ⟨hq₀_mem, hq₀_y⟩⟩
      obtain ⟨q_star, hqs_mem, hqs_max⟩ := SQ.exists_max_image
        (fun s => det3 (s - x) (y₀ - x) u / (-det3 (s - x) m u)) hSQ_ne
      have hqs_mem' : q_star ∈ ({a, b, c} : Finset ℝ³) := (Finset.mem_filter.mp hqs_mem).1
      have hqs_y : 0 < det3 (q_star - x) (y₀ - x) u := (Finset.mem_filter.mp hqs_mem).2
      have hqs_m : 0 < -det3 (q_star - x) m u := neg_pos.mpr (hq_m_lt q_star hqs_mem' hqs_y)
      have hle_all : ∀ s ∈ ({a, b, c} : Finset ℝ³),
          (-det3 (q_star - x) m u) * det3 (s - x) (y₀ - x) u +
            det3 (q_star - x) (y₀ - x) u * det3 (s - x) m u ≤ 0 := by
        intro s hs_mem
        by_cases hsy : 0 < det3 (s - x) (y₀ - x) u
        · have hs_m : 0 < -det3 (s - x) m u := neg_pos.mpr (hq_m_lt s hs_mem hsy)
          have hdiv := hqs_max s (Finset.mem_filter.mpr ⟨hs_mem, hsy⟩)
          rw [div_le_div_iff₀ hs_m hqs_m] at hdiv
          linarith
        · by_cases hsm : 0 < det3 (s - x) m u
          · have hpq_le : det3 (s - x) (q_star - x) u ≤ 0 := hw s hs_mem q_star hqs_mem' hsm hqs_y
            have hpl := det3_plucker (s - x) (q_star - x) m (y₀ - x) u
            have hprod : det3 (s - x) (q_star - x) u * det3 m (y₀ - x) u ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hpq_le hm_pos.le
            linarith
          · have hsy_le : det3 (s - x) (y₀ - x) u ≤ 0 := not_lt.mp hsy
            have hsm_le : det3 (s - x) m u ≤ 0 := not_lt.mp hsm
            nlinarith
      have h_a := hle_all a (by simp)
      have h_b := hle_all b (by simp)
      have h_c := hle_all c (by simp)
      have hform_y := hform (y₀ - x)
      have hform_m := hform m
      have hv_pos : 0 < (-det3 (q_star - x) m u) * det3 (v - x) (y₀ - x) u +
          det3 (q_star - x) (y₀ - x) u * det3 (v - x) m u := by nlinarith
      nlinarith
  rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hpos : 0 < ca + cb + cc := by linarith
    refine hcase (ca + cb + cc) (ca / (ca + cb + cc)) (cb / (ca + cb + cc)) (cc / (ca + cb + cc))
      (div_pos h1 hpos) (div_pos h2 hpos) (div_pos h3 hpos) fun z => ?_
    have := hcomb z
    field_simp [hpos.ne']
    linarith
  · have hneg : ca + cb + cc < 0 := by linarith
    refine hcase (ca + cb + cc) (ca / (ca + cb + cc)) (cb / (ca + cb + cc)) (cc / (ca + cb + cc))
      (div_pos_of_neg_of_neg h1 hneg) (div_pos_of_neg_of_neg h2 hneg) (div_pos_of_neg_of_neg h3 hneg) fun z => ?_
    have := hcomb z
    field_simp [hneg.ne]
    linarith

/-- **Hidden-Cap (iv), converse.** At a cone view `u = ca (a - v) + cb (b - v) + cc (c - v)`
of three independent edges to `a, b, c ∈ O` (coefficients all positive or all negative),
first-order freedom of `insert v O` at `u` implies first-order freedom of `O` at `u`. -/
theorem freeAt_of_insert_of_cone (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hD : det3 (a - v) (b - v) (c - v) ≠ 0) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0))
    (hfree : FreeAt (insert v O) (ca • (a - v) + cb • (b - v) + cc • (c - v))) :
    FreeAt O (ca • (a - v) + cb • (b - v) + cc • (c - v)) := by
  classical
  set u := ca • (a - v) + cb • (b - v) + cc • (c - v)
  obtain ⟨ω, τ, hcert⟩ := hfree
  -- Step 1: perturb τ to τ' so cross ω x + τ' avoids all nonzero rays y - x (x, y ∈ O)
  let pairs := (O ×ˢ O).filter (fun p => cross (p.2 - p.1) u ≠ 0)
  obtain ⟨δ, hδ⟩ := exists_delta_det3_ne pairs u (fun p hp => (Finset.mem_filter.mp hp).2)
  have hev_cert : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ insert v O, TiltCert (insert v O) u ω (τ + ε • δ) z := by
    rw [Finset.eventually_all]
    intro z hz
    rcases hcert z hz with ⟨y₀, hy₀, y₁, hy₁, h1, h2, h3⟩ | ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩
    · have hc2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (y₁ - z) (cross ω z + (τ + ε • δ)) u := by
        have heq : ∀ ε : ℝ, det3 (y₁ - z) (cross ω z + (τ + ε • δ)) u =
            det3 (y₁ - z) (cross ω z + τ) u + ε * det3 (y₁ - z) δ u := fun ε => by
          simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        simp_rw [heq]
        exact Minimality.eventually_pos_affine (Or.inl h2)
      have hc3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (z - y₀) (cross ω z + (τ + ε • δ)) u := by
        have heq : ∀ ε : ℝ, det3 (z - y₀) (cross ω z + (τ + ε • δ)) u =
            det3 (z - y₀) (cross ω z + τ) u + ε * det3 (z - y₀) δ u := fun ε => by
          simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        simp_rw [heq]
        exact Minimality.eventually_pos_affine (Or.inl h3)
      filter_upwards [hc2, hc3] with ε h2' h3'
      exact Or.inl ⟨y₀, hy₀, y₁, hy₁, h1, h2', h3'⟩
    · filter_upwards with ε
      exact Or.inr ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩
  have hev_ne : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ x ∈ O, ∀ y ∈ O, cross (y - x) u ≠ 0 → det3 (y - x) (cross ω x + (τ + ε • δ)) u ≠ 0 := by
    rw [Finset.eventually_all]
    intro x hx
    rw [Finset.eventually_all]
    intro y hy
    by_cases hcr : cross (y - x) u = 0
    · filter_upwards with _ h; exact absurd hcr h
    · have hmem : (x, y) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hcr⟩
      have hδp : det3 (y - x) δ u ≠ 0 := hδ (x, y) hmem
      have hlin : ∀ ε : ℝ, det3 (y - x) (cross ω x + (τ + ε • δ)) u =
          det3 (y - x) (cross ω x + τ) u + ε * det3 (y - x) δ u := fun ε => by
        simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      by_cases h0 : det3 (y - x) (cross ω x + τ) u = 0
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) _
        rw [hlin, h0, zero_add]
        exact mul_ne_zero hε.ne' hδp
      · have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            det3 (y - x) (cross ω x + τ) u + ε * det3 (y - x) δ u ≠ 0 := by
          rcases lt_or_gt_of_ne h0 with hn | hp
          · filter_upwards [Minimality.eventually_pos_affine (Or.inl (neg_pos.mpr hn)) (B := -det3 (y - x) δ u)]
              with ε hε
            linarith
          · filter_upwards [Minimality.eventually_pos_affine (Or.inl hp) (B := det3 (y - x) δ u)] with ε hε
            linarith
        filter_upwards [hpos] with ε hε _
        rw [hlin]; exact hε
  obtain ⟨ε, hcert', hne'⟩ := (hev_cert.and hev_ne).exists
  refine ⟨ω, τ + ε • δ, fun x hx => ?_⟩
  set τ' := τ + ε • δ
  set m := cross ω x + τ'
  have hne_x : ∀ y ∈ O, cross (y - x) u ≠ 0 → det3 (y - x) m u ≠ 0 := hne' x hx
  rcases hcert' x (Finset.mem_insert_of_mem hx) with
      ⟨y₀, hy₀, y₁, hy₁, h1, h2, h3⟩ | ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩
  · -- Case 1: Wedge in insert v O
    rcases Finset.mem_insert.mp hy₀ with hy₀_eq | hy₀O
    · rcases Finset.mem_insert.mp hy₁ with hy₁_eq | hy₁O
      · exfalso; rw [hy₀_eq, hy₁_eq] at h1; simp only [det3, PiLp.sub_apply] at h1; linarith
      · rw [hy₀_eq] at h1 h3
        have hs_neg : (0 < -ca ∧ 0 < -cb ∧ 0 < -cc) ∨ (-ca < 0 ∧ -cb < 0 ∧ -cc < 0) := by
          rcases hs with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
          · right; exact ⟨by linarith, by linarith, by linarith⟩
          · left; exact ⟨by linarith, by linarith, by linarith⟩
        have h_ne_neg : ∀ y ∈ O, cross (y - x) (-u) ≠ 0 → det3 (y - x) (cross ω x + τ') (-u) ≠ 0 := by
          intro y hy hcr
          have hcr' : cross (y - x) u ≠ 0 := by
            intro h0
            apply hcr
            have hc0 : cross (y - x) (-u) = -cross (y - x) u := by
              ext i; fin_cases i <;> simp [cross] <;> ring
            rw [hc0, h0, neg_zero]
          have := hne_x y hy hcr'
          change det3 (y - x) m (-u) ≠ 0
          rw [show det3 (y - x) m (-u) = -det3 (y - x) m u from by
            simp only [det3, PiLp.neg_apply]; ring]
          exact neg_ne_zero.mpr this
        have hdet' : 0 < det3 (v - x) (y₁ - x) (-u) := by
          have : det3 (v - x) (y₁ - x) (-u) = det3 (y₁ - x) (v - x) u := by simp only [det3, PiLp.neg_apply]; ring
          linarith
        have hm1' : 0 < det3 (v - x) (cross ω x + τ') (-u) := by
          have : det3 (v - x) (cross ω x + τ') (-u) = det3 (x - v) (cross ω x + τ') u := by
            simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
          linarith
        have hm0' : 0 < det3 (x - y₁) (cross ω x + τ') (-u) := by
          have : det3 (x - y₁) (cross ω x + τ') (-u) = det3 (y₁ - x) (cross ω x + τ') u := by
            simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
          linarith
        have hw' := tiltCert_wedge_replace O v a b c ha hb hc (-ca) (-cb) (-cc) hs_neg (-u)
          (by dsimp only [u]; module) ω τ' x
          h_ne_neg y₁ hy₁O hdet' hm1' hm0'
        rcases hw' with ⟨p₀, hp₀, p₁, hp₁, g1, g2, g3⟩ | ⟨p', hp', q', hq', r', hr', g1, g2, g3, g4⟩
        · left
          refine ⟨p₁, hp₁, p₀, hp₀, ?_, ?_, ?_⟩
          · have : det3 (p₀ - x) (p₁ - x) u = det3 (p₁ - x) (p₀ - x) (-u) := by simp only [det3, PiLp.neg_apply]; ring
            linarith
          · have : det3 (p₀ - x) (cross ω x + τ') u = det3 (x - p₀) (cross ω x + τ') (-u) := by
              simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
            linarith
          · have : det3 (x - p₁) (cross ω x + τ') u = det3 (p₁ - x) (cross ω x + τ') (-u) := by
              simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
            linarith
        · right
          exact ⟨p', hp', r', hr', q', hq', by simp only [det3, PiLp.sub_apply, PiLp.neg_apply] at g1 ⊢; linarith,
            by simp only [det3, PiLp.sub_apply, PiLp.neg_apply] at g4 ⊢; linarith,
            by simp only [det3, PiLp.sub_apply, PiLp.neg_apply] at g3 ⊢; linarith,
            by simp only [det3, PiLp.sub_apply, PiLp.neg_apply] at g2 ⊢; linarith⟩
    · rcases Finset.mem_insert.mp hy₁ with hy₁_eq | hy₁O
      · rw [hy₁_eq] at h1 h2
        exact tiltCert_wedge_replace O v a b c ha hb hc ca cb cc hs u rfl ω τ' x hne_x y₀ hy₀O h1 h2 h3
      · exact Or.inl ⟨y₀, hy₀O, y₁, hy₁O, h1, h2, h3⟩
  · -- Case 2: Triangle in insert v O
    have tri_step : ∀ (p q r : ℝ³), p ∈ O → q ∈ O → r ∈ insert v O →
        0 < det3 (q - p) (r - p) u → 0 < det3 (q - p) (x - p) u →
        0 < det3 (r - q) (x - q) u → 0 < det3 (p - r) (x - r) u →
        TiltCert O u ω τ' x := by
      intro p q r hpO hqO hrI g1 g2 g3 g4
      rcases Finset.mem_insert.mp hrI with hr_eq | hrO
      · -- r = v: x is strictly inside Δ(p, q, v)
        rw [hr_eq] at g1 g3 g4
        left
        have hne_c : ca + cb + cc ≠ 0 := by rcases hs with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;> linarith
        set S : Finset ℝ³ := {a, b, c, p, q}
        have hSO : ∀ s ∈ S, s ∈ O := fun s hs' => by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs'
          rcases hs' with rfl | rfl | rfl | rfl | rfl <;> assumption
        have hbar := fun z : ℝ³ => det3_tri_bary p q v x z u
        let la := ca / (ca + cb + cc)
        let lb := cb / (ca + cb + cc)
        let lc := cc / (ca + cb + cc)
        have hla : 0 < la := by rcases hs with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;> [exact div_pos k1 (by linarith); exact div_pos_of_neg_of_neg k1 (by linarith)]
        have hlb : 0 < lb := by rcases hs with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;> [exact div_pos k2 (by linarith); exact div_pos_of_neg_of_neg k2 (by linarith)]
        have hlc : 0 < lc := by rcases hs with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;> [exact div_pos k3 (by linarith); exact div_pos_of_neg_of_neg k3 (by linarith)]
        let pts : Fin 5 → ℝ³ := ![a - x, b - x, c - x, p - x, q - x]
        let wt : Fin 5 → ℝ := ![det3 (q - p) (x - p) u * la, det3 (q - p) (x - p) u * lb,
          det3 (q - p) (x - p) u * lc, det3 (v - q) (x - q) u, det3 (p - v) (x - v) u]
        have hwt_pos : ∀ i : Fin 5, 0 < wt i := fun i => by
          fin_cases i
          · exact mul_pos g2 hla
          · exact mul_pos g2 hlb
          · exact mul_pos g2 hlc
          · exact g3
          · exact g4
        let S' : Finset ℝ³ := Finset.univ.image pts
        let w : ℝ³ → ℝ := fun s => ∑ i : Fin 5, if pts i = s then wt i else 0
        have hw_pos : ∀ s ∈ S', 0 < w s := fun s hs' => by
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs'
          exact Finset.sum_pos' (fun j _ => by split_ifs <;> [exact (hwt_pos j).le; exact le_rfl])
            ⟨i, Finset.mem_univ i, by simp [hwt_pos i]⟩
        have hsum_eq : ∀ z : ℝ³, ∑ s ∈ S', w s * det3 s z u = ∑ i : Fin 5, wt i * det3 (pts i) z u := by
          intro z
          simp only [w, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single (pts i)]
          · simp
          · intro s _ hsne; simp [hsne.symm]
          · intro hmem; exfalso; exact hmem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
        have hv_form : ∀ z : ℝ³, det3 (v - x) z u =
            la * det3 (a - x) z u + lb * det3 (b - x) z u + lc * det3 (c - x) z u := by
          intro z
          have hv : (ca + cb + cc) • (v - x) =
              ca • (a - x) + cb • (b - x) + cc • (c - x) - (ca • (a - v) + cb • (b - v) + cc • (c - v)) := by
            module
          have h0 : det3 ((ca + cb + cc) • (v - x)) z u =
              det3 (ca • (a - x) + cb • (b - x) + cc • (c - x) - (ca • (a - v) + cb • (b - v) + cc • (c - v))) z u := by
            rw [hv]
          have hu0 : det3 (ca • (a - v) + cb • (b - v) + cc • (c - v)) z u = 0 := by
            change det3 u z u = 0
            simp only [det3]; ring
          simp only [det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 hu0 ⊢
          dsimp only [la, lb, lc]
          field_simp [hne_c]
          linarith
        have hsum0 : ∀ z : ℝ³, ∑ s ∈ S', w s * det3 s z u = 0 := fun z => by
          rw [hsum_eq, Fin.sum_univ_five]
          simp only [pts, wt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          have hb0 := hbar z
          have hvf := hv_form z
          calc det3 (q - p) (x - p) u * la * det3 (a - x) z u +
              det3 (q - p) (x - p) u * lb * det3 (b - x) z u +
              det3 (q - p) (x - p) u * lc * det3 (c - x) z u +
              det3 (v - q) (x - q) u * det3 (p - x) z u +
              det3 (p - v) (x - v) u * det3 (q - x) z u
              = det3 (v - q) (x - q) u * det3 (p - x) z u +
                det3 (p - v) (x - v) u * det3 (q - x) z u +
                det3 (q - p) (x - p) u * (la * det3 (a - x) z u + lb * det3 (b - x) z u + lc * det3 (c - x) z u) := by ring
            _ = 0 := by rw [← hvf]; exact hb0
        -- Now filter out any 0-cross points? Wait: if `pts i` has `cross (pts i) u = 0`, then `det3 (pts i) z u = 0` for ALL z!
        -- So we can filter `S'' := S'.filter (fun s => cross s u ≠ 0)`!
        let S'' := S'.filter (fun s => cross s u ≠ 0)
        have hsum'' : ∀ z : ℝ³, ∑ s ∈ S'', w s * det3 s z u = 0 := fun z => by
          have : ∑ s ∈ S', w s * det3 s z u = ∑ s ∈ S'', w s * det3 s z u := by
            rw [← Finset.sum_filter_add_sum_filter_not S' (fun s => cross s u ≠ 0)]
            have hzero_rest : ∑ s ∈ S'.filter (fun s => ¬ cross s u ≠ 0), w s * det3 s z u = 0 := by
              refine Finset.sum_eq_zero fun s hs' => ?_
              have hcr : cross s u = 0 := not_not.mp (Finset.mem_filter.mp hs').2
              have hd0 : det3 s z u = 0 := by
                have : det3 s z u = -⟪cross s u, z⟫ := by
                  simp only [det3, cross_apply_zero, cross_apply_one, cross_apply_two,
                    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
                rw [this, hcr, inner_zero_left, neg_zero]
              rw [hd0, mul_zero]
            rw [hzero_rest, add_zero]
          rw [← this, hsum0 z]
        have hS''_O : ∀ s ∈ S'', ∃ y ∈ O, s = y - x := fun s hs' => by
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs').1
          fin_cases i
          · exact ⟨a, ha, hi.symm⟩
          · exact ⟨b, hb, hi.symm⟩
          · exact ⟨c, hc, hi.symm⟩
          · exact ⟨p, hpO, hi.symm⟩
          · exact ⟨q, hqO, hi.symm⟩
        have hne'' : ∀ s ∈ S'', det3 s m u ≠ 0 := fun s hs' => by
          obtain ⟨y, hyO, rfl⟩ := hS''_O s hs'
          exact hne_x y hyO (Finset.mem_filter.mp hs').2
        have hnoncol'' : ∃ s₁ ∈ S'', ∃ s₂ ∈ S'', det3 s₁ s₂ u ≠ 0 := by
          by_contra hno
          push_neg at hno
          have hzero_all : ∀ s₁ ∈ S', ∀ s₂ ∈ S', det3 s₁ s₂ u = 0 := fun s₁ hs₁ s₂ hs₂ => by
            by_cases h1c : cross s₁ u = 0
            · have : det3 s₁ s₂ u = -⟪cross s₁ u, s₂⟫ := by
                simp only [det3, cross_apply_zero, cross_apply_one, cross_apply_two,
                  PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
              rw [this, h1c, inner_zero_left, neg_zero]
            · by_cases h2c : cross s₂ u = 0
              · have : det3 s₁ s₂ u = ⟪cross s₂ u, s₁⟫ := by
                  simp only [det3, cross_apply_zero, cross_apply_one, cross_apply_two,
                    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
                rw [this, h2c, inner_zero_left]
              · exact hno s₁ (Finset.mem_filter.mpr ⟨hs₁, h1c⟩) s₂ (Finset.mem_filter.mpr ⟨hs₂, h2c⟩)
          have hmem_a : a - x ∈ S' := Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩
          have hmem_b : b - x ∈ S' := Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, rfl⟩
          have hmem_c : c - x ∈ S' := Finset.mem_image.mpr ⟨2, Finset.mem_univ 2, rfl⟩
          have hmem_p : p - x ∈ S' := Finset.mem_image.mpr ⟨3, Finset.mem_univ 3, rfl⟩
          have hmem_q : q - x ∈ S' := Finset.mem_image.mpr ⟨4, Finset.mem_univ 4, rfl⟩
          have hv1 := hv_form (p - x)
          have hv2 := hv_form (q - x)
          rw [hzero_all _ hmem_a _ hmem_p, hzero_all _ hmem_b _ hmem_p, hzero_all _ hmem_c _ hmem_p] at hv1
          rw [hzero_all _ hmem_a _ hmem_q, hzero_all _ hmem_b _ hmem_q, hzero_all _ hmem_c _ hmem_q] at hv2
          have hpq0 := hzero_all _ hmem_p _ hmem_q
          have e1 : det3 (q - p) (v - p) u = det3 (q - x) (v - x) u - det3 (p - x) (v - x) u - det3 (q - x) (p - x) u := by
            simp only [det3, PiLp.sub_apply]; ring
          have e2 : det3 (q - x) (v - x) u = -det3 (v - x) (q - x) u := by simp only [det3]; ring
          have e3 : det3 (p - x) (v - x) u = -det3 (v - x) (p - x) u := by simp only [det3]; ring
          have e4 : det3 (q - x) (p - x) u = -det3 (p - x) (q - x) u := by simp only [det3]; ring
          rw [e2, e3, e4] at e1
          linarith
        obtain ⟨s₀, hs₀, s₁, hs₁, k1, k2, k3⟩ :=
          wedge_of_pos_comb S'' w m u (fun s hs' => hw_pos s (Finset.mem_filter.mp hs').1) hsum'' hne'' hnoncol''
        obtain ⟨y₀', hy₀', rfl⟩ := hS''_O s₀ hs₀
        obtain ⟨y₁', hy₁', rfl⟩ := hS''_O s₁ hs₁
        refine ⟨y₀', hy₀', y₁', hy₁', k1, k2, ?_⟩
        have : det3 (x - y₀') m u = det3 m (y₀' - x) u := by simp only [det3, PiLp.sub_apply]; ring
        linarith
      · exact Or.inr ⟨p, hpO, q, hqO, r, hrO, g1, g2, g3, g4⟩
    rcases Finset.mem_insert.mp hp with hp_eq | hpO
    · rcases Finset.mem_insert.mp hq with hq_eq | hqO
      · exfalso; rw [hp_eq, hq_eq] at h1; simp only [det3, PiLp.sub_apply] at h1; linarith
      · rcases Finset.mem_insert.mp hr with hr_eq | hrO
        · exfalso; rw [hp_eq, hr_eq] at h1; simp only [det3, PiLp.sub_apply] at h1; linarith
        · rw [hp_eq] at h1 h2 h4
          exact tri_step q r v hqO hrO (Finset.mem_insert_self v O)
            (by simp only [det3, PiLp.sub_apply] at h1 ⊢; linarith) h3 h4 h2
    · rcases Finset.mem_insert.mp hq with hq_eq | hqO
      · rcases Finset.mem_insert.mp hr with hr_eq | hrO
        · exfalso; rw [hq_eq, hr_eq] at h1; simp only [det3, PiLp.sub_apply] at h1; linarith
        · rw [hq_eq] at h1 h2 h3
          exact tri_step r p v hrO hpO (Finset.mem_insert_self v O)
            (by simp only [det3, PiLp.sub_apply] at h1 ⊢; linarith) h4 h2 h3
      · exact tri_step p q r hpO hqO hr h1 h2 h3 h4

/-- Combined equivalence for Hidden-Cap (iv) at a cone view `u`. -/
theorem freeAt_insert_of_cone_iff (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hD : det3 (a - v) (b - v) (c - v) ≠ 0) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0)) :
    FreeAt (insert v O) (ca • (a - v) + cb • (b - v) + cc • (c - v)) ↔
      FreeAt O (ca • (a - v) + cb • (b - v) + cc • (c - v)) :=
  ⟨freeAt_of_insert_of_cone O v a b c ha hb hc hD ca cb cc hs,
   freeAt_insert_of_cone O v a b c ha hb hc hD ca cb cc hs⟩

end Minimality.Split
