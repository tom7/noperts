module

public import Minimality.SlideDS
public import Minimality.Type08

@[expose] public section

/-!
# Type 08: the cases of Theorem 10.1 by sliding along a face circle
(`FEWER-FACES-PROOFS.md` §10 addendum, Lemma C)

Theorem 10.1 (`Type08.lean`) ends each case in a reduced polygon `K_v` that is
unimodal at the view `u₀` along an edge, and needs strict depths and no horizontal
double normal of `K_v` at `u₀`.  Lemma C of the addendum removes both: slide the view
along the great circle of a face `F_j` through the crossing (`isRupert_of_slide'`).  At
`u₀ + t e` (`e` in `F_j`'s plane) the other end `w` of the edge and `F_j`'s other
middles lie over the side of `F_j`, the other face's middles go strictly inside, and
the rim is `K_v`'s.  A rim without a weak saddle at `u₀` (`NWS4`, ties allowed) keeps
none, and depth ties and double normals occur at isolated `t` unless a bad direction
of the rim is normal to `F_j` (`NoBadNormal`).  The table of Lemma C (c):

| case | closing | rim | circles |
|---|---|---|---|
| N2 | `K_y` (`K_c`) | `y p y' p'` | `x y p` (`Q_bc`) |
| N2 | `K_x` (`K_{a'}`) | `x p y' p'` | `x y p` or `x y p'` (`a'b'c`) |
| Q | `K_d` | `d a b' c` (the face `Q_ac`) | `Q_ab` or `Q_bc` |
| T4 | `K_b` | `b c b' c'` | `Q_bc` |
| T4 | `K_d` | `d c b' c'` | `Q_ab` |

For the three closings with one circle, Lemma H uses the other face `F_k` instead: along
`F_k`'s circle the middle `m` of `F_j` next to `v` pokes out, and the rim is `K_v` with
`m` inserted (five corners).  If that rim is strictly unimodal at `u₀`
(`StrictUnimodal`, Theorem 7.3) or has a depth-separated pair there (Lemma H (c), Theorem
8.10; both `UniOrSep`, `SlideDS.lean`) and `NoBadNormal` holds along `F_k`, `K` is Rupert;
the remaining case (a horizontal double normal perpendicular to `F_j` of type (d) with a
two-peaked five-corner rim) is the open piece `R_d` of the addendum.

| closing | five-corner rim | circle |
|---|---|---|
| `K_y` (N2) | `y m p y' p'` | `x y p'` (`isRupert_quad_edge_middle_five`) |
| `K_b` (T4) | `b c' b' c a'` | `Q_ab` (`isRupert_t4b_five`) |
| `K_d` (T4) | `d a c' b' c` | `Q_bc` (`isRupert_t4d_five`) |

* `quad_edge_tests_or`: the determinant tests of an octahedron's quad edge view in
  either orientation (`ρ = det3 (p − y) (p' − y) (y − x)`).
* `nws4_closing_x'`, `nws4_closing_oct`: the closing by `x` of Lemma 9.3 with the
  touching exclusion weakened to the triple tie `z p = z p' = z y'` (codimension 2).
* `isRupert_quad_edge_middle_slide` (case N2: Lemma 9.3 with a middle, by slides, in an
  octahedron with one more point); `isRupert_quad_edge_middle_sel`: its slides, given the
  closing with no weak saddle.
* In the frame `d; a, c, b` (`b' = d + α (a − d) + β (c − d)`, `c' = d + α₁ (a − d) +
  β₁ (b − d)`, `a' = d + α₂ (b − d) + β₂ (c − d)`; every test is a multiple of
  `E = det3 (a − d) (c − d) (b − d)`, `t4_slide_dets`, `q_slide_dets`, `t4b5_dets`,
  `t4d5_dets`): `isRupert_t4_slide` (case T4; its closing `t4_closing` and slides
  `isRupert_t4_sel`), `isRupert_q_slide` (case Q, with the planar
  quadrilateral `Q_ac` allowed level edges: `nws4_of_planar_quad'`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The determinant tests at a quad edge `x → y` of an octahedron (`x'` hidden), in
either orientation: each has the sign of `ρ = det3 (p − y) (p' − y) (y − x)`. -/
theorem quad_edge_tests_or {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y) :
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y → w ≠ p → w ≠ x →
      0 < det3 (p - y) (p' - y) (y - x) * det3 (p - y) (w - y) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p → w ≠ y' →
      0 < det3 (p - y) (p' - y) (y - x) * det3 (y' - p) (w - p) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y' → w ≠ p' →
      0 < det3 (p - y) (p' - y) (y - x) * det3 (p' - y') (w - y') (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p' → w ≠ y → w ≠ x →
      0 < det3 (p - y) (p' - y) (y - x) * det3 (y - p') (w - p') (y - x)) := by
  have hmem : ∀ w, w ∈ ({x, x', y, y', p, p'} : Finset ℝ³) →
      w ∈ ({x, x', y, y', p', p} : Finset ℝ³) := by
    intro w hw; simp only [mem_insert, mem_singleton] at hw ⊢; tauto
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hn | hp
  · obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F.swap₃ hq₂ hq₁
      (by rw [det3_swap12]; linarith)
    refine ⟨fun w hw h1 h2 h3 => ?_, fun w hw h1 h2 => ?_, fun w hw h1 h2 => ?_,
      fun w hw h1 h2 h3 => ?_⟩
    · have := E4 w (hmem w hw) h2 h1 h3
      rw [det3_rev_edge] at this; nlinarith
    · have := E3 w (hmem w hw) h2 h1
      rw [det3_rev_edge] at this; nlinarith
    · have := E2 w (hmem w hw) h2 h1
      rw [det3_rev_edge] at this; nlinarith
    · have := E1 w (hmem w hw) h2 h1 h3
      rw [det3_rev_edge] at this; nlinarith
  · obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hp
    exact ⟨fun w hw h1 h2 h3 => mul_pos hp (E1 w hw h1 h2 h3),
      fun w hw h1 h2 => mul_pos hp (E2 w hw h1 h2), fun w hw h1 h2 => mul_pos hp (E3 w hw h1 h2),
      fun w hw h1 h2 h3 => mul_pos hp (E4 w hw h1 h2 h3)⟩

/-- **The closing by `x` of Lemma 9.3**, as `nws4_closing_x`, with the touching
exclusion weakened to the triple tie `z p = z y' = z p'`. -/
theorem nws4_closing_x' {x y y' p p' : ℝ³}
    (hS₁ : 0 < det3 (y' - p) (p' - p) (y - x)) (hS₂ : 0 < det3 (y' - x) (p' - x) (y - x))
    (hS₃ : 0 < det3 (p - x) (p' - x) (y - x)) (hS₄ : 0 < det3 (p - x) (y' - x) (y - x))
    (hlow : det3 (y' - p) (p' - p) (y - x) * ⟪x, y - x⟫ +
        det3 (p - x) (p' - x) (y - x) * ⟪y', y - x⟫ <
      det3 (y' - x) (p' - x) (y - x) * ⟪p, y - x⟫ + det3 (p - x) (y' - x) (y - x) * ⟪p', y - x⟫)
    (hN : ¬ NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫)) :
    NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) := by
  set u := y - x
  have hsum := four_point_sum x p y' p' u
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hN ⊢
  simp only [max_le_iff, le_min_iff, not_and_or, not_le] at hgood
  have hY : ⟪p, u⟫ ≤ ⟪y, u⟫ ∧ ⟪p', u⟫ ≤ ⟪y, u⟫ ∧ ⟪p, u⟫ ≤ ⟪y', u⟫ ∧ ⟪p', u⟫ ≤ ⟪y', u⟫ := by
    by_contra hc
    apply hN
    constructor
    · simp only [not_and_or, not_le] at hc; exact hc
    · rcases hgood with (h | h) | (h | h) <;> simp only [h, true_or, or_true]
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  have hx_lt : ⟪x, u⟫ < ⟪p, u⟫ ∨ ⟪x, u⟫ < ⟪p', u⟫ := by
    by_contra hc; push Not at hc
    obtain ⟨c1, c2⟩ := hc
    rcases le_total ⟪p, u⟫ ⟪p', u⟫ with hpp | hpp
    · nlinarith [mul_le_mul_of_nonneg_left c2 hS₁.le, mul_le_mul_of_nonneg_left hY4 hS₃.le,
        mul_le_mul_of_nonneg_left hpp hS₂.le, mul_eq_zero_of_left hsum ⟪p', u⟫]
    · nlinarith [mul_le_mul_of_nonneg_left c1 hS₁.le, mul_le_mul_of_nonneg_left hY3 hS₃.le,
        mul_le_mul_of_nonneg_left hpp hS₄.le, mul_eq_zero_of_left hsum ⟪p, u⟫]
  refine ⟨by rcases hx_lt with h | h; exacts [Or.inl h, Or.inr (Or.inl h)], ?_⟩
  by_contra hc
  simp only [not_or, not_lt] at hc
  obtain ⟨-, -, c3, c4⟩ := hc
  exact htouch ⟨by linarith, by linarith⟩

/-- The closing by `x` at a quad edge `x → y` of an octahedron, in either
orientation: if `K_y`'s rim `y p y' p'` has a weak saddle, the edge is not bad and the
far ends are not at one depth with `y'`, then `K_x`'s rim `x p y' p'` has none. -/
theorem nws4_closing_oct {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hN : ¬ NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫)) :
    NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have key : ∀ {p p' : ℝ³} (F : OctFacets x x' y y' p p'), F.a'b'c.f x < F.a'b'c.f y →
      F.a'b'c'.f x < F.a'b'c'.f y → 0 < det3 (p - y) (p' - y) (y - x) →
      ¬ NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) →
      ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫ →
      ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫) →
      NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) := by
    intro p p' F hq₁ hq₂ hor hN hgood htouch
    have hnd := F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨-, -, hxy', hxp, hxp'⟩, -, ⟨hyy', hyp, -⟩, ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
    obtain ⟨E1, E2, E3, -⟩ := quad_edge_tests F hq₁ hq₂ hor
    have hS₁ := E2 p' (by simp) (Ne.symm hpp') (Ne.symm hy'p')
    have hS₂ : 0 < det3 (y' - x) (p' - x) (y - x) := by
      rw [← det3_cyc x y' p']; exact E3 x (by simp) hxy' hxp'
    have hS₃ : 0 < det3 (p - x) (p' - x) (y - x) := by rw [det3_shift_xy]; exact hor
    have hS₄ : 0 < det3 (p - x) (y' - x) (y - x) := by
      rw [det3_shift_xy]; exact E1 y' (by simp) (Ne.symm hyy') hy'p (Ne.symm hxy')
    exact nws4_closing_x' hS₁ hS₂ hS₃ hS₄ (quad_edge_lower F hS₁ hS₂ hS₃ hS₄) hN hgood htouch
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hn | hp
  · refine NWS4_quad_swap (key F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
      (fun h => hN (NWS4_quad_swap h)) (by rwa [min_comm]) (fun h => htouch ⟨h.2, h.1⟩))
  · exact key F hq₁ hq₂ hp hN hgood htouch

/-- `t < 1` for small `t > 0`. -/
theorem eventually_lt_one : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
  (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds

/-- An affine function of `t` positive at `0` stays positive for small `t > 0`. -/
theorem eventually_pos_of_pos {A B : ℝ} (h : 0 < A) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < A + t * B :=
  eventually_pos_affine (Or.inl h)

set_option maxHeartbeats 1000000 in
/-- **Lemma H for `K_y` (N2), the five-corner rim.**  At a quad edge `x → y` of an
octahedron (`x'` hidden) with one more point `m` over the chord from `y` to `p`, slide
along the other face `x y p'` (`e = p' − y`): `x` lies over its side `p' y`, and `m`
pokes out between `y` and `p`; the rim is `y m p y' p'`.  If its depths at the view
along `y − x` are strictly unimodal or have a depth-separated pair (`UniOrSep`, Lemma H
(c)) and no bad direction of it is normal to `x y p'`, the seven points are Rupert. -/
theorem isRupert_quad_edge_middle_five {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ m = y + s • (p - y) + δ • (y - x))
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hu5 : UniOrSep (quint y m p y' p') (y - x))
    (hs5 : NoBadNormal (quint y m p y' p') (y - x) (p' - y)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests_or F hq₁ hq₂
  set ρ := det3 (p - y) (p' - y) (y - x) with hρ_def
  have hρ : ρ ≠ 0 := quad_orient_ne F
  have hρρ : 0 < ρ * ρ := mul_self_pos.mpr hρ
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  obtain ⟨hmx, hmx', hmy, hmy', hmp, hmp'⟩ := hmO
  set V : Finset ℝ³ := insert m {x, x', y, y', p, p'} with hV
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp' : p' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have hmemV : ∀ z ∈ V, z = m ∨ z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  set u := y - x with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨s, δ, hs0, hs1, hδ, hm⟩ := hmid
  -- the tests of the rim `y m p y' p'`
  have T02a : det3 (m - y) (p - y) u = 0 := by
    rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have T02b : det3 (m - y) (p - y) (p' - y) = δ * ρ := by
    rw [hm]; simp only [hρ_def, u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have T10a : det3 (p - m) (y - m) u = 0 := by
    rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have T10b : det3 (p - m) (y - m) (p' - y) = δ * ρ := by
    rw [hm]; simp only [hρ_def, u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have Ty : ∀ w : ℝ³, det3 (m - y) (w - y) u = s * det3 (p - y) (w - y) u := by
    intro w; rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]; ring
  have Tm : ∀ w : ℝ³, det3 (p - m) (w - m) u = (1 - s) * det3 (p - y) (w - y) u := by
    intro w; rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]; ring
  have T21 : det3 (y' - p) (m - p) u = (1 - s) * det3 (y' - p) (y - p) u := by
    rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have T31 : det3 (p' - y') (m - y') u =
      (1 - s) * det3 (p' - y') (y - y') u + s * det3 (p' - y') (p - y') u := by
    rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have T41 : det3 (y - p') (m - p') u = s * det3 (y - p') (p - p') u := by
    rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have Tρ : det3 (p - y) (p' - y) u = ρ := rfl
  have e1y' := E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
  have e1p' := E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
  have e1x' := E1 x' mx' hx'y hx'p (Ne.symm hxx')
  have e2y := E2 y my hyp hyy'
  have e2p' := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
  have e2x' := E2 x' mx' hx'p hx'y'
  have e3y := E3 y my hyy' hyp'
  have e3p := E3 p mp (Ne.symm hy'p) hpp'
  have e3x' := E3 x' mx' hx'y' hx'p'
  have e4p := E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
  have e4y' := E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
  have e4x' := E4 x' mx' hx'p' hx'y (Ne.symm hxx')
  have hs1' : 0 < 1 - s := by linarith
  refine isRupert_of_slide_uos V {x} u (p' - y) hu (quint y m p y' p') ?_ ?_
    (quint_injective (Ne.symm hmy) hyp hyy' hyp' hmp hmy' hmp' (Ne.symm hy'p) hpp' hy'p')
    (by norm_num) ρ hρ ?_ ?_ ?_ hu5 hs5.toR
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_singleton]
    exacts [Ne.symm hxy, hmx, Ne.symm hxp, Ne.symm hxy', Ne.symm hxp']
  · intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    · exact Or.inr ⟨T02a, by rw [T02b, mul_left_comm]; exact mul_pos hδ hρρ⟩
    · left; rw [Ty, mul_left_comm]; exact mul_pos hs0 e1y'
    · left; rw [Ty, Tρ, mul_left_comm]; exact mul_pos hs0 hρρ
    · left; rw [Tm, mul_left_comm]; exact mul_pos hs1' e1y'
    · left; rw [Tm, Tρ, mul_left_comm]; exact mul_pos hs1' hρρ
    · exact Or.inr ⟨T10a, by rw [T10b, mul_left_comm]; exact mul_pos hδ hρρ⟩
    · exact Or.inl e2p'
    · exact Or.inl e2y
    · left; rw [T21, mul_left_comm]; exact mul_pos hs1' e2y
    · exact Or.inl e3y
    · left; rw [T31, mul_add, mul_left_comm, mul_left_comm ρ s]
      exact add_pos (mul_pos hs1' e3y) (mul_pos hs0 e3p)
    · exact Or.inl e3p
    · left; rw [T41, mul_left_comm]; exact mul_pos hs0 e4p
    · exact Or.inl e4p
    · exact Or.inl e4y'
  · intro z hz hzM hzx i
    have hzx' : z = x' := by
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
      rcases hmemV z hz with h | h | h | h | h | h | h
      exacts [absurd h h1, absurd (mem_singleton.mpr h) hzM, h, absurd h h0, absurd h h3,
        absurd h h2, absurd h h4]
    rw [hzx']
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    · left; rw [Ty, mul_left_comm]; exact mul_pos hs0 e1x'
    · left; rw [Tm, mul_left_comm]; exact mul_pos hs1' e1x'
    · exact Or.inl e2x'
    · exact Or.inl e3x'
    · exact Or.inl e4x'
  · intro z hz
    rw [mem_singleton.mp hz]
    filter_upwards [self_mem_nhdsWithin, eventually_lt_one] with t ht0 ht1
    have ht : (0 : ℝ) < t := ht0
    refine ⟨4, 1 - t, -1, by linarith, by linarith, by norm_num, ?_⟩
    simp only [b4, quint_4, quint_0, u]; module

/-- **Case N2 of Theorem 10.1 by slides, given the closing.**  At a quad edge `x → y` of an
octahedron (`x'` hidden) with one more point `m` over the chord from `y` to `p` (in the face
`x y p`): if `K_y`'s rim `y p y' p'` has no weak saddle, slide it along the face `x y p`; if
`K_x`'s rim `x p y' p'` has none, slide it along `x y p` or `x y p'`. -/
theorem isRupert_quad_edge_middle_sel {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ m = y + s • (p - y) + δ • (y - x))
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hsel : (NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) ∧
        NoBadNormal (quad y p y' p') (y - x) (p - y)) ∨
      (NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) ∧
        (NoBadNormal (quad x p y' p') (y - x) (p - x) ∨
          NoBadNormal (quad x p y' p') (y - x) (p' - x)))) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests_or F hq₁ hq₂
  set ρ := det3 (p - y) (p' - y) (y - x) with hρ_def
  have hρ : ρ ≠ 0 := quad_orient_ne F
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  obtain ⟨hmx, hmx', hmy, hmy', hmp, hmp'⟩ := hmO
  set V : Finset ℝ³ := insert m {x, x', y, y', p, p'} with hV
  have mx : x ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp' : p' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have hmemV : ∀ z ∈ V, z = m ∨ z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  set u := y - x with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨s, δ, hs0, hs1, hδ, hm⟩ := hmid
  -- the tests at `u` of the rims `v p y' p'` (`v = y` or `v = x`)
  have hcyc : ∀ v, (v = y ∨ v = x) → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad v p y' p' (i + 1) - quad v p y' p' i)
        (quad v p y' p' j - quad v p y' p' i) u := by
    intro v hv i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;>
    rcases hv with rfl | rfl
    · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    · rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
    · rw [det3_shift_xy]; exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
    · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    · exact E2 v my hyp hyy'
    · exact E2 v mx hxp hxy'
    · exact E3 v my hyy' hyp'
    · exact E3 v mx hxy' hxp'
    · exact E3 p mp (Ne.symm hy'p) hpp'
    · exact E3 p mp (Ne.symm hy'p) hpp'
    · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
    · rw [det3_shift_p']; exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
    · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · rw [det3_shift_p']; exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
  -- `x'` is strictly inside both rims
  have hx'in : ∀ v, (v = y ∨ v = x) → ∀ i : ZMod 4,
      0 < ρ * det3 (quad v p y' p' (i + 1) - quad v p y' p' i) (x' - quad v p y' p' i) u := by
    intro v hv i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;>
      rcases hv with rfl | rfl
    · exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
    · rw [det3_shift_xy]; exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
    · exact E2 x' mx' hx'p hx'y'
    · exact E2 x' mx' hx'p hx'y'
    · exact E3 x' mx' hx'y' hx'p'
    · exact E3 x' mx' hx'y' hx'p'
    · exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
    · rw [det3_shift_p']; exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
  have hinjq : ∀ v, (v = y ∨ v = x) → Function.Injective (quad v p y' p') := by
    intro v hv
    rcases hv with rfl | rfl
    · exact quad_injective hyp hyy' hyp' (Ne.symm hy'p) hpp' hy'p'
    · exact quad_injective hxp hxy' hxp' (Ne.symm hy'p) hpp' hy'p'
  have hxVq : ∀ v, (v = y ∨ v = x) → ∀ i, quad v p y' p' i ∈ V := by
    intro v hv i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rcases hv with rfl | rfl <;> simp [V, quad_0]
    all_goals simp [V, quad_1, quad_2, quad_3]
  -- the points off the rim `v p y' p'` and off `{w, m}`: only `x'` (and `m` if kept)
  have hrestV : ∀ v w, ((v = y ∧ w = x) ∨ (v = x ∧ w = y)) → ∀ z ∈ V, z ≠ m → z ≠ w →
      (∀ j, z ≠ quad v p y' p' j) → z = x' := by
    intro v w hvw z hz hzm hzw hzx
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
    simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
    rcases hmemV z hz with h | h | h | h | h | h | h
    · exact absurd h hzm
    · rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd h hzw, absurd h h0]
    · exact h
    · rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd h h0, absurd h hzw]
    · exact absurd h h2
    · exact absurd h h1
    · exact absurd h h3
  -- `m − x` in the face `x y p`
  have hmx' : m - x = (1 + δ - s) • u + s • (p - x) := by rw [hm]; simp only [u]; module
  rcases hsel with ⟨hN, hsy⟩ | ⟨hN', hsx⟩
  · -- `K_y`, sliding along the face `x y p` (`e = p − y`)
    refine isRupert_of_slide' V {x, m} u (p - y) hu (quad y p y' p') (hxVq y (Or.inl rfl)) ?_
      (hinjq y (Or.inl rfl)) (by norm_num) ρ hρ (hcyc y (Or.inl rfl)) ?_ ?_
      (eventually_unimodal_quad_slide hN) hsy
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
      exacts [⟨Ne.symm hxy, Ne.symm hmy⟩, ⟨Ne.symm hxp, Ne.symm hmp⟩,
        ⟨Ne.symm hxy', Ne.symm hmy'⟩, ⟨Ne.symm hxp', Ne.symm hmp'⟩]
    · intro z hz hzM hzx i
      have hzx' : z = x' := hrestV y x (Or.inl ⟨rfl, rfl⟩) z hz
        (fun h => hzM (by simp [h])) (fun h => hzM (by simp [h])) hzx
      rw [hzx']; exact Or.inl (hx'in y (Or.inl rfl) i)
    · intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · filter_upwards [self_mem_nhdsWithin, eventually_lt_one] with t ht0 ht1
        refine ⟨0, t, -1, ht0, ht1, by norm_num, ?_⟩
        simp only [quad_0, zero_add, quad_1, u]; module
      · rw [mem_singleton.mp hz]
        filter_upwards [self_mem_nhdsWithin,
          eventually_pos_of_pos (B := -δ) hs0] with t ht0 hts
        refine ⟨0, s + t * -δ, δ, hts, by nlinarith [mul_pos (show (0:ℝ) < t from ht0) hδ],
          hδ.ne', ?_⟩
        simp only [quad_0, zero_add, quad_1, hm]; module
  · -- `K_x`
    rcases hsx with hsx | hsx
    · -- along the face `x y p` (`e = x − p`): `y` and `m` are middles
      refine isRupert_of_slide' V {y, m} u (x - p) hu (quad x p y' p') (hxVq x (Or.inr rfl)) ?_
        (hinjq x (Or.inr rfl)) (by norm_num) ρ hρ (hcyc x (Or.inr rfl)) ?_ ?_
        (eventually_unimodal_quad_slide hN') ?_
      · intro i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
        exacts [⟨hxy, Ne.symm hmx⟩, ⟨Ne.symm hyp, Ne.symm hmp⟩,
          ⟨Ne.symm hyy', Ne.symm hmy'⟩, ⟨Ne.symm hyp', Ne.symm hmp'⟩]
      · intro z hz hzM hzx i
        have hzx' : z = x' := hrestV x y (Or.inr ⟨rfl, rfl⟩) z hz
          (fun h => hzM (by simp [h])) (fun h => hzM (by simp [h])) hzx
        rw [hzx']; exact Or.inl (hx'in x (Or.inr rfl) i)
      · intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · filter_upwards [self_mem_nhdsWithin, eventually_lt_one] with t ht0 ht1
          refine ⟨0, t, 1, ht0, ht1, one_ne_zero, ?_⟩
          simp only [quad_0, zero_add, quad_1, u]; module
        · rw [mem_singleton.mp hz]
          filter_upwards [self_mem_nhdsWithin,
            eventually_pos_of_pos (B := -(1 + δ - s)) (show 0 < 1 - s by linarith)] with t ht0 hts
          have ht0' : (0 : ℝ) < t := ht0
          have hpos : 0 < t * (1 + δ - s) := mul_pos ht0' (by linarith)
          refine ⟨0, s + t * (1 + δ - s), 1 + δ - s, by linarith, by linarith, by linarith, ?_⟩
          simp only [quad_0, zero_add, quad_1]
          rw [show m = x + (m - x) by abel, hmx']; module
      · exact hsx.of_span 0 (-1) (by module)
    · -- along the face `x y p'` (`e = x − p'`): `y` is a middle, `m` goes inside
      refine isRupert_of_slide' V {y} u (x - p') hu (quad x p y' p') (hxVq x (Or.inr rfl)) ?_
        (hinjq x (Or.inr rfl)) (by norm_num) ρ hρ (hcyc x (Or.inr rfl)) ?_ ?_
        (eventually_unimodal_quad_slide hN') ?_
      · intro i
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [quad_0, quad_1, quad_2, quad_3, mem_singleton]
        exacts [hxy, Ne.symm hyp, Ne.symm hyy', Ne.symm hyp']
      · intro z hz hzM hzx i
        by_cases hzm : z = m
        · rw [hzm]
          have e1 : 0 < 1 + δ - s := by linarith
          rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
            simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
          · -- the side `x p` of the face `x y p`: zero at `u`, inward along `e`
            right
            rw [hmx']
            have z1 : det3 (p - x) ((1 + δ - s) • u + s • (p - x)) u = 0 := by
              simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
                smul_eq_mul]; ring
            have z2 : det3 (p - x) ((1 + δ - s) • u + s • (p - x)) (x - p') = (1 + δ - s) * ρ := by
              simp only [hρ_def, u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
                smul_eq_mul]; ring
            refine ⟨z1, ?_⟩
            rw [z2]; have := mul_self_pos.mpr hρ; nlinarith
          · left
            have e2 : det3 (y' - p) (m - p) u = (1 - s) * det3 (y' - p) (y - p) u := by
              rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
                smul_eq_mul]; ring
            rw [e2]; have := E2 y my hyp hyy'; nlinarith
          · left
            have e3 : det3 (p' - y') (m - y') u =
                (1 - s) * det3 (p' - y') (y - y') u + s * det3 (p' - y') (p - y') u := by
              rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
                smul_eq_mul]; ring
            rw [e3]; have := E3 y my hyy' hyp'; have := E3 p mp (Ne.symm hy'p) hpp'; nlinarith
          · left
            have e4 : det3 (x - p') (m - p') u = s * det3 (y - p') (p - p') u := by
              rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
                smul_eq_mul]; ring
            rw [e4]; have := E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp); nlinarith
        · have hzx' : z = x' := hrestV x y (Or.inr ⟨rfl, rfl⟩) z hz hzm
            (fun h => hzM (by simp [h])) hzx
          rw [hzx']; exact Or.inl (hx'in x (Or.inr rfl) i)
      · intro z hz
        rw [mem_singleton.mp hz]
        filter_upwards [self_mem_nhdsWithin, eventually_lt_one] with t ht0 ht1
        have ht0' : (0 : ℝ) < t := ht0
        refine ⟨3, 1 - t, 1, by linarith, by linarith, one_ne_zero, ?_⟩
        simp only [quad_3, a3, quad_0, u]; module
      · exact hsx.of_span 0 (-1) (by module)


/-- **Case N2 of Theorem 10.1 by slides (Lemma 9.3 with a middle).**  At a quad edge
`x → y` of an octahedron (`x'` hidden) that is not bad, with one more point `m` over
the chord from `y` to `p` (in the face `x y p`): if `K_y`'s rim `y p y' p'` has no weak
saddle, slide it along the face `x y p`; otherwise `K_x`'s rim `x p y' p'` has none
(unless the far ends tie with `y'`), and slide it along `x y p` or `x y p'`.  No
distinct depths and no exclusion of horizontal double normals at the edge view are
needed, only `NoBadNormal` for the circles used. -/
theorem isRupert_quad_edge_middle_slide {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ m = y + s • (p - y) + δ • (y - x))
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫))
    (hsy : NoBadNormal (quad y p y' p') (y - x) (p - y) ∨
      (UniOrSep (quint y m p y' p') (y - x) ∧
        NoBadNormal (quint y m p y' p') (y - x) (p' - y)))
    (hsx : NoBadNormal (quad x p y' p') (y - x) (p - x) ∨
      NoBadNormal (quad x p y' p') (y - x) (p' - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  rcases hsy with hsy | ⟨hu5, hs5⟩
  swap
  · exact isRupert_quad_edge_middle_five F hq₁ hq₂ hmid hmO hu5 hs5
  by_cases hN : NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫)
  · exact isRupert_quad_edge_middle_sel F hq₁ hq₂ hmid hmO (Or.inl ⟨hN, hsy⟩)
  · exact isRupert_quad_edge_middle_sel F hq₁ hq₂ hmid hmO
      (Or.inr ⟨nws4_closing_oct F hq₁ hq₂ hN hgood htouch, hsx⟩)

/-! ### The T4 and Q cases in the frame `d; a, c, b` -/

/-- An oriented test that is a positive multiple of `E` has the sign of `E`. -/
theorem pos_of_coef {E P X : ℝ} (hX : X = P * E) (hP : 0 < P) (hE : E ≠ 0) : 0 < E * X := by
  rw [hX, show E * (P * E) = P * (E * E) by ring]; exact mul_pos hP (mul_self_pos.mpr hE)

theorem slideTest_strict {E P : ℝ} {X Y u₀ e : ℝ³} (hX : det3 X Y u₀ = P * E) (hP : 0 < P)
    (hE : E ≠ 0) : SlideTest E X Y u₀ e := Or.inl (pos_of_coef hX hP hE)

theorem slideTest_zero {E P : ℝ} {X Y u₀ e : ℝ³} (h0 : det3 X Y u₀ = 0)
    (hX : det3 X Y e = P * E) (hP : 0 < P) (hE : E ≠ 0) : SlideTest E X Y u₀ e :=
  Or.inr ⟨h0, pos_of_coef hX hP hE⟩

/-- **Lemma 1 (c), with ties.**  A convex planar quadrilateral with an affine depth
has no weak saddle unless all four depths are equal (here: unless both edges at `P₀`
are level). -/
theorem nws4_of_planar_quad' {P₀ P₁ P₂ P₃ u : ℝ³} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : 1 < α + β) (h : P₂ = P₀ + α • (P₁ - P₀) + β • (P₃ - P₀))
    (hne : ⟪P₀, u⟫ ≠ ⟪P₁, u⟫ ∨ ⟪P₀, u⟫ ≠ ⟪P₃, u⟫) :
    NWS4 (quad ⟪P₀, u⟫ ⟪P₁, u⟫ ⟪P₂, u⟫ ⟪P₃, u⟫) := by
  rcases hne with h01 | h03
  · exact nws4_of_planar_quad hα hβ hαβ h h01
  · exact NWS4_quad_swap (nws4_of_planar_quad hβ hα (by linarith)
      (by rw [h]; abel) h03)

/-- The determinant tests of the T4 slides, as multiples of `E = det3 (a − d) (c − d) (b − d)`. -/
theorem t4_slide_dets {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) :
    det3 (c' - b) (b' - b) (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - b) (c - b) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (c - c') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (b - c') (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (b - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (c' - b') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - c) (c' - c) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - c) (b' - c) (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - b) (a - b) (b - d) = 0 ∧
    det3 (c' - b) (a - b) (c - d) = (α₁ + β₁ - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (a - c') (b - d) = (β*α₁ - β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a - b') (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - c) (a - c) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - d) (b' - d) (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - d) (c - d) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (d - c') (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (d - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (c' - c) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (b' - c) (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - d) (a' - d) (b - d) = (α₁*β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (a' - c') (b - d) = (α*β₂ + β*α₁ - α₁*β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a' - b') (b - d) = (-α*β₂ + α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (a' - c) (b - d) = 0 ∧
    det3 (d - c) (a' - c) (d - a) = (α₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - d) (c - d) (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (c - d) (b' - d) = 0 ∧
    det3 (a - d) (c - d) (c' - d) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c) (c' - c) (b - d) = -((α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d)) ∧
    det3 (b' - d) (c' - d) (b - d) = -((β*α₁) * det3 (a - d) (c - d) (b - d)) ∧
    det3 (c - d) (c' - d) (b - d) = -((α₁) * det3 (a - d) (c - d) (b - d)) ∧
    det3 (c - d) (b' - d) (b - d) = -((α) * det3 (a - d) (c - d) (b - d)) := by
  subst hb' hc' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
/-- The determinant tests of the case-Q slides, as multiples of `E`. -/
theorem q_slide_dets {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) :
    det3 (a - d) (b' - d) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (c - d) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (c - a) (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (d - a) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (d - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a - b') (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (a - c) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (b' - c) (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (a' - d) (b - d) = (β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (a' - a) (b - d) = (α*β₂ + β - β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a' - b') (b - d) = (-α*β₂ + α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (a' - c) (b - d) = 0 ∧
    det3 (d - c) (a' - c) (d - a) = (α₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (c' - d) (b - d) = 0 ∧
    det3 (a - d) (c' - d) (d - c) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (c' - a) (b - d) = (-β*α₁ + β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (c' - b') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (c' - c) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring


/-- The determinant tests of the five-corner rim `b c' b' c a'` (Lemma H, `K_b` on `Q_ab`). -/
theorem t4b5_dets {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) :
    det3 (c' - b) (b' - b) (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - b) (c - b) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - b) (a' - b) (b - d) = (α₁*β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (c - c') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (a' - c') (b - d) = (α*β₂ + β*α₁ - α₁*β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (b - c') (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a' - b') (b - d) = (-α*β₂ + α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (b - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (c' - b') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - c) (b - c) (b - d) = 0 ∧
    det3 (a' - c) (b - c) (a - d) = (α₂ + β₂ - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - c) (c' - c) (b - d) = (-α₁*β₂ + α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - c) (b' - c) (b - d) = (-α*β₂ + α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - a') (c' - a') (b - d) = (α₁*β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - a') (b' - a') (b - d) = (α*β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - a') (c - a') (b - d) = 0 ∧
    det3 (b - a') (c - a') (a - d) = (α₂ + β₂ - 1) * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
/-- The determinant tests of the five-corner rim `d a c' b' c` (Lemma H, `K_d` on `Q_bc`). -/
theorem t4d5_dets {a b b' c c' d : ℝ³} {α β α₁ β₁ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    :
    det3 (a - d) (c' - d) (b - d) = 0 ∧
    det3 (a - d) (c' - d) (d - c) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (b' - d) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (c - d) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - a) (b' - a) (b - d) = (β*α₁ - β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - a) (c - a) (b - d) = (α₁ - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - a) (d - a) (b - d) = 0 ∧
    det3 (c' - a) (d - a) (d - c) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (c - c') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (d - c') (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (a - c') (b - d) = (β*α₁ - β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (d - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a - b') (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (c' - b') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (a - c) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (c' - c) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (b' - c) (b - d) = (α) * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring


set_option maxHeartbeats 1000000 in
/-- **Lemma H for `K_b` (T4), the five-corner rim.**  Slide along the other face `Q_ab`
(`e = a − d`): the middles of `Q_ab` (`d`, `a`) lie over its side `b c'`, and the middle
`a'` of `Q_bc` pokes out between `c` and `b`; the rim is `b c' b' c a'`.  If its depths at
the view along `d b` are strictly unimodal or have a depth-separated pair (`UniOrSep`) and
no bad direction of it is normal to `Q_ab`, `K` is Rupert. -/
theorem isRupert_t4b_five {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hαβ₂ : 1 < α₂ + β₂)
    (hκ : 0 < α + α₁ * (β - 1))
    (hu5 : UniOrSep (quint b c' b' c a') (b - d))
    (hs5 : NoBadNormal (quint b c' b' c a') (b - d) (a - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hα₁p : 0 < α₁ := by linarith
  have p1 : 0 < β * α₁ := mul_pos hβ hα₁p
  have p2 : 0 < α₁ * β₂ := mul_pos hα₁p hβ₂
  have p3 : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  have p4 : 0 < α * β₂ + β * α₁ - α₁ * β₂ := by
    rw [show α * β₂ + β * α₁ - α₁ * β₂ = β₂ * (α + α₁ * (β - 1)) + α₁ * β * (1 - β₂) by ring]
    exact add_pos (mul_pos hβ₂ hκ) (mul_pos (mul_pos hα₁p hβ) (by linarith))
  have p6 : 0 < -α * β₂ + α := by
    rw [show -α * β₂ + α = α * (1 - β₂) by ring]; exact mul_pos hα (by linarith)
  have p11 : 0 < -α₁ * β₂ + α₁ := by
    rw [show -α₁ * β₂ + α₁ = α₁ * (1 - β₂) by ring]; exact mul_pos hα₁p (by linarith)
  have p10 : 0 < α₂ + β₂ - 1 := by linarith
  have p14 : 0 < α * β₂ := mul_pos hα hβ₂
  obtain ⟨P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16⟩ :=
    t4b5_dets hb' hc' ha'
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  refine isRupert_of_slide_uos V {d, a} (b - d) (a - d) hu (quint b c' b' c a') ?_ ?_
    (quint_injective hbc' hbb' hbc (Ne.symm ha'b) (Ne.symm hb'c') (Ne.symm hcc') (Ne.symm ha'c')
      hb'c (Ne.symm ha'b') (Ne.symm ha'c)) (by norm_num) (det3 (a - d) (c - d) (b - d)) hE
    ?_ ?_ ?_ hu5 hs5.toR
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_insert, mem_singleton, not_or]
    exacts [⟨Ne.symm hdb, Ne.symm hab⟩, ⟨Ne.symm hdc', Ne.symm hac'⟩,
      ⟨Ne.symm hdb', Ne.symm hab'⟩, ⟨Ne.symm hdc, Ne.symm hac⟩, ⟨Ne.symm hda', Ne.symm haa'⟩]
  · intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [slideTest_strict P0 p1 hE, slideTest_strict P1 hα₁p hE, slideTest_strict P2 p2 hE,
      slideTest_strict P3 p3 hE, slideTest_strict P4 p4 hE, slideTest_strict P5 p1 hE,
      slideTest_strict P6 p6 hE, slideTest_strict P7 hα hE, slideTest_strict P8 p3 hE,
      slideTest_zero P9 P10 p10 hE, slideTest_strict P11 p11 hE, slideTest_strict P12 p6 hE,
      slideTest_strict P13 p2 hE, slideTest_strict P14 p14 hE, slideTest_zero P15 P16 p10 hE]
  · intro z hz hzM hzx
    exfalso
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    simp only [mem_insert, mem_singleton, not_or] at hzM
    rcases hmemV z hz with h | h | h | h | h | h | h
    exacts [hzM.1 h, hzM.2 h, h4 h, h0 h, h2 h, h3 h, h1 h]
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := -β₁) (by linarith : (0:ℝ) < α₁ - 1),
        eventually_pos_of_pos (B := 1 - β₁) (by linarith : (0:ℝ) < α₁)] with t ht0 hlt hD
      have ht : (0 : ℝ) < t := ht0
      have hD' : α₁ + t * (1 - β₁) ≠ 0 := hD.ne'
      refine ⟨0, t / (α₁ + t * (1 - β₁)), -α₁ / (α₁ + t * (1 - β₁)), div_pos ht hD, ?_,
        div_ne_zero (by linarith) hD', ?_⟩
      · rw [div_lt_one hD]; nlinarith [mul_pos ht hβ₁]
      · simp only [b0, quint_0, quint_1]; rw [hc']; match_scalars <;> field_simp <;> ring
    · rw [mem_singleton.mp h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := -β₁) (by linarith : (0:ℝ) < α₁ - 1),
        eventually_pos_of_pos (B := 1 - β₁) (by linarith : (0:ℝ) < α₁)] with t ht0 hlt hD
      have ht : (0 : ℝ) < t := ht0
      have hD' : α₁ + t * (1 - β₁) ≠ 0 := hD.ne'
      refine ⟨0, (1 + t) / (α₁ + t * (1 - β₁)), -(α₁ + β₁ - 1) / (α₁ + t * (1 - β₁)),
        div_pos (by linarith) hD, ?_, div_ne_zero (by linarith) hD', ?_⟩
      · rw [div_lt_one hD]; linarith
      · simp only [b0, quint_0, quint_1]; rw [hc']; match_scalars <;> field_simp <;> ring

set_option maxHeartbeats 1000000 in
/-- **Lemma H for `K_d` (T4), the five-corner rim.**  Slide along the other face `Q_bc`
(`e = d − c`): the middles of `Q_bc` (`b`, `a'`) lie over its side `c d`, and the middle
`a` of `Q_ab` pokes out between `d` and `c'`; the rim is `d a c' b' c`. -/
theorem isRupert_t4d_five {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hκ : 0 < α + α₁ * (β - 1))
    (hu5 : UniOrSep (quint d a c' b' c) (b - d))
    (hs5 : NoBadNormal (quint d a c' b' c) (b - d) (c - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hα₁p : 0 < α₁ := by linarith
  have p1 : 0 < β * α₁ := mul_pos hβ hα₁p
  have p3 : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  have p4 : 0 < β * α₁ - β := by
    rw [show β * α₁ - β = β * (α₁ - 1) by ring]; exact mul_pos hβ (by linarith)
  have p5 : 0 < α₁ - 1 := by linarith
  have p12 : 0 < α + β - 1 := by linarith
  obtain ⟨P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16⟩ :=
    t4d5_dets hb' hc'
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  refine isRupert_of_slide_uos V {b, a'} (b - d) (d - c) hu (quint d a c' b' c) ?_ ?_
    (quint_injective hda hdc' hdb' hdc hac' hab' hac (Ne.symm hb'c') (Ne.symm hcc') hb'c)
    (by norm_num) (det3 (a - d) (c - d) (b - d)) hE
    ?_ ?_ ?_ hu5
    (hs5.of_span 0 (-1) (by module)).toR
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_insert, mem_singleton, not_or]
    exacts [⟨hdb, hda'⟩, ⟨hab, haa'⟩, ⟨Ne.symm hbc', Ne.symm ha'c'⟩,
      ⟨Ne.symm hbb', Ne.symm ha'b'⟩, ⟨Ne.symm hbc, Ne.symm ha'c⟩]
  · intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [slideTest_zero P0 P1 hβ₁ hE, slideTest_strict P2 hβ hE, slideTest_strict P3 one_pos hE,
      slideTest_strict P4 p4 hE, slideTest_strict P5 p5 hE, slideTest_zero P6 P7 hβ₁ hE,
      slideTest_strict P8 p3 hE, slideTest_strict P9 p1 hE, slideTest_strict P10 p4 hE,
      slideTest_strict P11 hα hE, slideTest_strict P12 p12 hE, slideTest_strict P13 p3 hE,
      slideTest_strict P14 one_pos hE, slideTest_strict P15 hα₁p hE, slideTest_strict P16 hα hE]
  · intro z hz hzM hzx
    exfalso
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    simp only [mem_insert, mem_singleton, not_or] at hzM
    rcases hmemV z hz with h | h | h | h | h | h | h
    exacts [h0 h, h1 h, hzM.2 h, hzM.1 h, h3 h, h4 h, h2 h]
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin, eventually_lt_one] with t ht0 ht1
      have ht : (0 : ℝ) < t := ht0
      refine ⟨4, 1 - t, 1, by linarith, by linarith, one_ne_zero, ?_⟩
      simp only [b4, quint_4, quint_0]; module
    · rw [mem_singleton.mp h]
      filter_upwards [eventually_pos_affine (A := 1 - β₂) (B := -α₂) (Or.inl (by linarith)),
        self_mem_nhdsWithin] with t hlt ht0
      have ht : (0 : ℝ) < t := ht0
      refine ⟨4, 1 - β₂ - t * α₂, α₂, by linarith, by nlinarith [mul_pos ht hα₂], hα₂.ne', ?_⟩
      simp only [b4, quint_4, quint_0]; rw [ha']; module


/-- **The closing of Lemma 5** (T4): in the frame `d; a, c, b`, if `K_b`'s rim `b c' b' c`
has a weak saddle, the edge `d → b` is not bad and there is no triple tie
`z c = z c' = z b'`, then `K_d`'s rim `d c' b' c` has none. -/
theorem t4_closing {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) (hdb : d ≠ b)
    (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hα₁ : 0 < α₁) (hβ₁ : 0 < β₁) (hκ : 0 < α + α₁ * (β - 1))
    (hgood : ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (htouch : ¬ (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫))
    (hN : ¬ NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)) :
    NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) := by
  obtain ⟨K0, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16, K17, K18,
    K19, K20, K21, K22, K23, K24, K25, K26, D3, D21, D2, D1⟩ := t4_slide_dets hb' hc' ha'
  have hα₁p : 0 < α₁ := hα₁
  have hκ' : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  have pβα₁ : 0 < β * α₁ := mul_pos hβ hα₁p
  have hlowG : ∀ s t : ℝ³, (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) s -
      (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) t =
      ⟪-(det3 (a - d) (c - d) (b - d)) • cross (a - d) (c - d), s - t⟫ := by
    intro s t
    simp only [det3, real_inner_smul_left]
    have e : ⟪cross (a - d) (c - d), s - t⟫ =
        ⟪cross (a - d) (c - d), s - d⟫ - ⟪cross (a - d) (c - d), t - d⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    rw [e]; ring
  have hEE := mul_self_pos.mpr hE
  have Gd : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) d = 0 := by
    simp only [sub_self]; simp [det3_expand]
  have Gb' : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) b' = 0 := by
    simp only [K25, mul_zero, neg_zero]
  have Gb : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) b < 0 := by
    simp only; linarith
  have Gc : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) c = 0 := by
    simp only; rw [show det3 (a - d) (c - d) (c - d) = 0 by simp [det3_expand]; ring]; ring
  have Gc' : (fun X => -(det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (X - d))) c' < 0 := by
    simp only; rw [K26]
    have := mul_pos hβ₁ hEE
    linarith [show det3 (a - d) (c - d) (b - d) * (β₁ * det3 (a - d) (c - d) (b - d)) =
      β₁ * (det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d)) by ring]
  rcases lt_or_gt_of_ne hE with hEn | hEp
  · have S₁ : 0 < det3 (b' - c) (c' - c) (b - d) := by
      rw [D3]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hκ' hEn)
    have S₂ : 0 < det3 (b' - d) (c' - d) (b - d) := by
      rw [D21]; exact neg_pos.mpr (mul_neg_of_pos_of_neg pβα₁ hEn)
    have S₃ : 0 < det3 (c - d) (c' - d) (b - d) := by
      rw [D2]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα₁p hEn)
    have S₄ : 0 < det3 (c - d) (b' - d) (b - d) := by
      rw [D1]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα hEn)
    have hlow := quad_lower_of_face hlowG hdb Gd Gb' Gb S₂ S₄ (Or.inl ⟨Gc, Gc'⟩)
    exact NWS4_quad_swap (nws4_closing_x' S₁ S₂ S₃ S₄ hlow
      (fun h => hN (NWS4_quad_swap h)) hgood htouch)
  · have S₁ : 0 < det3 (b' - c') (c - c') (b - d) := by rw [K2]; exact mul_pos hκ' hEp
    have S₂ : 0 < det3 (b' - d) (c - d) (b - d) := by rw [K24]; exact mul_pos hα hEp
    have S₃ : 0 < det3 (c' - d) (c - d) (b - d) := by rw [K14]; exact mul_pos hα₁p hEp
    have S₄ : 0 < det3 (c' - d) (b' - d) (b - d) := by rw [K13]; exact mul_pos pβα₁ hEp
    have hlow := quad_lower_of_face hlowG hdb Gd Gb' Gb S₂ S₄ (Or.inr ⟨Gc, Gc'⟩)
    exact nws4_closing_x' S₁ S₂ S₃ S₄ hlow hN (by rwa [min_comm])
      (fun h => htouch ⟨h.2, h.1⟩)

set_option maxHeartbeats 1000000 in
/-- **The T4 case of Theorem 10.1 by slides, given the closing.**  In the frame
`d; a, c, b` (`b' = d + α (a − d) + β (c − d)`, `c' = d + α₁ (a − d) + β₁ (b − d)`,
`a' = d + α₂ (b − d) + β₂ (c − d)`), with far ends `c'` (`α₁ > 1`) and `c` (`β₂ < 1`) at
the view along `d b` and `b'` a corner (`κ' > 0`): if `K_b`'s rim `b c' b' c` has no weak
saddle, slide it along `Q_bc`; if `K_d`'s rim `d c' b' c` has none, slide it along `Q_ab`. -/
theorem isRupert_t4_sel {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hαβ₂ : 1 < α₂ + β₂)
    (hκ : 0 < α + α₁ * (β - 1))
    (hsel : (NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
        NoBadNormal (quad b c' b' c) (b - d) (c - d)) ∨
      (NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
        NoBadNormal (quad d c' b' c) (b - d) (a - d))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨K0, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16, K17, K18,
    K19, K20, K21, K22, K23, K24, K25, K26, D3, D21, D2, D1⟩ := t4_slide_dets hb' hc' ha'
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hα₁p : 0 < α₁ := by linarith
  have pK20 : 0 < α * β₂ + β * α₁ - α₁ * β₂ := by
    rw [show α * β₂ + β * α₁ - α₁ * β₂ = β₂ * (α + α₁ * (β - 1)) + α₁ * β * (1 - β₂) by ring]
    exact add_pos (mul_pos hβ₂ hκ) (mul_pos (mul_pos hα₁p hβ) (by linarith))
  have pK21 : 0 < -α * β₂ + α := by
    rw [show -α * β₂ + α = α * (1 - β₂) by ring]; exact mul_pos hα (by linarith)
  have hκ' : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  have pK10 : 0 < β * α₁ - β := by
    rw [show β * α₁ - β = β * (α₁ - 1) by ring]; exact mul_pos hβ (by linarith)
  have pβα₁ : 0 < β * α₁ := mul_pos hβ hα₁p
  rcases hsel with ⟨hN, hsb⟩ | ⟨hN', hsd⟩
  · -- `K_b`, sliding along `Q_bc` (`e = c − d`): `d` and `a'` are middles, `a` goes inside
    refine isRupert_of_slide' V {d, a'} (b - d) (c - d) hu (quad b c' b' c) ?_ ?_
      (quad_injective hbc' hbb' hbc (Ne.symm hb'c') (Ne.symm hcc') hb'c) (by norm_num)
      (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_ (eventually_unimodal_quad_slide hN) hsb
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
      exacts [⟨Ne.symm hdb, Ne.symm ha'b⟩, ⟨Ne.symm hdc', Ne.symm ha'c'⟩,
        ⟨Ne.symm hdb', Ne.symm ha'b'⟩, ⟨Ne.symm hdc, Ne.symm ha'c⟩]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      exacts [pos_of_coef K0 (by positivity) hE, pos_of_coef K1 hα₁p hE,
        pos_of_coef K2 hκ' hE, pos_of_coef K3 (by positivity) hE, pos_of_coef K4 hα hE,
        pos_of_coef K5 hκ' hE, pos_of_coef K6 hα₁p hE, pos_of_coef K7 hα hE]
    · intro z hz hzM hzx i
      have hza : z = a := by
        have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
        simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
        simp only [mem_insert, mem_singleton, not_or] at hzM
        rcases hmemV z hz with h | h | h | h | h | h | h
        exacts [absurd h hzM.1, h, absurd h hzM.2, absurd h h0, absurd h h2, absurd h h3,
          absurd h h1]
      rw [hza]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact slideTest_zero K8 K9 (by linarith) hE
      · exact slideTest_strict K10 pK10 hE
      · exact slideTest_strict K11 (by linarith) hE
      · exact slideTest_strict K12 one_pos hE
    · intro m hm
      rcases mem_insert.mp hm with h | h
      · rw [h]
        filter_upwards [self_mem_nhdsWithin] with t ht0
        have ht : (0 : ℝ) < t := ht0
        have h1 : (1 + t) ≠ 0 := by positivity
        refine ⟨3, 1 / (1 + t), -1 / (1 + t), by positivity, ?_, ?_, ?_⟩
        · rw [div_lt_one (by positivity)]; linarith
        · exact div_ne_zero (by norm_num) h1
        · simp only [a3, quad_3, quad_0]; match_scalars <;> field_simp <;> ring
      · rw [mem_singleton.mp h]
        filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := 1 - α₂) hβ₂] with t ht0 hlt
        have ht : (0 : ℝ) < t := ht0
        have h1 : (1 + t) ≠ 0 := by positivity
        refine ⟨3, (1 - β₂ + t * α₂) / (1 + t), (α₂ + β₂ - 1) / (1 + t), ?_, ?_, ?_, ?_⟩
        · exact div_pos (by have := mul_pos ht hα₂; linarith) (by positivity)
        · rw [div_lt_one (by positivity)]; linarith
        · exact div_ne_zero (by linarith) h1
        · simp only [a3, quad_3, quad_0]; rw [ha']; match_scalars <;> field_simp <;> ring
  · -- `K_d`, sliding along `Q_ab` (`e = d − a`)
    refine isRupert_of_slide' V {b, a} (b - d) (d - a) hu (quad d c' b' c) ?_ ?_
      (quad_injective hdc' hdb' hdc (Ne.symm hb'c') (Ne.symm hcc') hb'c) (by norm_num)
      (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_ (eventually_unimodal_quad_slide hN') ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
      exacts [⟨hdb, hda⟩, ⟨Ne.symm hbc', Ne.symm hac'⟩, ⟨Ne.symm hbb', Ne.symm hab'⟩,
        ⟨Ne.symm hbc, Ne.symm hac⟩]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      exacts [pos_of_coef K13 (by positivity) hE, pos_of_coef K14 hα₁p hE,
        pos_of_coef K2 hκ' hE, pos_of_coef K15 (by positivity) hE, pos_of_coef K16 hα hE,
        pos_of_coef K5 hκ' hE, pos_of_coef K17 hα₁p hE, pos_of_coef K18 hα hE]
    · intro z hz hzM hzx i
      have hza : z = a' := by
        have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
        simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
        simp only [mem_insert, mem_singleton, not_or] at hzM
        rcases hmemV z hz with h | h | h | h | h | h | h
        exacts [absurd h h0, absurd h hzM.2, h, absurd h hzM.1, absurd h h2, absurd h h3,
          absurd h h1]
      rw [hza]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact slideTest_strict K19 (by positivity) hE
      · exact slideTest_strict K20 pK20 hE
      · exact slideTest_strict K21 pK21 hE
      · exact slideTest_zero K22 K23 hα₂ hE
    · intro m hm
      rcases mem_insert.mp hm with h | h
      · rw [h]
        filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := β₁ - 1) hα₁p] with t ht0 hlt
        have ht : (0 : ℝ) < t := ht0
        have h1 : (α₁ + t * β₁) ≠ 0 := by positivity
        refine ⟨0, t / (α₁ + t * β₁), α₁ / (α₁ + t * β₁), by positivity, ?_, by positivity, ?_⟩
        · rw [div_lt_one (by positivity)]; linarith
        · simp only [a0, quad_0, quad_1]; rw [hc']
          match_scalars <;> field_simp <;> ring
      · rw [mem_singleton.mp h]
        filter_upwards [self_mem_nhdsWithin] with t ht0
        have ht : (0 : ℝ) < t := ht0
        have h1 : (α₁ + t * β₁) ≠ 0 := by positivity
        refine ⟨0, 1 / (α₁ + t * β₁), -β₁ / (α₁ + t * β₁), by positivity, ?_, ?_, ?_⟩
        · rw [div_lt_one (by positivity)]; linarith [mul_pos ht hβ₁]
        · exact div_ne_zero (by linarith) h1
        · simp only [a0, quad_0, quad_1]; rw [hc']
          match_scalars <;> field_simp <;> ring
    · exact hsd.of_span 0 (-1) (by module)



/-- **The T4 case of Theorem 10.1 by slides (Lemma 5 with Lemma C).**  In the frame
`d; a, c, b` (`b' = d + α (a − d) + β (c − d)`, `c' = d + α₁ (a − d) + β₁ (b − d)`,
`a' = d + α₂ (b − d) + β₂ (c − d)`), with far ends `c'` (`α₁ > 1`) and `c` (`β₂ < 1`) at
the view along `d b` and `b'` a corner (`κ' > 0`): if `K_b`'s rim `b c' b' c` has no weak
saddle, slide it along `Q_bc`; otherwise (the edge `d → b` not bad, no triple tie
`z c = z c' = z b'`) `K_d`'s rim `d c' b' c` has none, and slide it along `Q_ab`. -/
theorem isRupert_t4_slide {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hαβ₂ : 1 < α₂ + β₂)
    (hκ : 0 < α + α₁ * (β - 1))
    (hgood : ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (htouch : ¬ (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫))
    (hsb : NoBadNormal (quad b c' b' c) (b - d) (c - d) ∨
      (UniOrSep (quint b c' b' c a') (b - d) ∧
        NoBadNormal (quint b c' b' c a') (b - d) (a - d)))
    (hsd : NoBadNormal (quad d c' b' c) (b - d) (a - d) ∨
      (UniOrSep (quint d a c' b' c) (b - d) ∧
        NoBadNormal (quint d a c' b' c) (b - d) (c - d))) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  rcases hsb with hsb | ⟨hu5, hs5⟩
  swap
  · exact isRupert_t4b_five hb' hc' ha' hnd hE hα hβ hα₁ hβ₁ hβ₂ hβ₂1 hαβ₂ hκ hu5 hs5
  rcases hsd with hsd | ⟨hu5, hs5⟩
  swap
  · exact isRupert_t4d_five hb' hc' ha' hnd hE hα hβ hαβ hα₁ hβ₁ hα₂ hβ₂ hβ₂1 hκ hu5 hs5
  by_cases hN : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)
  · exact isRupert_t4_sel hb' hc' ha' hnd hE hα hβ hαβ hα₁ hβ₁ hα₂ hβ₂ hβ₂1 hαβ₂ hκ
      (Or.inl ⟨hN, hsb⟩)
  · have hdb : d ≠ b := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true] at hnd
      exact hnd.1.2.2.1
    exact isRupert_t4_sel hb' hc' ha' hnd hE hα hβ hαβ hα₁ hβ₁ hα₂ hβ₂ hβ₂1 hαβ₂ hκ
      (Or.inr ⟨t4_closing hb' hc' ha' hdb hE hα hβ (by linarith) hβ₁ hκ hgood htouch hN, hsd⟩)

set_option maxHeartbeats 1000000 in
/-- **Case Q of Theorem 10.1 by slides (Lemma 1 (c) with Lemma C).**  In the frame
`d; a, c, b`, with far ends `a` (`α₁ < 1`) and `c` (`β₂ < 1`) at the view along `d b`,
`K_d`'s rim is the face `Q_ac = d a b' c`, a convex planar quadrilateral with no weak
saddle unless `b − d` is normal to its plane; slide it along `Q_ab` (`c'` and `b` are
middles, `a'` goes inside) or along `Q_bc` (`a'` and `b` are middles, `c'` goes inside). -/
theorem isRupert_q_slide {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 0 < α₁) (hα₁1 : α₁ < 1) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hlev : ⟪a - d, b - d⟫ ≠ 0 ∨ ⟪c - d, b - d⟫ ≠ 0)
    (hs : NoBadNormal (quad d a b' c) (b - d) (a - d) ∨
      NoBadNormal (quad d a b' c) (b - d) (c - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  -- the coefficients
  have pαβ : 0 < α + β - 1 := by linarith
  have pQ9 : 0 < α * β₂ + β - β₂ := by
    rcases le_or_gt 1 α with h1 | h1
    · rw [show α * β₂ + β - β₂ = β + β₂ * (α - 1) by ring]
      exact add_pos_of_pos_of_nonneg hβ (mul_nonneg hβ₂.le (by linarith))
    · rw [show α * β₂ + β - β₂ = (α + β - 1) + (1 - α) * (1 - β₂) by ring]
      exact add_pos pαβ (mul_pos (by linarith) (by linarith))
  have pQ10 : 0 < -α * β₂ + α := by
    rw [show -α * β₂ + α = α * (1 - β₂) by ring]; exact mul_pos hα (by linarith)
  have pQ15 : 0 < -β * α₁ + β := by
    rw [show -β * α₁ + β = β * (1 - α₁) by ring]; exact mul_pos hβ (by linarith)
  have pQ16 : 0 < α + β * α₁ - α₁ := by
    rcases le_or_gt 1 β with h1 | h1
    · rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]
      exact add_pos_of_pos_of_nonneg hα (mul_nonneg hα₁.le (by linarith))
    · rw [show α + β * α₁ - α₁ = (α + β - 1) + (1 - α₁) * (1 - β) by ring]
      exact add_pos pαβ (mul_pos (by linarith) (by linarith))
  obtain ⟨Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15, Q16, Q17⟩ :=
    q_slide_dets hb' hc' ha'
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  -- the rim `d a b' c` (the face `Q_ac`): no weak saddle
  have hN : NWS4 (quad ⟪d, b - d⟫ ⟪a, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) := by
    refine nws4_of_planar_quad' hα hβ hαβ hb' ?_
    rcases hlev with h | h
    · left; intro h'; apply h; rw [inner_sub_left, h', sub_self]
    · right; intro h'; apply h; rw [inner_sub_left, h', sub_self]
  have hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < det3 (a - d) (c - d) (b - d) *
      det3 (quad d a b' c (i + 1) - quad d a b' c i) (quad d a b' c j - quad d a b' c i) (b - d) := by
    intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [pos_of_coef Q0 hβ hE, pos_of_coef Q1 one_pos hE, pos_of_coef Q2 pαβ hE,
      pos_of_coef Q3 hβ hE, pos_of_coef Q4 hα hE, pos_of_coef Q5 pαβ hE, pos_of_coef Q6 one_pos hE,
      pos_of_coef Q7 hα hE]
  have hxV : ∀ i, quad d a b' c i ∈ V := by
    intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [V, quad_0, quad_1, quad_2, quad_3]
  have hinj := quad_injective hda hdb' hdc hab' hac hb'c
  rcases hs with hs | hs
  · -- along `Q_ab` (`e = d − a`): `b`, `c'` are middles over `d a`; `a'` goes inside
    refine isRupert_of_slide' V {b, c'} (b - d) (d - a) hu (quad d a b' c) hxV ?_ hinj
      (by norm_num) (det3 (a - d) (c - d) (b - d)) hE hcyc ?_ ?_
      (eventually_unimodal_quad_slide hN) ?_
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
      exacts [⟨hdb, hdc'⟩, ⟨hab, hac'⟩, ⟨Ne.symm hbb', hb'c'⟩, ⟨Ne.symm hbc, hcc'⟩]
    · intro z hz hzM hzx i
      have hza : z = a' := by
        have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
        simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
        simp only [mem_insert, mem_singleton, not_or] at hzM
        rcases hmemV z hz with h | h | h | h | h | h | h
        exacts [absurd h h0, absurd h h1, h, absurd h hzM.1, absurd h h2, absurd h h3,
          absurd h hzM.2]
      rw [hza]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact slideTest_strict Q8 hβ₂ hE
      · exact slideTest_strict Q9 pQ9 hE
      · exact slideTest_strict Q10 pQ10 hE
      · exact slideTest_zero Q11 Q12 hα₂ hE
    · intro m hm
      rcases mem_insert.mp hm with h | h
      · rw [h]
        filter_upwards [self_mem_nhdsWithin, eventually_lt_one] with t ht0 ht1
        refine ⟨0, t, 1, ht0, ht1, one_ne_zero, ?_⟩
        simp only [a0, quad_0, quad_1]; module
      · rw [mem_singleton.mp h]
        filter_upwards [eventually_pos_of_pos (B := -β₁) (show 0 < 1 - α₁ by linarith),
          self_mem_nhdsWithin] with t hlt ht0
        have ht : (0 : ℝ) < t := ht0
        refine ⟨0, α₁ + t * β₁, β₁, by positivity, by linarith, hβ₁.ne', ?_⟩
        simp only [a0, quad_0, quad_1]; rw [hc']; module
    · exact hs.of_span 0 (-1) (by module)
  · -- along `Q_bc` (`e = d − c`): `b`, `a'` are middles over `c d`; `c'` goes inside
    refine isRupert_of_slide' V {b, a'} (b - d) (d - c) hu (quad d a b' c) hxV ?_ hinj
      (by norm_num) (det3 (a - d) (c - d) (b - d)) hE hcyc ?_ ?_
      (eventually_unimodal_quad_slide hN) ?_
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
      exacts [⟨hdb, hda'⟩, ⟨hab, haa'⟩, ⟨Ne.symm hbb', Ne.symm ha'b'⟩, ⟨Ne.symm hbc, Ne.symm ha'c⟩]
    · intro z hz hzM hzx i
      have hza : z = c' := by
        have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
        simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
        simp only [mem_insert, mem_singleton, not_or] at hzM
        rcases hmemV z hz with h | h | h | h | h | h | h
        exacts [absurd h h0, absurd h h1, absurd h hzM.2, absurd h hzM.1, absurd h h2,
          absurd h h3, h]
      rw [hza]
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact slideTest_zero Q13 Q14 hβ₁ hE
      · exact slideTest_strict Q15 pQ15 hE
      · exact slideTest_strict Q16 pQ16 hE
      · exact slideTest_strict Q17 hα₁ hE
    · intro m hm
      rcases mem_insert.mp hm with h | h
      · rw [h]
        filter_upwards [self_mem_nhdsWithin, eventually_lt_one] with t ht0 ht1
        have ht : (0 : ℝ) < t := ht0
        refine ⟨3, 1 - t, 1, by linarith, by linarith, one_ne_zero, ?_⟩
        simp only [a3, quad_3, quad_0]; module
      · rw [mem_singleton.mp h]
        filter_upwards [eventually_pos_of_pos (B := -α₂) (show 0 < 1 - β₂ by linarith),
          self_mem_nhdsWithin] with t hlt ht0
        have ht : (0 : ℝ) < t := ht0
        refine ⟨3, 1 - β₂ - t * α₂, α₂, by linarith, by nlinarith [mul_pos ht hα₂], hα₂.ne', ?_⟩
        simp only [a3, quad_3, quad_0]; rw [ha']; module
    · exact hs.of_span 0 (-1) (by module)


end Minimality

end
