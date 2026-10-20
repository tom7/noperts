module

public import Minimality.Type08Lemmas
public import Minimality.L8T3

@[expose] public section

/-!
# Type 08: the cases of Theorem 10.1 (`FEWER-FACES-PROOFS.md` §10)

`K = O ∪ {d}`: the octahedron `O` with opposite pairs `(a, a')`, `(b, b')`,
`(c, c')` and the cap `d` (`IsCap`, `Type08Lemmas.lean`).  Each case of Theorem 10.1
ends in an edge crossing whose reduced polygon `K_v` is unimodal at the view
along the edge; Theorem 8.9 with Theorem 7.3 (`isRupert_of_edgeChords_unimodal`)
gives the passage unless `K_v` has a horizontal double normal there.

* `isRupert_of_edgeView`: Theorem 8.9 with a unimodal `K_v`, from determinant
  tests at the view (no rotation in the statement), excluding horizontal double
  normals by `NoHDNAt`.
* `isRupert_quad_edge_middle` (the case N2 of Theorem 10.1): Lemma 9.3 at a quad
  edge `x → y` of an octahedron with one extra point over the chord from `y` to a
  far end (a middle).  Lemma 2 makes the cap such a point at the QT edge `a' → c`.
* `isRupert_type08_Q` (Lemma 1 (c)): far ends `a` and `c` at the view along `d b`;
  `K_d` is the face `Q_ac`.
The third case (the T4 `K − a`, Lemma 5) is in `Type08T4.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Theorem 8.9 at an edge view, from determinant tests -/

/-- **No horizontal double normal at the view `±u`.**  For every rotation taking
`u` to a nonzero multiple of `e_z`, no strictly convex cycle of points of `V` has a
horizontal double normal.  At a fixed view this fails only in codimension 1
(Lemma 7.4); it is the exclusion of Theorem 10.1. -/
def NoHDNAt (V : Finset ℝ³) (u : ℝ³) : Prop :=
  ∀ R ∈ SO3, ∀ r : ℝ, r ≠ 0 → R.toEuclideanLin u = r • ez → ∀ (k : ℕ) (x : ZMod k → ℝ³),
    (∀ i, x i ∈ V) → IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) →
    ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)

theorem NoHDNAt.neg {V : Finset ℝ³} {u : ℝ³} (h : NoHDNAt V u) : NoHDNAt V (-u) := by
  intro R hR r hr hRu
  refine h R hR (-r) (neg_ne_zero.mpr hr) ?_
  rw [map_neg] at hRu
  rw [neg_smul, ← hRu, neg_neg]

theorem NoHDNAt.mono {V W : Finset ℝ³} {u : ℝ³} (h : NoHDNAt W u) (hVW : V ⊆ W) :
    NoHDNAt V u :=
  fun R hR r hr hRu k x hx => h R hR r hr hRu k x (fun i => hVW (hx i))

theorem IsCyclicUnimodal.smul {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : IsCyclicUnimodal z)
    {c : ℝ} (hc : 0 < c) : IsCyclicUnimodal (fun i => c * z i) := by
  refine ⟨fun i j hij => hz.1 (mul_left_cancel₀ hc.ne' hij), ?_⟩
  simp only [mul_lt_mul_iff_right₀ hc]
  exact hz.2

/-- **Theorem 8.9 with a unimodal `K_v`, at an edge view given by determinant
tests.**  Two faces share the edge `v w` (`v = x i₀`, `w = v − h u₀`); the cycle `x`
passes all determinant tests at `u₀` (strictly convex, counterclockwise), every
other point except the middles `M` and `w` is strictly inside, the depths
`⟪x i, u₀⟫` are cyclically unimodal, and there is no horizontal double normal.
Then `V` is Rupert. -/
theorem isRupert_of_edgeView (V M : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → y ≠ w → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsCyclicUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt (V.erase w) u₀)
    (hM : ∀ m ∈ M, EdgeMiddle u₀ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) : IsRupert V := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u₀ hu₀
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  refine isRupert_of_edgeChords_unimodal V M R hR hr hRu x i₀ w h hwV hw hh hxV hxM hp ?_ ?_ ?_ hM
  · intro y hy hyM hyw hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyw hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact hnd R hR r hr.ne' hRu k x
      (fun i => mem_erase.mpr ⟨corner_ne_axle hr hRu hp hw hh i, hxV i⟩) hp

theorem zmod4_zero_add_one : (0 : ZMod 4) + 1 = 1 := by decide
theorem zmod4_zero_sub_one : (0 : ZMod 4) - 1 = 3 := by decide

/-- Depths of a 4-cycle as a `quad`. -/
theorem quad_inner (p₀ p₁ p₂ p₃ u : ℝ³) :
    (fun i => ⟪quad p₀ p₁ p₂ p₃ i, u⟫) = quad ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ := by
  funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

/-! ### Case N2: Lemma 9.3 with a middle -/

/-- **Lemma 9.3 with a middle, oriented.**  At a quad edge `x → y` of an
octahedron that is neither bad nor touching, with one more point `m` over the
chord from `y` to `p` or to `p'` (on the side away from `x`): the closing of
Lemma 9.3 gives a unimodal `K_v` (`v = y`, or `v = x` with `m` on the chain of
`w = y`), and Theorem 8.9 applies. -/
theorem isRupert_quad_edge_middle_core {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧
      (m = y + s • (p - y) + δ • (y - x) ∨ m = y + s • (p' - y) + δ • (y - x)))
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = p ∨ s = p') → (t = y' ∨ t = p ∨ t = p') →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hnd : NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hor
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
  -- the middle `m` for either choice of `v`
  have hEM : ∀ v w : ℝ³, ∀ hh : ℝ, ((v = y ∧ hh = 1) ∨ (w = y ∧ hh = -1)) →
      EdgeMiddle u v w p p' hh m := by
    intro v w hh hvw
    have hc : y = v ∨ (y = w ∧ δ * hh < 0) := by
      rcases hvw with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, by linarith⟩
    rcases hm with hm | hm
    · exact ⟨y, s, δ, hc, hs0, hs1, hδ.ne', Or.inl hm⟩
    · refine ⟨y, 1 - s, δ, hc, by linarith, by linarith, hδ.ne', Or.inr ?_⟩
      rw [hm]; module
  have hpy' : ⟪p, u⟫ ≠ ⟪y', u⟫ := fun h =>
    hinj p y' (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (Or.inl rfl) (Ne.symm hy'p) h
  have hpp'u : ⟪p, u⟫ ≠ ⟪p', u⟫ :=
    hinj p p' (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (Or.inr (Or.inr rfl)) hpp'
  have hy'p'u : ⟪y', u⟫ ≠ ⟪p', u⟫ :=
    hinj y' p' (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr rfl)) hy'p'
  have hinjq : ∀ z : ℝ³, (z = x ∨ z = y) → z ≠ p → z ≠ y' → z ≠ p' → Function.Injective
      (quad ⟪z, u⟫ ⟪p, u⟫ ⟪y', u⟫ ⟪p', u⟫) := by
    intro z hz h1 h2 h3
    have hs : z = x ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
      rcases hz with h | h
      exacts [Or.inl h, Or.inr (Or.inl h)]
    exact quad_injective (hinj z p hs (Or.inr (Or.inl rfl)) h1)
      (hinj z y' hs (Or.inl rfl) h2) (hinj z p' hs (Or.inr (Or.inr rfl)) h3) hpy' hpp'u hy'p'u
  by_cases hN : NWS4 (quad ⟪y, u⟫ ⟪p, u⟫ ⟪y', u⟫ ⟪p', u⟫)
  · -- `K_y` is unimodal
    refine isRupert_of_edgeView V {m} u hu (k := 4) (by norm_num) (quad y p y' p') 0 x 1
      (by simp [V]) (by simp only [quad_0, one_smul, u]; abel) one_ne_zero ?_ ?_ ?_ ?_ ?_
      hnd.1 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_singleton]
      exacts [Ne.symm hmy, Ne.symm hmp, Ne.symm hmy', Ne.symm hmp']
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 y my hyp hyy'
      · exact E3 y my hyy' hyp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · exact absurd (mem_singleton.mpr h) hzM
      · exact absurd h hzw
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h h0
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 (hinjq y (Or.inr rfl) hyp hyy' hyp') hN
    · intro m' hm'
      rw [mem_singleton.mp hm', zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM y x 1 (Or.inl ⟨rfl, rfl⟩)
  · -- `K_x` is unimodal (the closing by `x` of Lemma 9.3)
    have hS₁ := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    have hS₂ : 0 < det3 (y' - x) (p' - x) u := by
      rw [← det3_cyc x y' p']; exact E3 x mx hxy' hxp'
    have hS₃ : 0 < det3 (p - x) (p' - x) u := by rw [det3_shift_xy]; exact hor
    have hS₄ : 0 < det3 (p - x) (y' - x) u := by
      rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    have hlow := quad_edge_lower F hS₁ hS₂ hS₃ hS₄
    have hsum := four_point_sum x p y' p' u
    have htouch : ⟪p, u⟫ ≠ ⟪p', u⟫ := hpp'u
    have hN' : NWS4 (quad ⟪x, u⟫ ⟪p, u⟫ ⟪y', u⟫ ⟪p', u⟫) := by
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
      exact htouch (by linarith)
    refine isRupert_of_edgeView V {m} u hu (k := 4) (by norm_num) (quad x p y' p') 0 y (-1)
      (by simp [V]) (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add, u]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd.2 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_singleton]
      exacts [Ne.symm hmx, Ne.symm hmp, Ne.symm hmy', Ne.symm hmp']
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · rw [det3_shift_xy]; exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 x mx hxp hxy'
      · exact E3 x mx hxy' hxp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · rw [det3_shift_p']; exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · rw [det3_shift_p']; exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · exact absurd (mem_singleton.mpr h) hzM
      · exact absurd h h0
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · rw [det3_shift_p']; exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h hzw
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 (hinjq x (Or.inl rfl) hxp hxy' hxp') hN'
    · intro m' hm'
      rw [mem_singleton.mp hm', zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM x y (-1) (Or.inr ⟨rfl, rfl⟩)

/-- **Lemma 9.3 with a middle.**  At a quad edge `x → y` of an octahedron (`x'`
hidden) that is not bad, with one more point `m` over the chord from `y` to `p`
or to `p'` (strictly between, on the side away from `x`), in general position
(distinct depths along `y − x`, no horizontal double normal at the view), the
seven points are Rupert. -/
theorem isRupert_quad_edge_middle {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧
      (m = y + s • (p - y) + δ • (y - x) ∨ m = y + s • (p' - y) + δ • (y - x)))
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = p ∨ s = p') → (t = y' ∨ t = p ∨ t = p') →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hnd : NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  have e : (insert m {x, x', y, y', p', p} : Finset ℝ³) = insert m {x, x', y, y', p, p'} := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · have := isRupert_quad_edge_middle_core F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
      (by rwa [min_comm])
      (by obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid; exact ⟨s, δ, h1, h2, h3, h4.symm⟩)
      ⟨hmO.1, hmO.2.1, hmO.2.2.1, hmO.2.2.2.1, hmO.2.2.2.2.2, hmO.2.2.2.2.1⟩
      (fun s t hs ht => hinj s t (by rcases hs with h | h | h | h | h <;> simp only [h, true_or, or_true])
        (by rcases ht with h | h | h <;> simp only [h, true_or, or_true])) (by rw [e]; exact hnd)
    rwa [e] at this
  · exact isRupert_quad_edge_middle_core F hq₁ hq₂ hpos hgood hmid hmO hinj hnd

/-! ### Case Q: far ends `a` and `c`; `K_d` is the face `Q_ac` -/

/-- Three affine functions with a nonsingular matrix of values on a frame make
the frame a basis. -/
theorem det3_ne_zero_of_affine3 {f₀ f₁ f₂ : ℝ³ → ℝ} {N₀ N₁ N₂ : ℝ³}
    (h₀ : ∀ y z, f₀ y - f₀ z = ⟪N₀, y - z⟫) (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫)
    (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫) (o e₀ e₁ e₂ : ℝ³)
    (hdet : (f₀ e₀ - f₀ o) * ((f₁ e₁ - f₁ o) * (f₂ e₂ - f₂ o) - (f₁ e₂ - f₁ o) * (f₂ e₁ - f₂ o)) -
      (f₀ e₁ - f₀ o) * ((f₁ e₀ - f₁ o) * (f₂ e₂ - f₂ o) - (f₁ e₂ - f₁ o) * (f₂ e₀ - f₂ o)) +
      (f₀ e₂ - f₀ o) * ((f₁ e₀ - f₁ o) * (f₂ e₁ - f₂ o) - (f₁ e₁ - f₁ o) * (f₂ e₀ - f₂ o)) ≠ 0) :
    det3 (e₀ - o) (e₁ - o) (e₂ - o) ≠ 0 := by
  rw [h₀ e₀, h₀ e₁, h₀ e₂, h₁ e₀, h₁ e₁, h₁ e₂, h₂ e₀, h₂ e₁, h₂ e₂, ← det3_mul_det3] at hdet
  exact right_ne_zero_of_mul hdet

/-- The plane of `Q_ac` does not contain the direction `b − d`. -/
theorem IsCap.det_Qac_ne {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d) :
    det3 (a - d) (c - d) (b - d) ≠ 0 := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  refine det3_ne_zero_of_affine3 F.ab'c.hN F.a'bc.hN F.abc'.hN d a c b ?_
  rw [hd.ab'c, hd.a'bc, hd.abc', F.ab'c.hP, F.ab'c.hR, F.a'bc.hR, F.a'bc.hQ, F.abc'.hP,
    F.abc'.hQ]
  have n1 := F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc
  have n2 := F.a'bc.neg a (by simp) haa' hab hac
  have n3 := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  simp only [sub_zero, mul_zero, zero_mul, sub_self, zero_add]
  exact mul_ne_zero n1.ne (mul_ne_zero n2.ne n3.ne)

/-- The determinant tests of the case Q, as multiples of
`D = det3 (a − d) (c − d) u` (for the rim `d, a, b', c` and its reverse). -/
theorem q_dets {a c d b' u : ℝ³} {α β : ℝ} (hb' : b' = d + α • (a - d) + β • (c - d)) :
    let D := det3 (a - d) (c - d) u
    det3 (a - d) (b' - d) u = β * D ∧
    det3 (b' - a) (c - a) u = (α + β - 1) * D ∧
    det3 (b' - a) (d - a) u = β * D ∧
    det3 (c - b') (d - b') u = α * D ∧
    det3 (c - b') (a - b') u = (α + β - 1) * D ∧
    det3 (d - c) (a - c) u = D ∧
    det3 (d - c) (b' - c) u = α * D ∧
    det3 (c - d) (b' - d) u = -(α * D) ∧
    det3 (c - d) (a - d) u = -D ∧
    det3 (b' - c) (a - c) u = -((α + β - 1) * D) ∧
    det3 (b' - c) (d - c) u = -(α * D) ∧
    det3 (a - b') (d - b') u = -(β * D) ∧
    det3 (a - b') (c - b') u = -((α + β - 1) * D) ∧
    det3 (d - a) (c - a) u = -D ∧
    det3 (d - a) (b' - a) u = -(β * D) := by
  intro D
  subst hb'
  simp only [D, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **Case Q of Theorem 10.1 (Lemma 1 (c)).**  At the view along `d b`, if the far end
of `Q_ab` is `a` and that of `Q_bc` is `c`, then `K_d` is the face `Q_ac = (d, a, b', c)`
(the middles are `c'` and `a'`), a convex planar quadrilateral, unimodal by
Lemma 1 (c); with distinct depths and no horizontal double normal, `K` is Rupert. -/
theorem isRupert_type08_Q {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hfa : F.a'bc.f a < F.a'bc.f c') (hfc : F.abc'.f c < F.abc'.f a')
    (hinj : ∀ s t, (s = d ∨ s = a ∨ s = b' ∨ s = c) → (t = d ∨ t = a ∨ t = b' ∨ t = c) →
      s ≠ t → ⟪s, b - d⟫ ≠ ⟪t, b - d⟫)
    (hnd : NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase b) (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  set u := b - d with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  -- the three quadrilaterals in coordinates
  obtain ⟨hα, hβ, hαβ, hb'⟩ := hd.Qac_coords'
  set α := F.a'bc.f b' / F.a'bc.f a
  set β := F.abc'.f b' / F.abc'.f c
  obtain ⟨hα₁, hβ₁, hαβ₁, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  set α₁ := F.a'bc.f c' / F.a'bc.f a
  set β₁ := F.ab'c.f c' / F.ab'c.f b
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  set α₂ := F.ab'c.f a' / F.ab'c.f b
  set β₂ := F.abc'.f a' / F.abc'.f c
  have hα₁1 : α₁ < 1 :=
    (div_lt_one_of_neg (F.a'bc.neg a (by simp) haa' hab hac)).mpr hfa
  have hβ₂1 : β₂ < 1 :=
    (div_lt_one_of_neg (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')).mpr hfc
  -- the middles over the chords from `b`
  have hmc' : c' = b + α₁ • (a - b) + (α₁ + β₁ - 1) • u := by rw [hc']; module
  have hma' : a' = b + β₂ • (c - b) + (α₂ + β₂ - 1) • u := by rw [ha']; module
  -- the determinant tests, as multiples of `D`
  set D := det3 (a - d) (c - d) u
  have hD : D ≠ 0 := hd.det_Qac_ne
  obtain ⟨T1, T3, T4, T5, T6, T7, T8, R1, R2, R3, R4, R5, R6, R7, R8⟩ := q_dets (u := u) hb'
  have hαβ1 : 0 < α + β - 1 := sub_pos.mpr hαβ
  -- distinct depths on the rim
  have hi : ∀ s t, (s = d ∨ s = a ∨ s = b' ∨ s = c) → (t = d ∨ t = a ∨ t = b' ∨ t = c) →
      s ≠ t → ⟪s, u⟫ ≠ ⟪t, u⟫ := hinj
  have Hdb' : d ≠ b' := hdb'
  have hrestV : ∀ (x : ZMod 4 → ℝ³), (∀ j, x j = d ∨ x j = a ∨ x j = b' ∨ x j = c) →
      (∀ z, z = d ∨ z = a ∨ z = b' ∨ z = c → ∃ j, z = x j) →
      ∀ z ∈ V, z ∉ ({a', c'} : Finset ℝ³) → z ≠ b → (∀ j, z ≠ x j) → False := by
    intro x _ hx z hz hzM hzb hzx
    rcases hmemV z hz with h | h | h | h | h | h | h
    · obtain ⟨j, hj⟩ := hx z (Or.inl h); exact hzx j hj
    · obtain ⟨j, hj⟩ := hx z (Or.inr (Or.inl h)); exact hzx j hj
    · exact hzM (by simp [h])
    · exact hzb h
    · obtain ⟨j, hj⟩ := hx z (Or.inr (Or.inr (Or.inl h))); exact hzx j hj
    · obtain ⟨j, hj⟩ := hx z (Or.inr (Or.inr (Or.inr h))); exact hzx j hj
    · exact hzM (by simp [h])
  rcases lt_or_gt_of_ne hD with hDn | hDp
  · -- counterclockwise `d, c, b', a`
    refine isRupert_of_edgeView V {a', c'} u hu (k := 4) (by norm_num) (quad d c b' a) 0 b (-1)
      (by simp [V]) (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add, u]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
      exacts [⟨hda', hdc'⟩, ⟨Ne.symm ha'c, hcc'⟩, ⟨Ne.symm ha'b', hb'c'⟩, ⟨haa', hac'⟩]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [R1]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα hDn)
      · rw [R2]; exact neg_pos.mpr hDn
      · rw [R3]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hαβ1 hDn)
      · rw [R4]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα hDn)
      · rw [R5]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hβ hDn)
      · rw [R6]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hαβ1 hDn)
      · rw [R7]; exact neg_pos.mpr hDn
      · rw [R8]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hβ hDn)
    · intro z hz hzM hzw hzx
      exact (hrestV (quad d c b' a) (fun j => by
        rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3])
        (fun z hz => by
          rcases hz with h | h | h | h
          exacts [⟨0, h⟩, ⟨3, h⟩, ⟨2, h⟩, ⟨1, h⟩]) z hz hzM hzw hzx).elim
    · rw [quad_inner]
      refine isCyclicUnimodal_of_NWS4 (quad_injective (hi d c (by simp) (by simp) hdc)
        (hi d b' (by simp) (by simp) hdb') (hi d a (by simp) (by simp) hda)
        (hi c b' (by simp) (by simp) (Ne.symm hb'c)) (hi c a (by simp) (by simp) (Ne.symm hac))
        (hi b' a (by simp) (by simp) (Ne.symm hab'))) ?_
      exact nws4_of_planar_quad hβ hα (by rw [add_comm]; exact hαβ) (by rw [hb']; abel)
        (hi d c (by simp) (by simp) hdc)
    · intro m hm
      rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      simp only [quad_0, quad_1, quad_3]
      rcases mem_insert.mp hm with hm | hm
      · rw [hm]
        exact ⟨b, β₂, α₂ + β₂ - 1, Or.inr ⟨rfl, mul_neg_of_pos_of_neg (sub_pos.mpr hαβ₂)
          (by norm_num)⟩, hβ₂, hβ₂1, (sub_pos.mpr hαβ₂).ne', Or.inl hma'⟩
      · rw [mem_singleton.mp hm]
        refine ⟨b, 1 - α₁, α₁ + β₁ - 1, Or.inr ⟨rfl, mul_neg_of_pos_of_neg (sub_pos.mpr hαβ₁)
          (by norm_num)⟩, sub_pos.mpr hα₁1, by linarith only [hα₁], (sub_pos.mpr hαβ₁).ne',
          Or.inr ?_⟩
        rw [hmc']; module
  · -- counterclockwise `d, a, b', c`
    refine isRupert_of_edgeView V {a', c'} u hu (k := 4) (by norm_num) (quad d a b' c) 0 b (-1)
      (by simp [V]) (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add, u]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
      exacts [⟨hda', hdc'⟩, ⟨haa', hac'⟩, ⟨Ne.symm ha'b', hb'c'⟩, ⟨Ne.symm ha'c, hcc'⟩]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [T1]; positivity
      · exact hDp
      · rw [T3]; positivity
      · rw [T4]; positivity
      · rw [T5]; positivity
      · rw [T6]; positivity
      · rw [T7]; exact hDp
      · rw [T8]; positivity
    · intro z hz hzM hzw hzx
      exact (hrestV (quad d a b' c) (fun j => by
        rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3])
        (fun z hz => by
          rcases hz with h | h | h | h
          exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]) z hz hzM hzw hzx).elim
    · rw [quad_inner]
      refine isCyclicUnimodal_of_NWS4 (quad_injective (hi d a (by simp) (by simp) hda)
        (hi d b' (by simp) (by simp) hdb') (hi d c (by simp) (by simp) hdc)
        (hi a b' (by simp) (by simp) hab') (hi a c (by simp) (by simp) hac)
        (hi b' c (by simp) (by simp) hb'c)) ?_
      exact hd.Qac_nws4 u (hi d a (by simp) (by simp) hda)
    · intro m hm
      rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      simp only [quad_0, quad_1, quad_3]
      rcases mem_insert.mp hm with hm | hm
      · rw [hm]
        refine ⟨b, 1 - β₂, α₂ + β₂ - 1, Or.inr ⟨rfl, mul_neg_of_pos_of_neg (sub_pos.mpr hαβ₂)
          (by norm_num)⟩, sub_pos.mpr hβ₂1, by linarith only [hβ₂], (sub_pos.mpr hαβ₂).ne',
          Or.inr ?_⟩
        rw [hma']; module
      · rw [mem_singleton.mp hm]
        exact ⟨b, α₁, α₁ + β₁ - 1, Or.inr ⟨rfl, mul_neg_of_pos_of_neg (sub_pos.mpr hαβ₁)
          (by norm_num)⟩, hα₁, hα₁1, (sub_pos.mpr hαβ₁).ne', Or.inl hmc'⟩

end Minimality

end
