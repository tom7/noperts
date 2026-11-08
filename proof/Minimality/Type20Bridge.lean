module

public import Minimality.CaseC20Bridge
public import Minimality.Type20SilB

@[expose] public section

/-!
# Type 20: reusable bridge from frame coordinates to silhouette leaves

Tools used by the type 20 silhouette cells that are stated in `Frame20` coordinates (see
`Type20IMA`) and reusable for other type 20 items:
* `RobUni` helpers: shifting depths by a constant, 4-cycles, strict 5-cycle depth orders.
* The bridge from a general `F : Frame20 x`, a facet and a view in frame coordinates to facet
  values and depths (`facet_coords`, `dep_0` .. `dep_6`, `cross_coords`).
* `s0x_seg_rupert_tilt`: the segment leaf with a hand-chosen tilt, for views where a facet is
  edge-on without containing an endpoint (type-free).
* `realizesFaces_rperm`: the relabelling `R` preserves the faces of type 20.
-/

section

/-!
# I_MA: `RobUni` helpers (shift by a constant, 4-cycles, strict 5-cycle orders)
-/

open Minimality Minimality.H21 Finset

namespace Minimality.H20S

/-- Adding the same constant to all depths does not change robust unimodality. -/
theorem robUni_add_const {k : ℕ} {z : ZMod k → ℝ} (h : RobUni z) (a : ℝ) :
    RobUni (fun i => a + z i) := by
  intro B b c d hb hbc hcd hd hh
  exact h B b c d hb hbc hcd hd (by simp only at hh; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2])

/-- On a 4-cycle, `RobUni` is: neither the odd pair nor the even pair is weakly below the other. -/
theorem robUni4 {z : ZMod 4 → ℝ}
    (h1 : ¬ (z 1 ≤ z 0 ∧ z 1 ≤ z 2 ∧ z 3 ≤ z 0 ∧ z 3 ≤ z 2))
    (h2 : ¬ (z 0 ≤ z 1 ∧ z 0 ≤ z 3 ∧ z 2 ≤ z 1 ∧ z 2 ≤ z 3)) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hb1 : b = 1 := by omega
  have hc2 : c = 2 := by omega
  have hd3 : d = 3 := by omega
  subst hb1 hc2 hd3
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by revert B; decide
  rcases hB with rfl | rfl | rfl | rfl
  · exact fun h => h1 h
  · exact fun h => h2 ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
  · exact fun h => h1 ⟨h.2.2.2, h.2.2.1, h.2.1, h.1⟩
  · exact fun h => h2 ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- On a 4-cycle, `RobUni` is invariant under negating all depths. -/
theorem robUni4_neg {z : ZMod 4 → ℝ} (h : RobUni z) : RobUni (fun i => - z i) := by
  have h1 := h 0 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := h 1 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e : ∀ a b : ZMod 4, a = b → z a = z b := fun a b h => by rw [h]
  refine robUni4 ?_ ?_
  · rintro ⟨a, b, c, d⟩
    apply h2
    have e1 : (1:ZMod 4) + ((1:ℕ):ZMod 4) = 2 := by decide
    have e2 : (1:ZMod 4) + ((2:ℕ):ZMod 4) = 3 := by decide
    have e3 : (1:ZMod 4) + ((3:ℕ):ZMod 4) = 0 := by decide
    rw [e1, e2, e3]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c, d⟩
    apply h1
    have e1 : (0:ZMod 4) + ((1:ℕ):ZMod 4) = 1 := by decide
    have e2 : (0:ZMod 4) + ((2:ℕ):ZMod 4) = 2 := by decide
    have e3 : (0:ZMod 4) + ((3:ℕ):ZMod 4) = 3 := by decide
    rw [e1, e2, e3]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Sums in `ZMod 5`, for rewriting cycle positions. -/
theorem zmod5_sums : ((0:ZMod 5) + 1 = 1) ∧
    ((0:ZMod 5) + 2 = 2) ∧
    ((0:ZMod 5) + 3 = 3) ∧
    ((0:ZMod 5) + 4 = 4) ∧
    ((1:ZMod 5) + 1 = 2) ∧
    ((1:ZMod 5) + 2 = 3) ∧
    ((1:ZMod 5) + 3 = 4) ∧
    ((1:ZMod 5) + 4 = 0) ∧
    ((2:ZMod 5) + 1 = 3) ∧
    ((2:ZMod 5) + 2 = 4) ∧
    ((2:ZMod 5) + 3 = 0) ∧
    ((2:ZMod 5) + 4 = 1) ∧
    ((3:ZMod 5) + 1 = 4) ∧
    ((3:ZMod 5) + 2 = 0) ∧
    ((3:ZMod 5) + 3 = 1) ∧
    ((3:ZMod 5) + 4 = 2) ∧
    ((4:ZMod 5) + 1 = 0) ∧
    ((4:ZMod 5) + 2 = 1) ∧
    ((4:ZMod 5) + 3 = 2) ∧
    ((4:ZMod 5) + 4 = 3) := by decide

/-- On a 5-cycle with `z4 < z3 < z2 < z0 < z1` (peak at 1, valley at 4), `RobUni` holds. -/
theorem robUni5_a {z : ZMod 5 → ℝ} (h43 : z 4 < z 3) (h32 : z 3 < z 2) (h20 : z 2 < z 0)
    (h01 : z 0 < z 1) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hb4 : b < 5 := by omega
  have hc4 : c < 5 := by omega
  obtain ⟨e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44⟩ := zmod5_sums
  interval_cases b <;> interval_cases c <;> (try omega) <;> interval_cases d <;> (try omega) <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · rintro ⟨a1, a2, a3, a4⟩
    revert a1 a2 a3 a4
    simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44]
    intro a1 a2 a3 a4
    linarith

/-- The same on a 5-cycle with the opposite order `z1 < z0 < z2 < z3 < z4`. -/
theorem robUni5_b {z : ZMod 5 → ℝ} (h43 : z 3 < z 4) (h32 : z 2 < z 3) (h20 : z 0 < z 2)
    (h01 : z 1 < z 0) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hb4 : b < 5 := by omega
  have hc4 : c < 5 := by omega
  obtain ⟨e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44⟩ := zmod5_sums
  interval_cases b <;> interval_cases c <;> (try omega) <;> interval_cases d <;> (try omega) <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · rintro ⟨a1, a2, a3, a4⟩
    revert a1 a2 a3 a4
    simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44]
    intro a1 a2 a3 a4
    linarith

end Minimality.H20S
end

section

/-!
# I_MA: the bridge from `Frame20` coordinates to facet values and depths

Everything is stated for a general `F : Frame20 x`, a general facet (value function `f`, normal `N`)
and a general view `q` in frame coordinates (the view vector is `fvC q = q.x u1 + q.y u2 + q.z e`
with `u1 = x 1 - x 5`, `u2 = x 6 - x 5`), so that other type 20 items can reuse it.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- A facet normal applied to the view `q` is its coordinate form: `q.x α + q.y β + q.z δ`
with `α = ⟪N,u1⟫`, `β = ⟪N,u2⟫`, `δ = ⟪N,e⟫`. -/
lemma inner_fvC_right (N : ℝ³) (q : C3) :
    ⟪N, F.toFrame7.fvC q⟫ =
      q.x * ⟪N, x 1 - x 5⟫ + q.y * ⟪N, x 6 - x 5⟫ + q.z * ⟪N, F.e⟫ := by
  simp only [Frame7.fvC, toFrame7, inner_add_right, real_inner_smul_right]

/-- The values of a facet function at the four off-axis points, in terms of its values at
`x 1`, `x 5`, `x 6` and its normal's `e`-component `δ = ⟪N,e⟫`. -/
lemma facet_coords (f : ℝ³ → ℝ) (N : ℝ³) (hN : ∀ y z, f y - f z = ⟪N, y - z⟫) :
    f (x 0) - f (x 5) = F.S.tp * (f (x 1) - f (x 5)) + F.S.hp * ⟪N, F.e⟫ ∧
    f (x 3) - f (x 5) = F.S.tm * (f (x 1) - f (x 5)) - F.S.hm * ⟪N, F.e⟫ ∧
    f (x 2) - f (x 5) = F.S.sp * (f (x 6) - f (x 5)) + F.S.kp * ⟪N, F.e⟫ ∧
    f (x 4) - f (x 5) = F.S.sm * (f (x 6) - f (x 5)) - F.S.km * ⟪N, F.e⟫ := by
  have h0 : x 0 - x 5 = F.S.tp • (x 1 - x 5) + F.S.hp • F.e := by rw [F.x0_eq]; abel
  have h3 : x 3 - x 5 = F.S.tm • (x 1 - x 5) + (-F.S.hm) • F.e := by
    rw [F.x3_eq]; module
  have h2 : x 2 - x 5 = F.S.sp • (x 6 - x 5) + F.S.kp • F.e := by rw [F.x2_eq]; abel
  have h4 : x 4 - x 5 = F.S.sm • (x 6 - x 5) + (-F.S.km) • F.e := by
    rw [F.x4_eq]; module
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hN, h0, hN (x 1) (x 5)]; simp only [inner_add_right, real_inner_smul_right]
  · rw [hN, h3, hN (x 1) (x 5)]; simp only [inner_add_right, real_inner_smul_right]; ring
  · rw [hN, h2, hN (x 6) (x 5)]; simp only [inner_add_right, real_inner_smul_right]
  · rw [hN, h4, hN (x 6) (x 5)]; simp only [inner_add_right, real_inner_smul_right]; ring

/-- The depth of `x j` along the view `fvC q` is its value at `x 5` plus the Gram-form depth
`dep q j = x_j^T G q` of the frame (`x 5` is the origin of the frame). -/
lemma inner_x_fvC (q : C3) (j : Fin 7) :
    ⟪x j, F.toFrame7.fvC q⟫ = ⟪x 5, F.toFrame7.fvC q⟫ + F.dep q j :=
  F.toFrame7.inner_x_fvC j q

/-! ### The depths as explicit polynomials in `a11 a12 a22 gg` and the shape -/

lemma dep_0 (q : C3) : F.dep q 0 =
    F.a11 * (F.S.tp * q.x) + F.a12 * (F.S.tp * q.y) + F.gg * (F.S.hp * q.z) := by
  simp only [dep, GG_eq, ptC_0]; ring
lemma dep_1 (q : C3) : F.dep q 1 = F.a11 * q.x + F.a12 * q.y := by
  simp only [dep, GG_eq, ptC_1]; ring
lemma dep_2 (q : C3) : F.dep q 2 =
    F.a12 * (F.S.sp * q.x) + F.a22 * (F.S.sp * q.y) + F.gg * (F.S.kp * q.z) := by
  simp only [dep, GG_eq, ptC_2]; ring
lemma dep_3 (q : C3) : F.dep q 3 =
    F.a11 * (F.S.tm * q.x) + F.a12 * (F.S.tm * q.y) - F.gg * (F.S.hm * q.z) := by
  simp only [dep, GG_eq, ptC_3]; ring
lemma dep_4 (q : C3) : F.dep q 4 =
    F.a12 * (F.S.sm * q.x) + F.a22 * (F.S.sm * q.y) - F.gg * (F.S.km * q.z) := by
  simp only [dep, GG_eq, ptC_4]; ring
lemma dep_5 (q : C3) : F.dep q 5 = 0 := by
  simp only [dep, GG_eq, ptC_5]; ring
lemma dep_6 (q : C3) : F.dep q 6 = F.a12 * q.x + F.a22 * q.y := by
  simp only [dep, GG_eq, ptC_6]; ring

/-! ### Line views: the cross product of two facet normals in frame coordinates -/

end Frame20

/-- Binet-Cauchy for the cross product on `ℝ³`. -/
lemma inner_cross_cross (a b c d : ℝ³) :
    ⟪cross a b, cross c d⟫ = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  simp only [Classify.inner_eq3, (Classify.cross_apply _ _).1, (Classify.cross_apply _ _).2.1,
    (Classify.cross_apply _ _).2.2]
  ring

namespace Frame20
variable {x : Fin 7 → ℝ³} (F : Frame20 x)

/-- The cross product of two vectors is nonzero when their pairings with `u1, u2` are not
proportional in the Binet-Cauchy sense. -/
lemma cross_ne_zero (a b : ℝ³)
    (h : ⟪a, x 6 - x 5⟫ * ⟪b, x 1 - x 5⟫ ≠ ⟪a, x 1 - x 5⟫ * ⟪b, x 6 - x 5⟫) :
    cross a b ≠ 0 := by
  intro h0
  have := inner_cross_cross a b (x 6 - x 5) (x 1 - x 5)
  rw [h0] at this
  simp only [inner_zero_left] at this
  apply h
  have c1 : ⟪b, x 6 - x 5⟫ = ⟪x 6 - x 5, b⟫ := real_inner_comm _ _
  linarith [mul_comm ⟪b, x 6 - x 5⟫ ⟪a, x 1 - x 5⟫]

/-- A cross product `cross a b` is a frame vector `fvC q` orthogonal to `a` and `b`. -/
lemma cross_coords (a b : ℝ³) : ∃ q : C3, cross a b = F.toFrame7.fvC q ∧
    q.x * ⟪a, x 1 - x 5⟫ + q.y * ⟪a, x 6 - x 5⟫ + q.z * ⟪a, F.e⟫ = 0 ∧
    q.x * ⟪b, x 1 - x 5⟫ + q.y * ⟪b, x 6 - x 5⟫ + q.z * ⟪b, F.e⟫ = 0 := by
  obtain ⟨q, hq⟩ := F.toFrame7.decomp (cross a b)
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← F.inner_fvC_right, ← hq, real_inner_comm]; exact inner_cross_left a b
  · rw [← F.inner_fvC_right, ← hq, real_inner_comm]; exact inner_cross_right a b

end Frame20
end Minimality.CaseC20
end

section

/-!
# I_MA: the special position `D1 = 0` (tilted segment leaf `s05:13526[BvCvG^]`)

A segment view `x j - x i` where a facet is edge-on without containing an endpoint (here `G`, at
`D1 = 0`): a tilt `v` is supplied by hand.
-/

open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.H20S

/-- On a 5-cycle with the valley at 0 and `z0 < z4 < z3 < z2`, `z0 < z1` (peak at 1 or 2),
`RobUni` holds. -/
theorem robUni5_c {z : ZMod 5 → ℝ} (h04 : z 0 < z 4) (h43 : z 4 < z 3) (h32 : z 3 < z 2)
    (h01 : z 0 < z 1) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hb4 : b < 5 := by omega
  have hc4 : c < 5 := by omega
  obtain ⟨e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44⟩ := zmod5_sums
  interval_cases b <;> interval_cases c <;> (try omega) <;> interval_cases d <;> (try omega) <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · rintro ⟨a1, a2, a3, a4⟩
    revert a1 a2 a3 a4
    simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44]
    intro a1 a2 a3 a4
    linarith

end Minimality.H20S

namespace Minimality.H21
variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- **Segment leaf with a hand-chosen tilt** (type-free, reusable).  For the view `x j - x i`, if the
facings of all facets at `(x j - x i, v)` follow the pattern in the lex sense (so facets that are
edge-on at the view, even ones containing neither endpoint, are decided by the tilt `v`), the cycle is
a silhouette of the pattern and the depths are robustly unimodal, then the point set is Rupert.
This replaces `s0x_seg_rupert` when an edge-on facet does not contain both endpoints. -/
theorem s0x_seg_rupert_tilt {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {i j : Fin n} {pat : Fin m → Bool} {c : ZMod k → Fin n} (hij : i ≠ j) (hk : 3 ≤ k)
    (hc : Function.Injective c) (hcyc : S0xCycOK S c pat) (v : ℝ³)
    (hfac : S0xFacOK F pat (x j - x i) v) (hU : RobUni (fun a : ZMod k => ⟪x (c a), x j - x i⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨D⟩ := s0x_silL (k := k) F hcyc hfac
  have hu0 : x j - x i ≠ 0 := fun h => hij (hx (sub_eq_zero.1 h)).symm
  exact s0x_sil_isRupert_lex hk hx hc hu0 D hU

end Minimality.H21
end

section
open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace
namespace Minimality.CaseC20

set_option maxRecDepth 100000 in
/-- The relabelling `R` maps each face of type 20 to a face of type 20. -/
lemma rperm_faces : ∀ f ∈ sevenTypeFaces 19, f.image rperm ∈ sevenTypeFaces 19 := by decide

/-- If `x` realizes the faces of type 20, so does the relabelled point set `x ∘ R`. -/
lemma realizesFaces_rperm {x : Fin 7 → ℝ³} (hR : RealizesFaces x (sevenTypeFaces 19)) :
    RealizesFaces (x ∘ rperm) (sevenTypeFaces 19) := by
  intro f hf
  obtain ⟨φ, hφ⟩ := hR (f.image rperm) (rperm_faces f hf)
  refine ⟨φ, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · exact (hφ (rperm i)).1 (Finset.mem_image_of_mem _ hi)
  · refine (hφ (rperm i)).2 fun h => hi ?_
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 h
    rwa [rperm_bijective.1 hji] at hj
end Minimality.CaseC20
end

