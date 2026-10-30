module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.SCk
public import Minimality.Type08S.SCn

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W5

variable {e1 e2 e3 : ℝ³}

/-- An affine function with gradient `N` in frame coordinates about `o`. -/
theorem fcoord (hF : Fr e1 e2 e3) {f : ℝ³ → ℝ} {N : ℝ³} (hN : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (o y : ℝ³) :
    f y - f o = ⟪N, e1⟫ * ⟪y - o, e1⟫ + ⟪N, e2⟫ * ⟪y - o, e2⟫ + ⟪N, e3⟫ * ⟪y - o, e3⟫ := by
  rw [hN]
  have h := hF.expand (y - o)
  conv_lhs => rw [h]
  simp only [inner_add_right, real_inner_smul_right]
  ring

/-- **Plane lemma.**  If `f` vanishes at `o` and at two points `p1 p2` of the plane `Y = 0`
(independent there), then `f = B * Y` with `B < 0` as soon as one point `q` of `Y > 0` has `f q < 0`. -/
theorem plane_Y (hF : Fr e1 e2 e3) {f : ℝ³ → ℝ} {N : ℝ³} (hN : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {o p1 p2 q : ℝ³} (ho : f o = 0) (h1 : f p1 = 0) (h2 : f p2 = 0)
    (hY1 : ⟪p1 - o, e2⟫ = 0) (hY2 : ⟪p2 - o, e2⟫ = 0)
    (hdet : ⟪p1 - o, e1⟫ * ⟪p2 - o, e3⟫ - ⟪p2 - o, e1⟫ * ⟪p1 - o, e3⟫ ≠ 0)
    (hq : f q < 0) (hYq : 0 < ⟪q - o, e2⟫) :
    ∃ B : ℝ, B < 0 ∧ ∀ y, f y = B * ⟪y - o, e2⟫ := by
  have c1 := fcoord hF hN o p1
  have c2 := fcoord hF hN o p2
  rw [h1, ho, hY1] at c1
  rw [h2, ho, hY2] at c2
  have hA : ⟪N, e1⟫ = 0 := by
    have : ⟪N, e1⟫ * (⟪p1 - o, e1⟫ * ⟪p2 - o, e3⟫ - ⟪p2 - o, e1⟫ * ⟪p1 - o, e3⟫) = 0 := by
      linear_combination ⟪p2 - o, e3⟫ * (-c1) - ⟪p1 - o, e3⟫ * (-c2)
    exact (mul_eq_zero.mp this).resolve_right hdet
  have hC : ⟪N, e3⟫ = 0 := by
    have : ⟪N, e3⟫ * (⟪p1 - o, e1⟫ * ⟪p2 - o, e3⟫ - ⟪p2 - o, e1⟫ * ⟪p1 - o, e3⟫) = 0 := by
      linear_combination ⟪p1 - o, e1⟫ * (-c2) - ⟪p2 - o, e1⟫ * (-c1)
    exact (mul_eq_zero.mp this).resolve_right hdet
  have hf : ∀ y, f y = ⟪N, e2⟫ * ⟪y - o, e2⟫ := by
    intro y
    have := fcoord hF hN o y
    rw [ho, hA, hC] at this
    linarith
  refine ⟨⟪N, e2⟫, ?_, hf⟩
  have := hf q
  rw [this] at hq
  by_contra hB
  push_neg at hB
  nlinarith

/-- **Side lemma** (a facet through the F-side `xp f` seen in the plane `Y = 0`): `x` and `p`
on the same (negative) side forces `κ (L zp - zf Xp) > 0`. -/
theorem side_pos (hF : Fr e1 e2 e3) {f : ℝ³ → ℝ} {N : ℝ³} (hN : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {xp x fp p : ℝ³} {κ : ℝ} (hxp : f xp = 0) (hf : f fp = 0) (hx : f x < 0) (hp : f p < 0)
    (hxe : x - xp = κ • e3) (hfY : ⟪fp - xp, e2⟫ = 0) (hpY : ⟪p - xp, e2⟫ = 0)
    (hL : 0 < ⟪fp - xp, e1⟫) :
    0 < κ * (⟪fp - xp, e1⟫ * ⟪p - xp, e3⟫ - ⟪fp - xp, e3⟫ * ⟪p - xp, e1⟫) := by
  have cf := fcoord hF hN xp fp
  have cx := fcoord hF hN xp x
  have cp := fcoord hF hN xp p
  have n31 : ⟪e3, e1⟫ = 0 := by rw [real_inner_comm]; exact hF.n13
  have n32 : ⟪e3, e2⟫ = 0 := by rw [real_inner_comm]; exact hF.n23
  have e1x : ⟪x - xp, e1⟫ = 0 := by rw [hxe, real_inner_smul_left, n31]; ring
  have e2x : ⟪x - xp, e2⟫ = 0 := by rw [hxe, real_inner_smul_left, n32]; ring
  have e3x : ⟪x - xp, e3⟫ = κ := by rw [hxe, real_inner_smul_left, hF.n33]; ring
  rw [hf, hxp, hfY] at cf
  rw [hxp, e1x, e2x, e3x] at cx
  rw [hpY, hxp] at cp
  have hCk : ⟪N, e3⟫ * κ < 0 := by linarith
  set L := ⟪fp - xp, e1⟫
  set S := L * ⟪p - xp, e3⟫ - ⟪fp - xp, e3⟫ * ⟪p - xp, e1⟫ with hS
  have hCS : ⟪N, e3⟫ * S < 0 := by
    have : ⟪N, e3⟫ * S = L * (f p - 0) := by
      rw [hS]; linear_combination (-L) * cp + ⟪p - xp, e1⟫ * cf
    nlinarith
  have hC0 : ⟪N, e3⟫ ≠ 0 := by intro h; rw [h] at hCk; simp at hCk
  have : 0 < (⟪N, e3⟫ * κ) * (⟪N, e3⟫ * S) := mul_pos_of_neg_of_neg hCk hCS
  have h2 : 0 < ⟪N, e3⟫ ^ 2 * (κ * S) := by nlinarith
  exact (pos_of_mul_pos_right h2 (sq_nonneg _)) 

/-- **Chord lemma** (G-side): a facet through `x` and `g`, with `xp` and `q` on its negative side,
`q` over the screen point `lam * g`: `q` is on the `xp` side of the chord `x g`. -/
theorem chord_neg (hF : Fr e1 e2 e3) {f : ℝ³ → ℝ} {N : ℝ³} (hN : ∀ y z, f y - f z = ⟪N, y - z⟫)
    {xp x g q : ℝ³} {κ lam : ℝ} (hxe : x - xp = κ • e3) (hx : f x = 0) (hg : f g = 0)
    (hxp : f xp < 0) (hq : f q < 0)
    (hq1 : ⟪q - xp, e1⟫ = lam * ⟪g - xp, e1⟫) (hq2 : ⟪q - xp, e2⟫ = lam * ⟪g - xp, e2⟫) :
    κ * (⟪q - xp, e3⟫ - ((1 - lam) * ⟪x - xp, e3⟫ + lam * ⟪g - xp, e3⟫)) < 0 := by
  have n31 : ⟪e3, e1⟫ = 0 := by rw [real_inner_comm]; exact hF.n13
  have n32 : ⟪e3, e2⟫ = 0 := by rw [real_inner_comm]; exact hF.n23
  have e1x : ⟪x - xp, e1⟫ = 0 := by rw [hxe, real_inner_smul_left, n31]; ring
  have e2x : ⟪x - xp, e2⟫ = 0 := by rw [hxe, real_inner_smul_left, n32]; ring
  have e3x : ⟪x - xp, e3⟫ = κ := by rw [hxe, real_inner_smul_left, hF.n33]; ring
  have cx := fcoord hF hN xp x
  have cg := fcoord hF hN xp g
  have cq := fcoord hF hN xp q
  rw [hx, e1x, e2x, e3x] at cx
  rw [hg] at cg
  rw [hq1, hq2] at cq
  rw [e3x]
  set C := ⟪N, e3⟫
  set Δ := ⟪q - xp, e3⟫ - ((1 - lam) * κ + lam * ⟪g - xp, e3⟫) with hΔ
  have hCk : 0 < C * κ := by linarith
  have hCΔ : C * Δ < 0 := by
    have : f q = C * Δ := by
      rw [hΔ]; linear_combination cq - lam * cg - (1 - lam) * cx
    linarith
  have h1 : C * κ * (C * Δ) < 0 := mul_neg_of_pos_of_neg hCk hCΔ
  have hC0 : C ≠ 0 := by intro h; rw [h] at hCk; simp at hCk
  have h2 : C ^ 2 * (κ * Δ) < 0 := by nlinarith
  by_contra hh
  push_neg at hh
  nlinarith [sq_nonneg C, mul_nonneg (sq_nonneg C) hh]

/-- Nondegeneracy determinants of a `Norm08w` shape, through the normal form. -/
theorem det_ne08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    det3 (c' - a') (c - a') (b - a') ≠ 0 ∧ det3 (b' - d) (b - d) (c - d) ≠ 0 ∧
    det3 (b' - b) (d - b) (c' - b) ≠ 0 := by
  obtain ⟨o, E1, E2, E3, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
  have key : ∀ i j k w : Fin 7, det3 (pts08 a a' b b' c c' d j - pts08 a a' b b' c c' d i)
      (pts08 a a' b b' c c' d k - pts08 a a' b b' c c' d i)
      (pts08 a a' b b' c c' d w - pts08 a a' b b' c c' d i) = det3 E1 E2 E3 * fc08 θ i j k w := by
    intro i j k w; rw [hpts]; exact det3_nf08 o E1 E2 E3 θ i j k w
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := facts08w θ hθ.1 hθ.2.1 hθ.2.2
  have q9 := hθ.1 8 (by decide) (by decide) (by decide)
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at q9
  refine ⟨?_, ?_, ?_⟩
  · have h := key 1 5 4 2
    have e : fc08 θ 1 5 4 2 = θ 0 * (θ 4 + θ 5 - 1) := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
    simp only [pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    rw [e] at h; rw [h]
    exact mul_ne_zero hE (mul_pos p0 q9).ne'
  · have h := key 6 3 2 4
    have e : fc08 θ 6 3 2 4 = θ 2 := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
    simp only [pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    rw [e] at h; rw [h]
    exact mul_ne_zero hE p2.ne'
  · have h := key 2 3 6 5
    have e : fc08 θ 2 3 6 5 = θ 3 * θ 0 := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
    simp only [pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    rw [e] at h; rw [h]
    exact mul_ne_zero hE (mul_pos p3 p0).ne'

theorem kap_coords (hF : Fr e1 e2 e3) {x xp : ℝ³} {κ : ℝ} (h : x - xp = κ • e3) :
    ⟪x - xp, e1⟫ = 0 ∧ ⟪x - xp, e2⟫ = 0 ∧ ⟪x - xp, e3⟫ = κ := by
  have n31 : ⟪e3, e1⟫ = 0 := by rw [real_inner_comm]; exact hF.n13
  have n32 : ⟪e3, e2⟫ = 0 := by rw [real_inner_comm]; exact hF.n23
  refine ⟨?_, ?_, ?_⟩
  · rw [h, real_inner_smul_left, n31]; ring
  · rw [h, real_inner_smul_left, n32]; ring
  · rw [h, real_inner_smul_left, hF.n33]; ring

theorem pos_of_neg_mul {B Y : ℝ} (hB : B < 0) (h : B * Y < 0) : 0 < Y := by
  by_contra hh; push_neg at hh; nlinarith

theorem zero_of_neg_mul {B Y : ℝ} (hB : B < 0) (h : B * Y = 0) : Y = 0 :=
  (mul_eq_zero.mp h).resolve_left hB.ne

/-- Top-vertex class without the choice of `σ`: class (c) or class (d). -/
def TopP (zp L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  ClassC5 L zx zf Xr Yr zr Xg Yg zg ∨ ClassD5 zp L zx zf Xr Yr zr Xg Yg zg

/-- Choose `σ`: `κ` for class (c), `1` for class (d) (where `κ = zx > 0`). -/
theorem choose_sigma {L zx zf Xr Yr zr Xg Yg zg κ S : ℝ} (hzx : zx = κ) (hκ : κ ≠ 0)
    (hS : 0 < κ * S) (h : TopP 0 L zx zf Xr Yr zr Xg Yg zg) :
    ∃ σ : ℝ, 0 < σ * (zx - 0) ∧ 0 < σ * S ∧ Top5 σ 0 L zx zf Xr Yr zr Xg Yg zg := by
  rcases h with h | ⟨σ0, m, Xx, z0, hYY, hXrg, hzz, rest⟩
  · exact ⟨κ, by rw [hzx]; nlinarith [sq_pos_of_ne_zero hκ], hS, Or.inl h⟩
  · have hκp : 0 < κ := by rw [← hzx]; linarith
    refine ⟨1, by linarith, ?_, Or.inr ⟨rfl, σ0, m, Xx, z0, hYY, hXrg, hzz, rest⟩⟩
    rw [one_mul]; exact (mul_pos_iff_of_pos_left hκp).mp hS

/-- The part of the N2 `K_c` frame data that is NOT a consequence of `Norm08w`: strict convexity of
the screen quadrilateral `(x̄, f̄, r̄, ḡ)` at `r` and `g`, the class (c) package, the F-middle `d`
over the open chord, and `a` inside the screen triangle `(x̄, f̄, ḡ)`. -/
def N2Cls (L zx zf Xr Yr zr Xg Yg zg Xd Xa Ya : ℝ) : Prop :=
  0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yg * Xr - Xg * Yr ∧
  TopP 0 L zx zf Xr Yr zr Xg Yg zg ∧ 0 < Xd ∧ Xd < L ∧
  0 < (Xg - L) * Ya - Yg * (Xa - L) ∧ 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)

/-- **Explicit class-(c) predicate for N2 `K_c`** (view `c - a'`): in the canonical oriented frame
(`c - a' = κ e3`, `b - a'` edge-on with positive `e1`-coordinate, `c' - a'` with positive
`e2`-coordinate), the shadow numbers satisfy `N2Cls`.  Everything else of `SCfN2` is derived. -/
def ClsN2 (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ c - a' = κ • e3 ∧ ⟪b - a', e2⟫ = 0 ∧
    0 < ⟪b - a', e1⟫ ∧ 0 < ⟪c' - a', e2⟫ ∧
    N2Cls ⟪b - a', e1⟫ ⟪c - a', e3⟫ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫
      ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ ⟪d - a', e1⟫ ⟪a - a', e1⟫ ⟪a - a', e2⟫

theorem SCfN2_of_cls {a a' b b' c c' d u : ℝ³} (N : Norm08w a a' b b' c c' d)
    (h : ClsN2 a a' b b' c c' d) (hu : u = c - a' ∨ u = -(c - a')) : SCfN2' u a a' b b' c c' d := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hce, hb2, hL, hYr0, hcr, hcg, hcl, hX0, hXL, hc2, hc3⟩ := h
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hc01, hc02, hc03⟩ := kap_coords hF hce
  have hdet : ⟪b - a', e1⟫ * ⟪c - a', e3⟫ - ⟪c - a', e1⟫ * ⟪b - a', e3⟫ ≠ 0 := by
    rw [hc01, hc03]; simpa using ⟨hL.ne', hκ⟩
  have hpl := plane_Y hF N.F.a'bc.hN N.F.a'bc.hP N.F.a'bc.hQ N.F.a'bc.hR hb2 hc02 hdet
    (N.F.a'bc.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) hYr0
  obtain ⟨B, hB, hfB⟩ := hpl
  have hYd : ⟪d - a', e2⟫ = 0 := zero_of_neg_mul hB (by rw [← hfB, N.hd.a'bc])
  have hYa : 0 < ⟪a - a', e2⟫ :=
    pos_of_neg_mul hB (by rw [← hfB]; exact N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
  have hYg : 0 < ⟪b' - a', e2⟫ :=
    pos_of_neg_mul hB (by rw [← hfB]; exact N.F.a'bc.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
  have hside := side_pos hF N.F.a'bc'.hN (xp := a') (x := c) (fp := b) (p := d) (κ := κ)
    N.F.a'bc'.hP N.F.a'bc'.hQ (N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) N.hd.a'bc'
    hce hb2 hYd hL
  have hκ' : ∃ κ' : ℝ, κ' ≠ 0 ∧ u = κ' • e3 := by
    rcases hu with hu | hu
    · exact ⟨κ, hκ, by rw [hu, hce]⟩
    · exact ⟨-κ, neg_ne_zero.mpr hκ, by rw [hu, hce, neg_smul]⟩
  obtain ⟨κ', hκ'0, hκ'u⟩ := hκ'
  obtain ⟨σ, hσ1, hσ2, hTop⟩ := choose_sigma hc03 hκ (by simpa using hside) hcl
  refine SCfN2'_of_frame hF hκ'0 hκ'u σ ?_ hc01 hc02 hb2 hYd
  refine ⟨hL, ?_, hcr, hYr0, hYg, hcg, hTop, hX0, hXL, ?_, ?_, ?_, hc2, hc3⟩
  · simpa using hσ1
  · simpa using hσ2
  · exact mul_pos hL hYg
  · exact mul_pos hL hYa

theorem frame_N2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ c - a' = κ • e3 ∧ ⟪b - a', e2⟫ = 0 ∧
      0 < ⟪b - a', e1⟫ ∧ 0 < ⟪c' - a', e2⟫ := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩ := frame_ex_pos (det_ne08 N).1
  exact ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩

theorem sub_eq_pc (hF : Fr e1 e2 e3) (xp q : ℝ³) :
    q - xp = pc e1 e2 e3 ⟪q - xp, e1⟫ ⟪q - xp, e2⟫ ⟪q - xp, e3⟫ := by
  rw [pc]; exact hF.expand _

/-- The part of the T4 frame data (`K_b`, `K_2`) not implied by `Norm08w`. -/
def T4Cls (L zx zf Xr Yr zr Xg Yg zg Xd lam : ℝ) : Prop :=
  0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yg * Xr - Xg * Yr ∧
  TopP 0 L zx zf Xr Yr zr Xg Yg zg ∧ 0 < Xd ∧ Xd < L ∧ lam < 1

/-- **Explicit class-(c) predicate for a T4 closing** `(x', f, r, g, x)` with F-middle `p` and
G-middle `q`, in the canonical oriented frame at origin `x'` (`x - x' = κ e3`, `f - x'` edge-on with
positive `e1`-coordinate, `r - x'` with positive `e2`-coordinate); `lam = Y_q / Y_g`. -/
def ClsT4 (xp x f r g p q : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ x - xp = κ • e3 ∧ ⟪f - xp, e2⟫ = 0 ∧
    0 < ⟪f - xp, e1⟫ ∧ 0 < ⟪r - xp, e2⟫ ∧
    T4Cls ⟪f - xp, e1⟫ ⟪x - xp, e3⟫ ⟪f - xp, e3⟫ ⟪r - xp, e1⟫ ⟪r - xp, e2⟫ ⟪r - xp, e3⟫
      ⟪g - xp, e1⟫ ⟪g - xp, e2⟫ ⟪g - xp, e3⟫ ⟪p - xp, e1⟫ (⟪q - xp, e2⟫ / ⟪g - xp, e2⟫)

/-- **Generic T4 derivation**: from three facet functionals (the edge-on plane, the F-side facet, the
G-side chord facet) and the coplanarity of `q, g, x, x'`. -/
theorem SCfT4_of_cls {xp x f r g p q u : ℝ³}
    {fpl : ℝ³ → ℝ} {Npl : ℝ³} (hNpl : ∀ y z, fpl y - fpl z = ⟪Npl, y - z⟫)
    (pl_xp : fpl xp = 0) (pl_x : fpl x = 0) (pl_f : fpl f = 0) (pl_p : fpl p = 0)
    (pl_r : fpl r < 0) (pl_g : fpl g < 0) (pl_q : fpl q < 0)
    {fs : ℝ³ → ℝ} {Ns : ℝ³} (hNs : ∀ y z, fs y - fs z = ⟪Ns, y - z⟫)
    (s_xp : fs xp = 0) (s_f : fs f = 0) (s_x : fs x < 0) (s_p : fs p < 0)
    {fg : ℝ³ → ℝ} {Ng : ℝ³} (hNg : ∀ y z, fg y - fg z = ⟪Ng, y - z⟫)
    (g_x : fg x = 0) (g_g : fg g = 0) (g_xp : fg xp < 0) (g_q : fg q < 0)
    (hcop : det3 (q - xp) (g - xp) (x - xp) = 0)
    (h : ClsT4 xp x f r g p q) (hu : u = x - xp ∨ u = -(x - xp)) : SCfT4' u xp x f r g p q := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hxe, hf2, hL, hYr0, hcr, hcg, hcl, hX0, hXL, hlam⟩ := h
  obtain ⟨hx1, hx2, hx3⟩ := kap_coords hF hxe
  have hdet : ⟪f - xp, e1⟫ * ⟪x - xp, e3⟫ - ⟪x - xp, e1⟫ * ⟪f - xp, e3⟫ ≠ 0 := by
    rw [hx1, hx3]; simpa using ⟨hL.ne', hκ⟩
  obtain ⟨B, hB, hfB⟩ := plane_Y hF hNpl pl_xp pl_f pl_x hf2 hx2 hdet pl_r hYr0
  have hYp : ⟪p - xp, e2⟫ = 0 := zero_of_neg_mul hB (by rw [← hfB]; exact pl_p)
  have hYg : 0 < ⟪g - xp, e2⟫ := pos_of_neg_mul hB (by rw [← hfB]; exact pl_g)
  have hYq : 0 < ⟪q - xp, e2⟫ := pos_of_neg_mul hB (by rw [← hfB]; exact pl_q)
  have hside := side_pos hF hNs (xp := xp) (x := x) (fp := f) (p := p) (κ := κ) s_xp s_f s_x s_p
    hxe hf2 hYp hL
  -- coplanarity gives the screen position of q
  set lam := ⟪q - xp, e2⟫ / ⟪g - xp, e2⟫ with hlamdef
  have hq2 : ⟪q - xp, e2⟫ = lam * ⟪g - xp, e2⟫ := by rw [hlamdef]; field_simp
  have hq1 : ⟪q - xp, e1⟫ = lam * ⟪g - xp, e1⟫ := by
    have e := hcop
    rw [sub_eq_pc hF xp q, sub_eq_pc hF xp g, sub_eq_pc hF xp x, hx1, hx2, hx3, det3_pc hF] at e
    have : (⟪q - xp, e1⟫ * ⟪g - xp, e2⟫ - ⟪q - xp, e2⟫ * ⟪g - xp, e1⟫) * κ = 0 := by linarith
    have h0 := (mul_eq_zero.mp this).resolve_right hκ
    rw [hlamdef]; field_simp; linarith
  have hlam0 : 0 < lam := div_pos hYq hYg
  have hchord := chord_neg hF hNg (xp := xp) (x := x) (g := g) (q := q) (κ := κ) (lam := lam) hxe g_x g_g
    g_xp g_q hq1 hq2
  have hκ' : ∃ κ' : ℝ, κ' ≠ 0 ∧ u = κ' • e3 := by
    rcases hu with hu | hu
    · exact ⟨κ, hκ, by rw [hu, hxe]⟩
    · exact ⟨-κ, neg_ne_zero.mpr hκ, by rw [hu, hxe, neg_smul]⟩
  obtain ⟨κ', hκ'0, hκ'u⟩ := hκ'
  obtain ⟨σ, hσ1, hσ2, hTop⟩ := choose_sigma hx3 hκ (by simpa using hside) hcl
  have hσκ : 0 < σ * κ := by simpa [hx3] using hσ1
  refine SCfT4'_of_frame hF hκ'0 hκ'u σ lam ?_ hx1 hx2 hf2 hYp hq1 hq2
  refine ⟨hL, ?_, hcr, hYr0, hYg, hcg, hTop, hX0, hXL, ?_, hlam0, hlam, ?_⟩
  · simpa using hσ1
  · simpa using hσ2
  · -- chord: `κ * Δ < 0` and `σ * κ > 0` give `σ * Δ < 0` up to the positive factor
    have hk : 0 < κ * σ := by linarith
    have hs : 0 < κ * κ := mul_self_pos.mpr hκ
    set Δ := ⟪q - xp, e3⟫ - ((1 - lam) * ⟪x - xp, e3⟫ + lam * ⟪g - xp, e3⟫) with hΔ
    have h1 : κ * Δ < 0 := hchord
    by_contra hh; push_neg at hh
    have : 0 ≤ (σ * Δ) * (κ * κ) := mul_nonneg hh hs.le
    nlinarith [mul_pos hk hs]

theorem facet_cop08 {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) {w v : ℝ³}
    (hw : F.f w ≠ 0) (hv : F.f v = 0) : det3 (Q - P) (R - P) (v - P) = 0 := by
  have h := facet_prop08 F v w
  rw [hv, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hw

/-- **T4 `K_b`** (`x' = d`, `x = b`, `f = c`, `r = b'`, `g = c'`, F-middle `a'`, G-middle `a`). -/
theorem SCfT4_Kb_of_cls {a a' b b' c c' d u : ℝ³} (N : Norm08w a a' b b' c c' d)
    (h : ClsT4 d b c b' c' a' a) (hu : u = b - d ∨ u = -(b - d)) : SCfT4' u d b c b' c' a' a := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hc1 := facet_cop08 N.F.abc' (w := a') (v := d)
    (N.F.abc'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)).ne N.hd.abc'
  have hcop : det3 (a - d) (c' - d) (b - d) = 0 := by
    have e : det3 (a - d) (c' - d) (b - d) = det3 (b - a) (c' - a) (d - a) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact hc1
  exact SCfT4_of_cls N.F.a'bc.hN N.hd.a'bc N.F.a'bc.hQ N.F.a'bc.hR N.F.a'bc.hP
    (N.F.a'bc.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    (N.F.a'bc.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    (N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    N.F.ab'c.hN N.hd.ab'c N.F.ab'c.hR (N.F.ab'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    (N.F.ab'c.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    N.F.a'bc'.hN N.F.a'bc'.hQ N.F.a'bc'.hR N.hd.a'bc'
    (N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) hcop h hu

/-- **T4 `K_2`** (`x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`, F-middle `a`, G-middle `a'`). -/
theorem SCfT4_K2_of_cls {a a' b b' c c' d u : ℝ³} (N : Norm08w a a' b b' c c' d)
    (h : ClsT4 b d c' b' c a a') (hu : u = d - b ∨ u = -(d - b)) : SCfT4' u b d c' b' c a a' := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hc1 := facet_cop08 N.F.a'bc (w := a) (v := d)
    (N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)).ne N.hd.a'bc
  have hcop : det3 (a' - b) (c - b) (d - b) = 0 := by
    have e : det3 (a' - b) (c - b) (d - b) = - det3 (b - a') (c - a') (d - a') := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e, hc1, neg_zero]
  exact SCfT4_of_cls N.F.abc'.hN N.F.abc'.hQ N.hd.abc' N.F.abc'.hR N.F.abc'.hP
    (N.F.abc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    (N.F.abc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    (N.F.abc'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    N.F.a'bc'.hN N.F.a'bc'.hQ N.F.a'bc'.hR N.hd.a'bc'
    (N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    N.F.ab'c.hN N.hd.ab'c N.F.ab'c.hR (N.F.ab'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac))
    (N.F.ab'c.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) hcop h hu

theorem frame_Kb {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ b - d = κ • e3 ∧ ⟪c - d, e2⟫ = 0 ∧
      0 < ⟪c - d, e1⟫ ∧ 0 < ⟪b' - d, e2⟫ := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩ := frame_ex_pos (det_ne08 N).2.1
  exact ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩

theorem frame_K2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ d - b = κ • e3 ∧ ⟪c' - b, e2⟫ = 0 ∧
      0 < ⟪c' - b, e1⟫ ∧ 0 < ⟪b' - b, e2⟫ := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩ := frame_ex_pos (det_ne08 N).2.2
  exact ⟨e1, e2, e3, κ, hF, hκ, hu, hv2, hv1, hw2⟩

theorem view08_N2 (s : Bool) (y : Fin 7 → ℝ³) :
    (test08 0 s true).view y = y 4 - y 1 ∨ (test08 0 s true).view y = -(y 4 - y 1) := by
  cases s <;> simp [test08, grp08, ViewGroup.tests, LabTest.neg, LabTest.quad]

theorem view08_T4 (s j : Bool) (y : Fin 7 → ℝ³) :
    (test08 1 s j).view y = y 2 - y 6 ∨ (test08 1 s j).view y = -(y 2 - y 6) := by
  cases s <;> cases j <;> simp [test08, grp08, ViewGroup.tests, LabTest.neg, LabTest.quad]

/-- **Corrected single-circle class (c) clause.**  Differs from `SCcl` in the `K_2` disjunct: the
closing is `x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`, F-middle `a` (over the edge `b c'` of the
plane `abc'`), G-middle `a'` (over the side `c d` of the plane `a'bc`).  (The old disjunct
`SCfT4 u b d c b' c' a' a` is unsatisfiable on `Norm08w` shapes: `d` and `a'` lie on opposite sides
of the diagonal `bc` of the cap quadrilateral.) -/
def SCcl2 (a a' b b' c c' d : ℝ³) (t : Fin 3 × Bool × Bool) : Prop :=
  let u := (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)
  (t.1 = 0 ∧ t.2.2 = true ∧ SCfN2' u a a' b b' c c' d) ∨
  (t.1 = 1 ∧ t.2.2 = true ∧ SCfT4' u d b c b' c' a' a) ∨
  (t.1 = 1 ∧ t.2.2 = false ∧ SCfT4' u b d c' b' c a a')

/-- **Explicit class-(c) predicate** of the closing `t` (frame-free statement: canonical frame, then
`N2Cls`/`T4Cls` on the shadow numbers). -/
def ClassCt (a a' b b' c c' d : ℝ³) (t : Fin 3 × Bool × Bool) : Prop :=
  (t.1 = 0 ∧ t.2.2 = true ∧ ClsN2 a a' b b' c c' d) ∨
  (t.1 = 1 ∧ t.2.2 = true ∧ ClsT4 d b c b' c' a' a) ∨
  (t.1 = 1 ∧ t.2.2 = false ∧ ClsT4 b d c' b' c a a')

theorem SCcl2_of_ClassCt {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    {t : Fin 3 × Bool × Bool} (h : ClassCt a a' b b' c c' d t) : SCcl2 a a' b b' c c' d t := by
  obtain ⟨i, s, j⟩ := t
  rcases h with ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩
  · simp only at h1 h2; subst h1 h2
    left; refine ⟨rfl, rfl, SCfN2_of_cls N h ?_⟩
    have hp : pts08 a a' b b' c c' d 4 - pts08 a a' b b' c c' d 1 = c - a' := by simp [pts08]
    rcases view08_N2 s (pts08 a a' b b' c c' d) with h | h <;> rw [hp] at h
    exacts [Or.inl h, Or.inr h]
  · simp only at h1 h2; subst h1 h2
    right; left; refine ⟨rfl, rfl, SCfT4_Kb_of_cls N h ?_⟩
    have hp : pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6 = b - d := by simp [pts08]
    rcases view08_T4 s true (pts08 a a' b b' c c' d) with h | h <;> rw [hp] at h
    exacts [Or.inl h, Or.inr h]
  · simp only at h1 h2; subst h1 h2
    right; right; refine ⟨rfl, rfl, SCfT4_K2_of_cls N h ?_⟩
    have hp : pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6 = b - d := by simp [pts08]
    rcases view08_T4 s false (pts08 a a' b b' c c' d) with h | h <;> rw [hp] at h
    · right; rw [h]; abel
    · left; rw [h]; abel

end W5
end Type08Sp
end Minimality
