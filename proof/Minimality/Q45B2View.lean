module

public import Minimality.Q45J0Tilt
public import Minimality.Sym24Transport
public import Minimality.EdgeViewLink

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.LexCell Minimality.T24.SAT

/-!
# The B2 / C2 corner-tie view: in the face plane of `0345`, across edge `3 4` (job OSPEC6)

nopert229 notes/OPENSPECIAL-STRATEGY.md.  On the corner tie `T-B2` (`K+`, `1 < s`, `h6hi`, not `HlexB2`, so
`z2 = z5 = z6` at `e34 = x 3 - x 4`) the corner cell `B2` (view `-e34 - ε e5`) fails.  The view turned by 90 degrees
inside the face plane does not: `bB2 F = ⟪N8, N3⟫ N3 - |N3|² N8` is orthogonal to `N3` and to `e34` (both `N3` and
`N8` are), so it lies in the face plane, perpendicular to the edge `3 4`, pointing into the face (`⟪x 0 - x 3, bB2⟫ =
-|N3|² f8(x 0) > 0`); it is `-M34` of ospec5 cscan up to a positive factor.  The 3-level lex view `(bB2, +N3, -e4)`
tilts the face `0345` up (`b2_up3`), keeps the facet `346` down (`b2_dn8`: `⟪N8, bB2⟫ = -|bB2|² / |N3|²`), and its
rim is `0 1 6 3 4` (facets `5`, `7` up) or `0 1 2 3 4` (facets `5`, `7` down, `6` up): `B2ViewOK` asks for the
remaining facet signs and `RobUniLex` of that rim; `lexAny_of_b2View` turns it into a lex cell.  No hypothesis of the
B2 branch is used.  The mirror `π = (2 6)(4 5)` (`Sym24Transport.lean`) maps the corner tie `T-C2` onto `T-B2`;
`lexAny_of_b2View_sym` is the C2 form.

Image-plane form (`b2ViewOK_of_image`, every facet sign derived): projecting along `bB2` is projecting onto the
plane of `e34` and `N3`, image coordinates `y = ⟪·, e34⟫` and `f3` (`image_det_pair`, `b2_image`: the sign of `det3
a v bB2 * det3 a v' bB2` is that of the 2D cross products `imI`). Two facets through an edge have equal signs at a
view if their third vertices project to opposite sides of the projected edge, opposite signs if to the same side
(`facet_pair_sign`, generic `S0xFac`). From the known facets `3` (up) and `346` (down): `046` down if `y0 < y4`
(face angle at `4` obtuse, `b2_dn4_of_obtuse`), `235` up if `y5 < y3` (`b2_up6_of_acute`), `016` down if `1`, `4`
lie on opposite sides of the image line `0 6` (`b2_dn1`), `012` up if `2`, `6` lie on one side of the image line `0
1` (`b2_up0`); on the tie `y2 = y5 = y6`, `236` up if `f3(x 6) < f3(x 2)` (down if `>`) (`b2_sign7`) and `126` has
the sign of `236` if `y1 < y6` (`b2_flip57`). So the two facet patterns are the two signs of the S3 function `f3(x
2) - f3(x 6)` and `B2ImageOK` asks for image-plane positions plus `RobUniLex` of the selected rim. The depth is `⟪x,
bB2⟫ = ⟪N8, N3⟫ f3 - |N3|² f8` (+ const): on the face the edge `3 4` is lowest (`b2_face_low`).
-/

namespace Minimality.T24.Q45

variable {x : Fin 7 → ℝ³}

/-- The B2 view: in the face plane of `0345`, perpendicular to the edge `3 4`, pointing into the face. -/
noncomputable def bB2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : ℝ³ :=
  ⟪F.N 8, F.N 3⟫ • F.N 3 - ⟪F.N 3, F.N 3⟫ • F.N 8

/-- Rim `0 1 6 3 4` (facets `0 3 5 7` up, `1 4 8` down). -/
def rimB2A : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 4]
def UB2A : Finset (Fin 9) := {0, 3, 5, 7}
def DnB2A : Finset (Fin 9) := {1, 4, 8}
/-- Rim `0 1 2 3 4` (facets `0 3 6` up, `1 4 5 7 8` down). -/
def rimB2B : ZMod 5 → Fin 7 := ![0, 1, 2, 3, 4]
def UB2B : Finset (Fin 9) := {0, 3, 6}
def DnB2B : Finset (Fin 9) := {1, 4, 5, 7, 8}

theorem rimB2A_cyc : S0xCycUD s0x_S24 rimB2A UB2A DnB2A := by decide
theorem rimB2B_cyc : S0xCycUD s0x_S24 rimB2B UB2B DnB2B := by decide
theorem rimB2A_inj : Function.Injective rimB2A := by decide
theorem rimB2B_inj : Function.Injective rimB2B := by decide

/-- Facet `t` is up in the lex view `(bB2, N3, -e4)`. -/
def B2Up {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 ⟪F.N t, bB2 F⟫ ⟪F.N t, F.N 3⟫ ⟪F.N t, -(x 4 - x 0)⟫
/-- Facet `t` is down in the lex view `(bB2, N3, -e4)`. -/
def B2Dn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 (-⟪F.N t, bB2 F⟫) (-⟪F.N t, F.N 3⟫) (-⟪F.N t, -(x 4 - x 0)⟫)

/-- Lex depth triples of a rim in the view `(bB2, N3, -e4)`. -/
noncomputable def b2Z {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (c : ZMod 5 → Fin 7) : ZMod 5 → ℝ × ℝ × ℝ :=
  fun i => (⟪x (c i), bB2 F⟫, ⟪x (c i), F.N 3⟫, ⟪x (c i), -(x 4 - x 0)⟫)

/-- **The B2 view condition**: rim `0 1 6 3 4` with facets `0 5 7` up, `1 4` down, or rim `0 1 2 3 4` with facets
`0 6` up, `1 4 5 7` down, and the rim `RobUniLex` in the lex order `(bB2, N3, -e4)` (facets `3`, `8`: automatic). -/
def B2ViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (B2Up F 0 ∧ B2Dn F 1 ∧ B2Dn F 4 ∧ B2Up F 5 ∧ B2Up F 7 ∧ RobUniLex (b2Z F rimB2A)) ∨
    (B2Up F 0 ∧ B2Dn F 1 ∧ B2Dn F 4 ∧ B2Dn F 5 ∧ B2Up F 6 ∧ B2Dn F 7 ∧ RobUniLex (b2Z F rimB2B))

theorem inner_N3_bB2 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 3, bB2 F⟫ = 0 := by
  simp only [bB2, inner_sub_right, real_inner_smul_right]; rw [real_inner_comm (F.N 3) (F.N 8)]; ring

/-- `bB2` points into the face from the edge `3 4`: `⟪x 0 - x 3, bB2⟫ = -|N3|² f8(x 0) > 0`. -/
theorem inner_x03_bB2 (F : S0xFac 9 s0x_S24 x) : 0 < ⟪x 0 - x 3, bB2 F⟫ := by
  have h3 : ⟪F.N 3, x 0 - x 3⟫ = 0 := by
    rw [F.inner_sub 3 0 3, F.zero 3 0 (by decide), F.zero 3 3 (by decide)]; ring
  have h8 : ⟪F.N 8, x 0 - x 3⟫ = F.f 8 (x 0) := by
    rw [F.inner_sub 8 0 3, F.zero 8 3 (by decide)]; ring
  have hf8 : F.f 8 (x 0) < 0 := F.neg 8 0 (by decide)
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h3' : ⟪x 0 - x 3, F.N 3⟫ = 0 := by rw [real_inner_comm]; exact h3
  have h8' : ⟪x 0 - x 3, F.N 8⟫ = F.f 8 (x 0) := by rw [real_inner_comm]; exact h8
  simp only [bB2, inner_sub_right, real_inner_smul_right]
  rw [h3', h8']
  nlinarith

theorem bB2_ne_zero (F : S0xFac 9 s0x_S24 x) : bB2 F ≠ 0 := by
  intro h; have := inner_x03_bB2 F; rw [h, inner_zero_right] at this; exact lt_irrefl _ this

/-- The face `0345` is up in the lex view (decided by `d1 = N3`). -/
theorem b2_up3 (F : S0xFac 9 s0x_S24 x) : B2Up F 3 :=
  Or.inr ⟨inner_N3_bB2 F, Or.inl (real_inner_self_pos.mpr (n3_ne_zero F))⟩

/-- The facet `346` is down: `|N3|² ⟪N8, bB2⟫ = -|bB2|²`. -/
theorem b2_dn8 (F : S0xFac 9 s0x_S24 x) : B2Dn F 8 := by
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have hbb : 0 < ⟪bB2 F, bB2 F⟫ := real_inner_self_pos.mpr (bB2_ne_zero F)
  have e := inner_sub_left (𝕜 := ℝ) (⟪F.N 8, F.N 3⟫ • F.N 3) (⟪F.N 3, F.N 3⟫ • F.N 8) (bB2 F)
  rw [real_inner_smul_left, real_inner_smul_left, inner_N3_bB2 F] at e
  change ⟪bB2 F, bB2 F⟫ = _ at e
  left
  nlinarith

/-- Gram decomposition of `⟪N, w⟫` along `u`, `v`, `u × v` (a polynomial identity in `ℝ³`). -/
theorem gram_decomp (u v w N : ℝ³) :
    (⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2) * ⟪N, w⟫ =
      (⟪v, v⟫ * ⟪w, u⟫ - ⟪u, v⟫ * ⟪w, v⟫) * ⟪N, u⟫ + (⟪u, u⟫ * ⟪w, v⟫ - ⟪u, v⟫ * ⟪w, u⟫) * ⟪N, v⟫ +
        det3 u v w * det3 u v N := by
  have e : ∀ a b : ℝ³, ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    intro a b
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
  simp only [e, det3_expand]; ring

/-- **In-plane sign of a side facet.**  `w`, `u`, `v` coplanar, `N ⊥ u`, `w ⊥ v`: the sign of `⟪N, w⟫` is that of
`-⟪u, v⟫ ⟪w, u⟫ ⟪N, v⟫` (in the plane, `w` lies on the side of the line `u` given by the angle between `u` and
`v`). -/
theorem sign_side (u v w N : ℝ³) (hNu : ⟪N, u⟫ = 0) (hwv : ⟪w, v⟫ = 0) (hdet : det3 u v w = 0) :
    (⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2) * ⟪N, w⟫ = -(⟪u, v⟫ * ⟪w, u⟫ * ⟪N, v⟫) := by
  rw [gram_decomp, hNu, hwv, hdet]; ring

theorem gram_nonneg (u v : ℝ³) : 0 ≤ ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  have := real_inner_mul_inner_self_le u v; nlinarith

/-- `bB2` is in the face plane: coplanar with any two face-plane vectors. -/
theorem det_bB2 (F : S0xFac 9 s0x_S24 x) {u v : ℝ³} (hu : ⟪F.N 3, u⟫ = 0) (hv : ⟪F.N 3, v⟫ = 0) :
    det3 u v (bB2 F) = 0 := by
  have h := det_perp' u v (bB2 F) (F.N 3) hu hv
  rw [inner_N3_bB2, mul_zero] at h
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  exact (mul_eq_zero.mp h).resolve_right hNN.ne'

theorem inner_bB2_face (F : S0xFac 9 s0x_S24 x) (p q : Fin 7) (hp : p ∈ s0x_S24 3) (hq : q ∈ s0x_S24 3) :
    ⟪bB2 F, x p - x q⟫ = -(⟪F.N 3, F.N 3⟫ * (F.f 8 (x p) - F.f 8 (x q))) := by
  have h3 : ⟪x p - x q, F.N 3⟫ = 0 := by
    rw [real_inner_comm, F.inner_sub 3 p q, F.zero 3 p hp, F.zero 3 q hq]; ring
  have h8 : ⟪x p - x q, F.N 8⟫ = F.f 8 (x p) - F.f 8 (x q) := by rw [real_inner_comm, F.inner_sub 8 p q]
  rw [real_inner_comm]; simp only [bB2, inner_sub_right, real_inner_smul_right]; rw [h3, h8]; ring

theorem n3_perp_face (F : S0xFac 9 s0x_S24 x) (p q : Fin 7) (hp : p ∈ s0x_S24 3) (hq : q ∈ s0x_S24 3) :
    ⟪F.N 3, x p - x q⟫ = 0 := by
  rw [F.inner_sub 3 p q, F.zero 3 p hp, F.zero 3 q hq]; ring

/-- **Facet `046` is down at `bB2` if the face angle of `0345` at `4` is obtuse.** -/
theorem b2_dn4_of_obtuse (F : S0xFac 9 s0x_S24 x) (h : ⟪x 0 - x 4, x 3 - x 4⟫ < 0) : ⟪F.N 4, bB2 F⟫ < 0 := by
  have hNu : ⟪F.N 4, x 0 - x 4⟫ = 0 := by
    rw [F.inner_sub 4 0 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]; ring
  have hNv : ⟪F.N 4, x 3 - x 4⟫ = F.f 4 (x 3) := by rw [F.inner_sub 4 3 4, F.zero 4 4 (by decide)]; ring
  have hf : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  have hwv : ⟪bB2 F, x 3 - x 4⟫ = 0 := by
    rw [inner_bB2_face F 3 4 (by decide) (by decide), F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring
  have hwu : 0 < ⟪bB2 F, x 0 - x 4⟫ := by
    rw [inner_bB2_face F 0 4 (by decide) (by decide), F.zero 8 4 (by decide)]
    have := F.neg 8 0 (by decide); have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
    nlinarith
  have hd := det_bB2 F (n3_perp_face F 0 4 (by decide) (by decide)) (n3_perp_face F 3 4 (by decide) (by decide))
  have key := sign_side _ _ _ _ hNu hwv hd
  have hG := gram_nonneg (x 0 - x 4) (x 3 - x 4)
  rw [hNv] at key
  by_contra hc
  have : 0 ≤ (⟪x 0 - x 4, x 0 - x 4⟫ * ⟪x 3 - x 4, x 3 - x 4⟫ - ⟪x 0 - x 4, x 3 - x 4⟫ ^ 2) * ⟪F.N 4, bB2 F⟫ :=
    mul_nonneg hG (not_lt.mp hc)
  have h2 : 0 < ⟪x 0 - x 4, x 3 - x 4⟫ * ⟪bB2 F, x 0 - x 4⟫ * F.f 4 (x 3) :=
    mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos h hwu) hf
  linarith

/-- **Facet `235` is up at `bB2` if the face angle of `0345` at `3` is acute.** -/
theorem b2_up6_of_acute (F : S0xFac 9 s0x_S24 x) (h : 0 < ⟪x 5 - x 3, x 4 - x 3⟫) : 0 < ⟪F.N 6, bB2 F⟫ := by
  have hNu : ⟪F.N 6, x 5 - x 3⟫ = 0 := by
    rw [F.inner_sub 6 5 3, F.zero 6 5 (by decide), F.zero 6 3 (by decide)]; ring
  have hNv : ⟪F.N 6, x 4 - x 3⟫ = F.f 6 (x 4) := by rw [F.inner_sub 6 4 3, F.zero 6 3 (by decide)]; ring
  have hf : F.f 6 (x 4) < 0 := F.neg 6 4 (by decide)
  have hwv : ⟪bB2 F, x 4 - x 3⟫ = 0 := by
    rw [inner_bB2_face F 4 3 (by decide) (by decide), F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring
  have hwu : 0 < ⟪bB2 F, x 5 - x 3⟫ := by
    rw [inner_bB2_face F 5 3 (by decide) (by decide), F.zero 8 3 (by decide)]
    have := F.neg 8 5 (by decide); have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
    nlinarith
  have hd := det_bB2 F (n3_perp_face F 5 3 (by decide) (by decide)) (n3_perp_face F 4 3 (by decide) (by decide))
  have key := sign_side _ _ _ _ hNu hwv hd
  have hG := gram_nonneg (x 5 - x 3) (x 4 - x 3)
  rw [hNv] at key
  by_contra hc
  have : (⟪x 5 - x 3, x 5 - x 3⟫ * ⟪x 4 - x 3, x 4 - x 3⟫ - ⟪x 5 - x 3, x 4 - x 3⟫ ^ 2) * ⟪F.N 6, bB2 F⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hG (not_lt.mp hc)
  have h2 : ⟪x 5 - x 3, x 4 - x 3⟫ * ⟪bB2 F, x 5 - x 3⟫ * F.f 6 (x 4) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos h hwu) hf
  linarith

theorem pow_pos_of_ne_zero' {r : ℝ} (h : r ≠ 0) : 0 < r ^ 2 := by positivity

/-- Gram positivity: `u ≠ 0`, `N ⊥ u`, `⟪N, v⟫ ≠ 0` (so `u`, `v` are independent). -/
theorem gram_pos (u v N : ℝ³) (hu : u ≠ 0) (hNu : ⟪N, u⟫ = 0) (hNv : ⟪N, v⟫ ≠ 0) :
    0 < ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  have h := gram_decomp u v N N
  rw [hNu] at h
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hvv : 0 < ⟪N, v⟫ ^ 2 := by positivity
  have hG := gram_nonneg u v
  rcases hG.lt_or_eq with hG | hG
  · exact hG
  · exfalso
    rw [← hG, zero_mul] at h
    nlinarith [sq_nonneg (det3 u v N), mul_pos huu hvv]

/-- The decomposition of `b` along `e`, `n`, `e × n`, read by `det3 a v ·` (Binet-Cauchy for the last term). -/
theorem det_gram_cross (a v b e n : ℝ³) :
    (⟪e, e⟫ * ⟪n, n⟫ - ⟪e, n⟫ ^ 2) * det3 a v b =
      (⟪n, n⟫ * ⟪b, e⟫ - ⟪e, n⟫ * ⟪b, n⟫) * det3 a v e + (⟪e, e⟫ * ⟪b, n⟫ - ⟪e, n⟫ * ⟪b, e⟫) * det3 a v n +
        det3 e n b * (⟪a, e⟫ * ⟪v, n⟫ - ⟪a, n⟫ * ⟪v, e⟫) := by
  have e' : ∀ p q : ℝ³, ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
    intro p q
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
  simp only [e', det3_expand]; ring

theorem inner_bB2_e34 (F : S0xFac 9 s0x_S24 x) : ⟪bB2 F, x 3 - x 4⟫ = 0 := by
  rw [inner_bB2_face F 3 4 (by decide) (by decide), F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring

/-- **Two facets through an edge** (generic `S0xFac`): facets `t ∋ i, j, k` and `t' ∋ i, j, k'` (`k ∉ t'`,
`k' ∉ t`), `a = x j - x i`.  At any view `w`, `(G G')² f_t(x k') f_t'(x k) ⟪N t, w⟫ ⟪N t', w⟫ = -P (D d d')²` with
`P = det3 a (x k - x i) w * det3 a (x k' - x i) w`: the two facets have equal signs at `w` if `P < 0` (`k`, `k'`
project to opposite sides of the projected edge; the image orientations of the two triangles differ), opposite signs
if `0 < P`. -/
theorem facet_pair_sign {m n : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y)
    {t t' : Fin m} {i j k k' : Fin n} (hi : i ∈ S t) (hj : j ∈ S t) (hk : k ∈ S t) (hi' : i ∈ S t')
    (hj' : j ∈ S t') (hk' : k' ∈ S t') (hkt' : k ∉ S t') (hk't : k' ∉ S t) (ha0 : y j - y i ≠ 0) (w : ℝ³) :
    (det3 (y j - y i) (y k - y i) w * det3 (y j - y i) (y k' - y i) w < 0 → 0 < ⟪F.N t, w⟫ * ⟪F.N t', w⟫) ∧
      (0 < det3 (y j - y i) (y k - y i) w * det3 (y j - y i) (y k' - y i) w → ⟪F.N t, w⟫ * ⟪F.N t', w⟫ < 0) := by
  set a := y j - y i
  set v := y k - y i
  set v' := y k' - y i
  have hta : ⟪F.N t, a⟫ = 0 := by rw [F.inner_sub t j i, F.zero t j hj, F.zero t i hi]; ring
  have htv : ⟪F.N t, v⟫ = 0 := by rw [F.inner_sub t k i, F.zero t k hk, F.zero t i hi]; ring
  have htv' : ⟪F.N t, v'⟫ = F.f t (y k') := by rw [F.inner_sub t k' i, F.zero t i hi]; ring
  have hsa : ⟪F.N t', a⟫ = 0 := by rw [F.inner_sub t' j i, F.zero t' j hj', F.zero t' i hi']; ring
  have hsv' : ⟪F.N t', v'⟫ = 0 := by rw [F.inner_sub t' k' i, F.zero t' k' hk', F.zero t' i hi']; ring
  have hsv : ⟪F.N t', v⟫ = F.f t' (y k) := by rw [F.inner_sub t' k i, F.zero t' i hi']; ring
  have hf : F.f t (y k') < 0 := F.neg t k' hk't
  have hf' : F.f t' (y k) < 0 := F.neg t' k hkt'
  have hG := gram_pos a v (F.N t') ha0 hsa (by rw [hsv]; exact hf'.ne)
  have hG' := gram_pos a v' (F.N t) ha0 hta (by rw [htv']; exact hf.ne)
  have r1 := gram_decomp a v w (F.N t)
  have r2 := gram_decomp a v v' (F.N t)
  have r3 := gram_decomp a v' w (F.N t')
  have r4 := gram_decomp a v' v (F.N t')
  rw [hta, htv] at r1 r2
  rw [hsa, hsv'] at r3 r4
  rw [htv'] at r2
  rw [hsv] at r4
  have hswap : det3 a v' v = -det3 a v v' := by simp only [det3_expand]; ring
  rw [hswap] at r4
  simp only [mul_zero, zero_add] at r1 r2 r3 r4
  set G := ⟪a, a⟫ * ⟪v, v⟫ - ⟪a, v⟫ ^ 2
  set G' := ⟪a, a⟫ * ⟪v', v'⟫ - ⟪a, v'⟫ ^ 2
  set D := det3 a v v'
  set d := det3 a v (F.N t)
  set d' := det3 a v' (F.N t')
  have hDd : D * d ≠ 0 := by
    have : G * F.f t (y k') ≠ 0 := mul_ne_zero hG.ne' hf.ne
    intro h0; apply this; linarith
  have hDd' : D * d' ≠ 0 := by
    have : G' * F.f t' (y k) ≠ 0 := mul_ne_zero hG'.ne' hf'.ne
    intro h0; apply this; linarith
  have hQ : 0 < (D * d * d') ^ 2 :=
    pow_pos_of_ne_zero' (mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul hDd) (right_ne_zero_of_mul hDd))
      (right_ne_zero_of_mul hDd'))
  have hprod : (G * G') ^ 2 * (F.f t (y k') * F.f t' (y k)) * (⟪F.N t, w⟫ * ⟪F.N t', w⟫) =
      -(det3 a v w * det3 a v' w) * (D * d * d') ^ 2 := by
    have : (G * ⟪F.N t, w⟫) * (G * F.f t (y k')) * (G' * ⟪F.N t', w⟫) * (G' * F.f t' (y k)) =
        (det3 a v w * d) * (D * d) * (det3 a v' w * d') * (-D * d') := by
      rw [r1, r2, r3, r4]
    linear_combination this
  have hL : 0 < (G * G') ^ 2 * (F.f t (y k') * F.f t' (y k)) :=
    mul_pos (pow_pos (mul_pos hG hG') 2) (mul_pos_of_neg_of_neg hf hf')
  constructor
  · intro hP
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos hL.le (not_lt.mp hc)
    nlinarith [mul_pos (neg_pos.mpr hP) hQ]
  · intro hP
    by_contra hc
    have := mul_nonneg hL.le (not_lt.mp hc)
    nlinarith [mul_pos hP hQ]

/-- **Image-plane orientation** of an in-plane view: `w ⊥ e, n`, `w ≠ 0`, `e`, `n` independent.  Then
`det3 a v w * det3 a v' w` has the sign of `I(a, v) I(a, v')` with `I(a, v) = ⟪a, e⟫ ⟪v, n⟫ - ⟪a, n⟫ ⟪v, e⟫`, the 2D
cross product of the images of `a`, `v` in the coordinates `(⟪·, e⟫, ⟪·, n⟫)`. -/
theorem image_det_pair (a v v' w e n : ℝ³) (hwe : ⟪w, e⟫ = 0) (hwn : ⟪w, n⟫ = 0) (hw : w ≠ 0)
    (hGen : 0 < ⟪e, e⟫ * ⟪n, n⟫ - ⟪e, n⟫ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ c * (det3 a v w * det3 a v' w) =
      (⟪a, e⟫ * ⟪v, n⟫ - ⟪a, n⟫ * ⟪v, e⟫) * (⟪a, e⟫ * ⟪v', n⟫ - ⟪a, n⟫ * ⟪v', e⟫) := by
  have hdb : det3 e n w ≠ 0 := by
    have h := gram_decomp e n w w
    rw [hwe, hwn] at h
    have hbb : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw
    intro h0; rw [h0] at h; nlinarith [mul_pos hGen hbb]
  have r1 := det_gram_cross a v w e n
  have r2 := det_gram_cross a v' w e n
  rw [hwe, hwn] at r1 r2
  refine ⟨(⟪e, e⟫ * ⟪n, n⟫ - ⟪e, n⟫ ^ 2) ^ 2 / det3 e n w ^ 2, div_pos (pow_pos hGen 2)
    (pow_pos_of_ne_zero' hdb), ?_⟩
  field_simp
  linear_combination (⟪e, e⟫ * ⟪n, n⟫ - ⟪e, n⟫ ^ 2) * det3 a v' w * r1 +
    det3 e n w * (⟪a, e⟫ * ⟪v, n⟫ - ⟪a, n⟫ * ⟪v, e⟫) * r2

/-- The image coordinates of the B2 view are `(⟪·, e34⟫, ⟪·, N3⟫)`. -/
theorem b2_image (F : S0xFac 9 s0x_S24 x) (a v v' : ℝ³) :
    ∃ c : ℝ, 0 < c ∧ c * (det3 a v (bB2 F) * det3 a v' (bB2 F)) =
      (⟪a, x 3 - x 4⟫ * ⟪v, F.N 3⟫ - ⟪a, F.N 3⟫ * ⟪v, x 3 - x 4⟫) *
        (⟪a, x 3 - x 4⟫ * ⟪v', F.N 3⟫ - ⟪a, F.N 3⟫ * ⟪v', x 3 - x 4⟫) := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have he0 : x 3 - x 4 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
  have hen : ⟪F.N 3, x 3 - x 4⟫ = 0 := n3_perp_face F 3 4 (by decide) (by decide)
  refine image_det_pair a v v' (bB2 F) (x 3 - x 4) (F.N 3) (inner_bB2_e34 F)
    (by rw [real_inner_comm]; exact inner_N3_bB2 F) (bB2_ne_zero F) ?_
  have := gram_pos (x 3 - x 4) (F.N 3) (F.N 3) he0 hen (real_inner_self_pos.mpr (n3_ne_zero F)).ne'
  exact this

/-- **Facets `126` and `236` flip together on the tie** `⟪x 2, e34⟫ = ⟪x 6, e34⟫`: their signs at `bB2` agree if
`1` and `3` lie on opposite sides of the column `y = y2 = y6` (`y = ⟪·, e34⟫`), provided `f3(x 2) ≠ f3(x 6)`
(off S3).  Image-plane reason: projecting along `bB2` keeps `y` and `f3`; `2`, `6` project onto one vertical line, and
the edge `2 6` separates the projected triangles `126`, `236` (`facet_pair_sign`, `b2_image`). -/
theorem b2_flip57 (F : S0xFac 9 s0x_S24 x) (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫)
    (h13 : ⟪x 1 - x 6, x 3 - x 4⟫ * ⟪x 3 - x 6, x 3 - x 4⟫ < 0) (h26 : F.f 3 (x 2) ≠ F.f 3 (x 6)) :
    0 < ⟪F.N 5, bB2 F⟫ * ⟪F.N 7, bB2 F⟫ := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have ha0 : x 2 - x 6 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
  refine (facet_pair_sign F (t := 5) (t' := 7) (i := 6) (j := 2) (k := 1) (k' := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0 (bB2 F)).1 ?_
  obtain ⟨c, hc, hcP⟩ := b2_image F (x 2 - x 6) (x 1 - x 6) (x 3 - x 6)
  have hae : ⟪x 2 - x 6, x 3 - x 4⟫ = 0 := by rw [inner_sub_left]; linarith
  have han : ⟪x 2 - x 6, F.N 3⟫ = F.f 3 (x 2) - F.f 3 (x 6) := by rw [real_inner_comm, F.inner_sub 3 2 6]
  rw [hae, han] at hcP
  have hq : 0 < (F.f 3 (x 2) - F.f 3 (x 6)) ^ 2 := pow_pos_of_ne_zero' (sub_ne_zero.mpr h26)
  have hR : (0 * ⟪x 1 - x 6, F.N 3⟫ - (F.f 3 (x 2) - F.f 3 (x 6)) * ⟪x 1 - x 6, x 3 - x 4⟫) *
      (0 * ⟪x 3 - x 6, F.N 3⟫ - (F.f 3 (x 2) - F.f 3 (x 6)) * ⟪x 3 - x 6, x 3 - x 4⟫) < 0 := by
    nlinarith [mul_pos hq (neg_pos.mpr h13)]
  by_contra hP
  have := mul_nonneg hc.le (not_lt.mp hP)
  linarith

/-- **The B2 view is a lex cell** (no hypothesis of the B2 branch). -/
theorem lexAny_of_b2View (F : S0xFac 9 s0x_S24 x) (h : B2ViewOK F) : Gen.LexAny F := by
  rcases h with ⟨h0, h1, h4, h5, h7, hR⟩ | ⟨h0, h1, h4, h5, h6, h7, hR⟩
  · refine ⟨5, inferInstance, rimB2A, UB2A, DnB2A, bB2 F, F.N 3, -(x 4 - x 0), by norm_num, rimB2A_inj,
      rimB2A_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UB2A, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      exacts [h0, b2_up3 F, h5, h7]
    · intro t ht
      simp only [DnB2A, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [h1, h4, b2_dn8 F]
  · refine ⟨5, inferInstance, rimB2B, UB2B, DnB2B, bB2 F, F.N 3, -(x 4 - x 0), by norm_num, rimB2B_inj,
      rimB2B_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UB2B, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [h0, b2_up3 F, h6]
    · intro t ht
      simp only [DnB2B, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      exacts [h1, h4, h5, h7, b2_dn8 F]

/-- **The C2 form** (mirror `π = (2 6)(4 5)`): the B2 view of the mirrored solid is a lex cell of `x`. -/
theorem lexAny_of_b2View_sym (F : S0xFac 9 s0x_S24 x) (h : B2ViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_b2View (Sym.sym24 F) h)

/-- Image-plane cross product in the coordinates `(y, f3) = (⟪·, e34⟫, ⟪·, N3⟫)` of the B2 view. -/
noncomputable def imI {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (a v : ℝ³) : ℝ :=
  ⟪a, x 3 - x 4⟫ * ⟪v, F.N 3⟫ - ⟪a, F.N 3⟫ * ⟪v, x 3 - x 4⟫

/-- The sign of `det3 a v bB2 * det3 a v' bB2` is that of `imI a v * imI a v'`. -/
theorem b2_P_sign (F : S0xFac 9 s0x_S24 x) (a v v' : ℝ³) :
    (imI F a v * imI F a v' < 0 → det3 a v (bB2 F) * det3 a v' (bB2 F) < 0) ∧
      (0 < imI F a v * imI F a v' → 0 < det3 a v (bB2 F) * det3 a v' (bB2 F)) := by
  obtain ⟨c, hc, hcP⟩ := b2_image F a v v'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hP; have := mul_nonneg hc.le (not_lt.mp hP); simp only [imI] at h; linarith
  · by_contra hP; have := mul_nonpos_of_nonneg_of_nonpos hc.le (not_lt.mp hP); simp only [imI] at h; linarith

/-- **Facet `016` is down** when `046` is: `1` and `4` project to opposite sides of the image line `0 6`. -/
theorem b2_dn1 (F : S0xFac 9 s0x_S24 x) (h4 : ⟪F.N 4, bB2 F⟫ < 0)
    (hI : imI F (x 6 - x 0) (x 1 - x 0) * imI F (x 6 - x 0) (x 4 - x 0) < 0) : ⟪F.N 1, bB2 F⟫ < 0 := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have ha0 : x 6 - x 0 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
  have := (facet_pair_sign F (t := 1) (t' := 4) (i := 0) (j := 6) (k := 1) (k' := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0 (bB2 F)).1 ((b2_P_sign F _ _ _).1 hI)
  nlinarith

/-- **Facet `012` is up** when `016` is down: `2` and `6` project to the same side of the image line `0 1`. -/
theorem b2_up0 (F : S0xFac 9 s0x_S24 x) (h1 : ⟪F.N 1, bB2 F⟫ < 0)
    (hI : 0 < imI F (x 1 - x 0) (x 2 - x 0) * imI F (x 1 - x 0) (x 6 - x 0)) : 0 < ⟪F.N 0, bB2 F⟫ := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have ha0 : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
  have := (facet_pair_sign F (t := 0) (t' := 1) (i := 0) (j := 1) (k := 2) (k' := 6) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0 (bB2 F)).2 ((b2_P_sign F _ _ _).2 hI)
  nlinarith

/-- **Facet `236` follows the S3 sign** on the tie `y2 = y6 < y3`: up if `f3(x 6) < f3(x 2)` (`6` farther from the
face plane), by the edge `3 6` shared with the down facet `346`. -/
theorem b2_sign7 (F : S0xFac 9 s0x_S24 x) (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫)
    (h63 : ⟪x 6 - x 3, x 3 - x 4⟫ < 0) :
    (F.f 3 (x 6) < F.f 3 (x 2) → 0 < ⟪F.N 7, bB2 F⟫) ∧ (F.f 3 (x 2) < F.f 3 (x 6) → ⟪F.N 7, bB2 F⟫ < 0) := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have ha0 : x 6 - x 3 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
  have h8 : ⟪F.N 8, bB2 F⟫ < 0 := by
    have := b2_dn8 F
    rcases this with h | ⟨h, -⟩
    · linarith
    · exfalso
      have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
      have hbb : 0 < ⟪bB2 F, bB2 F⟫ := real_inner_self_pos.mpr (bB2_ne_zero F)
      have e := inner_sub_left (𝕜 := ℝ) (⟪F.N 8, F.N 3⟫ • F.N 3) (⟪F.N 3, F.N 3⟫ • F.N 8) (bB2 F)
      rw [real_inner_smul_left, real_inner_smul_left, inner_N3_bB2 F] at e
      change ⟪bB2 F, bB2 F⟫ = _ at e
      have h0 : ⟪F.N 8, bB2 F⟫ = 0 := by linarith
      rw [h0] at e; linarith
  have hP := facet_pair_sign F (t := 7) (t' := 8) (i := 3) (j := 6) (k := 2) (k' := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0 (bB2 F)
  have hf6 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have a1 : ⟪x 2 - x 3, F.N 3⟫ = F.f 3 (x 2) := by
    rw [real_inner_comm, F.inner_sub 3 2 3, F.zero 3 3 (by decide)]; ring
  have a2 : ⟪x 6 - x 3, F.N 3⟫ = F.f 3 (x 6) := by
    rw [real_inner_comm, F.inner_sub 3 6 3, F.zero 3 3 (by decide)]; ring
  have a3 : ⟪x 2 - x 3, x 3 - x 4⟫ = ⟪x 6 - x 3, x 3 - x 4⟫ := by rw [inner_sub_left, inner_sub_left, htie]
  have b1 : ⟪x 4 - x 3, F.N 3⟫ = 0 := by
    rw [real_inner_comm, F.inner_sub 3 4 3, F.zero 3 4 (by decide), F.zero 3 3 (by decide)]; ring
  have hv : imI F (x 6 - x 3) (x 2 - x 3) = ⟪x 6 - x 3, x 3 - x 4⟫ * (F.f 3 (x 2) - F.f 3 (x 6)) := by
    simp only [imI]; rw [a1, a2, a3]; ring
  have hv' : imI F (x 6 - x 3) (x 4 - x 3) = -(F.f 3 (x 6) * ⟪x 4 - x 3, x 3 - x 4⟫) := by
    simp only [imI]; rw [b1, a2]; ring
  have h43 : ⟪x 4 - x 3, x 3 - x 4⟫ < 0 := by
    have hne : x 3 - x 4 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
    have := real_inner_self_pos.mpr hne
    rw [show x 4 - x 3 = -(x 3 - x 4) by abel, inner_neg_left]; linarith
  have hq : 0 < ⟪x 6 - x 3, x 3 - x 4⟫ * ⟪x 4 - x 3, x 3 - x 4⟫ * -F.f 3 (x 6) :=
    mul_pos (mul_pos_of_neg_of_neg h63 h43) (neg_pos.mpr hf6)
  constructor
  · intro h
    have hI : 0 < imI F (x 6 - x 3) (x 2 - x 3) * imI F (x 6 - x 3) (x 4 - x 3) := by
      rw [hv, hv']; nlinarith [mul_pos hq (sub_pos.mpr h)]
    have := hP.2 ((b2_P_sign F _ _ _).2 hI)
    nlinarith
  · intro h
    have hI : imI F (x 6 - x 3) (x 2 - x 3) * imI F (x 6 - x 3) (x 4 - x 3) < 0 := by
      rw [hv, hv']; nlinarith [mul_pos hq (sub_pos.mpr h)]
    have := hP.1 ((b2_P_sign F _ _ _).1 hI)
    nlinarith

/-- **The B2 view condition in image-plane form** (on the tie): in the coordinates `y = ⟪·, e34⟫`, `f3`: `y0 < y4`
(face angle at `4` obtuse), `y5 < y3` (at `3` acute), `y1 < y6`, off S3, `1`, `4` on opposite sides of the image line
`0 6` and `2`, `6` on the same side of the image line `0 1`, and the rim selected by the S3 sign `RobUniLex`
(`0 1 6 3 4` when `6` is farther from the face plane, `0 1 2 3 4` when `2` is). -/
def B2ImageOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪x 0 - x 4, x 3 - x 4⟫ < 0 ∧ ⟪x 5 - x 3, x 3 - x 4⟫ < 0 ∧ ⟪x 1 - x 6, x 3 - x 4⟫ < 0 ∧
    imI F (x 6 - x 0) (x 1 - x 0) * imI F (x 6 - x 0) (x 4 - x 0) < 0 ∧
    0 < imI F (x 1 - x 0) (x 2 - x 0) * imI F (x 1 - x 0) (x 6 - x 0) ∧
    (F.f 3 (x 6) < F.f 3 (x 2) → RobUniLex (b2Z F rimB2A)) ∧
    (F.f 3 (x 2) < F.f 3 (x 6) → RobUniLex (b2Z F rimB2B)) ∧ F.f 3 (x 2) ≠ F.f 3 (x 6)

/-- **On the B2 tie the image-plane conditions give the B2 view** (every facet sign derived). -/
theorem b2ViewOK_of_image (F : S0xFac 9 s0x_S24 x) (htie : Q45TieLocusB2 x) (h : B2ImageOK F) :
    B2ViewOK F := by
  obtain ⟨h04, h53, h16, hI1, hI0, hA, hB, h26⟩ := h
  have t26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := htie.1.trans htie.2
  have t56 : ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := htie.2
  have h63 : ⟪x 6 - x 3, x 3 - x 4⟫ < 0 := by rw [inner_sub_left] at h53 ⊢; linarith
  have hac : 0 < ⟪x 5 - x 3, x 4 - x 3⟫ := by
    rw [show x 4 - x 3 = -(x 3 - x 4) by abel, inner_neg_right]; linarith
  have h13 : ⟪x 1 - x 6, x 3 - x 4⟫ * ⟪x 3 - x 6, x 3 - x 4⟫ < 0 := by
    have : 0 < ⟪x 3 - x 6, x 3 - x 4⟫ := by
      rw [show x 3 - x 6 = -(x 6 - x 3) by abel, inner_neg_left]; linarith
    exact mul_neg_of_neg_of_pos h16 this
  have hp := b2_flip57 F t26 h13 h26
  have n4 := b2_dn4_of_obtuse F h04
  have n1 := b2_dn1 F n4 hI1
  have n0 := b2_up0 F n1 hI0
  have s7 := b2_sign7 F t26 h63
  have d4 : B2Dn F 4 := Or.inl (neg_pos.mpr n4)
  have d1 : B2Dn F 1 := Or.inl (neg_pos.mpr n1)
  have u0 : B2Up F 0 := Or.inl n0
  rcases lt_or_gt_of_ne h26 with h | h
  · have h7 := s7.2 h
    have h5 : ⟪F.N 5, bB2 F⟫ < 0 := by nlinarith
    exact Or.inr ⟨u0, d1, d4, Or.inl (neg_pos.mpr h5), Or.inl (b2_up6_of_acute F hac), Or.inl (neg_pos.mpr h7),
      hB h⟩
  · have h7 := s7.1 h
    have h5 : 0 < ⟪F.N 5, bB2 F⟫ := by nlinarith
    exact Or.inl ⟨u0, d1, d4, Or.inl h5, Or.inl h7, hA h⟩

/-- On the face `0345` the edge `3 4` is lowest at `bB2`: `z_p - z_3 = -|N3|² f8(x p) ≥ 0`. -/
theorem b2_face_low (F : S0xFac 9 s0x_S24 x) (p : Fin 7) (hp : p ∈ s0x_S24 3) :
    ⟪x 3, bB2 F⟫ = ⟪x 4, bB2 F⟫ ∧ ⟪x 3, bB2 F⟫ ≤ ⟪x p, bB2 F⟫ := by
  have e34 := inner_bB2_e34 F
  have ep := inner_bB2_face F p 3 hp (by decide)
  rw [F.zero 8 3 (by decide)] at ep
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have hf := F.le 8 p
  rw [real_inner_comm, inner_sub_left] at e34 ep
  exact ⟨by linarith, by nlinarith⟩

end Minimality.T24.Q45
