module

public import Minimality.Octahedron
public import Minimality.Type24SAT.K24.ParOffOB1
public import Minimality.Type24SAT.K24.FinalPpmmm
public import Minimality.Type24SAT.K24.FinalPpmpp
public import Minimality.Type24SAT.K24.FinalPpppm
public import Minimality.Type24SAT.K24.FinalPmmpp
public import Minimality.Type24SAT.K24.FinalMpmpp
public import Minimality.Type24SAT.K24.FinalPpmpm
public import Minimality.Type29SAT.Mir

@[expose] public section

/-!
# Type 24: the ten closed bracket classes off the obtuse corner, wired to the skeleton

The SAT route sorts a type 24 configuration (facets `s0x_S24`) by the signs of the five class brackets
`[1234] [1245] [1356] [1456] [2456]` (`b1234 … b2456`), read in the orientation where the chirality bracket
`[0126] = chi24 x` is negative (the mirror image reverses all six signs, `cls24`).  With all five brackets nonzero the
sign vector is one of twelve classes (`cls12_of_ne`: the other 20 vectors each violate a three-term Grassmann-Plücker
relation whose other brackets have signs forced by the facets; `chi24_ne`: the chirality bracket never vanishes).  Ten
classes are closed off the obtuse corner `OB1` (all face angles at vertex `1` non-acute): `ppmmm ppmpp ppppm pmmpp
mpmpp ppmpm` by encoder cores and `ppppp pmppp mpmpm mpmmm` by the parallelogram split
(`Minimality.T24.isRupert_offOB1_*`).  `Resid24 x` is what is left: `OB1`, a zero class bracket, or one of the open
classes `mpppp`, `mpppm`.  `rupert_or_resid24` takes the nine facet witnesses of the skeleton's type 24 branch
(`RealizesFaces`) and gives Rupert or `Resid24 x`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24
open Minimality Minimality.H21 Minimality.T24.SAT
open Minimality.H29.SAT (mir mir_sub mir_det3 mirFac)

/-- The chirality bracket `[0126]` (negative in the reference orientation of the classes). -/
noncomputable def chi24 (x : Fin 7 → ℝ³) : ℝ := det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)
/-- Class bracket `[1234]`. -/
noncomputable def b1234 (x : Fin 7 → ℝ³) : ℝ := det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1)
/-- Class bracket `[1245]`. -/
noncomputable def b1245 (x : Fin 7 → ℝ³) : ℝ := det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1)
/-- Class bracket `[1356]`. -/
noncomputable def b1356 (x : Fin 7 → ℝ³) : ℝ := det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1)
/-- Class bracket `[1456]`. -/
noncomputable def b1456 (x : Fin 7 → ℝ³) : ℝ := det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)
/-- Class bracket `[2456]`. -/
noncomputable def b2456 (x : Fin 7 → ℝ³) : ℝ := det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2)

/-- `sg true r` is `0 < r` (letter `p`), `sg false r` is `r < 0` (letter `m`). -/
def sg : Bool → ℝ → Prop
  | true, r => 0 < r
  | false, r => r < 0

/-- The bracket class with letters `s0 … s4` (`true` = `p`): the reference orientation (`[0126] < 0`) with these signs,
or the mirror orientation with all six signs reversed.  This is the hypothesis `hcls` of the class theorems. -/
def cls24 (x : Fin 7 → ℝ³) (s0 s1 s2 s3 s4 : Bool) : Prop :=
  (chi24 x < 0 ∧ sg s0 (b1234 x) ∧ sg s1 (b1245 x) ∧ sg s2 (b1356 x) ∧ sg s3 (b1456 x) ∧ sg s4 (b2456 x)) ∨
    (0 < chi24 x ∧ sg (!s0) (b1234 x) ∧ sg (!s1) (b1245 x) ∧ sg (!s2) (b1356 x) ∧ sg (!s3) (b1456 x) ∧
      sg (!s4) (b2456 x))

/-- The twelve classes of the SAT route (all sign vectors with nonzero brackets, `cls12_of_ne`). -/
def Cls12 (x : Fin 7 → ℝ³) : Prop :=
  cls24 x true true false false false ∨ cls24 x true true false true true ∨ cls24 x true true true true false ∨
    cls24 x true false false true true ∨ cls24 x false true false true true ∨ cls24 x true true false true false ∨
    cls24 x true true true true true ∨ cls24 x true false true true true ∨ cls24 x false true false true false ∨
    cls24 x false true false false false ∨ cls24 x false true true true true ∨ cls24 x false true true true false

/-- **The type 24 residual**: the obtuse corner `OB1`, a zero class bracket, or one of the open classes `mpppp`,
`mpppm`. -/
def Resid24 (x : Fin 7 → ℝ³) : Prop :=
  H24K.SAT.OB1 x ∨ (b1234 x = 0 ∨ b1245 x = 0 ∨ b1356 x = 0 ∨ b1456 x = 0 ∨ b2456 x = 0) ∨
    cls24 x false true true true true ∨ cls24 x false true true true false

/-! ### The twelve classes are all sign vectors (three-term Grassmann-Plücker relations)

Each excluded sign vector violates one three-term relation `[abcd][abef] - [abce][abdf] + [abcf][abde] = 0` whose six
brackets are class brackets or brackets of a facet triple and a vertex off the facet (sign forced by convexity,
`cv_pos24`).  Four relations suffice: pairs `12`, `24`, `16`, `46`. -/

/-- A forced bracket: a facet's reference triple and a vertex off the facet, in the orientation `[0126] < 0`. -/
theorem forced24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (t : Fin 9) (v i j k : Fin 7) (s : ℝ)
    (hv : v ∉ s0x_S24 t) (hi : fA t = i) (hj : fB t = j) (hk : fC t = k) (hs : ((sig t.val : Int) : ℝ) = s) :
    0 < -s * det3 (x j - x i) (x k - x i) (x v - x i) := by
  subst hi hj hk hs; rw [← cv_ext]; exact cv_pos24 F hc t v hv

theorem excl_R1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h1 : b1245 x < 0) (h0 : b1234 x < 0) : False := by
  have aF0_3 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) := by
    have h := forced24 F hc 0 3 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1245 : 0 < -1 * (b1245 x) := by linarith
  have aF0_4 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 0 4 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF6_1 : 0 < -1 * (det3 (x 3 - x 2) (x 5 - x 2) (x 1 - x 2)) := by
    have h := forced24 F hc 6 1 2 3 5 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF0_5 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0)) := by
    have h := forced24 F hc 0 5 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1234 : 0 < -1 * (b1234 x) := by linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) * (b1245 x) + (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) * (det3 (x 3 - x 2) (x 5 - x 2) (x 1 - x 2)) + (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0)) * (b1234 x) = 0 := by
    simp only [b1234, b1245, det3_expand, PiLp.sub_apply]; ring
  nlinarith [mul_pos aF0_3 ab1245, mul_pos aF0_4 aF6_1, mul_pos aF0_5 ab1234]

theorem excl_RA {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h4 : b2456 x < 0) (h1 : b1245 x < 0) : False := by
  have aF0_4 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 0 4 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab2456 : 0 < -1 * (b2456 x) := by linarith
  have aF2_4 : 0 < -1 * (det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 2 4 0 2 5 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF5_4 : 0 < 1 * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) := by
    have h := forced24 F hc 5 4 1 2 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF4_2 : 0 < -1 * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) := by
    have h := forced24 F hc 4 2 0 4 6 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1245 : 0 < -1 * (b1245 x) := by linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) * (b2456 x) + (-1) * (det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0)) * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) + (1) * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) * (b1245 x) = 0 := by
    simp only [b1245, b2456, det3_expand, PiLp.sub_apply]; ring
  nlinarith [mul_pos aF0_4 ab2456, mul_pos aF2_4 aF5_4, mul_pos aF4_2 ab1245]

theorem excl_RB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h3 : b1456 x < 0) (h2 : 0 < b1356 x) : False := by
  have aF1_3 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 3 - x 0)) := by
    have h := forced24 F hc 1 3 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1456 : 0 < -1 * (b1456 x) := by linarith
  have aF1_4 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 1 4 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1356 : 0 < 1 * (b1356 x) := by linarith
  have aF1_5 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 5 - x 0)) := by
    have h := forced24 F hc 1 5 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF8_1 : 0 < 1 * (det3 (x 4 - x 3) (x 6 - x 3) (x 1 - x 3)) := by
    have h := forced24 F hc 8 1 3 4 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 3 - x 0)) * (b1456 x) + (-1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) * (b1356 x) + (-1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 5 - x 0)) * (det3 (x 4 - x 3) (x 6 - x 3) (x 1 - x 3)) = 0 := by
    simp only [b1356, b1456, det3_expand, PiLp.sub_apply]; ring
  nlinarith [mul_pos aF1_3 ab1456, mul_pos aF1_4 ab1356, mul_pos aF1_5 aF8_1]

theorem excl_RC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h4 : 0 < b2456 x) (h3 : b1456 x < 0) : False := by
  have aF1_4 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 1 4 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab2456 : 0 < 1 * (b2456 x) := by linarith
  have aF4_2 : 0 < -1 * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) := by
    have h := forced24 F hc 4 2 0 4 6 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1456 : 0 < -1 * (b1456 x) := by linarith
  have aF4_5 : 0 < -1 * (det3 (x 4 - x 0) (x 6 - x 0) (x 5 - x 0)) := by
    have h := forced24 F hc 4 5 0 4 6 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF5_4 : 0 < 1 * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) := by
    have h := forced24 F hc 5 4 1 2 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) * (b2456 x) + (1) * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) * (b1456 x) + (-1) * (det3 (x 4 - x 0) (x 6 - x 0) (x 5 - x 0)) * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) = 0 := by
    simp only [b1456, b2456, det3_expand, PiLp.sub_apply]; ring
  nlinarith [mul_pos aF1_4 ab2456, mul_pos aF4_2 ab1456, mul_pos aF4_5 aF5_4]


private theorem det3_mul_det3' (N₀ N₁ N₂ e₀ e₁ e₂ : ℝ³) :
    det3 N₀ N₁ N₂ * det3 e₀ e₁ e₂ =
      ⟪N₀, e₀⟫ * (⟪N₁, e₁⟫ * ⟪N₂, e₂⟫ - ⟪N₁, e₂⟫ * ⟪N₂, e₁⟫) -
      ⟪N₀, e₁⟫ * (⟪N₁, e₀⟫ * ⟪N₂, e₂⟫ - ⟪N₁, e₂⟫ * ⟪N₂, e₀⟫) +
      ⟪N₀, e₂⟫ * (⟪N₁, e₀⟫ * ⟪N₂, e₁⟫ - ⟪N₁, e₁⟫ * ⟪N₂, e₀⟫) := by
  simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- The chirality bracket does not vanish: `x 6` is off the facet `012`, `x 2` off `016`, `x 1` off `025`. -/
theorem chi24_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : chi24 x ≠ 0 := by
  intro h0
  have key := det3_mul_det3' (F.N 0) (F.N 1) (F.N 2) (x 1 - x 0) (x 2 - x 0) (x 6 - x 0)
  have z : ∀ (t : Fin 9) (a b : Fin 7), a ∈ s0x_S24 t → b ∈ s0x_S24 t → ⟪F.N t, x a - x b⟫ = 0 := by
    intro t a b ha hb; rw [F.inner_sub, F.zero t a ha, F.zero t b hb, sub_zero]
  have n : ∀ (t : Fin 9) (a b : Fin 7), a ∉ s0x_S24 t → b ∈ s0x_S24 t → ⟪F.N t, x a - x b⟫ < 0 := by
    intro t a b ha hb; rw [F.inner_sub, F.zero t b hb, sub_zero]; exact F.neg t a ha
  have ha := n 0 6 0 (by decide) (by decide)
  have hb := n 1 2 0 (by decide) (by decide)
  have hc := n 2 1 0 (by decide) (by decide)
  rw [show det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) = 0 from h0, mul_zero, z 0 1 0 (by decide) (by decide),
    z 0 2 0 (by decide) (by decide), z 1 1 0 (by decide) (by decide), z 1 6 0 (by decide) (by decide),
    z 2 2 0 (by decide) (by decide)] at key
  have := mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg ha hb) hc
  nlinarith

/-- A bracket of the mirror image is minus the bracket. -/
theorem mdet24 (a b c d : ℝ³) :
    det3 (mir b - mir a) (mir c - mir a) (mir d - mir a) = - det3 (b - a) (c - a) (d - a) := by
  rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]

theorem excl_R1' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h1 : 0 < b1245 x)
    (h0 : 0 < b1234 x) : False :=
  excl_R1 (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos h1)
    (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos h0)

theorem excl_RA' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h4 : 0 < b2456 x)
    (h1 : 0 < b1245 x) : False :=
  excl_RA (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos h4)
    (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos h1)

theorem excl_RB' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h3 : 0 < b1456 x)
    (h2 : b1356 x < 0) : False :=
  excl_RB (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos h3)
    (by show 0 < det3 _ _ _; rw [mdet24]; exact neg_pos_of_neg h2)

theorem excl_RC' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h4 : b2456 x < 0)
    (h3 : 0 < b1456 x) : False :=
  excl_RC (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show 0 < det3 _ _ _; rw [mdet24]; exact neg_pos_of_neg h4)
    (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos h3)

/-- **Class exhaustion for type 24**: with all five class brackets nonzero, the sign vector is one of the twelve classes
(either orientation). -/
theorem cls12_of_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h0 : b1234 x ≠ 0) (h1 : b1245 x ≠ 0)
    (h2 : b1356 x ≠ 0) (h3 : b1456 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls12 x := by
  rcases lt_or_gt_of_ne (chi24_ne F) with hc | hc <;>
  rcases lt_or_gt_of_ne h0 with a0 | a0 <;> rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h2 with a2 | a2 <;> rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  first
  | exact (excl_R1 F hc ‹_› ‹_›).elim | exact (excl_RA F hc ‹_› ‹_›).elim
  | exact (excl_RB F hc ‹_› ‹_›).elim | exact (excl_RC F hc ‹_› ‹_›).elim
  | exact (excl_R1' F hc ‹_› ‹_›).elim | exact (excl_RA' F hc ‹_› ‹_›).elim
  | exact (excl_RB' F hc ‹_› ‹_›).elim | exact (excl_RC' F hc ‹_› ‹_›).elim
  | simp only [Cls12, cls24, sg, Bool.not_true, Bool.not_false, hc, a0, a1, a2, a3, a4, and_self, true_or,
      or_true, and_true]

/-- Off the residual, one of the ten closed classes holds off `OB1`: Rupert. -/
theorem isRupert_of_not_resid24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : ¬ Resid24 x) :
    IsRupert (univ.image x) := by
  simp only [Resid24, not_or] at h
  obtain ⟨hO, ⟨h0, h1, h2, h3, h4⟩, hmpppp, hmpppm⟩ := h
  rcases cls12_of_ne F h0 h1 h2 h3 h4 with h | h | h | h | h | h | h | h | h | h | h | h
  · exact isRupert_offOB1_ppmmm F h hO
  · exact isRupert_offOB1_ppmpp F h hO
  · exact isRupert_offOB1_ppppm F h hO
  · exact isRupert_offOB1_pmmpp F h hO
  · exact isRupert_offOB1_mpmpp F h hO
  · exact isRupert_offOB1_ppmpm F h hO
  · exact isRupert_offOB1_ppppp F h hO
  · exact isRupert_offOB1_pmppp F h hO
  · exact isRupert_offOB1_mpmpm F h hO
  · exact isRupert_offOB1_mpmmm F h hO
  · exact (hmpppp h).elim
  · exact (hmpppm h).elim

/-- The nine facets of type 24 as an `S0xFac` from affine witnesses. -/
noncomputable def mkFac24 {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)) :
    S0xFac 9 s0x_S24 x where
  f t := fs t
  N t := Classical.choose (exists_normal_of_affine (fs t))
  hN t := Classical.choose_spec (exists_normal_of_affine (fs t))
  zero t i hi := (h t i).1 hi
  neg t i hi := (h t i).2 hi

/-- **The type 24 branch, closed off the residual**: from the nine facet witnesses (`012 016 126 236 046 025 0345 235
346`, the skeleton's `hR`), the points are Rupert or `Resid24 x` holds. -/
theorem rupert_or_resid24 {x : Fin 7 → ℝ³} (fA fB fC fD fE fF fG fH fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) < 0)) :
    IsRupert (univ.image x) ∨ Resid24 x := by
  by_cases hr : Resid24 x
  · exact Or.inr hr
  refine Or.inl (isRupert_of_not_resid24 (mkFac24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] ?_) hr)
  intro t i
  fin_cases t
  exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]

end Minimality.T24

