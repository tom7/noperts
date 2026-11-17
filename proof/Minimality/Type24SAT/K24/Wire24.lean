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
(`Minimality.T24.isRupert_offOB1_*`).  `Resid24Wide x` is what is left: `OB1`, a zero class bracket, or one of the open
classes `mpppp`, `mpppm`.  `rupert_or_resid24_wide` takes the nine facet witnesses of the skeleton's type 24 branch
(`RealizesFaces`) and gives Rupert or `Resid24Wide x`.
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
def Resid24Wide (x : Fin 7 → ℝ³) : Prop :=
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
  linarith [mul_pos aF0_3 ab1245, mul_pos aF0_4 aF6_1, mul_pos aF0_5 ab1234]

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
  linarith [mul_pos aF0_4 ab2456, mul_pos aF2_4 aF5_4, mul_pos aF4_2 ab1245]

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
  linarith [mul_pos aF1_3 ab1456, mul_pos aF1_4 ab1356, mul_pos aF1_5 aF8_1]

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
  linarith [mul_pos aF1_4 ab2456, mul_pos aF4_2 ab1456, mul_pos aF4_5 aF5_4]


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
  linarith

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


/-! ### Class exhaustion with zero brackets

With zero brackets the three-term relations still apply with `≤` (`exclw_*`: a bracket that vanishes satisfies both
`≤ 0` and `0 ≤`, and in each relation one term is strictly signed by the facets).  So the sign vectors with exactly
one zero bracket (`cls18_of_one_zero`) are the 18 classes `Cls18` (the 18 neighbours-in-`Cls12` candidates of
ZSTRATA24), and with two zero brackets the 8 classes `Cls8`, except that five pairs are impossible (`imp_*`): two
zero brackets that share three points put five points on a plane that contains the plane of a facet triple.  Three
zeros: every triple but `{[1234], [1356], [2456]}` contains an impossible pair; this triple is NOT excluded (the
class `Cls3` is realised by an exact rational solid, `data/hard/t24_cls3_zpzpz`), so it stays an explicit case of `zero_split`. -/

theorem exclw_R1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h1 : b1245 x ≤ 0) (h0 : b1234 x ≤ 0) : False := by
  have aF0_3 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) := by
    have h := forced24 F hc 0 3 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1245 : 0 ≤ -1 * (b1245 x) := by linarith
  have aF0_4 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 0 4 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF6_1 : 0 < -1 * (det3 (x 3 - x 2) (x 5 - x 2) (x 1 - x 2)) := by
    have h := forced24 F hc 6 1 2 3 5 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF0_5 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0)) := by
    have h := forced24 F hc 0 5 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1234 : 0 ≤ -1 * (b1234 x) := by linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) * (b1245 x) + (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) * (det3 (x 3 - x 2) (x 5 - x 2) (x 1 - x 2)) + (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0)) * (b1234 x) = 0 := by
    simp only [b1234, b1245, det3_expand, PiLp.sub_apply]; ring
  linarith [mul_nonneg aF0_3.le ab1245, mul_pos aF0_4 aF6_1, mul_nonneg aF0_5.le ab1234]

theorem exclw_RA {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h4 : b2456 x ≤ 0) (h1 : b1245 x ≤ 0) : False := by
  have aF0_4 : 0 < -1 * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 0 4 0 1 2 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab2456 : 0 ≤ -1 * (b2456 x) := by linarith
  have aF2_4 : 0 < -1 * (det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 2 4 0 2 5 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF5_4 : 0 < 1 * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) := by
    have h := forced24 F hc 5 4 1 2 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF4_2 : 0 < -1 * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) := by
    have h := forced24 F hc 4 2 0 4 6 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1245 : 0 ≤ -1 * (b1245 x) := by linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0)) * (b2456 x) + (-1) * (det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0)) * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) + (1) * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) * (b1245 x) = 0 := by
    simp only [b1245, b2456, det3_expand, PiLp.sub_apply]; ring
  linarith [mul_nonneg aF0_4.le ab2456, mul_pos aF2_4 aF5_4, mul_nonneg aF4_2.le ab1245]

theorem exclw_RB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h3 : b1456 x ≤ 0) (h2 : 0 ≤ b1356 x) : False := by
  have aF1_3 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 3 - x 0)) := by
    have h := forced24 F hc 1 3 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1456 : 0 ≤ -1 * (b1456 x) := by linarith
  have aF1_4 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 1 4 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1356 : 0 ≤ 1 * (b1356 x) := by linarith
  have aF1_5 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 5 - x 0)) := by
    have h := forced24 F hc 1 5 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF8_1 : 0 < 1 * (det3 (x 4 - x 3) (x 6 - x 3) (x 1 - x 3)) := by
    have h := forced24 F hc 8 1 3 4 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 3 - x 0)) * (b1456 x) + (-1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) * (b1356 x) + (-1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 5 - x 0)) * (det3 (x 4 - x 3) (x 6 - x 3) (x 1 - x 3)) = 0 := by
    simp only [b1356, b1456, det3_expand, PiLp.sub_apply]; ring
  linarith [mul_nonneg aF1_3.le ab1456, mul_nonneg aF1_4.le ab1356, mul_pos aF1_5 aF8_1]

theorem exclw_RC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : chi24 x < 0) (h4 : 0 ≤ b2456 x) (h3 : b1456 x ≤ 0) : False := by
  have aF1_4 : 0 < 1 * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) := by
    have h := forced24 F hc 1 4 0 1 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab2456 : 0 ≤ 1 * (b2456 x) := by linarith
  have aF4_2 : 0 < -1 * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) := by
    have h := forced24 F hc 4 2 0 4 6 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have ab1456 : 0 ≤ -1 * (b1456 x) := by linarith
  have aF4_5 : 0 < -1 * (det3 (x 4 - x 0) (x 6 - x 0) (x 5 - x 0)) := by
    have h := forced24 F hc 4 5 0 4 6 (1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have aF5_4 : 0 < 1 * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) := by
    have h := forced24 F hc 5 4 1 2 6 (-1) (by decide) (by decide) (by decide) (by decide) (by norm_num [sig, sigs])
    linarith
  have gp : (1) * (det3 (x 1 - x 0) (x 6 - x 0) (x 4 - x 0)) * (b2456 x) + (1) * (det3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)) * (b1456 x) + (-1) * (det3 (x 4 - x 0) (x 6 - x 0) (x 5 - x 0)) * (det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)) = 0 := by
    simp only [b1456, b2456, det3_expand, PiLp.sub_apply]; ring
  linarith [mul_nonneg aF1_4.le ab2456, mul_nonneg aF4_2.le ab1456, mul_pos aF4_5 aF5_4]

theorem exclw_R1' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h1 : 0 ≤ b1245 x)
    (h0 : 0 ≤ b1234 x) : False :=
  exclw_R1 (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show det3 _ _ _ ≤ 0; rw [mdet24]; exact neg_nonpos.mpr h1)
    (by show det3 _ _ _ ≤ 0; rw [mdet24]; exact neg_nonpos.mpr h0)

theorem exclw_RA' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h4 : 0 ≤ b2456 x)
    (h1 : 0 ≤ b1245 x) : False :=
  exclw_RA (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show det3 _ _ _ ≤ 0; rw [mdet24]; exact neg_nonpos.mpr h4)
    (by show det3 _ _ _ ≤ 0; rw [mdet24]; exact neg_nonpos.mpr h1)

theorem exclw_RB' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h3 : 0 ≤ b1456 x)
    (h2 : b1356 x ≤ 0) : False :=
  exclw_RB (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show det3 _ _ _ ≤ 0; rw [mdet24]; exact neg_nonpos.mpr h3)
    (by show 0 ≤ det3 _ _ _; rw [mdet24]; exact neg_nonneg.mpr h2)

theorem exclw_RC' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hc : 0 < chi24 x) (h4 : b2456 x ≤ 0)
    (h3 : 0 ≤ b1456 x) : False :=
  exclw_RC (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc)
    (by show 0 ≤ det3 _ _ _; rw [mdet24]; exact neg_nonneg.mpr h4)
    (by show det3 _ _ _ ≤ 0; rw [mdet24]; exact neg_nonpos.mpr h3)

/-- Letter of a bracket in a class with possible zeros: `some true` = `p`, `some false` = `m`, `none` = `z` (the
bracket is `0`). -/
def sgz : Option Bool → ℝ → Prop
  | some b, r => sg b r
  | none, r => r = 0

/-- Reversing the orientation reverses `p`/`m` and keeps `z`. -/
def flipz : Option Bool → Option Bool
  | some b => some (!b)
  | none => none

/-- The class with letters `s0 … s4` (`z` allowed) in the reference orientation `[0126] < 0`, or its mirror. -/
def clsz24 (x : Fin 7 → ℝ³) (s0 s1 s2 s3 s4 : Option Bool) : Prop :=
  (chi24 x < 0 ∧ sgz s0 (b1234 x) ∧ sgz s1 (b1245 x) ∧ sgz s2 (b1356 x) ∧ sgz s3 (b1456 x) ∧ sgz s4 (b2456 x)) ∨
    (0 < chi24 x ∧ sgz (flipz s0) (b1234 x) ∧ sgz (flipz s1) (b1245 x) ∧ sgz (flipz s2) (b1356 x) ∧
      sgz (flipz s3) (b1456 x) ∧ sgz (flipz s4) (b2456 x))

/-- The 18 one-zero classes (zero bracket, four nonzero) that occur. -/
def Cls18 (x : Fin 7 → ℝ³) : Prop :=
  clsz24 x none (some true) (some false) (some false) (some false) ∨
  clsz24 x none (some true) (some false) (some true) (some true) ∨
  clsz24 x none (some true) (some true) (some true) (some false) ∨
  clsz24 x none (some true) (some false) (some true) (some false) ∨
  clsz24 x none (some true) (some true) (some true) (some true) ∨
  clsz24 x (some true) none (some false) (some true) (some true) ∨
  clsz24 x (some true) none (some true) (some true) (some true) ∨
  clsz24 x (some true) (some true) none (some true) (some true) ∨
  clsz24 x (some true) (some true) none (some true) (some false) ∨
  clsz24 x (some true) (some false) none (some true) (some true) ∨
  clsz24 x (some false) (some true) none (some true) (some true) ∨
  clsz24 x (some false) (some true) none (some true) (some false) ∨
  clsz24 x (some true) (some true) (some false) none (some false) ∨
  clsz24 x (some false) (some true) (some false) none (some false) ∨
  clsz24 x (some true) (some true) (some false) (some true) none ∨
  clsz24 x (some true) (some true) (some true) (some true) none ∨
  clsz24 x (some false) (some true) (some false) (some true) none ∨
  clsz24 x (some false) (some true) (some true) (some true) none

/-- The 8 two-zero classes that occur. -/
def Cls8 (x : Fin 7 → ℝ³) : Prop :=
  clsz24 x none (some true) none (some true) (some true) ∨
  clsz24 x none (some true) none (some true) (some false) ∨
  clsz24 x none (some true) (some false) none (some false) ∨
  clsz24 x none (some true) (some false) (some true) none ∨
  clsz24 x none (some true) (some true) (some true) none ∨
  clsz24 x (some true) none none (some true) (some true) ∨
  clsz24 x (some true) (some true) none (some true) none ∨
  clsz24 x (some false) (some true) none (some true) none

set_option hygiene false in
macro "zexh_tac" : tactic => `(tactic| (
  rcases lt_or_gt_of_ne (chi24_ne F) with hc | hc
  all_goals first
  | exact (exclw_R1 F hc (by linarith) (by linarith)).elim | exact (exclw_RA F hc (by linarith) (by linarith)).elim
  | exact (exclw_RB F hc (by linarith) (by linarith)).elim | exact (exclw_RC F hc (by linarith) (by linarith)).elim
  | exact (exclw_R1' F hc (by linarith) (by linarith)).elim | exact (exclw_RA' F hc (by linarith) (by linarith)).elim
  | exact (exclw_RB' F hc (by linarith) (by linarith)).elim | exact (exclw_RC' F hc (by linarith) (by linarith)).elim
  | skip))

theorem cls18_z1234 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz : b1234 x = 0) (h1 : b1245 x ≠ 0)
    (h2 : b1356 x ≠ 0) (h3 : b1456 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls18 x := by
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;> rcases lt_or_gt_of_ne h2 with a2 | a2 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;> rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  zexh_tac <;>
  simp only [Cls18, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hz, hc, a1, a2, a3, a4, and_self, true_or,
      or_true, and_true, lt_self_iff_false]

theorem cls18_z1245 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz : b1245 x = 0) (h0 : b1234 x ≠ 0) (h2 : b1356 x ≠ 0) (h3 : b1456 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls18 x := by
  rcases lt_or_gt_of_ne h0 with a0 | a0 <;>
  rcases lt_or_gt_of_ne h2 with a2 | a2 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  zexh_tac <;>
  simp only [Cls18, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hz, hc, a0, a2, a3, a4, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls18_z1356 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz : b1356 x = 0) (h0 : b1234 x ≠ 0) (h1 : b1245 x ≠ 0) (h3 : b1456 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls18 x := by
  rcases lt_or_gt_of_ne h0 with a0 | a0 <;>
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  zexh_tac <;>
  simp only [Cls18, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hz, hc, a0, a1, a3, a4, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls18_z1456 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz : b1456 x = 0) (h0 : b1234 x ≠ 0) (h1 : b1245 x ≠ 0) (h2 : b1356 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls18 x := by
  rcases lt_or_gt_of_ne h0 with a0 | a0 <;>
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h2 with a2 | a2 <;>
  rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  zexh_tac <;>
  simp only [Cls18, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hz, hc, a0, a1, a2, a4, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls18_z2456 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz : b2456 x = 0) (h0 : b1234 x ≠ 0) (h1 : b1245 x ≠ 0) (h2 : b1356 x ≠ 0) (h3 : b1456 x ≠ 0) : Cls18 x := by
  rcases lt_or_gt_of_ne h0 with a0 | a0 <;>
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h2 with a2 | a2 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  zexh_tac <;>
  simp only [Cls18, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hz, hc, a0, a1, a2, a3, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

/-- **Class exhaustion with one zero**: exactly one class bracket vanishes, the other four do not: the sign vector (in
either orientation) is one of the 18 realised one-zero classes. -/
theorem cls18_of_one_zero {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h : (b1234 x = 0 ∧ b1245 x ≠ 0 ∧ b1356 x ≠ 0 ∧ b1456 x ≠ 0 ∧ b2456 x ≠ 0) ∨
      (b1234 x ≠ 0 ∧ b1245 x = 0 ∧ b1356 x ≠ 0 ∧ b1456 x ≠ 0 ∧ b2456 x ≠ 0) ∨
      (b1234 x ≠ 0 ∧ b1245 x ≠ 0 ∧ b1356 x = 0 ∧ b1456 x ≠ 0 ∧ b2456 x ≠ 0) ∨
      (b1234 x ≠ 0 ∧ b1245 x ≠ 0 ∧ b1356 x ≠ 0 ∧ b1456 x = 0 ∧ b2456 x ≠ 0) ∨
      (b1234 x ≠ 0 ∧ b1245 x ≠ 0 ∧ b1356 x ≠ 0 ∧ b1456 x ≠ 0 ∧ b2456 x = 0)) : Cls18 x := by
  rcases h with ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩
  exacts [cls18_z1234 F a b c d e, cls18_z1245 F b a c d e, cls18_z1356 F c a b d e, cls18_z1456 F d a b c e,
    cls18_z2456 F e a b c d]

/-! ### Two zero brackets: five pairs are impossible (Grassmann-Plücker relations) -/

/-- The bracket of four vertices, `[a b c d]`. -/
@[reducible] noncomputable def Bk (x : Fin 7 → ℝ³) (a b c d : Fin 7) : ℝ := det3 (x b - x a) (x c - x a) (x d - x a)

/-- The three-term Grassmann-Plücker relation. -/
theorem Bk_gp (x : Fin 7 → ℝ³) (a b c d e f : Fin 7) :
    Bk x a b c d * Bk x a b e f - Bk x a b c e * Bk x a b d f + Bk x a b c f * Bk x a b d e = 0 := by
  simp only [Bk, det3_expand, PiLp.sub_apply]; ring

theorem bk_eq_zero {B b : ℝ} (s : ℝ) (h : b = 0) (e : B = s * b) : B = 0 := by rw [e, h, mul_zero]

/-- A forced bracket (a facet's reference triple and a vertex off it) is nonzero, in either orientation. -/
theorem fne24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v i j k : Fin 7)
    (hv : v ∉ s0x_S24 t) (hi : fA t = i) (hj : fB t = j) (hk : fC t = k) : Bk x i j k v ≠ 0 := by
  intro h
  rcases lt_or_gt_of_ne (chi24_ne F) with hc | hc
  · have := forced24 F hc t v i j k _ hv hi hj hk rfl
    rw [show det3 (x j - x i) (x k - x i) (x v - x i) = 0 from h, mul_zero] at this
    exact lt_irrefl _ this
  · have := forced24 (mirFac F) (by show det3 _ _ _ < 0; rw [mdet24]; exact neg_neg_of_pos hc) t v i j k _ hv hi hj hk rfl
    have h' : det3 (mir (x j) - mir (x i)) (mir (x k) - mir (x i)) (mir (x v) - mir (x i)) = 0 := by
      rw [mdet24]; rw [show det3 (x j - x i) (x k - x i) (x v - x i) = 0 from h, neg_zero]
    rw [show det3 ((fun i => mir (x i)) j - (fun i => mir (x i)) i) ((fun i => mir (x i)) k - (fun i => mir (x i)) i)
      ((fun i => mir (x i)) v - (fun i => mir (x i)) i) = 0 from h', mul_zero] at this
    exact lt_irrefl _ this

theorem fneB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v i j k : Fin 7)
    (hv : v ∉ s0x_S24 t) (hi : fA t = i) (hj : fB t = j) (hk : fC t = k) (a b c d : Fin 7) (s : ℝ) (hs : s ≠ 0)
    (e : Bk x a b c d = s * Bk x i j k v) : Bk x a b c d ≠ 0 := by
  rw [e]; exact mul_ne_zero hs (fne24 F t v i j k hv hi hj hk)


/-- Three vectors orthogonal to a nonzero `N` are coplanar. -/
theorem det3_zero_of_inner (N u v w : ℝ³) (hN : N ≠ 0) (hu : ⟪N, u⟫ = 0) (hv : ⟪N, v⟫ = 0) (hw : ⟪N, w⟫ = 0) :
    det3 u v w = 0 := by
  have e : ∀ z : ℝ³, ⟪N, z⟫ = N 0 * z 0 + N 1 * z 1 + N 2 * z 2 := by
    intro z; simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
  rw [e] at hu hv hw
  have h3 : N 0 ≠ 0 ∨ N 1 ≠ 0 ∨ N 2 ≠ 0 := by
    by_contra h; simp only [not_or, not_not] at h; apply hN; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  simp only [det3_expand]
  rcases h3 with h | h | h
  · apply mul_left_cancel₀ h
    linear_combination (v 1 * w 2 - v 2 * w 1) * hu + (w 1 * u 2 - w 2 * u 1) * hv + (u 1 * v 2 - u 2 * v 1) * hw
  · apply mul_left_cancel₀ h
    linear_combination (v 2 * w 0 - v 0 * w 2) * hu + (w 2 * u 0 - w 0 * u 2) * hv + (u 2 * v 0 - u 0 * v 2) * hw
  · apply mul_left_cancel₀ h
    linear_combination (v 0 * w 1 - v 1 * w 0) * hu + (w 0 * u 1 - w 1 * u 0) * hv + (u 0 * v 1 - u 1 * v 0) * hw

/-- The quadrilateral facet `0345` is planar: `[0345] = 0`. -/
theorem bkD {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Bk x 0 3 4 5 = 0 := by
  have z : ∀ a : Fin 7, a ∈ s0x_S24 3 → ⟪F.N 3, x a - x 0⟫ = 0 := by
    intro a ha; rw [F.inner_sub, F.zero 3 a ha, F.zero 3 0 (by decide), sub_zero]
  have off : ⟪F.N 3, x 1 - x 0⟫ < 0 := by
    rw [F.inner_sub, F.zero 3 0 (by decide), sub_zero]; exact F.neg 3 1 (by decide)
  have hN : F.N 3 ≠ 0 := by
    intro h; rw [h] at off; simp at off
  exact det3_zero_of_inner (F.N 3) _ _ _ hN (z 3 (by decide)) (z 4 (by decide)) (z 5 (by decide))
theorem imp_1234_1245 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz1 : b1234 x = 0) (hz2 : b1245 x = 0) : False := by
  have g := Bk_gp x 1 2 0 3 4 5
  have z0 : Bk x 1 2 4 5 = 0 := bk_eq_zero (1) hz2 (by simp only [Bk, b1245, det3_expand, PiLp.sub_apply]; ring)
  have z1 : Bk x 1 2 3 4 = 0 := bk_eq_zero (1) hz1 (by simp only [Bk, b1234, det3_expand, PiLp.sub_apply]; ring)
  have n0 : Bk x 1 2 0 4 ≠ 0 := fneB F 0 4 0 1 2 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  have n1 : Bk x 1 2 3 5 ≠ 0 := fneB F 6 1 2 3 5 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (-1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  rw [z0, z1] at g
  exact mul_ne_zero n0 n1 (by linarith)

theorem imp_1245_2456 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz1 : b1245 x = 0) (hz2 : b2456 x = 0) : False := by
  have g := Bk_gp x 2 4 0 1 5 6
  have z0 : Bk x 2 4 5 6 = 0 := bk_eq_zero (1) hz2 (by simp only [Bk, b2456, det3_expand, PiLp.sub_apply]; ring)
  have z1 : Bk x 2 4 1 5 = 0 := bk_eq_zero (1) hz1 (by simp only [Bk, b1245, det3_expand, PiLp.sub_apply]; ring)
  have n0 : Bk x 2 4 0 5 ≠ 0 := fneB F 2 4 0 2 5 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (-1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  have n1 : Bk x 2 4 1 6 ≠ 0 := fneB F 5 4 1 2 6 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (-1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  rw [z0, z1] at g
  exact mul_ne_zero n0 n1 (by linarith)

theorem imp_1456_2456 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz1 : b1456 x = 0) (hz2 : b2456 x = 0) : False := by
  have g := Bk_gp x 4 6 0 1 2 5
  have z0 : Bk x 4 6 2 5 = 0 := bk_eq_zero (-1) hz2 (by simp only [Bk, b2456, det3_expand, PiLp.sub_apply]; ring)
  have z1 : Bk x 4 6 1 5 = 0 := bk_eq_zero (-1) hz1 (by simp only [Bk, b1456, det3_expand, PiLp.sub_apply]; ring)
  have n0 : Bk x 4 6 0 5 ≠ 0 := fneB F 4 5 0 4 6 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  have n1 : Bk x 4 6 1 2 ≠ 0 := fneB F 5 4 1 2 6 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (-1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  rw [z0, z1] at g
  exact mul_ne_zero n0 n1 (by linarith)

theorem imp_1356_1456 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz1 : b1356 x = 0) (hz2 : b1456 x = 0) : False := by
  have g := Bk_gp x 1 6 0 3 4 5
  have z0 : Bk x 1 6 4 5 = 0 := bk_eq_zero (1) hz2 (by simp only [Bk, b1456, det3_expand, PiLp.sub_apply]; ring)
  have z1 : Bk x 1 6 3 5 = 0 := bk_eq_zero (1) hz1 (by simp only [Bk, b1356, det3_expand, PiLp.sub_apply]; ring)
  have n0 : Bk x 1 6 0 5 ≠ 0 := fneB F 1 5 0 1 6 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  have n1 : Bk x 1 6 3 4 ≠ 0 := fneB F 8 1 3 4 6 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (-1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  rw [z0, z1] at g
  exact mul_ne_zero n0 n1 (by linarith)


theorem imp_1245_1456 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz1 : b1245 x = 0) (hz2 : b1456 x = 0) : False := by
  have g := Bk_gp x 1 5 4 2 6 0
  have z0 : Bk x 1 5 4 2 = 0 := bk_eq_zero (-1) hz1 (by simp only [Bk, b1245, det3_expand, PiLp.sub_apply]; ring)
  have z1 : Bk x 1 5 4 6 = 0 := bk_eq_zero (-1) hz2 (by simp only [Bk, b1456, det3_expand, PiLp.sub_apply]; ring)
  have n0 : Bk x 1 5 2 6 ≠ 0 := fneB F 5 5 1 2 6 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  rw [z0, z1] at g
  have z2 : Bk x 1 5 4 0 = 0 := by
    have : Bk x 1 5 4 0 * Bk x 1 5 2 6 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n0
  have g2 := Bk_gp x 0 4 5 3 1 2
  have z3 : Bk x 0 4 5 1 = 0 := bk_eq_zero (1) z2 (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  have z4 : Bk x 0 4 5 3 = 0 := bk_eq_zero (1) (bkD F) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  have n1 : Bk x 0 4 5 2 ≠ 0 := fneB F 2 4 0 2 5 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (-1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  have n2 : Bk x 0 4 3 1 ≠ 0 := fneB F 3 1 0 3 4 (by decide) (by decide) (by decide) (by decide) _ _ _ _ (-1) (by norm_num) (by simp only [Bk, det3_expand, PiLp.sub_apply]; ring)
  rw [z3, z4] at g2
  exact mul_ne_zero n1 n2 (by linarith)

/-- The 3-zero class `[1234] = [1356] = [2456] = 0` with `[1245] > 0`, `[1456] > 0` (reference orientation). -/
def Cls3 (x : Fin 7 → ℝ³) : Prop := clsz24 x none (some true) none (some true) none

theorem cls8_z13 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz0 : b1234 x = 0) (hz2 : b1356 x = 0) (h1 : b1245 x ≠ 0) (h3 : b1456 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls8 x := by
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  zexh_tac <;>
  simp only [Cls8, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hc, hz0, hz2, a1, a3, a4, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls8_z14 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz0 : b1234 x = 0) (hz3 : b1456 x = 0) (h1 : b1245 x ≠ 0) (h2 : b1356 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls8 x := by
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h2 with a2 | a2 <;>
  rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  zexh_tac <;>
  simp only [Cls8, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hc, hz0, hz3, a1, a2, a4, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls8_z15 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz0 : b1234 x = 0) (hz4 : b2456 x = 0) (h1 : b1245 x ≠ 0) (h2 : b1356 x ≠ 0) (h3 : b1456 x ≠ 0) : Cls8 x := by
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h2 with a2 | a2 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  zexh_tac <;>
  simp only [Cls8, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hc, hz0, hz4, a1, a2, a3, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls8_z23 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz1 : b1245 x = 0) (hz2 : b1356 x = 0) (h0 : b1234 x ≠ 0) (h3 : b1456 x ≠ 0) (h4 : b2456 x ≠ 0) : Cls8 x := by
  rcases lt_or_gt_of_ne h0 with a0 | a0 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  rcases lt_or_gt_of_ne h4 with a4 | a4 <;>
  zexh_tac <;>
  simp only [Cls8, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hc, hz1, hz2, a0, a3, a4, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls8_z35 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz2 : b1356 x = 0) (hz4 : b2456 x = 0) (h0 : b1234 x ≠ 0) (h1 : b1245 x ≠ 0) (h3 : b1456 x ≠ 0) : Cls8 x := by
  rcases lt_or_gt_of_ne h0 with a0 | a0 <;>
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  zexh_tac <;>
  simp only [Cls8, clsz24, sgz, flipz, sg, Bool.not_true, Bool.not_false, hc, hz2, hz4, a0, a1, a3, and_self,
      true_or, or_true, and_true, lt_self_iff_false]

theorem cls3_z024 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hz0 : b1234 x = 0) (hz2 : b1356 x = 0) (hz4 : b2456 x = 0) (h1 : b1245 x ≠ 0) (h3 : b1456 x ≠ 0) : Cls3 x := by
  rcases lt_or_gt_of_ne h1 with a1 | a1 <;>
  rcases lt_or_gt_of_ne h3 with a3 | a3 <;>
  zexh_tac <;>
  simp only [Cls3, clsz24, sgz, flipz, sg, Bool.not_true, hc, hz0, hz2, hz4, a1, a3, and_self,
      true_or, or_true, and_true]

/-- **Zero split**: if some class bracket vanishes, the sign vector is one of the 18 one-zero classes, one of the 8
two-zero classes, or the three-zero class `Cls3` (`[1234] = [1356] = [2456] = 0`, which the pair argument does not
exclude). -/
theorem zero_split {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h : b1234 x = 0 ∨ b1245 x = 0 ∨ b1356 x = 0 ∨ b1456 x = 0 ∨ b2456 x = 0) :
    Cls18 x ∨ Cls8 x ∨ Cls3 x := by
  by_cases e0 : b1234 x = 0 <;> by_cases e1 : b1245 x = 0 <;> by_cases e2 : b1356 x = 0 <;>
  by_cases e3 : b1456 x = 0 <;> by_cases e4 : b2456 x = 0 <;>
  first
  | exact (imp_1234_1245 F ‹_› ‹_›).elim | exact (imp_1245_2456 F ‹_› ‹_›).elim
  | exact (imp_1456_2456 F ‹_› ‹_›).elim | exact (imp_1356_1456 F ‹_› ‹_›).elim
  | exact (imp_1245_1456 F ‹_› ‹_›).elim
  | exact Or.inr (Or.inr (cls3_z024 F ‹_› ‹_› ‹_› ‹_› ‹_›))
  | exact Or.inr (Or.inl (cls8_z13 F ‹_› ‹_› ‹_› ‹_› ‹_›))
  | exact Or.inr (Or.inl (cls8_z14 F ‹_› ‹_› ‹_› ‹_› ‹_›))
  | exact Or.inr (Or.inl (cls8_z15 F ‹_› ‹_› ‹_› ‹_› ‹_›))
  | exact Or.inr (Or.inl (cls8_z23 F ‹_› ‹_› ‹_› ‹_› ‹_›))
  | exact Or.inr (Or.inl (cls8_z35 F ‹_› ‹_› ‹_› ‹_› ‹_›))
  | exact Or.inl (cls18_z1234 F ‹_› ‹_› ‹_› ‹_› ‹_›)
  | exact Or.inl (cls18_z1245 F ‹_› ‹_› ‹_› ‹_› ‹_›)
  | exact Or.inl (cls18_z1356 F ‹_› ‹_› ‹_› ‹_› ‹_›)
  | exact Or.inl (cls18_z1456 F ‹_› ‹_› ‹_› ‹_› ‹_›)
  | exact Or.inl (cls18_z2456 F ‹_› ‹_› ‹_› ‹_› ‹_›)
  | (exfalso; tauto)


/-- Off the residual, one of the ten closed classes holds off `OB1`: Rupert. -/
theorem isRupert_of_not_resid24_wide {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : ¬ Resid24Wide x) :
    IsRupert (univ.image x) := by
  simp only [Resid24Wide, not_or] at h
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
346`, the skeleton's `hR`), the points are Rupert or `Resid24Wide x` holds. -/
theorem rupert_or_resid24_wide {x : Fin 7 → ℝ³} (fA fB fC fD fE fF fG fH fI : ℝ³ →ᵃ[ℝ] ℝ)
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
    IsRupert (univ.image x) ∨ Resid24Wide x := by
  by_cases hr : Resid24Wide x
  · exact Or.inr hr
  refine Or.inl (isRupert_of_not_resid24_wide (mkFac24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] ?_) hr)
  intro t i
  fin_cases t
  exacts [hA i, hB i, hF i, hG i, hE i, hC i, hH i, hD i, hI i]

end Minimality.T24

