module

public import Minimality.Type24OffOB1T234

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the T234 view with every facet pattern of the free letters (job OSPEC18)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2f.  On the B2 branch `T234BrL` the depth poset of the T234 view
`(t234b, x 4 - x 3, x 5 - x 6)` is fixed and derived (`t234_depths`, `t234_derived`): `6 < 3 < {2, 4} < {0, 1, 5}`
(`z2 = z3 = z4`, `z6 < z2 < z0, z1, z5` at level 1; `z3 < z4`, `z3 < z2` at level 2).  The facets `0345 235` are up,
and `126 236 346` are decided by `t234C` and `X6`.  A lex cell (`LexAny`) needs only the signs of the facets on its rim
edges (`S0xCycUD`), so for each regime of `(t234C, X6)` the cells of the view are the rims whose edge facets have the
required signs and whose depth sequence is `RobUniLex` for every order extending the poset.  The combinatorial census
(nopert229 tools/genleaves/runs/ospec18/rims.cc: all 120 RobUniLex rim certificates of the facet graph) gives, for the
free letters `012 016 025 046`:

* cone (`t234C ≥ 0`, `X6 ≥ 0`): a cell iff `046` down and not (`012 016 025` all up); new rim `0 4 3 2 5` (`025` down);
  moreover `016` and `046` are DERIVED there (`t234_dn1_of_cone`, `t234_dn4_of_cone`, from the tangent-cone identity
  `t234_cone_id`: `n234` is the combination `t234C |E|² (P0 - x6) + X6 (x2 - x6)` of two tie-section chords from `x 6`,
  so every facet through `6` is down), leaving only special positions;
* `t234C < 0`: a cell iff `046` down and (`012` up or `016` up); new rim `0 4 3 6` (`016` up);
* `X6 < 0`: a cell unless `012` down, `016` up, `025` down and `046` up; new rims `0 4 6 3 2 5`, `1 2 3 6`,
  `0 5 2 3 6`, `0 1 6 3 2`.

`T234RedN` is that condition (thirteen rims, `lexAny_of_t234RedN`); it is implied by `T234RedM` (`t234RedN_of_M`),
so the residue `Q45ResWN` / `OpenSpecialN` is contained in `Q45ResWM` / implied by `OpenSpecialM`.
-/

namespace Minimality.T24.OSpec

section T234N
open Minimality.LexCell

variable {x : Fin 7 → ℝ³}

/-- Rim `0 2 3 4` with only its edge facets: `025 0345 235` up, `012 046 236 346` down (no `016`, `126`). -/
def DnTDN : Finset (Fin 9) := {0, 4, 7, 8}
theorem rimTDN_cyc : S0xCycUD s0x_S24 rimDB UTD DnTDN := by decide

/-- Rim `5 0 4 3 2` (`025 046 236 346` down; cone). -/
def rimTJ : ZMod 5 → Fin 7 := ![5, 0, 4, 3, 2]
def UTJ : Finset (Fin 9) := {3, 6}
def DnTJ : Finset (Fin 9) := {2, 4, 7, 8}
theorem rimTJ_cyc : S0xCycUD s0x_S24 rimTJ UTJ DnTJ := by decide
theorem rimTJ_inj : Function.Injective rimTJ := by decide

/-- Rim `0 4 3 6` (`016 236` up, `046 346` down; `t234C < 0`). -/
def rimTK : ZMod 4 → Fin 7 := ![0, 4, 3, 6]
def UTK : Finset (Fin 9) := {1, 3, 7}
def DnTK : Finset (Fin 9) := {4, 8}
theorem rimTK_cyc : S0xCycUD s0x_S24 rimTK UTK DnTK := by decide
theorem rimTK_inj : Function.Injective rimTK := by decide

/-- Rim `0 4 6 3 2 5` (`346` up, `025 046 236` down; `X6 < 0`). -/
def rimTL : ZMod 6 → Fin 7 := ![0, 4, 6, 3, 2, 5]
def UTL : Finset (Fin 9) := {3, 6, 8}
def DnTL : Finset (Fin 9) := {2, 4, 7}
theorem rimTL_cyc : S0xCycUD s0x_S24 rimTL UTL DnTL := by decide
theorem rimTL_inj : Function.Injective rimTL := by decide

/-- Rim `1 2 3 6` (`012 016 235 346` up, `126 236` down; `X6 < 0`). -/
def rimTM : ZMod 4 → Fin 7 := ![1, 2, 3, 6]
def UTM : Finset (Fin 9) := {0, 1, 6, 8}
def DnTM : Finset (Fin 9) := {5, 7}
theorem rimTM_cyc : S0xCycUD s0x_S24 rimTM UTM DnTM := by decide
theorem rimTM_inj : Function.Injective rimTM := by decide

/-- Rim `5 0 6 3 2` (`0345 046 235 346` up, `016 025 236` down; `X6 < 0`). -/
def rimTN : ZMod 5 → Fin 7 := ![5, 0, 6, 3, 2]
def UTN : Finset (Fin 9) := {3, 4, 6, 8}
def DnTN : Finset (Fin 9) := {1, 2, 7}
theorem rimTN_cyc : S0xCycUD s0x_S24 rimTN UTN DnTN := by decide
theorem rimTN_inj : Function.Injective rimTN := by decide

/-- Rim `0 1 6 3 2` (`016 025 235 346` up, `012 126 236` down; `X6 < 0`). -/
def rimTO : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 2]
def UTO : Finset (Fin 9) := {1, 2, 6, 8}
def DnTO : Finset (Fin 9) := {0, 5, 7}
theorem rimTO_cyc : S0xCycUD s0x_S24 rimTO UTO DnTO := by decide
theorem rimTO_inj : Function.Injective rimTO := by decide

/-- A rim certificate of the T234 view at `b` is a lex cell. -/
theorem t234_cell (F : S0xFac 9 s0x_S24 x) {b : ℝ³} {k : ℕ} [NeZero k] (c : ZMod k → Fin 7)
    (U Dn : Finset (Fin 9)) (hk : 4 ≤ k) (hc : Function.Injective c) (hcyc : S0xCycUD s0x_S24 c U Dn)
    (hU : ∀ t ∈ U, T234Up F b t) (hD : ∀ t ∈ Dn, T234Dn F b t) (hR : RobUniLex (t234Z x b c)) : Gen.LexAny F :=
  ⟨k, inferInstance, c, U, Dn, b, x 4 - x 3, x 5 - x 6, hk, hc, hcyc, hU, hD, hR⟩

/-! ### The cone: every facet through `6` is down (the tangent cone of the tie section at `x 6`) -/

/-- **The tangent-cone identity** (tie `⟪E, g⟫ = ⟪E, w⟫`; scalar Binet-Cauchy, `t234_gram`): with `n = E × g`,
`⟪N, n⟫ ⟪w - g, n⟫ = -(C (τ ⟪N, E⟫ - |E|² ⟪N, w⟫) + X6 ⟪N, g - w⟫)`, `C = ⟪g, g - w⟫`, `τ = ⟪E, g⟫`,
`X6 = |E|² ⟪w, g⟫ - ⟪E, w⟫ ⟪E, g⟫`.  For `E = x4 - x3`, `g = x2 - x3`, `w = x6 - x3` this is `n234` written as the
combination `C |E|² (P0 - x6) + X6 (x2 - x6)` of two chords of the tie section from `x 6` (`P0` = the point of the
edge `3 4` at the tie height). -/
theorem t234_cone_id (N E g w : ℝ³) (htie : ⟪E, g⟫ = ⟪E, w⟫) :
    ⟪N, cross E g⟫ * ⟪w - g, cross E g⟫ =
      -(⟪g, g - w⟫ * (⟪E, g⟫ * ⟪N, E⟫ - ⟪E, E⟫ * ⟪N, w⟫) + (⟪E, E⟫ * ⟪w, g⟫ - ⟪E, w⟫ * ⟪E, g⟫) * ⟪N, g - w⟫) := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply] at htie ⊢
  linear_combination ((g 0 * g 0 + g 1 * g 1 + g 2 * g 2) * (N 0 * E 0 + N 1 * E 1 + N 2 * E 2) -
    (E 0 * g 0 + E 1 * g 1 + E 2 * g 2) * (N 0 * w 0 + N 1 * w 1 + N 2 * w 2)) * htie

/-- The identity for a facet `t` through `x 6` at `t234b` (tie `h2 = h6`): `⟪N t, b⟫ ⟪x6 - x2, b⟫ = -(t234C (τ f(x4)
+ (|E|² - τ) f(x3)) + X6 f(x2))`. -/
theorem t234_cone_prod (F : S0xFac 9 s0x_S24 x) (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫) {t : Fin 9}
    (h6 : (6 : Fin 7) ∈ s0x_S24 t) :
    ⟪F.N t, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ =
      -(t234C x * (⟪x 4 - x 3, x 2 - x 3⟫ * F.f t (x 4) +
          (⟪x 4 - x 3, x 4 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫) * F.f t (x 3)) + t234X6 x * F.f t (x 2)) := by
  have ht : ⟪x 4 - x 3, x 2 - x 3⟫ = ⟪x 4 - x 3, x 6 - x 3⟫ := by
    simp only [t234_inner3, PiLp.sub_apply] at htie ⊢; linear_combination -htie
  have hI := t234_cone_id (F.N t) (x 4 - x 3) (x 2 - x 3) (x 6 - x 3) ht
  have e1 : (x 6 - x 3) - (x 2 - x 3) = x 6 - x 2 := by abel
  have e2 : (x 2 - x 3) - (x 6 - x 3) = x 2 - x 6 := by abel
  rw [e1, e2, ← n234_eq, F.inner_sub t 4 3, F.inner_sub t 6 3, F.inner_sub t 2 6, F.zero t 6 h6] at hI
  rw [t234b_prod, hI, t234C, t234X6]
  ring

/-- On the B2 branch the tie section is not degenerate at the cone corner: `t234C = 0` and `X6 = 0` do not both hold
(`t234_cone_id` with `N = n234` would put `x 6` on the plane `2 3 4`). -/
theorem t234_cone_pos (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) (hX : 0 ≤ t234X6 x) (hc : 0 ≤ t234C x) :
    0 < t234X6 x ∨ 0 < t234C x := by
  have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
    obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := hB; exact htie.trans h56
  have ht : ⟪x 4 - x 3, x 2 - x 3⟫ = ⟪x 4 - x 3, x 6 - x 3⟫ := by
    simp only [t234_inner3, PiLp.sub_apply] at htie26 ⊢; linear_combination -htie26
  by_contra hn
  have hX0 : t234X6 x = 0 := le_antisymm (not_lt.mp fun h => hn (Or.inl h)) hX
  have hc0 : t234C x = 0 := le_antisymm (not_lt.mp fun h => hn (Or.inr h)) hc
  have hI := t234_cone_id (n234 x) (x 4 - x 3) (x 2 - x 3) (x 6 - x 3) ht
  have e1 : (x 6 - x 3) - (x 2 - x 3) = x 6 - x 2 := by abel
  rw [e1, ← n234_eq] at hI
  have hC' : ⟪x 2 - x 3, (x 2 - x 3) - (x 6 - x 3)⟫ = 0 := by
    have e2 : (x 2 - x 3) - (x 6 - x 3) = x 2 - x 6 := by abel
    rw [e2]; exact hc0
  have hX' : ⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 6 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 6 - x 3⟫ * ⟪x 4 - x 3, x 2 - x 3⟫ = 0 :=
    hX0
  rw [hC', hX', zero_mul, zero_mul, add_zero, neg_zero] at hI
  have hq := t234_z6 F hB.1
  have hq' : ⟪x 6 - x 2, n234 x⟫ ≠ 0 := by
    rcases t234b_cases x with e | e <;> rw [e] at hq
    · exact hq.ne
    · rw [inner_neg_right] at hq; intro h0; rw [h0, neg_zero] at hq; exact lt_irrefl _ hq
  rcases mul_eq_zero.mp hI with h | h
  · exact hq' (by rw [inner_self_eq_zero.mp h, inner_zero_right])
  · exact hq' h

/-- **On the cone every facet through `x 6` with `C (τ f(x4) + (|E|² - τ) f(x3)) + X6 f(x2) < 0` is down at level 1.** -/
theorem t234_dn_of_cone (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) {t : Fin 9} (h6 : (6 : Fin 7) ∈ s0x_S24 t)
    (hneg : t234C x * (⟪x 4 - x 3, x 2 - x 3⟫ * F.f t (x 4) +
          (⟪x 4 - x 3, x 4 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫) * F.f t (x 3)) + t234X6 x * F.f t (x 2) < 0) :
    T234Dn F (t234b x) t := by
  have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
    obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := hB; exact htie.trans h56
  have hp := t234_cone_prod F htie26 h6
  have hq := t234_z6 F hB.1
  left
  have : 0 < ⟪F.N t, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ := by rw [hp]; linarith
  by_contra hn
  have h1 : 0 ≤ ⟪F.N t, t234b x⟫ := by linarith [not_lt.mp hn]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hq.le]

/-- The tie-section facts used below: `τ > 0` and `|E|² - τ = h5 - h4 ≥ 0` on `T234BrL`. -/
theorem t234_cone_tau (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) :
    0 < ⟪x 4 - x 3, x 2 - x 3⟫ ∧
      ⟪x 4 - x 3, x 4 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫ = ⟪x 5, x 3 - x 4⟫ - ⟪x 4, x 3 - x 4⟫ ∧
      0 ≤ ⟪x 5, x 3 - x 4⟫ - ⟪x 4, x 3 - x 4⟫ := by
  obtain ⟨htau, -, eg⟩ := t234_tau_eqs F hB.1
  obtain ⟨⟨⟨-, -, -, -, -, -, htie, -⟩, -, -⟩, h45⟩ := hB
  refine ⟨eg ▸ htau, ?_, by linarith⟩
  simp only [t234_inner3, PiLp.sub_apply] at htie ⊢; linear_combination htie

/-- **`016` is down at `t234b` on the whole cone** (`t234C ≥ 0`, `X6 ≥ 0`; `T234BrL`): the tie-section chords `x6 →
P0` and `x6 → x2` span the view and `016` misses `x 2`, `x 3`, `x 4`. -/
theorem t234_dn1_of_cone (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (hX : 0 ≤ t234X6 x) (hc : 0 ≤ t234C x) :
    T234Dn F (t234b x) 1 := by
  obtain ⟨htau, -, hd⟩ := t234_cone_tau F hB
  obtain ⟨-, he, -⟩ := t234_cone_tau F hB
  have f4 : F.f 1 (x 4) < 0 := F.neg 1 4 (by decide)
  have f3 : F.f 1 (x 3) < 0 := F.neg 1 3 (by decide)
  have f2 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  refine t234_dn_of_cone F hB.1 (by decide) ?_
  rw [he]
  have hA : ⟪x 4 - x 3, x 2 - x 3⟫ * F.f 1 (x 4) + (⟪x 5, x 3 - x 4⟫ - ⟪x 4, x 3 - x 4⟫) * F.f 1 (x 3) < 0 := by
    nlinarith [mul_neg_of_pos_of_neg htau f4, mul_nonpos_of_nonneg_of_nonpos hd f3.le]
  rcases t234_cone_pos F hB.1 hX hc with h | h
  · nlinarith [mul_neg_of_pos_of_neg h f2, mul_nonpos_of_nonneg_of_nonpos hc hA.le]
  · nlinarith [mul_neg_of_pos_of_neg h hA, mul_nonpos_of_nonneg_of_nonpos hX f2.le]

/-- **`046` is down at `t234b` on the cone** unless `X6 = 0` and `h4 = h5` (`P0 = x 4`, both chords from `x 6` then
lie in `046` or reach `x 4`): with `X6 > 0` by the chord to `x 2`, with `h4 < h5` by the chord to `P0`. -/
theorem t234_dn4_of_cone (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (hX : 0 ≤ t234X6 x) (hc : 0 ≤ t234C x)
    (h : 0 < t234X6 x ∨ ⟪x 4, x 3 - x 4⟫ < ⟪x 5, x 3 - x 4⟫) : T234Dn F (t234b x) 4 := by
  obtain ⟨-, he, hd⟩ := t234_cone_tau F hB
  have f4 : F.f 4 (x 4) = 0 := F.zero 4 4 (by decide)
  have f3 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  have f2 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
  refine t234_dn_of_cone F hB.1 (by decide) ?_
  rw [he, f4, mul_zero, zero_add]
  rcases h with h | h
  · nlinarith [mul_neg_of_pos_of_neg h f2, mul_nonpos_of_nonneg_of_nonpos hc
      (mul_nonpos_of_nonneg_of_nonpos hd f3.le)]
  · rcases t234_cone_pos F hB.1 hX hc with hX' | hc'
    · nlinarith [mul_neg_of_pos_of_neg hX' f2, mul_nonpos_of_nonneg_of_nonpos hc
        (mul_nonpos_of_nonneg_of_nonpos hd f3.le)]
    · have : (⟪x 5, x 3 - x 4⟫ - ⟪x 4, x 3 - x 4⟫) * F.f 4 (x 3) < 0 := mul_neg_of_pos_of_neg (by linarith) f3
      nlinarith [mul_neg_of_pos_of_neg hc' this, mul_nonpos_of_nonneg_of_nonpos hX f2.le]

/-- The `X6 < 0` letters (eight rims): every sign pattern of `012 016 025 046` except `012` down, `016` up, `025`
down, `046` up. -/
def T234RedNX {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (T234Dn F (t234b x) 2 ∧ T234Dn F (t234b x) 4) ∨
  (T234Up F (t234b x) 0 ∧ T234Dn F (t234b x) 1 ∧ T234Dn F (t234b x) 4) ∨
  (T234Dn F (t234b x) 0 ∧ T234Up F (t234b x) 2 ∧ T234Dn F (t234b x) 4) ∨
  (T234Up F (t234b x) 0 ∧ T234Up F (t234b x) 1) ∨
  (T234Dn F (t234b x) 1 ∧ T234Dn F (t234b x) 2 ∧ T234Up F (t234b x) 4) ∨
  (T234Up F (t234b x) 0 ∧ T234Dn F (t234b x) 1 ∧ T234Up F (t234b x) 4) ∨
  (T234Dn F (t234b x) 0 ∧ T234Dn F (t234b x) 1 ∧ T234Up F (t234b x) 2 ∧ T234Up F (t234b x) 4) ∨
  (T234Dn F (t234b x) 0 ∧ T234Up F (t234b x) 1 ∧ T234Up F (t234b x) 2)

/-- **The T234 letters with every facet pattern** on `T234BrL` (OSPEC18).  In the cone (`t234C ≥ 0`, `X6 ≥ 0`)
`016` and `046` are derived (`t234_dn1_of_cone`, `t234_dn4_of_cone`), so only the special positions are left: `046`
when `X6 = 0` and `h4 = h5`, and `126` at `t234C = 0` when `012` is up and `025` is not down (`012` up: rim `0 1 2 3 4`;
`012` down with `025` up: `0 2 3 4`; `025` down: `5 0 4 3 2`).  For `t234C < 0`: `046` down and (`012` up with `016`
down, or `016` up).  For `X6 < 0`: `T234RedNX`. -/
def T234RedN {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (0 ≤ t234X6 x → 0 ≤ t234C x →
      (0 < t234X6 x ∨ ⟪x 4, x 3 - x 4⟫ < ⟪x 5, x 3 - x 4⟫ ∨ T234Dn F (t234b x) 4) ∧
      ((T234Up F (t234b x) 0 ∧ (t234C x = 0 → T234Dn F (t234b x) 5)) ∨
        (T234Dn F (t234b x) 0 ∧ T234Up F (t234b x) 2) ∨ T234Dn F (t234b x) 2)) ∧
  (t234C x < 0 → T234Dn F (t234b x) 4 ∧
      ((T234Up F (t234b x) 0 ∧ T234Dn F (t234b x) 1) ∨ T234Up F (t234b x) 1)) ∧
  (t234X6 x < 0 → T234RedNX F)

/-- **The T234 view is a lex cell on the B2 branch for every admitted facet pattern** (thirteen rims). -/
theorem lexAny_of_t234RedN (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (h : T234RedN F) : Gen.LexAny F := by
  obtain ⟨hA, hBr, hC⟩ := h
  obtain ⟨t3, t4, h20, h21, h62, l34, l32⟩ := t234_depths F hB.1
  have h25 : ⟪x 2, t234b x⟫ < ⟪x 5, t234b x⟫ := by
    have := (t234_derived F hB.1.1).1; rw [inner_sub_left] at this; linarith
  have u3 : T234Up F (t234b x) 3 := Or.inl (t234_derived F hB.1.1).2.1
  have u6 := t234_up6 F hB.1
  have hb := t234b_cases x
  set b := t234b x with hbdef
  -- the rims and their `RobUniLex`
  have rimJ : RobUniLex (t234Z x b rimTJ) := by
    have e0 : rimTJ 0 = 5 := by decide
    have e1 : rimTJ 1 = 0 := by decide
    have e2 : rimTJ 2 = 4 := by decide
    have e3 : rimTJ 3 = 3 := by decide
    have e4 : rimTJ 4 = 2 := by decide
    apply robUniLex_five_e26
    · simp only [t234Z, e1, e2]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e4]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
  have rimK : RobUniLex (t234Z x b rimTK) := by
    have e0 : rimTK 0 = 0 := by decide
    have e1 : rimTK 1 = 4 := by decide
    have e2 : rimTK 2 = 3 := by decide
    apply robUniLex_four_of_mixed
    · refine ⟨(2, 1), by decide, ?_⟩
      simp only [t234Z, e2, e1]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · refine ⟨(0, 1), by decide, ?_⟩
      simp only [t234Z, e0, e1]; exact lexLt3_of_fst (by simp only; linarith)
  have rimL : RobUniLex (t234Z x b rimTL) := by
    have e0 : rimTL 0 = 0 := by decide
    have e1 : rimTL 1 = 4 := by decide
    have e2 : rimTL 2 = 6 := by decide
    have e3 : rimTL 3 = 3 := by decide
    have e4 : rimTL 4 = 2 := by decide
    have e5 : rimTL 5 = 5 := by decide
    apply robUniLex_six_dw
    · right; simp only [t234Z, e3, e4]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · right; simp only [t234Z, e1, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · left; simp only [t234Z, e4, e5]; exact lexLt3_of_fst (by simp only; linarith)
    · left; simp only [t234Z, e2, e1]; exact lexLt3_of_fst (by simp only; linarith)
  have rimM : RobUniLex (t234Z x b rimTM) := by
    have e0 : rimTM 0 = 1 := by decide
    have e1 : rimTM 1 = 2 := by decide
    have e2 : rimTM 2 = 3 := by decide
    apply robUniLex_four_of_mixed
    · refine ⟨(2, 1), by decide, ?_⟩
      simp only [t234Z, e2, e1]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · refine ⟨(0, 1), by decide, ?_⟩
      simp only [t234Z, e0, e1]; exact lexLt3_of_fst (by simp only; linarith)
  have rimN : RobUniLex (t234Z x b rimTN) := by
    have e0 : rimTN 0 = 5 := by decide
    have e1 : rimTN 1 = 0 := by decide
    have e2 : rimTN 2 = 6 := by decide
    have e3 : rimTN 3 = 3 := by decide
    have e4 : rimTN 4 = 2 := by decide
    apply robUniLex_five_e26
    · simp only [t234Z, e1, e2]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e4]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
  have rimO : RobUniLex (t234Z x b rimTO) := by
    have e0 : rimTO 0 = 0 := by decide
    have e1 : rimTO 1 = 1 := by decide
    have e2 : rimTO 2 = 6 := by decide
    have e3 : rimTO 3 = 3 := by decide
    have e4 : rimTO 4 = 2 := by decide
    apply robUniLex_five_e26
    · simp only [t234Z, e1, e2]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e4]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
  rcases lt_or_ge (t234X6 x) 0 with hX | hX
  · -- `X6 < 0`: `346` up, `t234C > 0`, `126 236` down
    have u8 := t234_up8_of F hB.1.1 hX
    have hc := t234C_pos_of_X6 F hB.1 hX
    have n5 := t234_dn5_of F hB hc
    have n7 := (t234_dn7_iff F hB.1).mpr hc.le
    rcases hC hX with ⟨n2, n4⟩ | ⟨u0, n1, n4⟩ | ⟨n0, u2, n4⟩ | ⟨u0, u1⟩ | ⟨n1, n2, u4⟩ | ⟨u0, n1, u4⟩ |
      ⟨n0, n1, u2, u4⟩ | ⟨n0, u1, u2⟩
    · refine t234_cell F (b := b) rimTL UTL DnTL (by norm_num) rimTL_inj rimTL_cyc ?_ ?_ rimL
      · intro t ht; simp only [UTL, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [u3, u6, u8]
      · intro t ht; simp only [DnTL, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n2, n4, n7]
    · refine t234_cell F (b := b) rimTF UTF DnTF (by norm_num) rimTF_inj rimTF_cyc ?_ ?_ ?_
      · intro t ht; simp only [UTF, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u0, u3, u6, u8]
      · intro t ht; simp only [DnTF, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [n1, n4, n5, n7]
      · have e0 : rimTF 0 = 0 := by decide
        have e1 : rimTF 1 = 1 := by decide
        have e2 : rimTF 2 = 2 := by decide
        have e3 : rimTF 3 = 3 := by decide
        have e4 : rimTF 4 = 6 := by decide
        have e5 : rimTF 5 = 4 := by decide
        apply robUniLex_six_dw
        · left; simp only [t234Z, e3, e2]
          exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
        · left; simp only [t234Z, e5, e0]; exact lexLt3_of_fst (by simp only; linarith)
        · left; simp only [t234Z, e4, e5]; exact lexLt3_of_fst (by simp only; linarith)
        · left; simp only [t234Z, e2, e1]; exact lexLt3_of_fst (by simp only; linarith)
    · refine t234_cell F (b := b) rimTG UTG DnTG (by norm_num) rimTG_inj rimTG_cyc ?_ ?_ ?_
      · intro t ht; simp only [UTG, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u2, u3, u6, u8]
      · intro t ht; simp only [DnTG, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n0, n4, n7]
      · have e0 : rimTG 0 = 0 := by decide
        have e1 : rimTG 1 = 2 := by decide
        have e2 : rimTG 2 = 3 := by decide
        have e3 : rimTG 3 = 6 := by decide
        have e4 : rimTG 4 = 4 := by decide
        apply robUniLex_five_e26
        · simp only [t234Z, e1, e2]
          exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
        · simp only [t234Z, e3, e4]; exact lexLt3_of_fst (by simp only; linarith)
        · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
        · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · refine t234_cell F (b := b) rimTM UTM DnTM le_rfl rimTM_inj rimTM_cyc ?_ ?_ rimM
      · intro t ht; simp only [UTM, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u0, u1, u6, u8]
      · intro t ht; simp only [DnTM, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        exacts [n5, n7]
    · refine t234_cell F (b := b) rimTN UTN DnTN (by norm_num) rimTN_inj rimTN_cyc ?_ ?_ rimN
      · intro t ht; simp only [UTN, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u3, u4, u6, u8]
      · intro t ht; simp only [DnTN, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n1, n2, n7]
    · refine t234_cell F (b := b) rimTH UTH DnTH (by norm_num) rimTH_inj rimTH_cyc ?_ ?_ ?_
      · intro t ht; simp only [UTH, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u0, u4, u6, u8]
      · intro t ht; simp only [DnTH, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n1, n5, n7]
      · have e0 : rimTH 0 = 1 := by decide
        have e1 : rimTH 1 = 0 := by decide
        have e2 : rimTH 2 = 6 := by decide
        have e3 : rimTH 3 = 3 := by decide
        have e4 : rimTH 4 = 2 := by decide
        apply robUniLex_five_e26
        · simp only [t234Z, e1, e2]; exact lexLt3_of_fst (by simp only; linarith)
        · simp only [t234Z, e3, e4]
          exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
        · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
        · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · refine t234_cell F (b := b) rimTI UTI DnTI le_rfl rimTI_inj rimTI_cyc ?_ ?_ ?_
      · intro t ht; simp only [UTI, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u2, u4, u6, u8]
      · intro t ht; simp only [DnTI, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n0, n1, n7]
      · have e0 : rimTI 0 = 0 := by decide
        have e1 : rimTI 1 = 2 := by decide
        have e2 : rimTI 2 = 3 := by decide
        have e3 : rimTI 3 = 6 := by decide
        apply robUniLex_four_of_mixed
        · refine ⟨(2, 1), by decide, ?_⟩
          simp only [t234Z, e2, e1]
          exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
        · refine ⟨(0, 3), by decide, ?_⟩
          simp only [t234Z, e0, e3]; exact lexLt3_of_fst (by simp only; linarith)
    · refine t234_cell F (b := b) rimTO UTO DnTO (by norm_num) rimTO_inj rimTO_cyc ?_ ?_ rimO
      · intro t ht; simp only [UTO, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u1, u2, u6, u8]
      · intro t ht; simp only [DnTO, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n0, n5, n7]
  · have n8 := (t234_dn8_iff F hB.1.1).mpr hX
    rcases lt_or_ge (t234C x) 0 with hc | hc
    · -- `t234C < 0`: `126 236` up, rims `0 1 6 3 4` / `0 4 3 6`
      have u5 := t234_up5_of F hB hc
      have u7 := t234_up7_of F hB.1 hc
      obtain ⟨n4, ⟨u0, n1⟩ | u1⟩ := hBr hc
      · refine t234_cell F (b := b) rimTE UTE DnTE (by norm_num) rimTE_inj rimTE_cyc ?_ ?_ ?_
        · intro t ht; simp only [UTE, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl
          exacts [u0, u3, u5, u7]
        · intro t ht; simp only [DnTE, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          exacts [n1, n4, n8]
        · have e0 : rimTE 0 = 0 := by decide
          have e1 : rimTE 1 = 1 := by decide
          have e2 : rimTE 2 = 6 := by decide
          have e3 : rimTE 3 = 3 := by decide
          have e4 : rimTE 4 = 4 := by decide
          apply robUniLex_five_e26
          · simp only [t234Z, e1, e2]; exact lexLt3_of_fst (by simp only; linarith)
          · simp only [t234Z, e3, e4]
            exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
          · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
          · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
      · refine t234_cell F (b := b) rimTK UTK DnTK le_rfl rimTK_inj rimTK_cyc ?_ ?_ rimK
        · intro t ht; simp only [UTK, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          exacts [u1, u3, u7]
        · intro t ht; simp only [DnTK, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          exacts [n4, n8]
    · -- the cone: rims `0 1 2 3 4`, `0 2 3 4`, `5 0 4 3 2`
      have n7 := (t234_dn7_iff F hB.1).mpr hc
      have n1 := t234_dn1_of_cone F hB hX hc
      have hA' := hA hX hc
      have n4 : T234Dn F b 4 := by
        rcases hA'.1 with h | h | h
        · exact t234_dn4_of_cone F hB hX hc (Or.inl h)
        · exact t234_dn4_of_cone F hB hX hc (Or.inr h)
        · exact h
      obtain ⟨-, ⟨u0, h5⟩ | ⟨n0, u2⟩ | n2⟩ := hA'
      · have n5 : T234Dn F b 5 := by
          rcases hc.lt_or_eq with hc | hc
          · exact t234_dn5_of F hB hc
          · exact h5 hc.symm
        refine t234_cell F (b := b) rimB2B UB2B DnB2B (by norm_num) rimB2B_inj rimB2B_cyc ?_ ?_
          (t234_rim_B F hb h20 h21)
        · intro t ht; simp only [UB2B, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          exacts [u0, u3, u6]
        · intro t ht; simp only [DnB2B, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl | rfl
          exacts [n1, n4, n5, n7, n8]
      · refine t234_cell F (b := b) rimDB UTD DnTDN le_rfl rimDB_inj rimTDN_cyc ?_ ?_ (t234_rim_D F hb h20)
        · intro t ht; simp only [UTD, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          exacts [u2, u3, u6]
        · intro t ht; simp only [DnTDN, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl
          exacts [n0, n4, n7, n8]
      · refine t234_cell F (b := b) rimTJ UTJ DnTJ (by norm_num) rimTJ_inj rimTJ_cyc ?_ ?_ rimJ
        · intro t ht; simp only [UTJ, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          exacts [u3, u6]
        · intro t ht; simp only [DnTJ, Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl | rfl
          exacts [n2, n4, n7, n8]

/-- `T234RedN` is weaker than `T234RedM` on the branch (the OSPEC17 letters imply the new ones). -/
theorem t234RedN_of_M (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (h : T234RedM F) : T234RedN F := by
  obtain ⟨n1, h4, h0, h5⟩ := h
  refine ⟨fun hX _ => ?_, fun hc => ?_, fun _ => ?_⟩
  · have n4 : T234Dn F (t234b x) 4 := h4.elim id (fun h => absurd hX (not_le.mpr h.1))
    rcases h0 with u0 | ⟨n0, u2, -⟩
    · exact ⟨Or.inr (Or.inr n4), Or.inl ⟨u0, h5⟩⟩
    · exact ⟨Or.inr (Or.inr n4), Or.inr (Or.inl ⟨n0, u2⟩)⟩
  · have hX : 0 ≤ t234X6 x := by
      by_contra hX
      exact absurd (t234C_pos_of_X6 F hB.1 (not_le.mp hX)) (not_lt.mpr hc.le)
    have n4 : T234Dn F (t234b x) 4 := h4.elim id (fun h => absurd hX (not_le.mpr h.1))
    rcases h0 with u0 | ⟨-, -, hc'⟩
    · exact ⟨n4, Or.inl ⟨u0, n1⟩⟩
    · exact absurd hc' (not_le.mpr hc)
  · rcases h4 with n4 | ⟨-, u4⟩ <;> rcases h0 with u0 | ⟨n0, u2, -⟩
    · exact Or.inr (Or.inl ⟨u0, n1, n4⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n0, u2, n4⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨u0, n1, u4⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n0, n1, u2, u4⟩))))))

/-! ### The residue after the T234 view with every facet pattern (OSPEC18) -/

/-- The T234 view with every admitted facet pattern: `T234ViewOK`, or on `T234BrL` the letters `T234RedN`. -/
def T234ViewN {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234ViewOK F ∨ (T234BrL F ∧ T234RedN F)

theorem lexAny_of_t234ViewN (F : S0xFac 9 s0x_S24 x) (h : T234ViewN F) : Gen.LexAny F := by
  rcases h with h | ⟨hB, h⟩
  · exact lexAny_of_t234View F h
  · exact lexAny_of_t234RedN F hB h

theorem t234ViewN_of_M (F : S0xFac 9 s0x_S24 x) (h : T234ViewM F) : T234ViewN F := by
  rcases h with h | ⟨hB, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨hB, t234RedN_of_M F hB h⟩

/-- `Q45ResSTG` where neither T234 view of OSPEC18 (nor its mirror) applies: on the B2 branch the failure of
`T234RedN` (cone: `046` up, or `012 016 025` all up, or `012` up `016` down `025` up with `126` up at `t234C = 0`;
`t234C < 0`: `046` up, or `012` and `016` down; `X6 < 0`: `012` down, `016` up, `025` down, `046` up). -/
def Q45ResSTN {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTG F s t ∧ ¬ T234ViewN F ∧ ¬ T234ViewN (Sym.sym24 F)

/-- The branch-tagged residue after OSPEC18. -/
def Q45ResWN {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTN F s t

theorem q45_resN_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : Q45ResSTG F s t) :
    Gen.LexAny F ∨ Q45ResSTN F s t := by
  by_cases hA : T234ViewN F
  · exact Or.inl (lexAny_of_t234ViewN F hA)
  by_cases hB : T234ViewN (Sym.sym24 F)
  · exact Or.inl (Sym.lexAny_sym F (lexAny_of_t234ViewN (Sym.sym24 F) hB))
  exact Or.inr ⟨h, hA, hB⟩

/-- `Q45ResWN ⊆ Q45ResWM`. -/
theorem q45ResWM_of_N {F : S0xFac 9 s0x_S24 x} (h : Q45ResWN F) : Q45ResWM F := by
  obtain ⟨s, t, hs, ht, hst, hd, h, hA, hB⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h, fun h' => hA (t234ViewN_of_M F h'),
    fun h' => hB (t234ViewN_of_M (Sym.sym24 F) h')⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWN`. -/
theorem q45_resN (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWN F := by
  rcases q45_resG F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resN_local F h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the T234 view with every facet pattern, Rupert form**: `OpenSpecialM` with
`Q45ResWN` in place of `Q45ResWM` (implied by it: `openSpecialN_of_openSpecialM`). -/
def OpenSpecialN : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWN F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialM → OpenSpecialN` (`Q45ResWN ⊆ Q45ResWM`). -/
theorem openSpecialN_of_openSpecialM (h : OpenSpecialM) : OpenSpecialN :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWM_of_N hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialN`. -/
theorem hole24_offOB1_N {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialN) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resN F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the T234 view with every facet pattern) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_N (h1 : OpenOB1) (h2 : OpenSpecialN) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_N hH hO h2

end T234N

/-! ### The double wall: `s, t < 1` from the frame signs (job OSPEC19)

On the double wall `a4 = a5 = 1` the face `0345` lies in the plane `a = 1` parallel to `126` (`a = 0`), so the
oblique coordinates of `x 3 = x 0 + s e4 + t e5` are `a3 = 1`, `b3 = s b4 + t b5`, `c3 = s c4 + t c5`.  The frame
signs of `OpenSpecialN` then give `(1 - t) b5 > s b4 > 0` (`b2`) and `(1 - s) c4 > t c5 > 0` (`b1`): both `s` and `t`
are `< 1`, so the `t ≤ 1` / `s ≤ 1` clauses of `DwK0Cut` (and the rim choice of `BsRU`) are automatic there. -/

section DwST

variable {x : Fin 7 → ℝ³}

/-- `a3 = 1 - s - t + s a4 + t a5` (the facet `126` through the frame vertices, `bs_f5_obl`). -/
theorem obl3_a (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    oblX0 x 3 = 1 - s - t + s * oblX0 x 4 + t * oblX0 x 5 := by
  have h := congrArg (fun w => ⟪F.N 5, w⟫) hd
  simp only [inner_add_right, real_inner_smul_right] at h
  rw [F.inner_sub 5 3 0, F.inner_sub 5 4 0, F.inner_sub 5 5 0, bs_f5_obl F 3, bs_f5_obl F 4,
    bs_f5_obl F 5] at h
  have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have hid : F.f 5 (x 0) * (oblX0 x 3 - (1 - s - t + s * oblX0 x 4 + t * oblX0 x 5)) = 0 := by
    linear_combination h
  linarith [(mul_eq_zero.mp hid).resolve_left h0.ne]

/-- **On the double wall `t < 1`** (frame sign `b2`: `0 < a3 b5 - a5 b3`). -/
theorem dw_t_lt_one (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) : t < 1 := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have ha3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  obtain ⟨hb3, -⟩ := t234_obl3_bc F hd
  rw [ha3, hw5, hb3] at b2
  by_contra hc
  push Not at hc
  nlinarith [mul_pos hs0 hb4]

/-- **On the double wall `s < 1`** (frame sign `b1`: `a4 c3 - a3 c4 < 0`). -/
theorem dw_s_lt_one (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (ht0 : 0 < t)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0) : s < 1 := by
  have T := M4.type24OfFac F
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have ha3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  obtain ⟨-, hc3⟩ := t234_obl3_bc F hd
  rw [ha3, hw4, hc3] at b1
  by_contra hc
  push Not at hc
  nlinarith [mul_pos ht0 hc5]

/-- On the double wall (with the frame signs) the double-wall K0 cut is exactly its junction clauses. -/
theorem dwK0Cut_iff (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) : DwK0Cut F t ↔ DwK0C F :=
  ⟨fun h => h.2.2.2, fun h => ⟨hw4, hw5, (dw_t_lt_one F hs0 hd hw4 hw5 b2).le, h⟩⟩

end DwST

end Minimality.T24.OSpec
