module

public import Minimality.Type29T1Escape
public import Minimality.SVCCells
public import Minimality.SVCLex
public import Minimality.Chi29

@[expose] public section

/-!
# Type 29, `t = 1` escape closed: `F023 x F356` with lexicographic depths

Closes the whole escape of `t1_closed` (Type29T1Escape, nopert229 T1RES), so `T1Hyp` needs no
escape hypothesis.
* **K1b is empty on the escape** (`t1r_K1b_false`): `0 < a2`, `b0 < 0`, `s ≥ 1` and the NF29 /
  cell facts `D234 > 0`, `dG4 > 0` force `h2 < 1`, `h0 < 1`, hence `dG > 0` and
  `DG4 - D023 = (1 - s) dG4 - dG < 0`, against the cell fact `0 < DG4 - D023`.
* **K1a**: the view `u023_356` with the tilt `x3 - x1` (nonzero on every facet, `t1r_tilt31`) and
  the third direction `x1 - x4` (`u, x3 - x1, x1 - x4` is a basis, `t1r_det`) closes by
  `SVC.single_view_closure_lex` in all five ranges of `m = b2 + h2`: `m < 0` (rim C), `m = 0`
  (facet 124 edge-on, tilt sign `-`, rim B), `0 < m < b0 + h0` (rim B), `m = b0 + h0` (facet 012
  edge-on, tilt sign `-`, rim A), `b0 + h0 < m` (rim A, forced `z2 < z0`). Lexicographic depths
  make depth ties at the view harmless: no genericity hypothesis (`lexAny29_F023F356`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21 Minimality.SVC

namespace Minimality.NF29

/-! ### K1b is empty on the escape -/

/-- `DG4 - D023 < 0` at `t = 1` for `0 < a2`, `b0 < 0`, `s ≥ 1`. -/
theorem t1r_U5_K1b (a0 b0 h0 a2 b2 h2 s : ℝ) (ha0 : a0 < 0) (hb2 : b2 < 0) (ha2 : 0 < a2)
    (hb0 : b0 < 0) (hs1 : 1 ≤ s) (hd234 : 0 < b2 * s + (1 - h2 - a2) - b2)
    (hdG4 : 0 < b0 * (1 - h2) - b2 * (1 - h0)) :
    (1 - s) * (b0 * (1 - h2) - b2 * (1 - h0)) - (a2 * (1 - h0) - a0 * (1 - h2)) < 0 := by
  have hh2 : h2 < 1 := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hb2.le) (sub_nonneg.mpr hs1)]
  have hh0 : h0 < 1 := by
    nlinarith [mul_pos (neg_pos.mpr hb0) (sub_pos.mpr hh2)]
  nlinarith [mul_pos ha2 (sub_pos.mpr hh0), mul_pos (neg_pos.mpr ha0) (sub_pos.mpr hh2),
    mul_nonneg (sub_nonneg.mpr hs1) hdG4.le]

variable {x : Fin 7 → ℝ³}

/-- **K1b part of the escape is empty**: the cell fact `0 < DG4 - D023` fails for `0 < a2`,
`b0 < 0`, `s ≥ 1` at `t = 1`. -/
theorem t1r_K1b_false (N : NF29 x) (ht : N.t = 1) (ha2 : 0 < N.a2) (hb0 : N.b0 < 0)
    (hs1 : 1 ≤ N.s) (hdG4 : 0 < N.dG4) (hU5 : 0 < N.DG4 - N.D023) : False := by
  have hd := N.d234
  rw [ht] at hd
  have h := t1r_U5_K1b N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.ha0 N.hb2 ha2 hb0 hs1
    (by linarith) hdG4
  have e : N.DG4 - N.D023 = (1 - N.s) * N.dG4 - N.dG := by
    simp only [DG4, D023, ht]; ring
  simp only [dG4, dG] at e
  linarith

/-! ### the tilt `x3 - x1` and the basis -/

/-- Signs of the tilt `x3 - x1` on the nine facets (`+` through 3 not 1, `-` through 1 not 3). -/
def t1r_sd31 : Fin 9 → SignType := ![-1, -1, 1, 1, -1, -1, 1, 1, 1]

theorem t1r_tilt31 (N : NF29 x) (t : Fin 9) :
    SignType.sign ⟪(s0x_fac29 N.facets).N t, x 3 - x 1⟫ = t1r_sd31 t := by
  fin_cases t
  · exact sign_neg (SVCC.edge_neg _ _ (by decide) (by decide))
  · exact sign_neg (SVCC.edge_neg _ _ (by decide) (by decide))
  · exact sign_pos (SVCC.edge_pos _ _ (by decide) (by decide))
  · exact sign_pos (SVCC.edge_pos _ _ (by decide) (by decide))
  · exact sign_neg (SVCC.edge_neg _ _ (by decide) (by decide))
  · exact sign_neg (SVCC.edge_neg _ _ (by decide) (by decide))
  · exact sign_pos (SVCC.edge_pos _ _ (by decide) (by decide))
  · exact sign_pos (SVCC.edge_pos _ _ (by decide) (by decide))
  · exact sign_pos (SVCC.edge_pos _ _ (by decide) (by decide))

theorem t1r_u_nfV (N : NF29 x) :
    N.u023_356 x = nfV N.E₁ N.E₂ N.E₃ (N.dG4 * N.s - N.D023) (N.dG4 * N.t) N.dG4 := by
  dsimp only [u023_356]
  nf29_vec N

/-- `u023_356, x3 - x1, x1 - x4` is a basis: its determinant is `dG4 t D`. -/
theorem t1r_det_eq (N : NF29 x) :
    Split.det3 (N.u023_356 x) (x 3 - x 1) (x 1 - x 4) = N.dG4 * N.t * N.D := by
  rw [split_det3_eq, t1r_u_nfV]
  nf29_simp N
  simp only [det3c, NF29.D]
  ring

theorem t1r_det (N : NF29 x) (hdG4 : 0 < N.dG4) :
    Split.det3 (N.u023_356 x) (x 3 - x 1) (x 1 - x 4) ≠ 0 := by
  rw [t1r_det_eq]
  exact mul_ne_zero (mul_pos hdG4 N.ht).ne' N.hD

/-! ### the lexicographic leaf -/

/-- One case of the leaf: facings `s012`, `s124` on the two facets that vary with `m`. -/
theorem t1r_core {p : ℕ} (N : NF29 x) (ht : N.t = 1) (ha2 : N.a2 < 0) (hdG4 : 0 < N.dG4)
    (hA : 0 < 1 - N.b0 - N.h0) (P : Fin p → Fin 7) (hP : Function.Injective P)
    (s012 s124 : SignType)
    (h012 : SignType.sign (N.D02 * (N.b0 - N.b2 + N.h0 - N.h2)) = s012)
    (h124 : SignType.sign (-(N.b2 + N.h2) * N.dG4) = s124)
    (ρ : Rim 9 p) (hsd : ρ.sd = t1r_sd31) (forced : List (Fin p × Fin p))
    (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), N.u023_356 x⟫ < ⟪x (P ij.1), N.u023_356 x⟫)
    (hcheck : check s0x_S29 P ![s012, 1, 0, 1, s124, 1, -1, -1, 0] forced [] [ρ] = true) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  single_view_closure_lex (s0x_fac29 N.facets) P (N.u023_356 x) (x 3 - x 1) (x 1 - x 4) _
    (t1e_facing_signs N ht ha2 hdG4 hA s012 s124 h012 h124) ρ
    (fun t _ => by rw [hsd]; exact t1r_tilt31 N t) forced hforced
    (fun _ _ h => hP (N.inj h)) (t1r_det N hdG4) hcheck

/-- rim `4 6 3 2` (case `m < 0`) -/
def t1r_rimC : Rim 9 5 :=
  { k := 4, c := ![3, 4, 2, 1], U := {0, 1, 2, 3, 4, 5, 8}, Dn := {6, 7}, sd := t1r_sd31 }
/-- rim `4 6 3 2 1` (`0 ≤ m < b0 + h0`) -/
def t1r_rimB : Rim 9 5 :=
  { k := 5, c := ![3, 4, 2, 1, 0], U := {0, 1, 2, 3, 5, 8}, Dn := {4, 6, 7}, sd := t1r_sd31 }
/-- rim `4 6 3 2 0 1` (`b0 + h0 ≤ m`) -/
def t1r_rimA : Rim 9 6 :=
  { k := 6, c := ![3, 4, 2, 1, 5, 0], U := {1, 2, 3, 5, 8}, Dn := {0, 4, 6, 7}, sd := t1r_sd31 }

theorem t1r_checkC :
    check s0x_S29 t1e_P5 ![1, 1, 0, 1, 1, 1, -1, -1, 0] t1e_forced5 [] [t1r_rimC] = true := by
  decide +kernel
theorem t1r_checkW0 :
    check s0x_S29 t1e_P5 ![1, 1, 0, 1, 0, 1, -1, -1, 0] t1e_forced5 [] [t1r_rimB] = true := by
  decide +kernel
theorem t1r_checkB :
    check s0x_S29 t1e_P5 ![1, 1, 0, 1, -1, 1, -1, -1, 0] t1e_forced5 [] [t1r_rimB] = true := by
  decide +kernel
theorem t1r_checkW1 :
    check s0x_S29 t1e_P6 ![0, 1, 0, 1, -1, 1, -1, -1, 0] t1e_forced6 [] [t1r_rimA] = true := by
  decide +kernel
theorem t1r_checkA :
    check s0x_S29 t1e_P6 ![-1, 1, 0, 1, -1, 1, -1, -1, 0] t1e_forced6 [] [t1r_rimA] = true := by
  decide +kernel

/-- **The `F023 x F356` leaf of the `t = 1` escape**, for every `m = b2 + h2` and without any
depth genericity: on the metric slice `g35 = g45 = 0`, `g34 < 0` (from `t1_escape` and `¬ Z`),
K1a, `s ≥ 1`, the view `u023_356` with lexicographic depths `(u, x3 - x1, x1 - x4)` closes. -/
theorem lexAny29_F023F356 (N : NF29 x) (ht : N.t = 1) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hs1 : 1 ≤ N.s)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  obtain ⟨z1, z2, z3⟩ := t1e_forced_z N ht hdG4 h35 h45 hg34
  have hD02 : 0 < N.D02 := N.hDD
  have hh0 := N.hh0
  have hP5 : Function.Injective t1e_P5 := by decide
  have hP6 : Function.Injective t1e_P6 := by decide
  have f5 : ∀ ij ∈ t1e_forced5,
      ⟪x (t1e_P5 ij.2), N.u023_356 x⟫ < ⟪x (t1e_P5 ij.1), N.u023_356 x⟫ := by
    intro ij hij
    simp only [t1e_forced5, List.mem_cons, List.not_mem_nil, or_false] at hij
    rcases hij with rfl | rfl | rfl
    · exact z1
    · exact z2
    · exact z3
  have f6 : N.b0 + N.h0 ≤ N.b2 + N.h2 → ∀ ij ∈ t1e_forced6,
      ⟪x (t1e_P6 ij.2), N.u023_356 x⟫ < ⟪x (t1e_P6 ij.1), N.u023_356 x⟫ := by
    intro hm ij hij
    simp only [t1e_forced6, List.mem_cons, List.not_mem_nil, or_false] at hij
    rcases hij with rfl | rfl | rfl | rfl
    · exact z1
    · exact z2
    · exact z3
    · exact t1e_z02_A N ht hb0 hdG4 hA hs1 h35 h45 hg34 hm
  rcases lt_trichotomy (N.b2 + N.h2) 0 with hC | hW0 | hpos
  · exact t1r_core N ht ha2 hdG4 hA t1e_P5 hP5 1 1
      (sign_pos (mul_pos hD02 (by linarith))) (sign_pos (mul_pos (by linarith) hdG4))
      t1r_rimC rfl t1e_forced5 f5 t1r_checkC
  · exact t1r_core N ht ha2 hdG4 hA t1e_P5 hP5 1 0
      (sign_pos (mul_pos hD02 (by linarith))) (by rw [hW0, neg_zero, zero_mul, sign_zero])
      t1r_rimB rfl t1e_forced5 f5 t1r_checkW0
  rcases lt_trichotomy (N.b2 + N.h2) (N.b0 + N.h0) with hB | hW1 | hAc
  · exact t1r_core N ht ha2 hdG4 hA t1e_P5 hP5 1 (-1)
      (sign_pos (mul_pos hD02 (by linarith))) (sign_neg (mul_neg_of_neg_of_pos (by linarith) hdG4))
      t1r_rimB rfl t1e_forced5 f5 t1r_checkB
  · have e : N.b0 - N.b2 + N.h0 - N.h2 = 0 := by linarith
    exact t1r_core N ht ha2 hdG4 hA t1e_P6 hP6 0 (-1)
      (by rw [e, mul_zero, sign_zero]) (sign_neg (mul_neg_of_neg_of_pos (by linarith) hdG4))
      t1r_rimA rfl t1e_forced6 (f6 hW1.ge) t1r_checkW1
  · exact t1r_core N ht ha2 hdG4 hA t1e_P6 hP6 (-1) (-1)
      (sign_neg (mul_neg_of_pos_of_neg hD02 (by linarith)))
      (sign_neg (mul_neg_of_neg_of_pos (by linarith) hdG4))
      t1r_rimA rfl t1e_forced6 (f6 hAc.le) t1r_checkA

/-! ### `t1_closed'`: the `t = 1` cell without `hsD` -/

/-- **`t1_closed` without the sample fact `hsD`.** On the `t = 1` cell with the V46 leaf region
and the K1 sign pattern: if `hsD`, the old proof `t1_closed`; otherwise K1b contradicts `hU5`
(`t1r_K1b_false`), and in K1a `t1_escape` gives `s ≥ 1`, `g35 = g45 = 0`, `¬ Z` makes `g34 < 0`,
and `lexAny29_F023F356` closes. -/
theorem t1_closed' (N : NF29 x) (ht : N.t = 1)
    (hK : (N.a2 < 0 ∧ 0 < N.b0) ∨ (0 < N.a2 ∧ N.b0 < 0))
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hU5 : 0 < N.DG4 - N.D023)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ ≤ 0)
    (hZ : ¬ (⟪x 3 - x 6, x 4 - x 6⟫ = 0 ∧ ⟪x 3 - x 6, x 5 - x 6⟫ = 0 ∧
      ⟪x 4 - x 6, x 5 - x 6⟫ = 0))
    (hg35 : ⟪x 3 - x 6, x 5 - x 6⟫ ≤ 0) (hg45 : ⟪x 4 - x 6, x 5 - x 6⟫ ≤ 0)
    (h012 : 0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3))
    (h015 : N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3))
    (h356 : N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0)
    (lam mu eta : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (heta : 0 < eta)
    (hfront : lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False := by
  by_cases hsD : N.s < 1 ∨ N.D234 < 1
  · exact t1_closed N ht hdG4 hA hU5 hsD hg35 hg45 h012 h015 h035 h124 h1456 h234 h356
      lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront hnf
  push Not at hsD
  rcases hK with ⟨ha2, hb0⟩ | ⟨ha2, hb0⟩
  swap
  · exact t1r_K1b_false N ht ha2 hb0 hsD.1 hdG4 hU5
  obtain ⟨hs1, -, h35, h45⟩ := t1_escape N ht hdG4 hA hU5 hg35 hg45 h012 h015 h035 h124
    h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront hnf
  have hg34' : ⟪x 3 - x 6, x 4 - x 6⟫ < 0 :=
    lt_of_le_of_ne hg34 (fun h => hZ ⟨h, h35, h45⟩)
  exact hnf (lexAny29_F023F356 N ht ha2 hb0 hdG4 hA hs1 h35 h45 hg34')

end Minimality.NF29
