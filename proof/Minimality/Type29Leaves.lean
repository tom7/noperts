module

public import Minimality.Type29Hole
public import Minimality.GenericLeaves

@[expose] public section

/-!
# Type 29: Building blocks from `A14-REFEREE`

Formalizes the refereed Type-29 building blocks:
1. `NF29.e023quad` and the nine facet values at `u23Q`;
2. `NF29.lexAny29_W14`: the `LexAny29` leaf at `b = x 1 - x 4`, `d1 = x 3 - x 1`, `d2 = 0` on the
   4-rim `![1, 2, 3, 5]`, under `N.a2 < 0`, `N.t < 1`, `0 < N.dG4`, `0 < 1 - N.b0 - N.h0`, and
   `G ∉ M_14`;
3. `NF29.fhat_1456_u35` and `NF29.front3524` (the metric-free front pair at `u35_24`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

noncomputable def dG (N : NF29 x) : ℝ := N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2)
noncomputable def dG4 (N : NF29 x) : ℝ := N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0)
noncomputable def D02 (N : NF29 x) : ℝ := N.a0 * N.b2 - N.a2 * N.b0
noncomputable def DG4 (N : NF29 x) : ℝ := N.D02 + N.dG4
noncomputable def DG5 (N : NF29 x) : ℝ := N.D02 + N.dG
noncomputable def D023 (N : NF29 x) : ℝ := N.D02 + N.s * N.dG4 + N.t * N.dG
noncomputable def E35 (N : NF29 x) : ℝ := (N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)
noncomputable def P4 (N : NF29 x) : ℝ := N.a2 * N.h0 - N.a0 * N.h2
noncomputable def P5 (N : NF29 x) : ℝ := N.b0 * N.h2 - N.b2 * N.h0
noncomputable def del0 (N : NF29 x) : ℝ := 1 - N.a0 - N.b0 - N.h0
noncomputable def del2 (N : NF29 x) : ℝ := 1 - N.a2 - N.b2 - N.h2

noncomputable def u23Q (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  (1 - N.h2) • (x 0 - x 3) - (1 - N.h0) • (x 2 - x 3)

noncomputable def u35_24 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  N.del0 • (x 2 - x 3) + N.E35 • (x 4 - x 3)

/-! ### 1. Identity `e023quad` and the nine facet values at `u23Q` -/

theorem e023quad (N : NF29 x) :
    (1 - N.h2) • (x 0 - x 3) - (1 - N.h0) • (x 2 - x 3) =
      (-N.dG) • (x 4 - x 1) + N.dG4 • (x 5 - x 1) := by
  dsimp only [dG, dG4]
  nf29_vec N

local macro "u23Q_fac_val " N:term:max f:ident : tactic =>
  `(tactic| (
    rw [($f $N).hN (x 3 + u23Q $N x) (x 3), add_sub_cancel_left]
    dsimp only [u23Q]
    rw [e023quad $N, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← ($f $N).hN (x 4) (x 1), ← ($f $N).hN (x 5) (x 1)]
    dsimp only [dG, dG4, D02, DG4, DG5, D023, E35, P4, P5,
      f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

theorem f012_u23Q (N : NF29 x) :
    N.f012.f (x 3 + N.u23Q x) - N.f012.f (x 3) = -((-N.dG) * N.P5 + N.dG4 * N.P4) * N.D ^ 2 := by
  u23Q_fac_val N f012

theorem f015_u23Q (N : NF29 x) :
    N.f015.f (x 3 + N.u23Q x) - N.f015.f (x 3) = (N.dG * N.h0) * N.D ^ 2 := by
  u23Q_fac_val N f015

theorem f023_u23Q (N : NF29 x) :
    N.f023.f (x 3 + N.u23Q x) - N.f023.f (x 3) = 0 := by
  u23Q_fac_val N f023

theorem f035_u23Q (N : NF29 x) :
    N.f035.f (x 3 + N.u23Q x) - N.f035.f (x 3) = (-(1 - N.h0) * N.E35) * N.D ^ 2 := by
  u23Q_fac_val N f035

theorem f124_u23Q (N : NF29 x) :
    N.f124.f (x 3 + N.u23Q x) - N.f124.f (x 3) = (-N.dG4 * N.h2) * N.D ^ 2 := by
  u23Q_fac_val N f124

theorem f1456_u23Q (N : NF29 x) :
    N.f1456.f (x 3 + N.u23Q x) - N.f1456.f (x 3) = 0 := by
  u23Q_fac_val N f1456

theorem f234_u23Q (N : NF29 x) :
    N.f234.f (x 3 + N.u23Q x) - N.f234.f (x 3) = (-(1 - N.h2) * N.DG4) * N.D ^ 2 := by
  u23Q_fac_val N f234

theorem f346_u23Q (N : NF29 x) :
    N.f346.f (x 3 + N.u23Q x) - N.f346.f (x 3) = (N.DG4 - N.D023) * N.D ^ 2 := by
  u23Q_fac_val N f346

theorem f356_u23Q (N : NF29 x) :
    N.f356.f (x 3 + N.u23Q x) - N.f356.f (x 3) = (N.D023 - N.DG5) * N.D ^ 2 := by
  u23Q_fac_val N f356

/-! ### 2. `W14-Region`: `lexAny29_W14` -/

local macro "w14_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG4, P5, f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def w14_c : ZMod 4 → Fin 7 := ![1, 2, 3, 5]
private def w14_U : Finset (Fin 9) := {0, 1, 2, 3}
private def w14_Dn : Finset (Fin 9) := {4, 5, 6, 7, 8}

private theorem w14_c_inj : Function.Injective w14_c := by decide
private theorem w14_cyc : S0xCycUD s0x_S29 w14_c w14_U w14_Dn := by decide

theorem lexAny29_W14 (N : NF29 x)
    (ha2 : N.a2 < 0) (ht : N.t < 1) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (hM : ¬ (⟪x 1, x 1 - x 4⟫ ≤ ⟪x 2, x 1 - x 4⟫ ∧ ⟪x 3, x 1 - x 4⟫ ≤ ⟪x 2, x 1 - x 4⟫ ∧
             ⟪x 1, x 1 - x 4⟫ ≤ ⟪x 5, x 1 - x 4⟫ ∧ ⟪x 3, x 1 - x 4⟫ ≤ ⟪x 5, x 1 - x 4⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := w14_c
  let U := w14_U
  let Dn := w14_Dn
  let b : ℝ³ := x 1 - x 4
  let d1 : ℝ³ := x 3 - x 1
  have hc_inj : Function.Injective c := w14_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := w14_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, 0⟫ := by
    intro t ht_mem
    have hnb : ⟪F.N t, b⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    rw [hnb]
    fin_cases t
    · refine Or.inl ?_
      have hv : N.f012.f (x 1) - N.f012.f (x 4) = N.P5 * N.D ^ 2 := by w14_fac_val N
      change 0 < N.f012.f (x 1) - N.f012.f (x 4)
      rw [hv]
      exact mul_pos (by dsimp [P5]; linarith [N.hF4]) hD2
    · refine Or.inl ?_
      have hv : N.f015.f (x 1) - N.f015.f (x 4) = N.h0 * N.D ^ 2 := by w14_fac_val N
      change 0 < N.f015.f (x 1) - N.f015.f (x 4)
      rw [hv]
      exact mul_pos N.hh0 hD2
    · refine Or.inl ?_
      have hv : N.f023.f (x 1) - N.f023.f (x 4) = N.dG4 * N.D ^ 2 := by w14_fac_val N
      change 0 < N.f023.f (x 1) - N.f023.f (x 4)
      rw [hv]
      exact mul_pos hdG4 hD2
    · refine Or.inl ?_
      have hv : N.f035.f (x 1) - N.f035.f (x 4) = (1 - N.b0 - N.h0) * N.D ^ 2 := by w14_fac_val N
      change 0 < N.f035.f (x 1) - N.f035.f (x 4)
      rw [hv]
      exact mul_pos hA hD2
    all_goals exact absurd ht_mem (by decide)
  have hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, 0⟫) := by
    intro t ht_mem
    have hnb : ⟪F.N t, b⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 1) := (F.hN t (x 3) (x 1)).symm
    rw [hnb, hnd1]
    fin_cases t
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · have hb0 : N.f124.f (x 1) - N.f124.f (x 4) = 0 := by w14_fac_val N
      have hd1v : N.f124.f (x 3) - N.f124.f (x 1) = N.b2 * N.D ^ 2 := by w14_fac_val N
      refine Or.inr ⟨by change -(N.f124.f (x 1) - N.f124.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f124.f (x 3) - N.f124.f (x 1))
      rw [hd1v]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · have hb0 : N.f1456.f (x 1) - N.f1456.f (x 4) = 0 := by w14_fac_val N
      have hd1v : N.f1456.f (x 3) - N.f1456.f (x 1) = -N.D ^ 2 := by w14_fac_val N
      refine Or.inr ⟨by change -(N.f1456.f (x 1) - N.f1456.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f1456.f (x 3) - N.f1456.f (x 1))
      rw [hd1v, neg_neg]
      exact hD2
    · refine Or.inl ?_
      have hv : N.f234.f (x 1) - N.f234.f (x 4) = N.b2 * N.D ^ 2 := by w14_fac_val N
      change 0 < -(N.f234.f (x 1) - N.f234.f (x 4))
      rw [hv]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · refine Or.inl ?_
      have hv : N.f346.f (x 1) - N.f346.f (x 4) = -N.t * N.D ^ 2 := by w14_fac_val N
      change 0 < -(N.f346.f (x 1) - N.f346.f (x 4))
      rw [hv, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos N.ht hD2
    · refine Or.inl ?_
      have hv : N.f356.f (x 1) - N.f356.f (x 4) = (N.t - 1) * N.D ^ 2 := by w14_fac_val N
      change 0 < -(N.f356.f (x 1) - N.f356.f (x 4))
      rw [hv]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr ht) hD2)
  have hRob : RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), 0⟫)) := by
    let lam2 : ℝ := 1 / (1 - N.b2)
    let mu1 : ℝ := (1 - N.b2 - N.h2) / (1 - N.b2)
    let eta : ℝ := -N.a2 / (1 - N.b2)
    have hb2_pos : 0 < 1 - N.b2 := by linarith [N.hb2]
    have hlam0 : 0 < lam2 := div_pos zero_lt_one hb2_pos
    have hlam1 : lam2 < 1 := by
      rw [div_lt_one hb2_pos]
      linarith [N.hb2]
    have hmu_num : 0 < 1 - N.b2 - N.h2 := by
      have hid : (1 - N.b2 - N.h2) * N.D02 = -N.b2 * N.DG5 - N.a2 * N.dG4 := by
        dsimp only [D02, DG5, dG, dG4]
        ring
      have hDG5 : 0 < N.DG5 := by dsimp only [DG5, D02, dG]; exact N.hDG5
      have hprod : 0 < (1 - N.b2 - N.h2) * N.D02 := by
        rw [hid]
        have h1 : 0 < -N.b2 * N.DG5 := mul_pos (neg_pos.mpr N.hb2) hDG5
        have h2 : 0 < -N.a2 * N.dG4 := mul_pos (neg_pos.mpr ha2) hdG4
        linarith
      exact pos_of_mul_pos_left hprod (by dsimp only [D02]; linarith [N.hDD])
    have hmu0 : 0 < mu1 := div_pos hmu_num hb2_pos
    have hmu1 : mu1 < 1 := by
      rw [div_lt_one hb2_pos]
      linarith [N.hh2]
    have heta0 : 0 < eta := div_pos (neg_pos.mpr ha2) hb2_pos
    have hvec : lam2 • x 2 + (1 - lam2) • x 5 = mu1 • x 1 + (1 - mu1) • x 3 + eta • b := by
      dsimp only [lam2, mu1, eta, b]
      have hne : 1 - N.b2 ≠ 0 := hb2_pos.ne'
      field_simp
      nf29_vec N
    have hb_ne : b ≠ 0 := sub_ne_zero.mpr (N.inj.ne (by decide))
    have hb_sq : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hb_ne
    have hz_id :
        lam2 * ⟪x 2, b⟫ + (1 - lam2) * ⟪x 5, b⟫ =
          mu1 * ⟪x 1, b⟫ + (1 - mu1) * ⟪x 3, b⟫ + eta * ⟪b, b⟫ := by
      have h := congrArg (fun v => ⟪v, b⟫) hvec
      simpa only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, smul_eq_mul,
        conj_trivial] using h
    have hz_lt :
        mu1 * ⟪x 1, b⟫ + (1 - mu1) * ⟪x 3, b⟫ < lam2 * ⟪x 2, b⟫ + (1 - lam2) * ⟪x 5, b⟫ := by
      linarith [mul_pos heta0 hb_sq]
    have hex_pos : ∃ p ∈ Minimality.RimCell.diagPairs,
        LexLt3 (⟪x (c p.1), b⟫, ⟪x (c p.1), d1⟫, ⟪x (c p.1), 0⟫)
               (⟪x (c p.2), b⟫, ⟪x (c p.2), d1⟫, ⟪x (c p.2), 0⟫) := by
      by_contra hnone
      simp only [Minimality.RimCell.diagPairs, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, not_exists, not_and] at hnone
      have hle : ∀ i ∈ ({0, 2} : Finset (ZMod 4)), ∀ j ∈ ({1, 3} : Finset (ZMod 4)),
          ⟪x (c j), b⟫ ≤ ⟪x (c i), b⟫ := by
        intro i hi j hj
        by_contra hgt
        push Not at hgt
        exact hnone (i, j) ⟨by simpa using hi, by simpa using hj⟩ (Or.inl (sub_pos.mpr hgt))
      have h21 : ⟪x 2, b⟫ ≤ ⟪x 1, b⟫ := hle 0 (by simp) 1 (by simp)
      have h23 : ⟪x 2, b⟫ ≤ ⟪x 3, b⟫ := hle 2 (by simp) 1 (by simp)
      have h51 : ⟪x 5, b⟫ ≤ ⟪x 1, b⟫ := hle 0 (by simp) 3 (by simp)
      have h53 : ⟪x 5, b⟫ ≤ ⟪x 3, b⟫ := hle 2 (by simp) 3 (by simp)
      have h_rhs : lam2 * ⟪x 2, b⟫ + (1 - lam2) * ⟪x 5, b⟫ ≤
          mu1 * ⟪x 1, b⟫ + (1 - mu1) * ⟪x 3, b⟫ := by
        have h1 : lam2 * ⟪x 2, b⟫ + (1 - lam2) * ⟪x 5, b⟫ ≤ ⟪x 1, b⟫ := by
          nlinarith
        have h3 : lam2 * ⟪x 2, b⟫ + (1 - lam2) * ⟪x 5, b⟫ ≤ ⟪x 3, b⟫ := by
          nlinarith
        nlinarith
      linarith
    have hex_neg : ∃ q ∈ Minimality.RimCell.diagPairs,
        LexLt3 (⟪x (c q.2), b⟫, ⟪x (c q.2), d1⟫, ⟪x (c q.2), 0⟫)
               (⟪x (c q.1), b⟫, ⟪x (c q.1), d1⟫, ⟪x (c q.1), 0⟫) := by
      by_contra hnone
      simp only [Minimality.RimCell.diagPairs, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, not_exists, not_and] at hnone
      have hle : ∀ i ∈ ({0, 2} : Finset (ZMod 4)), ∀ j ∈ ({1, 3} : Finset (ZMod 4)),
          ⟪x (c i), b⟫ ≤ ⟪x (c j), b⟫ := by
        intro i hi j hj
        by_contra hgt
        push Not at hgt
        exact hnone (i, j) ⟨by simpa using hi, by simpa using hj⟩ (Or.inl (sub_pos.mpr hgt))
      exact hM ⟨hle 0 (by simp) 1 (by simp), hle 2 (by simp) 1 (by simp),
                hle 0 (by simp) 3 (by simp), hle 2 (by simp) 3 (by simp)⟩
    exact robUniLex_four_of_mixed hex_pos hex_neg
  exact ⟨4, inferInstance, c, U, Dn, b, d1, 0, le_rfl, hc_inj, hcyc, hU, hD, hRob⟩

/-! ### 3. `Front-3524`: `fhat_1456_u35` and `front3524` -/

theorem fhat_1456_u35 (N : NF29 x) :
    N.f1456.f (x 3 + N.u35_24 x) - N.f1456.f (x 3) =
      -(N.DG4 - N.del2 * (1 - N.h0)) * N.D ^ 2 := by
  rw [N.f1456.hN (x 3 + N.u35_24 x) (x 3), add_sub_cancel_left]
  dsimp only [u35_24]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    ← N.f1456.hN (x 2) (x 3), ← N.f1456.hN (x 4) (x 3)]
  dsimp only [del0, del2, E35, DG4, D02, dG4, f1456, Face16.ofPoly]
  nf29_simp N
  simp only [det3c, NF29.D]
  ring

theorem front3524 (N : NF29 x)
    (hb0 : 0 < N.b0) (h : N.del2 * (1 - N.h0) < N.DG4) :
    ∃ lam mu eta : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧ 0 < eta ∧
      lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u35_24 x := by
  let Dn : ℝ := -N.b2 * N.del0 - N.a0 * N.DG4
  have hdel0 : 0 < N.del0 := by dsimp only [del0]; linarith [N.t345_0]
  have hDG4 : 0 < N.DG4 := by dsimp only [DG4, D02, dG4]; exact N.hDG4
  have hDn : 0 < Dn := by
    have h1 : 0 < -N.b2 * N.del0 := mul_pos (neg_pos.mpr N.hb2) hdel0
    have h2 : 0 < -N.a0 * N.DG4 := mul_pos (neg_pos.mpr N.ha0) hDG4
    dsimp only [Dn]
    linarith
  refine ⟨N.del0 * N.DG4 / Dn, N.del0 * (-N.b2) / Dn, N.b0 / Dn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos (mul_pos hdel0 hDG4) hDn
  · rw [div_lt_one hDn]
    have hrem : Dn - N.del0 * N.DG4 =
        N.del0 * (-N.b2) * N.h0 + N.b0 * (N.DG4 - N.del2 * (1 - N.h0)) := by
      dsimp only [Dn, del0, del2, DG4, D02, dG4]
      ring
    have h1 : 0 < N.del0 * (-N.b2) * N.h0 :=
      mul_pos (mul_pos hdel0 (neg_pos.mpr N.hb2)) N.hh0
    have h2 : 0 < N.b0 * (N.DG4 - N.del2 * (1 - N.h0)) :=
      mul_pos hb0 (sub_pos.mpr h)
    linarith
  · exact div_pos (mul_pos hdel0 (neg_pos.mpr N.hb2)) hDn
  · rw [div_lt_one hDn]
    have h2 : 0 < -N.a0 * N.DG4 := mul_pos (neg_pos.mpr N.ha0) hDG4
    dsimp only [Dn]
    linarith
  · exact div_pos hb0 hDn
  · apply smul_right_injective ℝ³ hDn.ne'
    simp only [smul_add, smul_smul, mul_sub, mul_one, mul_div_cancel₀ _ hDn.ne']
    dsimp only [Dn, u35_24, del0, E35, DG4, D02, dG4]
    nf29_vec N

end Minimality.NF29
