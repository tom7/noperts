module

public import Minimality.Type29LeavesA16

@[expose] public section

/-!
# Type 29, `S1`: the views `W14` and `V46` cannot both fail at `t = 1`

On the K1a cell at `t = 1` (`x 5 - x 6 = s • (x 1 - x 4)`, `t1_par`), if the depth inequality
`z1(u46) ≥ z4(u46)` of the view `V46` holds then, with the weak obtuse corner at vertex 6 (`g35, g45 ≤ 0`),
`g35 = g45 = 0` (`g35_g45_zero_of_V46`), the `W14` depths are explicit and the rim `1 2 3 6 5` is
robustly unimodal at `b = x 1 - x 4` unless `s ≥ 1 ∧ D234 ≥ 1` (`lexAny29_W14_of_V46`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-- At `t = 1` the edge `56` is parallel to the edge `14`: `x 5 - x 6 = s • (x 1 - x 4)`. -/
theorem t1_par (N : NF29 x) (ht : N.t = 1) : x 5 - x 6 = N.s • (x 1 - x 4) := by
  nf29_simp N
  rw [ht]
  ext i
  simp only [nfV, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The view vector of `V46`: `u46 = U5 e3 + D023 e4`, `e_i = x i - x 6`, `U5 = DG4 - D023`. -/
noncomputable def u46 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  (N.DG4 - N.D023) • (x 3 - x 6) + N.D023 • (x 4 - x 6)

theorem D023_pos (N : NF29 x) : 0 < N.D023 := by
  have := N.d023
  dsimp only [D023, D02, dG4, dG]
  linarith

/-- At `t = 1`, `s (z1 - z4)(u46) = z5(u46) = U5 g35 + D023 g45`. -/
theorem V46_depth_t1 (N : NF29 x) (ht : N.t = 1) :
    N.s * (⟪x 1 - x 6, N.u46 x⟫ - ⟪x 4 - x 6, N.u46 x⟫) =
      (N.DG4 - N.D023) * ⟪x 3 - x 6, x 5 - x 6⟫ + N.D023 * ⟪x 4 - x 6, x 5 - x 6⟫ := by
  have h5 := t1_par N ht
  have h14 : x 1 - x 6 = (x 1 - x 4) + (x 4 - x 6) := by abel
  rw [← inner_sub_left, h14, add_sub_cancel_right, ← real_inner_smul_left, ← h5]
  simp only [u46, inner_add_right, real_inner_smul_right]
  rw [real_inner_comm (x 5 - x 6) (x 3 - x 6), real_inner_comm (x 5 - x 6) (x 4 - x 6)]

/-- The `V46` consequence at `t = 1`: weak `OB6` (`g35, g45 ≤ 0`) and `z1(u46) ≥ z4(u46)` give
`g35 = g45 = 0`. -/
theorem g35_g45_zero_of_V46 (N : NF29 x) (ht : N.t = 1) (hU5 : 0 < N.DG4 - N.D023)
    (hg35 : ⟪x 3 - x 6, x 5 - x 6⟫ ≤ 0) (hg45 : ⟪x 4 - x 6, x 5 - x 6⟫ ≤ 0)
    (hA46 : ⟪x 4 - x 6, N.u46 x⟫ ≤ ⟪x 1 - x 6, N.u46 x⟫) :
    ⟪x 3 - x 6, x 5 - x 6⟫ = 0 ∧ ⟪x 4 - x 6, x 5 - x 6⟫ = 0 := by
  have h := V46_depth_t1 N ht
  have hs := N.hs
  have hD := D023_pos N
  have h1 : 0 ≤ N.s * (⟪x 1 - x 6, N.u46 x⟫ - ⟪x 4 - x 6, N.u46 x⟫) :=
    mul_nonneg hs.le (by linarith)
  have a := mul_nonpos_of_nonneg_of_nonpos hU5.le hg35
  have b := mul_nonpos_of_nonneg_of_nonpos hD.le hg45
  constructor
  · by_contra hne
    have : ⟪x 3 - x 6, x 5 - x 6⟫ < 0 := lt_of_le_of_ne hg35 hne
    nlinarith
  · by_contra hne
    have : ⟪x 4 - x 6, x 5 - x 6⟫ < 0 := lt_of_le_of_ne hg45 hne
    nlinarith


/-- Depths at `b = x 1 - x 4` at `t = 1` once `g35 = g45 = 0`: `z3 = z4 = 0`, `z1 = |b|^2`, `z5 = s |b|^2`,
`z2 = D234 |b|^2` (this is `(G55 / s^2) (p0, 1, D234, 0, 0, s, 0)`). -/
theorem W14_depths_t1 (N : NF29 x) (ht : N.t = 1)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0) :
    ⟪x 3 - x 6, x 1 - x 4⟫ = 0 ∧ ⟪x 4 - x 6, x 1 - x 4⟫ = 0 ∧
    ⟪x 1 - x 6, x 1 - x 4⟫ = ⟪x 1 - x 4, x 1 - x 4⟫ ∧
    ⟪x 5 - x 6, x 1 - x 4⟫ = N.s * ⟪x 1 - x 4, x 1 - x 4⟫ ∧
    ⟪x 2 - x 6, x 1 - x 4⟫ = N.D234 * ⟪x 1 - x 4, x 1 - x 4⟫ := by
  have h5 := t1_par N ht
  have hs : N.s ≠ 0 := N.hs.ne'
  have hb3 : ⟪x 3 - x 6, x 1 - x 4⟫ = 0 := by
    have : ⟪x 3 - x 6, x 5 - x 6⟫ = N.s * ⟪x 3 - x 6, x 1 - x 4⟫ := by
      rw [h5, real_inner_smul_right]
    rw [h35] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hs
    · exact h
  have hb4 : ⟪x 4 - x 6, x 1 - x 4⟫ = 0 := by
    have : ⟪x 4 - x 6, x 5 - x 6⟫ = N.s * ⟪x 4 - x 6, x 1 - x 4⟫ := by
      rw [h5, real_inner_smul_right]
    rw [h45] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hs
    · exact h
  have h14 : x 1 - x 6 = (x 1 - x 4) + (x 4 - x 6) := by abel
  have h2v : x 2 - x 6 = N.h2 • (x 3 - x 6) + (1 - N.b2 - N.h2) • (x 4 - x 6) +
      (N.D234 / N.s) • (x 5 - x 6) := by
    dsimp only [D234]
    nf29_simp N
    rw [ht]
    ext i
    simp only [nfV, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨hb3, hb4, ?_, ?_, ?_⟩
  · rw [h14, inner_add_left, hb4, add_zero]
  · rw [h5, real_inner_smul_left]
  · rw [h2v, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, hb3, hb4, h5, real_inner_smul_left]
    field_simp
    ring

/-- A five-cycle with a valley plateau `z 2 = z 3`: robustly unimodal (no tie-break needed) when `z 2` is below
`z 1` and `z 0`, `z 3` below `z 4`, and one of `z 1`, `z 4` is below `z 0`. -/
theorem rob5_t1 (z e : ZMod 5 → ℝ) (hp : z 1 < z 0 ∨ z 4 < z 0) (h21 : z 2 < z 1) (h20 : z 2 < z 0)
    (h34 : z 3 < z 4) (h23 : z 2 = z 3) :
    RobUniLex (fun i => (z i, e i, (0 : ℝ))) := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl] <;>
  unfold LexLt3 LexPos3 <;> simp only <;>
  rcases hp with hp | hp <;> rcases lt_trichotomy (z 1) (z 4) with h14 | h14 | h14 <;>
  first
    | (left; left; linarith)
    | (right; left; left; linarith)
    | (right; right; left; left; linarith)
    | (right; right; right; left; linarith)

local macro "w14p_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG4, P5, f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))


private def w14p_c : ZMod 5 → Fin 7 := ![1, 2, 3, 6, 5]
private def w14p_U : Finset (Fin 9) := {0, 1, 2, 3, 8}
private def w14p_Dn : Finset (Fin 9) := {4, 5, 6, 7}

private theorem w14p_c_inj : Function.Injective w14p_c := by decide
private theorem w14p_cyc : S0xCycUD s0x_S29 w14p_c w14p_U w14p_Dn := by decide


/-- **S1: `W14` x `V46` at `t = 1`.** On the K1a cell at `t = 1`, if `z1(u46) ≥ z4(u46)` (the `V46` view does not
separate) and the corner at vertex 6 is weakly obtuse at `g35, g45`, then the `W14` leaf (rim `1 2 3 6 5` at
`b = x 1 - x 4`) is a `LexAny29` leaf unless `s ≥ 1 ∧ D234 ≥ 1` (`hsD` is a sample fact). -/
theorem lexAny29_W14_of_V46 (N : NF29 x)
    (ht : N.t = 1) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hU5 : 0 < N.DG4 - N.D023)
    (hsD : N.s < 1 ∨ N.D234 < 1)
    (hg35 : ⟪x 3 - x 6, x 5 - x 6⟫ ≤ 0) (hg45 : ⟪x 4 - x 6, x 5 - x 6⟫ ≤ 0)
    (hA46 : ⟪x 4 - x 6, N.u46 x⟫ ≤ ⟪x 1 - x 6, N.u46 x⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  obtain ⟨h35, h45⟩ := g35_g45_zero_of_V46 N ht hU5 hg35 hg45 hA46
  obtain ⟨q3, q4, q1, q5, q2⟩ := W14_depths_t1 N ht h35 h45
  let F := s0x_fac29 N.facets
  let c := w14p_c
  let U := w14p_U
  let Dn := w14p_Dn
  let b : ℝ³ := x 1 - x 4
  let d1 : ℝ³ := x 3 - x 4
  have hc_inj : Function.Injective c := w14p_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := w14p_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, 0⟫ := by
    intro t ht_mem
    have hnb : ⟪F.N t, b⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 4) := (F.hN t (x 3) (x 4)).symm
    rw [hnb, hnd1]
    fin_cases t
    · refine Or.inl ?_
      have hv : N.f012.f (x 1) - N.f012.f (x 4) = N.P5 * N.D ^ 2 := by w14p_fac_val N
      change 0 < N.f012.f (x 1) - N.f012.f (x 4)
      rw [hv]
      exact mul_pos (by dsimp [P5]; linarith [N.hF4]) hD2
    · refine Or.inl ?_
      have hv : N.f015.f (x 1) - N.f015.f (x 4) = N.h0 * N.D ^ 2 := by w14p_fac_val N
      change 0 < N.f015.f (x 1) - N.f015.f (x 4)
      rw [hv]
      exact mul_pos N.hh0 hD2
    · refine Or.inl ?_
      have hv : N.f023.f (x 1) - N.f023.f (x 4) = N.dG4 * N.D ^ 2 := by w14p_fac_val N
      change 0 < N.f023.f (x 1) - N.f023.f (x 4)
      rw [hv]
      exact mul_pos hdG4 hD2
    · refine Or.inl ?_
      have hv : N.f035.f (x 1) - N.f035.f (x 4) = (1 - N.b0 - N.h0) * N.D ^ 2 := by
        w14p_fac_val N
      change 0 < N.f035.f (x 1) - N.f035.f (x 4)
      rw [hv]
      exact mul_pos hA hD2
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · have hb0 : N.f356.f (x 1) - N.f356.f (x 4) = 0 := by
        have hv : N.f356.f (x 1) - N.f356.f (x 4) = (N.t - 1) * N.D ^ 2 := by w14p_fac_val N
        rw [hv, ht]; ring
      have hd1v : N.f356.f (x 3) - N.f356.f (x 4) = (N.t - 1 + N.s) * N.D ^ 2 := by
        w14p_fac_val N
      refine Or.inr ⟨hb0, Or.inl ?_⟩
      change 0 < N.f356.f (x 3) - N.f356.f (x 4)
      rw [hd1v, ht]
      exact mul_pos (by linarith [N.hs]) hD2
  have hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, 0⟫) := by
    intro t ht_mem
    have hnb : ⟪F.N t, b⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 4) := (F.hN t (x 3) (x 4)).symm
    rw [hnb, hnd1]
    fin_cases t
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · have hb0 : N.f124.f (x 1) - N.f124.f (x 4) = 0 := by w14p_fac_val N
      have hd1v : N.f124.f (x 3) - N.f124.f (x 4) = N.b2 * N.D ^ 2 := by w14p_fac_val N
      refine Or.inr ⟨by change -(N.f124.f (x 1) - N.f124.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f124.f (x 3) - N.f124.f (x 4))
      rw [hd1v]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · have hb0 : N.f1456.f (x 1) - N.f1456.f (x 4) = 0 := by w14p_fac_val N
      have hd1v : N.f1456.f (x 3) - N.f1456.f (x 4) = -N.D ^ 2 := by w14p_fac_val N
      refine Or.inr ⟨by change -(N.f1456.f (x 1) - N.f1456.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f1456.f (x 3) - N.f1456.f (x 4))
      rw [hd1v, neg_neg]
      exact hD2
    · refine Or.inl ?_
      have hv : N.f234.f (x 1) - N.f234.f (x 4) = N.b2 * N.D ^ 2 := by w14p_fac_val N
      change 0 < -(N.f234.f (x 1) - N.f234.f (x 4))
      rw [hv]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · refine Or.inl ?_
      have hv : N.f346.f (x 1) - N.f346.f (x 4) = -N.t * N.D ^ 2 := by w14p_fac_val N
      change 0 < -(N.f346.f (x 1) - N.f346.f (x 4))
      rw [hv, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos N.ht hD2
    · exact absurd ht_mem (by decide)
  have hb_ne : b ≠ 0 := sub_ne_zero.mpr (N.inj.ne (by decide))
  have hb_sq : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hb_ne
  have hD234 : 0 < N.D234 := by
    have := N.d234
    dsimp only [D234]
    linarith
  have e1 : ⟪x 1, b⟫ - ⟪x 6, b⟫ = ⟪b, b⟫ := by rw [← inner_sub_left]; exact q1
  have e2 : ⟪x 2, b⟫ - ⟪x 6, b⟫ = N.D234 * ⟪b, b⟫ := by rw [← inner_sub_left]; exact q2
  have e3 : ⟪x 3, b⟫ - ⟪x 6, b⟫ = 0 := by rw [← inner_sub_left]; exact q3
  have e5 : ⟪x 5, b⟫ - ⟪x 6, b⟫ = N.s * ⟪b, b⟫ := by rw [← inner_sub_left]; exact q5
  have p2 := mul_pos hD234 hb_sq
  have p5 := mul_pos N.hs hb_sq
  have hRob : RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), 0⟫)) := by
    have h := rob5_t1 (fun i => ⟪x (c i), b⟫) (fun i => ⟪x (c i), d1⟫)
      (by
        change ⟪x 2, b⟫ < ⟪x 1, b⟫ ∨ ⟪x 5, b⟫ < ⟪x 1, b⟫
        rcases hsD with h | h
        · right; nlinarith [mul_pos (sub_pos.mpr h) hb_sq]
        · left; nlinarith [mul_pos (sub_pos.mpr h) hb_sq])
      (by change ⟪x 3, b⟫ < ⟪x 2, b⟫; linarith)
      (by change ⟪x 3, b⟫ < ⟪x 1, b⟫; linarith)
      (by change ⟪x 6, b⟫ < ⟪x 5, b⟫; linarith)
      (by change ⟪x 3, b⟫ = ⟪x 6, b⟫; linarith)
    simpa only [inner_zero_right] using h
  exact ⟨5, inferInstance, c, U, Dn, b, d1, 0, by norm_num, hc_inj, hcyc, hU, hD, hRob⟩

end Minimality.NF29
