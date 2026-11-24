module

public import Minimality.FaceChordFac
public import Minimality.Sym24Transport
public import Minimality.SlideDS
public import Minimality.RimFromSigns
public import Minimality.Q45Signs

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Sym
open Minimality.RimFromSigns Minimality.T24.Q45

namespace Minimality.T24.Mer

/-- The meridian view `u_{S->T}` of the face circle of facet `T` towards facet `S`:
the component of `F.N S` orthogonal to `F.N T` (times `⟪F.N T, F.N T⟫`).
`⟪F.N T, mer F S T⟫ = 0`, and `⟪x i - x j, mer F S T⟫ =
  ⟪F.N T, F.N T⟫ * (F.f S (x i) - F.f S (x j)) - ⟪F.N T, F.N S⟫ * (F.f T (x i) - F.f T (x j))`. -/
noncomputable def mer {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) : ℝ³ :=
  ⟪F.N T, F.N T⟫ • F.N S - ⟪F.N T, F.N S⟫ • F.N T

/-- Rim of case C1 (view `mer F 1 7`, circle 236): `0 1 2 3 4`, chord `2 → 3` (index 2). -/
def rimC1 : ZMod 5 → Fin 7 := ![0, 1, 2, 3, 4]

/-- Rim of the mirror case C1' (view `mer F 0 7`): `π ∘ rimC1 = 0 1 6 3 5`, chord `6 → 3`. -/
def rimC1' : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]

/-! ### Generic meridian & 5-rim helpers -/

private theorem inner_facet_mer {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) :
    ⟪F.N T, mer F S T⟫ = 0 := by
  simp only [mer, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

private theorem inner_source_mer_eq_normSq_cross {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (S T : Fin 9) :
    ⟪F.N S, mer F S T⟫ = ⟪cross (F.N T) (F.N S), cross (F.N T) (F.N S)⟫ := by
  simp only [mer, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

private theorem mer_eq_cross_cross {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) :
    mer F S T = cross (cross (F.N T) (F.N S)) (F.N T) := by
  ext j
  fin_cases j <;> (simp only [mer, cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring)

private theorem inner_cross_mer {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) :
    ⟪cross (F.N T) (F.N S), mer F S T⟫ = 0 := by
  rw [mer_eq_cross_cross, real_inner_comm]
  exact inner_cross_left _ _

private theorem inner_mer_self_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) :
    ⟪mer F S T, mer F S T⟫ =
      ⟪F.N T, F.N T⟫ * ⟪cross (F.N T) (F.N S), cross (F.N T) (F.N S)⟫ := by
  simp only [mer, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

/-- Generic chord-middle lemma: if `Q, R, P` lie on facet `T`, `Q, R` lie on facet `Fsep` while
`P ∉ S Fsep`, and `0 < ⟪x P - x Q, L⟫ * ⟪x R - x P, L⟫` for `L = cross (F.N T) (F.N S)`,
then `x P` lies strictly in the open slab `(0, 1)` along `x Q → x R` with non-zero `mer F S T` offset. -/
theorem chord_middle_of_mer {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T Fsep : Fin 9)
    (Q R P : Fin 7) (hQT : Q ∈ s0x_S24 T) (hRT : R ∈ s0x_S24 T) (hPT : P ∈ s0x_S24 T)
    (hQF : Q ∈ s0x_S24 Fsep) (hRF : R ∈ s0x_S24 Fsep) (hPF : P ∉ s0x_S24 Fsep)
    (hM2 : 0 < ⟪x P - x Q, cross (F.N T) (F.N S)⟫ * ⟪x R - x P, cross (F.N T) (F.N S)⟫) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x P = x Q + s • (x R - x Q) + δ • mer F S T := by
  set L := cross (F.N T) (F.N S)
  set u := mer F S T
  set e := x R - x Q
  set d := x P - x Q
  have hdL_ne : ⟪d, L⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hM2
    exact lt_irrefl 0 hM2
  have hL_ne : L ≠ 0 := by
    intro h0
    apply hdL_ne
    rw [h0, inner_zero_right]
  have hLL_pos : 0 < ⟪L, L⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hL_ne)
  have hNT_ne : F.N T ≠ 0 := by
    intro h0
    apply hL_ne
    simp [L, h0, cross]
  have hNT_pos : 0 < ⟪F.N T, F.N T⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hNT_ne)
  have hu_pos : 0 < ⟪u, u⟫ := by
    rw [show u = mer F S T from rfl, inner_mer_self_eq]
    exact mul_pos hNT_pos hLL_pos
  have hu_ne : u ≠ 0 := by
    intro h0
    simp [h0] at hu_pos
  have he_sub_d : x R - x P = e - d := by
    dsimp [e, d]; abel
  rw [he_sub_d] at hM2
  have heL_split : ⟪e, L⟫ = ⟪d, L⟫ + ⟪e - d, L⟫ := by
    rw [← inner_add_left, add_sub_cancel]
  have hprod : 0 < ⟪d, L⟫ * (⟪e, L⟫ - ⟪d, L⟫) := by
    simpa [heL_split] using hM2
  have heL_ne : ⟪e, L⟫ ≠ 0 := by
    intro h0
    rw [h0, zero_sub, mul_neg] at hprod
    have : 0 ≤ ⟪d, L⟫ * ⟪d, L⟫ := mul_self_nonneg _
    linarith
  set s := ⟪d, L⟫ / ⟪e, L⟫
  have heL2_pos : 0 < ⟪e, L⟫ ^ 2 := sq_pos_of_ne_zero heL_ne
  have hs_prod : s * (1 - s) * ⟪e, L⟫ ^ 2 = ⟪d, L⟫ * (⟪e, L⟫ - ⟪d, L⟫) := by
    dsimp [s]; field_simp
  have hs01 : 0 < s * (1 - s) := by
    have : 0 < s * (1 - s) * ⟪e, L⟫ ^ 2 := by linarith
    exact pos_of_mul_pos_left this heL2_pos.le
  have hs_pos : 0 < s := by
    by_contra hs_le
    push Not at hs_le
    by_cases h0 : s = 0
    · rw [h0, zero_mul] at hs01; exact lt_irrefl 0 hs01
    · have hs_neg : s < 0 := lt_of_le_of_ne hs_le h0
      have h1s_pos : 0 < 1 - s := by linarith
      have : s * (1 - s) < 0 := mul_neg_of_neg_of_pos hs_neg h1s_pos
      linarith
  have hs_lt : s < 1 := by
    by_contra h1_le
    push Not at h1_le
    have h1s_le : 1 - s ≤ 0 := by linarith
    have : s * (1 - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs_pos.le h1s_le
    linarith
  set D := d - s • e
  have hNT_d : ⟪F.N T, d⟫ = 0 := by
    have := (F.hN T (x P) (x Q)).symm
    rw [F.zero T P hPT, F.zero T Q hQT, sub_self] at this
    exact this
  have hNT_e : ⟪F.N T, e⟫ = 0 := by
    have := (F.hN T (x R) (x Q)).symm
    rw [F.zero T R hRT, F.zero T Q hQT, sub_self] at this
    exact this
  have hD_NT : ⟪D, F.N T⟫ = 0 := by
    dsimp [D]
    rw [inner_sub_left, real_inner_smul_left]
    rw [real_inner_comm] at hNT_d hNT_e
    rw [hNT_d, hNT_e, mul_zero, sub_zero]
  have hD_L : ⟪D, L⟫ = 0 := by
    dsimp [D, s]
    rw [inner_sub_left, real_inner_smul_left]
    field_simp
    ring
  have hu_NT : ⟪u, F.N T⟫ = 0 := by
    rw [real_inner_comm]
    exact inner_facet_mer F S T
  have hu_L : ⟪u, L⟫ = 0 := by
    rw [real_inner_comm]
    exact inner_cross_mer F S T
  have hNT_L_cross : cross (F.N T) L ≠ 0 := by
    have hcl : cross (F.N T) L = - u := by
      rw [show u = mer F S T from rfl, mer_eq_cross_cross]
      ext j; fin_cases j <;> simp [L, cross] <;> ring
    rw [hcl]
    exact neg_ne_zero.mpr hu_ne
  have huD_cross : cross u D = 0 :=
    cross_eq_zero_of_perp2 hu_NT hu_L hD_NT hD_L hNT_L_cross
  set δ := ⟪D, u⟫ / ⟪u, u⟫
  have hδ : D = δ • u := eq_smul_of_cross_eq_zero hu_ne huD_cross
  have hδ_ne : δ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hδ
    have hDP : x P = x Q + s • (x R - x Q) := by
      have : d = s • e := sub_eq_zero.mp hδ
      dsimp [d, e] at this
      rw [← this]
      abel
    have hFP0 : F.f Fsep (x P) = 0 := by
      have h1 := F.hN Fsep (x Q + s • (x R - x Q)) (x Q)
      rw [add_sub_cancel_left, real_inner_smul_right] at h1
      have h2 := (F.hN Fsep (x R) (x Q)).symm
      rw [F.zero Fsep R hRF, F.zero Fsep Q hQF, sub_self] at h2
      rw [h2, mul_zero, F.zero Fsep Q hQF, sub_zero] at h1
      rwa [hDP]
    have hFP_neg : F.f Fsep (x P) < 0 := F.neg Fsep P hPF
    linarith
  refine ⟨s, δ, hs_pos, hs_lt, hδ_ne, ?_⟩
  have : x P = x Q + d := by dsimp [d]; abel
  rw [this, show d = s • e + D by dsimp [D]; abel, hδ]
  dsimp [e, u]
  abel

/-- Generic 5-rim sign chaining: given 5 edges with non-zero multipliers `σ : ZMod 5 → ℝ` on
vertex sets `off : ZMod 5 → Finset (Fin N)` such that `r (i + 2) ∈ off i` and `r i ∈ off (i + 1)`
for `i = 0, 1, 2, 3`, a single `ρ = σ 0` works simultaneously for all 5 edges on `off i`. -/
private theorem rim5_chain {N : ℕ} {x : Fin N → ℝ³} (r : ZMod 5 → Fin N) (u : ℝ³)
    (off : ZMod 5 → Finset (Fin N))
    (h_edge : ∀ i : ZMod 5, ∃ σ : ℝ, σ ≠ 0 ∧ ∀ y ∈ off i,
      0 < σ * det3 (x (r (i + 1)) - x (r i)) (x y - x (r i)) u)
    (h_fwd : ∀ i : ZMod 5, i ≠ 4 → r (i + 2) ∈ off i)
    (h_bwd : ∀ i : ZMod 5, i ≠ 4 → r i ∈ off (i + 1)) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ∀ i : ZMod 5, ∀ y ∈ off i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x y - x (r i)) u := by
  choose σ hσ_ne hσ using h_edge
  have link : ∀ i : ZMod 5, i ≠ 4 → 0 < σ i * σ (i + 1) := fun i hi => by
    have h1 := hσ i (r (i + 2)) (h_fwd i hi)
    have h2 := hσ (i + 1) (r i) (h_bwd i hi)
    have hcyc : det3 (x (r (i + 1)) - x (r i)) (x (r (i + 2)) - x (r i)) u =
        det3 (x (r (i + 2)) - x (r (i + 1))) (x (r i) - x (r (i + 1))) u := by
      simpa [add_assoc] using det3_cycle_triangle (x (r i)) (x (r (i + 1))) (x (r (i + 2))) u
    rw [hcyc] at h1
    rw [show i + 1 + 1 = i + 2 by ring] at h2
    exact sign_prod h1 h2
  have h01 : 0 < σ 0 * σ 1 := link 0 (by decide)
  have h02 : 0 < σ 0 * σ 2 := sign_transfer h01 (link 1 (by decide))
  have h03 : 0 < σ 0 * σ 3 := sign_transfer h02 (link 2 (by decide))
  have h04 : 0 < σ 0 * σ 4 := sign_transfer h03 (link 3 (by decide))
  refine ⟨σ 0, hσ_ne 0, fun i y hy => ?_⟩
  fin_cases i
  · exact hσ 0 y hy
  · exact sign_transfer h01 (hσ 1 y hy)
  · exact sign_transfer h02 (hσ 2 y hy)
  · exact sign_transfer h03 (hσ 3 y hy)
  · exact sign_transfer h04 (hσ 4 y hy)

/-- **Meridian case C1 (Carbon A54, `M016>236`).**  At the meridian view `u₀ = mer F 1 7` on the
face circle of facet 7 (236), with the six rim-edge facet signs (M1), the chord-middle sign (M2:
vertex 6 projects strictly inside the chord `2 → 3`), distinct unimodal-or-separated rim depths
(M3) and a far vertex `w ∈ {0, 4, 1}` of Lemma H (M4), the rim `0 1 2 3 4` is a FaceChordView of
facet 7.  Witness: `u = mer F 1 7`, `k = 5`, `r = rimC1`, `a = 2`, `w = 0 / 4 / 1`, `ρ = ±1`. -/
theorem faceChordView_C1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 0, mer F 1 7⟫ < 0 ∧ 0 < ⟪F.N 5, mer F 1 7⟫ ∧ ⟪F.N 6, mer F 1 7⟫ < 0 ∧
      ⟪F.N 3, mer F 1 7⟫ < 0 ∧ 0 < ⟪F.N 8, mer F 1 7⟫ ∧ 0 < ⟪F.N 4, mer F 1 7⟫)
    (hM2 : 0 < ⟪x 6 - x 2, cross (F.N 7) (F.N 1)⟫ * ⟪x 3 - x 6, cross (F.N 7) (F.N 1)⟫)
    (hinj : Function.Injective fun i : ZMod 5 => ⟪x (rimC1 i), mer F 1 7⟫)
    (hz : UniOrSep (fun i : ZMod 5 => x (rimC1 i)) (mer F 1 7))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 0 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 4 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 1 - x 3, x 2 - x 3⟫ < 0))) :
    FaceChordView F 7 := by
  set u := mer F 1 7
  rcases hM1 with ⟨hN0, hN5, hN6, hN3, hN8, hN4⟩
  have hnu : ⟪F.N 7, u⟫ = 0 := inner_facet_mer F 1 7
  have hL_ne : cross (F.N 7) (F.N 1) ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right, zero_mul] at hM2
    exact lt_irrefl 0 hM2
  have hN1 : 0 < ⟪F.N 1, u⟫ := by
    dsimp [u]
    rw [inner_source_mer_eq_normSq_cross, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hL_ne)
  let off : ZMod 5 → Finset (Fin 7) :=
    ![(s0x_S24 0)ᶜ ∪ (s0x_S24 1)ᶜ,
      (s0x_S24 0)ᶜ ∪ (s0x_S24 5)ᶜ,
      (s0x_S24 7)ᶜ,
      (s0x_S24 3)ᶜ ∪ (s0x_S24 8)ᶜ,
      (s0x_S24 3)ᶜ ∪ (s0x_S24 4)ᶜ]
  have h_edge : ∀ i : ZMod 5, ∃ σ : ℝ, σ ≠ 0 ∧ ∀ y ∈ off i,
      0 < σ * det3 (x (rimC1 (i + 1)) - x (rimC1 i)) (x y - x (rimC1 i)) u := by
    intro i
    fin_cases i
    · have hcr : cross u (x 1 - x 0) ≠ 0 :=
        cross_ne_zero_of_facet_sign F 0 0 1 (by decide) (by decide) hN0.ne 2 (by decide) (by decide)
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_ridge F 0 1 0 1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN0, hN1⟩ hcr
      exact ⟨σ, hσ_ne, fun y hy => hσ y (by simpa [off] using hy)⟩
    · have hcr : cross u (x 2 - x 1) ≠ 0 :=
        cross_ne_zero_of_facet_sign F 0 1 2 (by decide) (by decide) hN0.ne 1 (by decide) (by decide)
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_ridge F 0 5 1 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN0, hN5⟩ hcr
      exact ⟨σ, hσ_ne, fun y hy => hσ y (by simpa [off] using hy)⟩
    · have hcr : cross u (x 3 - x 2) ≠ 0 :=
        cross_ne_zero_of_facet_sign F 6 2 3 (by decide) (by decide) hN6.ne 0 (by decide) (by decide)
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_edgeOn F 7 2 3 (by decide) (by decide) u hnu hcr
      exact ⟨σ, hσ_ne, fun y hy => hσ y (by simpa [off] using hy)⟩
    · have hcr : cross u (x 4 - x 3) ≠ 0 :=
        cross_ne_zero_of_facet_sign F 3 3 4 (by decide) (by decide) hN3.ne 6 (by decide) (by decide)
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_ridge F 3 8 3 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN3, hN8⟩ hcr
      exact ⟨σ, hσ_ne, fun y hy => hσ y (by simpa [off] using hy)⟩
    · have hcr : cross u (x 0 - x 4) ≠ 0 :=
        cross_ne_zero_of_facet_sign F 3 4 0 (by decide) (by decide) hN3.ne 8 (by decide) (by decide)
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_ridge F 3 4 4 0 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN3, hN4⟩ hcr
      exact ⟨σ, hσ_ne, fun y hy => hσ y (by simpa [off] using hy)⟩
  obtain ⟨ρ, hρ_ne, hρ⟩ := rim5_chain rimC1 u off h_edge
    (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
    (fun i hi => by fin_cases i <;> first | exact absurd rfl hi | decide)
  have hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (rimC1 (i + 1)) - x (rimC1 i)) (x (rimC1 j) - x (rimC1 i)) u := by
    intro i j hji hji1
    apply hρ i (rimC1 j)
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hji | exact absurd rfl hji1 | decide
  have hin : ∀ q : Fin 7, q ∉ s0x_S24 7 → (∀ j : ZMod 5, q ≠ rimC1 j) → ∀ i : ZMod 5,
      0 < ρ * det3 (x (rimC1 (i + 1)) - x (rimC1 i)) (x q - x (rimC1 i)) u := by
    intro q hqS hqr i
    have hq5 : q = 5 := by
      fin_cases q
      · exact absurd rfl (hqr 0)
      · exact absurd rfl (hqr 1)
      · exact absurd rfl (hqr 2)
      · exact absurd rfl (hqr 3)
      · exact absurd rfl (hqr 4)
      · rfl
      · exact absurd (by decide : (6 : Fin 7) ∈ s0x_S24 7) hqS
    subst hq5
    apply hρ i 5
    fin_cases i <;> decide
  have hmid : ∀ q ∈ s0x_S24 7, (∀ j : ZMod 5, q ≠ rimC1 j) →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        x q = x (rimC1 2) + s • (x (rimC1 (2 + 1)) - x (rimC1 2)) + δ • u := by
    intro q hqS hqr
    have hq6 : q = 6 := by
      fin_cases q <;> (first | exact absurd hqS (by decide) |
        exact absurd rfl (hqr 2) | exact absurd rfl (hqr 3) | rfl)
    subst hq6
    exact chord_middle_of_mer F 1 7 6 2 3 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hM2
  rcases hM4 with ⟨h01, h04, hoff0⟩ | ⟨h40, h41, hoff4⟩ | ⟨h10, h14, hoff1⟩
  · refine ⟨u, 5, inferInstance, rimC1, 2, 0, ρ, hnu, by decide, by decide, by decide, hρ_ne,
      hcyc, hin, hmid, hinj, hz, by decide, fun m hm hmr => ?_, hoff0⟩
    fin_cases m <;> (first | exact absurd rfl hm | exact absurd hmr (by decide) |
      simpa [rimC1] using h01 | simpa [rimC1] using h04)
  · refine ⟨u, 5, inferInstance, rimC1, 2, 4, ρ, hnu, by decide, by decide, by decide, hρ_ne,
      hcyc, hin, hmid, hinj, hz, by decide, fun m hm hmr => ?_, hoff4⟩
    fin_cases m <;> (first | exact absurd rfl hm | exact absurd hmr (by decide) |
      simpa [rimC1] using h40 | simpa [rimC1] using h41)
  · refine ⟨u, 5, inferInstance, rimC1, 2, 1, ρ, hnu, by decide, by decide, by decide, hρ_ne,
      hcyc, hin, hmid, hinj, hz, by decide, fun m hm hmr => ?_, hoff1⟩
    fin_cases m <;> (first | exact absurd rfl hm | exact absurd hmr (by decide) |
      simpa [rimC1] using h10 | simpa [rimC1] using h14)

/-- **Mirror case C1' (`M012>236`)**: `faceChordView_C1` for `sym24 F` (the `(2 6)(4 5)` relabelling,
facets `0↔1, 2↔4, 6↔8`), written out in `F`.  View `mer F 0 7`, rim `0 1 6 3 5`, chord `6 → 3`,
far vertex `w ∈ {0, 5, 1}`. -/
theorem faceChordView_C1' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 1, mer F 0 7⟫ < 0 ∧ 0 < ⟪F.N 5, mer F 0 7⟫ ∧ ⟪F.N 8, mer F 0 7⟫ < 0 ∧
      ⟪F.N 3, mer F 0 7⟫ < 0 ∧ 0 < ⟪F.N 6, mer F 0 7⟫ ∧ 0 < ⟪F.N 2, mer F 0 7⟫)
    (hM2 : 0 < ⟪x 2 - x 6, cross (F.N 7) (F.N 0)⟫ * ⟪x 3 - x 2, cross (F.N 7) (F.N 0)⟫)
    (hinj : Function.Injective fun i : ZMod 5 => ⟪x (rimC1' i), mer F 0 7⟫)
    (hz : UniOrSep (fun i : ZMod 5 => x (rimC1' i)) (mer F 0 7))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 0 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 5 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 1 - x 3, x 6 - x 3⟫ < 0))) :
    FaceChordView F 7 := by
  have hr : ∀ i : ZMod 5, (x ∘ pi24) (rimC1 i) = x (rimC1' i) := by
    intro i; fin_cases i <;> rfl
  have hm : mer (sym24 F) 1 7 = mer F 0 7 := rfl
  have h := faceChordView_C1 (sym24 F) (x := x ∘ pi24) hM1 hM2
    (by simp only [hr, hm]; exact hinj) (by simp only [hr, hm]; exact hz) hM4
  exact faceChordView_sym F h

end Minimality.T24.Mer
