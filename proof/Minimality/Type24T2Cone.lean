module

public import Minimality.Type24WDCell

/-!
# Hidden-`2` cone `T_2` (`cA2 = ![0, 5, 3, 6, 1]`, `cB2 = ![0, 5, 3, 4, 6, 1]`, Carbon A85)

* `FS2` (`edgePlaneAt_of_T2`, `edgePlaneAny_of_T2`, `uT2_four_facets`, `cA2_cellAt_iff`,
  `cB2_cellAt_iff`, `cA2_edgePlaneAny`, `cB2_edgePlaneAny`, `CA2CertAt`, `CB2CertAt`,
  hole facts, `π_24` twins, `TwoConeResidue_FS2`, `hole24_twoConeResidue_FS2`):
  transfer of `EdgePlaneAt` from `x ∘ (2 : Fin 7).succAbove` to `x` on the 5-facet cone
  `T_2 = {0, 2, 5, 6, 7}` around vertex `2`, automatic `HiddenInTriangles` for vertex `4`
  on `cA2` via `hidden_of_three_facets`, and interior line-separation leaves + `π_24` twins.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-! ## `edgePlaneAt_of_T2`: transferring `EdgePlaneAt` across hidden vertex `2` -/

/-- **FS2 (Lemma T2):** If all five facets `{0, 2, 5, 6, 7}` incident to vertex `2` have
one strict sign at `w`, then `EdgePlaneAt (x ∘ (2 : Fin 7).succAbove) w` implies
`EdgePlaneAt x w`. -/
theorem edgePlaneAt_of_T2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hw : (∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), ⟪F.N t, w⟫ < 0) ∨
          (∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), 0 < ⟪F.N t, w⟫))
    (hEP : EdgePlaneAt (x ∘ (2 : Fin 7).succAbove) w) :
    EdgePlaneAt x w := by
  suffices hneg : ∀ w' : ℝ³,
      (∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), ⟪F.N t, w'⟫ < 0) →
      EdgePlaneAt (x ∘ (2 : Fin 7).succAbove) w' → EdgePlaneAt x w' by
    rcases hw with hw_neg | hw_pos
    · exact hneg w hw_neg hEP
    · have hw_neg : ∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), ⟪F.N t, -w⟫ < 0 := fun t ht => by
        rw [inner_neg_right, neg_lt_zero]; exact hw_pos t ht
      exact (edgePlaneAt_neg_iff x w).mp (hneg (-w) hw_neg ((edgePlaneAt_neg_iff _ w).mpr hEP))
  intro w' hw' hEP'
  let e0 := x 0 - x 2
  let e1 := x 1 - x 2
  let e3 := x 3 - x 2
  let e5 := x 5 - x 2
  let e6 := x 6 - x 2
  have hdet_ne : Split.det3 e0 e1 e6 ≠ 0 := by
    have hne := (M4.type24OfFac F).det_ne
    intro h0; apply hne
    have heq : det24 x = -Split.det3 e0 e1 e6 := by
      dsimp only [e0, e1, e6]
      simp only [det24, vol3, Split.det3, PiLp.sub_apply]
      ring
    rw [heq, h0, neg_zero]
  have hcross_eq : ∀ (t : Fin 9) (u v : ℝ³) (hu : ⟪F.N t, u⟫ = 0) (hv : ⟪F.N t, v⟫ = 0)
      (q0 : Fin 7) (hq0 : ⟪F.N t, x q0 - x 2⟫ < 0)
      (hdq : Split.det3 u v (x q0 - x 2) ≠ 0) (z : ℝ³),
      Split.det3 u v z * ⟪F.N t, x q0 - x 2⟫ = Split.det3 u v (x q0 - x 2) * ⟪F.N t, z⟫ := by
    intro t u v hu hv q0 hq0 hdq z
    let N := F.N t
    let d0 := x q0 - x 2
    have horth : ∀ r : ℝ³, ⟪r, u⟫ = 0 → ⟪r, v⟫ = 0 → ⟪r, d0⟫ = 0 → r = 0 := by
      intro r hru hrv hrd
      have hlin : ∀ y : ℝ³, Split.det3 u v d0 * ⟪r, y⟫ = 0 := by
        intro y
        have hid : Split.det3 u v d0 * ⟪r, y⟫ =
            ⟪r, u⟫ * Split.det3 v d0 y - ⟪r, v⟫ * Split.det3 u d0 y + ⟪r, d0⟫ * Split.det3 u v y := by
          simp only [Split.det3, Split.inner3]; ring
        rw [hid, hru, hrv, hrd]; ring
      have hr0 : ⟪r, r⟫ = 0 := (mul_eq_zero.mp (hlin r)).resolve_left hdq
      exact inner_self_eq_zero.mp hr0
    let r := Split.det3 u v d0 • N - ⟪N, d0⟫ • cross u v
    have hr0 : r = 0 := horth r
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hu, mul_zero,
        show ⟪cross u v, u⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
        mul_zero, sub_zero])
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hv, mul_zero,
        show ⟪cross u v, v⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
        mul_zero, sub_zero])
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
          have : ⟪cross u v, d0⟫ = Split.det3 u v d0 := by
            simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
          rw [this]; ring)
    have hrz : ⟪r, z⟫ = 0 := by rw [hr0, inner_zero_left]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hrz
    have hcz : ⟪cross u v, z⟫ = Split.det3 u v z := by
      simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
    rw [hcz] at hrz
    linarith
  have hplane_pos : ∀ (t : Fin 9) (ht : t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9))) (u v : ℝ³)
      (hu : ⟪F.N t, u⟫ = 0) (hv : ⟪F.N t, v⟫ = 0)
      (q0 : Fin 7) (hq0 : ⟪F.N t, x q0 - x 2⟫ < 0)
      (σ : ℝ) (hσq : 0 < σ * Split.det3 u v (x q0 - x 2)),
      0 < σ * Split.det3 u v w' := by
    intro t ht u v hu hv q0 hq0 σ hσq
    have hdq : Split.det3 u v (x q0 - x 2) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hσq; exact lt_irrefl 0 hσq
    have hcw := hcross_eq t u v hu hv q0 hq0 hdq w'
    have hNw : ⟪F.N t, w'⟫ < 0 := hw' t ht
    have hmul : 0 < (σ * Split.det3 u v (x q0 - x 2)) * ⟪F.N t, w'⟫ * ⟪F.N t, x q0 - x 2⟫ := by
      nlinarith [mul_neg_of_pos_of_neg hσq hNw]
    have heq : (σ * Split.det3 u v w') * (⟪F.N t, x q0 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫) =
        (σ * Split.det3 u v (x q0 - x 2)) * ⟪F.N t, w'⟫ * ⟪F.N t, x q0 - x 2⟫ := by
      calc (σ * Split.det3 u v w') * (⟪F.N t, x q0 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫)
          = σ * (Split.det3 u v w' * ⟪F.N t, x q0 - x 2⟫) * ⟪F.N t, x q0 - x 2⟫ := by ring
        _ = σ * (Split.det3 u v (x q0 - x 2) * ⟪F.N t, w'⟫) * ⟪F.N t, x q0 - x 2⟫ := by rw [hcw]
        _ = (σ * Split.det3 u v (x q0 - x 2)) * ⟪F.N t, w'⟫ * ⟪F.N t, x q0 - x 2⟫ := by ring
    rw [← heq] at hmul
    have hsq : 0 < ⟪F.N t, x q0 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫ := mul_self_pos.mpr hq0.ne
    exact (mul_pos_iff.mp hmul).elim (fun h => h.1) (fun h => absurd h.2 (not_lt_of_gt hsq))
  have hf_lt : ∀ (t : Fin 9) (q : Fin 7), (2 : Fin 7) ∈ s0x_S24 t → q ∉ s0x_S24 t →
      ⟪F.N t, x q - x 2⟫ < 0 := by
    intro t q h2t hq
    rw [F.inner_sub t q 2, F.zero t 2 h2t, sub_zero]
    exact F.neg t q hq
  have h00 : ⟪F.N 0, e0⟫ = 0 := by rw [F.inner_sub 0 0 2, F.zero 0 0 (by decide), F.zero 0 2 (by decide), sub_self]
  have h10 : ⟪F.N 0, e1⟫ = 0 := by rw [F.inner_sub 0 1 2, F.zero 0 1 (by decide), F.zero 0 2 (by decide), sub_self]
  have h15 : ⟪F.N 5, e1⟫ = 0 := by rw [F.inner_sub 5 1 2, F.zero 5 1 (by decide), F.zero 5 2 (by decide), sub_self]
  have h65 : ⟪F.N 5, e6⟫ = 0 := by rw [F.inner_sub 5 6 2, F.zero 5 6 (by decide), F.zero 5 2 (by decide), sub_self]
  have h67 : ⟪F.N 7, e6⟫ = 0 := by rw [F.inner_sub 7 6 2, F.zero 7 6 (by decide), F.zero 7 2 (by decide), sub_self]
  have h37 : ⟪F.N 7, e3⟫ = 0 := by rw [F.inner_sub 7 3 2, F.zero 7 3 (by decide), F.zero 7 2 (by decide), sub_self]
  have h36 : ⟪F.N 6, e3⟫ = 0 := by rw [F.inner_sub 6 3 2, F.zero 6 3 (by decide), F.zero 6 2 (by decide), sub_self]
  have h56 : ⟪F.N 6, e5⟫ = 0 := by rw [F.inner_sub 6 5 2, F.zero 6 5 (by decide), F.zero 6 2 (by decide), sub_self]
  have h52 : ⟪F.N 2, e5⟫ = 0 := by rw [F.inner_sub 2 5 2, F.zero 2 5 (by decide), F.zero 2 2 (by decide), sub_self]
  have h02 : ⟪F.N 2, e0⟫ = 0 := by rw [F.inner_sub 2 0 2, F.zero 2 0 (by decide), F.zero 2 2 (by decide), sub_self]
  let σ : ℝ := if 0 < Split.det3 e0 e1 e6 then 1 else -1
  have hσD : 0 < σ * Split.det3 e0 e1 e6 := by
    dsimp only [σ]
    split_ifs with h
    · simpa using h
    · have hlt : Split.det3 e0 e1 e6 < 0 := lt_of_le_of_ne (not_lt.mp h) hdet_ne
      nlinarith
  have hprop : ∀ (t : Fin 9) (u v : ℝ³) (hu : ⟪F.N t, u⟫ = 0) (hv : ⟪F.N t, v⟫ = 0)
      (q0 q1 : Fin 7) (hq0 : (2 : Fin 7) ∈ s0x_S24 t) (hq0' : q0 ∉ s0x_S24 t) (hq1' : q1 ∉ s0x_S24 t)
      (hσq0 : 0 < σ * Split.det3 u v (x q0 - x 2)),
      0 < σ * Split.det3 u v (x q1 - x 2) := by
    intro t u v hu hv q0 q1 hq0 hq0' hq1' hσq0
    have hlt0 := hf_lt t q0 hq0 hq0'
    have hlt1 := hf_lt t q1 hq0 hq1'
    have hdq0 : Split.det3 u v (x q0 - x 2) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hσq0; exact lt_irrefl 0 hσq0
    have hcw := hcross_eq t u v hu hv q0 hlt0 hdq0 (x q1 - x 2)
    have hmul : 0 < (σ * Split.det3 u v (x q0 - x 2)) * ⟪F.N t, x q1 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫ := by
      nlinarith [mul_neg_of_pos_of_neg hσq0 hlt1]
    have heq : (σ * Split.det3 u v (x q1 - x 2)) * (⟪F.N t, x q0 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫) =
        (σ * Split.det3 u v (x q0 - x 2)) * ⟪F.N t, x q1 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫ := by
      calc (σ * Split.det3 u v (x q1 - x 2)) * (⟪F.N t, x q0 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫)
          = σ * (Split.det3 u v (x q1 - x 2) * ⟪F.N t, x q0 - x 2⟫) * ⟪F.N t, x q0 - x 2⟫ := by ring
        _ = σ * (Split.det3 u v (x q0 - x 2) * ⟪F.N t, x q1 - x 2⟫) * ⟪F.N t, x q0 - x 2⟫ := by rw [hcw]
        _ = (σ * Split.det3 u v (x q0 - x 2)) * ⟪F.N t, x q1 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫ := by ring
    rw [← heq] at hmul
    have hsq : 0 < ⟪F.N t, x q0 - x 2⟫ * ⟪F.N t, x q0 - x 2⟫ := mul_self_pos.mpr hlt0.ne
    exact (mul_pos_iff.mp hmul).elim (fun h => h.1) (fun h => absurd h.2 (not_lt_of_gt hsq))
  -- Propagate sign `σ` around `(e0, e1, e6, e3, e5)`:
  have hs_015 : 0 < σ * Split.det3 e0 e1 e5 :=
    hprop 0 e0 e1 h00 h10 6 5 (by decide) (by decide) (by decide) hσD
  have hs_013 : 0 < σ * Split.det3 e0 e1 e3 :=
    hprop 0 e0 e1 h00 h10 6 3 (by decide) (by decide) (by decide) hσD
  have hs_160 : 0 < σ * Split.det3 e1 e6 e0 := by
    have : Split.det3 e1 e6 e0 = Split.det3 e0 e1 e6 := by simp only [Split.det3]; ring
    rw [this]; exact hσD
  have hs_163 : 0 < σ * Split.det3 e1 e6 e3 :=
    hprop 5 e1 e6 h15 h65 0 3 (by decide) (by decide) (by decide) hs_160
  have hs_631 : 0 < σ * Split.det3 e6 e3 e1 := by
    have : Split.det3 e6 e3 e1 = Split.det3 e1 e6 e3 := by simp only [Split.det3]; ring
    rw [this]; exact hs_163
  have hs_635 : 0 < σ * Split.det3 e6 e3 e5 :=
    hprop 7 e6 e3 h67 h37 1 5 (by decide) (by decide) (by decide) hs_631
  have hs_356 : 0 < σ * Split.det3 e3 e5 e6 := by
    have : Split.det3 e3 e5 e6 = Split.det3 e6 e3 e5 := by simp only [Split.det3]; ring
    rw [this]; exact hs_635
  have hs_350 : 0 < σ * Split.det3 e3 e5 e0 :=
    hprop 6 e3 e5 h36 h56 6 0 (by decide) (by decide) (by decide) hs_356
  have hs_501 : 0 < σ * Split.det3 e5 e0 e1 := by
    have : Split.det3 e5 e0 e1 = Split.det3 e0 e1 e5 := by simp only [Split.det3]; ring
    rw [this]; exact hs_015
  have hw_01 : 0 < σ * Split.det3 e0 e1 w' :=
    hplane_pos 0 (by decide) e0 e1 h00 h10 6 (hf_lt 0 6 (by decide) (by decide)) σ hσD
  have hw_16 : 0 < σ * Split.det3 e1 e6 w' :=
    hplane_pos 5 (by decide) e1 e6 h15 h65 0 (hf_lt 5 0 (by decide) (by decide)) σ hs_160
  have hw_63 : 0 < σ * Split.det3 e6 e3 w' :=
    hplane_pos 7 (by decide) e6 e3 h67 h37 1 (hf_lt 7 1 (by decide) (by decide)) σ hs_631
  have hw_35 : 0 < σ * Split.det3 e3 e5 w' :=
    hplane_pos 6 (by decide) e3 e5 h36 h56 6 (hf_lt 6 6 (by decide) (by decide)) σ hs_356
  have hw_50 : 0 < σ * Split.det3 e5 e0 w' :=
    hplane_pos 2 (by decide) e5 e0 h52 h02 1 (hf_lt 2 1 (by decide) (by decide)) σ
      (by have : Split.det3 e5 e0 (x 1 - x 2) = Split.det3 e5 e0 e1 := rfl; rw [this]; exact hs_501)
  have htri : ∃ a b c : ℝ³,
      (a ∈ ({e0, e1, e6, e3, e5} : Finset ℝ³) ∧
       b ∈ ({e0, e1, e6, e3, e5} : Finset ℝ³) ∧
       c ∈ ({e0, e1, e6, e3, e5} : Finset ℝ³)) ∧
      0 < Split.det3 (b - a) (c - a) w' ∧
      0 < Split.det3 (b - a) (-a) w' ∧
      0 < Split.det3 (c - b) (-b) w' ∧
      0 < Split.det3 (a - c) (-c) w' := by
    dsimp only [σ] at hw_01 hw_16 hw_63 hw_35 hw_50
    split_ifs at hw_01 hw_16 hw_63 hw_35 hw_50
    · exact triangle_of_five_ccw e0 e1 e6 e3 e5 w'
        (by simpa using hw_01) (by simpa using hw_16) (by simpa using hw_63)
        (by simpa using hw_35) (by simpa using hw_50)
    · have flip : ∀ u v : ℝ³, -1 * Split.det3 u v w' = Split.det3 v u w' := fun u v => by
        simp only [Split.det3]; ring
      rw [flip] at hw_01 hw_16 hw_63 hw_35 hw_50
      obtain ⟨a, b, c, ⟨ha, hb, hc⟩, t1, t2, t3, t4⟩ :=
        triangle_of_five_ccw e0 e5 e3 e6 e1 w' hw_50 hw_35 hw_63 hw_16 hw_01
      refine ⟨a, b, c, ⟨?_, ?_, ?_⟩, t1, t2, t3, t4⟩
      · rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; (have := Finset.mem_singleton.mp ha; subst this; simp)]]]]
      · rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; (have := Finset.mem_singleton.mp hb; subst this; simp)]]]]
      · rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; (have := Finset.mem_singleton.mp hc; subst this; simp)]]]]
  rcases htri with ⟨a, b, c, ⟨ha, hb, hc⟩, t1, t2, t3, t4⟩
  have hmem_base : ∀ e : ℝ³, e ∈ ({e0, e1, e6, e3, e5} : Finset ℝ³) →
      e + x 2 ∈ Finset.univ.image (x ∘ (2 : Fin 7).succAbove) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and]
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by dsimp [e0]; abel⟩
    · exact ⟨1, by dsimp [e1]; abel⟩
    · exact ⟨5, by dsimp [e6]; abel⟩
    · exact ⟨2, by dsimp [e3]; abel⟩
    · exact ⟨4, by dsimp [e5]; abel⟩
  refine edgePlaneAt_of_hidden (x := x) (v := 2) (w := w') hEP'
    ⟨a + x 2, b + x 2, c + x 2, hmem_base a ha, hmem_base b hb, hmem_base c hc, ?_, ?_, ?_, ?_⟩
  · simpa [add_sub_add_right_eq_sub] using t1
  · simpa [sub_add_cancel_right, add_sub_add_right_eq_sub] using t2
  · simpa [sub_add_cancel_right, add_sub_add_right_eq_sub] using t3
  · simpa [sub_add_cancel_right, add_sub_add_right_eq_sub] using t4

theorem edgePlaneAny_of_T2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hw : (∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), ⟪F.N t, w⟫ < 0) ∨
          (∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), 0 < ⟪F.N t, w⟫))
    (hEP : EdgePlaneAt (x ∘ (2 : Fin 7).succAbove) w) :
    Gen.EdgePlaneAny x :=
  (edgePlaneAny_iff_exists_at x).mpr ⟨w, edgePlaneAt_of_T2 F hw hEP⟩

/-! ## `T_2` cone cells `cA2 = ![0, 5, 3, 6, 1]` and `cB2 = ![0, 5, 3, 4, 6, 1]` -/

/-- Rim `cA2 = ![0, 5, 3, 6, 1]` (`3.5.0.1.6` reversed, hiding `2` and `4`). -/
def cA2 : ZMod 5 → Fin 7 := ![0, 5, 3, 6, 1]

/-- Base `Fin 6` rim corresponding to `cA2` under `(2 : Fin 7).succAbove`. -/
def cA2' : ZMod 5 → Fin 6 := ![0, 4, 2, 5, 1]

/-- Rim `cB2 = ![0, 5, 3, 4, 6, 1]` (`3.5.0.1.6.4` reversed, hiding `2`). -/
def cB2 : ZMod 6 → Fin 7 := ![0, 5, 3, 4, 6, 1]

/-- Base `Fin 6` rim corresponding to `cB2` under `(2 : Fin 7).succAbove`. -/
def cB2' : ZMod 6 → Fin 6 := ![0, 4, 2, 3, 5, 1]

theorem cA2_inj : Function.Injective cA2 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem cA2'_inj : Function.Injective cA2' := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem succAbove_cA2' : ∀ i : ZMod 5, (2 : Fin 7).succAbove (cA2' i) = cA2 i := by
  intro i; fin_cases i <;> rfl

theorem cB2_inj : Function.Injective cB2 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem cB2'_inj : Function.Injective cB2' := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem succAbove_cB2' : ∀ i : ZMod 6, (2 : Fin 7).succAbove (cB2' i) = cB2 i := by
  intro i; fin_cases i <;> rfl

/-- Up facets `{1, 3, 4, 8}` of `cA2`. -/
def U_A2 : Finset (Fin 9) := {1, 3, 4, 8}

/-- Down facets `{0, 2, 5, 6, 7}` (`T_2`) of `cA2`. -/
def D_A2 : Finset (Fin 9) := {0, 2, 5, 6, 7}

/-- Up facets `{1, 3, 4}` of `cB2`. -/
def U_B2 : Finset (Fin 9) := {1, 3, 4}

/-- Down facets `{0, 2, 5, 6, 7, 8}` of `cB2`. -/
def D_B2 : Finset (Fin 9) := {0, 2, 5, 6, 7, 8}

theorem cA2_cyc : S0xCycUD s0x_S24 cA2 U_A2 D_A2 := by
  decide

theorem cB2_cyc : S0xCycUD s0x_S24 cB2 U_B2 D_B2 := by
  decide

/-- View `u_{T_2}(x, β, γ) := capView x 1 (-β) γ`. -/
noncomputable def uT2 (x : Fin 7 → ℝ³) (beta gamma : ℝ) : ℝ³ :=
  capView x 1 (-beta) gamma

/-- On `uT2 x β γ` with `CbarIn x`, `β > 0`, `γ > 0`, four facets `{1, 4}` (`> 0`) and
`{0, 5}` (`< 0`) hold automatically. -/
theorem uT2_four_facets {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    0 < ⟪F.N 1, uT2 x beta gamma⟫ ∧ 0 < ⟪F.N 4, uT2 x beta gamma⟫ ∧
    ⟪F.N 0, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 5, uT2 x beta gamma⟫ < 0 := by
  have T := type24OfFac F
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [uT2, inner_cap, F.zero 1 1 (by decide), F.zero 1 0 (by decide), F.zero 1 6 (by decide)]
    have hf := F.neg 1 2 (by decide)
    nlinarith
  · rw [uT2, inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
    have e4 := fac_eval F 4 4
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e4
    have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
    have h4eq := eq4 F
    have hf21 : F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
      have hmul : oblX2 x 4 * (F.f 4 (x 2) - F.f 4 (x 1)) =
          oblX2 x 4 * (omega4 x * F.f 4 (x 1)) := by
        linear_combination -e4 + F.f 4 (x 1) * h4eq
      exact mul_left_cancel₀ hb4.ne' hmul
    have hf1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
    have hw4 : 0 < omega4 x := hC.2.1
    rw [hf21]
    have heval : 1 * (0 - F.f 4 (x 1)) + -beta * (omega4 x * F.f 4 (x 1)) +
        gamma * (0 - F.f 4 (x 1)) = -(1 + omega4 x * beta + gamma) * F.f 4 (x 1) := by ring
    rw [heval]
    have hpos : 0 < 1 + omega4 x * beta + gamma := by nlinarith
    exact mul_pos_of_neg_of_neg (by linarith) hf1
  · rw [uT2, inner_cap, F.zero 0 1 (by decide), F.zero 0 0 (by decide), F.zero 0 2 (by decide)]
    have hf := F.neg 0 6 (by decide)
    nlinarith
  · rw [uT2, inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    have hf := F.neg 5 0 (by decide)
    nlinarith

private theorem t2_core_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (c' : ZMod k → Fin 6) (hc' : Function.Injective c')
    (hcc' : ∀ i : ZMod k, (2 : Fin 7).succAbove (c' i) = c i)
    {U D : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U D) {w : ℝ³}
    (hcell : CellAt F U D w) (hT2 : ∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), ⟪F.N t, w⟫ < 0)
    (hhid : Split.HiddenInTriangles (x ∘ (2 : Fin 7).succAbove) w c')
    (a : ZMod k)
    (hD0 : ⟪x (c (a + 1)) - x (c a), w⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod k, i ≠ a →
      Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) w ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) w →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a i j, w⟫ /
          Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) w) -
        μ' * ⟪x (c j) - x (c a), w⟫ < α')
    (hOrange0 : ∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) w < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a p q, w⟫ /
          Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) w) -
        μ' * ⟪x (c q) - x (c a), w⟫) :
    Gen.EdgePlaneAny x := by
  let x' : Fin 6 → ℝ³ := x ∘ (2 : Fin 7).succAbove
  have hx'c : ∀ i : ZMod k, x' (c' i) = x (c i) := fun i => by dsimp [x']; rw [hcc' i]
  have hEP : EdgePlaneAt x' w := by
    rcases LexEP.strictRimN_of_openCell hk F hc hcyc hcell with hrim | hrim_rev
    · have hrim' : Split.StrictRimN x' w c' := fun m i hm0 hm1 => by
        have hm := hrim ((2 : Fin 7).succAbove m) i
          (fun h => hm0 (Fin.succAbove_right_injective (by rw [h, hcc'])))
          (fun h => hm1 (Fin.succAbove_right_injective (by rw [h, hcc'])))
        simpa [x', hcc'] using hm
      exact Split.Slope.edgePlaneAt_of_lineSep hk x' w c' hc' hrim' hhid a
        (by simpa [hx'c] using hD0)
        (fun i hi => by simpa [hx'c] using hc_ne0 i hi)
        sh hsh α' μ'
        (fun i j hi hj hpos => by
          simp only [hx'c] at hpos ⊢
          exact hBlue0 i j hi hj hpos)
        (fun p q hp hq hneg => by
          simp only [hx'c] at hneg ⊢
          exact hOrange0 p q hp hq hneg)
    · let c_rev : ZMod k → Fin 7 := fun i => c (-i)
      let c'_rev : ZMod k → Fin 6 := fun i => c' (-i)
      let a' : ZMod k := -a - 1
      have hc'_rev_inj : Function.Injective c'_rev := fun i j h => neg_inj.mp (hc' h)
      have hcc_rev : ∀ i : ZMod k, x' (c'_rev i) = x (c_rev i) := fun i => hx'c (-i)
      have hrim' : Split.StrictRimN x' w c'_rev := fun m i hm0 hm1 => by
        have hm := hrim_rev ((2 : Fin 7).succAbove m) i
          (fun h => hm0 (Fin.succAbove_right_injective (by rw [h, hcc'])))
          (fun h => hm1 (Fin.succAbove_right_injective (by rw [h, hcc'])))
        simpa [x', c'_rev, hcc'] using hm
      have hhid' : Split.HiddenInTriangles x' w c'_rev := fun m hm =>
        hhid m (fun i h => hm (-i) (by dsimp [c'_rev]; simpa using h))
      have ha1 : x' (c'_rev (a' + 1)) = x (c a) := by
        rw [hcc_rev]; dsimp only [c_rev, a']; congr 2; ring
      have ha0 : x' (c'_rev a') = x (c (a + 1)) := by
        rw [hcc_rev]; dsimp only [c_rev, a']; congr 2; ring
      have hD' : ⟪x' (c'_rev (a' + 1)) - x' (c'_rev a'), w⟫ ≠ 0 := by
        rw [ha1, ha0]
        intro h; apply hD0
        have hsub : x (c (a + 1)) - x (c a) = -(x (c a) - x (c (a + 1))) := by abel
        rw [hsub, inner_neg_left, h, neg_zero]
      have hc_eq : ∀ i : ZMod k,
          Split.det3 (x' (c'_rev (i + 1)) - x' (c'_rev i))
            (x' (c'_rev (a' + 1)) - x' (c'_rev a')) w =
          Split.det3 (x (c ((-i - 1) + 1)) - x (c (-i - 1))) (x (c (a + 1)) - x (c a)) w := by
        intro i
        have hc1 : x' (c'_rev (i + 1)) = x (c (-i - 1)) := by rw [hcc_rev]; dsimp [c_rev]; congr 2; ring
        have hc0 : x' (c'_rev i) = x (c (-i - 1 + 1)) := by rw [hcc_rev]; dsimp [c_rev]; congr 2; ring
        rw [hc1, hc0, ha1, ha0]
        simp only [Split.det3, PiLp.sub_apply]; ring
      have hv_eq : ∀ i j : ZMod k,
          ⟪Split.Slope.linSpinVec (fun t => x' (c'_rev t)) a' i j, w⟫ =
          ⟪Split.Slope.linSpinVec (fun t => x (c t)) a (-i - 1) (-j), w⟫ := by
        intro i j
        have hc1 : x' (c'_rev (i + 1)) = x (c (-i - 1)) := by rw [hcc_rev]; dsimp [c_rev]; congr 2; ring
        have hc0 : x' (c'_rev i) = x (c (-i - 1 + 1)) := by rw [hcc_rev]; dsimp [c_rev]; congr 2; ring
        dsimp only [Split.Slope.linSpinVec]
        rw [hc1, hc0, ha1, ha0, hcc_rev j]
        dsimp only [c_rev]
        have heq_v : (⟪x (c (-i - 1)) - x (c (-i - 1 + 1)), x (c (-j)) - x (c (a + 1))⟫ •
              (x (c a) - x (c (a + 1))) -
            ⟪x (c (-i - 1)) - x (c (-i - 1 + 1)), x (c a) - x (c (a + 1))⟫ •
              (x (c (-j)) - x (c (a + 1)))) =
          (⟪x (c (-i - 1 + 1)) - x (c (-i - 1)), x (c (-j)) - x (c a)⟫ • (x (c (a + 1)) - x (c a)) -
            ⟪x (c (-i - 1 + 1)) - x (c (-i - 1)), x (c (a + 1)) - x (c a)⟫ • (x (c (-j)) - x (c a))) := by
          have hsub : x (c (-j)) - x (c (a + 1)) = (x (c (-j)) - x (c a)) - (x (c (a + 1)) - x (c a)) := by abel
          have he1 : x (c (-i - 1)) - x (c (-i - 1 + 1)) = -(x (c (-i - 1 + 1)) - x (c (-i - 1))) := by abel
          have he2 : x (c a) - x (c (a + 1)) = -(x (c (a + 1)) - x (c a)) := by abel
          rw [hsub, he1, he2]
          simp only [inner_sub_right, inner_neg_left, inner_neg_right]
          module
        rw [heq_v]
      have hz_eq : ∀ j : ZMod k,
          ⟪x' (c'_rev j) - x' (c'_rev a'), w⟫ =
          ⟪x (c (-j)) - x (c a), w⟫ - ⟪x (c (a + 1)) - x (c a), w⟫ := by
        intro j
        have h4 : -a' = a + 1 := by dsimp [a']; ring
        rw [hcc_rev, hcc_rev]
        dsimp only [c_rev]
        rw [h4]
        have : x (c (-j)) - x (c (a + 1)) = (x (c (-j)) - x (c a)) - (x (c (a + 1)) - x (c a)) := by abel
        rw [this, inner_sub_left]
      have hi_iff : ∀ i : ZMod k, i ≠ a' → -i - 1 ≠ a := by
        intro i hi h; apply hi; linear_combination -h
      have hj_iff : ∀ i j : ZMod k, j = i ∨ j = i + 1 → -j = -i - 1 ∨ -j = -i - 1 + 1 := by
        intro i j hj
        rcases hj with rfl | rfl
        · right; ring
        · left; ring
      refine Split.Slope.edgePlaneAt_of_lineSep hk x' w c'_rev hc'_rev_inj hrim' hhid'
        a' hD' (fun i hi => by rw [hc_eq]; exact hc_ne0 (-i - 1) (hi_iff i hi))
        sh hsh (α' + μ' * ⟪x (c (a + 1)) - x (c a), w⟫) μ' ?_ ?_
      · intro i j hi hj hpos
        rw [hc_eq] at hpos
        rw [hc_eq, hv_eq, hz_eq]
        have h0 := hBlue0 (-i - 1) (-j) (hi_iff i hi) (hj_iff i j hj) hpos
        linarith
      · intro p q hp hq hneg
        rw [hc_eq] at hneg
        rw [hc_eq, hv_eq, hz_eq]
        have h0 := hOrange0 (-p - 1) (-q) (hi_iff p hp) (hj_iff p q hq) hneg
        linarith
  exact edgePlaneAny_of_T2 F (Or.inl hT2) hEP

/-- **FS2 (`cA2 = ![0, 5, 3, 6, 1]`):** interior `uT2 x β γ` leaf (`2, 4` hidden; `4` hidden
automatically from `{3, 4, 8} ⊆ U_A2`). -/
theorem cA2_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (h2 : ⟪F.N 2, uT2 x beta gamma⟫ < 0) (h3 : 0 < ⟪F.N 3, uT2 x beta gamma⟫)
    (h6 : ⟪F.N 6, uT2 x beta gamma⟫ < 0) (h7 : ⟪F.N 7, uT2 x beta gamma⟫ < 0)
    (h8 : 0 < ⟪F.N 8, uT2 x beta gamma⟫)
    (a : ZMod 5)
    (hD0 : ⟪x (cA2 (a + 1)) - x (cA2 a), uT2 x beta gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA2 t)) a i j, uT2 x beta gamma⟫ /
          Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma)) -
        μ' * ⟪x (cA2 j) - x (cA2 a), uT2 x beta gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (cA2 (p + 1)) - x (cA2 p)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA2 t)) a p q, uT2 x beta gamma⟫ /
          Split.det3 (x (cA2 (p + 1)) - x (cA2 p)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma)) -
        μ' * ⟪x (cA2 q) - x (cA2 a), uT2 x beta gamma⟫) :
    Gen.EdgePlaneAny x := by
  have ⟨h1, h4, h0, h5⟩ := uT2_four_facets F hC hbeta hgamma
  have hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma) := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · fin_cases t <;> simp [U_A2] at ht
      · exact h1
      · exact h3
      · exact h4
      · exact h8
    · fin_cases t <;> simp [D_A2] at ht
      · exact h0
      · exact h2
      · exact h5
      · exact h6
      · exact h7
  have hT2 : ∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), ⟪F.N t, uT2 x beta gamma⟫ < 0 :=
    fun t ht => hcell.2 t (by simpa [D_A2] using ht)
  have hhid : Split.HiddenInTriangles (x ∘ (2 : Fin 7).succAbove) (uT2 x beta gamma) cA2' := by
    intro m hm
    have hm3 : m = 3 := by
      fin_cases m
      · exact absurd rfl (hm 0)
      · exact absurd rfl (hm 4)
      · exact absurd rfl (hm 2)
      · rfl
      · exact absurd rfl (hm 1)
      · exact absurd rfl (hm 3)
    subst hm3
    have hw3 : ⟪F.N 3, -uT2 x beta gamma⟫ < 0 := by rw [inner_neg_right, neg_lt_zero]; exact h3
    have hw8 : ⟪F.N 8, -uT2 x beta gamma⟫ < 0 := by rw [inner_neg_right, neg_lt_zero]; exact h8
    have hw4 : ⟪F.N 4, -uT2 x beta gamma⟫ < 0 := by rw [inner_neg_right, neg_lt_zero]; exact h4
    obtain ⟨p, hp, q, hq, r, hr, d1, d2, d3, d4⟩ :=
      hidden_of_three_facets F 4 0 3 6 3 8 4
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hw3 hw8 hw4
    have hmem : ∀ v ∈ ({0, 3, 6} : Finset (Fin 7)),
        x v ∈ Finset.univ.image (x ∘ (2 : Fin 7).succAbove) := by
      intro v hv
      simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and]
      fin_cases v <;> simp at hv
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨5, rfl⟩
    have h036 : ∀ y ∈ ({x 0, x 3, x 6} : Finset ℝ³),
        y ∈ Finset.univ.image (x ∘ (2 : Fin 7).succAbove) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hmem 0 (by decide)
      · exact hmem 3 (by decide)
      · exact hmem 6 (by decide)
    have d1' : 0 < Split.det3 (r - p) (q - p) (uT2 x beta gamma) := by
      have : Split.det3 (r - p) (q - p) (uT2 x beta gamma) = Split.det3 (q - p) (r - p) (-uT2 x beta gamma) := by
        simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
      rw [this]; exact d1
    have d2' : 0 < Split.det3 (r - p) ((x ∘ (2 : Fin 7).succAbove) 3 - p) (uT2 x beta gamma) := by
      have : Split.det3 (r - p) (x 4 - p) (uT2 x beta gamma) = Split.det3 (p - r) (x 4 - r) (-uT2 x beta gamma) := by
        simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
      change 0 < Split.det3 (r - p) (x 4 - p) (uT2 x beta gamma)
      rw [this]; exact d4
    have d3' : 0 < Split.det3 (q - r) ((x ∘ (2 : Fin 7).succAbove) 3 - r) (uT2 x beta gamma) := by
      have : Split.det3 (q - r) (x 4 - r) (uT2 x beta gamma) = Split.det3 (r - q) (x 4 - q) (-uT2 x beta gamma) := by
        simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
      change 0 < Split.det3 (q - r) (x 4 - r) (uT2 x beta gamma)
      rw [this]; exact d3
    have d4' : 0 < Split.det3 (p - q) ((x ∘ (2 : Fin 7).succAbove) 3 - q) (uT2 x beta gamma) := by
      have : Split.det3 (p - q) (x 4 - q) (uT2 x beta gamma) = Split.det3 (q - p) (x 4 - p) (-uT2 x beta gamma) := by
        simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
      change 0 < Split.det3 (p - q) (x 4 - q) (uT2 x beta gamma)
      rw [this]; exact d2
    exact ⟨p, h036 p hp, r, h036 r hr, q, h036 q hq, d1', d2', d3', d4'⟩
  exact t2_core_edgePlaneAny F (by norm_num) cA2 cA2_inj cA2' cA2'_inj succAbove_cA2'
    cA2_cyc hcell hT2 hhid a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- **FS2 (`cB2 = ![0, 5, 3, 4, 6, 1]`):** interior `uT2 x β γ` leaf (only `2` hidden on `T_2`). -/
theorem cB2_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (h2 : ⟪F.N 2, uT2 x beta gamma⟫ < 0) (h3 : 0 < ⟪F.N 3, uT2 x beta gamma⟫)
    (h6 : ⟪F.N 6, uT2 x beta gamma⟫ < 0) (h7 : ⟪F.N 7, uT2 x beta gamma⟫ < 0)
    (h8 : ⟪F.N 8, uT2 x beta gamma⟫ < 0)
    (a : ZMod 6)
    (hD0 : ⟪x (cB2 (a + 1)) - x (cB2 a), uT2 x beta gamma⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB2 t)) a i j, uT2 x beta gamma⟫ /
          Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma)) -
        μ' * ⟪x (cB2 j) - x (cB2 a), uT2 x beta gamma⟫ < α')
    (hOrange0 : ∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (cB2 (p + 1)) - x (cB2 p)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB2 t)) a p q, uT2 x beta gamma⟫ /
          Split.det3 (x (cB2 (p + 1)) - x (cB2 p)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma)) -
        μ' * ⟪x (cB2 q) - x (cB2 a), uT2 x beta gamma⟫) :
    Gen.EdgePlaneAny x := by
  have ⟨h1, h4, h0, h5⟩ := uT2_four_facets F hC hbeta hgamma
  have hcell : CellAt F U_B2 D_B2 (uT2 x beta gamma) := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · fin_cases t <;> simp [U_B2] at ht
      · exact h1
      · exact h3
      · exact h4
    · fin_cases t <;> simp [D_B2] at ht
      · exact h0
      · exact h2
      · exact h5
      · exact h6
      · exact h7
      · exact h8
  have hT2 : ∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)), ⟪F.N t, uT2 x beta gamma⟫ < 0 :=
    fun t ht => hcell.2 t (by fin_cases t <;> simp [D_B2] at ht ⊢)
  have hhid : Split.HiddenInTriangles (x ∘ (2 : Fin 7).succAbove) (uT2 x beta gamma) cB2' := by
    intro m hm
    exfalso
    fin_cases m
    · exact hm 0 rfl
    · exact hm 5 rfl
    · exact hm 2 rfl
    · exact hm 3 rfl
    · exact hm 1 rfl
    · exact hm 4 rfl
  exact t2_core_edgePlaneAny F (by norm_num) cB2 cB2_inj cB2' cB2'_inj succAbove_cB2'
    cB2_cyc hcell hT2 hhid a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- `CA2CertAt x F β γ`: interior `(U_A2, D_A2)` cell conditions and strict line separation at
`uT2 x β γ` on some edge `a : ZMod 5` of `cA2 = ![0, 5, 3, 6, 1]`. -/
def CA2CertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  0 < ⟪F.N 8, uT2 x beta gamma⟫ ∧
  ∃ a : ZMod 5,
    ⟪x (cA2 (a + 1)) - x (cA2 a), uT2 x beta gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA2 t)) a i j, uT2 x beta gamma⟫ /
            Split.det3 (x (cA2 (i + 1)) - x (cA2 i)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cA2 j) - x (cA2 a), uT2 x beta gamma⟫ < α') ∧
      (∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cA2 (p + 1)) - x (cA2 p)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA2 t)) a p q, uT2 x beta gamma⟫ /
            Split.det3 (x (cA2 (p + 1)) - x (cA2 p)) (x (cA2 (a + 1)) - x (cA2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cA2 q) - x (cA2 a), uT2 x beta gamma⟫)

/-- `CB2CertAt x F β γ`: interior `(U_B2, D_B2)` cell conditions and strict line separation at
`uT2 x β γ` on some edge `a : ZMod 6` of `cB2 = ![0, 5, 3, 4, 6, 1]`. -/
def CB2CertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  ⟪F.N 8, uT2 x beta gamma⟫ < 0 ∧
  ∃ a : ZMod 6,
    ⟪x (cB2 (a + 1)) - x (cB2 a), uT2 x beta gamma⟫ ≠ 0 ∧
    (∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB2 t)) a i j, uT2 x beta gamma⟫ /
            Split.det3 (x (cB2 (i + 1)) - x (cB2 i)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cB2 j) - x (cB2 a), uT2 x beta gamma⟫ < α') ∧
      (∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cB2 (p + 1)) - x (cB2 p)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB2 t)) a p q, uT2 x beta gamma⟫ /
            Split.det3 (x (cB2 (p + 1)) - x (cB2 p)) (x (cB2 (a + 1)) - x (cB2 a)) (uT2 x beta gamma)) -
          μ' * ⟪x (cB2 q) - x (cB2 a), uT2 x beta gamma⟫)

theorem holeLeaf_not_cA2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : CA2CertAt x F beta gamma) : False := by
  rcases hc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (cA2_edgePlaneAny F hF.1 hb hg h2 h3 h6 h7 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_cA2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : CA2CertAt x F beta gamma) : False :=
  holeLeaf_not_cA2 hF.1 hc

/-- **FV2 (`CA2OCCertAt`):** `CA2` cell conditions plus `OrderCertAt` at `uT2 x β γ`. -/
def CA2OCCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  0 < ⟪F.N 8, uT2 x beta gamma⟫ ∧
  Split.Slope.OrderCertAt (fun t => x (cA2 t)) (uT2 x beta gamma)

/-- **FV2 (`CB2OCCertAt`):** `CB2` cell conditions plus `OrderCertAt` at `uT2 x β γ`. -/
def CB2OCCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (beta gamma : ℝ) : Prop :=
  0 < beta ∧ 0 < gamma ∧
  ⟪F.N 2, uT2 x beta gamma⟫ < 0 ∧ 0 < ⟪F.N 3, uT2 x beta gamma⟫ ∧
  ⟪F.N 6, uT2 x beta gamma⟫ < 0 ∧ ⟪F.N 7, uT2 x beta gamma⟫ < 0 ∧
  ⟪F.N 8, uT2 x beta gamma⟫ < 0 ∧
  Split.Slope.OrderCertAt (fun t => x (cB2 t)) (uT2 x beta gamma)

theorem cA2CertAt_of_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} {beta gamma : ℝ}
    (hoc : CA2OCCertAt x F beta gamma) : CA2CertAt x F beta gamma := by
  rcases hoc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, hsh, hOrd, hEq⟩
  obtain ⟨α', μ', hB, hO⟩ := Split.Slope.lineSep_of_depthOrder_ties
    (fun t => x (cA2 t)) (uT2 x beta gamma) a sh hOrd hEq
  exact ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩

theorem cB2CertAt_of_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} {beta gamma : ℝ}
    (hoc : CB2OCCertAt x F beta gamma) : CB2CertAt x F beta gamma := by
  rcases hoc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, hsh, hOrd, hEq⟩
  obtain ⟨α', μ', hB, hO⟩ := Split.Slope.lineSep_of_depthOrder_ties
    (fun t => x (cB2 t)) (uT2 x beta gamma) a sh hOrd hEq
  exact ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩

theorem holeLeaf_not_cA2_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : CA2OCCertAt x F beta gamma) : False :=
  holeLeaf_not_cA2 hF (cA2CertAt_of_oc hc)

theorem holeLeaf_not_cB2_oc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : CB2OCCertAt x F beta gamma) : False := by
  rcases cB2CertAt_of_oc hc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (cB2_edgePlaneAny F hF.1 hb hg h2 h3 h6 h7 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem holeLeaf_not_cB2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : CB2CertAt x F beta gamma) : False := by
  rcases hc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (cB2_edgePlaneAny F hF.1 hb hg h2 h3 h6 h7 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_cB2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : CB2CertAt x F beta gamma) : False :=
  holeLeaf_not_cB2 hF.1 hc

theorem cA2_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hc : CA2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) :
    Gen.EdgePlaneAny x := by
  rcases hc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact edgePlaneAny_of_comp_pi24 x
    (cA2_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hb hg h2 h3 h6 h7 h8
      a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem cB2_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {beta gamma : ℝ} (hc : CB2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) :
    Gen.EdgePlaneAny x := by
  rcases hc with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact edgePlaneAny_of_comp_pi24 x
    (cB2_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hb hg h2 h3 h6 h7 h8
      a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem holeLeaf_not_cA2_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : CA2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False :=
  Atlas.holeLeaf_not_edgePlaneAny hF (cA2_edgePlaneAny_twin F hF.1 hc)

theorem hole24_not_cA2_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : CA2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False :=
  holeLeaf_not_cA2_twin hF.1 hc

theorem holeLeaf_not_cB2_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {beta gamma : ℝ} (hc : CB2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False :=
  Atlas.holeLeaf_not_edgePlaneAny hF (cB2_edgePlaneAny_twin F hF.1 hc)

theorem hole24_not_cB2_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {beta gamma : ℝ} (hc : CB2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : False :=
  holeLeaf_not_cB2_twin hF.1 hc

/-- Extended two-cone residue adding `¬ CA2CertAt`, `¬ CB2CertAt`, and their `π_24` twins. -/
def TwoConeResidue_FS2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  TwoConeResidue_FS1 x F ∧
  (∀ beta gamma : ℝ, ¬ CA2CertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ CB2CertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ CA2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ CB2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma)

theorem hole24_twoConeResidue_FS2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    TwoConeResidue_FS2 x F :=
  ⟨hole24_twoConeResidue_FS1 hF,
    fun _ _ h => hole24_not_cA2 hF h,
    fun _ _ h => hole24_not_cB2 hF h,
    fun _ _ h => hole24_not_cA2_twin hF h,
    fun _ _ h => hole24_not_cB2_twin hF h⟩

end Minimality.T24.TwoCone
