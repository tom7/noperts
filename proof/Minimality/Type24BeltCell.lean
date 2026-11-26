module

public import Minimality.M4bType24
public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.RDispatch24

/-!
# Belt cells `A` and `A_i` at the hidden-cap corner (Carbon A76 Theorem 2.1)

At every `CbarIn` type-24 point the cell `A` (rim `0.1.2.3.4`) contains the view `capView x ε 1 (-1)` for small
`ε > 0` when `nB ≥ nC`, and the cell `A_i` (rim `0.1.6.3.5`) contains `capView x ε (-1) 1` when `nC ≥ nB`.
Facet signs of `⟪N t, w⟫` (outward normals `N`, `s0x_S24` indices): `A`: `+` on `{0,2,3,6}`, `-` on `{1,4,5,7,8}`;
`A_i`: `+` on `{1,3,4,8}`, `-` on `{0,2,5,6,7}`.  (Lean's `patA` of Type24EPHide is the negation of `A`, i.e. the
cell of the view `-w`.)
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology

namespace Minimality.T24.Belt

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.HC

variable {x : Fin 7 → ℝ³}

def A_up : Finset (Fin 9) := {0, 2, 3, 6}
def A_dn : Finset (Fin 9) := {1, 4, 5, 7, 8}
def Ai_up : Finset (Fin 9) := {1, 3, 4, 8}
def Ai_dn : Finset (Fin 9) := {0, 2, 5, 6, 7}

theorem inner_cap (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (a b c : ℝ) :
    ⟪F.N t, capView x a b c⟫ = a * (F.f t (x 0) - F.f t (x 1)) + b * (F.f t (x 2) - F.f t (x 1)) +
      c * (F.f t (x 6) - F.f t (x 1)) := by
  simp only [capView, inner_add_right, real_inner_smul_right]
  rw [← F.hN, ← F.hN, ← F.hN]

theorem ev_neg (A B : ℝ) (h : A < 0) : ∀ᶠ ε : ℝ in 𝓝[>] 0, A + B * ε < 0 := by
  have : Tendsto (fun ε : ℝ => A + B * ε) (𝓝 0) (𝓝 (A + B * 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
  rw [mul_zero, add_zero] at this
  exact (this.eventually (gt_mem_nhds h)).filter_mono nhdsWithin_le_nhds

theorem ev_pos (A B : ℝ) (h : 0 < A) : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < A + B * ε := by
  have : Tendsto (fun ε : ℝ => A + B * ε) (𝓝 0) (𝓝 (A + B * 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
  rw [mul_zero, add_zero] at this
  exact (this.eventually (lt_mem_nhds h)).filter_mono nhdsWithin_le_nhds

theorem ev_gt0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := eventually_mem_nhdsWithin

/-- `f7 x0 - f7 x1 = ω3 f7 x1` (facet `236` through `x3`). -/
theorem f7_rel (F : S0xFac 9 s0x_S24 x) :
    F.f 7 (x 0) - F.f 7 (x 1) = omega3 x * F.f 7 (x 1) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ev := fac_eval F 7 3
  rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev
  have hw : omega3 x * oblX0 x 3 = oblX2 x 3 + oblX6 x 3 - 1 := by
    unfold omega3; field_simp
  have : oblX0 x 3 * ((F.f 7 (x 0) - F.f 7 (x 1)) - omega3 x * F.f 7 (x 1)) = 0 := by
    linear_combination -ev - F.f 7 (x 1) * hw
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha3.ne')

theorem f7_neg (F : S0xFac 9 s0x_S24 x) (hw : 0 < omega3 x) :
    F.f 7 (x 0) - F.f 7 (x 1) < 0 := by
  rw [f7_rel F]; nlinarith [F.neg 7 1 (by decide)]

/-- Facet 3 value at `(ε, s, -s)`. -/
theorem f3_val (F : S0xFac 9 s0x_S24 x) (s ε : ℝ) :
    D45 x * ⟪F.N 3, capView x ε s (-s)⟫ =
      (-F.f 3 (x 1)) * (ε * D45 x + s * (nB x - nC x)) := by
  rw [inner_cap, F.zero 3 0 (by decide)]
  have h := fac3_lin F
  linear_combination (-s) * h.2 + s * h.1

theorem f3_pos (F : S0xFac 9 s0x_S24 x) (s ε : ℝ) (hε : 0 < ε) (h : 0 ≤ s * (nB x - nC x)) :
    0 < ⟪F.N 3, capView x ε s (-s)⟫ := by
  have hD := d45_pos F
  have f1 := F.neg 3 1 (by decide)
  have : 0 < D45 x * ⟪F.N 3, capView x ε s (-s)⟫ := by
    rw [f3_val]; exact mul_pos (by linarith) (by nlinarith)
  exact (mul_pos_iff_of_pos_left hD).mp this

theorem cellA_eventually (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h : nC x ≤ nB x) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, CellAt F A_up A_dn (capView x ε 1 (-1)) := by
  have e4 := ev_neg (F.f 4 (x 2)) (-F.f 4 (x 1)) (F.neg 4 2 (by decide))
  have e6 := ev_pos (-F.f 6 (x 6)) (F.f 6 (x 0) - F.f 6 (x 1)) (by linarith [F.neg 6 6 (by decide)])
  have e8 := ev_neg (F.f 8 (x 2)) (F.f 8 (x 0) - F.f 8 (x 1)) (F.neg 8 2 (by decide))
  filter_upwards [e4, e6, e8, ev_gt0] with ε h4 h6 h8 hε
  have n7 := f7_neg F hC.1
  refine ⟨?_, ?_⟩ <;> intro t ht <;>
    simp only [A_up, A_dn, Finset.mem_insert, Finset.mem_singleton] at ht <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [inner_cap, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    linarith [F.neg 0 6 (by decide)]
  · rw [inner_cap, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
    nlinarith [F.neg 2 1 (by decide), F.neg 2 6 (by decide)]
  · exact f3_pos F 1 ε hε (by linarith)
  · rw [inner_cap, F.zero 6 2 (by decide)]; linarith
  · rw [inner_cap, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
    linarith [F.neg 1 2 (by decide)]
  · rw [inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]; linarith
  · rw [inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    nlinarith [F.neg 5 0 (by decide)]
  · rw [inner_cap, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    nlinarith
  · rw [inner_cap, F.zero 8 6 (by decide)]; linarith

theorem cellAi_eventually (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h : nB x ≤ nC x) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, CellAt F Ai_up Ai_dn (capView x ε (-1) 1) := by
  have e2 := ev_neg (F.f 2 (x 6)) (-F.f 2 (x 1)) (F.neg 2 6 (by decide))
  have e6 := ev_neg (F.f 6 (x 6)) (F.f 6 (x 0) - F.f 6 (x 1)) (F.neg 6 6 (by decide))
  have e8 := ev_pos (-F.f 8 (x 2)) (F.f 8 (x 0) - F.f 8 (x 1)) (by linarith [F.neg 8 2 (by decide)])
  filter_upwards [e2, e6, e8, ev_gt0] with ε h2 h6 h8 hε
  have n7 := f7_neg F hC.1
  refine ⟨?_, ?_⟩ <;> intro t ht <;>
    simp only [Ai_up, Ai_dn, Finset.mem_insert, Finset.mem_singleton] at ht <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [inner_cap, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
    linarith [F.neg 1 2 (by decide)]
  · have := f3_pos F (-1) ε hε (by linarith)
    simpa using this
  · rw [inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
    nlinarith [F.neg 4 1 (by decide), F.neg 4 2 (by decide)]
  · rw [inner_cap, F.zero 8 6 (by decide)]; linarith
  · rw [inner_cap, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    linarith [F.neg 0 6 (by decide)]
  · rw [inner_cap, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]; nlinarith [F.neg 2 6 (by decide)]
  · rw [inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    nlinarith [F.neg 5 0 (by decide)]
  · rw [inner_cap, F.zero 6 2 (by decide)]; linarith
  · rw [inner_cap, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
    nlinarith

/-- **A76 Theorem 2.1 (belt existence).** -/
theorem cellA_or_cellAi (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo 0 ε₀,
      (nC x ≤ nB x → CellAt F A_up A_dn (capView x ε 1 (-1))) ∧
      (nB x ≤ nC x → CellAt F Ai_up Ai_dn (capView x ε (-1) 1)) := by
  have hA : ∀ᶠ ε : ℝ in 𝓝[>] 0, nC x ≤ nB x → CellAt F A_up A_dn (capView x ε 1 (-1)) := by
    by_cases h : nC x ≤ nB x
    · exact (cellA_eventually F hC h).mono fun _ h' _ => h'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  have hB : ∀ᶠ ε : ℝ in 𝓝[>] 0, nB x ≤ nC x → CellAt F Ai_up Ai_dn (capView x ε (-1) 1) := by
    by_cases h : nB x ≤ nC x
    · exact (cellAi_eventually F hC h).mono fun _ h' _ => h'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (hA.and hB)
  exact ⟨u, hu.out, fun ε hε => hsub hε⟩

end Minimality.T24.Belt
