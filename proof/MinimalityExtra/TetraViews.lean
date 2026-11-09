module

public import MinimalityExtra

/-!
# Three views of one tetrahedron: rim shape and first-order freedom are independent

Proof of `MinimalityExtra.ExistsTetrahedronViewsIndependent` (see `MinimalityExtra.lean`).
Tetrahedron `TX` with vertices `(0,0,0), (1,0,3), (1,1,2), (0,1,1)`; views
`WA = (0,0,1)` (unimodal rim, horizontal double normal, rigid), `WB = (-7,4,6)` (two-peaked, free),
`WC = (-1,0,-2)` (two-peaked, rigid).  The views were found by a small search over integer vectors.

Rigidity is proved by: a certificate at a vertex gives the two inequalities of the true rim
(`cert*`, by finite case analysis on the choices `y₀, y₁` or the triangle), then a Farkas
combination of four of them (weights found by an LP, closed by `linarith`).
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra
open scoped RealInnerProductSpace
open Finset

/-- The tetrahedron. -/
noncomputable def TX : Fin 4 → ℝ³ := ![!₂[0, 0, 0], !₂[1, 0, 3], !₂[1, 1, 2], !₂[0, 1, 1]]
noncomputable def WA : ℝ³ := !₂[0, 0, 1]
noncomputable def WB : ℝ³ := !₂[-7, 4, 6]
noncomputable def WC : ℝ³ := !₂[-1, 0, -2]

theorem all4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
theorem all4z (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

theorem tx_noncoplanar : det3 (TX 1 - TX 0) (TX 2 - TX 0) (TX 3 - TX 0) ≠ 0 := by
  norm_num [det3, TX]

set_option maxHeartbeats 1600000 in
/-- At view `WA`, a certificate at vertex `i` gives the two inequalities of the true rim
(cyclic order given by `![1, 2, 3, 0]`, `![3, 0, 1, 2]`). -/
theorem certA (ω τ : ℝ³) (i : Fin 4) (h : TiltCert (univ.image TX) WA ω τ (TX i)) :
    0 < det3 (TX (![1, 2, 3, 0] i) - TX i) (cross ω (TX i) + τ) WA ∧
    0 < det3 (TX i - TX (![3, 0, 1, 2] i)) (cross ω (TX i) + τ) WA := by
  rcases h with ⟨y0, hy0, y1, hy1, h1, h2, h3⟩ | ⟨a, ha, b, hb, c, hc, h1, h2, h3, h4⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy0 hy1
    obtain ⟨j0, rfl⟩ := hy0
    obtain ⟨j1, rfl⟩ := hy1
    rcases all4 i with rfl | rfl | rfl | rfl <;> rcases all4 j0 with rfl | rfl | rfl | rfl <;>
      rcases all4 j1 with rfl | rfl | rfl | rfl <;>
      norm_num [det3, cross, TX, WA] at h1 <;> norm_num [det3, cross, TX, WA] at h2 <;>
      norm_num [det3, cross, TX, WA] at h3 <;> refine ⟨?_, ?_⟩ <;>
      norm_num [det3, cross, TX, WA] <;> linarith
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb hc
    obtain ⟨j0, rfl⟩ := ha
    obtain ⟨j1, rfl⟩ := hb
    obtain ⟨j2, rfl⟩ := hc
    rcases all4 i with rfl | rfl | rfl | rfl <;> rcases all4 j0 with rfl | rfl | rfl | rfl <;>
      rcases all4 j1 with rfl | rfl | rfl | rfl <;> rcases all4 j2 with rfl | rfl | rfl | rfl <;>
      norm_num [det3, TX, WA] at h1 <;> norm_num [det3, TX, WA] at h2 <;>
      norm_num [det3, TX, WA] at h3 <;> norm_num [det3, TX, WA] at h4

set_option maxHeartbeats 1600000 in
/-- At view `WC`, a certificate at vertex `i` gives the two inequalities of the true rim
(cyclic order given by `![1, 3, 0, 2]`, `![2, 0, 3, 1]`). -/
theorem certC (ω τ : ℝ³) (i : Fin 4) (h : TiltCert (univ.image TX) WC ω τ (TX i)) :
    0 < det3 (TX (![1, 3, 0, 2] i) - TX i) (cross ω (TX i) + τ) WC ∧
    0 < det3 (TX i - TX (![2, 0, 3, 1] i)) (cross ω (TX i) + τ) WC := by
  rcases h with ⟨y0, hy0, y1, hy1, h1, h2, h3⟩ | ⟨a, ha, b, hb, c, hc, h1, h2, h3, h4⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy0 hy1
    obtain ⟨j0, rfl⟩ := hy0
    obtain ⟨j1, rfl⟩ := hy1
    rcases all4 i with rfl | rfl | rfl | rfl <;> rcases all4 j0 with rfl | rfl | rfl | rfl <;>
      rcases all4 j1 with rfl | rfl | rfl | rfl <;>
      norm_num [det3, cross, TX, WC] at h1 <;> norm_num [det3, cross, TX, WC] at h2 <;>
      norm_num [det3, cross, TX, WC] at h3 <;> refine ⟨?_, ?_⟩ <;>
      norm_num [det3, cross, TX, WC] <;> linarith
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb hc
    obtain ⟨j0, rfl⟩ := ha
    obtain ⟨j1, rfl⟩ := hb
    obtain ⟨j2, rfl⟩ := hc
    rcases all4 i with rfl | rfl | rfl | rfl <;> rcases all4 j0 with rfl | rfl | rfl | rfl <;>
      rcases all4 j1 with rfl | rfl | rfl | rfl <;> rcases all4 j2 with rfl | rfl | rfl | rfl <;>
      norm_num [det3, TX, WC] at h1 <;> norm_num [det3, TX, WC] at h2 <;>
      norm_num [det3, TX, WC] at h3 <;> norm_num [det3, TX, WC] at h4

/-- Rigid at `WA`: the Farkas weights are `1` on the next-side inequality at vertices 0, 2 and
the previous-side inequality at vertices 1, 3 (a horizontal double normal). -/
theorem rigidA : ¬ FreeAt (univ.image TX) WA := by
  rintro ⟨ω, τ, h⟩
  have m : ∀ i, TX i ∈ univ.image TX := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have c0 := (certA ω τ 0 (h _ (m 0))).1
  have c1 := (certA ω τ 1 (h _ (m 1))).2
  have c2 := (certA ω τ 2 (h _ (m 2))).1
  have c3 := (certA ω τ 3 (h _ (m 3))).2
  norm_num [det3, cross, TX, WA] at c0 c1 c2 c3
  linarith

/-- Rigid at `WC`: Farkas weights `1` on next-side at vertices 0, 3 (indices in the rim order
`0,1,3,2`: positions 0 and 2) and previous-side at the other two, found by an LP. -/
theorem rigidC : ¬ FreeAt (univ.image TX) WC := by
  rintro ⟨ω, τ, h⟩
  have m : ∀ i, TX i ∈ univ.image TX := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have c0 := (certC ω τ 0 (h _ (m 0))).1
  have c1 := (certC ω τ 1 (h _ (m 1))).2
  have c3 := (certC ω τ 3 (h _ (m 3))).1
  have c2 := (certC ω τ 2 (h _ (m 2))).2
  norm_num [det3, cross, TX, WC] at c0 c1 c2 c3
  linarith

/-- Free at `WB`: the motion `ω = (0,-4,5)`, `τ = (0,2,6)` moves every vertex strictly into
the angle between its two rim neighbours (cyclic order `0,1,2,3`). -/
theorem freeB : FreeAt (univ.image TX) WB := by
  refine ⟨!₂[0, -4, 5], !₂[0, 2, 6], ?_⟩
  intro y hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  have m : ∀ i, TX i ∈ univ.image TX := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  left
  rcases all4 i with rfl | rfl | rfl | rfl
  · exact ⟨TX 3, m _, TX 1, m _, by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB]⟩
  · exact ⟨TX 0, m _, TX 2, m _, by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB]⟩
  · exact ⟨TX 1, m _, TX 3, m _, by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB]⟩
  · exact ⟨TX 2, m _, TX 0, m _, by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB], by norm_num [det3, cross, TX, WB]⟩

theorem peaks_A (z : ZMod 4 → ℝ) (h0 : z 0 = 0) (h1 : z 1 = 3) (h2 : z 2 = 2) (h3 : z 3 = 1) :
    IsCyclicUnimodal z := by
  have e0 : ((0 : ZMod 4) - 1) = 3 := by decide
  have e1 : ((1 : ZMod 4) - 1) = 0 := by decide
  have e2 : ((2 : ZMod 4) - 1) = 1 := by decide
  have e3 : ((3 : ZMod 4) - 1) = 2 := by decide
  have f0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have f1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have f2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have f3 : ((3 : ZMod 4) + 1) = 0 := by decide
  refine ⟨?_, Finset.card_eq_one.2 ⟨1, ?_⟩⟩
  · intro a b hab
    rcases all4z a with rfl | rfl | rfl | rfl <;> rcases all4z b with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [h0, h1, h2, h3] at hab; norm_num at hab)
  · ext i
    rcases all4z i with rfl | rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, e0, e1, e2, e3,
        f0, f1, f2, f3, h0, h1, h2, h3] <;> norm_num <;> decide

theorem peaks_B (z : ZMod 4 → ℝ) (h0 : z 0 = 0) (h1 : z 1 = 11) (h2 : z 2 = 9) (h3 : z 3 = 10) :
    IsCyclicTwoPeaked z := by
  have e0 : ((0 : ZMod 4) - 1) = 3 := by decide
  have e1 : ((1 : ZMod 4) - 1) = 0 := by decide
  have e2 : ((2 : ZMod 4) - 1) = 1 := by decide
  have e3 : ((3 : ZMod 4) - 1) = 2 := by decide
  have f0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have f1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have f2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have f3 : ((3 : ZMod 4) + 1) = 0 := by decide
  refine ⟨?_, Finset.card_eq_two.2 ⟨1, 3, by decide, ?_⟩⟩
  · intro a b hab
    rcases all4z a with rfl | rfl | rfl | rfl <;> rcases all4z b with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [h0, h1, h2, h3] at hab; norm_num at hab)
  · ext i
    rcases all4z i with rfl | rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, e0, e1, e2, e3,
        f0, f1, f2, f3, h0, h1, h2, h3] <;> norm_num <;> decide

theorem peaks_C (z : ZMod 4 → ℝ) (h0 : z 0 = 0) (h1 : z 1 = -7) (h2 : z 2 = -2) (h3 : z 3 = -5) :
    IsCyclicTwoPeaked z := by
  have e0 : ((0 : ZMod 4) - 1) = 3 := by decide
  have e1 : ((1 : ZMod 4) - 1) = 0 := by decide
  have e2 : ((2 : ZMod 4) - 1) = 1 := by decide
  have e3 : ((3 : ZMod 4) - 1) = 2 := by decide
  have f0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have f1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have f2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have f3 : ((3 : ZMod 4) + 1) = 0 := by decide
  refine ⟨?_, Finset.card_eq_two.2 ⟨0, 2, by decide, ?_⟩⟩
  · intro a b hab
    rcases all4z a with rfl | rfl | rfl | rfl <;> rcases all4z b with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [h0, h1, h2, h3] at hab; norm_num at hab)
  · ext i
    rcases all4z i with rfl | rfl | rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, e0, e1, e2, e3,
        f0, f1, f2, f3, h0, h1, h2, h3] <;> norm_num <;> decide


theorem inj4 (lab : ZMod 4 → Fin 4) (h : lab 0 ≠ lab 1 ∧ lab 0 ≠ lab 2 ∧ lab 0 ≠ lab 3 ∧
    lab 1 ≠ lab 2 ∧ lab 1 ≠ lab 3 ∧ lab 2 ≠ lab 3) : Function.Injective lab := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := h
  intro a b hab
  rcases all4z a with rfl | rfl | rfl | rfl <;> rcases all4z b with rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd hab ‹_› | exact absurd hab.symm ‹_›

theorem rimA : ∃ lab : ZMod 4 → Fin 4, Function.Injective lab ∧ StrictRimN TX WA lab ∧
    IsCyclicUnimodal (fun i => ⟪TX (lab i), WA⟫) := by
  refine ⟨![0, 1, 2, 3], inj4 _ (by decide), ?_, peaks_A _ ?_ ?_ ?_ ?_⟩
  · intro m i h1 h2
    rcases all4z i with rfl | rfl | rfl | rfl <;> fin_cases m <;>
      first | exact absurd rfl h1 | exact absurd rfl h2 | skip
    all_goals norm_num [det3, TX, WA]
  all_goals (simp [TX, WA, PiLp.inner_apply, Fin.sum_univ_three] )

theorem rimB : ∃ lab : ZMod 4 → Fin 4, Function.Injective lab ∧ StrictRimN TX WB lab ∧
    IsCyclicTwoPeaked (fun i => ⟪TX (lab i), WB⟫) := by
  refine ⟨![0, 1, 2, 3], inj4 _ (by decide), ?_, peaks_B _ ?_ ?_ ?_ ?_⟩
  · intro m i h1 h2
    rcases all4z i with rfl | rfl | rfl | rfl <;> fin_cases m <;>
      first | exact absurd rfl h1 | exact absurd rfl h2 | skip
    all_goals norm_num [det3, TX, WB]
  all_goals (simp [TX, WB, PiLp.inner_apply, Fin.sum_univ_three] <;> norm_num)

theorem rimC : ∃ lab : ZMod 4 → Fin 4, Function.Injective lab ∧ StrictRimN TX WC lab ∧
    IsCyclicTwoPeaked (fun i => ⟪TX (lab i), WC⟫) := by
  refine ⟨![0, 1, 3, 2], inj4 _ (by decide), ?_, peaks_C _ ?_ ?_ ?_ ?_⟩
  · intro m i h1 h2
    rcases all4z i with rfl | rfl | rfl | rfl <;> fin_cases m <;>
      first | exact absurd rfl h1 | exact absurd rfl h2 | skip
    all_goals norm_num [det3, TX, WC]
  all_goals (simp [TX, WC, PiLp.inner_apply, Fin.sum_univ_three] <;> norm_num)

/-- **Rim shape and first-order freedom are independent at a single view.** -/
theorem existsTetrahedronViewsIndependent : ExistsTetrahedronViewsIndependent :=
  ⟨TX, tx_noncoplanar, WA, WB, WC, rimA, rigidA, rimB, freeB, rimC, rigidC⟩

end MinimalityExtra

#print axioms MinimalityExtra.existsTetrahedronViewsIndependent
