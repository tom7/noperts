module

public import Minimality.Type24RayQuad
public import Minimality.SplitApex
public import Minimality.Type24Corner
public import Minimality.EdgeViewLink
public import Minimality.M4Sym24
public import Minimality.Type24HoleAtlas

@[expose] public section

/-!
# Type 24: the one-parameter Split family in the sector next to the wall `c_a = 0` (Carbon A70, Theorem 1.1)

Merge of Carbon A70 Theorem 1.1 (referee A70 REFEREE 2).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.Split

namespace Minimality.T24.SF

variable {x : Fin 7 → ℝ³}

/-- Heights above the base edge `[1,2]` at the view `capView x (-x0) 1 γ`. -/
noncomputable def Hh (x : Fin 7 → ℝ³) (x0 γ : ℝ) (v : Fin 7) : ℝ :=
  oblX0 x v * γ + oblX6 x v * x0

theorem det3_height (F : S0xFac 9 s0x_S24 x) (x0 γ : ℝ) (v : Fin 7) :
    det3 (x v - x 1) (x 2 - x 1) (capView x (-x0) 1 γ) = det24 x * Hh x x0 γ v := by
  have T := Minimality.T24.M4.type24OfFac F
  have h1 : x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
    rw [T.rep v]; abel
  have h2 : x 2 - x 1 = (0:ℝ) • (x 0 - x 1) + (1:ℝ) • (x 2 - x 1) + (0:ℝ) • (x 6 - x 1) := by
    simp
  have e := Minimality.T24.M4.det3_frame x (oblX0 x v) (oblX2 x v) (oblX6 x v) 0 1 0 (-x0) 1 γ
  rw [← h1, ← h2] at e
  unfold capView
  rw [e]; simp only [Hh]; ring

theorem det3_height6 (x0 γ : ℝ) :
    det3 (x 2 - x 1) (x 6 - x 1) (capView x (-x0) 1 γ) = - x0 * det24 x := by
  have h2 : x 2 - x 1 = (0:ℝ) • (x 0 - x 1) + (1:ℝ) • (x 2 - x 1) + (0:ℝ) • (x 6 - x 1) := by
    simp
  have h6 : x 6 - x 1 = (0:ℝ) • (x 0 - x 1) + (0:ℝ) • (x 2 - x 1) + (1:ℝ) • (x 6 - x 1) := by
    simp
  have e := Minimality.T24.M4.det3_frame x 0 1 0 0 0 1 (-x0) 1 γ
  rw [← h2, ← h6] at e
  unfold capView
  rw [e]; ring

/-- Rim determinants of a strict rim have one global sign. -/
theorem rim_det_sign (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c) (pat : Fin 9 → Bool)
    (hcyc : S0xCycOK s0x_S24 c pat) (u : ℝ³)
    (hfac : ∀ t, (pat t = true → 0 < ⟪F.N t, u⟫) ∧ (pat t = false → ⟪F.N t, u⟫ < 0)) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) u := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have hS0 : S0xFacOK F pat u 0 := fun t =>
    ⟨fun h => Or.inl ((hfac t).1 h), fun h => Or.inl (by simpa using (hfac t).2 h)⟩
  obtain ⟨D⟩ := s0x_silL F hcyc hS0
  choose μ hμ0 hμ using fun i => h21b_exists_mu hk hx hc D i
  have hsign := h21b_sign_agree hk hx hc D μ hμ0 hμ
  have Q : ∀ i m, m ≠ c i → m ≠ c (i + 1) →
      0 < D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫ := by
    intro i m h0 h1
    have := h21b_Q_pos D i m h0 h1
    simp only [inner_zero_right, mul_zero, sub_zero, h21b_LP] at this
    rcases this with h | ⟨_, h⟩
    · exact h
    · exact absurd h (lt_irrefl _)
  have key : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      det3 (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) u =
        μ i * (D.fA i (x (c j)) * ⟪D.B i, u⟫ - D.fB i (x (c j)) * ⟪D.A i, u⟫) := by
    intro i j _ _
    exact h21b_det_eq D i (μ i) (hμ i) (c j) u
  rcases hsign with h | h
  · refine ⟨1, Or.inl rfl, fun i j hji hj1 => ?_⟩
    rw [key i j hji hj1, one_mul]
    exact mul_pos (h i) (Q i _ (fun e => hji (hc e)) (fun e => hj1 (hc e)))
  · refine ⟨-1, Or.inr rfl, fun i j hji hj1 => ?_⟩
    rw [key i j hji hj1]
    have := Q i _ (fun e => hji (hc e)) (fun e => hj1 (hc e))
    nlinarith [h i]


/-- Depth `⟪x v - x 1, u⟫`. -/
noncomputable def zz (x : Fin 7 → ℝ³) (u : ℝ³) (v : Fin 7) : ℝ := ⟪x v - x 1, u⟫

/-- **Generic Split leaf on a rim with base edge `[1,2]`**: strict facings at `u = capView x (-x0) 1 γ`,
the heights over `[1,2]` are maximal at the apex `cc`, and the depths separate the two chains. -/
theorem splitAny_of_rim (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c) (pat : Fin 9 → Bool)
    (hcyc : S0xCycOK s0x_S24 c pat) (hc0 : c 0 = 1) (hc1 : c 1 = 2)
    (j6 : ZMod k) (hj6 : c j6 = 6) (hj60 : j6 ≠ 0) (hj61 : j6 ≠ 1)
    (cc : ZMod k) (hcc0 : cc ≠ 0) (hcc1 : cc ≠ 1) (x0 γ : ℝ) (hx0 : 0 < x0)
    (hfac : ∀ t, (pat t = true → 0 < ⟪F.N t, capView x (-x0) 1 γ⟫) ∧
      (pat t = false → ⟪F.N t, capView x (-x0) 1 γ⟫ < 0))
    (hext : ∀ j : ZMod k, j ≠ 0 → j ≠ 1 → j ≠ cc → Hh x x0 γ (c j) < Hh x x0 γ (c cc))
    (hfirst : ∀ j : ZMod k, (j - 0 - 1).val < (cc - 0 - 1).val →
      0 < zz x (capView x (-x0) 1 γ) (c j) - zz x (capView x (-x0) 1 γ) (c cc))
    (hsecond : ∀ j : ZMod k, (cc - 0 - 1).val < (j - 0 - 1).val →
      zz x (capView x (-x0) 1 γ) (c j) - zz x (capView x (-x0) 1 γ) (c cc) < 0) :
    Gen.SplitAny F := by
  set w := capView x (-x0) 1 γ with hw
  obtain ⟨ρ, hρ, hrim⟩ := rim_det_sign F hk c hc pat hcyc w hfac
  have hdet : det24 x ≠ 0 := (Minimality.T24.M4.type24OfFac F).det_ne
  -- sign of `ρ * det24`
  have hκ : ρ * det24 x < 0 := by
    have h := hrim 0 j6 (fun e => hj60 e) (fun e => hj61 (by simpa using e))
    rw [zero_add, hc0, hc1, hj6, hw, det3_height6] at h
    nlinarith
  have hcc1' : cc ≠ 0 + 1 := by simpa using hcc1
  have hρ2 : ρ * ρ = 1 := by rcases hρ with rfl | rfl <;> norm_num
  have hrows : SplitRows (fun i => x (c i)) w 0 cc (-ρ) := by
    refine splitRows_of_unimodal_separated (ρ := ρ) (σ := -ρ) hk (a := 0) (c := cc)
      (fun i j h1 h2 => by rw [Split.det3_eq_minimality]; exact hrim i j h1 h2)
      hcc0 hcc1' ?_ ?_ ?_
    · intro j hj0 hj1 hjc
      have hj1' : j ≠ 1 := by simpa using hj1
      simp only [zero_add, hc0, hc1, Split.det3_eq_minimality]
      rw [hw, det3_height F, det3_height F]
      have := hext j hj0 hj1' hjc
      nlinarith
    · intro j hj
      have := hfirst j hj
      simp only [zz, inner_sub_left] at this
      have e : ⟪x (c j), w⟫ - ⟪x (c cc), w⟫ = ⟪x (c j) - x 1, w⟫ - ⟪x (c cc) - x 1, w⟫ := by
        simp only [inner_sub_left]; ring
      rw [e]; nlinarith
    · intro j hj
      have := hsecond j hj
      simp only [zz, inner_sub_left] at this
      have e : ⟪x (c j), w⟫ - ⟪x (c cc), w⟫ = ⟪x (c j) - x 1, w⟫ - ⟪x (c cc) - x 1, w⟫ := by
        simp only [inner_sub_left]; ring
      rw [e]; nlinarith
  exact ⟨k, inferInstance, c, pat, w, 0, 0, cc, -ρ, hk, hc, hcyc,
    fun t => ⟨fun h => Or.inl ((hfac t).1 h), fun h => Or.inl (by simpa using (hfac t).2 h)⟩,
    hcc0, hcc1', hrows⟩

/-- **FW1 (`oc_splitAny_of_cell`, Carbon A87 §0/1):** at any open cell `CellAt F U Dn w`
(`U ∪ Dn = univ`) with rim `c : ZMod k → Fin 7` (`k ≥ 3`), a strict height apex `cc ∉ {a, a+1}`
over base edge `c a → c (a+1)` with one open arc strictly above `z(c cc)` and the other
strictly below (either orientation) yields `Gen.SplitAny F` directly via
`Split.splitRows_of_unimodal_separated` and `rim_det_sign`, with **no** `hD` (`⟪d, w⟫ ≠ 0`)
and **no** `HiddenInTriangles` hypothesis. -/
theorem oc_splitAny_of_cell (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcov : ∀ t : Fin 9, t ∈ U ∨ t ∈ Dn)
    (hcyc : S0xCycUD s0x_S24 c U Dn) {w : ℝ³} (hcell : CellAt F U Dn w)
    {a cc : ZMod k} (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hext : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 → j ≠ cc →
      |Split.det3 (x (c j) - x (c a)) (x (c (a + 1)) - x (c a)) w| <
        |Split.det3 (x (c cc) - x (c a)) (x (c (a + 1)) - x (c a)) w|)
    (hsep : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ j : ZMod k, (j - a - 1).val < (cc - a - 1).val → σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) < 0) ∧
      (∀ j : ZMod k, (cc - a - 1).val < (j - a - 1).val → 0 < σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫))) :
    Gen.SplitAny F := by
  let pat : Fin 9 → Bool := fun t => decide (t ∈ U)
  have hfac : ∀ t, (pat t = true → 0 < ⟪F.N t, w⟫) ∧ (pat t = false → ⟪F.N t, w⟫ < 0) := by
    intro t
    refine ⟨fun ht => hcell.1 t (by simpa [pat] using ht), fun ht => ?_⟩
    have hnot : t ∉ U := by simpa [pat] using ht
    rcases hcov t with hU | hD
    · exact absurd hU hnot
    · exact hcell.2 t hD
  have hcycOK : S0xCycOK s0x_S24 c pat := by
    intro i
    obtain ⟨ea, hea, eb, heb, h1, h2, h3, h4, hs⟩ := hcyc i
    have hpa : pat ea = true := by simpa [pat] using hea
    have hpb : pat eb = false := by
      by_contra h
      have hU : eb ∈ U := by simpa [pat] using h
      exact absurd (hcell.1 eb hU) (not_lt.mpr (hcell.2 eb heb).le)
    exact ⟨ea, eb, hpa, hpb, h1, h2, h3, h4, hs⟩
  obtain ⟨ρ, hρ, hrim⟩ := rim_det_sign F hk c hc pat hcycOK w hfac
  have hρ2 : ρ * ρ = 1 := by rcases hρ with rfl | rfl <;> norm_num
  have hneg : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 →
      ρ * Split.det3 (x (c j) - x (c a)) (x (c (a + 1)) - x (c a)) w < 0 := by
    intro j hja hja1
    have hpos := hrim a j hja hja1
    rw [← Split.det3_eq_minimality] at hpos
    have hswap : Split.det3 (x (c (a + 1)) - x (c a)) (x (c j) - x (c a)) w =
        -Split.det3 (x (c j) - x (c a)) (x (c (a + 1)) - x (c a)) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [hswap] at hpos
    linarith
  have hext' : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 → j ≠ cc →
      ρ * Split.det3 (x (c cc) - x (c a)) (x (c (a + 1)) - x (c a)) w <
        ρ * Split.det3 (x (c j) - x (c a)) (x (c (a + 1)) - x (c a)) w := by
    intro j hja hja1 hjc
    have hj_neg := hneg j hja hja1
    have hcc_neg := hneg cc hca hca1
    have habs := hext j hja hja1 hjc
    have h1 : |Split.det3 (x (c j) - x (c a)) (x (c (a + 1)) - x (c a)) w| =
        -(ρ * Split.det3 (x (c j) - x (c a)) (x (c (a + 1)) - x (c a)) w) := by
      rcases hρ with rfl | rfl
      · simp only [one_mul] at hj_neg ⊢; exact abs_of_neg hj_neg
      · simp only [neg_mul, one_mul, neg_neg] at hj_neg ⊢
        rw [abs_of_pos (by linarith)]
    have h2 : |Split.det3 (x (c cc) - x (c a)) (x (c (a + 1)) - x (c a)) w| =
        -(ρ * Split.det3 (x (c cc) - x (c a)) (x (c (a + 1)) - x (c a)) w) := by
      rcases hρ with rfl | rfl
      · simp only [one_mul] at hcc_neg ⊢; exact abs_of_neg hcc_neg
      · simp only [neg_mul, one_mul, neg_neg] at hcc_neg ⊢
        rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨σ, hσ, hfirst, hsecond⟩ := hsep
  have hrows : SplitRows (fun i => x (c i)) w a cc (σ * ρ) := by
    refine splitRows_of_unimodal_separated (ρ := ρ) (σ := σ * ρ) hk
      (fun i j hji hj1 => by rw [Split.det3_eq_minimality]; exact hrim i j hji hj1)
      hca hca1 hext' ?_ ?_
    · intro j hj
      have : σ * ρ * ρ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) =
          σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) := by
        calc σ * ρ * ρ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫)
            = σ * (ρ * ρ) * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) := by ring
          _ = σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) := by rw [hρ2, mul_one]
      rw [this]; exact hfirst j hj
    · intro j hj
      have : σ * ρ * ρ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) =
          σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) := by
        calc σ * ρ * ρ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫)
            = σ * (ρ * ρ) * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) := by ring
          _ = σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) := by rw [hρ2, mul_one]
      rw [this]; exact hsecond j hj
  exact ⟨k, inferInstance, c, pat, w, w, a, cc, σ * ρ, hk, hc, hcycOK,
    fun t => ⟨fun h => Or.inl ((hfac t).1 h), fun h => Or.inl (by simpa using (hfac t).2 h)⟩,
    hca, hca1, hrows⟩

/-- **FW1 (`holeLeaf_not_oc_cell`):** at a hole point `HoleLeaf x F`, no open-cell view of any
rim `c` (`k ≥ 3`) has a strict height apex with depth-separated open arcs. -/
theorem holeLeaf_not_oc_cell (F : S0xFac 9 s0x_S24 x) (h : T24.HoleLeaf x F) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcov : ∀ t : Fin 9, t ∈ U ∨ t ∈ Dn)
    (hcyc : S0xCycUD s0x_S24 c U Dn) {w : ℝ³} (hcell : CellAt F U Dn w)
    {a cc : ZMod k} (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hext : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 → j ≠ cc →
      |Split.det3 (x (c j) - x (c a)) (x (c (a + 1)) - x (c a)) w| <
        |Split.det3 (x (c cc) - x (c a)) (x (c (a + 1)) - x (c a)) w|)
    (hsep : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ j : ZMod k, (j - a - 1).val < (cc - a - 1).val → σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫) < 0) ∧
      (∀ j : ZMod k, (cc - a - 1).val < (j - a - 1).val → 0 < σ * (⟪x (c j), w⟫ - ⟪x (c cc), w⟫))) :
    False :=
  h.2.2.2.2.1 (oc_splitAny_of_cell F hk c hc hcov hcyc hcell hca hca1 hext hsep)


/-! ## The unconditional facet signs -/

theorem inner_cap (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (α β γ : ℝ) :
    ⟪F.N t, capView x α β γ⟫ = α * (F.f t (x 0) - F.f t (x 1)) +
      β * (F.f t (x 2) - F.f t (x 1)) + γ * (F.f t (x 6) - F.f t (x 1)) := by
  unfold capView
  simp only [inner_add_right, real_inner_smul_right, F.inner_sub]

theorem real_f3 (x0 g w5 a5 b5 c5 P f2 f6 : ℝ) (hs : a5 + b5 - 1 = w5 * c5) (hg : g * w5 = 1 - x0)
    (e5 : 0 = P + a5 * (0 - P) + b5 * (f2 - P) + c5 * (f6 - P)) (hw : 0 < w5) (hc5 : 0 < c5)
    (hf2 : f2 < 0) (hI : 1 - a5 < b5 * x0) :
    -x0 * (0 - P) + 1 * (f2 - P) + g * (f6 - P) < 0 := by
  have key : (a5 + b5 - 1) * (-x0 * (0 - P) + 1 * (f2 - P) + g * (f6 - P)) =
      (a5 - 1 + b5 * x0) * f2 := by
    linear_combination (-(1 - x0)) * e5 + (c5 * (f6 - P)) * hg + (g * (f6 - P)) * hs
  have hs0 : 0 < a5 + b5 - 1 := by rw [hs]; positivity
  have h2 : 0 < a5 - 1 + b5 * x0 := by linarith
  have : (a5 + b5 - 1) * (-x0 * (0 - P) + 1 * (f2 - P) + g * (f6 - P)) < 0 := by
    rw [key]; exact mul_neg_of_pos_of_neg h2 hf2
  by_contra hh
  push Not at hh
  nlinarith


theorem real_f4 (x0 g w4 w5 a4 b4 c4 P f2 : ℝ)
    (e4 : 0 = P + a4 * (0 - P) + b4 * (f2 - P) + c4 * (0 - P))
    (hs4 : a4 + c4 - 1 = w4 * b4) (hb4 : 0 < b4) (hP : P < 0)
    (hg : g * w5 = 1 - x0) (hw5 : 0 < w5) (hx0 : 0 < x0) (hprod : 1 < w4 * w5) :
    -x0 * (0 - P) + 1 * (f2 - P) + g * (0 - P) < 0 := by
  have hB : f2 - P = w4 * P := by
    apply mul_left_cancel₀ hb4.ne'
    linear_combination (-1 : ℝ) * e4 + P * hs4
  have hgw : 0 < w4 - g := by
    have : 0 < (w4 - g) * w5 := by nlinarith
    exact pos_of_mul_pos_left this hw5.le |>.trans_le le_rfl
  have : -x0 * (0 - P) + 1 * (f2 - P) + g * (0 - P) = P * (x0 + (w4 - g)) := by
    rw [hB]; ring
  rw [this]
  exact mul_neg_of_neg_of_pos hP (by linarith)

theorem real_f7 (x0 g w3 a3 b3 c3 P f0 : ℝ)
    (e3 : 0 = P + a3 * (f0 - P) + b3 * (0 - P) + c3 * (0 - P))
    (hs3 : b3 + c3 - 1 = w3 * a3) (ha3 : 0 < a3) (hP : P < 0) (hg : 0 < g) (hx0 : 0 < x0)
    (hw3 : 0 < w3) :
    0 < -x0 * (f0 - P) + 1 * (0 - P) + g * (0 - P) := by
  have hB : f0 - P = w3 * P := by
    apply mul_left_cancel₀ ha3.ne'
    linear_combination (-1 : ℝ) * e3 + P * hs3
  have : -x0 * (f0 - P) + 1 * (0 - P) + g * (0 - P) = (-P) * (x0 * w3 + 1 + g) := by
    rw [hB]; ring
  rw [this]
  exact mul_pos (by linarith) (by positivity)

theorem real_f2 (x0 δ g w5 a5 b5 c5 P f6 : ℝ)
    (e5 : 0 = P + a5 * (0 - P) + b5 * (0 - P) + c5 * (f6 - P))
    (hs : a5 + b5 - 1 = w5 * c5) (hc5 : 0 < c5) (hg : g * w5 = 1 - x0 + δ) :
    -x0 * (0 - P) + 1 * (0 - P) + g * (f6 - P) = δ * P := by
  have hB : f6 - P = w5 * P := by
    apply mul_left_cancel₀ hc5.ne'
    linear_combination (-1 : ℝ) * e5 + P * hs
  rw [hB]
  linear_combination P * hg

variable (F : S0xFac 9 s0x_S24 x)

theorem facet0_neg (x0 γ : ℝ) (hγ : 0 < γ) : ⟪F.N 0, capView x (-x0) 1 γ⟫ < 0 := by
  rw [inner_cap, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
  have := F.neg 0 6 (by decide)
  nlinarith

theorem facet1_neg (x0 γ : ℝ) : ⟪F.N 1, capView x (-x0) 1 γ⟫ < 0 := by
  rw [inner_cap, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
  have := F.neg 1 2 (by decide)
  nlinarith

theorem facet5_pos (x0 γ : ℝ) (hx0 : 0 < x0) : 0 < ⟪F.N 5, capView x (-x0) 1 γ⟫ := by
  rw [inner_cap, F.zero 5 2 (by decide), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]
  have := F.neg 5 0 (by decide)
  nlinarith


open Minimality.T24.M4 in
theorem facet7_pos (hC : CbarIn x) (x0 γ : ℝ) (hx0 : 0 < x0) (hγ : 0 < γ) :
    0 < ⟪F.N 7, capView x (-x0) 1 γ⟫ := by
  have T := type24OfFac F
  rw [inner_cap, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
  have e3 := fac_eval F 7 3
  rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at e3
  exact real_f7 x0 γ (omega3 x) (oblX0 x 3) (oblX2 x 3) (oblX6 x 3) (F.f 7 (x 1)) (F.f 7 (x 0))
    e3 (by rw [← eq3 F]; ring) (T.X0_pos (v := 3) (by decide)) (F.neg 7 1 (by decide)) hγ hx0 hC.1

open Minimality.T24.M4 in
theorem facet4_neg (hC : CbarIn x) (x0 : ℝ) (hx0 : 0 < x0) :
    ⟪F.N 4, capView x (-x0) 1 ((1 - x0) / omega5 x)⟫ < 0 := by
  have T := type24OfFac F
  rw [inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]
  have e4 := fac_eval F 4 4
  rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e4
  have hw5 := hC.2.2.1
  exact real_f4 x0 _ (omega4 x) (omega5 x) (oblX0 x 4) (oblX2 x 4) (oblX6 x 4) (F.f 4 (x 1))
    (F.f 4 (x 2)) e4 (eq4 F) (T.X2_pos (v := 4) (by decide)) (F.neg 4 1 (by decide))
    (by field_simp) hw5 hx0 (omega_prod_gt_one hC.2.1 hC.2.2.1 hC.1 (by
      have := hC.2.2.2; unfold Delta24 at this; nlinarith) |> fun h => by nlinarith)

open Minimality.T24.M4 in
theorem facet3_neg (hC : CbarIn x) (x0 : ℝ) (hI : 1 - oblX0 x 5 < oblX2 x 5 * x0) :
    ⟪F.N 3, capView x (-x0) 1 ((1 - x0) / omega5 x)⟫ < 0 := by
  have T := type24OfFac F
  rw [inner_cap, F.zero 3 0 (by decide)]
  have e5 := fac_eval F 3 5
  rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at e5
  have hw5 := hC.2.2.1
  exact real_f3 x0 _ (omega5 x) (oblX0 x 5) (oblX2 x 5) (oblX6 x 5) (F.f 3 (x 1))
    (F.f 3 (x 2)) (F.f 3 (x 6)) (eq5 F) (by field_simp) e5 hw5
    (T.X6_pos (v := 5) (by decide)) (F.neg 3 2 (by decide)) hI

open Minimality.T24.M4 in
theorem facet2_eq (hC : CbarIn x) (x0 δ : ℝ) :
    ⟪F.N 2, capView x (-x0) 1 ((1 - x0 + δ) / omega5 x)⟫ = δ * F.f 2 (x 1) := by
  have T := type24OfFac F
  rw [inner_cap, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
  have e5 := fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e5
  have hw5 := hC.2.2.1
  exact real_f2 x0 δ _ (omega5 x) (oblX0 x 5) (oblX2 x 5) (oblX6 x 5) (F.f 2 (x 1))
    (F.f 2 (x 6)) e5 (eq5 F) (T.X6_pos (v := 5) (by decide)) (by field_simp)


/-- The family `c^(b)(x0, δ) = (-x0, 1, (1 - x0 + δ) / ω5)` as a view. -/
noncomputable def uF (x : Fin 7 → ℝ³) (x0 δ : ℝ) : ℝ³ :=
  capView x (-x0) 1 ((1 - x0 + δ) / omega5 x)

theorem ev_pos {g : ℝ → ℝ} (hg : Continuous g) (h0 : 0 < g 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < g δ :=
  (hg.continuousAt.eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds

/-- **Core**: the Split family from its value at `δ = 0`. -/
theorem splitFam_core (hC : CbarIn x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c) (pat : Fin 9 → Bool)
    (hcyc : S0xCycOK s0x_S24 c pat) (hc0 : c 0 = 1) (hc1 : c 1 = 2)
    (j6 : ZMod k) (hj6 : c j6 = 6) (hj60 : j6 ≠ 0) (hj61 : j6 ≠ 1)
    (cc : ZMod k) (hcc0 : cc ≠ 0) (hcc1 : cc ≠ 1) (hp2 : pat 2 = false)
    (x0 : ℝ) (hx0 : 0 < x0)
    (hfac : ∀ t, t ≠ 2 → ((pat t = true → 0 < ⟪F.N t, uF x x0 0⟫) ∧
      (pat t = false → ⟪F.N t, uF x x0 0⟫ < 0)))
    (hext : ∀ j : ZMod k, j ≠ 0 → j ≠ 1 → j ≠ cc →
      Hh x x0 ((1 - x0) / omega5 x) (c j) < Hh x x0 ((1 - x0) / omega5 x) (c cc))
    (hfirst : ∀ j : ZMod k, (j - 0 - 1).val < (cc - 0 - 1).val →
      0 < zz x (uF x x0 0) (c j) - zz x (uF x x0 0) (c cc))
    (hsecond : ∀ j : ZMod k, (cc - 0 - 1).val < (j - 0 - 1).val →
      zz x (uF x x0 0) (c j) - zz x (uF x x0 0) (c cc) < 0) :
    Gen.SplitAny F := by
  have hw5 := hC.2.2.1
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ t, (pat t = true → 0 < ⟪F.N t, uF x x0 δ⟫) ∧ (pat t = false → ⟪F.N t, uF x x0 δ⟫ < 0)) ∧
      (∀ j : ZMod k, j ≠ 0 → j ≠ 1 → j ≠ cc →
        Hh x x0 ((1 - x0 + δ) / omega5 x) (c j) < Hh x x0 ((1 - x0 + δ) / omega5 x) (c cc)) ∧
      (∀ j : ZMod k, (j - 0 - 1).val < (cc - 0 - 1).val →
        0 < zz x (uF x x0 δ) (c j) - zz x (uF x x0 δ) (c cc)) ∧
      (∀ j : ZMod k, (cc - 0 - 1).val < (j - 0 - 1).val →
        zz x (uF x x0 δ) (c j) - zz x (uF x x0 δ) (c cc) < 0) := by
    refine Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ ?_))
    · rw [eventually_all]
      intro t
      by_cases ht : t = 2
      · subst ht
        have hP := F.neg 2 1 (by decide)
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        have hδ' : (0 : ℝ) < δ := hδ
        simp only [hp2, uF, facet2_eq F hC]
        exact ⟨by simp, fun _ => mul_neg_of_pos_of_neg hδ' hP⟩
      · obtain ⟨h1, h2⟩ := hfac t ht
        by_cases hpt : pat t = true
        · have := ev_pos (g := fun δ => ⟪F.N t, uF x x0 δ⟫) (by unfold uF capView; fun_prop) (h1 hpt)
          filter_upwards [this] with δ hδ
          exact ⟨fun _ => hδ, fun h => absurd hpt (by simp [h])⟩
        · have hpf : pat t = false := by simpa using hpt
          have := ev_pos (g := fun δ => - ⟪F.N t, uF x x0 δ⟫) (by unfold uF capView; fun_prop)
            (by have := h2 hpf; simpa using this)
          filter_upwards [this] with δ hδ
          exact ⟨fun h => absurd h hpt, fun _ => by linarith⟩
    · rw [eventually_all]; intro j
      by_cases hj : j ≠ 0 ∧ j ≠ 1 ∧ j ≠ cc
      · have := ev_pos (g := fun δ => Hh x x0 ((1 - x0 + δ) / omega5 x) (c cc) -
            Hh x x0 ((1 - x0 + δ) / omega5 x) (c j)) (by unfold Hh; fun_prop)
          (by simpa using hext j hj.1 hj.2.1 hj.2.2)
        filter_upwards [this] with δ hδ
        intro _ _ _; linarith
      · exact Eventually.of_forall fun δ h0 h1 hc' => absurd ⟨h0, h1, hc'⟩ hj
    · rw [eventually_all]; intro j
      by_cases hj : (j - 0 - 1).val < (cc - 0 - 1).val
      · have := ev_pos (g := fun δ => zz x (uF x x0 δ) (c j) - zz x (uF x x0 δ) (c cc))
          (by unfold zz uF capView; fun_prop) (hfirst j hj)
        filter_upwards [this] with δ hδ using fun _ => hδ
      · exact Eventually.of_forall fun δ h => absurd h hj
    · rw [eventually_all]; intro j
      by_cases hj : (cc - 0 - 1).val < (j - 0 - 1).val
      · have := ev_pos (g := fun δ => -(zz x (uF x x0 δ) (c j) - zz x (uF x x0 δ) (c cc)))
          (by unfold zz uF capView; fun_prop) (by simpa using hsecond j hj)
        filter_upwards [this] with δ hδ
        intro _; linarith
      · exact Eventually.of_forall fun δ h => absurd h hj
  obtain ⟨δ, ⟨h1, h2, h3, h4⟩, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
  exact splitAny_of_rim F hk c hc pat hcyc hc0 hc1 j6 hj6 hj60 hj61 cc hcc0 hcc1 x0
    ((1 - x0 + δ) / omega5 x) hx0 h1 h2 h3 h4


/-! ## The four systems -/

/-- The base view `c^(b)(x0, 0)` of the family. -/
noncomputable def uB (x : Fin 7 → ℝ³) (x0 : ℝ) : ℝ³ := capView x (-x0) 1 ((1 - x0) / omega5 x)

theorem uF_zero (x0 : ℝ) : uF x x0 0 = uB x x0 := by simp [uF, uB]

theorem zz_one (u : ℝ³) : zz x u 1 = 0 := by simp [zz]

open Minimality.T24.M4 in
theorem Hh_six (F : S0xFac 9 s0x_S24 x) (x0 γ : ℝ) : Hh x x0 γ 6 = x0 := by
  have T := type24OfFac F
  simp [Hh, T.oblX6_six, Type24.oblX0_six]

def cA : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]
def cB : ZMod 6 → Fin 7 := ![1, 2, 5, 3, 4, 6]
/-- Up facets `5, 6, 7` (facet `8 = 346` front: vertex `4` hidden). -/
def patA : Fin 9 → Bool := fun t => decide (t = 5 ∨ t = 6 ∨ t = 7)
/-- Up facets `5, 6, 7, 8`. -/
def patB : Fin 9 → Bool := fun t => decide (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8)

theorem cA_inj : Function.Injective cA := by decide
theorem cB_inj : Function.Injective cB := by decide
theorem cA_cyc : S0xCycOK s0x_S24 cA patA := by unfold S0xCycOK; decide
theorem cB_cyc : S0xCycOK s0x_S24 cB patB := by unfold S0xCycOK; decide

/-- The exponent data `I5`: `max 0 ((1 - a5)/b5) < x0 < 1`. -/
def InI5 (x : Fin 7 → ℝ³) (x0 : ℝ) : Prop :=
  0 < x0 ∧ x0 < 1 ∧ 1 - oblX0 x 5 < oblX2 x 5 * x0

/-- System `S6-`: 5-rim `1.2.5.3.6`, edge `[1,2]`, apex `6`. -/
def S6m (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  0 < ⟪F.N 6, uB x x0⟫ ∧ ⟪F.N 8, uB x x0⟫ < 0 ∧
  Hh x x0 ((1 - x0) / omega5 x) 3 < x0 ∧ Hh x x0 ((1 - x0) / omega5 x) 5 < x0 ∧
  0 < zz x (uB x x0) 6 ∧ zz x (uB x x0) 6 < zz x (uB x x0) 2 ∧
  zz x (uB x x0) 6 < zz x (uB x x0) 5 ∧ zz x (uB x x0) 6 < zz x (uB x x0) 3

theorem facets_base (hC : CbarIn x) {x0 : ℝ} (hI : InI5 x x0) (t : Fin 9) (ht : t ≠ 2) :
    (t = 0 → ⟪F.N t, uB x x0⟫ < 0) ∧ (t = 1 → ⟪F.N t, uB x x0⟫ < 0) ∧
    (t = 3 → ⟪F.N t, uB x x0⟫ < 0) ∧ (t = 4 → ⟪F.N t, uB x x0⟫ < 0) ∧
    (t = 5 → 0 < ⟪F.N t, uB x x0⟫) ∧ (t = 7 → 0 < ⟪F.N t, uB x x0⟫) := by
  obtain ⟨hx0, hx1, hI5⟩ := hI
  have hγ : 0 < (1 - x0) / omega5 x := div_pos (by linarith) hC.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl; exact facet0_neg F x0 _ hγ
  · rintro rfl; exact facet1_neg F x0 _
  · rintro rfl; exact facet3_neg F hC x0 hI5
  · rintro rfl; exact facet4_neg F hC x0 hx0
  · rintro rfl; exact facet5_pos F x0 _ hx0
  · rintro rfl; exact facet7_pos F hC x0 _ hx0 hγ

theorem splitFam_S6m (hC : CbarIn x) {x0 : ℝ} (hI : InI5 x x0) (h : S6m F x0) :
    Gen.SplitAny F := by
  obtain ⟨h6, h8, hH3, hH5, hz6, hz62, hz65, hz63⟩ := h
  have hb := facets_base F hC hI
  refine splitFam_core F hC (k := 5) (by norm_num) cA cA_inj patA cA_cyc rfl rfl 4 rfl
    (by decide) (by decide) 4 (by decide) (by decide) (by decide) x0 hI.1 ?_ ?_ ?_ ?_
  · intro t ht
    rw [uF_zero]
    have key : ∀ t : Fin 9, t ≠ 2 → (patA t = true ↔ (t = 5 ∨ t = 6 ∨ t = 7)) := by
      intro t _; simp [patA]
    obtain ⟨b0, b1, b3, b4, b5, b7⟩ := hb t ht
    constructor
    · intro hp
      rcases (key t ht).1 hp with rfl | rfl | rfl
      · exact b5 rfl
      · exact h6
      · exact b7 rfl
    · intro hp
      have : ¬ (t = 5 ∨ t = 6 ∨ t = 7) := fun hh => by simp [(key t ht).2 hh] at hp
      have hdec : ∀ t : Fin 9, t ≠ 2 → ¬ (t = 5 ∨ t = 6 ∨ t = 7) →
          t = 0 ∨ t = 1 ∨ t = 3 ∨ t = 4 ∨ t = 8 := by decide
      have h' := hdec t ht this
      rcases h' with rfl | rfl | rfl | rfl | rfl
      · exact b0 rfl
      · exact b1 rfl
      · exact b3 rfl
      · exact b4 rfl
      · exact h8
  · intro j hj0 hj1 hjc
    have : j = 2 ∨ j = 3 := by revert hj0 hj1 hjc; revert j; decide
    have e4 : cA 4 = 6 := rfl
    rw [e4, Hh_six F]
    rcases this with rfl | rfl
    · exact hH5
    · exact hH3
  · intro j hj
    have : j = 1 ∨ j = 2 ∨ j = 3 := by revert hj; revert j; decide
    rw [uF_zero]
    have e4 : cA 4 = 6 := rfl
    rw [e4]
    rcases this with rfl | rfl | rfl
    · show 0 < zz x _ 2 - _; linarith
    · show 0 < zz x _ 5 - _; linarith
    · show 0 < zz x _ 3 - _; linarith
  · intro j hj
    have : j = 0 := by revert hj; revert j; decide
    subst this
    rw [uF_zero]
    have e4 : cA 4 = 6 := rfl
    rw [e4]
    show zz x _ 1 - _ < 0
    rw [zz_one]; linarith

/-- System `S6+`: 6-rim `1.2.5.3.4.6`, edge `[1,2]`, apex `6`. -/
def S6p (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  0 < ⟪F.N 6, uB x x0⟫ ∧ 0 < ⟪F.N 8, uB x x0⟫ ∧
  Hh x x0 ((1 - x0) / omega5 x) 3 < x0 ∧ Hh x x0 ((1 - x0) / omega5 x) 4 < x0 ∧
  Hh x x0 ((1 - x0) / omega5 x) 5 < x0 ∧
  0 < zz x (uB x x0) 6 ∧ zz x (uB x x0) 6 < zz x (uB x x0) 2 ∧
  zz x (uB x x0) 6 < zz x (uB x x0) 5 ∧ zz x (uB x x0) 6 < zz x (uB x x0) 3 ∧
  zz x (uB x x0) 6 < zz x (uB x x0) 4

theorem splitFam_S6p (hC : CbarIn x) {x0 : ℝ} (hI : InI5 x x0) (h : S6p F x0) :
    Gen.SplitAny F := by
  obtain ⟨h6, h8, hH3, hH4, hH5, hz6, hz62, hz65, hz63, hz64⟩ := h
  have hb := facets_base F hC hI
  refine splitFam_core F hC (k := 6) (by norm_num) cB cB_inj patB cB_cyc rfl rfl 5 rfl
    (by decide) (by decide) 5 (by decide) (by decide) (by decide) x0 hI.1 ?_ ?_ ?_ ?_
  · intro t ht
    rw [uF_zero]
    have key : ∀ t : Fin 9, t ≠ 2 → (patB t = true ↔ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8)) := by
      intro t _; simp [patB]
    obtain ⟨b0, b1, b3, b4, b5, b7⟩ := hb t ht
    constructor
    · intro hp
      rcases (key t ht).1 hp with rfl | rfl | rfl | rfl
      · exact b5 rfl
      · exact h6
      · exact b7 rfl
      · exact h8
    · intro hp
      have : ¬ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8) := fun hh => by simp [(key t ht).2 hh] at hp
      have hdec : ∀ t : Fin 9, t ≠ 2 → ¬ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8) →
          t = 0 ∨ t = 1 ∨ t = 3 ∨ t = 4 := by decide
      have h' := hdec t ht this
      rcases h' with rfl | rfl | rfl | rfl
      · exact b0 rfl
      · exact b1 rfl
      · exact b3 rfl
      · exact b4 rfl
  · intro j hj0 hj1 hjc
    have : j = 2 ∨ j = 3 ∨ j = 4 := by revert hj0 hj1 hjc; revert j; decide
    have e : cB 5 = 6 := rfl
    rw [e, Hh_six F]
    rcases this with rfl | rfl | rfl
    · exact hH5
    · exact hH3
    · exact hH4
  · intro j hj
    have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert hj; revert j; decide
    rw [uF_zero]
    have e : cB 5 = 6 := rfl
    rw [e]
    rcases this with rfl | rfl | rfl | rfl
    · show 0 < zz x _ 2 - _; linarith
    · show 0 < zz x _ 5 - _; linarith
    · show 0 < zz x _ 3 - _; linarith
    · show 0 < zz x _ 4 - _; linarith
  · intro j hj
    have : j = 0 := by revert hj; revert j; decide
    subst this
    rw [uF_zero]
    have e : cB 5 = 6 := rfl
    rw [e]
    show zz x _ 1 - _ < 0
    rw [zz_one]; linarith

/-- System `S4+`: 6-rim `1.2.5.3.4.6`, edge `[1,2]`, apex `4`. -/
def S4p (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  0 < ⟪F.N 6, uB x x0⟫ ∧ 0 < ⟪F.N 8, uB x x0⟫ ∧
  x0 < Hh x x0 ((1 - x0) / omega5 x) 4 ∧ Hh x x0 ((1 - x0) / omega5 x) 3 <
    Hh x x0 ((1 - x0) / omega5 x) 4 ∧
  Hh x x0 ((1 - x0) / omega5 x) 5 < Hh x x0 ((1 - x0) / omega5 x) 4 ∧
  0 < zz x (uB x x0) 4 ∧ zz x (uB x x0) 6 < zz x (uB x x0) 4 ∧
  zz x (uB x x0) 4 < zz x (uB x x0) 2 ∧ zz x (uB x x0) 4 < zz x (uB x x0) 5 ∧
  zz x (uB x x0) 4 < zz x (uB x x0) 3

theorem splitFam_S4p (hC : CbarIn x) {x0 : ℝ} (hI : InI5 x x0) (h : S4p F x0) :
    Gen.SplitAny F := by
  obtain ⟨h6, h8, hH6, hH3, hH5, hz4, hz64, hz42, hz45, hz43⟩ := h
  have hb := facets_base F hC hI
  refine splitFam_core F hC (k := 6) (by norm_num) cB cB_inj patB cB_cyc rfl rfl 5 rfl
    (by decide) (by decide) 4 (by decide) (by decide) (by decide) x0 hI.1 ?_ ?_ ?_ ?_
  · intro t ht
    rw [uF_zero]
    have key : ∀ t : Fin 9, t ≠ 2 → (patB t = true ↔ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8)) := by
      intro t _; simp [patB]
    obtain ⟨b0, b1, b3, b4, b5, b7⟩ := hb t ht
    constructor
    · intro hp
      rcases (key t ht).1 hp with rfl | rfl | rfl | rfl
      · exact b5 rfl
      · exact h6
      · exact b7 rfl
      · exact h8
    · intro hp
      have : ¬ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8) := fun hh => by simp [(key t ht).2 hh] at hp
      have hdec : ∀ t : Fin 9, t ≠ 2 → ¬ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8) →
          t = 0 ∨ t = 1 ∨ t = 3 ∨ t = 4 := by decide
      have h' := hdec t ht this
      rcases h' with rfl | rfl | rfl | rfl
      · exact b0 rfl
      · exact b1 rfl
      · exact b3 rfl
      · exact b4 rfl
  · intro j hj0 hj1 hjc
    have : j = 2 ∨ j = 3 ∨ j = 5 := by revert hj0 hj1 hjc; revert j; decide
    rcases this with rfl | rfl | rfl
    · exact hH5
    · exact hH3
    · show Hh x x0 _ 6 < _
      rw [Hh_six F]; exact hH6
  · intro j hj
    have : j = 1 ∨ j = 2 ∨ j = 3 := by revert hj; revert j; decide
    rw [uF_zero]
    rcases this with rfl | rfl | rfl
    · show 0 < zz x _ 2 - zz x _ 4; linarith
    · show 0 < zz x _ 5 - zz x _ 4; linarith
    · show 0 < zz x _ 3 - zz x _ 4; linarith
  · intro j hj
    have : j = 5 ∨ j = 0 := by revert hj; revert j; decide
    rw [uF_zero]
    rcases this with rfl | rfl
    · show zz x _ 6 - zz x _ 4 < 0; linarith
    · show zz x _ 1 - zz x _ 4 < 0
      rw [zz_one]; linarith

/-- System `S3` with `psi8 < 0`: 5-rim `1.2.5.3.6`, edge `[1,2]`, apex `3`. -/
def S3m (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  0 < ⟪F.N 6, uB x x0⟫ ∧ ⟪F.N 8, uB x x0⟫ < 0 ∧
  x0 < Hh x x0 ((1 - x0) / omega5 x) 3 ∧ Hh x x0 ((1 - x0) / omega5 x) 5 <
    Hh x x0 ((1 - x0) / omega5 x) 3 ∧
  0 < zz x (uB x x0) 3 ∧ zz x (uB x x0) 6 < zz x (uB x x0) 3 ∧
  zz x (uB x x0) 3 < zz x (uB x x0) 2 ∧ zz x (uB x x0) 3 < zz x (uB x x0) 5

theorem splitFam_S3m (hC : CbarIn x) {x0 : ℝ} (hI : InI5 x x0) (h : S3m F x0) :
    Gen.SplitAny F := by
  obtain ⟨h6, h8, hH6, hH5, hz3, hz63, hz32, hz35⟩ := h
  have hb := facets_base F hC hI
  refine splitFam_core F hC (k := 5) (by norm_num) cA cA_inj patA cA_cyc rfl rfl 4 rfl
    (by decide) (by decide) 3 (by decide) (by decide) (by decide) x0 hI.1 ?_ ?_ ?_ ?_
  · intro t ht
    rw [uF_zero]
    have key : ∀ t : Fin 9, t ≠ 2 → (patA t = true ↔ (t = 5 ∨ t = 6 ∨ t = 7)) := by
      intro t _; simp [patA]
    obtain ⟨b0, b1, b3, b4, b5, b7⟩ := hb t ht
    constructor
    · intro hp
      rcases (key t ht).1 hp with rfl | rfl | rfl
      · exact b5 rfl
      · exact h6
      · exact b7 rfl
    · intro hp
      have : ¬ (t = 5 ∨ t = 6 ∨ t = 7) := fun hh => by simp [(key t ht).2 hh] at hp
      have hdec : ∀ t : Fin 9, t ≠ 2 → ¬ (t = 5 ∨ t = 6 ∨ t = 7) →
          t = 0 ∨ t = 1 ∨ t = 3 ∨ t = 4 ∨ t = 8 := by decide
      have h' := hdec t ht this
      rcases h' with rfl | rfl | rfl | rfl | rfl
      · exact b0 rfl
      · exact b1 rfl
      · exact b3 rfl
      · exact b4 rfl
      · exact h8
  · intro j hj0 hj1 hjc
    have : j = 2 ∨ j = 4 := by revert hj0 hj1 hjc; revert j; decide
    rcases this with rfl | rfl
    · exact hH5
    · show Hh x x0 _ 6 < _
      rw [Hh_six F]; exact hH6
  · intro j hj
    have : j = 1 ∨ j = 2 := by revert hj; revert j; decide
    rw [uF_zero]
    rcases this with rfl | rfl
    · show 0 < zz x _ 2 - zz x _ 3; linarith
    · show 0 < zz x _ 5 - zz x _ 3; linarith
  · intro j hj
    have : j = 4 ∨ j = 0 := by revert hj; revert j; decide
    rw [uF_zero]
    rcases this with rfl | rfl
    · show zz x _ 6 - zz x _ 3 < 0; linarith
    · show zz x _ 1 - zz x _ 3 < 0
      rw [zz_one]; linarith

/-- System `S3` with `psi8 > 0`: 6-rim `1.2.5.3.4.6`, edge `[1,2]`, apex `3`. -/
def S3p (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  0 < ⟪F.N 6, uB x x0⟫ ∧ 0 < ⟪F.N 8, uB x x0⟫ ∧
  x0 < Hh x x0 ((1 - x0) / omega5 x) 3 ∧ Hh x x0 ((1 - x0) / omega5 x) 5 <
    Hh x x0 ((1 - x0) / omega5 x) 3 ∧
  Hh x x0 ((1 - x0) / omega5 x) 4 < Hh x x0 ((1 - x0) / omega5 x) 3 ∧
  0 < zz x (uB x x0) 3 ∧ zz x (uB x x0) 6 < zz x (uB x x0) 3 ∧
  zz x (uB x x0) 4 < zz x (uB x x0) 3 ∧
  zz x (uB x x0) 3 < zz x (uB x x0) 2 ∧ zz x (uB x x0) 3 < zz x (uB x x0) 5

theorem splitFam_S3p (hC : CbarIn x) {x0 : ℝ} (hI : InI5 x x0) (h : S3p F x0) :
    Gen.SplitAny F := by
  obtain ⟨h6, h8, hH6, hH5, hH4, hz3, hz63, hz43, hz32, hz35⟩ := h
  have hb := facets_base F hC hI
  refine splitFam_core F hC (k := 6) (by norm_num) cB cB_inj patB cB_cyc rfl rfl 5 rfl
    (by decide) (by decide) 3 (by decide) (by decide) (by decide) x0 hI.1 ?_ ?_ ?_ ?_
  · intro t ht
    rw [uF_zero]
    have key : ∀ t : Fin 9, t ≠ 2 → (patB t = true ↔ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8)) := by
      intro t _; simp [patB]
    obtain ⟨b0, b1, b3, b4, b5, b7⟩ := hb t ht
    constructor
    · intro hp
      rcases (key t ht).1 hp with rfl | rfl | rfl | rfl
      · exact b5 rfl
      · exact h6
      · exact b7 rfl
      · exact h8
    · intro hp
      have : ¬ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8) := fun hh => by simp [(key t ht).2 hh] at hp
      have hdec : ∀ t : Fin 9, t ≠ 2 → ¬ (t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8) →
          t = 0 ∨ t = 1 ∨ t = 3 ∨ t = 4 := by decide
      have h' := hdec t ht this
      rcases h' with rfl | rfl | rfl | rfl
      · exact b0 rfl
      · exact b1 rfl
      · exact b3 rfl
      · exact b4 rfl
  · intro j hj0 hj1 hjc
    have : j = 2 ∨ j = 4 ∨ j = 5 := by revert hj0 hj1 hjc; revert j; decide
    rcases this with rfl | rfl | rfl
    · exact hH5
    · exact hH4
    · show Hh x x0 _ 6 < _
      rw [Hh_six F]; exact hH6
  · intro j hj
    have : j = 1 ∨ j = 2 := by revert hj; revert j; decide
    rw [uF_zero]
    rcases this with rfl | rfl
    · show 0 < zz x _ 2 - zz x _ 3; linarith
    · show 0 < zz x _ 5 - zz x _ 3; linarith
  · intro j hj
    have : j = 4 ∨ j = 5 ∨ j = 0 := by revert hj; revert j; decide
    rw [uF_zero]
    rcases this with rfl | rfl | rfl
    · show zz x _ 4 - zz x _ 3 < 0; linarith
    · show zz x _ 6 - zz x _ 3 < 0; linarith
    · show zz x _ 1 - zz x _ 3 < 0
      rw [zz_one]; linarith

/-- **Carbon A70, Theorem 1.1 (full Gram matrix version).**  One of the five affine systems holds at `x0`. -/
def SplitFamily (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  S6m F x0 ∨ S6p F x0 ∨ S4p F x0 ∨ S3m F x0 ∨ S3p F x0

/-- **Theorem (single-family Split criterion).**  `CbarIn`, `x0 in I5 = (max 0 ((1-a5)/b5), 1)` and one of
the systems `S6-`, `S6+`, `S4+`, `S3` at the view `capView x (-x0) 1 ((1-x0)/omega5)` give a Split leaf.
No hypothesis `omega5 >= omega4` and no obtuseness is needed (the twin is the `pi24` image). -/
theorem splitFamily_splitAny (hC : CbarIn x) {x0 : ℝ} (hI : InI5 x x0) (h : SplitFamily F x0) :
    Gen.SplitAny F := by
  rcases h with h | h | h | h | h
  · exact splitFam_S6m F hC hI h
  · exact splitFam_S6p F hC hI h
  · exact splitFam_S4p F hC hI h
  · exact splitFam_S3m F hC hI h
  · exact splitFam_S3p F hC hI h

/-- The `pi24` twin (`omega4 > omega5`): the system for `x o pi24`, base edge `[6,1]`. -/
def SplitFamilyTwin (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  SplitFamily (Minimality.T24.Sym.sym24 F) x0

theorem splitFamilyTwin_splitAny (hC : CbarIn x) {x0 : ℝ} (hI : InI5 (x ∘ Minimality.T24.Sym.pi24) x0)
    (h : SplitFamilyTwin F x0) : Gen.SplitAny F :=
  Minimality.T24.Sym.splitAny24_sym F
    (splitFamily_splitAny _ ((Minimality.T24.Sym.cbarIn_comp_pi24 x).2 hC) hI h)

theorem holeLeaf_not_splitFamily (h : T24.HoleLeaf x F) {x0 : ℝ} (hI : InI5 x x0) :
    ¬ SplitFamily F x0 :=
  fun hs => h.2.2.2.2.1 (splitFamily_splitAny F h.1 hI hs)

theorem holeLeaf_not_splitFamilyTwin (h : T24.HoleLeaf x F) {x0 : ℝ}
    (hI : InI5 (x ∘ Minimality.T24.Sym.pi24) x0) : ¬ SplitFamilyTwin F x0 :=
  fun hs => h.2.2.2.2.1 (splitFamilyTwin_splitAny F h.1 hI hs)

theorem holeLeaf_not_splitFamS6m (h : T24.HoleLeaf x F) {x0 : ℝ} (hI : InI5 x x0) : ¬ S6m F x0 :=
  fun hs => holeLeaf_not_splitFamily F h hI (Or.inl hs)
theorem holeLeaf_not_splitFamS6p (h : T24.HoleLeaf x F) {x0 : ℝ} (hI : InI5 x x0) : ¬ S6p F x0 :=
  fun hs => holeLeaf_not_splitFamily F h hI (Or.inr (Or.inl hs))
theorem holeLeaf_not_splitFamS4p (h : T24.HoleLeaf x F) {x0 : ℝ} (hI : InI5 x x0) : ¬ S4p F x0 :=
  fun hs => holeLeaf_not_splitFamily F h hI (Or.inr (Or.inr (Or.inl hs)))

end Minimality.T24.SF
