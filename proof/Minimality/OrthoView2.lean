module

public import Minimality.OrthoView

@[expose] public section

open scoped RealInnerProductSpace

namespace Minimality.H21

open Minimality.RimCell Filter Topology

variable {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Openness of the strict cell along a ray: `u + ε d` is in the open cell for small `ε > 0`. -/
theorem eventually_cellAt_add {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u : ℝ³}
    (hu : CellAt F U Dn u) (d : ℝ³) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (u + ε • d) := by
  have e : ∀ t ε, ⟪F.N t, u + ε • d⟫ = ⟪F.N t, u⟫ + ε * ⟪F.N t, d⟫ := by
    intro t ε; rw [inner_add_right, inner_smul_right]
  refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
    (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
  · exact (eventually_pos_affine (A := ⟪F.N t, u⟫) (B := ⟪F.N t, d⟫)
      (Or.inl (hu.1 t ht))).mono fun ε hε => by rw [e]; exact hε
  · exact (eventually_pos_affine (A := -⟪F.N t, u⟫) (B := -⟪F.N t, d⟫)
      (Or.inl (by linarith [hu.2 t ht]))).mono fun ε hε => by rw [e]; linarith

/-- **Q4 with a lexicographic positive form.**  4-rim cell, `u` in the open cell; a diagonal
form negative at `u`, and a diagonal form that is `≥ 0` at `u` and, if it vanishes there,
positive along a direction `d`: Rupert (the perturbation `u + ε d` is a closed-cell point). -/
theorem isRupert_of_q4_lex (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u) (d : ℝ³)
    (hn : ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), u⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 ≤ ⟪x (c p.1) - x (c p.2), u⟫ ∧
      (⟪x (c p.1) - x (c p.2), u⟫ = 0 → 0 < ⟪x (c p.1) - x (c p.2), d⟫)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨p, hpm, hp0, hp1⟩ := hp
  rcases hp0.lt_or_eq with h | h
  · exact isRupert_of_closedCell_q4 F hx hc hcyc hu hu.cellLe hu.cellLe hn ⟨p, hpm, h⟩
  · obtain ⟨ε, hε, hε0⟩ := ((eventually_cellAt_add hu d).and self_mem_nhdsWithin).exists
    refine isRupert_of_closedCell_q4 F hx hc hcyc hu hu.cellLe hε.cellLe hn ⟨p, hpm, ?_⟩
    have h3 := hp1 h.symm
    have h4 : 0 < ε := hε0
    rw [inner_add_right, inner_smul_right, ← h]
    nlinarith [mul_pos h4 h3]

/-- **Lemma CV1 (cevian lemma), metric-free.**  A 4-rim cell certificate whose rim has two
adjacent vertices `K = c a`, `J = c (a+1)` and closure points `g, g'` with
`⟪x K - x J, g⟫ < 0 < ⟪x K - x J, g'⟫`: Rupert. -/
theorem isRupert_of_cevian (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a₀ g g' : ℝ³} (ha : CellAt F U Dn a₀)
    (hg : CellLe F U Dn g) (hg' : CellLe F U Dn g') (a : ZMod 4)
    (hn : ⟪x (c a) - x (c (a + 1)), g⟫ < 0) (hp : 0 < ⟪x (c a) - x (c (a + 1)), g'⟫) :
    IsRupert (Finset.univ.image x) := by
  have ng : ∀ w : ℝ³, ⟪x (c (a + 1)) - x (c a), w⟫ = -⟪x (c a) - x (c (a + 1)), w⟫ := by
    intro w; rw [← inner_neg_left, neg_sub]
  have h1 := ng g
  have h2 := ng g'
  rcases (by decide : ∀ a : ZMod 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) a with rfl | rfl | rfl | rfl
  · have e : (0 : ZMod 4) + 1 = 1 := by decide
    rw [e] at hn hp
    exact isRupert_of_closedCell_q4 F hx hc hcyc ha hg hg'
      ⟨(0, 1), by decide, hn⟩ ⟨(0, 1), by decide, hp⟩
  · have e : (1 : ZMod 4) + 1 = 2 := by decide
    rw [e] at hn hp h1 h2
    exact isRupert_of_closedCell_q4 F hx hc hcyc ha hg' hg
      ⟨(2, 1), by decide, by linarith⟩ ⟨(2, 1), by decide, by linarith⟩
  · have e : (2 : ZMod 4) + 1 = 3 := by decide
    rw [e] at hn hp
    exact isRupert_of_closedCell_q4 F hx hc hcyc ha hg hg'
      ⟨(2, 3), by decide, hn⟩ ⟨(2, 3), by decide, hp⟩
  · have e : (3 : ZMod 4) + 1 = 0 := by decide
    rw [e] at hn hp h1 h2
    exact isRupert_of_closedCell_q4 F hx hc hcyc ha hg' hg
      ⟨(0, 3), by decide, by linarith⟩ ⟨(0, 3), by decide, by linarith⟩

/-- **Theorem P, EEEV case.**  Rim `c 0 = E1, c 1 = V, c 2 = E2, c 3 = E3` at the orthocentre
view `u` (`⟪v e, u⟫ = 1`): `σ E1 < σ V` (e.g. `σ E1 = 1 < σ V`) and `σ E1 = σ E3`.  The form
`E1 - V` is negative at `u`, the form `E1 - E3` vanishes there; given a direction `d` with
`⟪x E1 - x E3, d⟫ > 0` (the geometric part), the perturbation `u + ε d` is in the closed cell. -/
theorem isRupert_of_orthocentre_eeev {k : ℕ} (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³)
    (y : Fin n → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (h01 : (∑ e, y (c 0) e) < ∑ e, y (c 1) e) (h03 : (∑ e, y (c 0) e) = ∑ e, y (c 3) e)
    (d : ℝ³) (hd : 0 < ⟪x (c 0) - x (c 3), d⟫) :
    IsRupert (Finset.univ.image x) := by
  refine isRupert_of_q4_lex F hx hc hcyc hu d ⟨(0, 1), by decide, ?_⟩
    ⟨(0, 3), by decide, ?_, fun _ => hd⟩
  · rw [depth_orthocentre x p v y hxy u hv]; exact sub_neg.2 h01
  · rw [depth_orthocentre x p v y hxy u hv, h03]; simp

/-- **Theorem P, EVVV case.**  Rim `c 0, c 1, c 2, c 3` with crossing diagonals
`[c 0, c 2]`, `[c 1, c 3]` (`hX`), orthocentre view `u`, `σ (c 0) < σ (c 1), σ (c 3)`.  Lemma S
gives `min (σ c1) (σ c3) ≤ σ c2`; the strict case closes at `u`; in the tie case `σ c2 = σ c1`
(resp. `σ c3`) a direction `d` with `⟪x c2 - x c1, d⟫ > 0` (resp. `⟪x c2 - x c3, d⟫ > 0`)
is needed. -/
theorem isRupert_of_orthocentre_evvv {k : ℕ} (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u) (p : ℝ³) (v : Fin k → ℝ³)
    (y : Fin n → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (h01 : (∑ e, y (c 0) e) < ∑ e, y (c 1) e) (h03 : (∑ e, y (c 0) e) < ∑ e, y (c 3) e)
    {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hX : (1 - s) • x (c 0) + s • x (c 2) = (1 - t) • x (c 1) + t • x (c 3))
    (d : ℝ³)
    (d1 : (∑ e, y (c 2) e) = ∑ e, y (c 1) e → 0 < ⟪x (c 2) - x (c 1), d⟫)
    (d3 : (∑ e, y (c 2) e) = ∑ e, y (c 3) e → 0 < ⟪x (c 2) - x (c 3), d⟫) :
    IsRupert (Finset.univ.image x) := by
  have D := depth_orthocentre x p v y hxy u hv
  have key : ∀ i j, ⟪u, x (c i)⟫ - ⟪u, x (c j)⟫ = (∑ e, y (c i) e) - ∑ e, y (c j) e := by
    intro i j; rw [← D, inner_sub_left, real_inner_comm u (x (c i)),
      real_inner_comm u (x (c j))]
  have hS := lemmaS (x (c 0)) (x (c 2)) (x (c 1)) (x (c 3)) u 0 s t hs hs1 ht ht1 hX
    (by simp only [add_zero]; linarith [key 1 0]) (by simp only [add_zero]; linarith [key 3 0])
  simp only [add_zero] at hS
  have hn : ⟪x (c 0) - x (c 1), u⟫ < 0 := by rw [D]; exact sub_neg.2 h01
  have e1 : ⟪x (c 2) - x (c 1), u⟫ = (∑ e, y (c 2) e) - ∑ e, y (c 1) e := D _ _
  have e3 : ⟪x (c 2) - x (c 3), u⟫ = (∑ e, y (c 2) e) - ∑ e, y (c 3) e := D _ _
  have k1 := key 2 1; have k3 := key 2 3; have k13 := key 1 3
  rcases le_total (⟪u, x (c 1)⟫) (⟪u, x (c 3)⟫) with h | h
  · refine isRupert_of_q4_lex F hx hc hcyc hu d ⟨(0, 1), by decide, hn⟩
      ⟨(2, 1), by decide, ?_, ?_⟩
    · rw [e1]; rw [min_eq_left h] at hS; linarith
    · intro h0; apply d1; rw [e1] at h0; linarith
  · refine isRupert_of_q4_lex F hx hc hcyc hu d ⟨(0, 1), by decide, hn⟩
      ⟨(2, 3), by decide, ?_, ?_⟩
    · rw [e3]; rw [min_eq_right h] at hS; linarith
    · intro h0; apply d3; rw [e3] at h0; linarith

/-- **5/6-rims (and any `k ≥ 4`): robust unimodality along a ray.**  `u` in the open cell and
a direction `d` such that the rim depths at `u + ε d` are `RobUni` for all small `ε > 0`
(ties at `u` broken by `d`): Rupert. -/
theorem isRupert_of_closedCell_ray {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u)
    (d : ℝ³) (hR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), RobUni (fun i => ⟪x (c i), u + ε • d⟫)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨ε, ⟨h1, h2⟩, _⟩ := ((eventually_cellAt_add hu d).and hR |>.and
    self_mem_nhdsWithin).exists
  exact isRupert_of_closedCell hk F hx hc hcyc hu h1.cellLe h2

end Minimality.H21
