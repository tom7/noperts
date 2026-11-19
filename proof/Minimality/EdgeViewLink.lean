module

public import Minimality.RimCellClosed
public import Minimality.Type24SAT.Facets24

@[expose] public section

/-!
# Edge views with an end hidden: the link rim (Lemma E23 of the type 24 band residue)

General part: a closed-cell leaf (`isRupert_of_closedCell`) on a 5-rim whose depths at `u₀` have one
valley and one peak: rim positions `0..4`, `z 0` the minimum, `z 0 < z 1`, `z 0 < z 4 < z 3 < z 2`,
and the tie `z 1 = z 2` excluded (the peak is `2` or `1`).

Type 24 corollary `isRupert_edgeView23`: view `u₀ = x 3 - x 2`, rim `1 6 3 5 0` (the link of vertex 2),
facets up `B D E I`, down `A C F G H`.  Facings of `A C D F I` are automatic from the facet data; `G`, `H` are
edge-on at `u₀` and are tilted back by `d = (x 6 - x 2) + (x 5 - x 2)`; `B` (016) is the hypothesis (F), `E` (046)
the connectivity hypothesis.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset Filter Topology

namespace Minimality.EdgeViewLink
open Minimality Minimality.H21 Minimality.T24.SAT

/-- A robustly unimodal 5-cycle: `z 0 < z 1`, `z 0 < z 4 < z 3 < z 2`, `z 1 ≠ z 2`. -/
theorem ev_robUni5 (z : ZMod 5 → ℝ) (h01 : z 0 < z 1) (h04 : z 0 < z 4) (h43 : z 4 < z 3)
    (h32 : z 3 < z 2) (hne : z 1 ≠ z 2) : RobUni z := by
  have tab : ((0 : ZMod 5) + 1 = 1) ∧
      ((0 : ZMod 5) + 2 = 2) ∧
      ((0 : ZMod 5) + 3 = 3) ∧
      ((0 : ZMod 5) + 4 = 4) ∧
      ((1 : ZMod 5) + 1 = 2) ∧
      ((1 : ZMod 5) + 2 = 3) ∧
      ((1 : ZMod 5) + 3 = 4) ∧
      ((1 : ZMod 5) + 4 = 0) ∧
      ((2 : ZMod 5) + 1 = 3) ∧
      ((2 : ZMod 5) + 2 = 4) ∧
      ((2 : ZMod 5) + 3 = 0) ∧
      ((2 : ZMod 5) + 4 = 1) ∧
      ((3 : ZMod 5) + 1 = 4) ∧
      ((3 : ZMod 5) + 2 = 0) ∧
      ((3 : ZMod 5) + 3 = 1) ∧
      ((3 : ZMod 5) + 4 = 2) ∧
      ((4 : ZMod 5) + 1 = 0) ∧
      ((4 : ZMod 5) + 2 = 1) ∧
      ((4 : ZMod 5) + 3 = 2) ∧
      ((4 : ZMod 5) + 4 = 3) := by decide
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44⟩ := tab
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨ (b = 1 ∧ c = 3 ∧ d = 4) ∨
      (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rintro ⟨h1, h2, h3, h4⟩
  rcases lt_or_gt_of_ne hne with h12 | h12 <;>
  rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44] at h1 h2 h3 h4 <;>
  linarith

section General
variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- General edge-view leaf on a 5-rim `c` with one valley (position 0) and one peak. -/
theorem isRupert_edgeViewLink (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 5 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a u₀ : ℝ³} (ha : CellAt F U Dn a) (hu : CellLe F U Dn u₀)
    (h01 : ⟪x (c 0), u₀⟫ < ⟪x (c 1), u₀⟫) (h04 : ⟪x (c 0), u₀⟫ < ⟪x (c 4), u₀⟫)
    (h43 : ⟪x (c 4), u₀⟫ < ⟪x (c 3), u₀⟫) (h32 : ⟪x (c 3), u₀⟫ < ⟪x (c 2), u₀⟫)
    (hne : ⟪x (c 1), u₀⟫ ≠ ⟪x (c 2), u₀⟫) : IsRupert (univ.image x) :=
  isRupert_of_closedCell (by norm_num) F hx hc hcyc ha hu (ev_robUni5 _ h01 h04 h43 h32 hne)

/-- Tilt: from weak facings at `u₀`, with each zero one strictly signed along `d`, a strict point. -/
theorem ev_cellAt_of_tilt (F : S0xFac m S x) {U Dn : Finset (Fin m)} {u₀ d : ℝ³}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, u₀⟫ ∨ (⟪F.N t, u₀⟫ = 0 ∧ 0 < ⟪F.N t, d⟫))
    (hD : ∀ t ∈ Dn, ⟪F.N t, u₀⟫ < 0 ∨ (⟪F.N t, u₀⟫ = 0 ∧ ⟪F.N t, d⟫ < 0)) :
    ∃ a, CellAt F U Dn a ∧ CellLe F U Dn u₀ := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ t ∈ U, 0 < ⟪F.N t, u₀ + ε • d⟫) ∧
      ∀ t ∈ Dn, ⟪F.N t, u₀ + ε • d⟫ < 0 := by
    refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
      (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
    · rcases hU t ht with h | ⟨h0, h1⟩
      · have hc : Continuous fun ε : ℝ => ⟪F.N t, u₀ + ε • d⟫ := by fun_prop
        have := hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using h))
        exact nhdsWithin_le_nhds this
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [inner_add_right, inner_smul_right, h0, zero_add]
        exact mul_pos hε h1
    · rcases hD t ht with h | ⟨h0, h1⟩
      · have hc : Continuous fun ε : ℝ => ⟪F.N t, u₀ + ε • d⟫ := by fun_prop
        have := hc.continuousAt (x := 0) |>.eventually (gt_mem_nhds (by simpa using h))
        exact nhdsWithin_le_nhds this
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [inner_add_right, inner_smul_right, h0, zero_add]
        exact mul_neg_of_pos_of_neg hε h1
  obtain ⟨ε, hε⟩ := hev.exists
  refine ⟨u₀ + ε • d, hε, fun t ht => ?_, fun t ht => ?_⟩
  · rcases hU t ht with h | ⟨h0, _⟩
    exacts [h.le, h0.ge]
  · rcases hD t ht with h | ⟨h0, _⟩
    exacts [h.le, h0.le]

end General

variable {x : Fin 7 → ℝ³}

/-- Rim `1 6 3 5 0`: the link of vertex 2 of type 24. Up facets `B D E I`, down `A C F G H`. -/
def cLink : ZMod 5 → Fin 7 := ![1, 6, 3, 5, 0]
def ULink : Finset (Fin 9) := {1, 3, 4, 8}
def DLink : Finset (Fin 9) := {0, 2, 5, 6, 7}

theorem cyc_cLink : S0xCycUD s0x_S24 cLink ULink DLink := by decide
theorem inj_cLink : Function.Injective cLink := by decide

/-- Distinct vertices are separated by a facet, so a type 24 solid has injective `x`. -/
theorem inj_of_fac24 (F : S0xFac 9 s0x_S24 x) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have key : ∀ i j : Fin 7, i ≠ j → ∃ t, (i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t) ∨
      (j ∈ s0x_S24 t ∧ i ∉ s0x_S24 t) := by decide
  obtain ⟨t, h | h⟩ := key i j hne
  · have := F.neg t j h.2
    rw [← hij, F.zero t i h.1] at this
    exact lt_irrefl _ this
  · have := F.neg t i h.2
    rw [hij, F.zero t j h.1] at this
    exact lt_irrefl _ this

/-- **Lemma E23** (edge view `x 3 - x 2`, vertex 2 hidden behind 3, rim = link of 2). Hypotheses:
`hB` the face `016` is front (`(F)`), `hE` the face `046` is front (connectivity), and the depths
`⟪x 1,u⟫ < ⟪x 0,u⟫ < ⟪x 5,u⟫ < ⟪x 3,u⟫`, `⟪x 1,u⟫ < ⟪x 6,u⟫`, `⟪x 6,u⟫ ≠ ⟪x 3,u⟫`, `u = x 3 - x 2`.
The edge-on faces `235`, `236` are tilted back by `d = (x 6 - x 2) + (x 5 - x 2)` (Lemma EV-Tilt,
`EdgeTiltBD`); the earlier hypothesis that their normals are not parallel is not needed. -/
theorem isRupert_edgeView23 (F : S0xFac 9 s0x_S24 x)
    (hB : 0 < ⟪F.N 1, x 3 - x 2⟫) (hE : 0 < ⟪F.N 4, x 3 - x 2⟫)
    (h10 : ⟪x 1, x 3 - x 2⟫ < ⟪x 0, x 3 - x 2⟫) (h05 : ⟪x 0, x 3 - x 2⟫ < ⟪x 5, x 3 - x 2⟫)
    (h53 : ⟪x 5, x 3 - x 2⟫ < ⟪x 3, x 3 - x 2⟫) (h16 : ⟪x 1, x 3 - x 2⟫ < ⟪x 6, x 3 - x 2⟫)
    (h63 : ⟪x 6, x 3 - x 2⟫ ≠ ⟪x 3, x 3 - x 2⟫) : IsRupert (univ.image x) := by
  set u : ℝ³ := x 3 - x 2 with hu
  have hf : ∀ t, ⟪F.N t, u⟫ = F.f t (x 3) - F.f t (x 2) := fun t => by
    rw [hu, F.hN, inner_sub_right]
  have s3 : ∀ t, (3 : Fin 7) ∈ s0x_S24 t → F.f t (x 3) = 0 := fun t h => F.zero t 3 h
  have s2 : ∀ t, (2 : Fin 7) ∈ s0x_S24 t → F.f t (x 2) = 0 := fun t h => F.zero t 2 h
  have n3 : ∀ t, (3 : Fin 7) ∉ s0x_S24 t → F.f t (x 3) < 0 := fun t h => F.neg t 3 h
  have n2 : ∀ t, (2 : Fin 7) ∉ s0x_S24 t → F.f t (x 2) < 0 := fun t h => F.neg t 2 h
  -- tilt direction (Lemma EV-Tilt): `6 ∉ 235`, `5 ∉ 236`
  set d : ℝ³ := (x 6 - x 2) + (x 5 - x 2) with hd
  have dG : ⟪F.N 6, d⟫ < 0 := by
    rw [hd, inner_add_right, F.inner_sub, F.inner_sub, s2 6 (by decide), F.zero 6 5 (by decide)]
    have := F.neg 6 6 (by decide); linarith
  have dH : ⟪F.N 7, d⟫ < 0 := by
    rw [hd, inner_add_right, F.inner_sub, F.inner_sub, s2 7 (by decide), F.zero 7 6 (by decide)]
    have := F.neg 7 5 (by decide); linarith
  have hG0 : ⟪F.N 6, u⟫ = 0 := by rw [hf, s3 6 (by decide), s2 6 (by decide)]; ring
  have hH0 : ⟪F.N 7, u⟫ = 0 := by rw [hf, s3 7 (by decide), s2 7 (by decide)]; ring
  obtain ⟨a, ha, hu'⟩ := ev_cellAt_of_tilt F (U := ULink) (Dn := DLink) (u₀ := u) (d := d)
    (fun t ht => by
      simp only [ULink, Finset.mem_insert, Finset.mem_singleton] at ht
      left
      rcases ht with rfl | rfl | rfl | rfl
      · exact hB
      · rw [hf, s3 3 (by decide)]; have := n2 3 (by decide); linarith
      · exact hE
      · rw [hf, s3 8 (by decide)]; have := n2 8 (by decide); linarith)
    (fun t ht => by
      simp only [DLink, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · left; rw [hf, s2 0 (by decide)]; have := n3 0 (by decide); linarith
      · left; rw [hf, s2 2 (by decide)]; have := n3 2 (by decide); linarith
      · left; rw [hf, s2 5 (by decide)]; have := n3 5 (by decide); linarith
      · right; exact ⟨hG0, dG⟩
      · right; exact ⟨hH0, dH⟩)
  exact isRupert_edgeViewLink F (inj_of_fac24 F) inj_cLink cyc_cLink ha hu'
    (by simpa [cLink] using h16) (by simpa [cLink] using h10) (by simpa [cLink] using h05)
    (by simpa [cLink] using h53) (by simpa [cLink] using h63)

end Minimality.EdgeViewLink
