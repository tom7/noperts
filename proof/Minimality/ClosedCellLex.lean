module

public import Minimality.RimCellClosed
public import Minimality.GenericLeaves

@[expose] public section

/-!
# Lemma Q4 on a closed cell gives a lex cell (job OSPEC2, nopert229 notes/OPENSPECIAL-STRATEGY.md)

`H21.isRupert_of_closedCell_q4` (RimCellClosed.lean) finds a view in the OPEN cell where the 4-rim is robustly
unimodal and concludes `IsRupert` through `isRupert_of_closedCell`.  That view is itself a lex cell (`d1 = d2 = 0`),
so the same hypotheses give `Gen.LexAny F`.  Consequence: every leaf built on `isRupert_of_closedCell_q4` (the Q45
corner cells `q45_B1_cell` .. `q45_C2_cell`, BandTwo, Cell0234, OrthoView2, ...) is excluded by `¬ LexAny`, i.e. by
`HoleLeaf`.

`exists_mixed_cellAt` is the mixed-view step of `isRupert_of_closedCell_q4` (copied; dedup candidate: that proof
could call this lemma).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

open Minimality.RimCell in
/-- The mixed-view step of Lemma Q4 on a closed cell: some view of the open cell has a negative and a positive
diagonal form. -/
theorem exists_mixed_cellAt (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a g g' : ℝ³} (ha : CellAt F U Dn a)
    (hg : CellLe F U Dn g) (hg' : CellLe F U Dn g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g'⟫) :
    ∃ u, CellAt F U Dn u ∧ (∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), u⟫ < 0) ∧
      ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), u⟫ := by
  set A : Set ℝ³ := {u | CellAt F U Dn u} with hA
  let f : {p // p ∈ diagPairs} → ℝ³ →ₗ[ℝ] ℝ := fun p =>
    (innerSL ℝ (x (c p.1.1) - x (c p.1.2))).toLinearMap
  have hf : ∀ p u, f p u = ⟪x (c p.1.1) - x (c p.1.2), u⟫ := fun p u => rfl
  have hfc : ∀ p, Continuous (f p) := fun p => (innerSL ℝ _).continuous
  have hAc : Convex ℝ A := by
    intro u hu v hv s t hs ht hst
    have e : ∀ N : ℝ³, ⟪N, s • u + t • v⟫ = s * ⟪N, u⟫ + t * ⟪N, v⟫ := by
      intro N; rw [inner_add_right, inner_smul_right, inner_smul_right]
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [e]
      have := hu.1 r hr; have := hv.1 r hr
      rcases hs.lt_or_eq with h | h
      · nlinarith
      · subst h; simp at hst; subst hst; simpa
    · rw [e]
      have := hu.2 r hr; have := hv.2 r hr
      rcases hs.lt_or_eq with h | h
      · nlinarith
      · subst h; simp at hst; subst hst; simpa
  have hmix : ∃ u ∈ A, (∃ p, f p u < 0) ∧ ∃ p, 0 < f p u := by
    by_contra H
    have hz : ∀ u ∈ A, ∃ p, f p u ≠ 0 := by
      intro u hu
      by_contra hall
      push Not at hall
      set P := x (c 0) - x (c 1)
      set Q := x (c 2) - x (c 1)
      set d : ℝ³ := cross Q u - cross u P with hd
      have hD := det_ne_zero_of_cellAt (by norm_num) F hx hc hcyc hu
      have ePd : ⟪P, d⟫ = ⟪P, cross Q u⟫ := by
        simp only [hd, inner3, cross_apply_zero, cross_apply_one, cross_apply_two,
          PiLp.sub_apply]; ring
      have eQd : ⟪Q, d⟫ = -⟪P, cross Q u⟫ := by
        simp only [hd, inner3, cross_apply_zero, cross_apply_one, cross_apply_two,
          PiLp.sub_apply]; ring
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (u + ε • d) := by
        have e : ∀ t ε, ⟪F.N t, u + ε • d⟫ = ⟪F.N t, u⟫ + ε * ⟪F.N t, d⟫ := by
          intro t ε; rw [inner_add_right, inner_smul_right]
        refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
          (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
        · exact (eventually_pos_affine (Or.inl (hu.1 t ht))).mono fun ε hε => by rw [e]; exact hε
        · exact (eventually_pos_affine (B := -⟪F.N t, d⟫) (Or.inl (neg_pos.2 (hu.2 t ht)))).mono
            fun ε hε => by rw [e]; linarith
      obtain ⟨ε, hεA, hε⟩ := (hev.and self_mem_nhdsWithin).exists
      have hε0 : (0 : ℝ) < ε := hε
      have p01 : ((0 : ZMod 4), (1 : ZMod 4)) ∈ diagPairs := by decide
      have p21 : ((2 : ZMod 4), (1 : ZMod 4)) ∈ diagPairs := by decide
      have v01 : f ⟨_, p01⟩ (u + ε • d) = ε * ⟪P, cross Q u⟫ := by
        rw [map_add, map_smul, hall, hf, smul_eq_mul, zero_add]
        simp only; rw [ePd]
      have v21 : f ⟨_, p21⟩ (u + ε • d) = -(ε * ⟪P, cross Q u⟫) := by
        rw [map_add, map_smul, hall, hf, smul_eq_mul, zero_add]
        simp only; rw [eQd]; ring
      apply H
      refine ⟨u + ε • d, hεA, ?_⟩
      rcases lt_or_gt_of_ne hD with h | h
      · exact ⟨⟨_, by rw [v01]; nlinarith⟩, ⟨_, by rw [v21]; nlinarith⟩⟩
      · exact ⟨⟨_, by rw [v21]; nlinarith⟩, ⟨_, by rw [v01]; nlinarith⟩⟩
    obtain ⟨pn, hpn, hpnv⟩ := hn
    obtain ⟨pp, hpp, hppv⟩ := hp
    exact H (exists_mixed_sign_of_closure f hfc hAc hz (mem_closure_cell ha hg)
      (mem_closure_cell ha hg') ⟨⟨pn, hpn⟩, hpnv⟩ ⟨⟨pp, hpp⟩, hppv⟩)
  obtain ⟨u, hu, ⟨pn, hpn⟩, ⟨pp, hpp⟩⟩ := hmix
  exact ⟨u, hu, ⟨pn.1, pn.2, hpn⟩, ⟨pp.1, pp.2, hpp⟩⟩

/-- **A strict cell view with a robustly unimodal rim is a lex cell** (`d1 = d2 = 0`). -/
theorem lexAny_of_cellAt_robUni {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    {c : ZMod k → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u)
    (hR : RobUni (fun i => ⟪x (c i), u⟫)) : Gen.LexAny F := by
  refine ⟨k, inferInstance, c, U, Dn, u, 0, 0, hk, hc, hcyc, fun t ht => Or.inl (hu.1 t ht),
    fun t ht => Or.inl (neg_pos.2 (hu.2 t ht)), ?_⟩
  simp only [inner_zero_right]
  intro B b c' d hb hbc hcd hd
  have := hR B b c' d hb hbc hcd hd
  simp only [LexCell.LexLt3, LexCell.LexPos3, sub_pos]
  by_contra hn
  simp only [not_or] at hn
  exact this ⟨not_lt.mp hn.1.1, not_lt.mp hn.2.1.1, not_lt.mp hn.2.2.1.1, not_lt.mp hn.2.2.2.1⟩

open Minimality.RimCell in
/-- **Lemma Q4 on a closed cell, lex form**: the hypotheses of `isRupert_of_closedCell_q4` give `Gen.LexAny F`. -/
theorem lexAny_of_closedCell_q4 (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a g g' : ℝ³} (ha : CellAt F U Dn a)
    (hg : CellLe F U Dn g) (hg' : CellLe F U Dn g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g'⟫) : Gen.LexAny F := by
  obtain ⟨u, hu, ⟨pn, hpn, hpnv⟩, ⟨pp, hpp, hppv⟩⟩ := exists_mixed_cellAt F hx hc hcyc ha hg hg' hn hp
  refine lexAny_of_cellAt_robUni le_rfl F hc hcyc hu (robUni_four_of_mixed ?_ ?_)
  · exact ⟨pn, hpn, by rw [← inner_sub_left]; exact hpnv⟩
  · exact ⟨pp, hpp, by rw [← inner_sub_left]; exact hppv⟩

end Minimality.H21
