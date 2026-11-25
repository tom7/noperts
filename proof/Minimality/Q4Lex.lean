module

public import Minimality.EdgeLeaf
public import Minimality.Q4Leaf

/-! Item 1 of GENREV24-HOLE: the Q4, edge-cone and closed-cell leaves all give `Gen.LexAny`.
`Q4Any` and `EdgeAny` therefore imply `LexAny`, so the negated conjuncts `¬ Q4Any`, `¬ EdgeAny` of `Hole24` are
redundant (they do not shrink the hole). -/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

@[expose] public section

namespace Minimality.GenRev
open Minimality Minimality.H21 Minimality.LexCell

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Item 1a: a closed-cell RobUni view is a `LexAny` witness (body of `isRupert_of_closedCell_via_lex`). -/
theorem lexAny_of_closedCell {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a u₀ : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    Gen.LexAny F := by
  refine ⟨k, inferInstance, c, U, Dn, u₀, a - u₀, 0, hk, hc, hcyc, ?_, ?_, ?_⟩
  · intro t ht
    rcases (hu.1 t ht).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.symm, Or.inl ?_⟩
      rw [inner_sub_right, ← h]; simpa using ha.1 t ht
  · intro t ht
    rcases (hu.2 t ht).lt_or_eq with h | h
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [h]; simp, Or.inl ?_⟩
      rw [inner_sub_right, h]; have := ha.2 t ht; simp; linarith
  · intro B b c d h1 h2 h3 h4
    have := hR B b c d h1 h2 h3 h4
    by_contra hn
    push Not at hn
    have key : ∀ p q : ℝ³, ¬ LexLt3 (⟪p, u₀⟫, ⟪p, a - u₀⟫, ⟪p, (0 : ℝ³)⟫)
        (⟪q, u₀⟫, ⟪q, a - u₀⟫, ⟪q, (0 : ℝ³)⟫) → ⟪q, u₀⟫ ≤ ⟪p, u₀⟫ := by
      intro p q h
      by_contra h'
      exact h (Or.inl (by simp only; linarith [not_le.1 h']))
    exact this ⟨key _ _ hn.1, key _ _ hn.2.1, key _ _ hn.2.2.1, key _ _ hn.2.2.2⟩

/-- Item 1b: `EdgeAny` is a `LexAny` witness (same proof as `edgeAny_isRupert`, last line changed). -/
theorem lexAny_of_edgeAny (F : S0xFac m S x) (h : GenPlus.EdgeAny F) : Gen.LexAny F := by
  rcases h with ⟨k, hk_ne, c, U, Dn, a, g, g', i, ε, hk, hc, hcyc, ha, hg, hg', hε, hov⟩
  obtain ⟨t, ht0, ht1, ht_pos⟩ := GenPlus.exists_pos_of_overlap
    (fun j : Fin (k - 2) => ⟪GenPlus.edgeVec x c i ε j, g⟫)
    (fun j : Fin (k - 2) => ⟪GenPlus.edgeVec x c i ε j, g'⟫) hov
  set u₀ := (1 - t) • g + t • g'
  have hu₀ : CellLe F U Dn u₀ := by
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · dsimp [u₀]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      exact add_nonneg (mul_nonneg (by linarith) (hg.1 s hs)) (mul_nonneg ht0 (hg'.1 s hs))
    · dsimp [u₀]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) (hg.2 s hs))
        (mul_nonpos_of_nonneg_of_nonpos ht0 (hg'.2 s hs))
  have h_form : ∀ j : Fin (k - 2), 0 < ⟪GenPlus.edgeVec x c i ε j, u₀⟫ := fun j => by
    have := ht_pos j
    dsimp [u₀]
    rwa [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hR : RobUni fun m => ⟪x (c m), u₀⟫ := by
    refine GenPlus.robUni_of_edgeCone hk i ε hε ?_ ?_
    · have hf0 := h_form ⟨0, by omega⟩
      dsimp [GenPlus.edgeVec] at hf0
      rwa [real_inner_smul_left, inner_sub_left] at hf0
    · intro j hj hjk
      have hf := h_form ⟨j - 2, by omega⟩
      have hne : j - 2 ≠ 0 := by omega
      dsimp [GenPlus.edgeVec] at hf
      simp only [hne, ↓reduceIte, real_inner_smul_left, inner_sub_left] at hf
      rw [show j - 2 + 3 = j + 1 by omega, show j - 2 + 2 = j by omega] at hf
      linarith
  exact lexAny_of_closedCell hk F hc hcyc ha hu₀ hR

open Minimality.RimCell in
/-- Item 1c: the Q4 witness is an open-cell RobUni view, hence a `LexAny` witness
(body of `isRupert_of_closedCell_q4`, last line changed). -/
theorem lexAny_of_q4Any (F : S0xFac m S x) (hx : Function.Injective x) (h : GenPlus.Q4Any F) :
    Gen.LexAny F := by
  rcases h with ⟨c, U, Dn, a, g, g', hc, hcyc, ha, hg, hg', hn, hp⟩
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
  -- a mixed cell view
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
      -- move along d inside the cell
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
  refine lexAny_of_closedCell le_rfl F hc hcyc hu hu.cellLe (robUni_four_of_mixed ?_ ?_)
  · exact ⟨pn.1, pn.2, by rw [← inner_sub_left]; exact hpn⟩
  · exact ⟨pp.1, pp.2, by rw [← inner_sub_left]; exact hpp⟩

end Minimality.GenRev
