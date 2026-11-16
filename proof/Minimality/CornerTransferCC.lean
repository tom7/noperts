module

public import Mathlib
public import Minimality.CornerTransfer
public import Minimality.RimCellClosed

/-!
# Closed-cell adapter: a closed-cell vertex leaf is a corner leaf at its own apex

Source: `notes/LIFT-TRANSFER-DESIGN.md`, build step 5.  Rim-exposing variants (additive: the old lemmas
`h21b_core_pos`, `s0x_sil_cell_lexUni`, `s0x_sil_cell_lex` are untouched) of the lex-cell constructions, and
the adapter `cornerLeaf_of_closedCell`.

* `h21b_core_pos_rim`, `s0x_sil_cell_lexUni_rim`, `s0x_sil_cell_lex_rim`: the lex cell is exposed with
  its rim `y`, every rim vertex being a vertex `x (c j)` of the cycle.
* `lexCell_of_closedCell`: closed cell + `RobUni` gives `u₀ ≠ 0` and a lex cell of `univ.image x` with such a rim.
* `cornerLeaf_of_closedCell`: if the cycle avoids the vertex `i₀` (`c i ≠ i₀`), this is a `CornerLeaf` of
  `(univ.erase i₀).image x` at the apex `x i₀`, ready for `cornerLeaf_lift`.
-/

@[expose] public section

set_option autoImplicit false

namespace Minimality.H21

open Finset
open scoped RealInnerProductSpace

variable {n m k : ℕ} [NeZero k] {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ v : ℝ³}

/-- Rim-exposing `h21b_core_pos`: the lex cell has rim `x ∘ c`. -/
theorem h21b_core_pos_rim (hc : Function.Injective c) (hk : 3 ≤ k) (D : h21b_SilDataL k x c u₀ v)
    (μ : ZMod k → ℝ) (hμ : ∀ i, 0 < μ i)
    (hd : ∀ i, x (c (i + 1)) - x (c i) = μ i • cross (D.A i) (D.B i))
    (hL : LexUni (fun i => ⟪x (c i), u₀⟫) (fun i => ⟪x (c i), v⟫)) :
    ∃ v' : ℝ³, LexCell (univ.image x) u₀ v' (fun i => x (c i)) := by
  have P : ∀ i m, m ≠ c i → m ≠ c (i + 1) →
      TiltSign (x (c (i + 1)) - x (c i)) (x m - x (c i)) u₀ v := by
    intro i m h0 h1
    have Q := h21b_Q_pos D i m h0 h1
    unfold TiltSign
    rw [h21b_det_eq D i (μ i) (hd i) m u₀, h21b_det_eq D i (μ i) (hd i) m v]
    unfold h21b_LP at Q
    rcases Q with Q | ⟨Q, Q'⟩
    · exact Or.inl (mul_pos (hμ i) Q)
    · right; rw [Q]; exact ⟨by ring, mul_pos (hμ i) Q'⟩
  refine ⟨v, hk, fun i => mem_image_of_mem _ (mem_univ _), ?_, ?_, hL⟩
  · intro i j hji hj1
    exact P i (c j) (fun h => hji (hc h)) (fun h => hj1 (hc h))
  · intro y hy hne i
    obtain ⟨m, -, rfl⟩ := mem_image.1 hy
    exact P i m (fun h => hne i (by rw [h])) (fun h => hne (i + 1) (by rw [h]))

/-- Rim-exposing `s0x_sil_cell_lexUni`: the rim is `x ∘ c` or its reverse `x ∘ c ∘ neg`. -/
theorem s0x_sil_cell_lexUni_rim (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : h21b_SilDataL k x c u₀ v)
    (hL : LexUni (fun i => ⟪x (c i), u₀⟫) (fun i => ⟪x (c i), v⟫)) :
    ∃ (v' : ℝ³) (y : ZMod k → ℝ³), (∀ i, ∃ j, y i = x (c j)) ∧ LexCell (univ.image x) u₀ v' y := by
  choose μ hμ0 hd using h21b_exists_mu hk hx hc D
  rcases h21b_sign_agree hk hx hc D μ hμ0 hd with hp | hn
  · obtain ⟨v', h⟩ := h21b_core_pos_rim hc hk D μ hp hd hL
    exact ⟨v', _, fun i => ⟨i, rfl⟩, h⟩
  · have hd' : ∀ i, x (c (-(i + 1))) - x (c (-i)) =
        (-μ (-i - 1)) • cross (D.rev.A i) (D.rev.B i) := by
      intro i
      have := hd (-i - 1)
      rw [sub_add_cancel] at this
      show x (c (-(i + 1))) - x (c (-i)) = (-μ (-i - 1)) • cross (D.A (-i - 1)) (D.B (-i - 1))
      rw [show -(i + 1) = -i - 1 by ring, neg_smul, ← this]
      abel
    obtain ⟨v', h⟩ := h21b_core_pos_rim (c := fun i => c (-i)) (fun i j h => neg_injective (hc h)) hk
      D.rev (fun i => - μ (-i - 1)) (fun i => by linarith [hn (-i - 1)]) hd' (Type08Sp.lexUni_neg hL)
    exact ⟨v', _, fun i => ⟨-i, rfl⟩, h⟩

/-- Rim-exposing `s0x_sil_cell_lex`. -/
theorem s0x_sil_cell_lex_rim (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : h21b_SilDataL k x c u₀ v) (hU : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    ∃ (v' : ℝ³) (y : ZMod k → ℝ³), (∀ i, ∃ j, y i = x (c j)) ∧ LexCell (univ.image x) u₀ v' y := by
  obtain ⟨v', ⟨D'⟩, hv⟩ := s0x_sep_tilt hx hc D
  exact s0x_sil_cell_lexUni_rim hk hx hc D'
    (s0x_lexUni_of_robUni hk hU _ fun i j _ h => by_contra fun hij => hv i j hij h)

/-- **Closed cell as a lex cell with exposed rim.**  Same hypotheses as `isRupert_of_closedCell`. -/
theorem lexCell_of_closedCell (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    u₀ ≠ 0 ∧ ∃ (v' : ℝ³) (y : ZMod k → ℝ³), (∀ i, ∃ j, y i = x (c j)) ∧
      LexCell (univ.image x) u₀ v' y := by
  obtain ⟨D⟩ := silL_of_cell F hcyc hu ha
  refine ⟨?_, s0x_sil_cell_lex_rim (by omega) hx hc D hR⟩
  intro h0
  rw [h0] at hR
  exact not_robUni_const hk 0 (by simpa using hR)

/-- **Closed-cell corner leaf.**  If the cycle avoids the vertex `i₀` (this is what the leaf must record),
the closed-cell leaf is a `CornerLeaf` of `O = x '' (univ \ {i₀})` at the apex `x i₀`. -/
theorem cornerLeaf_of_closedCell (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) (i₀ : Fin n)
    (hci : ∀ i, c i ≠ i₀) (z : Fin 3 → ℝ³) :
    Minimality.CornerEQ.CornerLeaf ((univ.erase i₀).image x) z (x i₀) := by
  obtain ⟨hu0, v', y, hy, hlex⟩ := lexCell_of_closedCell hk F hx hc hcyc ha hu hR
  left
  have hI : insert (x i₀) ((univ.erase i₀).image x) = univ.image x := by
    ext w
    simp only [mem_insert, mem_image, mem_erase, mem_univ, and_true]
    constructor
    · rintro (rfl | ⟨j, -, rfl⟩)
      · exact ⟨i₀, trivial, rfl⟩
      · exact ⟨j, trivial, rfl⟩
    · rintro ⟨j, -, rfl⟩
      by_cases h : j = i₀
      · exact Or.inl (by rw [h])
      · exact Or.inr ⟨j, h, rfl⟩
  refine ⟨u₀, v', k, inferInstance, y, hu0, fun i => ?_, fun i => ?_, by rw [hI]; exact hlex⟩
  · obtain ⟨j, hj⟩ := hy i
    rw [hj]
    exact mem_image.2 ⟨c j, mem_erase.2 ⟨hci j, mem_univ _⟩, rfl⟩
  · obtain ⟨j, hj⟩ := hy i
    rw [hj]
    exact fun h => hci j (hx h)

end Minimality.H21
