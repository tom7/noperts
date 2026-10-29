module

public import Minimality.Generic.PV.PVRows
public import Minimality.Generic.PV.PVDefs

@[expose] public section


/-! Rows of the PV rim for a prismatoid pair `P` with ends `E` and hidden set `H`. -/

namespace Minimality
open scoped RealInnerProductSpace
open Finset

section
variable {V F₁ F₂ H : Finset ℝ³} {n₁ n₂ : ℝ³} {h₁ h₂ : ℝ}

theorem mem_V_cases (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) {y : ℝ³} (hy : y ∈ V) :
    y ∈ F₁ ∨ y ∈ F₂ ∨ y ∈ H := by
  have := P.union ▸ hy
  simp only [mem_union] at this
  tauto

theorem IsPrismPair.n₁_ne (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) : n₁ ≠ 0 := by
  intro h; apply P.d_ne; ext i; fin_cases i <;> simp [h, cross]

theorem IsPrismPair.n₂_ne (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) : n₂ ≠ 0 := by
  intro h; apply P.d_ne; ext i; fin_cases i <;> simp [h, cross]

theorem face1_lt {n₁ n₂ y A : ℝ³} {h₁ : ℝ} (hn : n₁ ≠ 0) (hy : ⟪n₁, y⟫ = h₁) (hA : ⟪n₁, A⟫ = h₁)
    (hlt : ⟪n₂, y⟫ < ⟪n₂, A⟫) : ⟪cross n₁ (cross n₁ n₂), A⟫ < ⟪cross n₁ (cross n₁ n₂), y⟫ := by
  have hu : ⟪n₁, y - A⟫ = 0 := by rw [inner_sub_right, hy, hA]; ring
  have := t1_rel n₁ n₂ (y - A) hu
  rw [inner_sub_right, inner_sub_right] at this
  have hp := real_inner_self_pos.mpr hn
  nlinarith

theorem face2_lt {n₁ n₂ y A : ℝ³} {h₂ : ℝ} (hn : n₂ ≠ 0) (hy : ⟪n₂, y⟫ = h₂) (hA : ⟪n₂, A⟫ = h₂)
    (hlt : ⟪n₁, A⟫ < ⟪n₁, y⟫) : ⟪cross n₂ (cross n₁ n₂), A⟫ < ⟪cross n₂ (cross n₁ n₂), y⟫ := by
  have hu : ⟪n₂, y - A⟫ = 0 := by rw [inner_sub_right, hy, hA]; ring
  have := t2_rel n₁ n₂ (y - A) hu
  rw [inner_sub_right, inner_sub_right] at this
  have hp := real_inner_self_pos.mpr hn
  nlinarith

theorem hidden_lt {n d e q : ℝ³} (hn : n ≠ 0) (hnd : ⟪n, d⟫ = 0) (hne : ⟪n, e⟫ = 0)
    (hpos : 0 < ⟪cross n d, e⟫) (hd : det3 e q d < 0) : ⟪n, q⟫ < 0 := by
  have g := det3_gram n e q d
  rw [hne, hnd] at g
  have h3 : det3 e n d = ⟪cross n d, e⟫ := by rw [det3_swap_ab, det3_nea]; ring
  rw [h3] at g
  have hp := real_inner_self_pos.mpr hn
  nlinarith

theorem IsPrismPair.A₁_ne_B₁ (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂) :
    E.A₁ ≠ E.B₁ := by
  intro h
  obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne (by have := P.card₁; omega : 1 < F₁.card) E.A₁
  have h1 := E.A₁_near y hy hne
  have h2 := E.B₁_far y hy (h ▸ hne)
  rw [← h] at h2
  linarith

theorem IsPrismPair.A₂_ne_B₂ (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂) :
    E.A₂ ≠ E.B₂ := by
  intro h
  obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne (by have := P.card₂; omega : 1 < F₂.card) E.A₂
  have h1 := E.A₂_near y hy hne
  have h2 := E.B₂_far y hy (h ▸ hne)
  rw [← h] at h2
  linarith

/-- Hidden points are strictly below both planes. -/
theorem hidden_planes (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂)
    {p : ℝ³} (hp : PVHidden E p) : ⟪n₁, p⟫ < h₁ ∧ ⟪n₂, p⟫ < h₂ := by
  obtain ⟨c1, -, c3, -⟩ := hp
  have hAB := P.A₁_ne_B₁ E
  have hAB2 := P.A₂_ne_B₂ E
  constructor
  · have hpos : 0 < ⟪cross n₁ (cross n₁ n₂), E.B₁ - E.A₁⟫ := by
      have := face1_lt (n₂ := n₂) P.n₁_ne (P.on₁ _ E.B₁_mem) (P.on₁ _ E.A₁_mem)
        (E.A₁_near _ E.B₁_mem hAB.symm)
      rw [inner_sub_right]; linarith
    have := hidden_lt (n := n₁) (d := cross n₁ n₂) (e := E.B₁ - E.A₁) (q := p - E.A₁) P.n₁_ne
      (inner_d1 _ _) (by rw [inner_sub_right, P.on₁ _ E.B₁_mem, P.on₁ _ E.A₁_mem]; ring) hpos c1
    rw [inner_sub_right, P.on₁ _ E.A₁_mem] at this
    linarith
  · have hpos : 0 < ⟪cross n₂ (cross n₁ n₂), E.A₂ - E.B₂⟫ := by
      have := face2_lt (n₁ := n₁) P.n₂_ne (P.on₂ _ E.A₂_mem) (P.on₂ _ E.B₂_mem)
        (E.B₂_far _ E.A₂_mem hAB2)
      rw [inner_sub_right]; linarith
    have := hidden_lt (n := n₂) (d := cross n₁ n₂) (e := E.A₂ - E.B₂) (q := p - E.B₂) P.n₂_ne
      (inner_d2 _ _) (by rw [inner_sub_right, P.on₂ _ E.A₂_mem, P.on₂ _ E.B₂_mem]; ring) hpos c3
    rw [inner_sub_right, P.on₂ _ E.B₂_mem] at this
    linarith

theorem V_plane₁ (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂)
    (hH : ∀ p ∈ H, PVHidden E p) {y : ℝ³} (hy : y ∈ V) : ⟪n₁, y⟫ < h₁ ∨ y ∈ F₁ := by
  rcases mem_V_cases P hy with h | h | h
  · exact Or.inr h
  · exact Or.inl (P.strict₁ y h)
  · exact Or.inl (hidden_planes P E (hH y h)).1

theorem V_plane₂ (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂)
    (hH : ∀ p ∈ H, PVHidden E p) {y : ℝ³} (hy : y ∈ V) : ⟪n₂, y⟫ < h₂ ∨ y ∈ F₂ := by
  rcases mem_V_cases P hy with h | h | h
  · exact Or.inl (P.strict₂ y h)
  · exact Or.inr h
  · exact Or.inl (hidden_planes P E (hH y h)).2

/-- **Chain-edge row** (both faces, both signs): `tiltSignS_edge` for the edge `cᵢ → cᵢ₊₁`. -/
theorem row_chain {s : ℝ} {n d v : ℝ³} {F : Finset ℝ³} {h : ℝ} {A B : ℝ³} {m : ℕ}
    {c : Fin m → ℝ³} (hn : n ≠ 0) (hd : 0 < ⟪d, d⟫) (hnd : ⟪n, d⟫ = 0)
    (hF : ∀ p ∈ F, ⟪n, p⟫ = h) (hc : IsFaceChain s n d F A B c) (hnv : ⟪n, v⟫ = s * ⟪d, d⟫)
    {i : ℕ} (hi : i + 1 < m) {y : ℝ³} (hy : ⟪n, y⟫ < h ∨ y ∈ F)
    (hy1 : y ≠ c ⟨i, by omega⟩) (hy2 : y ≠ c ⟨i + 1, hi⟩) :
    TiltSignS (-1) (c ⟨i + 1, hi⟩ - c ⟨i, by omega⟩) (y - c ⟨i, by omega⟩) d v := by
  have hle : ⟪n, y⟫ ≤ h := by
    rcases hy with h' | h'
    · exact h'.le
    · exact (hF y h').le
  refine tiltSignS_edge hn hnd (hF _ (hc.mem _)) (hF _ (hc.mem _)) hle ?_ ?_
  · rw [det3_nea, inner_sub_right]
    have := hc.mono ⟨i, by omega⟩ ⟨i + 1, hi⟩ (Fin.lt_def.mpr (by simp))
    linarith
  · intro heq
    have hyF : y ∈ F := by
      rcases hy with h' | h'
      · exact absurd heq h'.ne
      · exact h'
    have := hc.turn ⟨i, by omega⟩ hi y hyF hy1 hy2
    rw [hnv]
    nlinarith [mul_pos hd (neg_pos.mpr this)]

theorem row_bridge₁ (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂)
    (hH : ∀ p ∈ H, PVHidden E p) {y : ℝ³} (hy : y ∈ V) (h1 : y ≠ E.B₁) (h2 : y ≠ E.B₂) (v : ℝ³) :
    TiltSignS (-1) (E.B₂ - E.B₁) (y - E.B₁) (cross n₁ n₂) v := by
  left
  have hB1a := P.on₁ _ E.B₁_mem
  have hB2b := P.on₂ _ E.B₂_mem
  have hB2a := P.strict₁ _ E.B₂_mem
  have hB1b := P.strict₂ _ E.B₁_mem
  rcases mem_V_cases P hy with hF | hF | hHH
  · have ha := P.on₁ _ hF
    have hb := E.B₁_far _ hF h1
    rw [det3_pair]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm n₁, real_inner_comm n₂]
    rw [ha, hB1a, hB2b]
    nlinarith [mul_pos (sub_pos.mpr hB2a) (sub_pos.mpr hb)]
  · have hb := P.on₂ _ hF
    have ha := E.B₂_far _ hF h2
    rw [det3_pair]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm n₁, real_inner_comm n₂]
    rw [hb, hB1a, hB2b]
    nlinarith [mul_pos (sub_pos.mpr hB1b) (sub_pos.mpr ha)]
  · have := (hH y hHH).2.1
    linarith

theorem row_bridge₂ (P : IsPrismPair V F₁ F₂ H n₁ n₂ h₁ h₂) (E : PVEnds F₁ F₂ n₁ n₂ h₁ h₂)
    (hH : ∀ p ∈ H, PVHidden E p) {y : ℝ³} (hy : y ∈ V) (h1 : y ≠ E.A₂) (h2 : y ≠ E.A₁) (v : ℝ³) :
    TiltSignS (-1) (E.A₁ - E.A₂) (y - E.A₂) (cross n₁ n₂) v := by
  left
  have hA1a := P.on₁ _ E.A₁_mem
  have hA2b := P.on₂ _ E.A₂_mem
  have hA2a := P.strict₁ _ E.A₂_mem
  have hA1b := P.strict₂ _ E.A₁_mem
  rcases mem_V_cases P hy with hF | hF | hHH
  · have ha := P.on₁ _ hF
    have hb := E.A₁_near _ hF h2
    rw [det3_pair]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm n₁, real_inner_comm n₂]
    rw [ha, hA1a, hA2b]
    nlinarith [mul_pos (sub_pos.mpr hA2a) (sub_pos.mpr hb)]
  · have hb := P.on₂ _ hF
    have ha := E.A₂_near _ hF h1
    rw [det3_pair]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm n₁, real_inner_comm n₂]
    rw [hb, hA1a, hA2b]
    nlinarith [mul_pos (sub_pos.mpr hA1b) (sub_pos.mpr ha)]
  · have := (hH y hHH).2.2.2
    linarith

end
end Minimality
