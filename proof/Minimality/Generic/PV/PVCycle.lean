module

public import Minimality.Generic.PV.PVRim

@[expose] public section


/-! The cyclic concatenation of two sequences, indexed by `ZMod (m₁ + m₂)`. -/

namespace Minimality
open Finset

section
variable {α : Type*} [Zero α] {m₁ m₂ : ℕ}

/-- `c₁ 0 … c₁ (m₁-1) c₂ 0 … c₂ (m₂-1)` as a function on `ZMod (m₁+m₂)`. -/
noncomputable def xr [NeZero (m₁ + m₂)] (c₁ : Fin m₁ → α) (c₂ : Fin m₂ → α) (i : ZMod (m₁ + m₂)) : α :=
  if h : i.val < m₁ then c₁ ⟨i.val, h⟩ else if h2 : i.val - m₁ < m₂ then c₂ ⟨i.val - m₁, h2⟩ else 0

theorem xr_lt [NeZero (m₁ + m₂)] (c₁ : Fin m₁ → α) (c₂ : Fin m₂ → α) (i : ZMod (m₁ + m₂))
    (h : i.val < m₁) : xr c₁ c₂ i = c₁ ⟨i.val, h⟩ := by simp [xr, h]

theorem xr_ge [NeZero (m₁ + m₂)] (c₁ : Fin m₁ → α) (c₂ : Fin m₂ → α) (i : ZMod (m₁ + m₂))
    (h : m₁ ≤ i.val) (h2 : i.val - m₁ < m₂) : xr c₁ c₂ i = c₂ ⟨i.val - m₁, h2⟩ := by
  simp [xr, not_lt.mpr h, h2]

theorem zmod_succ_val {k : ℕ} [NeZero k] (hk : 2 ≤ k) (i : ZMod k) (h : i.val + 1 < k) :
    (i + 1).val = i.val + 1 := by
  haveI : Fact (1 < k) := ⟨by omega⟩
  rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; exact h), ZMod.val_one]

theorem zmod_succ_last {k : ℕ} [NeZero k] (i : ZMod k) (h : i.val + 1 = k) : i + 1 = 0 := by
  have : i = ((k - 1 : ℕ) : ZMod k) := by
    rw [← ZMod.natCast_zmod_val i]; congr 1; omega
  rw [this]
  have : ((k - 1 : ℕ) : ZMod k) + 1 = ((k : ℕ) : ZMod k) := by
    have hk : 1 ≤ k := NeZero.pos k
    have h' : ((k - 1 + 1 : ℕ) : ZMod k) = ((k : ℕ) : ZMod k) := by congr 1; omega
    push_cast at h'; exact h'
  rw [this, ZMod.natCast_self]

theorem rim_cases [NeZero (m₁ + m₂)] (hm₁ : 2 ≤ m₁) (hm₂ : 2 ≤ m₂)
    (c₁ : Fin m₁ → α) (c₂ : Fin m₂ → α) (i : ZMod (m₁ + m₂)) :
    (∃ (j : ℕ) (hj : j + 1 < m₁), xr c₁ c₂ i = c₁ ⟨j, by omega⟩ ∧ xr c₁ c₂ (i + 1) = c₁ ⟨j + 1, hj⟩) ∨
    (xr c₁ c₂ i = c₁ ⟨m₁ - 1, by omega⟩ ∧ xr c₁ c₂ (i + 1) = c₂ ⟨0, by omega⟩) ∨
    (∃ (j : ℕ) (hj : j + 1 < m₂), xr c₁ c₂ i = c₂ ⟨j, by omega⟩ ∧ xr c₁ c₂ (i + 1) = c₂ ⟨j + 1, hj⟩) ∨
    (xr c₁ c₂ i = c₂ ⟨m₂ - 1, by omega⟩ ∧ xr c₁ c₂ (i + 1) = c₁ ⟨0, by omega⟩) := by
  have hk : 2 ≤ m₁ + m₂ := by omega
  have hlt := ZMod.val_lt i
  by_cases h1 : i.val + 1 < m₁
  · left
    refine ⟨i.val, h1, xr_lt _ _ i (by omega), ?_⟩
    have := zmod_succ_val hk i (by omega)
    rw [xr_lt _ _ (i + 1) (by omega)]
    congr 1; exact Fin.ext this
  by_cases h2 : i.val + 1 = m₁
  · right; left
    have hv := zmod_succ_val hk i (by omega)
    refine ⟨?_, ?_⟩
    · rw [xr_lt _ _ i (by omega)]; congr 1; exact Fin.ext (by simp; omega)
    · rw [xr_ge _ _ (i + 1) (by omega) (by omega)]; congr 1; exact Fin.ext (by simp; omega)
  by_cases h3 : i.val + 1 < m₁ + m₂
  · right; right; left
    have hv := zmod_succ_val hk i h3
    refine ⟨i.val - m₁, by omega, ?_, ?_⟩
    · rw [xr_ge _ _ i (by omega) (by omega)]
    · rw [xr_ge _ _ (i + 1) (by omega) (by omega)]; congr 1; exact Fin.ext (by simp; omega)
  · right; right; right
    have h0 := zmod_succ_last i (by omega)
    refine ⟨?_, ?_⟩
    · rw [xr_ge _ _ i (by omega) (by omega)]; congr 1; exact Fin.ext (by simp; omega)
    · rw [h0, xr_lt _ _ 0 (by simp; omega)]; congr 1; exact Fin.ext (by simp)

theorem xr_inj [NeZero (m₁ + m₂)] (c₁ : Fin m₁ → α) (c₂ : Fin m₂ → α) (h1 : Function.Injective c₁)
    (h2 : Function.Injective c₂) (hd : ∀ a b, c₁ a ≠ c₂ b) : Function.Injective (xr c₁ c₂) := by
  intro i j hij
  apply ZMod.val_injective
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  by_cases a : i.val < m₁ <;> by_cases b : j.val < m₁
  · rw [xr_lt _ _ i a, xr_lt _ _ j b] at hij
    exact congrArg Fin.val (h1 hij)
  · rw [xr_lt _ _ i a, xr_ge _ _ j (by omega) (by omega)] at hij
    exact absurd hij (hd _ _)
  · rw [xr_ge _ _ i (by omega) (by omega), xr_lt _ _ j b] at hij
    exact absurd hij.symm (hd _ _)
  · rw [xr_ge _ _ i (by omega) (by omega), xr_ge _ _ j (by omega) (by omega)] at hij
    have := congrArg Fin.val (h2 hij)
    simp at this; omega

theorem ofFn_xr [NeZero (m₁ + m₂)] (c₁ : Fin m₁ → α) (c₂ : Fin m₂ → α) {β : Type*} (g : α → β) :
    List.ofFn (fun i : Fin (m₁ + m₂) => g (xr c₁ c₂ ((i : ℕ) : ZMod (m₁ + m₂)))) =
      List.ofFn (fun i : Fin m₁ => g (c₁ i)) ++ List.ofFn (fun i : Fin m₂ => g (c₂ i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    have hv : (((i : ℕ) : ZMod (m₁ + m₂))).val = i := ZMod.val_cast_of_lt (by simpa using h1)
    split_ifs with h
    · rw [xr_lt _ _ _ (by rw [hv]; exact h)]
      congr 2
      ext; simp [hv]
    · rw [xr_ge _ _ _ (by rw [hv]; omega) (by rw [hv]; simp at h1; omega)]
      congr 2
      ext; simp [hv]

theorem skel1_nodup {a e b : ℝ} (h : a ≠ b) : (skel1 a e b).Nodup := by
  unfold skel1
  split_ifs with hc
  · simp [h]
  · push Not at hc
    simp [h, hc.1, hc.2, Ne.symm hc.1, Ne.symm hc.2]

theorem skel1_mem {a e b x : ℝ} {L : List ℝ} (ha : a ∈ L) (he : e ∈ L) (hb : b ∈ L)
    (hx : x ∈ skel1 a e b) : x ∈ L := by
  unfold skel1 at hx
  split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl | rfl <;> assumption

end
end Minimality
