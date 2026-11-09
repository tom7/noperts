module

public import SeptopertShell.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# Watertightness

A set `W` of parameters *separates* `a` from `b` if every continuous path from `a` to `b` meets `W`. The
criterion used for the Septopert shell: if `a ∈ D`, `b ∉ D` and the frontier of `D` lies in `W`, then `W`
separates `a` from `b` (a path is connected, so it cannot leave `D` without meeting its frontier).
-/

@[expose] public section

namespace SeptopertShell

open Set

/-- Every continuous path from `a` to `b` meets `W`. -/
def Separates (W : Set ℝ³) (a b : ℝ³) : Prop := ∀ γ : Path a b, ∃ t, γ t ∈ W

/-- A preconnected set that meets both `D` and its complement meets the frontier of `D`. -/
theorem IsPreconnected.inter_frontier_nonempty' {X : Type*} [TopologicalSpace X] {S D : Set X}
    (hS : IsPreconnected S) (h1 : (S ∩ D).Nonempty) (h2 : (S \ D).Nonempty) :
    (S ∩ frontier D).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  -- S lies in the union of the disjoint open sets `interior D` and `(closure D)ᶜ`
  have hcover : S ⊆ interior D ∪ (closure D)ᶜ := by
    intro x hx
    by_cases hc : x ∈ closure D
    · left
      by_contra hi
      have : x ∈ S ∩ frontier D := ⟨hx, hc, hi⟩
      rw [hne] at this; exact this
    · right; exact hc
  obtain ⟨x, hxS, hxD⟩ := h1
  obtain ⟨y, hyS, hyD⟩ := h2
  have hx : (S ∩ interior D).Nonempty := by
    refine ⟨x, hxS, ?_⟩
    rcases hcover hxS with h | h
    · exact h
    · exact absurd (subset_closure hxD) h
  have hy : (S ∩ (closure D)ᶜ).Nonempty := by
    refine ⟨y, hyS, ?_⟩
    rcases hcover hyS with h | h
    · exact absurd (interior_subset h) hyD
    · exact h
  obtain ⟨z, hzS, hz1, hz2⟩ := hS _ _ isOpen_interior isClosed_closure.isOpen_compl hcover hx hy
  exact hz2 (subset_closure (interior_subset hz1))

/-- **The criterion.** If `a ∈ D`, `b ∉ D` and `frontier D ⊆ W`, every path from `a` to `b` meets `W`. -/
theorem separates_of_frontier_subset {W D : Set ℝ³} {a b : ℝ³} (ha : a ∈ D) (hb : b ∉ D)
    (hW : frontier D ⊆ W) : Separates W a b := by
  intro γ
  have hS : IsPreconnected (range γ) := (isConnected_range γ.continuous).isPreconnected
  obtain ⟨_, ⟨t, rfl⟩, hf⟩ := IsPreconnected.inter_frontier_nonempty' hS ⟨a, ⟨0, γ.source⟩, ha⟩
    ⟨b, ⟨1, γ.target⟩, hb⟩
  exact ⟨t, hW hf⟩

end SeptopertShell

end
