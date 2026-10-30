module

public import Minimality.Type08S.P2TX3

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X4: `AngBig ↔ 1 < γ4` in the frame of `h3_setup`, and the choice of a good tilt.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **`AngBig ↔ 1 < γ4`** in the frame of `h3_setup` (only `ν ≠ 0`, `ha ≠ 0`, `v1 ≠ 0` are used):
`det3 (c - b') (a - d) (b - d) * det3 (a - d) (c - d) (b - d) = ν² ha² v1² (γ4 - 1)`. -/
theorem angBig_iff_gamma4 {a b b' c d o : ℝ³} (hF : Fr e1 e2 e3) {ν v1 C0 w1 ha w3 α4 γ4 : ℝ}
    (hν : ν ≠ 0) (hv1 : v1 ≠ 0) (hha : ha ≠ 0)
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν)
    (hc : c = pt e1 e2 e3 o 0 0 C0) (haa : a = pt e1 e2 e3 o (-v1 + w1) ha w3)
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0)) :
    AngBig a b b' c d ↔ 1 < γ4 := by
  have sub : ∀ X Y z X' Y' z' : ℝ, pt e1 e2 e3 o X Y z - pt e1 e2 e3 o X' Y' z' =
      pc e1 e2 e3 (X - X') (Y - Y') (z - z') := by
    intro X Y z X' Y' z'; simp only [pt, pc]; module
  have e1' : det3 (c - b') (a - d) (b - d) = ν * ha * v1 * (1 - γ4) := by
    rw [hc, hb', haa, hd, hb]; simp only [sub, det3_pc hF]; ring
  have e2' : det3 (a - d) (c - d) (b - d) = -(ν * ha * v1) := by
    rw [hc, haa, hd, hb]; simp only [sub, det3_pc hF]; ring
  unfold AngBig
  rw [e1', e2']
  have hp : 0 < (ν * ha * v1) ^ 2 := by positivity
  have : ν * ha * v1 * (1 - γ4) * -(ν * ha * v1) = (ν * ha * v1) ^ 2 * (γ4 - 1) := by ring
  rw [this]
  constructor
  · intro h; by_contra hc'; push Not at hc'
    nlinarith
  · intro h; exact mul_pos hp (by linarith)

/-- Avoiding finitely many affine zeros. -/
theorem exists_avoid (M : ℝ) (hM : 0 < M) (L : List (ℝ × ℝ)) (hL : ∀ P ∈ L, P.1 ≠ 0 ∨ P.2 ≠ 0) :
    ∃ u : ℝ, 0 < u ∧ u < M ∧ ∀ P ∈ L, P.1 + P.2 * u ≠ 0 := by
  obtain ⟨u, hu, huS⟩ := (Set.Ioo_infinite hM).exists_notMem_finset (L.map (fun P => -P.1 / P.2)).toFinset
  refine ⟨u, hu.1, hu.2, fun P hP e => huS ?_⟩
  simp only [List.mem_toFinset, List.mem_map]
  refine ⟨P, hP, ?_⟩
  rcases hL P hP with h | h
  · by_cases hB : P.2 = 0
    · rw [hB] at e; simp at e; exact absurd e h
    · field_simp; linarith
  · field_simp; linarith

/-- A tilt `t1 = (w1 - σ u)/ha` separates two distinct screen points for all but one `u`. -/
theorem tilt_pair {ha σ w1 x1 y1 x2 y2 : ℝ} (hha : ha ≠ 0) (hσ : σ * σ = 1)
    (hxy : x1 ≠ x2 ∨ y1 ≠ y2) :
    (w1 * (x1 - x2) / ha + (y1 - y2) ≠ 0 ∨ -σ * (x1 - x2) / ha ≠ 0) ∧
    ∀ u : ℝ, (w1 * (x1 - x2) / ha + (y1 - y2)) + (-σ * (x1 - x2) / ha) * u ≠ 0 →
      (w1 - σ * u) / ha * x1 + 1 * y1 ≠ (w1 - σ * u) / ha * x2 + 1 * y2 := by
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  refine ⟨?_, fun u h e => h ?_⟩
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hx : x1 - x2 = 0 := by
      have : -σ * (x1 - x2) = 0 := by
        rcases div_eq_zero_iff.1 h2 with h | h
        · exact h
        · exact absurd h hha
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (neg_eq_zero.1 h) hσ0
      · exact h
    rw [hx] at h1
    simp at h1
    rcases hxy with h | h
    · exact h (by linarith)
    · exact h (by linarith)
  · field_simp
    field_simp at e
    linarith

end Type08Sp
end Minimality
