module

public import Minimality.Type08S.C2K5AB

@[expose] public section


/-!
# K5a / H: P0-Kb and P0-N2: `ParEndKb` / `ParEndN2` (with `κ_a = 0`) ⟹ `α4 = α1`, `γ4 = β1` and, in the frame of the
`ParEnd`, `Coll5 ∧ PersF` (CEf5 branch: `Coll5` from the vector identity `w ∥ e2`, `PersF` with `s = 1`;
Par5 branch: immediate).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The W0 coordinate data of `norm08w_coords` (as a proposition). -/
def P0Coords {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (α1 α4 β1 γ4 β6 γ6 : ℝ) : Prop :=
  det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + α1 • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      0 < α1 ∧ 0 < β1 ∧ 1 < α1 + β1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β6 ∧ 0 < γ6 ∧ 1 < β6 + γ6 ∧
      (W.F.abc'.f c < W.F.abc'.f a' → γ6 < 1) ∧ (W.F.a'bc.f c' < W.F.a'bc.f a → 1 < α1)

theorem p0_inner_sub (e : ℝ³) (x y : ℝ³) : ⟪x - y, e⟫ = ⟪x, e⟫ - ⟪y, e⟫ := inner_sub_left x y e

theorem p0_comb_e (e x y w : ℝ³) (s t : ℝ) :
    ⟪s • x + t • y - w, e⟫ = s * ⟪x, e⟫ + t * ⟪y, e⟫ - ⟪w, e⟫ := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, RCLike.conj_to_real]

theorem p0_smul_e3 {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (κ : ℝ) :
    ⟪κ • e3, e1⟫ = 0 ∧ ⟪κ • e3, e2⟫ = 0 ∧ ⟪κ • e3, e3⟫ = κ := by
  simp only [inner_smul_left, RCLike.conj_to_real]
  rw [real_inner_comm e1 e3, real_inner_comm e2 e3, hF.n13, hF.n23, hF.n33]; simp

/-- **P0-Kb.**  `ParEndKb` + `κ_a = 0` ⟹ `α4 = α1`, `γ4 = β1` and, in the `ParEnd` frame (`x' = d`, `x = b`, `f = c`,
`r = b'`, `g = c'`), `Yr = Yg ∧ Coll5 ∧ PersF`. -/
theorem p0_kb_collpers {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (h : ParEndKb b b' c c' d) :
    ∃ α1 α4 β1 γ4 β6 γ6 : ℝ, P0Coords W α1 α4 β1 γ4 β6 γ6 ∧ α4 = α1 ∧ γ4 = β1 ∧
      ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ b - d = κ • e3 ∧ ⟪c - d, e2⟫ = 0 ∧
        0 < ⟪c - d, e1⟫ ∧ 0 < ⟪b' - d, e2⟫ ∧ ⟪b' - d, e2⟫ = ⟪c' - d, e2⟫ ∧
        Coll5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e3⟫ ∧
        PersF ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫
          ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3,
    hfa, hfb⟩ := norm08w_coords W
  obtain ⟨e1, e2, e3, κ, hF, hκ0, hxe, hce2, hL, hr, hrob, hbr⟩ := h
  obtain ⟨hYY, hbr⟩ := hbr
  obtain ⟨hq1, hq2, hq3⟩ := p0_smul_e3 hF κ
  rw [← hxe] at hq1 hq2 hq3
  have hpne : ⟪a - d, e2⟫ ≠ 0 := fun hp => p0_e2_not_perp hF.n22 hdet hp hq2 hce2
  have hb'd : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hb']; abel
  have hc'd : c' - d = α1 • (a - d) + β1 • (b - d) := by rw [hc']; abel
  have hα : α4 = α1 := by
    have e1' : ⟪b' - d, e2⟫ = α4 * ⟪a - d, e2⟫ := by
      rw [hb'd, inner_add_left, inner_smul_left, inner_smul_left, hce2]; simp
    have e2' : ⟪c' - d, e2⟫ = α1 * ⟪a - d, e2⟫ := by
      rw [hc'd, inner_add_left, inner_smul_left, inner_smul_left, hq2]; simp
    have : (α4 - α1) * ⟪a - d, e2⟫ = 0 := by
      have := hYY; rw [e1', e2'] at this; linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpne
  have hγ : γ4 = β1 := by
    have := (planar_a_iff hdet hc' hb').mp hκ
    rw [hα] at this
    have : α1 * (β1 - γ4) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hα1.ne'
    · linarith
  refine ⟨α1, α4, β1, γ4, β6, γ6, ⟨hdet, hc', hb', ha', hα1, hβ1, h1, hα4, hγ4, h2, hβ6, hγ6, h3, hfa, hfb⟩,
    hα, hγ, e1, e2, e3, κ, hF, hκ0, hxe, hce2, hL, hr, hYY, ?_⟩
  rcases hbr with hce | hpar
  · obtain ⟨s', hs0, hs1, -, hL1, hz1⟩ := hce
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ³, w = c - (b' + s' • (c' - b')) := ⟨_, rfl⟩
    have hwd : w = (c - d) - (b' - d) - s' • ((c' - d) - (b' - d)) := by rw [hwdef]; module
    have hw1 : ⟪w, e1⟫ = 0 := by rw [hwd, p0_cef_inner]; linarith
    have hw3 : ⟪w, e3⟫ = 0 := by rw [hwd, p0_cef_inner]; linarith
    have hb'id : b' - d = (1 + s' * β1) • (c - d) + (-(s' * β1)) • (b - d) - w := by
      rw [hwdef, hb', hc', hα, hγ]; module
    have hc'id : c' - d = (1 - β1 + s' * β1) • (c - d) + (β1 - s' * β1) • (b - d) - w := by
      rw [hwdef, hb', hc', hα, hγ]; module
    have X1 : ⟪b' - d, e1⟫ = (1 + s' * β1) * ⟪c - d, e1⟫ := by
      rw [hb'id, p0_comb_e, hq1, hw1]; ring
    have Z1 : ⟪b' - d, e3⟫ = (1 + s' * β1) * ⟪c - d, e3⟫ + (-(s' * β1)) * κ := by
      rw [hb'id, p0_comb_e, hq3, hw3]; ring
    have X2 : ⟪c' - d, e1⟫ = (1 - β1 + s' * β1) * ⟪c - d, e1⟫ := by
      rw [hc'id, p0_comb_e, hq1, hw1]; ring
    have Z2 : ⟪c' - d, e3⟫ = (1 - β1 + s' * β1) * ⟪c - d, e3⟫ + (β1 - s' * β1) * κ := by
      rw [hc'id, p0_comb_e, hq3, hw3]; ring
    refine ⟨⟨?_, ?_⟩, 1, s', zero_le_one, le_refl _, hs0, hs1, Or.inl hYY, ?_, ?_⟩
    · rw [Z1, X1]; ring
    · rw [Z2, X2]; ring
    · rw [one_mul]; exact hL1
    · linarith
  · obtain ⟨-, hcoll, hpers⟩ := hpar
    exact ⟨hcoll, hpers⟩

end C2
end Type08Sp
end Minimality
