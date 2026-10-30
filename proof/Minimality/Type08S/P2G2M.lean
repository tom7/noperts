module

public import Minimality.Tilt

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# G-2M: second-order generic motion certificate (package 8)

Rows `A + εB + ε²C` (`TiltSign2`), motion `(ω₀ + εω₁, τ₀ + ετ₁)`, view `u₀ + εd`.
Concludes `IsRupert V` via `isRupert_of_tiltCert` at one small `ε`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter

/-- Sign of the quadratic `A + εB + ε²C` for all small `ε > 0`, as a lexicographic condition. -/
def Pos2 (A B C : ℝ) : Prop := 0 < A ∨ (A = 0 ∧ 0 < B) ∨ (A = 0 ∧ B = 0 ∧ 0 < C)

theorem Pos2.eventually {A B C : ℝ} (h : Pos2 A B C) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A + ε * B + ε ^ 2 * C := by
  have hc : Continuous fun ε : ℝ => A + ε * B + ε ^ 2 * C := by fun_prop
  have hc2 : Continuous fun ε : ℝ => B + ε * C := by fun_prop
  rcases h with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
  · exact (hc.continuousAt.eventually (lt_mem_nhds (by simpa using h))).filter_mono
      nhdsWithin_le_nhds
  · have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < B + ε * C :=
      (hc2.continuousAt.eventually (lt_mem_nhds (by simpa using h))).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, h2] with ε hε h3
    have : (0 : ℝ) < ε := hε
    have := mul_pos this h3
    nlinarith
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    simpa using mul_pos (pow_pos this 2) h

theorem cross_add_smul_right_aux (a b₀ b₁ : ℝ³) (ε : ℝ) :
    cross a (b₀ + ε • b₁) = cross a b₀ + ε • cross a b₁ := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem det3_quad (a b₀ b₁ u d : ℝ³) (ε : ℝ) :
    det3 a (b₀ + ε • b₁) (u + ε • d) =
      det3 a b₀ u + ε * (det3 a b₁ u + det3 a b₀ d) + ε ^ 2 * det3 a b₁ d := by
  simp only [det3, cross_add_smul_right_aux, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- `TiltSign2 a b₀ b₁ u₀ d`: `det3 a (b₀ + ε b₁) (u₀ + ε d) > 0` for all small `ε > 0`,
read off from the coefficients of `1, ε, ε²`. -/
def TiltSign2 (a b₀ b₁ u₀ d : ℝ³) : Prop :=
  Pos2 (det3 a b₀ u₀) (det3 a b₁ u₀ + det3 a b₀ d) (det3 a b₁ d)

theorem TiltSign2.eventually {a b₀ b₁ u₀ d : ℝ³} (h : TiltSign2 a b₀ b₁ u₀ d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 a (b₀ + ε • b₁) (u₀ + ε • d) := by
  filter_upwards [Pos2.eventually h] with ε hε
  rw [det3_quad]; exact hε

theorem cross_add_smul_left_aux (ω₀ ω₁ x : ℝ³) (ε : ℝ) :
    cross (ω₀ + ε • ω₁) x = cross ω₀ x + ε • cross ω₁ x := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- Second-order local certificate at `x`: velocity `v(ε) = (ω₀ × x + τ₀) + ε (ω₁ × x + τ₁)`. -/
def MotionCert2 (V : Finset ℝ³) (u₀ d ω₀ ω₁ τ₀ τ₁ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, TiltSign2 (y₁ - x) (y₀ - x) 0 u₀ d ∧
      TiltSign2 (y₁ - x) (cross ω₀ x + τ₀) (cross ω₁ x + τ₁) u₀ d ∧
      TiltSign2 (x - y₀) (cross ω₀ x + τ₀) (cross ω₁ x + τ₁) u₀ d) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, TiltSign2 (b - a) (c - a) 0 u₀ d ∧ TiltSign2 (b - a) (x - a) 0 u₀ d ∧
      TiltSign2 (c - b) (x - b) 0 u₀ d ∧ TiltSign2 (a - c) (x - c) 0 u₀ d)

theorem MotionCert2.eventually {V : Finset ℝ³} {u₀ d ω₀ ω₁ τ₀ τ₁ x : ℝ³}
    (h : MotionCert2 V u₀ d ω₀ ω₁ τ₀ τ₁ x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      TiltCert V (u₀ + ε • d) (ω₀ + ε • ω₁) (τ₀ + ε • τ₁) x := by
  have hv : ∀ ε : ℝ, cross (ω₀ + ε • ω₁) x + (τ₀ + ε • τ₁) =
      (cross ω₀ x + τ₀) + ε • (cross ω₁ x + τ₁) := by
    intro ε; rw [cross_add_smul_left_aux, smul_add]; abel
  rcases h with ⟨y₀, hy₀, y₁, hy₁, h0, h1, h2⟩ | ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩
  · filter_upwards [h0.eventually, h1.eventually, h2.eventually] with ε e0 e1 e2
    refine Or.inl ⟨y₀, hy₀, y₁, hy₁, ?_, ?_, ?_⟩
    · simpa using e0
    · rw [hv]; exact e1
    · rw [hv]; exact e2
  · filter_upwards [h0.eventually, h1.eventually, h2.eventually, h3.eventually] with ε e0 e1 e2 e3
    simp only [smul_zero, add_zero] at e0 e1 e2 e3
    exact Or.inr ⟨a, ha, b, hb, c, hc, e0, e1, e2, e3⟩

/-- **G-2M.** A base view `u₀ ≠ 0`, a tilt direction `d`, a first-order motion `(ω₀, τ₀)` and its
correction `(ω₁, τ₁)` (spin allowed): if every vertex has a `MotionCert2` (rows `A + εB + ε²C`), then
`V` is Rupert (`isRupert_of_tiltCert` at one small `ε`, view `u₀ + εd`, motion
`(ω₀ + εω₁, τ₀ + ετ₁)`). -/
theorem isRupert_of_motionCert2 (V : Finset ℝ³) (u₀ d ω₀ ω₁ τ₀ τ₁ : ℝ³) (hu : u₀ ≠ 0)
    (h : ∀ x ∈ V, MotionCert2 V u₀ d ω₀ ω₁ τ₀ τ₁ x) : IsRupert V := by
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ V,
      TiltCert V (u₀ + ε • d) (ω₀ + ε • ω₁) (τ₀ + ε • τ₁) x :=
    (eventually_all_finset V).2 fun x hx => (h x hx).eventually
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • d ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • d := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hu)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, h1, h2⟩ := (hall.and hne).exists
  exact isRupert_of_tiltCert V _ h2 _ _ h1

end Minimality

#print axioms Minimality.isRupert_of_motionCert2
