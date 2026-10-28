module

public import Minimality.Tilt

@[expose] public section

/-!
# Generic tilted-view motion certificate (Statement A(M))

Plain points in `ℝ³`, no frame.  Rim data are given as `TiltSign` (determinant sign at `u₀`,
tie-broken by `d`); one fixed motion `(ω, τ)`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter

/-- Local certificate at vertex `x` for the tilted view `u₀ + εd`, as `TiltSign` data, with the
ε-independent velocity `v = ω × x + τ`. Mirror of `TiltCert`. -/
def MotionCert (V : Finset ℝ³) (u₀ d ω τ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, TiltSign (y₁ - x) (y₀ - x) u₀ d ∧
      TiltSign (y₁ - x) (cross ω x + τ) u₀ d ∧ TiltSign (x - y₀) (cross ω x + τ) u₀ d) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, TiltSign (b - a) (c - a) u₀ d ∧ TiltSign (b - a) (x - a) u₀ d ∧
      TiltSign (c - b) (x - b) u₀ d ∧ TiltSign (a - c) (x - c) u₀ d)

theorem MotionCert.eventually {V : Finset ℝ³} {u₀ d ω τ x : ℝ³} (h : MotionCert V u₀ d ω τ x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (u₀ + ε • d) ω τ x := by
  rcases h with ⟨y₀, hy₀, y₁, hy₁, h0, h1, h2⟩ | ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩
  · filter_upwards [h0.eventually, h1.eventually, h2.eventually] with ε e0 e1 e2
    exact Or.inl ⟨y₀, hy₀, y₁, hy₁, e0, e1, e2⟩
  · filter_upwards [h0.eventually, h1.eventually, h2.eventually, h3.eventually] with ε e0 e1 e2 e3
    exact Or.inr ⟨a, ha, b, hb, c, hc, e0, e1, e2, e3⟩

/-- Eventual form: if for all small `ε > 0` every vertex has a `TiltCert` at `u₀ + ε d` for one
fixed motion, then `V` is Rupert. -/
theorem isRupert_of_eventually_tiltCert (V : Finset ℝ³) (u₀ d ω τ : ℝ³) (hu : u₀ ≠ 0)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ V, TiltCert V (u₀ + ε • d) ω τ x) :
    IsRupert V := by
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • d ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • d := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hu)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, h1, h2⟩ := (h.and hne).exists
  exact isRupert_of_tiltCert V _ h2 ω τ h1

/-- **Statement A(M).** A base view `u₀ ≠ 0`, a tilt direction `d`, one rigid motion `(ω, τ)`
(spin allowed), and a `MotionCert` (TiltSign rows) at every vertex give `IsRupert V`.
Rim hypotheses (R1, R2) enter only through the `TiltSign` rows of the chosen certificates. -/
theorem isRupert_of_motionCert (V : Finset ℝ³) (u₀ d ω τ : ℝ³) (hu : u₀ ≠ 0)
    (h : ∀ x ∈ V, MotionCert V u₀ d ω τ x) : IsRupert V :=
  isRupert_of_eventually_tiltCert V u₀ d ω τ hu
    ((eventually_all_finset V).2 fun x hx => (h x hx).eventually)

end Minimality

#print axioms Minimality.isRupert_of_motionCert
