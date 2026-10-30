module

public import Minimality.Type08S.P2SC2S2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# SC2-S, case `f̄ = r̄` (package G): selection of `z0, κ, ρ, μ`

`ClassS2r`: the frame form of "`f̄ ∈ (ḡ, r̄)` on the top side, `x' ∉ Π'`, far vertices `{f, r}` strictly on one side of
the near vertices `{g, x}` in depth".  (HDN classification taken as this hypothesis; `hPi` is `x' ∉ Π'` with the sign
of Lemma E: `ζ = σ0` lies on `x`'s side of `z_{x'}`.)
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Class SC2-S (interior): the top-side line `z = σ0 + m X` passes over `f̄`, `Xg < L < Xr`;
`x' ∉ Π'` with `ζ = σ0` on the `x`-side of `z_{x'}`; robust separation of `{f,r}` from `{g,x}` (both directions). -/
def ClassS2r (σ L zp zx Xg m σ0 : ℝ) : Prop :=
  Xg < L ∧ 0 < σ * (σ0 - zp) ∧
  ((σ * (σ0 + m * L) < σ * (σ0 + m * Xg) ∧ σ * (σ0 + m * L) < σ * zx) ∨
   (σ * (σ0 + m * Xg) < σ * (σ0 + m * L) ∧ σ * zx < σ * (σ0 + m * L)))

theorem sc2S_params_r {σ L zp zx Xg m σ0 : ℝ} (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hc : ClassS2r σ L zp zx Xg m σ0) :
    ∃ z0 κ ρ : ℝ, 0 < ρ ∧ κ * ((σ0 + m * L) - z0) < 0 ∧
      0 < κ * ((σ0 + m * Xg) - z0) ∧ 0 < κ * (zx - z0) ∧
      0 < ρ * κ * (zp - z0) + σ * (σ0 - zp) ∧ 0 < ρ * κ * (zx - z0) + σ * (σ0 - zx) := by
  obtain ⟨hXg, hPi, h | h⟩ := hc
  · obtain ⟨h1, h2⟩ := h
    have hσ : σ ≠ 0 := by rintro rfl; simp at hzx
    have hm : σ * m < 0 := by nlinarith
    set δ := min (min (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) (σ * zx - σ * (σ0 + m * L)))
      (σ * σ0 - σ * (σ0 + m * L)) / 2 with hδ
    have hδ1 : δ ≤ (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) / 2 := by
      rw [hδ]; have := min_le_left (min (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) (σ * zx - σ * (σ0 + m * L)))
        (σ * σ0 - σ * (σ0 + m * L)); have := min_le_left (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) (σ * zx - σ * (σ0 + m * L)); linarith
    have hδ2 : δ ≤ (σ * zx - σ * (σ0 + m * L)) / 2 := by
      rw [hδ]; have := min_le_left (min (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) (σ * zx - σ * (σ0 + m * L)))
        (σ * σ0 - σ * (σ0 + m * L)); have := min_le_right (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) (σ * zx - σ * (σ0 + m * L)); linarith
    have hδ3 : δ ≤ (σ * σ0 - σ * (σ0 + m * L)) / 2 := by
      rw [hδ]; have := min_le_right (min (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) (σ * zx - σ * (σ0 + m * L)))
        (σ * σ0 - σ * (σ0 + m * L)); linarith
    have hδ0 : 0 < δ := by
      rw [hδ]
      have : 0 < min (min (σ * (σ0 + m * Xg) - σ * (σ0 + m * L)) (σ * zx - σ * (σ0 + m * L)))
        (σ * σ0 - σ * (σ0 + m * L)) :=
        lt_min (lt_min (by linarith) (by linarith)) (by nlinarith)
      linarith
    refine ⟨(σ * (σ0 + m * L) + δ) / σ, σ, 1, one_pos, ?_, ?_, ?_, ?_, ?_⟩
    · have : σ * ((σ0 + m * L) - (σ * (σ0 + m * L) + δ) / σ) = -δ := by field_simp; ring
      linarith
    · have : σ * ((σ0 + m * Xg) - (σ * (σ0 + m * L) + δ) / σ) = σ * (σ0 + m * Xg) - σ * (σ0 + m * L) - δ := by
        field_simp; ring
      linarith
    · have : σ * (zx - (σ * (σ0 + m * L) + δ) / σ) = σ * zx - σ * (σ0 + m * L) - δ := by
        field_simp; ring
      linarith
    · have : 1 * σ * (zp - (σ * (σ0 + m * L) + δ) / σ) + σ * (σ0 - zp) =
          σ * σ0 - σ * (σ0 + m * L) - δ := by field_simp; ring
      linarith
    · have : 1 * σ * (zx - (σ * (σ0 + m * L) + δ) / σ) + σ * (σ0 - zx) =
          σ * σ0 - σ * (σ0 + m * L) - δ := by field_simp; ring
      linarith
  · obtain ⟨h1, h2⟩ := h
    have hσ : σ ≠ 0 := by rintro rfl; simp at hzx
    have hm : 0 < σ * m := by nlinarith
    set δ := min (σ * (σ0 + m * L) - σ * (σ0 + m * Xg)) (σ * (σ0 + m * L) - σ * zx) / 2 with hδ
    have hδ1 : δ ≤ (σ * (σ0 + m * L) - σ * (σ0 + m * Xg)) / 2 := by
      rw [hδ]; have := min_le_left (σ * (σ0 + m * L) - σ * (σ0 + m * Xg)) (σ * (σ0 + m * L) - σ * zx); linarith
    have hδ2 : δ ≤ (σ * (σ0 + m * L) - σ * zx) / 2 := by
      rw [hδ]; have := min_le_right (σ * (σ0 + m * L) - σ * (σ0 + m * Xg)) (σ * (σ0 + m * L) - σ * zx); linarith
    have hδ0 : 0 < δ := by
      rw [hδ]
      have : 0 < min (σ * (σ0 + m * L) - σ * (σ0 + m * Xg)) (σ * (σ0 + m * L) - σ * zx) :=
        lt_min (by linarith) (by linarith)
      linarith
    set z0 := (σ * (σ0 + m * L) - δ) / σ with hz0
    have hσz0 : σ * z0 = σ * (σ0 + m * L) - δ := by rw [hz0]; field_simp
    set T := σ * z0 - σ * zx with hT
    have hT0 : 0 < T := by rw [hT]; linarith
    refine ⟨z0, -σ, 1 + |σ * (σ0 - zx)| / T, by positivity, ?_, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · have hpos : 0 < 1 + |σ * (σ0 - zx)| / T := by positivity
      have : 0 < σ * z0 - σ * zp := by nlinarith
      nlinarith [mul_pos hpos this]
    · have : (1 + |σ * (σ0 - zx)| / T) * T = T + |σ * (σ0 - zx)| := by field_simp
      nlinarith [neg_abs_le (σ * (σ0 - zx))]

end Type08Sp
end Minimality
