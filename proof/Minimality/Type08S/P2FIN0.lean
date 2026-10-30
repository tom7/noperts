module

public import Minimality.Type08S.P2NP6

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a assembly, helpers: `eF` in a frame, transfer of the rim hypotheses to labelled points.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- `eF` in a frame where the view is `κv e3` and `v` is edge-on. -/
theorem eF_calc (hF : Fr e1 e2 e3) {κv : ℝ} (hκv : κv ≠ 0) (v : ℝ³) (hv2 : ⟪v, e2⟫ = 0) :
    v - (⟪v, κv • e3⟫ / ⟪κv • e3, κv • e3⟫) • (κv • e3) = ⟪v, e1⟫ • e1 := by
  have hexp := hF.expand v
  have h1 : ⟪v, κv • e3⟫ = κv * ⟪v, e3⟫ := by rw [real_inner_smul_right]
  have h2 : ⟪κv • e3, κv • e3⟫ = κv * κv := by
    rw [real_inner_smul_left, real_inner_smul_right, hF.n33]; ring
  rw [h1, h2]
  have h3 : (κv * ⟪v, e3⟫ / (κv * κv)) • (κv • e3) = ⟪v, e3⟫ • e3 := by
    rw [smul_smul]; congr 1; field_simp
  rw [h3]
  have hv' : v = ⟪v, e1⟫ • e1 + ⟪v, e3⟫ • e3 := by
    have := hexp; rwa [hv2, zero_smul, add_zero] at this
  calc v - ⟪v, e3⟫ • e3 = (⟪v, e1⟫ • e1 + ⟪v, e3⟫ • e3) - ⟪v, e3⟫ • e3 := by congr 1
    _ = ⟪v, e1⟫ • e1 := by abel

theorem rim_transfer {x : Fin 7 → ℝ³} {k' m : ℕ} [NeZero k'] [NeZero m] (lab : ZMod m → Fin 7)
    (σ : ZMod k' → ZMod m) (u : ℝ³) (Pt : ZMod m → ℝ³) (hPt : ∀ j, x (lab j) = Pt j)
    (hrim : RimCertAt x u (lab ∘ σ)) (hrob : IsRobustUnimodal (fun i => ⟪x (lab (σ i)), u⟫)) :
    3 ≤ k' ∧
    (∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (Pt (σ (i + 1)) - Pt (σ i))
      (Pt (σ j) - Pt (σ i)) u) ∧
    (∀ (i : ZMod k') (a_ : ZMod m), 0 ≤ det3 (Pt (σ (i + 1)) - Pt (σ i)) (Pt a_ - Pt (σ i)) u) ∧
    IsRobustUnimodal (fun i => ⟪Pt (σ i), u⟫) := by
  refine ⟨hrim.three, fun i j hi hj => ?_, fun i a_ => ?_, ?_⟩
  · have := hrim.cyc i j hi hj
    simpa only [Function.comp, hPt] using this
  · have := hrim.left (lab a_) i
    simpa only [Function.comp, hPt] using this
  · simpa only [hPt] using hrob

end Type08Sp
end Minimality
