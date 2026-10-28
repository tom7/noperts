module

public import Minimality.Type08S.G6Lem

@[expose] public section

set_option autoImplicit true

/-!
# Theorem 08.T' (core, frame coordinates), PROOFS §41 + sp08b/draft.md §4a

On H1 with R1 robust with a class-(d) HDN (foot interior), R2', X_ba' not robust: Lemma 08.2'
gives the weak order `W ≤ C, P ≤ C < B ≤ R`; Lemma 08.1 gives `σ(L) < B`, `C < σ(0)` for the line
`σ(X) = P + κ (X - X0)` of `S*`.  No tie or HDN condition enters.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem thm08Tp_core (hF : Fr e1 e2 e3) (o : ℝ³)
    {L h X0 X1 C W B A P R t za κ : ℝ}
    (hL : 0 < L) (hh : 0 < h) (hX : X0 < X1) (hWB : W < B) (hCA : C < A)
    (ht0 : 0 < t) (ht1 : t < 1) (hza : za < B + t * (R - B))
    (hWC : W ≤ C) (hPC : P ≤ C) (hCB : C < B) (hBR : B ≤ R)
    (hκ : κ * (X1 - X0) = R - P)
    (hσL : P + κ * (L - X0) < B) (hσ0 : C < P + κ * (0 - X0)) :
    IsRupert ({pt e1 e2 e3 o L 0 W, pt e1 e2 e3 o (L + t * (X1 - L)) (t * h) za,
      pt e1 e2 e3 o 0 0 A, pt e1 e2 e3 o L 0 B, pt e1 e2 e3 o X0 h P, pt e1 e2 e3 o 0 0 C,
      pt e1 e2 e3 o X1 h R} : Finset ℝ³) := by
  have hRP : 0 < R - P := by linarith
  have hκ0 : 0 < κ := by
    by_contra hn
    push Not at hn
    nlinarith [mul_nonneg (neg_nonneg.2 hn) (sub_pos.2 hX).le]
  have hX0 : X0 < 0 := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg hκ0.le hn]
  have hX1 : L < X1 := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg hκ0.le (sub_nonneg.2 hn)]
  have hs0 : 0 < P + κ * (0 - X0) - C := by linarith
  have hs1 : 0 < κ * (L - X0) := mul_pos hκ0 (by linarith)
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η < P + κ * (0 - X0) - C ∧ η < κ * (L - X0) :=
    ⟨min (P + κ * (0 - X0) - C) (κ * (L - X0)) / 2, by positivity,
      by have := min_le_left (P + κ * (0 - X0) - C) (κ * (L - X0)); linarith,
      by have := min_le_right (P + κ * (0 - X0) - C) (κ * (L - X0)); linarith⟩
  -- F(X, z) = (P - κ X0 - η) + (-1) z + κ X
  have hκL : 0 < κ * L := mul_pos hκ0 hL
  have hκ1 : 0 < κ * (X1 - L) := mul_pos hκ0 (by linarith)
  have F1 : 0 < (P - κ * X0 - η) + (-1) * C + κ * 0 := by linarith
  have F2 : 0 < (P - κ * X0 - η) + (-1) * W + κ * L := by linarith
  have F3 : 0 < (P - κ * X0 - η) + (-1) * C + κ * L := by linarith
  have F4 : 0 < (P - κ * X0 - η) + (-1) * P + κ * L := by linarith
  have F5 : (P - κ * X0 - η) + (-1) * P + κ * X0 < 0 := by linarith
  have F6 : (P - κ * X0 - η) + (-1) * R + κ * X1 < 0 := by linarith
  have F7 : (P - κ * X0 - η) + (-1) * B + κ * L < 0 := by linarith
  have F8 : (P - κ * X0 - η) + (-1) * R + κ * L < 0 := by linarith
  have e3' := ev_aff (h * ((P - κ * X0 - η) + (-1) * C + κ * L))
    (-X0 * ((P - κ * X0 - η) + (-1) * C + κ * 0) - h) (mul_pos hh F3)
  have e4 := ev_aff (h * ((P - κ * X0 - η) + (-1) * P + κ * L))
    (-X0 * ((P - κ * X0 - η) + (-1) * P + κ * X0) - h * (1 + κ * h)) (mul_pos hh F4)
  have e5 := ev_aff (-(h * ((P - κ * X0 - η) + (-1) * R + κ * L)))
    ((X1 - L) * ((P - κ * X0 - η) + (-1) * R + κ * X1) + h * (1 + κ * h))
    (neg_pos.2 (mul_neg_of_pos_of_neg hh F8))
  have e1' := ev_aff h (-(X1 - L)) hh
  have e2' := ev_aff h (-X0) hh
  obtain ⟨k, hk5, hk4, hk3, hk1, hk2⟩ := (e5.and (e4.and (e3'.and (e1'.and e2')))).exists
  exact lemma08S_core hF o (f0 := (P - κ * X0 - η)) (f1 := -1) (θ := κ) (k := k)
    hL hh hX hWB hCA ht0 ht1 hza F1 F2 F3 F4 F5 F6 F7 F8 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

end Type08Sp
end Minimality
