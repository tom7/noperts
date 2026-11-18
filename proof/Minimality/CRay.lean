module

public import Minimality.OrthoView2

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter

namespace Minimality.CRay
open Minimality Minimality.H21

private theorem zmod5_tab : ((0 : ZMod 5) + 1 = 1) ∧ ((0 : ZMod 5) + 2 = 2) ∧ ((0 : ZMod 5) + 3 = 3) ∧
    ((0 : ZMod 5) + 4 = 4) ∧ ((1 : ZMod 5) + 1 = 2) ∧ ((1 : ZMod 5) + 2 = 3) ∧
    ((1 : ZMod 5) + 3 = 4) ∧ ((1 : ZMod 5) + 4 = 0) ∧ ((2 : ZMod 5) + 1 = 3) ∧
    ((2 : ZMod 5) + 2 = 4) ∧ ((2 : ZMod 5) + 3 = 0) ∧ ((2 : ZMod 5) + 4 = 1) ∧
    ((3 : ZMod 5) + 1 = 4) ∧ ((3 : ZMod 5) + 2 = 0) ∧ ((3 : ZMod 5) + 3 = 1) ∧
    ((3 : ZMod 5) + 4 = 2) ∧ ((4 : ZMod 5) + 1 = 0) ∧ ((4 : ZMod 5) + 2 = 1) ∧
    ((4 : ZMod 5) + 3 = 2) ∧ ((4 : ZMod 5) + 4 = 3) := by decide


/-- **Lemma CR5, combinatorial core, K+ case.**  The 5-cycle `(K, v1, J, M, v2)` of depths
`z 0 .. z 4` with `K` above both ends, `v1 < K` or `v2 < K` (`z_K > min`), and `J0` (the higher end)
below its neighbour `v(J0)`: robustly unimodal.  (`J0 = J`: `z M < z J < z v1`;
`J0 = M`: `z J < z M < z v2`.) -/
theorem robUni5_kplus (z : ZMod 5 → ℝ) (hKJ : z 2 < z 0) (hKM : z 3 < z 0)
    (hK : z 1 < z 0 ∨ z 4 < z 0)
    (hJ0 : (z 3 < z 2 ∧ z 2 < z 1) ∨ (z 2 < z 3 ∧ z 3 < z 4)) : RobUni z := by
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34,
    a41, a42, a43, a44⟩ := zmod5_tab
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨ (b = 1 ∧ c = 3 ∧ d = 4) ∨
      (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rintro ⟨h1, h2, h3, h4⟩
  rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23,
    a24, a31, a32, a33, a34, a41, a42, a43, a44] at h1 h2 h3 h4 <;>
  rcases hK with hK | hK <;> rcases hJ0 with ⟨hJ1, hJ2⟩ | ⟨hJ1, hJ2⟩ <;>
  linarith

/-- **Lemma CR5, combinatorial core, K- case.**  The 5-cycle `(K, v1, J, M, v2)` of depths
`z 0 .. z 4` with `K` below both ends, `K < v1` or `K < v2` (`z_K < max`), and `J0` (the lower end)
above its neighbour `v(J0)`: robustly unimodal.  (`J0 = J`: `z v1 < z J < z M`;
`J0 = M`: `z v2 < z M < z J`.) -/
theorem robUni5_kminus (z : ZMod 5 → ℝ) (hKJ : z 0 < z 2) (hKM : z 0 < z 3)
    (hK : z 0 < z 1 ∨ z 0 < z 4)
    (hJ0 : (z 2 < z 3 ∧ z 1 < z 2) ∨ (z 3 < z 2 ∧ z 4 < z 3)) : RobUni z := by
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34,
    a41, a42, a43, a44⟩ := zmod5_tab
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨ (b = 1 ∧ c = 3 ∧ d = 4) ∨
      (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rintro ⟨h1, h2, h3, h4⟩
  rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23,
    a24, a31, a32, a33, a34, a41, a42, a43, a44] at h1 h2 h3 h4 <;>
  rcases hK with hK | hK <;> rcases hJ0 with ⟨hJ1, hJ2⟩ | ⟨hJ1, hJ2⟩ <;>
  linarith


/-- **Lemma CR5, geometric leaf (K+).**  A cell certificate `CellAt F U Dn u` for an injective
5-rim `c` whose depths `(K, v1, J, M, v2) = (⟪x (c i), u⟫)` satisfy the K+ conditions: Rupert.
`u` is the ray point `c(τ)`; its cell certificate is a hypothesis. -/
theorem isRupert_of_cr5_kplus {m n : ℕ} {S : Fin m → Finset (Fin n)}
    {x : Fin n → ℝ³} (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 5 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³}
    (hu : CellAt F U Dn u) (hKJ : ⟪x (c 2), u⟫ < ⟪x (c 0), u⟫) (hKM : ⟪x (c 3), u⟫ < ⟪x (c 0), u⟫)
    (hK : ⟪x (c 1), u⟫ < ⟪x (c 0), u⟫ ∨ ⟪x (c 4), u⟫ < ⟪x (c 0), u⟫)
    (hJ0 : (⟪x (c 3), u⟫ < ⟪x (c 2), u⟫ ∧ ⟪x (c 2), u⟫ < ⟪x (c 1), u⟫) ∨
      (⟪x (c 2), u⟫ < ⟪x (c 3), u⟫ ∧ ⟪x (c 3), u⟫ < ⟪x (c 4), u⟫)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_closedCell (by norm_num) F hx hc hcyc hu hu.cellLe
    (robUni5_kplus _ hKJ hKM hK hJ0)

/-- **Lemma CR5, geometric leaf (K-).**  A cell certificate `CellAt F U Dn u` for an injective
5-rim `c` whose depths `(K, v1, J, M, v2) = (⟪x (c i), u⟫)` satisfy the K- conditions: Rupert.
`u` is the ray point `c(τ)`; its cell certificate is a hypothesis. -/
theorem isRupert_of_cr5_kminus {m n : ℕ} {S : Fin m → Finset (Fin n)}
    {x : Fin n → ℝ³} (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 5 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³}
    (hu : CellAt F U Dn u) (hKJ : ⟪x (c 0), u⟫ < ⟪x (c 2), u⟫) (hKM : ⟪x (c 0), u⟫ < ⟪x (c 3), u⟫)
    (hK : ⟪x (c 0), u⟫ < ⟪x (c 1), u⟫ ∨ ⟪x (c 0), u⟫ < ⟪x (c 4), u⟫)
    (hJ0 : (⟪x (c 2), u⟫ < ⟪x (c 3), u⟫ ∧ ⟪x (c 1), u⟫ < ⟪x (c 2), u⟫) ∨
      (⟪x (c 3), u⟫ < ⟪x (c 2), u⟫ ∧ ⟪x (c 4), u⟫ < ⟪x (c 3), u⟫)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_closedCell (by norm_num) F hx hc hcyc hu hu.cellLe
    (robUni5_kminus _ hKJ hKM hK hJ0)

/-- **Depth along the c-ray, frame form.**  `x i = p + ∑ e, y i e • v e`, `⟪v e, u⟫ = 1`
(`G c* = 1`, `u = ∑ c*_e v e`), tilted view `u + t • v K` (`t = sg τ c*_K`):
`⟪x i, u + t v K⟫ = ⟪p, u + t v K⟫ + σ i + t ∑ e, y i e ⟪v e, v K⟫` with `σ i = ∑ e, y i e`;
the Gram entries `⟪v e, v K⟫ = G_eK`. -/
theorem depth_ray {ι : Type*} {k : ℕ} (x : ι → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : ι → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (u : ℝ³)
    (hv : ∀ e, ⟪v e, u⟫ = 1) (K : Fin k) (t : ℝ) (i : ι) :
    ⟪x i, u + t • v K⟫ = ⟪p, u + t • v K⟫ + ((∑ e, y i e) + t * ∑ e, y i e * ⟪v e, v K⟫) := by
  rw [hxy i, inner_add_left, sum_inner]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [inner_smul_left, inner_add_right, inner_smul_right, hv e]; simp; ring

/-- The frame vertex `p + v K` (the end `K`): `z_K - ⟪p,·⟫ = 1 + t G_KK`; a vertex with
`y = e_J`: `1 + t G_JK` (the note's `z_K = 1 + sg τ (1+P)`, `z_J = 1 - sg τ Q_J`). -/
theorem depth_ray_single {ι : Type*} {k : ℕ} (x : ι → ℝ³) (p : ℝ³) (v : Fin k → ℝ³)
    (y : ι → Fin k → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (u : ℝ³)
    (hv : ∀ e, ⟪v e, u⟫ = 1) (K J : Fin k) (t : ℝ) (i : ι) (hi : y i = Pi.single J 1) :
    ⟪x i, u + t • v K⟫ = ⟪p, u + t • v K⟫ + (1 + t * ⟪v J, v K⟫) := by
  rw [depth_ray x p v y hxy u hv K t i, hi]
  simp [Pi.single_apply]

end Minimality.CRay
