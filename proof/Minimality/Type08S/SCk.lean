module

public import Minimality.Type08S.SCj

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Frame coordinates by inner products. -/
theorem pc_coords (hF : Fr e1 e2 e3) (o p : ℝ³) :
    p = o + pc e1 e2 e3 ⟪p - o, e1⟫ ⟪p - o, e2⟫ ⟪p - o, e3⟫ := by
  have := hF.expand (p - o)
  rw [pc]; rw [← this]; abel

theorem Fr.neg_13 (hF : Fr e1 e2 e3) : Fr (-e1) e2 (-e3) where
  n11 := by simpa using hF.n11
  n22 := hF.n22
  n33 := by simpa using hF.n33
  n12 := by simpa using hF.n12
  n13 := by simpa using hF.n13
  n23 := by simpa using hF.n23
  c12 := by
    have := cross_smul_l (-1) e1 e2
    simp only [neg_smul, one_smul] at this; rw [this, hF.c12]
  c23 := by
    have := cross_smul_r (-1) e2 e3
    simp only [neg_smul, one_smul] at this; rw [this, hF.c23]
  c31 := by
    have h1 := cross_smul_l (-1) e3 (-e1)
    have h2 := cross_smul_r (-1) e3 e1
    simp only [neg_smul, one_smul] at h1 h2
    rw [h1, h2, hF.c31]; simp

/-- **Oriented frame at a view.**  `u = κ e3`, `v` edge-on (`⟪v,e2⟫ = 0`) with `⟪v,e1⟫ > 0`,
`⟪w,e2⟫ > 0` (right-handed; `κ` of either sign). -/
theorem frame_ex_pos {w u v : ℝ³} (hdet : det3 w u v ≠ 0) :
    ∃ e1 e2 e3 : ℝ³, ∃ κ : ℝ, Fr e1 e2 e3 ∧ κ ≠ 0 ∧ u = κ • e3 ∧ ⟪v, e2⟫ = 0 ∧ 0 < ⟪v, e1⟫ ∧
      0 < ⟪w, e2⟫ := by
  obtain ⟨e1, e2, e3, hF, hu1, hu2, hu3, hv2, hv1, hw2⟩ := frame_exists hdet
  have hu : u = ⟪u, e3⟫ • e3 := by
    have := hF.expand u; rw [hu1, hu2] at this; simpa using this
  rcases lt_or_gt_of_ne hv1 with h | h
  · refine ⟨-e1, e2, -e3, -⟪u, e3⟫, hF.neg_13, by simpa using hu3.ne', ?_, ?_, ?_, hw2⟩
    · rw [neg_smul, ← smul_neg] ; simpa using hu
    · simpa using hv2
    · simpa using h
  · exact ⟨e1, e2, e3, ⟪u, e3⟫, hF, hu3.ne', hu, hv2, h, hw2⟩

/-- Inequality part of `SCfN2` (frame numbers). -/
def N2Nums (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd Xa Ya za : ℝ) : Prop :=
  0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ ClassC5 L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < L * Yg ∧ 0 < L * Ya ∧ 0 < (Xg - L) * Ya - Yg * (Xa - L) ∧
    0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)

/-- **Frame dictionary for N2 `K_c`** (item 1a): in any right-handed frame with `u = κ e3`, the
seven points have coordinates `⟪· - a', e_i⟫` (so `a'` is the origin, `zp = 0`), and `SCfN2`
holds as soon as the inequalities `N2Nums` hold for these coordinates. -/
theorem SCfN2_of_frame {u a a' b b' c c' d : ℝ³} (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0)
    (hu : u = κ • e3) (σ : ℝ)
    (H : N2Nums σ ⟪b - a', e1⟫ 0 ⟪c - a', e3⟫ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫
      ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ ⟪d - a', e1⟫ ⟪d - a', e3⟫ ⟪a - a', e1⟫
      ⟪a - a', e2⟫ ⟪a - a', e3⟫)
    (hc0 : ⟪c - a', e1⟫ = 0) (hc2 : ⟪c - a', e2⟫ = 0) (hb2 : ⟪b - a', e2⟫ = 0)
    (hd2 : ⟪d - a', e2⟫ = 0) :
    SCfN2 u a a' b b' c c' d := by
  refine ⟨e1, e2, e3, a', σ, ⟪b - a', e1⟫, 0, ⟪c - a', e3⟫, ⟪b - a', e3⟫, ⟪c' - a', e1⟫, ⟪c' - a', e2⟫,
    ⟪c' - a', e3⟫, ⟪b' - a', e1⟫, ⟪b' - a', e2⟫, ⟪b' - a', e3⟫, ⟪d - a', e1⟫, ⟪d - a', e3⟫,
    ⟪a - a', e1⟫, ⟪a - a', e2⟫, ⟪a - a', e3⟫, κ, hF, hκ, hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H⟩
  · have := pc_coords hF a' a'; simp at this; simp [pc]
  · have := pc_coords hF a' c; rw [hc0, hc2] at this; exact this
  · have := pc_coords hF a' b; rw [hb2] at this; exact this
  · exact pc_coords hF a' c'
  · exact pc_coords hF a' b'
  · have := pc_coords hF a' d; rw [hd2] at this; exact this
  · exact pc_coords hF a' a

/-- Inequality part of `SCfT4` (frame numbers). -/
def T4Nums (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd lam za : ℝ) : Prop :=
  0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ ClassC5 L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < lam ∧ lam < 1 ∧ σ * (za - ((1 - lam) * zx + lam * zg)) < 0

/-- **Frame dictionary for T4 (`K_b`, `K_2`)**: origin `xp`, coordinates `⟪· - xp, e_i⟫`; `x - xp`
is along `e3`, `f - xp` and `p - xp` are edge-on (`e2`-coordinate 0), and the G-middle `q` lies
over the point `lam * (g - xp)` of the screen. -/
theorem SCfT4_of_frame {u xp x f r g p q : ℝ³} (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0)
    (hu : u = κ • e3) (σ lam : ℝ)
    (H : T4Nums σ ⟪f - xp, e1⟫ 0 ⟪x - xp, e3⟫ ⟪f - xp, e3⟫ ⟪r - xp, e1⟫ ⟪r - xp, e2⟫ ⟪r - xp, e3⟫
      ⟪g - xp, e1⟫ ⟪g - xp, e2⟫ ⟪g - xp, e3⟫ ⟪p - xp, e1⟫ ⟪p - xp, e3⟫ lam ⟪q - xp, e3⟫)
    (hx1 : ⟪x - xp, e1⟫ = 0) (hx2 : ⟪x - xp, e2⟫ = 0) (hf2 : ⟪f - xp, e2⟫ = 0)
    (hp2 : ⟪p - xp, e2⟫ = 0) (hq1 : ⟪q - xp, e1⟫ = lam * ⟪g - xp, e1⟫)
    (hq2 : ⟪q - xp, e2⟫ = lam * ⟪g - xp, e2⟫) :
    SCfT4 u xp x f r g p q := by
  refine ⟨e1, e2, e3, xp, σ, ⟪f - xp, e1⟫, 0, ⟪x - xp, e3⟫, ⟪f - xp, e3⟫, ⟪r - xp, e1⟫, ⟪r - xp, e2⟫,
    ⟪r - xp, e3⟫, ⟪g - xp, e1⟫, ⟪g - xp, e2⟫, ⟪g - xp, e3⟫, ⟪p - xp, e1⟫, ⟪p - xp, e3⟫, lam,
    ⟪q - xp, e3⟫, κ, hF, hκ, hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H⟩
  · have := pc_coords hF xp xp; simp at this; simp [pc]
  · have := pc_coords hF xp x; rw [hx1, hx2] at this; exact this
  · have := pc_coords hF xp f; rw [hf2] at this; exact this
  · exact pc_coords hF xp r
  · exact pc_coords hF xp g
  · have := pc_coords hF xp p; rw [hp2] at this; exact this
  · have := pc_coords hF xp q; rw [hq1, hq2] at this; exact this

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.SCfN2_of_frame
#print axioms Minimality.Type08Sp.frame_ex_pos
#print axioms Minimality.Type08Sp.SCfT4_of_frame
