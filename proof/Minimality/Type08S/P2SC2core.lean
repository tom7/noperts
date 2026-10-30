module

public import Minimality.Type08S.SCn
public import Minimality.Type08S.SCs
public import Minimality.Type08S.P2G2M

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# SC2 core (package G): second-order version of `sc5_core` (split corner rim `(x', f, r, g, x)`)

Motion `M0 + ε M1` (each `(w1,w2,w3,t1,t2)` in the frame, `ω = pc w1 w2 w3`, `τ = pc t1 t2 0 - ω × o`), view
`u0 + ε d`, `u0 = e3`, `d = σ (S e1 - e2)`.  The ten rim rows (two per corner) are `Pos2`-rows `A + εB + ε²C`; we only
use the lexicographic first two levels (`L2 A B`: `0 < A ∨ (A = 0 ∧ 0 < B)`), the paper's finding that no row needs `ε²`.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Lexicographic positivity of `A + εB` for small `ε > 0`. -/
def L2 (A B : ℝ) : Prop := 0 < A ∨ (A = 0 ∧ 0 < B)

/-- A frame motion `ω = (w1,w2,w3)`, `τ = (t1,t2,0)`. -/
structure Mo where
  w1 : ℝ
  w2 : ℝ
  w3 : ℝ
  t1 : ℝ
  t2 : ℝ

/-- Row of the vertex `(X,Y,z)` against the rim edge vector `(a1,a2,a3)` (tilt `d = σ(S e1 - e2)`): order-0 and
order-1 coefficients for the motion `m + ε m'`. -/
def Rw (σ S a1 a2 a3 X Y z : ℝ) (m m' : Mo) : Prop :=
  L2 (a1 * VY m.w1 m.w3 m.t2 X z - a2 * VX m.w2 m.w3 m.t1 Y z)
    ((a1 * VY m'.w1 m'.w3 m'.t2 X z - a2 * VX m'.w2 m'.w3 m'.t1 Y z) +
      σ * ((a1 + S * a2) * (m.w1 * Y - m.w2 * X + 0) -
        a3 * (VX m.w2 m.w3 m.t1 Y z + S * VY m.w1 m.w3 m.t2 X z)))

theorem pc_zero : pc e1 e2 e3 0 0 0 = 0 := by simp [pc]

theorem ts2_pc (hF : Fr e1 e2 e3) (σ S a1 a2 a3 v1 v2 v3 u1 u2 u3 : ℝ)
    (h : L2 (a1 * v2 - a2 * v1) ((a1 * u2 - a2 * u1) + σ * ((a1 + S * a2) * v3 - a3 * (v1 + S * v2)))) :
    TiltSign2 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 v1 v2 v3) (pc e1 e2 e3 u1 u2 u3)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * S) (-σ) 0) := by
  have h0 : det3 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 v1 v2 v3) (pc e1 e2 e3 0 0 1) = a1 * v2 - a2 * v1 := by
    rw [det3_pc hF]; ring
  have h1 : det3 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 u1 u2 u3) (pc e1 e2 e3 0 0 1) +
      det3 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 v1 v2 v3) (pc e1 e2 e3 (σ * S) (-σ) 0) =
      (a1 * u2 - a2 * u1) + σ * ((a1 + S * a2) * v3 - a3 * (v1 + S * v2)) := by
    rw [det3_pc hF, det3_pc hF]; ring
  unfold TiltSign2 Pos2
  rw [h0, h1]
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, h'⟩)

theorem ts2_static (hF : Fr e1 e2 e3) (σ S a1 a2 a3 b1 b2 b3 : ℝ)
    (h : L2 (a1 * b2 - a2 * b1) (σ * ((a1 + S * a2) * b3 - a3 * (b1 + S * b2)))) :
    TiltSign2 (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) 0
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * S) (-σ) 0) := by
  have := ts2_pc hF σ S a1 a2 a3 b1 b2 b3 0 0 0 (by simpa using h)
  rwa [pc_zero] at this

theorem ts2_gen (hF : Fr e1 e2 e3) (o : ℝ³) (σ S X Y z a1 a2 a3 : ℝ) (m m' : Mo) (A : ℝ³)
    (hA : A = pc e1 e2 e3 a1 a2 a3) (h : Rw σ S a1 a2 a3 X Y z m m') :
    TiltSign2 A (cross (pc e1 e2 e3 m.w1 m.w2 m.w3) (o + pc e1 e2 e3 X Y z) +
        (pc e1 e2 e3 m.t1 m.t2 0 - cross (pc e1 e2 e3 m.w1 m.w2 m.w3) o))
      (cross (pc e1 e2 e3 m'.w1 m'.w2 m'.w3) (o + pc e1 e2 e3 X Y z) +
        (pc e1 e2 e3 m'.t1 m'.t2 0 - cross (pc e1 e2 e3 m'.w1 m'.w2 m'.w3) o))
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * S) (-σ) 0) := by
  subst hA
  rw [vel_pc hF, vel_pc hF]
  exact ts2_pc hF σ S a1 a2 a3 _ _ _ _ _ _ h

theorem triCert_to_2 {V : Finset ℝ³} {s d x : ℝ³} (h : TriCert V s d x) :
    ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, TiltSign2 (b - a) (c - a) 0 s d ∧ TiltSign2 (b - a) (x - a) 0 s d ∧
      TiltSign2 (c - b) (x - b) 0 s d ∧ TiltSign2 (a - c) (x - c) 0 s d := by
  have key : ∀ {p q : ℝ³}, TiltSign p q s d → TiltSign2 p q 0 s d := by
    intro p q hh
    unfold TiltSign at hh
    unfold TiltSign2 Pos2
    have cz : cross p (0 : ℝ³) = 0 := by ext i; fin_cases i <;> simp [cross]
    have e1 : det3 p (0 : ℝ³) s = 0 := by simp [det3, cz]
    have e2 : det3 p (0 : ℝ³) d = 0 := by simp [det3, cz]
    rw [e1, e2, zero_add]
    rcases hh with hh | ⟨h1, h2⟩
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  obtain ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  exact ⟨a, ha, b, hb, c, hc, key h0, key h1, key h2, key h3⟩

/-- **Second-order version of `sc5_core`.** -/
theorem sc5_core2 (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L S zp zx zf Xr Yr zr Xg Yg zg : ℝ} (m m' : Mo)
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hs : 0 < Xg + S * Yg)
    (r1 : Rw σ S L 0 (zf - zp) 0 0 zp m m')
    (r2 : Rw σ S 0 0 (zp - zx) 0 0 zp m m')
    (r3 : Rw σ S 0 0 (zp - zx) 0 0 zx m m')
    (r4 : Rw σ S (-Xg) (-Yg) (zx - zg) 0 0 zx m m')
    (r5 : Rw σ S (Xr - L) Yr (zr - zf) L 0 zf m m')
    (r6 : Rw σ S L 0 (zf - zp) L 0 zf m m')
    (r7 : Rw σ S (Xg - Xr) (Yg - Yr) (zg - zr) Xr Yr zr m m')
    (r8 : Rw σ S (Xr - L) Yr (zr - zf) Xr Yr zr m m')
    (r9 : Rw σ S (-Xg) (-Yg) (zx - zg) Xg Yg zg m m')
    (r10 : Rw σ S (Xg - Xr) (Yg - Yr) (zg - zr) Xg Yg zg m m')
    (hE : ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * S) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  have hu : pc e1 e2 e3 0 0 1 ≠ 0 := by
    intro h0
    have := inner_pc hF 0 0 1 0 0 1
    rw [h0, inner_zero_left] at this; norm_num at this
  refine isRupert_of_motionCert2 _ (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * S) (-σ) 0)
    (pc e1 e2 e3 m.w1 m.w2 m.w3) (pc e1 e2 e3 m'.w1 m'.w2 m'.w3)
    (pc e1 e2 e3 m.t1 m.t2 0 - cross (pc e1 e2 e3 m.w1 m.w2 m.w3) o)
    (pc e1 e2 e3 m'.t1 m'.t2 0 - cross (pc e1 e2 e3 m'.w1 m'.w2 m'.w3) o) hu ?_
  intro x hx
  have hmem : ∀ p ∈ ({o + pc e1 e2 e3 0 0 zp, o + pc e1 e2 e3 0 0 zx, o + pc e1 e2 e3 L 0 zf,
    o + pc e1 e2 e3 Xr Yr zr, o + pc e1 e2 e3 Xg Yg zg} : Finset ℝ³),
      p ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E := fun p hp => by
    simp only [rim5]; exact Finset.mem_union_left _ hp
  have m1 := hmem (o + pc e1 e2 e3 0 0 zp) (by simp)
  have m2 := hmem (o + pc e1 e2 e3 0 0 zx) (by simp)
  have m3 := hmem (o + pc e1 e2 e3 L 0 zf) (by simp)
  have m4 := hmem (o + pc e1 e2 e3 Xr Yr zr) (by simp)
  have m5 := hmem (o + pc e1 e2 e3 Xg Yg zg) (by simp)
  have q1 : 0 < L * (σ * (zx - zp)) := mul_pos hL hzx
  have q3 : 0 < σ * (zx - zp) * (Xg + S * Yg) := mul_pos hzx hs
  have q4 : 0 < L * Yr := mul_pos hL hYr
  simp only [rim5, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl | rfl | rfl | rfl) | hx
  · -- x'
    refine Or.inl ⟨_, m2, _, m3, ?_, ?_, ?_⟩
    · simp only [add_sub_add_left_eq_sub, pc_sub]
      refine ts2_static hF σ S _ _ _ _ _ _ ?_
      right; exact ⟨by ring, by nlinarith⟩
    · exact ts2_gen hF o σ S 0 0 zp _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r1
    · exact ts2_gen hF o σ S 0 0 zp _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r2
  · -- x
    refine Or.inl ⟨_, m5, _, m1, ?_, ?_, ?_⟩
    · simp only [add_sub_add_left_eq_sub, pc_sub]
      refine ts2_static hF σ S _ _ _ _ _ _ ?_
      right; exact ⟨by ring, by nlinarith⟩
    · exact ts2_gen hF o σ S 0 0 zx _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r3
    · exact ts2_gen hF o σ S 0 0 zx _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r4
  · -- f
    refine Or.inl ⟨_, m1, _, m4, ?_, ?_, ?_⟩
    · simp only [add_sub_add_left_eq_sub, pc_sub]
      refine ts2_static hF σ S _ _ _ _ _ _ ?_
      left; nlinarith
    · exact ts2_gen hF o σ S L 0 zf _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r5
    · exact ts2_gen hF o σ S L 0 zf _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r6
  · -- r
    refine Or.inl ⟨_, m3, _, m5, ?_, ?_, ?_⟩
    · simp only [add_sub_add_left_eq_sub, pc_sub]
      refine ts2_static hF σ S _ _ _ _ _ _ ?_
      left; nlinarith
    · exact ts2_gen hF o σ S Xr Yr zr _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r7
    · exact ts2_gen hF o σ S Xr Yr zr _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r8
  · -- g
    refine Or.inl ⟨_, m4, _, m2, ?_, ?_, ?_⟩
    · simp only [add_sub_add_left_eq_sub, pc_sub]
      refine ts2_static hF σ S _ _ _ _ _ _ ?_
      left; nlinarith
    · exact ts2_gen hF o σ S Xg Yg zg _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r9
    · exact ts2_gen hF o σ S Xg Yg zg _ _ _ m m' _ (by simp only [add_sub_add_left_eq_sub, pc_sub, sub_zero, zero_sub, sub_self]) r10
  · exact Or.inr (triCert_to_2 (hE x hx))

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.sc5_core2
