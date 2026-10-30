module

public import Minimality.Type08S.P2G2M
public import Minimality.Oct9Par
public import Minimality.OctaTools

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem pos2A {x y z : ℝ} (h : 0 < x) : Pos2 x y z := Or.inl h
theorem pos2B {x y z : ℝ} (hx : x = 0) (h : 0 < y) : Pos2 x y z := Or.inr (Or.inl ⟨hx, h⟩)
theorem pos2C {x y z : ℝ} (hx : x = 0) (hy : y = 0) (h : 0 < z) : Pos2 x y z :=
  Or.inr (Or.inr ⟨hx, hy, h⟩)

macro "ex" : tactic => `(tactic| (simp only [det3_expand, cross_apply_zero, cross_apply_one, cross_apply_two,
  PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, PiLp.zero_apply, smul_eq_mul,
  PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring))

/-- Per-vertex rows of Lemma T'S, with `w` and `κ N > 0` given. -/
theorem Tp_sep_rows (d A B C w : ℝ³) {α4 β1 γ4 β6 γ6 s ζ : ℝ} (κ : ℝ)
    (hw : w = (α4 - 1) • A + (s + γ4) • C)
    (hH : 0 < det3 A C B)
    (hα4 : 0 < α4) (hα : α4 < 1) (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 0 < s)
    (hN : 0 < κ * (⟪B, B⟫ * ⟪A, (α4 - 1) • A + (s + γ4) • C⟫ -
        ⟪A, B⟫ * ⟪B, (α4 - 1) • A + (s + γ4) • C⟫))
    (hz0 : 0 < ζ) (hDa : ⟪A, B⟫ < ζ) (hDb' : α4 * ⟪A, B⟫ + γ4 * ⟪C, B⟫ < ζ) (hDc : ⟪C, B⟫ < ζ)
    (hDb : ζ < ⟪B, B⟫) (hDc' : ζ < ⟪A, B⟫ + β1 * ⟪B, B⟫) :
    let v0 : ℝ³ → ℝ³ := fun x => (⟪x - d, B⟫ - ζ) • w - ⟪w, x - d⟫ • B
    let v1 : ℝ³ → ℝ³ := fun x => κ • cross B (x - d - (1/2 : ℝ) • A)
    -- c
    (TiltSign2 (d - (d + C)) ((d + α4 • A + γ4 • C) - (d + C)) 0 B w ∧
     TiltSign2 (d - (d + C)) (v0 (d + C)) (v1 (d + C)) B w ∧
     TiltSign2 ((d + C) - (d + α4 • A + γ4 • C)) (v0 (d + C)) (v1 (d + C)) B w) ∧
    -- d
    (TiltSign2 ((d + B) - d) ((d + C) - d) 0 B w ∧
     TiltSign2 ((d + B) - d) (v0 d) (v1 d) B w ∧
     TiltSign2 (d - (d + C)) (v0 d) (v1 d) B w) ∧
    -- b
    (TiltSign2 ((d + A + β1 • B) - (d + B)) (d - (d + B)) 0 B w ∧
     TiltSign2 ((d + A + β1 • B) - (d + B)) (v0 (d + B)) (v1 (d + B)) B w ∧
     TiltSign2 ((d + B) - d) (v0 (d + B)) (v1 (d + B)) B w) ∧
    -- c'
    (TiltSign2 ((d + A) - (d + A + β1 • B)) ((d + B) - (d + A + β1 • B)) 0 B w ∧
     TiltSign2 ((d + A) - (d + A + β1 • B)) (v0 (d + A + β1 • B)) (v1 (d + A + β1 • B)) B w ∧
     TiltSign2 ((d + A + β1 • B) - (d + B)) (v0 (d + A + β1 • B)) (v1 (d + A + β1 • B)) B w) ∧
    -- a
    (TiltSign2 ((d + α4 • A + γ4 • C) - (d + A)) ((d + A + β1 • B) - (d + A)) 0 B w ∧
     TiltSign2 ((d + α4 • A + γ4 • C) - (d + A)) (v0 (d + A)) (v1 (d + A)) B w ∧
     TiltSign2 ((d + A) - (d + A + β1 • B)) (v0 (d + A)) (v1 (d + A)) B w) ∧
    -- b'
    (TiltSign2 ((d + C) - (d + α4 • A + γ4 • C)) ((d + A) - (d + α4 • A + γ4 • C)) 0 B w ∧
     TiltSign2 ((d + C) - (d + α4 • A + γ4 • C)) (v0 (d + α4 • A + γ4 • C))
       (v1 (d + α4 • A + γ4 • C)) B w ∧
     TiltSign2 ((d + α4 • A + γ4 • C) - (d + A)) (v0 (d + α4 • A + γ4 • C))
       (v1 (d + α4 • A + γ4 • C)) B w) ∧
    -- a' hidden in (c, d, a)
    (TiltSign2 (d - (d + C)) ((d + A) - (d + C)) 0 B w ∧
     TiltSign2 (d - (d + C)) ((d + β6 • B + γ6 • C) - (d + C)) 0 B w ∧
     TiltSign2 ((d + A) - d) ((d + β6 • B + γ6 • C) - d) 0 B w ∧
     TiltSign2 ((d + C) - (d + A)) ((d + β6 • B + γ6 • C) - (d + A)) 0 B w) := by
  intro v0 v1
  have f1 : 0 < 1 - α4 := sub_pos.2 hα
  have f2 : 0 < (1 + s) * α4 + γ4 - 1 := by nlinarith
  have f3 : 0 < α4 + γ4 - 1 := by linarith
  have f4 : 0 < s + γ4 := by linarith
  have hN2 := half_pos hN
  have g1 := sub_pos.2 hDa
  have g2 := sub_pos.2 hDb'
  have g3 := sub_pos.2 hDc
  have g4 := sub_pos.2 hDb
  have g5 := sub_pos.2 hDc'
  subst hw
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩⟩
  -- c
  · exact pos2A (lt_of_lt_of_eq (mul_pos hα4 hH) (by ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos g3 f1) hH) (by simp only [v0, v1]; ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos g3 f2) hH) (by simp only [v0, v1]; ex))
  -- d
  · exact pos2B (by ex) (lt_of_lt_of_eq (mul_pos f1 hH) (by ex))
  · exact pos2C (by simp only [v0, v1]; ex) (by simp only [v0, v1]; ex)
      (lt_of_lt_of_eq hN2 (by simp only [v0, v1]; ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos hz0 f1) hH) (by simp only [v0, v1]; ex))
  -- b
  · exact pos2B (by ex) (lt_of_lt_of_eq (mul_pos f4 hH) (by ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos g4 f4) hH) (by simp only [v0, v1]; ex))
  · exact pos2C (by simp only [v0, v1]; ex) (by simp only [v0, v1]; ex)
      (lt_of_lt_of_eq hN2 (by simp only [v0, v1]; ex))
  -- c'
  · exact pos2B (by ex) (lt_of_lt_of_eq (mul_pos (mul_pos hβ1 f4) hH) (by ex))
  · exact pos2C (by simp only [v0, v1]; ex) (by simp only [v0, v1]; ex)
      (lt_of_lt_of_eq (mul_pos hβ1 hN2) (by simp only [v0, v1]; ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos g5 f4) hH) (by simp only [v0, v1]; ex))
  -- a
  · exact pos2B (by ex) (lt_of_lt_of_eq (mul_pos (mul_pos (mul_pos hs hβ1) f1) hH) (by ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos (mul_pos hs g1) f1) hH) (by simp only [v0, v1]; ex))
  · exact pos2C (by simp only [v0, v1]; ex) (by simp only [v0, v1]; ex)
      (lt_of_lt_of_eq (mul_pos hβ1 hN2) (by simp only [v0, v1]; ex))
  -- b'
  · exact pos2A (lt_of_lt_of_eq (mul_pos f3 hH) (by ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos g2 f2) hH) (by simp only [v0, v1]; ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (mul_pos (mul_pos hs g2) f1) hH) (by simp only [v0, v1]; ex))
  -- a'
  · exact pos2A (lt_of_lt_of_eq hH (by ex))
  · exact pos2B (by ex) (lt_of_lt_of_eq (mul_pos (mul_pos hβ6 f1) hH) (by ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos hγ6 hH) (by ex))
  · exact pos2A (lt_of_lt_of_eq (mul_pos (sub_pos.2 hγ61) hH) (by ex))

end Minimality
