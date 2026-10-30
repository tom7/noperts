module

public import Minimality.Type08S.P2RDefs

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K, core: the sign-normalised (σ = 1) coordinate model of the T frame and the cell tests.
Screen coordinates `(X, Y)`, depth `z`; `q = (r,0)` (over `d`, `b`), `q' = (0,0)` (over `c`, `a'`),
`c̄' = q + α1 (W, ha)`, `a` on the open side `(q, c̄')`.  Tilt `(T1, t2)`.
`L1 = W t2 - ha T1` (side `[q,c̄']`), `L4 = r t2` (side `[q',q]`), `L3 = r (γ4-1) t2 - α4 L1` (side `[b̄',q']`);
the map.md sign `s_i` is `- sign L_i`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace K

abbrev P3 := ℝ × ℝ × ℝ

def kd (r : ℝ) : P3 := (r, 0, 0)
def kb (r ν : ℝ) : P3 := (r, 0, ν)
def kc (C0 : ℝ) : P3 := (0, 0, C0)
def ka (r W ha w3 : ℝ) : P3 := (r + W, ha, w3)
def ka' (ν β6 C0 : ℝ) : P3 := (0, 0, β6 * ν + C0)
def kb' (r W ha w3 C0 α4 γ4 : ℝ) : P3 := (r * (1 - γ4) + α4 * W, α4 * ha, α4 * w3 + γ4 * C0)
def kc' (r W ha w3 ν α1 β1 : ℝ) : P3 := (r + α1 * W, α1 * ha, α1 * w3 + β1 * ν)

def cyc4 {α : Type*} (p0 p1 p2 p3 : α) : ZMod 4 → α := ![p0, p1, p2, p3]
def cyc5 {α : Type*} (p0 p1 p2 p3 p4 : α) : ZMod 5 → α := ![p0, p1, p2, p3, p4]
def cyc6 {α : Type*} (p0 p1 p2 p3 p4 p5 : α) : ZMod 6 → α := ![p0, p1, p2, p3, p4, p5]

theorem z4c (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
theorem z5c (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide
theorem z6c (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
theorem z4s : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧ (3 : ZMod 4) + 1 = 0 := by decide
theorem z5s : (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧ (3 : ZMod 5) + 1 = 4 ∧
    (4 : ZMod 5) + 1 = 0 := by decide
theorem z6s : (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧ (3 : ZMod 6) + 1 = 4 ∧
    (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide

theorem c4_0 {α : Type*} {p0 p1 p2 p3 : α} : cyc4 p0 p1 p2 p3 0 = p0 := rfl
theorem c4_1 {α : Type*} {p0 p1 p2 p3 : α} : cyc4 p0 p1 p2 p3 1 = p1 := rfl
theorem c4_2 {α : Type*} {p0 p1 p2 p3 : α} : cyc4 p0 p1 p2 p3 2 = p2 := rfl
theorem c4_3 {α : Type*} {p0 p1 p2 p3 : α} : cyc4 p0 p1 p2 p3 3 = p3 := rfl
theorem c5_0 {α : Type*} {p0 p1 p2 p3 p4 : α} : cyc5 p0 p1 p2 p3 p4 0 = p0 := rfl
theorem c5_1 {α : Type*} {p0 p1 p2 p3 p4 : α} : cyc5 p0 p1 p2 p3 p4 1 = p1 := rfl
theorem c5_2 {α : Type*} {p0 p1 p2 p3 p4 : α} : cyc5 p0 p1 p2 p3 p4 2 = p2 := rfl
theorem c5_3 {α : Type*} {p0 p1 p2 p3 p4 : α} : cyc5 p0 p1 p2 p3 p4 3 = p3 := rfl
theorem c5_4 {α : Type*} {p0 p1 p2 p3 p4 : α} : cyc5 p0 p1 p2 p3 p4 4 = p4 := rfl
theorem c6_0 {α : Type*} {p0 p1 p2 p3 p4 p5 : α} : cyc6 p0 p1 p2 p3 p4 p5 0 = p0 := rfl
theorem c6_1 {α : Type*} {p0 p1 p2 p3 p4 p5 : α} : cyc6 p0 p1 p2 p3 p4 p5 1 = p1 := rfl
theorem c6_2 {α : Type*} {p0 p1 p2 p3 p4 p5 : α} : cyc6 p0 p1 p2 p3 p4 p5 2 = p2 := rfl
theorem c6_3 {α : Type*} {p0 p1 p2 p3 p4 p5 : α} : cyc6 p0 p1 p2 p3 p4 p5 3 = p3 := rfl
theorem c6_4 {α : Type*} {p0 p1 p2 p3 p4 p5 : α} : cyc6 p0 p1 p2 p3 p4 p5 4 = p4 := rfl
theorem c6_5 {α : Type*} {p0 p1 p2 p3 p4 p5 : α} : cyc6 p0 p1 p2 p3 p4 p5 5 = p5 := rfl

/- Positive facts (names are used by the cell proofs): the strict-convexity table of the screen quadrilateral
`(q, c̄', b̄', q')` with `ā` on `(q, c̄')` (Lemma G′), and products of the three side signs `p1 p3 p4 > 0` with the
depth coefficients of the corner-split and side lemmas. -/
set_option hygiene false in
macro "kfacts" : tactic => `(tactic| (
  have hα1' : (0:ℝ) < α1 - 1 := by linarith
  have hγ4' : (0:ℝ) < α4 + α1 * (γ4 - 1) := by nlinarith [mul_pos hα4 hβ1]
  have hγ4'' : (0:ℝ) < α4 + γ4 - 1 := by nlinarith [mul_pos hα4 hβ1, mul_pos hα1' hγ4]
  have hab : (0:ℝ) < α1 + β1 - 1 := by linarith
  have oA := mul_pos (mul_pos (mul_pos hr hha) hα1pos) hγ4
  have oB := mul_pos (mul_pos hr hha) hγ4'
  have oC := mul_pos (mul_pos hr hha) hα4
  have oD := mul_pos (mul_pos hr hha) hα1pos
  have oE := mul_pos (mul_pos hr hha) hα1'
  have oF := mul_pos (mul_pos hr hha) hγ4''
  have oG := mul_pos hr hha
  have oH := mul_pos (mul_pos hr hha) hγ4
  have oI := mul_pos (mul_pos (mul_pos hr hha) hα1') hγ4
  have f1 := mul_pos hν hp1
  have f2 := mul_pos (mul_pos hν hα1pos) hp1
  have f3 := mul_pos (mul_pos hν hα1') hp1
  have f4 := mul_pos (mul_pos hν hβ1) hp1
  have f5 := mul_pos (mul_pos hν hab) hp1
  have f6 := mul_pos hν hp3
  have f7 := mul_pos hν hp4
  have g1 := mul_pos (mul_pos hβ6 hν) hp1
  have g2 := mul_pos (mul_pos (mul_pos hβ6 hν) hα1pos) hp1
  have g3 := mul_pos (mul_pos hβ6 hν) hp3
  have g4 := mul_pos (mul_pos hβ6 hν) hp4))

end K
end Type08Sp
end Minimality
