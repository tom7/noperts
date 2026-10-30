module

public import Minimality.Type08S.P2RS0

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H2: robust 4-cycles, the order facts (sp08d Lemma 2.1 for 4-corner rims)

`Rob4 z0 z1 z2 z3`: the real content of `IsRobustUnimodal (quad z0 z1 z2 z3)` (no two weak peaks on the
diagonals, no three equal entries, no level edge inside a monotone run).  `rob4_of` extracts it.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Unpacked robustness of the 4-cycle `(z0, z1, z2, z3)`. -/
structure Rob4 (z0 z1 z2 z3 : ℝ) : Prop where
  pk1 : ¬ (z1 < z0 ∧ z1 < z2 ∧ z3 < z0 ∧ z3 < z2)
  pk2 : ¬ (z0 < z1 ∧ z0 < z3 ∧ z2 < z1 ∧ z2 < z3)
  t012 : ¬ (z0 = z1 ∧ z1 = z2)
  t013 : ¬ (z0 = z1 ∧ z1 = z3)
  t023 : ¬ (z0 = z2 ∧ z2 = z3)
  t123 : ¬ (z1 = z2 ∧ z2 = z3)
  -- level edge (z1,z2) between z0 and z3
  l0 : z1 = z2 → ¬ (z0 < z1 ∧ z2 < z3) ∧ ¬ (z1 < z0 ∧ z3 < z2)
  -- level edge (z2,z3) between z1 and z0
  l1 : z2 = z3 → ¬ (z1 < z2 ∧ z3 < z0) ∧ ¬ (z2 < z1 ∧ z0 < z3)
  -- level edge (z3,z0) between z2 and z1
  l2 : z3 = z0 → ¬ (z2 < z3 ∧ z0 < z1) ∧ ¬ (z3 < z2 ∧ z1 < z0)
  -- level edge (z0,z1) between z3 and z2
  l3 : z0 = z1 → ¬ (z3 < z0 ∧ z1 < z2) ∧ ¬ (z0 < z3 ∧ z2 < z1)

theorem rob4_of {z0 z1 z2 z3 : ℝ} (h : IsRobustUnimodal (quad z0 z1 z2 z3)) : Rob4 z0 z1 z2 z3 := by
  have q0 : quad z0 z1 z2 z3 0 = z0 := rfl
  have q1 : quad z0 z1 z2 z3 1 = z1 := rfl
  have q2 : quad z0 z1 z2 z3 2 = z2 := rfl
  have q3 : quad z0 z1 z2 z3 3 = z3 := rfl
  have pk := fun (B : ZMod 4) => h.noPeaks B 0 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have lv := fun (B : ZMod 4) => h.noLevelRun B 0 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e : ∀ (B : ZMod 4) (n : ℕ), B + (n : ZMod 4) = B + (n : ZMod 4) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := pk 0; simpa [q0, q1, q2, q3] using this
  · have := pk 1
    have a1 : (1 : ZMod 4) + 1 = 2 := by decide
    have a2 : (1 : ZMod 4) + 2 = 3 := by decide
    have a3 : (1 : ZMod 4) + 3 = 0 := by decide
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, a1, a2, a3, q0, q1, q2, q3] at this
    intro ⟨h1, h2, h3, h4⟩; exact this ⟨h3, h4, h1, h2⟩
  · intro ⟨h1, h2⟩; exact h.noTriple 0 1 2 (by decide) (by decide) (by decide) h1 h2
  · intro ⟨h1, h2⟩; exact h.noTriple 0 1 3 (by decide) (by decide) (by decide) h1 h2
  · intro ⟨h1, h2⟩; exact h.noTriple 0 2 3 (by decide) (by decide) (by decide) h1 h2
  · intro ⟨h1, h2⟩; exact h.noTriple 1 2 3 (by decide) (by decide) (by decide) h1 h2
  · intro he; have := lv 0; simpa [q0, q1, q2, q3] using this he
  · intro he
    have := lv 1
    have a1 : (1 : ZMod 4) + 1 = 2 := by decide
    have a2 : (1 : ZMod 4) + 2 = 3 := by decide
    have a3 : (1 : ZMod 4) + 3 = 0 := by decide
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, a1, a2, a3, q0, q1, q2, q3] at this
    exact this he
  · intro he
    have := lv 2
    have a1 : (2 : ZMod 4) + 1 = 3 := by decide
    have a2 : (2 : ZMod 4) + 2 = 0 := by decide
    have a3 : (2 : ZMod 4) + 3 = 1 := by decide
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, a1, a2, a3, q0, q1, q2, q3] at this
    exact this he
  · intro he
    have := lv 3
    have a1 : (3 : ZMod 4) + 1 = 0 := by decide
    have a2 : (3 : ZMod 4) + 2 = 1 := by decide
    have a3 : (3 : ZMod 4) + 3 = 2 := by decide
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero, a1, a2, a3, q0, q1, q2, q3] at this
    exact this he

/-- Robustness is invariant under the depth reflection `z ↦ -z`. -/
theorem Rob4.neg {z0 z1 z2 z3 : ℝ} (h : Rob4 z0 z1 z2 z3) : Rob4 (-z0) (-z1) (-z2) (-z3) := by
  obtain ⟨p1, p2, t1, t2, t3, t4, l0, l1, l2, l3⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨a, b, c, d⟩; exact p2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro ⟨a, b, c, d⟩; exact p1 ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro ⟨a, b⟩; exact t1 ⟨by linarith, by linarith⟩
  · intro ⟨a, b⟩; exact t2 ⟨by linarith, by linarith⟩
  · intro ⟨a, b⟩; exact t3 ⟨by linarith, by linarith⟩
  · intro ⟨a, b⟩; exact t4 ⟨by linarith, by linarith⟩
  · intro he; have := l0 (by linarith)
    exact ⟨fun ⟨a, b⟩ => this.2 ⟨by linarith, by linarith⟩, fun ⟨a, b⟩ => this.1 ⟨by linarith, by linarith⟩⟩
  · intro he; have := l1 (by linarith)
    exact ⟨fun ⟨a, b⟩ => this.2 ⟨by linarith, by linarith⟩, fun ⟨a, b⟩ => this.1 ⟨by linarith, by linarith⟩⟩
  · intro he; have := l2 (by linarith)
    exact ⟨fun ⟨a, b⟩ => this.2 ⟨by linarith, by linarith⟩, fun ⟨a, b⟩ => this.1 ⟨by linarith, by linarith⟩⟩
  · intro he; have := l3 (by linarith)
    exact ⟨fun ⟨a, b⟩ => this.2 ⟨by linarith, by linarith⟩, fun ⟨a, b⟩ => this.1 ⟨by linarith, by linarith⟩⟩

/-! ### Lemma 2.1 for the 4-corner closing `(x, f, r, g)` = `(z0, z1, z2, z3)` -/

/-- (c), top vertex `g` with `z_g` a strict convex combination of `z_x`, `z_f` (or `z_x = z_f = z_g`). -/
theorem rob4_cg {zx zf zr zg s : ℝ} (h : Rob4 zx zf zr zg) (hs0 : 0 < s) (hs1 : s < 1)
    (hz : zx + s * (zf - zx) = zg) :
    (zx - zg) * (zf - zg) < 0 ∧ (zx - zg) * (zr - zg) < 0 := by
  obtain ⟨p1, p2, t1, t2, t3, t4, l0, l1, l2, l3⟩ := h
  rcases lt_trichotomy zx zf with hxf | hxf | hxf
  · have a1 : zx < zg := by nlinarith
    have a2 : zg < zf := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    rcases lt_trichotomy zr zg with hr | hr | hr
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p2
    · exact absurd ⟨by linarith, by linarith⟩ (l1 hr).2
    · nlinarith
  · exact absurd ⟨hxf, by nlinarith⟩ t2
  · have a1 : zg < zx := by nlinarith
    have a2 : zf < zg := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    rcases lt_trichotomy zr zg with hr | hr | hr
    · nlinarith
    · exact absurd ⟨by linarith, by linarith⟩ (l1 hr).1
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p1

/-- (c), top vertex `r`. -/
theorem rob4_cr {zx zf zr zg s : ℝ} (h : Rob4 zx zf zr zg) (hs0 : 0 < s) (hs1 : s < 1)
    (hz : zx + s * (zf - zx) = zr) :
    (zx - zr) * (zf - zr) < 0 ∧ 0 < (zx - zr) * (zg - zr) := by
  obtain ⟨p1, p2, t1, t2, t3, t4, l0, l1, l2, l3⟩ := h
  rcases lt_trichotomy zx zf with hxf | hxf | hxf
  · have a1 : zx < zr := by nlinarith
    have a2 : zr < zf := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    rcases lt_trichotomy zg zr with hr | hr | hr
    · nlinarith
    · exact absurd ⟨by linarith, by linarith⟩ (l1 hr.symm).2
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p2
  · exact absurd ⟨hxf, by nlinarith⟩ t1
  · have a1 : zr < zx := by nlinarith
    have a2 : zf < zr := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    rcases lt_trichotomy zg zr with hr | hr | hr
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p1
    · exact absurd ⟨by linarith, by linarith⟩ (l1 hr.symm).1
    · nlinarith

/-- (d): the top side `[r, g]` crosses the open chord at depth `zc = zx + s (zf - zx)` at the point
`r̄ + s' (ḡ - r̄)`, `0 ≤ s' ≤ 1`.  Then (x above) `zf < zc < zx`, `zr ≤ zc ≤ zg`, `zr < zg`, or the
mirror. -/
theorem rob4_d {zx zf zr zg s s' : ℝ} (h : Rob4 zx zf zr zg) (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 ≤ s') (ht1 : s' ≤ 1) (hz : zx + s * (zf - zx) = zr + s' * (zg - zr)) :
    (zf < zx ∧ zr ≤ zx + s * (zf - zx) ∧ zx + s * (zf - zx) ≤ zg ∧ zr < zg) ∨
    (zx < zf ∧ zg ≤ zx + s * (zf - zx) ∧ zx + s * (zf - zx) ≤ zr ∧ zg < zr) := by
  obtain ⟨p1, p2, t1, t2, t3, t4, l0, l1, l2, l3⟩ := h
  set c := zx + s * (zf - zx) with hc
  -- convexity of the crossing on the top side
  have cv1 : zr ≤ zg → zr ≤ c ∧ c ≤ zg := fun h => ⟨by nlinarith, by nlinarith⟩
  have cv2 : zg ≤ zr → zg ≤ c ∧ c ≤ zr := fun h => ⟨by nlinarith, by nlinarith⟩
  rcases lt_trichotomy zx zf with hxf | hxf | hxf
  · have a1 : zx < c := by nlinarith
    have a2 : c < zf := by nlinarith
    right
    rcases lt_trichotomy zg zr with hg | hg | hg
    · obtain ⟨k1, k2⟩ := cv2 hg.le
      exact ⟨hxf, k1, k2, hg⟩
    · exfalso
      have e1 : zr = c := by rw [hz, hg]; ring
      exact (l1 hg.symm).2 ⟨by linarith, by linarith⟩
    · exfalso
      obtain ⟨k1, k2⟩ := cv1 hg.le
      exact p2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  · exfalso
    have e1 : c = zx := by rw [hc, hxf]; ring
    rcases lt_trichotomy zr zg with hg | hg | hg
    · obtain ⟨k1, k2⟩ := cv1 hg.le
      rcases lt_or_eq_of_le k1 with h1 | h1
      · rcases lt_or_eq_of_le k2 with h2 | h2
        · exact (l3 hxf).2 ⟨by linarith, by linarith⟩
        · exact t2 ⟨hxf, by linarith⟩
      · exact t1 ⟨hxf, by linarith⟩
    · have : zr = c := by rw [hz, hg]; ring
      exact t1 ⟨hxf, by linarith⟩
    · obtain ⟨k1, k2⟩ := cv2 hg.le
      rcases lt_or_eq_of_le k1 with h1 | h1
      · rcases lt_or_eq_of_le k2 with h2 | h2
        · exact (l3 hxf).1 ⟨by linarith, by linarith⟩
        · exact t1 ⟨hxf, by linarith⟩
      · exact t2 ⟨hxf, by linarith⟩
  · have a1 : c < zx := by nlinarith
    have a2 : zf < c := by nlinarith
    left
    rcases lt_trichotomy zr zg with hg | hg | hg
    · obtain ⟨k1, k2⟩ := cv1 hg.le
      exact ⟨hxf, k1, k2, hg⟩
    · exfalso
      have e1 : zr = c := by rw [hz, hg]; ring
      exact (l1 hg).1 ⟨by linarith, by linarith⟩
    · exfalso
      obtain ⟨k1, k2⟩ := cv2 hg.le
      exact p1 ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Chord end at `x`, top vertex `g` (or near end `g`) over `x̄` (`z_g = z_x`): `f`, `r` strictly on one side. -/
theorem rob4_xg {zx zf zr zg : ℝ} (h : Rob4 zx zf zr zg) (hz : zg = zx) : 0 < (zf - zx) * (zr - zx) := by
  obtain ⟨p1, p2, t1, t2, t3, t4, l0, l1, l2, l3⟩ := h
  rcases lt_trichotomy zf zx with hf | hf | hf
  · rcases lt_trichotomy zr zx with hr | hr | hr
    · nlinarith
    · exact absurd ⟨by linarith, by linarith⟩ t3
    · exact absurd ⟨by linarith, by linarith⟩ (l2 (by linarith)).2
  · exact absurd ⟨hf.symm, by linarith⟩ t2
  · rcases lt_trichotomy zr zx with hr | hr | hr
    · exact absurd ⟨by linarith, by linarith⟩ (l2 (by linarith)).1
    · exact absurd ⟨by linarith, by linarith⟩ t3
    · nlinarith

/-- Chord end at `x`, top vertex `r` (or far end `r`) over `x̄` (`z_r = z_x`): `f`, `g` strictly opposite. -/
theorem rob4_xr {zx zf zr zg : ℝ} (h : Rob4 zx zf zr zg) (hz : zr = zx) : (zf - zx) * (zg - zx) < 0 := by
  obtain ⟨p1, p2, t1, t2, t3, t4, l0, l1, l2, l3⟩ := h
  rcases lt_trichotomy zf zx with hf | hf | hf
  · rcases lt_trichotomy zg zx with hg | hg | hg
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p1
    · exact absurd ⟨by linarith, by linarith⟩ t3
    · nlinarith
  · exact absurd ⟨hf.symm, by linarith⟩ t1
  · rcases lt_trichotomy zg zx with hg | hg | hg
    · nlinarith
    · exact absurd ⟨by linarith, by linarith⟩ t3
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p2

/-- Chord end at `x`, `x̄` in the open top side (`z_x` strictly between `z_r`, `z_g`, or all equal):
`f` strictly on `r`'s side of `z_x`. -/
theorem rob4_xside {zx zf zr zg s' : ℝ} (h : Rob4 zx zf zr zg) (ht0 : 0 < s') (ht1 : s' < 1)
    (hz : zx = zr + s' * (zg - zr)) : 0 < (zf - zx) * (zr - zx) := by
  obtain ⟨p1, p2, t1, t2, t3, t4, l0, l1, l2, l3⟩ := h
  rcases lt_trichotomy zr zg with hg | hg | hg
  · have a1 : zr < zx := by nlinarith
    have a2 : zx < zg := by nlinarith
    rcases lt_trichotomy zf zx with hf | hf | hf
    · nlinarith
    · exact absurd ⟨by linarith, by linarith⟩ (l3 hf.symm).2
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p2
  · exact absurd ⟨by nlinarith, by linarith⟩ t3
  · have a1 : zx < zr := by nlinarith
    have a2 : zg < zx := by nlinarith
    rcases lt_trichotomy zf zx with hf | hf | hf
    · exact absurd ⟨by linarith, by linarith, by linarith, by linarith⟩ p1
    · exact absurd ⟨by linarith, by linarith⟩ (l3 hf.symm).1
    · nlinarith

end Type08Sp
end Minimality
