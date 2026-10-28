module

public import Minimality.Type08S.G6B2
public import Minimality.Type08S.G6O

@[expose] public section

set_option autoImplicit true

/-!
# G6' : the order Claim (PROOFS 29.12 case B) from the Gale data

If all four corner polygons at `ℓ` are `Sep` (weakly two-peaked), contradiction: pure reals from
`norm08_coords` (`0 < β1 < γ4`, `0 < β6`, `0 < |u|²`).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem allsep_real {z0 n q A β1 γ4 β6 : ℝ} (hn : 0 < n) (hb1 : 0 < β1) (hb14 : β1 < γ4)
    (hb6 : 0 < β6)
    (h1 : Sep (z0 + n) (z0 + A + γ4 * q) (z0 + q) (z0 + A + β1 * n))
    (h2 : Sep z0 (z0 + A + γ4 * q) (z0 + q) (z0 + A + β1 * n))
    (hX : Sep (z0 + n) (z0 + A + γ4 * q) (z0 + β6 * n + q) (z0 + A + β1 * n)) : False := by
  have p1 : 0 < β1 * n := mul_pos hb1 hn
  have p2 : 0 < β6 * n := mul_pos hb6 hn
  have p3 : 0 < (γ4 - β1) * n := mul_pos (by linarith) hn
  have hγ : 0 < γ4 := by linarith
  unfold Sep at h1 h2 hX
  simp only [max_le_iff, le_min_iff] at h1 h2 hX
  rcases h1 with ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ | ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
  · -- {c,c'} ≤ {b,b'}
    rcases h2 with ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ | ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩
    · -- {c,c'} ≤ {d,b'}: q ≤ 0 but γ4 q ≥ β1 n
      have : β1 * n ≤ γ4 * q := by linarith
      nlinarith
    · -- {d,b'} ≤ {c,c'}: all tied
      rcases hX with ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩ | ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩
      · linarith
      · have hq : q = n := by linarith
        have : γ4 * q = β1 * n := by linarith
        rw [hq] at this
        nlinarith
  · -- {b,b'} ≤ {c,c'}: n ≤ q and γ4 q ≤ β1 n
    have : γ4 * q ≤ β1 * n := by linarith
    nlinarith

theorem allsep_false {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H1 b b' c c' d)
    (h1 : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫)
    (h2 : Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ ⟪c', b - d⟫)
    (hX : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫) : False := by
  obtain ⟨α, β1, γ4, β6, hdet, hc', hb', ha', hα, hb1, hb14, hb6⟩ := norm08_coords N hT hH
  have hu : 0 < ⟪b - d, b - d⟫ := by
    apply real_inner_self_pos.mpr
    intro h
    apply hdet
    have : b - d = 0 := h
    simp [det3_expand, this]
  have e : ∀ x : ℝ³, ⟪x, b - d⟫ = ⟪d, b - d⟫ + ⟪x - d, b - d⟫ := by
    intro x; rw [← inner_add_left]; congr 1; abel
  have ec' : ⟪c', b - d⟫ = ⟪d, b - d⟫ + α * ⟪a - d, b - d⟫ + β1 * ⟪b - d, b - d⟫ := by
    rw [hc']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have eb' : ⟪b', b - d⟫ = ⟪d, b - d⟫ + α * ⟪a - d, b - d⟫ + γ4 * ⟪c - d, b - d⟫ := by
    rw [hb']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have ea' : ⟪a', b - d⟫ = ⟪d, b - d⟫ + β6 * ⟪b - d, b - d⟫ + ⟪c - d, b - d⟫ := by
    rw [ha']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  have eb : ⟪b, b - d⟫ = ⟪d, b - d⟫ + ⟪b - d, b - d⟫ := e b
  have ec : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := e c
  rw [eb, eb', ec, ec'] at h1
  rw [eb', ec, ec'] at h2
  rw [eb, eb', ea', ec'] at hX
  exact allsep_real (A := α * ⟪a - d, b - d⟫) hu hb1 hb14 hb6 (by convert h1 using 2 <;> ring_nf)
    (by convert h2 using 2 <;> ring_nf) (by convert hX using 2 <;> ring_nf)

end Type08Sp
end Minimality
