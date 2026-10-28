module

public import Minimality.Type08S.G6H5

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 0 in
/-- Real core of the H2 selection: depths `b = z0+n`, `c = z0+q`, `c' = z0+X1+β1 n`, `b' = z0+X4+q` (`X1 = α1 p`, `X4 = α4 p` same strict sign),
`a' = z0+β6 n+q`, `d = z0` (`0<n`, `0<β1<1`, `0<β6`).  At most one corner polygon robust forces
two ties at `b' = c'`. -/
theorem h2_real {z0 n q X1 X4 β1 β6 : ℝ}
    (hs : (X4 = 0 ∧ X1 = 0) ∨ (0 < X4 ∧ 0 < X1) ∨ (X4 < 0 ∧ X1 < 0)) (hn : 0 < n) (hb1 : 0 < β1) (hb11 : β1 < 1) (hb6 : 0 < β6) :
    let zb := z0 + n; let zc := z0 + q; let zc' := z0 + X1 + β1 * n; let zb' := z0 + X4 + q
    let za' := z0 + β6 * n + q
    (¬ Sep zb zb' zc zc' ∧ ¬ Sep z0 zb' zc zc') ∨ (¬ Sep zb zb' zc zc' ∧ ¬ Sep zb zb' za' zc') ∨
    (¬ Sep zb zb' zc zc' ∧ ¬ Sep z0 zb' za' zc') ∨ (¬ Sep z0 zb' zc zc' ∧ ¬ Sep zb zb' za' zc') ∨
    (¬ Sep z0 zb' zc zc' ∧ ¬ Sep z0 zb' za' zc') ∨ (¬ Sep zb zb' za' zc' ∧ ¬ Sep z0 zb' za' zc') ∨
    (zb' = zc' ∧ (zb' = zc ∨ zb' = za' ∨ zc' = zb)) := by
  intro zb zc zc' zb' za'
  have p1 : 0 < β1 * n := mul_pos hb1 hn
  have p2 : 0 < β6 * n := mul_pos hb6 hn
  have p3 : 0 < (1 - β1) * n := mul_pos (by linarith) hn
  rcases hs with ⟨hs4, hs1⟩ | ⟨hs4, hs1⟩ | ⟨hs4, hs1⟩
  all_goals
    by_cases s1 : Sep zb zb' zc zc'
    · by_cases s2 : Sep z0 zb' zc zc'
      · right; right; right; right; right; right
        simp only [zb, zc, zc', zb', Sep, max_le_iff, le_min_iff] at s1 s2
        rcases s1 with ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ | ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ <;>
        rcases s2 with ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ | ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ <;>
        first
          | (exfalso; linarith)
          | (refine ⟨by linarith, Or.inl (by linarith)⟩)
      · by_cases sX : Sep zb zb' za' zc'
        · by_cases s2a : Sep z0 zb' za' zc'
          · right; right; right; right; right; right
            simp only [zb, zc, zc', zb', za', Sep, max_le_iff, le_min_iff] at s1 sX s2a
            rcases s1 with ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ | ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ <;>
            rcases sX with ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ | ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ <;>
            rcases s2a with ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩ | ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩ <;>
            first
              | (exfalso; linarith)
              | (refine ⟨by linarith, Or.inr (Or.inl (by linarith))⟩)
              | (refine ⟨by linarith, Or.inr (Or.inr (by linarith))⟩)
          · tauto
        · tauto
    · by_cases s2 : Sep z0 zb' zc zc'
      · by_cases sX : Sep zb zb' za' zc'
        · exfalso
          simp only [zb, zc, zc', zb', za', Sep, max_le_iff, le_min_iff] at s2 sX
          rcases s2 with ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ | ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ <;>
          rcases sX with ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩ | ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩ <;> linarith
        · tauto
      · tauto

end Type08Sp
end Minimality
