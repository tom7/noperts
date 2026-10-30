module

public import Minimality.Type08S.P2H8

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H11: Lemma E (iii) (D6) as a culJ determinant inequality — proved on every `Norm08` shape

In culJ coordinates (`a = e₁`, `b = e₂`, `c = e₃`, `d = 0`, `a' = (0, β6, γ6)`, `b' = (α4, 0, γ4)`,
`c' = (α1, β1, 0)`, `θ = (α1, β1, α4, γ4, β6, γ6)`):
* `K_b`, `K_2` (plane `c b' c'`, points `b`, `d`): the two determinants are `gWa` and `-α4 β1`;
* `K_c` (plane `b c' b'`, points `c`, `a'`): `gWa` and `α1 γ4 (1 - β6) - α1 γ6 + α4 γ6 (1 - β1)`, the negative of
  a `common08` entry.
So the products are strictly negative on `Norm08` (no region hypothesis needed); `x ∉ Π'` is automatic too.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 1000000 in
theorem lemE_all {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    LemE3 a' c b c' b' ∧ LemE3 d b c b' c' ∧ LemE3 b d c' b' c := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  have hS : ∀ i, pts08 a a' b b' c c' d i = nfShape08 o E₁ E₂ E₃ θ i := fun i => by rw [hpts]
  have ha' : a' = nfShape08 o E₁ E₂ E₃ θ 1 := by simpa [pts08] using hS 1
  have hb : b = nfShape08 o E₁ E₂ E₃ θ 2 := by simpa [pts08] using hS 2
  have hb' : b' = nfShape08 o E₁ E₂ E₃ θ 3 := by simpa [pts08] using hS 3
  have hc : c = nfShape08 o E₁ E₂ E₃ θ 4 := by simpa [pts08] using hS 4
  have hc' : c' = nfShape08 o E₁ E₂ E₃ θ 5 := by simpa [pts08] using hS 5
  have hd : d = nfShape08 o E₁ E₂ E₃ θ 6 := by simpa [pts08] using hS 6
  obtain ⟨p0, p1, p2, p3, p4, p5, e1', e2', e3', ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have hD2 : 0 ≤ det3 E₁ E₂ E₃ * det3 E₁ E₂ E₃ := mul_self_nonneg _
  unfold LemE3
  rw [ha', hb, hb', hc, hc', hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [det3_nfd, det3_nfd]
    simp only [ddet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]
    have k : 0 < (-(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2)) *
        (-(θ 0) * (θ 3) + (θ 0) * (θ 3) * (θ 4) + (θ 0) * (θ 5) + (θ 1) * (θ 2) * (θ 5) - (θ 2) * (θ 5)) :=
      mul_pos ga (by linarith)
    nlinarith [mul_nonneg hD2 k.le]
  · rw [det3_nfd, det3_nfd]
    simp only [ddet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]
    have k : 0 < (-(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2)) * (θ 1 * θ 2) :=
      mul_pos ga (mul_pos p1 p2)
    nlinarith [mul_nonneg hD2 k.le]
  · rw [det3_nfd, det3_nfd]
    simp only [ddet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]
    have k : 0 < (-(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2)) * (θ 1 * θ 2) :=
      mul_pos ga (mul_pos p1 p2)
    nlinarith [mul_nonneg hD2 k.le]

end Type08Sp
end Minimality
