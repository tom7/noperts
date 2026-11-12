module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Cycle `a, d, b, a', b'` in the frame `(b-d, c-d, a-c')`, with `w = 1/(α1-1)`, `β6 = 1+k`, `γ4 = 1+g`,
`α4 = 1 + (1+g) k`. -/
def k22z1c1bY (w k g : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-w, 0, -w), (0, 0, 0), (1, 0, 0), (1 + k, 1, 0),
    (-(1 + (1 + g) * k) * w, 1 + g, -(1 + (1 + g) * k) * w)]

theorem k22z1c1bY_0 : k22z1c1bY w k g 0 = (-w, 0, -w) := rfl
theorem k22z1c1bY_1 : k22z1c1bY w k g 1 = (0, 0, 0) := rfl
theorem k22z1c1bY_2 : k22z1c1bY w k g 2 = (1, 0, 0) := rfl
theorem k22z1c1bY_3 : k22z1c1bY w k g 3 = (1 + k, 1, 0) := rfl
theorem k22z1c1bY_4 : k22z1c1bY w k g 4 = (-(1 + (1 + g) * k) * w, 1 + g, -(1 + (1 + g) * k) * w) := rfl

theorem k22z1c1bY_inj {w k g : ℝ} (hw : 0 < w) (hk : 0 < k) (hg : 0 ≤ g) :
    ∀ i j, k22z1c1bY w k g i = k22z1c1bY w k g j → i = j := by
  intro i j h
  have h1 := mul_pos hw hk
  have h2 : 0 ≤ g * k := mul_nonneg hg hk.le
  have h3 : 0 ≤ g * k * w := mul_nonneg h2 hw.le
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k22z1c1bY_0, k22z1c1bY_1, k22z1c1bY_2, k22z1c1bY_3, k22z1c1bY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k22z1c1b_tsc {D w k g v1 v2 : ℝ} (hD : 0 < D) (hw : 0 < w) (hk : 0 < k) (hg : 0 ≤ g)
    (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k22z1c1bY w k g (i + 1) - k22z1c1bY w k g i) (k22z1c1bY w k g j - k22z1c1bY w k g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (-w, 0, -w - 1)], ∀ i : ZMod 5,
      TSc D (k22z1c1bY w k g (i + 1) - k22z1c1bY w k g i) (t - k22z1c1bY w k g i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have m1 : ∀ x : ℝ, 0 < x → 0 < D * x := fun x hx => mul_pos hD hx
  have m0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ D * x := fun x hx => mul_nonneg hD.le hx
  have pw := hw
  have pk := hk
  have pwk := mul_pos hw hk
  have pgk := mul_nonneg hg hk.le
  have pgw := mul_nonneg hg hw.le
  have pgwk := mul_nonneg pgk hw.le
  have pgg := mul_nonneg hg hg
  have pggk := mul_nonneg pgg hk.le
  have pggw := mul_nonneg pgg hw.le
  have pggwk := mul_nonneg pggk hw.le
  have pww := mul_pos hw hw
  have pwwk := mul_pos pww hk
  have pwkk := mul_pos pwk hk
  have pkk := mul_pos hk hk
  have pgkk := mul_nonneg pgk hk.le
  have pgwkk := mul_nonneg pgwk hk.le
  have pggwkk := mul_nonneg pggwk hk.le
  have pgkkw := mul_nonneg pgkk hw.le
  have pgwwk := mul_nonneg pgwk hw.le
  have pggwwk := mul_nonneg pggwk hw.le
  have pgww := mul_nonneg pgw hw.le
  have pv1 := hv1
  have pv2 := hv2
  have pv1g := mul_nonneg hv1.le hg
  have pv2w := mul_pos hv2 hw
  have pv2wk := mul_pos pv2w hk
  have pv2wg := mul_nonneg pv2w.le hg
  have pv2wkg := mul_nonneg pv2wk.le hg
  have pv2wgg := mul_nonneg pv2wg hg
  have pv2wkgg := mul_nonneg pv2wkg hg
  have pv2k := mul_pos hv2 hk
  have pv2kg := mul_nonneg pv2k.le hg
  have pv1k := mul_pos hv1 hk
  have pv1kg := mul_nonneg pv1k.le hg
  have pv1w := mul_pos hv1 hw
  have pv1wk := mul_pos pv1w hk
  have pv1wg := mul_nonneg pv1w.le hg
  have pv1wkg := mul_nonneg pv1wk.le hg
  have pv2g := mul_nonneg hv2.le hg
  have pv1gg := mul_nonneg pv1g hg
  have pv2gg := mul_nonneg pv2g hg
  have H1 := m1 _ pw
  have H2 := m1 _ pk
  have H3 := m1 _ pwk
  have H4 := m0 _ pgk
  have H5 := m0 _ pgw
  have H6 := m0 _ pgwk
  have H7 := m0 _ pgg
  have H8 := m0 _ pggk
  have H9 := m0 _ pggw
  have H10 := m0 _ pggwk
  have H11 := m1 _ pww
  have H12 := m1 _ pwwk
  have H13 := m1 _ pwkk
  have H14 := m1 _ pkk
  have H15 := m0 _ pgkk
  have H16 := m0 _ pgwkk
  have H17 := m0 _ pggwkk
  have H18 := m0 _ pgkkw
  have H19 := m0 _ pgwwk
  have H20 := m0 _ pggwwk
  have H21 := m0 _ pgww
  have H22 := m1 _ pv1
  have H23 := m1 _ pv2
  have H24 := m0 _ pv1g
  have H25 := m1 _ pv2w
  have H26 := m1 _ pv2wk
  have H27 := m0 _ pv2wg
  have H28 := m0 _ pv2wkg
  have H29 := m0 _ pv2wgg
  have H30 := m0 _ pv2wkgg
  have H31 := m1 _ pv2k
  have H32 := m0 _ pv2kg
  have H33 := m1 _ pv1k
  have H34 := m0 _ pv1kg
  have H35 := m1 _ pv1w
  have H36 := m1 _ pv1wk
  have H37 := m0 _ pv1wg
  have H38 := m0 _ pv1wkg
  have H39 := m0 _ pv2g
  have H40 := m0 _ pv1gg
  have H41 := m0 _ pv2gg
  have H0 := hD
  have H42 := m0 _ pggwkk
  have H43 := m0 _ hg
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22z1c1bY_0, k22z1c1bY_1, k22z1c1bY_2,
          k22z1c1bY_3, k22z1c1bY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; linarith)
         | (right; refine ⟨by ring, by linarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases hg.eq_or_lt with h0 | hpos
    · subst h0
      have q3 := m1 _ (mul_pos pv2wk hk)
      rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22z1c1bY_0, k22z1c1bY_1, k22z1c1bY_2,
            k22z1c1bY_3, k22z1c1bY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; linarith)
         | (right; refine ⟨by ring, by linarith⟩))
    · have q1 := mul_pos hD hpos
      have q2 := mul_pos (mul_pos hD hpos) hk
      have q3 := m1 _ (mul_pos pv2wk hk)
      rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22z1c1bY_0, k22z1c1bY_1, k22z1c1bY_2,
            k22z1c1bY_3, k22z1c1bY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; linarith)
         | (right; refine ⟨by ring, by linarith⟩))

end C2
end Type08Sp
end Minimality
