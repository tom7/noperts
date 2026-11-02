module

public import Minimality.Type08S.C2K17BA

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Pentagon with the chain `z4 < z3 < z2 < z1` and `z0 < z1` (peak at index 1). -/
theorem k17b2_pent_uni2 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h1 : z 4 < z 3) (h2 : z 3 < z 2) (h3 : z 2 < z 1) (h4 : z 0 < z 1) : LexUni z w := by
  have n0 : (-((0 : ZMod 5) + 1)) = 4 := by decide
  have n1 : (-((1 : ZMod 5) + 1)) = 3 := by decide
  have n2 : (-((2 : ZMod 5) + 1)) = 2 := by decide
  have n3 : (-((3 : ZMod 5) + 1)) = 1 := by decide
  have n4 : (-((4 : ZMod 5) + 1)) = 0 := by decide
  have key : LexUni (fun i => z (-i)) (fun i => w (-i)) := by
    refine lexUni_unshift1 ?_
    refine k17b_pent_uni _ _ ?_ ?_ ?_ ?_ ?_
    · intro i j e1 e2
      have := hinj _ _ e1 e2
      have := neg_injective this
      exact add_right_cancel this
    · simpa only [n0, n1] using h1
    · simpa only [n1, n2] using h2
    · simpa only [n2, n3] using h3
    · simpa only [n4, n3] using h4
  simpa [neg_neg] using lexUni_neg key

/-- Rule 2 cycle `(a, c', b, a', b')` in the frame `(b-a, b'-a, c'-a)` based at `a`. -/
def k17b2Cy2 (xA yA zA : ℝ) : ZMod 5 → ℝ × ℝ × ℝ := ![(0, 0, 0), (0, 0, 1), (1, 0, 0), (xA, yA, zA), (0, 1, 0)]

theorem k17b2Cy2_0 : k17b2Cy2 xA yA zA 0 = (0, 0, 0) := rfl
theorem k17b2Cy2_1 : k17b2Cy2 xA yA zA 1 = (0, 0, 1) := rfl
theorem k17b2Cy2_2 : k17b2Cy2 xA yA zA 2 = (1, 0, 0) := rfl
theorem k17b2Cy2_3 : k17b2Cy2 xA yA zA 3 = (xA, yA, zA) := rfl
theorem k17b2Cy2_4 {xA yA zA : ℝ} : k17b2Cy2 xA yA zA 4 = (0, 1, 0) := rfl

theorem k17b2Cy2_inj {xA yA zA : ℝ} (hxA : 1 < xA) (hyA : 0 < yA) :
    ∀ i j : ZMod 5, k17b2Cy2 xA yA zA i = k17b2Cy2 xA yA zA j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17b2Cy2_0, k17b2Cy2_1, k17b2Cy2_2, k17b2Cy2_3, k17b2Cy2_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 6400000 in
theorem k17b2_p2_tsc {xA yA zA yc zc xd zd v1 v2 : ℝ} (hxA : 1 < xA) (hyA : 0 < yA)
    (hyc : 0 < yc) (hyc1 : yc < 1) (hcin : 0 < xA * (1 - yc) + yA - 1)
    (hxd : 0 < xd) (hxd1 : xd < 1) (hzd : zd < 0) (hv1 : v1 < 0) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17b2Cy2 xA yA zA (i + 1) - k17b2Cy2 xA yA zA i) (k17b2Cy2 xA yA zA j - k17b2Cy2 xA yA zA i) (v1, v2, 0)) ∧
    (∀ p ∈ [((1 : ℝ), yc, zc), (xd, (0 : ℝ), zd)], ∀ i : ZMod 5,
      TSc 1 (k17b2Cy2 xA yA zA (i + 1) - k17b2Cy2 xA yA zA i) (p - k17b2Cy2 xA yA zA i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have a1 : 0 < xA - 1 := by linarith
  have a2 : 0 < 1 - yc := by linarith
  have a3 : 0 < 1 - xd := by linarith
  have a4 : 0 < -zd := by linarith
  have a5 : 0 < -v1 := by linarith
  have p1 := mul_pos hyA a1
  have p2 := mul_pos hyc a1
  have p3 := mul_pos hyA hyc
  have p4 := mul_pos hyA hxd
  have p5 := mul_pos hyA a3
  have p6 := mul_pos hxd a1
  have p7 := mul_pos hyc hv2
  have p8 := mul_pos hyc a5
  have p9 := mul_pos hxd hv2
  have p10 := mul_pos a1 hv2
  have p11 := mul_pos a1 a5
  have p12 := mul_pos hyA hv2
  have p13 := mul_pos hyA a5
  have p14 := mul_pos hxd a2
  have p15 := mul_pos a3 hv2
  have p16 := mul_pos a4 hv2
  have p17 := mul_pos a3 a1
  have p18 := mul_pos hyA a2
  have p19 := mul_pos (mul_pos hyA a3) hxd
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17b2Cy2_0, k17b2Cy2_1, k17b2Cy2_2, k17b2Cy2_3, k17b2Cy2_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro p hp i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17b2Cy2_0, k17b2Cy2_1, k17b2Cy2_2, k17b2Cy2_3, k17b2Cy2_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))


set_option maxHeartbeats 3200000 in
theorem k17b2_p2_frame (V : Finset ℝ³) (P Q R d0 : ℝ³) (hΔ : det3 P Q R ≠ 0) {xA yA zA yc zc xd zd : ℝ}
    (hxA : 1 < xA) (hyA : 0 < yA) (hyc : 0 < yc) (hyc1 : yc < 1) (hcin : 0 < xA * (1 - yc) + yA - 1)
    (hxd : 0 < xd) (hxd1 : xd < 1) (hzd : zd < 0)
    (hmem : ∀ i, fpoint P Q R d0 (k17b2Cy2 xA yA zA i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d0 (0, 0, 0) ∨ y = fpoint P Q R d0 (0, 0, 1) ∨
      y = fpoint P Q R d0 (1, 0, 0) ∨ y = fpoint P Q R d0 (xA, yA, zA) ∨ y = fpoint P Q R d0 (0, 1, 0) ∨
      y = fpoint P Q R d0 (1, yc, zc) ∨ y = fpoint P Q R d0 (xd, 0, zd))
    (h43 : ⟪fpoint P Q R d0 (0, 1, 0), R⟫ < ⟪fpoint P Q R d0 (xA, yA, zA), R⟫)
    (h32 : ⟪fpoint P Q R d0 (xA, yA, zA), R⟫ < ⟪fpoint P Q R d0 (1, 0, 0), R⟫)
    (h21 : ⟪fpoint P Q R d0 (1, 0, 0), R⟫ < ⟪fpoint P Q R d0 (0, 0, 1), R⟫)
    (h01 : ⟪fpoint P Q R d0 (0, 0, 0), R⟫ < ⟪fpoint P Q R d0 (0, 0, 1), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d0 hΔ (k := 5) (by norm_num) (k17b2Cy2 xA yA zA)
    (k17b2Cy2_inj hxA hyA) hmem
    [((1 : ℝ), yc, zc), (xd, (0 : ℝ), zd)] ?_
    (u1 := -1) (u2 := 1) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ 0 < v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by norm_num, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_neg, mul_one]
    linarith
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k17b2_p2_tsc hxA hyA hyc hyc1 hcin hxd hxd1 hzd hv1 hv2
  · intro v1 v2 _ hL
    refine k17b2_pent_uni2 _ _ hL ?_ ?_ ?_ ?_
    · simpa only [k17b2Cy2_4, k17b2Cy2_3] using h43
    · simpa only [k17b2Cy2_3, k17b2Cy2_2] using h32
    · simpa only [k17b2Cy2_2, k17b2Cy2_1] using h21
    · simpa only [k17b2Cy2_0, k17b2Cy2_1] using h01

set_option maxHeartbeats 12800000 in
/-- **K6M2 rule 2** (view `L03 = c' - a`, cell `(a, c', b, a', b')`, a and c' tie on screen, resolved by the tilt):
the θ-only hull literal `H' > 0` and the depth literals `b > a'`, `a' > b'`, `c' > b` at `V = c' - a`. -/
theorem k17b2_r2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hH : α1 * β1 < (α1 - 1) * (β1 - 1) * (β6 + γ6) + γ6 * (α1 + β1 - 1))
    (h1 : 0 < ⟪b - a', c' - a⟫) (h2 : 0 < ⟪a' - b', c' - a⟫) (h3 : 0 < ⟪c' - b, c' - a⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = d + p := ⟨a - d, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = d + q := ⟨b - d, by abel⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = d + r := ⟨c - d, by abel⟩
  simp only [add_sub_cancel_left] at hdet hc' hb' ha'
  subst hc' hb' ha'
  have hα0 : 0 < α1 := by linarith
  have hβ0 : 0 < β1 := by linarith
  have hσ : 0 < β6 + γ6 - 1 := by linarith
  have hS : 0 < α1 + β1 - 1 := by linarith
  have hα00 : α1 ≠ 0 := hα0.ne'
  have hβ00 : β1 ≠ 0 := hβ0.ne'
  have hS0 : α1 + β1 - 1 ≠ 0 := hS.ne'
  set a : ℝ³ := d + p with hadef
  set Rv : ℝ³ := (d + α1 • p + β1 • q) - a with hRv
  set P : ℝ³ := (d + q) - a with hP
  set Q : ℝ³ := (d + α1 • p + β1 • r) - a with hQ
  have hΔ : det3 P Q Rv ≠ 0 := by
    have e : det3 P Q Rv = (α1 + β1 - 1) * β1 * det3 p q r := by
      simp only [hP, hQ, hRv, hadef, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (mul_ne_zero hS0 hβ00) hdet
  set S : ℝ := α1 + β1 - 1 with hSdef
  have hS0' : α1 + β1 - 1 ≠ 0 := hS.ne'
  have hS0'' : -1 + β1 + α1 ≠ 0 := by intro h; apply hS0'; linarith
  set xA : ℝ := (β1 + (β6 + γ6) * (α1 - 1)) / S with hxA
  set yA : ℝ := γ6 / β1 with hyA
  set zA : ℝ := (β6 - 1) / S - γ6 * (α1 - 1) / (β1 * S) with hzA
  have eA : fpoint P Q Rv a (0, 0, 0) = a := by simp [fpoint, fcomb]
  have eC' : fpoint P Q Rv a (0, 0, 1) = d + α1 • p + β1 • q := by simp only [fpoint, fcomb, hRv]; module
  have eB : fpoint P Q Rv a (1, 0, 0) = d + q := by simp only [fpoint, fcomb, hP]; module
  have eB' : fpoint P Q Rv a (0, 1, 0) = d + α1 • p + β1 • r := by simp only [fpoint, fcomb, hQ]; module
  have eA' : fpoint P Q Rv a (xA, yA, zA) = d + β6 • q + γ6 • r := by
    simp only [fpoint, fcomb, hP, hQ, hRv, hadef, hxA, hyA, hzA, hSdef]
    match_scalars <;> field_simp <;> ring
  have eC : fpoint P Q Rv a (1, 1 / β1, -(1 / β1)) = d + r := by
    simp only [fpoint, fcomb, hP, hQ, hRv, hadef, hSdef]
    match_scalars <;> field_simp <;> ring
  have eD : fpoint P Q Rv a (β1 / S, 0, -(1 / S)) = d := by
    simp only [fpoint, fcomb, hP, hQ, hRv, hadef, hSdef]
    match_scalars <;> field_simp <;> ring
  have hσ1 : 0 < β6 + γ6 := by linarith
  have hxA1 : 1 < xA := by
    rw [hxA, lt_div_iff₀ hS]; simp only [hSdef]; nlinarith [mul_pos (sub_pos.2 hα1) hσ]
  have hyA0 : 0 < yA := by rw [hyA]; positivity
  have hb1 : 1 / β1 < 1 := by rw [div_lt_one hβ0]; exact hβ1
  have hb0 : 0 < 1 / β1 := by positivity
  have hcin : 0 < xA * (1 - 1 / β1) + yA - 1 := by
    have e : xA * (1 - 1 / β1) + yA - 1 =
        ((α1 - 1) * (β1 - 1) * (β6 + γ6) + γ6 * (α1 + β1 - 1) - α1 * β1) / (β1 * S) := by
      simp only [hxA, hyA, hSdef]; field_simp; ring
    rw [e]; apply div_pos _ (by positivity); linarith
  have hxd0 : 0 < β1 / S := by positivity
  have hxd1 : β1 / S < 1 := by rw [div_lt_one hS]; simp only [hSdef]; linarith
  have hzd : -(1 / S) < 0 := by have : 0 < 1 / S := by positivity
                                linarith
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, Rv⟫ → ⟪X, Rv⟫ < ⟪Y, Rv⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have hRne : Rv ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hRR : 0 < ⟪Rv, Rv⟫ := real_inner_self_pos.mpr hRne
  have h43 : ⟪d + α1 • p + β1 • r, Rv⟫ < ⟪d + β6 • q + γ6 • r, Rv⟫ := inner_lt _ _ h2
  have h32 : ⟪d + β6 • q + γ6 • r, Rv⟫ < ⟪d + q, Rv⟫ := inner_lt _ _ h1
  have h21 : ⟪d + q, Rv⟫ < ⟪d + α1 • p + β1 • q, Rv⟫ := inner_lt _ _ h3
  have h01 : ⟪a, Rv⟫ < ⟪d + α1 • p + β1 • q, Rv⟫ := inner_lt _ _ hRR
  refine ⟨Rv, hRne, ?_⟩
  refine k17b2_p2_frame (zA := zA) (zc := -(1 / β1)) (V8 a (d + β6 • q + γ6 • r) (d + q) (d + α1 • p + β1 • r) (d + r) (d + α1 • p + β1 • q) d)
    P Q Rv a hΔ hxA1 hyA0 hb0 hb1 hcin hxd0 hxd1 hzd ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17b2Cy2_0, eA]; simp [V8]
    · simp only [k17b2Cy2_1, eC']; simp [V8]
    · simp only [k17b2Cy2_2, eB]; simp [V8]
    · simp only [k17b2Cy2_3, eA']; simp [V8]
    · simp only [k17b2Cy2_4, eB']; simp [V8]
  · intro y hy
    rw [eA, eC', eB, eA', eB', eC, eD]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eB', eA']; exact h43
  · rw [eA', eB]; exact h32
  · rw [eB, eC']; exact h21
  · rw [eA, eC']; exact h01

end C2
end Type08Sp
end Minimality
