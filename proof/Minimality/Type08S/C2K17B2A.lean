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

/-- Quad with the depth peak at index 0: `z1 < z0`, `z2 < z0` and the opposite vertex 2 is not a local maximum. -/
theorem k17b2_quad_uni0 (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hba : z 1 < z 0) (hda : z 2 < z 0) (hs : z 2 < z 1 ∨ z 2 < z 3) : LexUni z w := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  refine lexUni_unshift1 ?_
  refine k17b_quad_uni _ _ ?_ ?_ ?_ ?_
  · intro i j h1 h2; exact add_right_cancel (hinj _ _ h1 h2)
  · simpa only [f0, f3] using hba
  · simpa only [f1, f3] using hda
  · simpa only [f1, f0, f2] using hs

/-- Rule 1 cycle `(a, b', a', c')` in the frame `(c'-a', b'-a', R)` based at `a'`: `a = (xa, ya, za)`. -/
def k17b2Cy1 (xa ya za : ℝ) : ZMod 4 → ℝ × ℝ × ℝ := ![(xa, ya, za), (0, 1, 0), (0, 0, 0), (1, 0, 0)]

theorem k17b2Cy1_0 : k17b2Cy1 xa ya za 0 = (xa, ya, za) := rfl
theorem k17b2Cy1_1 : k17b2Cy1 xa ya za 1 = (0, 1, 0) := rfl
theorem k17b2Cy1_2 : k17b2Cy1 xa ya za 2 = (0, 0, 0) := rfl
theorem k17b2Cy1_3 : k17b2Cy1 xa ya za 3 = (1, 0, 0) := rfl

theorem k17b2Cy1_inj {xa ya za : ℝ} (hxa : 0 < xa) (hya : 0 < ya) :
    ∀ i j : ZMod 4, k17b2Cy1 xa ya za i = k17b2Cy1 xa ya za j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17b2Cy1_0, k17b2Cy1_1, k17b2Cy1_2, k17b2Cy1_3] at e1 e2; linarith)

set_option maxHeartbeats 3200000 in
theorem k17b2_q1_tsc {xa ya za xb zb yc zc t zd v1 v2 : ℝ} (hxa : 0 < xa) (hya : 0 < ya) (hs : 1 < xa + ya)
    (hxb : 0 < xb) (hxb1 : xb < 1) (hzb : 0 < zb) (hyc : 0 < yc) (hyc1 : yc < 1) (hzc : 0 < zc)
    (ht : 0 < t) (ht1 : t < 1) (hv1 : v1 < 0) (hv2 : v2 < 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17b2Cy1 xa ya za (i + 1) - k17b2Cy1 xa ya za i) (k17b2Cy1 xa ya za j - k17b2Cy1 xa ya za i) (v1, v2, 0)) ∧
    (∀ p ∈ [(xb, (0 : ℝ), zb), ((0 : ℝ), yc, zc), (t * xa, t * ya, zd)], ∀ i : ZMod 4,
      TSc 1 (k17b2Cy1 xa ya za (i + 1) - k17b2Cy1 xa ya za i) (p - k17b2Cy1 xa ya za i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have s1 : 0 < xa + ya - 1 := by linarith
  have s2 : 0 < 1 - xb := by linarith
  have s3 : 0 < 1 - yc := by linarith
  have s4 : 0 < 1 - t := by linarith
  have p1 := mul_pos hxa hya
  have p2 := mul_pos hxa s2
  have p3 := mul_pos hya s2
  have p4 := mul_pos hxa s3
  have p5 := mul_pos hya s3
  have p6 := mul_pos hxa s4
  have p7 := mul_pos hya s4
  have p8 := mul_pos hxa ht
  have p9 := mul_pos hya ht
  have p10 := mul_pos hzb (neg_pos.2 hv2)
  have p11 := mul_pos hzc (neg_pos.2 hv1)
  have p12 := mul_pos hxb s2
  have p13 := mul_pos hyc s3
  have p14 := mul_pos hxb hya
  have p15 := mul_pos hyc hxa
  have p16 := mul_pos s1 hxb
  have p17 := mul_pos s1 hyc
  have p18 := mul_pos s1 s2
  have p19 := mul_pos s1 s3
  have p20 := mul_pos s1 ht
  have p21 := mul_pos s1 s4
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17b2Cy1_0, k17b2Cy1_1, k17b2Cy1_2, k17b2Cy1_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro p hp i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17b2Cy1_0, k17b2Cy1_1, k17b2Cy1_2, k17b2Cy1_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17b2_q1_frame (V : Finset ℝ³) (P Q R d0 : ℝ³) (hΔ : det3 P Q R ≠ 0) {xa ya za xb zb yc zc t zd : ℝ}
    (hxa : 0 < xa) (hya : 0 < ya) (hs : 1 < xa + ya)
    (hxb : 0 < xb) (hxb1 : xb < 1) (hzb : 0 < zb) (hyc : 0 < yc) (hyc1 : yc < 1) (hzc : 0 < zc)
    (ht : 0 < t) (ht1 : t < 1)
    (hmem : ∀ i, fpoint P Q R d0 (k17b2Cy1 xa ya za i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d0 (xa, ya, za) ∨ y = fpoint P Q R d0 (0, 1, 0) ∨
      y = fpoint P Q R d0 (0, 0, 0) ∨ y = fpoint P Q R d0 (1, 0, 0) ∨ y = fpoint P Q R d0 (xb, 0, zb) ∨
      y = fpoint P Q R d0 (0, yc, zc) ∨ y = fpoint P Q R d0 (t * xa, t * ya, zd))
    (hba : ⟪fpoint P Q R d0 (0, 1, 0), R⟫ < ⟪fpoint P Q R d0 (xa, ya, za), R⟫)
    (hda : ⟪fpoint P Q R d0 (0, 0, 0), R⟫ < ⟪fpoint P Q R d0 (xa, ya, za), R⟫)
    (hss : ⟪fpoint P Q R d0 (0, 0, 0), R⟫ < ⟪fpoint P Q R d0 (0, 1, 0), R⟫ ∨
      ⟪fpoint P Q R d0 (0, 0, 0), R⟫ < ⟪fpoint P Q R d0 (1, 0, 0), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d0 hΔ (k := 4) (by norm_num) (k17b2Cy1 xa ya za)
    (k17b2Cy1_inj hxa hya) hmem
    [(xb, (0 : ℝ), zb), ((0 : ℝ), yc, zc), (t * xa, t * ya, zd)] ?_
    (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by norm_num, ?_⟩
    simp only [mul_zero, add_zero, zero_add, mul_neg, mul_one]
    linarith
  · intro v1 v2 ⟨hv1, hv2⟩
    exact k17b2_q1_tsc hxa hya hs hxb hxb1 hzb hyc hyc1 hzc ht ht1 hv1 hv2
  · intro v1 v2 _ hL
    refine k17b2_quad_uni0 _ _ hL ?_ ?_ ?_
    · simpa only [k17b2Cy1_0, k17b2Cy1_1] using hba
    · simpa only [k17b2Cy1_0, k17b2Cy1_2] using hda
    · simpa only [k17b2Cy1_1, k17b2Cy1_2, k17b2Cy1_3] using hss.symm.symm


set_option maxHeartbeats 12800000 in
/-- **K6M2 rule 1** (view `L46`, cell `(a, b', a', c')`): `R = -α1 (a-d) - (β1-1)(a'-d)`; valid when R0 fails strictly and
the depth literals `a > b'`, `a > a'`, `c' > a'` hold at `R`. -/
theorem k17b2_r1 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hR : (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1) < α1 + β1 - 1)
    (h1 : 0 < ⟪a - b', (-α1) • (a - d) - (β1 - 1) • (a' - d)⟫)
    (h2 : 0 < ⟪a - a', (-α1) • (a - d) - (β1 - 1) • (a' - d)⟫)
    (h3 : 0 < ⟪c' - a', (-α1) • (a - d) - (β1 - 1) • (a' - d)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = d + p := ⟨a - d, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = d + q := ⟨b - d, by abel⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = d + r := ⟨c - d, by abel⟩
  simp only [add_sub_cancel_left] at hdet hc' hb' ha' h1 h2 h3
  subst hc' hb' ha'
  have hα0 : 0 < α1 := by linarith
  have hβ0 : 0 < β1 := by linarith
  have hσ : 0 < β6 + γ6 - 1 := by linarith
  have hS : 0 < α1 + β1 - 1 := by linarith
  have hα00 : α1 ≠ 0 := hα0.ne'
  have hβ00 : β1 ≠ 0 := hβ0.ne'
  have hσ0 : β6 + γ6 - 1 ≠ 0 := hσ.ne'
  have hS0 : α1 + β1 - 1 ≠ 0 := hS.ne'
  set Rv : ℝ³ := (-α1) • p - (β1 - 1) • ((d + β6 • q + γ6 • r) - d) with hRv
  set a' : ℝ³ := d + β6 • q + γ6 • r with ha'def
  set P : ℝ³ := (d + α1 • p + β1 • q) - a' with hP
  set Q : ℝ³ := (d + α1 • p + β1 • r) - a' with hQ
  have hΔ : det3 P Q Rv ≠ 0 := by
    have e : det3 P Q Rv = β1 ^ 2 * (β6 + γ6 - 1) * α1 * det3 p q r := by
      simp only [hP, hQ, hRv, ha'def, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]; ring
    rw [e]; exact mul_ne_zero (by positivity) hdet
  set k : ℝ := 1 / (β1 * (β6 + γ6 - 1)) with hk
  set S : ℝ := α1 + β1 - 1 with hSdef
  set xa : ℝ := S / α1 * k * β6 with hxa
  set ya : ℝ := S / α1 * k * γ6 with hya
  set za : ℝ := S / α1 * k * (β6 + γ6) - 1 / α1 with hza
  set t : ℝ := α1 / S with ht
  set zd : ℝ := k * (β6 + γ6) with hzd
  have eA' : fpoint P Q Rv a' (0, 0, 0) = a' := by simp [fpoint, fcomb]
  have eC' : fpoint P Q Rv a' (1, 0, 0) = d + α1 • p + β1 • q := by simp only [fpoint, fcomb, hP]; module
  have eB' : fpoint P Q Rv a' (0, 1, 0) = d + α1 • p + β1 • r := by simp only [fpoint, fcomb, hQ]; module
  have eB : fpoint P Q Rv a' (1 / β1, 0, 1 / β1) = d + q := by
    simp only [fpoint, fcomb, hP, hQ, hRv, ha'def]
    match_scalars <;> field_simp <;> ring
  have eC : fpoint P Q Rv a' (0, 1 / β1, 1 / β1) = d + r := by
    simp only [fpoint, fcomb, hP, hQ, hRv, ha'def]
    match_scalars <;> field_simp <;> ring
  have eD : fpoint P Q Rv a' (t * xa, t * ya, zd) = d := by
    simp only [fpoint, fcomb, hP, hQ, hRv, ha'def, ht, hxa, hya, hzd, hk]
    match_scalars <;> field_simp <;> ring
  have eA : fpoint P Q Rv a' (xa, ya, za) = d + p := by
    simp only [fpoint, fcomb, hP, hQ, hRv, ha'def, hxa, hya, hza, hk, hSdef]
    match_scalars <;> field_simp <;> ring
  have hk0 : 0 < k := by rw [hk]; positivity
  have hxa0 : 0 < xa := by rw [hxa]; positivity
  have hya0 : 0 < ya := by rw [hya]; positivity
  have hsum : 1 < xa + ya := by
    have e : xa + ya = S * (β6 + γ6) / (α1 * (β1 * (β6 + γ6 - 1))) := by
      simp only [hxa, hya, hk]; field_simp
    rw [e, lt_div_iff₀ (by positivity)]
    simp only [hSdef] at hR ⊢
    nlinarith [hR]
  have hb1 : 1 / β1 < 1 := by rw [div_lt_one hβ0]; exact hβ1
  have hb0 : 0 < 1 / β1 := by positivity
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hS]; simp only [hSdef]; linarith
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, Rv⟫ → ⟪X, Rv⟫ < ⟪Y, Rv⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  have hba : ⟪d + α1 • p + β1 • r, Rv⟫ < ⟪d + p, Rv⟫ := inner_lt _ _ h1
  have hda : ⟪a', Rv⟫ < ⟪d + p, Rv⟫ := inner_lt _ _ h2
  have hss : ⟪a', Rv⟫ < ⟪d + α1 • p + β1 • q, Rv⟫ := inner_lt _ _ h3
  refine ⟨Rv, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17b2_q1_frame (za := za) (zd := zd) (V8 (d + p) a' (d + q) (d + α1 • p + β1 • r) (d + r) (d + α1 • p + β1 • q) d)
    P Q Rv a' hΔ hxa0 hya0 hsum hb0 hb1 hb0 hb0 hb1 hb0 ht0 ht1 ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · simp only [k17b2Cy1_0, eA]; simp [V8]
    · simp only [k17b2Cy1_1, eB']; simp [V8]
    · simp only [k17b2Cy1_2, eA']; simp [V8]
    · simp only [k17b2Cy1_3, eC']; simp [V8]
  · intro y hy
    rw [eA, eB', eA', eC', eB, eC, eD]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eB', eA]; exact hba
  · rw [eA', eA]; exact hda
  · right; rw [eA', eC']; exact hss

end C2
end Type08Sp
end Minimality
