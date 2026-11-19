module

public import Minimality.LeafB24b

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
open HDNApex

namespace LeafB24

/-- Abstract pentagon core: the ten triple brackets of five points in convex position, their
linear (affine) and one quadratic Plücker relation, and the key row. -/
theorem pent_core (d012 d013 d014 d023 d024 d034 d123 d124 d134 d234 : ℝ)
    (h012 : 0 < d012) (h013 : 0 < d013) (h014 : 0 < d014) (h023 : 0 < d023) (h024 : 0 < d024)
    (h034 : 0 < d034) (h123 : 0 < d123) (h124 : 0 < d124) (h134 : 0 < d134)
    (p0123 : d012 - d013 + d023 - d123 = 0) (p0124 : d012 - d014 + d024 - d124 = 0)
    (p0134 : d013 - d014 + d034 - d134 = 0) (p0234 : d023 - d024 + d034 - d234 = 0)
    (g1 : d012 * d034 - d013 * d024 + d014 * d023 = 0)
    (key : d124 < d123) :
    d012 < d123 ∧ d034 < d234 ∧ d134 < d234 ∧ (d014 < d012 ∨ d014 < d013) ∧
      (d014 < d024 ∨ d014 < d034) := by
  have H1 : d012 < d123 := by
    nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]
  refine ⟨H1, ?_, by linarith, ?_, ?_⟩
  · nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]
  · by_contra h; push Not at h
    nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]
  · by_contra h; push Not at h
    nlinarith [mul_pos h012 h034, mul_pos h013 h024, mul_pos h014 h023, mul_pos h012 h134,
      mul_pos h124 h034, mul_pos h123 h024]

/-- **Far-corner lemma** (LEAFB24.md section 3) for the pentagon `p 0 .. p 4` (rim `0 4 6 2 5`):
convex in the sense of `hcyc`, with the key row `det3 (p 2 - p 1) (p 4 - p 3) u < 0` (the angles at
`p 2`, `p 3` sum to less than `pi`), then the far corners of the edges `0 → 1, 1 → 2, 3 → 4, 4 → 0`
are as `isRupert_leafB_04625_limit` needs (edge `1 → 2`: `3`, edge `3 → 4`: `2`, the others in `{2, 3}`).
Generic (tie) hypotheses: the two ties `p 2` vs `p 3` for the edges `0 → 1` and `4 → 0`
(an edge parallel to `p 2 p 3`), and a unique far corner `c2` for the edge `2 → 3` itself. -/
theorem pent_anti {p : ZMod 5 → ℝ³} {u : ℝ³}
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u)
    (key : det3 (p 2 - p 1) (p 4 - p 3) u < 0)
    (g0 : det3 (p 1 - p 0) (p 2 - p 0) u ≠ det3 (p 1 - p 0) (p 3 - p 0) u)
    (g4 : det3 (p 0 - p 4) (p 2 - p 4) u ≠ det3 (p 0 - p 4) (p 3 - p 4) u)
    (c2 : ZMod 5)
    (h2 : ∀ l, l ≠ c2 → det3 (p 3 - p 2) (p l - p 2) u < det3 (p 3 - p 2) (p c2 - p 2) u) :
    ∃ c : ZMod 5 → ZMod 5, c 1 = 3 ∧ c 3 = 2 ∧ (c 0 = 2 ∨ c 0 = 3) ∧ (c 4 = 2 ∨ c 4 = 3) ∧
      ∀ i l, l ≠ c i → det3 (p (i + 1) - p i) (p l - p i) u
        < det3 (p (i + 1) - p i) (p (c i) - p i) u := by
  have e1 : (0 : ZMod 5) + 1 = 1 := rfl
  have e2 : (1 : ZMod 5) + 1 = 2 := rfl
  have e3 : (2 : ZMod 5) + 1 = 3 := rfl
  have e4 : (3 : ZMod 5) + 1 = 4 := rfl
  have e5 : (4 : ZMod 5) + 1 = 0 := rfl
  have c01 := hcyc 0 2 (by decide) (by decide)
  have c02 := hcyc 0 3 (by decide) (by decide)
  have c03 := hcyc 0 4 (by decide) (by decide)
  have c04 := hcyc 2 0 (by decide) (by decide)
  have c05 := hcyc 4 2 (by decide) (by decide)
  have c06 := hcyc 3 0 (by decide) (by decide)
  have c07 := hcyc 1 3 (by decide) (by decide)
  have c08 := hcyc 1 4 (by decide) (by decide)
  have c09 := hcyc 3 1 (by decide) (by decide)
  have c10 := hcyc 2 4 (by decide) (by decide)
  simp only [e1, e2, e3, e4, e5] at c01 c02 c03 c04 c05 c06 c07 c08 c09 c10
  -- the R-table: every row as a bracket
  have t01 : det3 (p 1 - p 0) (p 1 - p 0) u = 0 := by simp [det3_expand]; ring
  have t02 : det3 (p 1 - p 0) (p 0 - p 0) u = 0 := by simp [det3_expand]
  have t10 : det3 (p 2 - p 1) (p 0 - p 1) u = det3 (p 1 - p 0) (p 2 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t11 : det3 (p 2 - p 1) (p 1 - p 1) u = 0 := by simp [det3_expand]
  have t12 : det3 (p 2 - p 1) (p 2 - p 1) u = 0 := by simp [det3_expand]; ring
  have t20 : det3 (p 3 - p 2) (p 0 - p 2) u = det3 (p 2 - p 0) (p 3 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t21 : det3 (p 3 - p 2) (p 1 - p 2) u = det3 (p 2 - p 1) (p 3 - p 1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t30 : det3 (p 4 - p 3) (p 0 - p 3) u = det3 (p 3 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t31 : det3 (p 4 - p 3) (p 1 - p 3) u = det3 (p 3 - p 1) (p 4 - p 1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t32 : det3 (p 4 - p 3) (p 2 - p 3) u = det3 (p 3 - p 2) (p 4 - p 2) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t41 : det3 (p 0 - p 4) (p 1 - p 4) u = det3 (p 1 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t42 : det3 (p 0 - p 4) (p 2 - p 4) u = det3 (p 2 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t43 : det3 (p 0 - p 4) (p 3 - p 4) u = det3 (p 3 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- brackets
  have s0123 : det3 (p 1 - p 0) (p 2 - p 0) u - det3 (p 1 - p 0) (p 3 - p 0) u
      + det3 (p 2 - p 0) (p 3 - p 0) u - det3 (p 2 - p 1) (p 3 - p 1) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s0124 : det3 (p 1 - p 0) (p 2 - p 0) u - det3 (p 1 - p 0) (p 4 - p 0) u
      + det3 (p 2 - p 0) (p 4 - p 0) u - det3 (p 2 - p 1) (p 4 - p 1) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s0134 : det3 (p 1 - p 0) (p 3 - p 0) u - det3 (p 1 - p 0) (p 4 - p 0) u
      + det3 (p 3 - p 0) (p 4 - p 0) u - det3 (p 3 - p 1) (p 4 - p 1) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s0234 : det3 (p 2 - p 0) (p 3 - p 0) u - det3 (p 2 - p 0) (p 4 - p 0) u
      + det3 (p 3 - p 0) (p 4 - p 0) u - det3 (p 3 - p 2) (p 4 - p 2) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s1234 : det3 (p 2 - p 1) (p 3 - p 1) u - det3 (p 2 - p 1) (p 4 - p 1) u
      + det3 (p 3 - p 1) (p 4 - p 1) u - det3 (p 3 - p 2) (p 4 - p 2) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have gp : det3 (p 1 - p 0) (p 2 - p 0) u * det3 (p 3 - p 0) (p 4 - p 0) u
      - det3 (p 1 - p 0) (p 3 - p 0) u * det3 (p 2 - p 0) (p 4 - p 0) u
      + det3 (p 1 - p 0) (p 4 - p 0) u * det3 (p 2 - p 0) (p 3 - p 0) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have kk : det3 (p 2 - p 1) (p 4 - p 3) u
      = det3 (p 2 - p 1) (p 4 - p 1) u - det3 (p 2 - p 1) (p 3 - p 1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have c04' : 0 < det3 (p 2 - p 0) (p 3 - p 0) u := by rw [← t20]; exact c04
  have c05' : 0 < det3 (p 2 - p 0) (p 4 - p 0) u := by rw [← t42]; exact c05
  have c06' : 0 < det3 (p 3 - p 0) (p 4 - p 0) u := by rw [← t30]; exact c06
  have c09' : 0 < det3 (p 3 - p 1) (p 4 - p 1) u := by rw [← t31]; exact c09
  have c10' : 0 < det3 (p 3 - p 2) (p 4 - p 2) u := by exact c10
  obtain ⟨k1, k2, k3, k4, k5⟩ := pent_core _ _ _ _ _ _ _ _ _ c01 c02 c03 c04' c05' c06' c07 c08 c09'
    s0123 s0124 s0134 (d234 := det3 (p 3 - p 2) (p 4 - p 2) u) (by linarith) gp (by linarith)
  have hz : ∀ a : ℝ³, det3 a a u = 0 := fun a => by simp [det3_expand]; ring
  have hz2 : ∀ a : ℝ³, det3 a 0 u = 0 := fun a => by simp [det3_expand]
  -- edge 0
  obtain ⟨c0, hc0, r0⟩ : ∃ c0 : ZMod 5, (c0 = 2 ∨ c0 = 3) ∧ ∀ l, l ≠ c0 →
      det3 (p 1 - p 0) (p l - p 0) u < det3 (p 1 - p 0) (p c0 - p 0) u := by
    rcases lt_or_gt_of_ne g0 with h | h
    · refine ⟨3, Or.inr rfl, fun l hl => ?_⟩
      rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
      · simp only [sub_self, hz2]; linarith
      · simp only [hz]; linarith
      · linarith
      · rcases k4 with k | k <;> linarith
    · refine ⟨2, Or.inl rfl, fun l hl => ?_⟩
      rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
      · simp only [sub_self, hz2]; linarith
      · simp only [hz]; linarith
      · linarith
      · rcases k4 with k | k <;> linarith
  obtain ⟨c4, hc4, r4⟩ : ∃ c4 : ZMod 5, (c4 = 2 ∨ c4 = 3) ∧ ∀ l, l ≠ c4 →
      det3 (p 0 - p 4) (p l - p 4) u < det3 (p 0 - p 4) (p c4 - p 4) u := by
    rcases lt_or_gt_of_ne g4 with h | h
    · refine ⟨3, Or.inr rfl, fun l hl => ?_⟩
      rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
      · simp only [hz]; linarith
      · rcases k5 with k | k <;> linarith
      · linarith
      · simp only [sub_self, hz2]; linarith
    · refine ⟨2, Or.inl rfl, fun l hl => ?_⟩
      rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
      · simp only [hz]; linarith
      · rcases k5 with k | k <;> linarith
      · linarith
      · simp only [sub_self, hz2]; linarith
  refine ⟨![c0, 3, c2, 2, c4], rfl, rfl, hc0, hc4, fun i l hl => ?_⟩
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · exact r0 l hl
  · rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
    · show det3 (p 2 - p 1) (p 0 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      linarith
    · show det3 (p 2 - p 1) (p 1 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      simp only [sub_self, hz2]; linarith
    · show det3 (p 2 - p 1) (p 2 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      simp only [hz]; linarith
    · show det3 (p 2 - p 1) (p 4 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      linarith
  · exact h2 l hl
  · rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
    · show det3 (p 4 - p 3) (p 0 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      linarith
    · show det3 (p 4 - p 3) (p 1 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      linarith
    · show det3 (p 4 - p 3) (p 3 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      simp only [sub_self, hz2]; linarith
    · show det3 (p 4 - p 3) (p 4 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      simp only [hz]; linarith
  · exact r4 l hl

/-- A tilt with prescribed inner products `1` against two vectors exists when `det3 a b u ≠ 0`
(so `a`, `b` independent): `e = (b × n + n × a) / |n|²`, `n = a × b`.  (LeafB24b.md, open tilt item:
for the wedge `z6 < z2 < z0` take `a = x2 - x6`, `b = x0 - x2`; non-collinearity of the screen
triangle `x0, x6, x2` is `hcyc`.) -/
theorem exists_tilt {a b u : ℝ³} (h : det3 a b u ≠ 0) : ∃ e : ℝ³, ⟪a, e⟫ = 1 ∧ ⟪b, e⟫ = 1 := by
  have hN : ⟪cross a b, cross a b⟫ ≠ 0 := by
    intro h0
    apply h
    have : cross a b = 0 := inner_self_eq_zero.1 h0
    simp [det3, this]
  have ha : ⟪a, cross b (cross a b) + cross (cross a b) a⟫ = ⟪cross a b, cross a b⟫ := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
      cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.add_apply]
    ring
  have hb : ⟪b, cross b (cross a b) + cross (cross a b) a⟫ = ⟪cross a b, cross a b⟫ := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
      cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.add_apply]
    ring
  refine ⟨(⟪cross a b, cross a b⟫)⁻¹ • (cross b (cross a b) + cross (cross a b) a), ?_, ?_⟩
  · rw [real_inner_smul_right, ha]; field_simp
  · rw [real_inner_smul_right, hb]; field_simp

/-- **Leaf B at the orthocentre limit, from the key determinant.**  `isRupert_leafB_04625_limit_w1`
with `hanti` replaced by the strict key inequality `det3 (x 6 - x 4) (x 5 - x 2) u < 0` (angles at
`6`, `2` sum below `pi`) and three genericity conditions (no edge `0 4` or `5 0` parallel to `6 2` on the
screen: `g0`, `g4`; a unique far corner `c2` of the edge `6 → 2`, `h62`), and the tilt `e` constructed.
Only the wedge `z6 < z2 < z0` is used, with the foot condition `hf` of `2` on the edge `4 → 6`. -/
theorem isRupert_leafB_04625_of_det {x : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB j) - x (rimB i)) u)
    (hrest : ∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) u)
    (t0 : ⟪x 2, u⟫ = ⟪x 0, u⟫) (t6 : ⟪x 2, u⟫ = ⟪x 6, u⟫)
    (h4 : ⟪x 2, u⟫ < ⟪x 4, u⟫) (h5 : ⟪x 2, u⟫ < ⟪x 5, u⟫) (r5 : ⟪x 4, u⟫ ≠ ⟪x 5, u⟫)
    (key : det3 (x 6 - x 4) (x 5 - x 2) u < 0)
    (g0 : det3 (x 4 - x 0) (x 6 - x 0) u ≠ det3 (x 4 - x 0) (x 2 - x 0) u)
    (g4 : det3 (x 0 - x 5) (x 6 - x 5) u ≠ det3 (x 0 - x 5) (x 2 - x 5) u)
    (c2 : ZMod 5)
    (h62 : ∀ l, l ≠ c2 → det3 (x 2 - x 6) (x (rimB l) - x 6) u
      < det3 (x 2 - x 6) (x (rimB c2) - x 6) u)
    (hf0 : scr u (x 2 - x 4) (x 6 - x 4) ≠ 0)
    (hfL : scr u (x 2 - x 4) (x 6 - x 4) ≠ scr u (x 6 - x 4) (x 6 - x 4)) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨c, hc1, hc3, hc0, hc4, hanti⟩ := pent_anti (p := fun i => x (rimB i)) (u := u) hcyc
    (by simpa [rimB] using key) (by simpa [rimB] using g0) (by simpa [rimB] using g4) c2
    (by simpa [rimB] using h62)
  have hd : det3 (x 2 - x 6) (x 0 - x 2) u ≠ 0 := by
    have : 0 < det3 (x 2 - x 6) (x 0 - x 6) u := hcyc 2 0 (by decide) (by decide)
    have e : det3 (x 2 - x 6) (x 0 - x 2) u = det3 (x 2 - x 6) (x 0 - x 6) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact ne_of_gt this
  obtain ⟨e, he1, he2⟩ := exists_tilt hd
  refine isRupert_leafB_04625_limit_w1 (e := e) hu hcyc hrest t0 t6 h4 h5 r5 c hc1 hc3 hc0 hc4 hanti hf0 hfL ⟨?_, ?_⟩
  · rw [inner_sub_left] at he1; linarith
  · rw [inner_sub_left] at he2; linarith

end LeafB24
end Minimality
