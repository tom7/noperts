module

public import Minimality.Type24Side

@[expose] public section

/-!
# Type 24 at every metric: the planar quad rim, Lemma Y and DS side-safety (§20, continued (3))

`FEWER-FACES-PROOFS.md` §20, continued (3) (subagent cu14, refereed 2026-10-22, scratch
`referee_cu14/`), at `K`'s own metric (the depth at a view `d` is `⟪·, d⟫`).

* **Corollary 20.19 (the planar quad rim)** (`planarRim_coeffs`, `QuadTest.not_fails4_planar`,
  `QuadTest'.isRupert_planar`, `Face16.det3_eq_zero`; for type 24
  `isRupert_type24_planarQuad`): a crossing test whose rim is the planar quad `(0, 4, 3, 5)` (the
  face `0345`) never fails, at any metric and in both octants, off the ties of its rim and its
  horizontal double normals.  The coefficients `x 3 = x 0 + s (x 4 − x 0) + t (x 5 − x 0)` with
  `s, t > 0`, `s + t > 1` are read off the rim (Cramer's rule at the view; the four determinant
  tests of the rim give `t`, `s` and `s + t − 1` times the same positive determinant); then
  Lemma 17.4's argument (`planarQuad_fails4`) applies.  One affine certificate, no metric
  hypothesis.
* **Lemma 20.18 (Lemma Y, the single region)**: cu14's core (`Cu14.P1`, `Cu14.P2`,
  `Cu14.lemmaY`, moved here verbatim from `nopert229/cu14_lemmaY.lean`), its general form
  (`lemmaY_core`: arbitrary labels `P, Q, R`, a view `σ e_p + τ e_q` with `σ, τ > 0`), and the
  Rupert form (`isRupert_lemmaY`): on the region `R_k = {h_pq > 0, h_pr ≤ 0, h_qr ≤ 0}`, if the
  cap edges `E_P`, `E_Q` have the five-corner rims `(1, Q, s, r_P, R)`, `(1, P, s, r_Q, R)` and
  the crossing test `θ` has the rim `(Q, t, s, P)` at a view `σ e_p + τ e_q`, then under (Y1),
  (Y2) one of the three certifies `K`.  The boundaries `h_pr = 0`, `h_qr = 0` are ties of
  `E_P`, `E_Q` (excluded by their rim data).  The instance that matters, `k = bc`
  (`isRupert_lemmaY_bc`: `θ = 126/046` at the view `e_b + ω4 e_c`, rim `(6, 4, 3, 2)`), and its
  mirror (`isRupert_lemmaY_bc'`: `θ = 126/025` at `ω5 e_b + e_c`, rim `(2, 5, 3, 6)`).
* **DS side-safety (Theorems 20.16, 20.17)**: a cap edge is DS-good (`DSGood`) if its rim depths
  are unimodal or a parallel pair of its rim (`ParPairAt`, the affine half of `DepthSepAt`) is
  depth-separated (`DepthSepZ`, the depth half); *DS-safe on a quadrant* (`DSSafeQ`) if it is
  DS-good for every column `(g > 0, h_y ∈ Qy, h_w ∈ Qw)` with distinct rim depths (X-only
  depths).  Rupert form `isRupert_capEdge_dsSafe`.  For type 24: `Type24.DSSafeE2`, `_E6`, `_E0`,
  the regions `R_S` by sign patterns (`RegSign`, `Type24.DSRegion`), Theorem 20.17
  (`Type24.DSRegionsCovered`, `isRupert_type24_dsRegions`) and Theorem 20.16
  (`Type24.DSSideCovered`, `isRupert_type24_dsSide`; it is the case `DSSideCovered.regions`;
  old side-safety gives it, `SideCovered.ds`).
* **The acute side by uniform statements** (`Type24.AcuteCovered`, `isRupert_type24_acute`): a
  planar-quad test (20.19), or every region by a DS-safe cap edge (20.17), `R_bc` possibly by
  Lemma 20.18 (`Type24.LemmaYbc`, `isRupert_type24_lemmaYbc`).

Not formalized: Lemma 20.15 (the DS sink; DS-safety is a hypothesis, as `SideSafe` is), the
LPs and cell enumerations that decide DS-safety for given classes, Lemma 20.18 on `R_ab`, `R_ac`
as named instances (the general `isRupert_lemmaY` covers them), Proposition 20.20 and its
per-class certificates, the class counts.
-/

/-! ### cu14's core (Lemma 20.18 in the coordinates of the `bc` instance) -/

/-
cu14 (2026-10-22): the two linear arguments of Lemma Y (type 24, the region R_bc = {c_bc > 0, c_ab, c_ac ≤ 0}),
stated on Gram entries and depth values.  Moved verbatim from `nopert229/cu14_lemmaY.lean`.

Notation: X3 = (a3, b3, c3), X4 = (a4, b4, c4), X5 = (a5, b5, c5) (oblique coordinates at the cap 1).  Along the cap
edge 12 (view e_b) the depth of v is Zb v = a_v hab + b_v gb + c_v hbc; along 16 (view e_c) it is
Zc v = a_v hac + b_v hbc + c_v gc.  The test 126/046 has the view d4 = (0, 1, ω4), where the depth of v is
z v = a_v z0 + b_v z2 + c_v z6 with z2 = gb + ω4 hbc and z6 = hbc + ω4 gc.

* `P2`: the failure pattern {4,2} ≥ {6,3} of 126/046 is impossible when z2, z6 > 0, a3 > a4 ≥ 0 and the point
  Y' = (a3 X4 - a4 X3)/(a3 - a4) where the line 34 meets the plane of 126 satisfies b ≤ 0, c ≤ 1, one strictly.
* `P1`: the pattern {6,3} ≥ {4,2} (only its row z3 ≥ z2 is used) is impossible when E_2 and E_6 fail in the form
  of the m = 2 corollary (Zb 3 ≤ Zb 5 and Zc 3 ≤ hbc), gb, hbc > 0, ω4 > 0, a3 > a5 ≥ 0, and the point
  Y = (a3 X5 - a5 X3)/(a3 - a5) where the line 35 meets the plane of 126 satisfies b ≤ 1, c ≤ 0, one strictly.
-/

namespace Cu14

/-- P2: z4 ≥ z6 and z4 ≥ z3 at d4 are incompatible with the position of Y' (line 34 ∩ plane 126). -/
theorem P2 (a3 b3 c3 a4 b4 c4 z0 z2 z6 : ℝ) (h34 : a4 < a3) (ha4 : 0 ≤ a4)
    (hz2 : 0 < z2) (hz6 : 0 < z6)
    (hB : a3 * b4 - a4 * b3 ≤ 0) (hC : a3 * c4 - a4 * c3 ≤ a3 - a4)
    (hstrict : a3 * b4 - a4 * b3 < 0 ∨ a3 * c4 - a4 * c3 < a3 - a4)
    (h46 : z6 ≤ a4 * z0 + b4 * z2 + c4 * z6)
    (h43 : a3 * z0 + b3 * z2 + c3 * z6 ≤ a4 * z0 + b4 * z2 + c4 * z6) : False := by
  -- (a3 - a4)(z4 - z6) + a4 (z4 - z3) = (a3 b4 - a4 b3) z2 + (a3 c4 - a4 c3 - (a3 - a4)) z6
  have e1 : 0 ≤ (a3 - a4) * ((a4 * z0 + b4 * z2 + c4 * z6) - z6) := mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ a4 * ((a4 * z0 + b4 * z2 + c4 * z6) - (a3 * z0 + b3 * z2 + c3 * z6)) :=
    mul_nonneg ha4 (by linarith)
  have key : (a3 - a4) * ((a4 * z0 + b4 * z2 + c4 * z6) - z6)
      + a4 * ((a4 * z0 + b4 * z2 + c4 * z6) - (a3 * z0 + b3 * z2 + c3 * z6))
      = (a3 * b4 - a4 * b3) * z2 + (a3 * c4 - a4 * c3 - (a3 - a4)) * z6 := by ring
  have hneg : (a3 * b4 - a4 * b3) * z2 + (a3 * c4 - a4 * c3 - (a3 - a4)) * z6 < 0 := by
    rcases hstrict with h | h
    · have := mul_neg_of_neg_of_pos h hz2
      have := mul_nonpos_of_nonpos_of_nonneg (show a3 * c4 - a4 * c3 - (a3 - a4) ≤ 0 by linarith) hz6.le
      linarith
    · have := mul_nonpos_of_nonpos_of_nonneg hB hz2.le
      have := mul_neg_of_neg_of_pos (show a3 * c4 - a4 * c3 - (a3 - a4) < 0 by linarith) hz6
      linarith
  linarith

/-- P1: with E_2 and E_6 failing (Zb 3 ≤ Zb 5, Zc 3 ≤ hbc), the row z3 ≥ z2 of 126/046 at d4 is incompatible with
the position of Y (line 35 ∩ plane 126). -/
theorem P1 (a3 b3 c3 a5 b5 c5 w4 gb gc hab hac hbc : ℝ) (h35 : a5 < a3) (ha5 : 0 ≤ a5) (hw4 : 0 < w4)
    (hgb : 0 < gb) (hbcp : 0 < hbc)
    (hB : a3 * b5 - a5 * b3 ≤ a3 - a5) (hC : a3 * c5 - a5 * c3 ≤ 0)
    (hstrict : a3 * b5 - a5 * b3 < a3 - a5 ∨ a3 * c5 - a5 * c3 < 0)
    -- E_2 fails: Zb 3 ≤ Zb 5
    (hE2 : a3 * hab + b3 * gb + c3 * hbc ≤ a5 * hab + b5 * gb + c5 * hbc)
    -- E_6 fails: Zc 3 ≤ hbc
    (hE6 : a3 * hac + b3 * hbc + c3 * gc ≤ hbc)
    -- 126/046 fails by {6,3} ≥ {4,2}: z3 ≥ z2 at d4 = (0, 1, w4)
    (h32 : gb + w4 * hbc ≤ (a3 * hab + b3 * gb + c3 * hbc) + w4 * (a3 * hac + b3 * hbc + c3 * gc)) : False := by
  -- Zb 3 - gb ≥ w4 (hbc - Zc 3) ≥ 0, then a3 (Zb 5 - Zb 3) + (a3 - a5)(Zb 3 - gb)
  --   = (a3 b5 - a5 b3 - (a3 - a5)) gb + (a3 c5 - a5 c3) hbc
  have hZ : 0 ≤ (a3 * hab + b3 * gb + c3 * hbc) - gb := by
    have : 0 ≤ w4 * (hbc - (a3 * hac + b3 * hbc + c3 * gc)) := mul_nonneg hw4.le (by linarith)
    linarith
  have e1 : 0 ≤ a3 * ((a5 * hab + b5 * gb + c5 * hbc) - (a3 * hab + b3 * gb + c3 * hbc)) :=
    mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ (a3 - a5) * ((a3 * hab + b3 * gb + c3 * hbc) - gb) := mul_nonneg (by linarith) hZ
  have key : a3 * ((a5 * hab + b5 * gb + c5 * hbc) - (a3 * hab + b3 * gb + c3 * hbc))
      + (a3 - a5) * ((a3 * hab + b3 * gb + c3 * hbc) - gb)
      = (a3 * b5 - a5 * b3 - (a3 - a5)) * gb + (a3 * c5 - a5 * c3) * hbc := by ring
  have hneg : (a3 * b5 - a5 * b3 - (a3 - a5)) * gb + (a3 * c5 - a5 * c3) * hbc < 0 := by
    rcases hstrict with h | h
    · have := mul_neg_of_neg_of_pos (show a3 * b5 - a5 * b3 - (a3 - a5) < 0 by linarith) hgb
      have := mul_nonpos_of_nonpos_of_nonneg hC hbcp.le
      linarith
    · have := mul_nonpos_of_nonpos_of_nonneg (show a3 * b5 - a5 * b3 - (a3 - a5) ≤ 0 by linarith) hgb.le
      have := mul_neg_of_neg_of_pos h hbcp
      linarith
  linarith

/-- Lemma Y, the combinatorial step: on R_bc, if E_2 and E_6 fail (corollary form) and 126/046 fails, its pattern is
{4,2} ≥ {6,3} or {6,3} ≥ {4,2}; both are impossible.  Here the two patterns are given by their rows. -/
theorem lemmaY (a3 b3 c3 a4 b4 c4 a5 b5 c5 w4 gb gc hab hac hbc : ℝ)
    (h34 : a4 < a3) (ha4 : 0 ≤ a4) (h35 : a5 < a3) (ha5 : 0 ≤ a5) (hw4 : 0 < w4)
    (hgb : 0 < gb) (hgc : 0 < gc) (hbcp : 0 < hbc)
    (hB4 : a3 * b4 - a4 * b3 ≤ 0) (hC4 : a3 * c4 - a4 * c3 ≤ a3 - a4)
    (hs4 : a3 * b4 - a4 * b3 < 0 ∨ a3 * c4 - a4 * c3 < a3 - a4)
    (hB5 : a3 * b5 - a5 * b3 ≤ a3 - a5) (hC5 : a3 * c5 - a5 * c3 ≤ 0)
    (hs5 : a3 * b5 - a5 * b3 < a3 - a5 ∨ a3 * c5 - a5 * c3 < 0)
    (hE2 : a3 * hab + b3 * gb + c3 * hbc ≤ a5 * hab + b5 * gb + c5 * hbc)
    (hE6 : a3 * hac + b3 * hbc + c3 * gc ≤ hbc)
    (hfail : (gb + w4 * hbc ≤ (a3 * hab + b3 * gb + c3 * hbc) + w4 * (a3 * hac + b3 * hbc + c3 * gc))
      ∨ ((hbc + w4 * gc ≤ (a4 * hab + b4 * gb + c4 * hbc) + w4 * (a4 * hac + b4 * hbc + c4 * gc)) ∧
         ((a3 * hab + b3 * gb + c3 * hbc) + w4 * (a3 * hac + b3 * hbc + c3 * gc)
           ≤ (a4 * hab + b4 * gb + c4 * hbc) + w4 * (a4 * hac + b4 * hbc + c4 * gc)))) : False := by
  rcases hfail with h | ⟨h1, h2⟩
  · exact P1 a3 b3 c3 a5 b5 c5 w4 gb gc hab hac hbc h35 ha5 hw4 hgb hbcp hB5 hC5 hs5 hE2 hE6 h
  · -- at d4: z0 = hab + w4 hac, z2 = gb + w4 hbc, z6 = hbc + w4 gc
    have hz2 : 0 < gb + w4 * hbc := by nlinarith
    have hz6 : 0 < hbc + w4 * gc := by nlinarith
    refine P2 a3 b3 c3 a4 b4 c4 (hab + w4 * hac) (gb + w4 * hbc) (hbc + w4 * gc) h34 ha4 hz2 hz6 hB4 hC4 hs4 ?_ ?_
    · linarith
    · linarith

end Cu14

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Corollary 20.19: a rim that is a planar quad never fails -/

/-- **Cramer's rule at a view**: `[a b u] c = [c b u] a + [a c u] b + [a b c] u`. -/
theorem det3_cramer_view (a b c u : ℝ³) :
    det3 a b u • c = det3 c b u • a + det3 a c u • b + det3 a b c • u := by
  ext i
  fin_cases i <;> simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    simp <;> ring

/-- **The coefficients of a planar quad, read off its rim** (the proof of Corollary 20.19).  If
`y, a, c, b` are coplanar (`[a − y, b − y, c − y] = 0`) and at the view `u` they form the strictly
convex counterclockwise quadrilateral `(y, a, c, b)`, then `c = y + s (a − y) + t (b − y)` with
`s, t > 0` and `s + t > 1`: with `D = [a − y, b − y, u] > 0` (the test at `b`), the tests at `y`,
`c` and `a` are `t D`, `s D` and `(s + t − 1) D`. -/
theorem planarRim_coeffs {y a c b u : ℝ³} (hpl : det3 (a - y) (b - y) (c - y) = 0)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u) :
    ∃ s t : ℝ, c = y + s • (a - y) + t • (b - y) ∧ 0 < s ∧ 0 < t ∧ 1 < s + t := by
  have e4 : det3 (y - b) (a - b) u = det3 (a - y) (b - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e3 : det3 (b - c) (y - c) u = det3 (c - y) (b - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e1 : det3 (a - y) (c - y) u = det3 (a - y) (c - y) u := rfl
  have e2 : det3 (c - a) (b - a) u =
      det3 (c - y) (b - y) u + det3 (a - y) (c - y) u - det3 (a - y) (b - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e4] at q₄; rw [e3] at q₃; rw [e2] at q₂
  clear e1
  set D := det3 (a - y) (b - y) u with hD
  have hcr := det3_cramer_view (a - y) (b - y) (c - y) u
  rw [hpl, zero_smul, add_zero] at hcr
  refine ⟨det3 (c - y) (b - y) u / D, det3 (a - y) (c - y) u / D, ?_, div_pos q₃ q₄,
    div_pos q₁ q₄, ?_⟩
  · have hC : c - y = (det3 (c - y) (b - y) u / D) • (a - y) +
        (det3 (a - y) (c - y) u / D) • (b - y) := by
      rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← hcr, smul_smul,
        inv_mul_cancel₀ q₄.ne', one_smul]
    rw [add_assoc, ← hC]; abel
  · rw [← add_div, one_lt_div q₄]; linarith

/-- **Corollary 20.19, the depth form.**  A 4-corner test whose rim `(y, a, c, b)` is coplanar in
space and certified up to its depth pattern (`QuadTest`: strictly convex, distinct depths) does
not fail at its view. -/
theorem QuadTest.not_fails4_planar {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTest V u y a c b)
    (hpl : det3 (a - y) (b - y) (c - y) = 0) : ¬ Fails4 y c a b u := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, q₁, q₂, q₃, q₄, -, hz, -⟩ := h
  obtain ⟨s, t, hc, hs, ht, hst⟩ := planarRim_coeffs hpl q₁ q₂ q₃ q₄
  intro hF
  obtain ⟨-, e2, -⟩ := planarQuad_fails4 hc hs ht hst hF
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  exact hz.1.1 e2.symm

/-- **Corollary 20.19, Rupert form.**  A crossing test, in either orientation, whose rim
`(y, a, c, b)` is coplanar in space certifies `V` (no metric hypothesis: the test never fails). -/
theorem QuadTest'.isRupert_planar {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTest' V u y a c b)
    (hpl : det3 (a - y) (b - y) (c - y) = 0) : IsRupert V := by
  refine h.isRupert ?_
  rcases h with h | h
  · exact h.not_fails4_planar hpl
  · have hpl' : det3 (b - y) (a - y) (c - y) = 0 := by
      rw [← neg_eq_zero, ← hpl]; simp only [det3_expand, PiLp.sub_apply]; ring
    exact fun hF => h.not_fails4_planar hpl' (fails4_swap.mp hF)

/-- Four points of a face are coplanar: `[x j − x i, x k − x i, x l − x i] = 0`.  (The normal `N`
of the face is nonzero, since some point lies strictly beneath it, and `[A, B, C] N` is a
combination of `⟪N, A⟫`, `⟪N, B⟫`, `⟪N, C⟫`.) -/
theorem Face16.det3_eq_zero {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S)
    {i j k l m : Fin 7} (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S) (hl : l ∈ S) (hm : m ∉ S) :
    det3 (x j - x i) (x k - x i) (x l - x i) = 0 := by
  have hA : ⟪F.N, x j - x i⟫ = 0 := by rw [← F.hN, F.zero j hj, F.zero i hi, sub_self]
  have hB : ⟪F.N, x k - x i⟫ = 0 := by rw [← F.hN, F.zero k hk, F.zero i hi, sub_self]
  have hC : ⟪F.N, x l - x i⟫ = 0 := by rw [← F.hN, F.zero l hl, F.zero i hi, sub_self]
  have hN : F.N ≠ 0 := by
    intro h0
    have := F.hN (x m) (x i)
    rw [h0, inner_zero_left, F.zero i hi, sub_zero] at this
    exact (F.neg m hm).ne this
  set A := x j - x i
  set B := x k - x i
  set C := x l - x i
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hA hB hC
  have k0 : det3 A B C * F.N 0 = 0 := by
    rw [det3_expand]
    linear_combination (B 1 * C 2 - B 2 * C 1) * hA + (C 1 * A 2 - C 2 * A 1) * hB +
      (A 1 * B 2 - A 2 * B 1) * hC
  have k1 : det3 A B C * F.N 1 = 0 := by
    rw [det3_expand]
    linear_combination (B 2 * C 0 - B 0 * C 2) * hA + (C 2 * A 0 - C 0 * A 2) * hB +
      (A 2 * B 0 - A 0 * B 2) * hC
  have k2 : det3 A B C * F.N 2 = 0 := by
    rw [det3_expand]
    linear_combination (B 0 * C 1 - B 1 * C 0) * hA + (C 0 * A 1 - C 1 * A 0) * hB +
      (A 0 * B 1 - A 1 * B 0) * hC
  by_contra hne
  apply hN
  ext n
  have key : det3 A B C * F.N n = 0 := by
    fin_cases n
    exacts [k0, k1, k2]
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · simpa using h

/-- **Corollary 20.19 for type 24 (the planar quad rim `(0, 4, 3, 5)`).**  If `0, 3, 4, 5` span
the face `0345` and some crossing test has the rim `(0, 4, 3, 5)` at its view (either
orientation; certified up to its depth pattern, `QuadTest'`), the point set is Rupert, at every
metric, in both octants: the test never fails.  The exclusions are those of the test: ties of its
four depths (`z0 = z3 = z4 = z5` is the only failing one) and horizontal double normals.  The
tests that occur are `S_0 = 025/046`, `046/346-6`, `025/235-2`, `235/346`, `046|235`, `025|346`. -/
theorem isRupert_type24_planarQuad {x : Fin 7 → ℝ³} (F : Face16 x {0, 3, 4, 5}) {u : ℝ³}
    (hQ : QuadTest' (univ.image x) u (x 0) (x 4) (x 3) (x 5)) : IsRupert (univ.image x) :=
  hQ.isRupert_planar (F.det3_eq_zero (by decide) (by decide) (by decide) (by decide)
    (m := 1) (by decide))

/-! ### Lemma 20.18 (Lemma Y): the single region -/

/-- **Lemma 20.18, the linear core in general labels** (cu14's `P1`, `P2` with `σ, τ > 0`).
Coordinates: `s = (sr, sp, sq)`, `t = (tr, tp, tq)`, `r_P = (mr, mp, mq)` in the frame of the axes
`R, P, Q`; the depths along the cap edges are `Z_p(v) = v_r h_pr + v_p g_p + v_q h_pq` and
`Z_q(v) = v_r h_qr + v_p h_pq + v_q g_q`, and `θ`'s depth at `σ e_p + τ e_q` is
`σ Z_p + τ Z_q`.  With `E_P` and `E_Q` failing in the form of the `m = 2` corollary
(`Z_p(s) ≤ Z_p(r_P)`, `Z_q(s) ≤ h_pq`), (Y1) and (Y2) (cleared of denominators), `θ` fails by
neither of its patterns: `{t, P} ≥ {Q, s}` (its rows `z(t) ≥ z(Q)`, `z(t) ≥ z(s)`) and
`{Q, s} ≥ {t, P}` (its row `z(s) ≥ z(P)`). -/
theorem lemmaY_core (sr sp sq tr tp tq mr mp mq σ τ gp gq hpq hpr hqr : ℝ)
    (hσ : 0 < σ) (hτ : 0 < τ) (hgp : 0 < gp) (hgq : 0 ≤ gq) (hpq0 : 0 < hpq)
    (hts : tr < sr) (ht0 : 0 ≤ tr)
    (hY1p : sr * tp - tr * sp ≤ 0) (hY1q : sr * tq - tr * sq ≤ sr - tr)
    (hY1 : sr * tp - tr * sp < 0 ∨ sr * tq - tr * sq < sr - tr)
    (hms : mr < sr) (hm0 : 0 ≤ mr)
    (hY2p : sr * mp - mr * sp ≤ sr - mr) (hY2q : sr * mq - mr * sq ≤ 0)
    (hY2 : sr * mp - mr * sp < sr - mr ∨ sr * mq - mr * sq < 0)
    (hEP : sr * hpr + sp * gp + sq * hpq ≤ mr * hpr + mp * gp + mq * hpq)
    (hEQ : sr * hqr + sp * hpq + sq * gq ≤ hpq)
    (hθ : (σ * hpq + τ * gq ≤ σ * (tr * hpr + tp * gp + tq * hpq) + τ * (tr * hqr + tp * hpq + tq * gq) ∧
        σ * (sr * hpr + sp * gp + sq * hpq) + τ * (sr * hqr + sp * hpq + sq * gq) ≤
          σ * (tr * hpr + tp * gp + tq * hpq) + τ * (tr * hqr + tp * hpq + tq * gq)) ∨
      σ * gp + τ * hpq ≤ σ * (sr * hpr + sp * gp + sq * hpq) + τ * (sr * hqr + sp * hpq + sq * gq)) :
    False := by
  rcases hθ with ⟨h1, h2⟩ | h
  · have hz2 : 0 < σ * gp + τ * hpq := by positivity
    have hz6 : 0 < σ * hpq + τ * gq := by positivity
    exact Cu14.P2 sr sp sq tr tp tq (σ * hpr + τ * hqr) (σ * gp + τ * hpq) (σ * hpq + τ * gq) hts ht0
      hz2 hz6 hY1p hY1q hY1 (by linarith) (by linarith)
  · refine Cu14.P1 sr sp sq mr mp mq (τ / σ) gp gq hpr hqr hpq hms hm0 (div_pos hτ hσ) hgp hpq0
      hY2p hY2q hY2 hEP hEQ ?_
    have e : ∀ A B : ℝ, σ * (A + τ / σ * B) = σ * A + τ * B := fun A B => by
      field_simp
    refine le_of_mul_le_mul_left ?_ hσ
    rw [e, e]
    exact h

/-- **The position of `Y(s, v)`** (§20.29), cleared of the denominator `x_r(s) − x_r(v) > 0`: the
point `Y = (x_r(s) v − x_r(v) s) / (x_r(s) − x_r(v))` where the line `s v` meets the cap plane
`x_r = 0` beyond `v` has `x_p ≤ bp` and `x_q ≤ bq`, not both with equality.  X-only. -/
def YBelow (Xp Xq Xr : Fin 7 → ℝ) (s v : Fin 7) (bp bq : ℝ) : Prop :=
  Xr v < Xr s ∧ Xr s * Xp v - Xr v * Xp s ≤ bp * (Xr s - Xr v) ∧
    Xr s * Xq v - Xr v * Xq s ≤ bq * (Xr s - Xr v) ∧
    (Xr s * Xp v - Xr v * Xp s < bp * (Xr s - Xr v) ∨ Xr s * Xq v - Xr v * Xq s < bq * (Xr s - Xr v))

theorem YBelow.swap {Xp Xq Xr : Fin 7 → ℝ} {s v : Fin 7} {bp bq : ℝ} (h : YBelow Xp Xq Xr s v bp bq) :
    YBelow Xq Xp Xr s v bq bp :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩

section LemmaY

variable {x : Fin 7 → ℝ³} {P Q R : Fin 7} {Xp Xq Xr : Fin 7 → ℝ}

/-- The depth along the cap edge `1P` in the frame `x 1; P, Q, R`. -/
theorem lemmaY_depthP
    (hrep : ∀ v, x v = x 1 + Xp v • (x P - x 1) + Xq v • (x Q - x 1) + Xr v • (x R - x 1))
    (v : Fin 7) :
    ⟪x v, x P - x 1⟫ = ⟪x 1, x P - x 1⟫ + (Xr v * ⟪x P - x 1, x R - x 1⟫ +
      Xp v * ⟪x P - x 1, x P - x 1⟫ + Xq v * ⟪x P - x 1, x Q - x 1⟫) := by
  rw [inner_covDepth hrep, real_inner_comm (x P - x 1) (x Q - x 1),
    real_inner_comm (x P - x 1) (x R - x 1)]
  simp only [covDepth]; ring

/-- The depth along the cap edge `1Q` in the frame `x 1; P, Q, R`. -/
theorem lemmaY_depthQ
    (hrep : ∀ v, x v = x 1 + Xp v • (x P - x 1) + Xq v • (x Q - x 1) + Xr v • (x R - x 1))
    (v : Fin 7) :
    ⟪x v, x Q - x 1⟫ = ⟪x 1, x Q - x 1⟫ + (Xr v * ⟪x Q - x 1, x R - x 1⟫ +
      Xp v * ⟪x P - x 1, x Q - x 1⟫ + Xq v * ⟪x Q - x 1, x Q - x 1⟫) := by
  rw [inner_covDepth hrep, real_inner_comm (x Q - x 1) (x R - x 1)]
  simp only [covDepth]; ring

/-- The depth at a view `σ e_p + τ e_q` of the cap circle of `k = pq`. -/
theorem lemmaY_depth
    (hrep : ∀ v, x v = x 1 + Xp v • (x P - x 1) + Xq v • (x Q - x 1) + Xr v • (x R - x 1))
    (σ τ : ℝ) (v : Fin 7) :
    ⟪x v, σ • (x P - x 1) + τ • (x Q - x 1)⟫ = ⟪x 1, σ • (x P - x 1) + τ • (x Q - x 1)⟫ +
      (σ * (Xr v * ⟪x P - x 1, x R - x 1⟫ + Xp v * ⟪x P - x 1, x P - x 1⟫ +
          Xq v * ⟪x P - x 1, x Q - x 1⟫) +
        τ * (Xr v * ⟪x Q - x 1, x R - x 1⟫ + Xp v * ⟪x P - x 1, x Q - x 1⟫ +
          Xq v * ⟪x Q - x 1, x Q - x 1⟫)) := by
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, lemmaY_depthP hrep v, lemmaY_depthQ hrep v]
  ring

/-- A rim corner at the depth of the cap is a tie of the cap edge: in `CapRim0` the far end `R`
is not at the depth of `1`, so `h_pr ≤ 0` is strict. -/
theorem CapRim0.end_ne {ax ay aw : Fin 7} {r : ZMod 5 → Fin 7} (hR : CapRim0 x ax ay aw 5 r)
    {v : Fin 7} (hv : r 1 = v ∨ r 4 = v) : ⟪x v, x ax - x 1⟫ ≠ ⟪x 1, x ax - x 1⟫ := by
  have hz := hR.2.2.2.2.2.1
  have hr0 := hR.2.1
  intro e
  rcases hv with h | h
  · have := @hz 1 0 (by simp only; rw [h, hr0]; exact e)
    exact absurd this (by decide)
  · have := @hz 4 0 (by simp only; rw [h, hr0]; exact e)
    exact absurd this (by decide)

/-- **Lemma 20.18 (Lemma Y), Rupert form, general labels.**  Let `k = pq` be the cosine between the
cap edges `1P`, `1Q` and `R` the third axis vertex, with oblique coordinates `X_p, X_q, X_r` at
`1`.  On the region `R_k` (`h_pq > 0`, `h_pr ≤ 0`, `h_qr ≤ 0`, `K`'s own metric), suppose
* (Y0) `E_P` has the rim `(1, Q, s, r_P, R)` and `E_Q` the rim `(1, P, s, r_Q, R)` (`CapRim0`,
  either orientation; distinct depths, no horizontal double normal), and the crossing test `θ`
  has the rim `(Q, t, s, P)` at the view `σ e_p + τ e_q` with `σ, τ > 0` (`QuadTest'`);
* (Y1) `x_r(s) > x_r(t) ≥ 0` and `Y(s, t)` has `x_p ≤ 0`, `x_q ≤ 1`, not both with equality;
* (Y2) `x_r(s) > x_r(r_P) ≥ 0` and `Y(s, r_P)` has `x_p ≤ 1`, `x_q ≤ 0`, not both with equality.

Then `K` is Rupert: the three tests do not all fail (no positive definiteness and no view cut is
used), and the one that does not fail is unimodal.  `h_pr = 0`, `h_qr = 0` are the ties
`z(R) = z(1)` of `E_P`, `E_Q`, excluded by their rim data.  The mirror (`θ` with the rim
`(P, t, s, Q)`, (Y1) with `(x_p, x_q) ≤ (1, 0)`, (Y2) for `Y(s, r_Q)` with `(0, 1)`) is this
statement with `P` and `Q` exchanged. -/
theorem isRupert_lemmaY (hinj : Function.Injective x) {s t rP rQ : Fin 7} (hP : P ≠ 1)
    (hrep : ∀ v, x v = x 1 + Xp v • (x P - x 1) + Xq v • (x Q - x 1) + Xr v • (x R - x 1))
    {rp rq : ZMod 5 → Fin 7} (hEP : CapRim0 x P Q R 5 rp)
    (hEPo : (rp 1 = Q ∧ rp 2 = s ∧ rp 3 = rP ∧ rp 4 = R) ∨
      (rp 1 = R ∧ rp 2 = rP ∧ rp 3 = s ∧ rp 4 = Q))
    (hQ : Q ≠ 1) (hEQ : CapRim0 x Q P R 5 rq)
    (hEQo : (rq 1 = P ∧ rq 2 = s ∧ rq 3 = rQ ∧ rq 4 = R) ∨
      (rq 1 = R ∧ rq 2 = rQ ∧ rq 3 = s ∧ rq 4 = P))
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hθ : QuadTest' (univ.image x) (σ • (x P - x 1) + τ • (x Q - x 1)) (x Q) (x t) (x s) (x P))
    (hY1 : YBelow Xp Xq Xr s t 0 1) (ht0 : 0 ≤ Xr t)
    (hY2 : YBelow Xp Xq Xr s rP 1 0) (hm0 : 0 ≤ Xr rP)
    (hpq : 0 < ⟪x P - x 1, x Q - x 1⟫) (hpr : ⟪x P - x 1, x R - x 1⟫ ≤ 0)
    (hqr : ⟪x Q - x 1, x R - x 1⟫ ≤ 0) : IsRupert (univ.image x) := by
  -- the cap edge `E_P`
  by_cases hUP : IsCyclicUnimodal (fun i => ⟪x (rp i), x P - x 1⟫)
  · exact isRupert_capRim0 hinj hP hEP hUP
  by_cases hUQ : IsCyclicUnimodal (fun i => ⟪x (rq i), x Q - x 1⟫)
  · exact isRupert_capRim0 hinj hQ hEQ hUQ
  refine hθ.isRupert fun hF => ?_
  have c1 := real_inner_comm (x P - x 1) (x Q - x 1)
  have c2 := real_inner_comm (x P - x 1) (x R - x 1)
  have c3 := real_inner_comm (x Q - x 1) (x R - x 1)
  -- the ends of the cap rims
  have hRP : ⟪x R, x P - x 1⟫ < ⟪x 1, x P - x 1⟫ := by
    have hne := hEP.end_ne (v := R) (by rcases hEPo with h | h; exacts [Or.inr h.2.2.2, Or.inl h.1])
    have : ⟪x R, x P - x 1⟫ - ⟪x 1, x P - x 1⟫ ≤ 0 := by rw [← inner_sub_left, c2]; exact hpr
    exact lt_of_le_of_ne (by linarith) hne
  have hRQ : ⟪x R, x Q - x 1⟫ < ⟪x 1, x Q - x 1⟫ := by
    have hne := hEQ.end_ne (v := R) (by rcases hEQo with h | h; exacts [Or.inr h.2.2.2, Or.inl h.1])
    have : ⟪x R, x Q - x 1⟫ - ⟪x 1, x Q - x 1⟫ ≤ 0 := by rw [← inner_sub_left, c3]; exact hqr
    exact lt_of_le_of_ne (by linarith) hne
  have hQP : ⟪x 1, x P - x 1⟫ < ⟪x Q, x P - x 1⟫ := by
    have : 0 < ⟪x Q, x P - x 1⟫ - ⟪x 1, x P - x 1⟫ := by rw [← inner_sub_left, c1]; exact hpq
    linarith
  have hPQ : ⟪x 1, x Q - x 1⟫ < ⟪x P, x Q - x 1⟫ := by
    have : 0 < ⟪x P, x Q - x 1⟫ - ⟪x 1, x Q - x 1⟫ := by rw [← inner_sub_left]; exact hpq
    linarith
  -- the `m = 2` corollary for both cap edges
  obtain ⟨-, hsP, -⟩ := (capRim0_five_fails_iff hEP hEPo hQP hRP).mp hUP
  obtain ⟨hsQ, -, -⟩ := (capRim0_five_fails_iff hEQ hEQo hPQ hRQ).mp hUQ
  -- into the core
  have dP := lemmaY_depthP hrep
  have dQ := lemmaY_depthQ hrep
  have dθ := lemmaY_depth hrep σ τ
  have ePQ : ⟪x P, x Q - x 1⟫ = ⟪x 1, x Q - x 1⟫ + ⟪x P - x 1, x Q - x 1⟫ := by
    rw [inner_sub_left]; ring
  have eθP : ⟪x P, σ • (x P - x 1) + τ • (x Q - x 1)⟫ =
      ⟪x 1, σ • (x P - x 1) + τ • (x Q - x 1)⟫ +
        (σ * ⟪x P - x 1, x P - x 1⟫ + τ * ⟪x P - x 1, x Q - x 1⟫) := by
    have : ⟪x P - x 1, σ • (x P - x 1) + τ • (x Q - x 1)⟫ =
        σ * ⟪x P - x 1, x P - x 1⟫ + τ * ⟪x P - x 1, x Q - x 1⟫ := by
      simp only [inner_add_right, real_inner_smul_right]
    rw [← this, inner_sub_left]; ring
  have eθQ : ⟪x Q, σ • (x P - x 1) + τ • (x Q - x 1)⟫ =
      ⟪x 1, σ • (x P - x 1) + τ • (x Q - x 1)⟫ +
        (σ * ⟪x P - x 1, x Q - x 1⟫ + τ * ⟪x Q - x 1, x Q - x 1⟫) := by
    have : ⟪x Q - x 1, σ • (x P - x 1) + τ • (x Q - x 1)⟫ =
        σ * ⟪x P - x 1, x Q - x 1⟫ + τ * ⟪x Q - x 1, x Q - x 1⟫ := by
      simp only [inner_add_right, real_inner_smul_right]; rw [c1]
    rw [← this, inner_sub_left]; ring
  rw [dP s, dP rP] at hsP
  rw [dQ s, ePQ] at hsQ
  obtain ⟨hY1a, hY1p, hY1q, hY1s⟩ := hY1
  obtain ⟨hY2a, hY2p, hY2q, hY2s⟩ := hY2
  simp only [zero_mul, one_mul] at hY1p hY1q hY1s hY2p hY2q hY2s
  refine lemmaY_core (Xr s) (Xp s) (Xq s) (Xr t) (Xp t) (Xq t) (Xr rP) (Xp rP) (Xq rP) σ τ
    ⟪x P - x 1, x P - x 1⟫ ⟪x Q - x 1, x Q - x 1⟫ ⟪x P - x 1, x Q - x 1⟫ ⟪x P - x 1, x R - x 1⟫
    ⟪x Q - x 1, x R - x 1⟫ hσ hτ (real_inner_self_pos.mpr (sub_ne_zero.mpr (hinj.ne hP)))
    real_inner_self_nonneg hpq hY1a ht0 hY1p hY1q hY1s hY2a hm0 hY2p hY2q hY2s (by linarith)
    (by linarith) ?_
  simp only [Fails4, max_le_iff, le_min_iff] at hF
  rw [dθ s, dθ t, eθP, eθQ] at hF
  rcases hF with ⟨⟨h1, h2⟩, h3, -⟩ | ⟨⟨-, h2⟩, -, h4⟩
  · left; constructor <;> linarith
  · right; linarith

end LemmaY

/-- **Lemma 20.18 on `R_bc`, the instance that matters** (`k = bc`: `P = 2`, `Q = 6`, `R = 0`,
`s = 3`, `r_P = 5`, `r_Q = 4`; `θ = 126/046` at the view `(0, 1, ω4)`, rim `(6, 4, 3, 2)`,
`t = 4`).  (Y1): the line `34` meets the plane of `126` at `b ≤ 0`, `c ≤ 1`; (Y2): the line `35`
meets it at `b ≤ 1`, `c ≤ 0` (both need `a3 > a4`, `a3 > a5`).  Then at every metric with
`c_bc > 0 ≥ c_ab, c_ac`, `K` is Rupert. -/
theorem isRupert_lemmaY_bc {x : Fin 7 → ℝ³} (T : Type24 x) (h4 : 0 < omega4 x)
    {r2 r6 : ZMod 5 → Fin 7} (hE2 : CapRim0 x 2 6 0 5 r2)
    (hE2o : (r2 1 = 6 ∧ r2 2 = 3 ∧ r2 3 = 5 ∧ r2 4 = 0) ∨ (r2 1 = 0 ∧ r2 2 = 5 ∧ r2 3 = 3 ∧ r2 4 = 6))
    (hE6 : CapRim0 x 6 2 0 5 r6)
    (hE6o : (r6 1 = 2 ∧ r6 2 = 3 ∧ r6 3 = 4 ∧ r6 4 = 0) ∨ (r6 1 = 0 ∧ r6 2 = 4 ∧ r6 3 = 3 ∧ r6 4 = 2))
    (hθ : QuadTest' (univ.image x) ((x 2 - x 1) + omega4 x • (x 6 - x 1)) (x 6) (x 4) (x 3) (x 2))
    (hY1 : YBelow (oblX2 x) (oblX6 x) (oblX0 x) 3 4 0 1)
    (hY2 : YBelow (oblX2 x) (oblX6 x) (oblX0 x) 3 5 1 0)
    (hbc : 0 < ⟪x 2 - x 1, x 6 - x 1⟫) (hab : ⟪x 2 - x 1, x 0 - x 1⟫ ≤ 0)
    (hac : ⟪x 6 - x 1, x 0 - x 1⟫ ≤ 0) : IsRupert (univ.image x) := by
  rw [← one_smul ℝ (x 2 - x 1)] at hθ
  exact isRupert_lemmaY T.inj (by decide) T.rep260 hE2 hE2o (by decide) hE6 hE6o one_pos h4 hθ hY1
    (T.X0_pos (by decide)).le hY2 (T.X0_pos (by decide)).le hbc hab hac

/-- **Lemma 20.18 on `R_bc`, the mirror** (`θ = 126/025` at the view `(0, ω5, 1)`, rim
`(2, 5, 3, 6)`, `t = 5`): the same two conditions on the lines `34`, `35`, with roles
exchanged. -/
theorem isRupert_lemmaY_bc' {x : Fin 7 → ℝ³} (T : Type24 x) (h5 : 0 < omega5 x)
    {r2 r6 : ZMod 5 → Fin 7} (hE2 : CapRim0 x 2 6 0 5 r2)
    (hE2o : (r2 1 = 6 ∧ r2 2 = 3 ∧ r2 3 = 5 ∧ r2 4 = 0) ∨ (r2 1 = 0 ∧ r2 2 = 5 ∧ r2 3 = 3 ∧ r2 4 = 6))
    (hE6 : CapRim0 x 6 2 0 5 r6)
    (hE6o : (r6 1 = 2 ∧ r6 2 = 3 ∧ r6 3 = 4 ∧ r6 4 = 0) ∨ (r6 1 = 0 ∧ r6 2 = 4 ∧ r6 3 = 3 ∧ r6 4 = 2))
    (hθ : QuadTest' (univ.image x) (omega5 x • (x 2 - x 1) + (x 6 - x 1)) (x 2) (x 5) (x 3) (x 6))
    (hY1 : YBelow (oblX2 x) (oblX6 x) (oblX0 x) 3 4 0 1)
    (hY2 : YBelow (oblX2 x) (oblX6 x) (oblX0 x) 3 5 1 0)
    (hbc : 0 < ⟪x 2 - x 1, x 6 - x 1⟫) (hab : ⟪x 2 - x 1, x 0 - x 1⟫ ≤ 0)
    (hac : ⟪x 6 - x 1, x 0 - x 1⟫ ≤ 0) : IsRupert (univ.image x) := by
  have hrep : ∀ v, x v = x 1 + oblX6 x v • (x 6 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX0 x v • (x 0 - x 1) := fun v => by rw [T.rep260 v]; abel
  rw [← one_smul ℝ (x 6 - x 1), add_comm] at hθ
  exact isRupert_lemmaY T.inj (by decide) hrep hE6 hE6o (by decide) hE2 hE2o one_pos h5 hθ
    hY2.swap (T.X0_pos (by decide)).le hY1.swap (T.X0_pos (by decide)).le
    (by rw [real_inner_comm]; exact hbc) hac hab

/-! ### DS side-safety (Theorems 20.16, 20.17) -/

/-- **The parallel-pair geometry of a depth-separated pair** (the first half of `DepthSepAt`):
for the rim edge `e = [p a, p (a + 1)]`, the corner `p c` is strictly the farthest from the line of
`e` on the screen at `u` (`−n_e ∈ int N_c`).  Affine data of the rim at the view. -/
def ParPairAt {k : ℕ} (p : ZMod k → ℝ³) (u : ℝ³) (a c : ZMod k) : Prop :=
  ∀ j, j ≠ c → det3 (p (a + 1) - p a) (p j - p c) u * det3 (p (a + 1) - p a) (p c - p a) u < 0

/-- **The depth half of a depth-separated pair** (the second half of `DepthSepAt`), for values
`z`: the corners from `c` to `a` lie strictly on one side of `z c`, those from `a + 1` back to `c`
strictly on the other. -/
def DepthSepZ {k : ℕ} (z : ZMod k → ℝ) (a c : ZMod k) : Prop :=
  ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → z c < z (c + s)) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → z (c + s) < z c) ∨
    ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → z (c + s) < z c) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → z c < z (c + s))

theorem depthSepAt_of {k : ℕ} {p : ZMod k → ℝ³} {u : ℝ³} {a c : ZMod k} (h1 : ParPairAt p u a c)
    (h2 : DepthSepZ (fun i => ⟪p i, u⟫) a c) : DepthSepAt p u a c := ⟨h1, h2⟩

theorem DepthSepZ.const_add {k : ℕ} {z : ZMod k → ℝ} {a c : ZMod k} (C : ℝ) (h : DepthSepZ z a c) :
    DepthSepZ (fun i => C + z i) a c := by
  simp only [DepthSepZ, add_lt_add_iff_left]; exact h

/-- **DS-good** (the proxy of Conjecture B_DS): the rim depths `z` are unimodal, or the rim has a
parallel pair (at the view `u`) that `z` depth-separates. -/
def DSGood {k : ℕ} [NeZero k] (p : ZMod k → ℝ³) (u : ℝ³) (z : ZMod k → ℝ) : Prop :=
  IsCyclicUnimodal z ∨ ∃ a c : ZMod k, ParPairAt p u a c ∧ DepthSepZ z a c

/-- **DS-safe on a quadrant** (§20.28): for every column `(g, h_y, h_w)` of a Gram matrix with
`g > 0`, `h_y ∈ Qy`, `h_w ∈ Qw` and distinct rim depths `g X_x + h_y X_y + h_w X_w`, the cap edge
`E_x` (rim `x ∘ r` at the view `x ax − x 1`) is DS-good.  The depths are X-only; the parallel pairs
are the affine data of the rim at the view (as in `CapRim0`).  `Qy = (0 < ·)`, `Qw = ⊤` is
*DS-safe on side `y`*; the quadrants `Q_x(S)` of the regions `R_S` take `0 < ·` or `· ≤ 0`. -/
def DSSafeQ (x : Fin 7 → ℝ³) (ax : Fin 7) (cx cy cw : Fin 7 → ℝ) {k : ℕ} [NeZero k]
    (r : ZMod k → Fin 7) (Qy Qw : ℝ → Prop) : Prop :=
  ∀ g hy hw : ℝ, 0 < g → Qy hy → Qw hw →
    Function.Injective (fun i => cx (r i) * g + cy (r i) * hy + cw (r i) * hw) →
    DSGood (fun i => x (r i)) (x ax - x 1) (fun i => cx (r i) * g + cy (r i) * hy + cw (r i) * hw)

/-- Safety in the old sense (side-safety, 20.8′) implies DS-safety on that side. -/
theorem SideSafe.dsSafeQ {x : Fin 7 → ℝ³} {ax : Fin 7} {cx cy cw : Fin 7 → ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} (h : SideSafe cx cy cw r) :
    DSSafeQ x ax cx cy cw r (0 < ·) (fun _ => True) :=
  fun g hy hw hg h1 _ hinj => Or.inl (h g hy hw hg h1 hinj)

/-- DS-safety is monotone in the quadrant. -/
theorem DSSafeQ.mono {x : Fin 7 → ℝ³} {ax : Fin 7} {cx cy cw : Fin 7 → ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} {Qy Qw Qy' Qw' : ℝ → Prop} (h : DSSafeQ x ax cx cy cw r Qy Qw)
    (hy : ∀ t, Qy' t → Qy t) (hw : ∀ t, Qw' t → Qw t) : DSSafeQ x ax cx cy cw r Qy' Qw' :=
  fun g p q hg h1 h2 hinj => h g p q hg (hy p h1) (hw q h2) hinj

/-- **A cap edge DS-safe on a quadrant certifies `K`** at every metric whose column at `x` lies in
that quadrant (Theorem 7.3 if unimodal, Theorem 8.10 with 8.9 for a depth-separated pair; the
ties and horizontal double normals are those of the rim data `CapRim0`). -/
theorem isRupert_capEdge_dsSafe {x : Fin 7 → ℝ³} (hinj : Function.Injective x)
    {ax ay aw : Fin 7} {cx cy cw : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + cx v • (x ax - x 1) + cy v • (x ay - x 1) + cw v • (x aw - x 1))
    (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7} (hR : CapRim0 x ax ay aw k r)
    {Qy Qw : ℝ → Prop} (hS : DSSafeQ x ax cx cy cw r Qy Qw)
    (hy : Qy ⟪x ay - x 1, x ax - x 1⟫) (hw : Qw ⟪x aw - x 1, x ax - x 1⟫) :
    IsRupert (univ.image x) := by
  have hd : ∀ v, ⟪x v, x ax - x 1⟫ = ⟪x 1, x ax - x 1⟫ + (cx v * ⟪x ax - x 1, x ax - x 1⟫ +
      cy v * ⟪x ay - x 1, x ax - x 1⟫ + cw v * ⟪x aw - x 1, x ax - x 1⟫) := by
    intro v; rw [hrep v]; simp only [inner_add_left, real_inner_smul_left]; ring
  have hu : x ax - x 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne hax)
  have hz := hR.2.2.2.2.2.1
  have hfun : (fun i => ⟪x (r i), x ax - x 1⟫) = fun i => ⟪x 1, x ax - x 1⟫ +
      (cx (r i) * ⟪x ax - x 1, x ax - x 1⟫ + cy (r i) * ⟪x ay - x 1, x ax - x 1⟫ +
        cw (r i) * ⟪x aw - x 1, x ax - x 1⟫) := funext fun i => hd (r i)
  have hinj' : Function.Injective (fun i => cx (r i) * ⟪x ax - x 1, x ax - x 1⟫ +
      cy (r i) * ⟪x ay - x 1, x ax - x 1⟫ + cw (r i) * ⟪x aw - x 1, x ax - x 1⟫) := by
    intro i j e
    exact hz (by simp only at e ⊢; rw [hd (r i), hd (r j), e])
  rcases hS _ _ _ (real_inner_self_pos.mpr hu) hy hw hinj' with hU | ⟨a, c, hpp, hds⟩
  · refine isRupert_capRim0 hinj hax hR ?_
    rw [hfun]
    exact isCyclicUnimodal_const_add _ hU
  · refine isRupert_capRim0_depthSeparated hinj hax hR (a := a) (c := c) (depthSepAt_of hpp ?_)
    rw [hfun]
    exact hds.const_add _

/-- The sign of a cosine on the region `R_S`: `> 0` for the cosines in `S` (`true`), `≤ 0` for the
others. -/
def RegSign : Bool → ℝ → Prop
  | true, h => 0 < h
  | false, h => h ≤ 0

theorem regSign_decide (h : ℝ) : RegSign (decide (0 < h)) h := by
  by_cases hh : 0 < h
  · simp only [hh, decide_true, RegSign]
  · simp only [hh, decide_false, RegSign]; exact not_lt.mp hh

namespace Type24

/-- `E_2` (view `e_b`, rim from `0` to `6`) is DS-safe on the quadrant `h_ab ∈ Qa`, `h_bc ∈ Qc`. -/
def DSSafeE2 (x : Fin 7 → ℝ³) (Qa Qc : ℝ → Prop) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 2 0 6 k r ∧ DSSafeQ x 2 (oblX2 x) (oblX0 x) (oblX6 x) r Qa Qc

/-- `E_6` (view `e_c`, rim from `2` to `0`) is DS-safe on the quadrant `h_bc ∈ Qb`, `h_ac ∈ Qa`. -/
def DSSafeE6 (x : Fin 7 → ℝ³) (Qb Qa : ℝ → Prop) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 6 2 0 k r ∧ DSSafeQ x 6 (oblX6 x) (oblX2 x) (oblX0 x) r Qb Qa

/-- `E_0` (view `e_a`, rim from `2` to `6`) is DS-safe on the quadrant `h_ab ∈ Qb`, `h_ac ∈ Qc`. -/
def DSSafeE0 (x : Fin 7 → ℝ³) (Qb Qc : ℝ → Prop) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 0 2 6 k r ∧ DSSafeQ x 0 (oblX0 x) (oblX2 x) (oblX6 x) r Qb Qc

/-- **Each cosine is seen on a DS-safe side** (the hypothesis of Theorem 20.16): `c_ab` by `E_2`
or `E_0`, `c_ac` by `E_6` or `E_0`, `c_bc` by `E_2` or `E_6`. -/
def DSSideCovered (x : Fin 7 → ℝ³) : Prop :=
  (DSSafeE2 x (0 < ·) (fun _ => True) ∨ DSSafeE0 x (0 < ·) (fun _ => True)) ∧
    (DSSafeE6 x (fun _ => True) (0 < ·) ∨ DSSafeE0 x (fun _ => True) (0 < ·)) ∧
    (DSSafeE2 x (fun _ => True) (0 < ·) ∨ DSSafeE6 x (0 < ·) (fun _ => True))

/-- **The region `R_S` is covered by a DS-safe cap edge** (`S` given by the signs `sab`, `sac`,
`sbc`; the quadrant `Q_x(S)` of each cap edge). -/
def DSRegion (x : Fin 7 → ℝ³) (sab sac sbc : Bool) : Prop :=
  DSSafeE2 x (RegSign sab) (RegSign sbc) ∨ DSSafeE6 x (RegSign sbc) (RegSign sac) ∨
    DSSafeE0 x (RegSign sab) (RegSign sac)

/-- **The hypothesis of Theorem 20.17**: every one of the seven regions `R_S` (`S ≠ ∅`) is covered
by a cap edge DS-safe on its quadrant. -/
def DSRegionsCovered (x : Fin 7 → ℝ³) : Prop :=
  ∀ sab sac sbc : Bool, (sab || sac || sbc) = true → DSRegion x sab sac sbc

/-- Theorem 20.16 is the case of 20.17 where the quadrant comes from a cosine `k ∈ S` seen on a
DS-safe side. -/
theorem DSSideCovered.regions {x : Fin 7 → ℝ³} (h : DSSideCovered x) : DSRegionsCovered x := by
  obtain ⟨hab, hac, hbc⟩ := h
  intro sab sac sbc hS
  have tt : ∀ (b : Bool) (t : ℝ), RegSign b t → True := fun _ _ _ => trivial
  have tp : ∀ t : ℝ, RegSign true t → 0 < t := fun _ h => h
  cases sab
  · cases sac
    · cases sbc
      · exact absurd hS (by decide)
      · rcases hbc with ⟨k, i, r, hR, hS'⟩ | ⟨k, i, r, hR, hS'⟩
        · exact Or.inl ⟨k, i, r, hR, hS'.mono (tt _) (tp)⟩
        · exact Or.inr (Or.inl ⟨k, i, r, hR, hS'.mono tp (tt _)⟩)
    · rcases hac with ⟨k, i, r, hR, hS'⟩ | ⟨k, i, r, hR, hS'⟩
      · exact Or.inr (Or.inl ⟨k, i, r, hR, hS'.mono (tt _) tp⟩)
      · exact Or.inr (Or.inr ⟨k, i, r, hR, hS'.mono (tt _) tp⟩)
  · rcases hab with ⟨k, i, r, hR, hS'⟩ | ⟨k, i, r, hR, hS'⟩
    · exact Or.inl ⟨k, i, r, hR, hS'.mono tp (tt _)⟩
    · exact Or.inr (Or.inr ⟨k, i, r, hR, hS'.mono tp (tt _)⟩)

/-- Side-safety in the old sense (20.8′) gives DS side-safety. -/
theorem SideCovered.ds {x : Fin 7 → ℝ³} (h : SideCovered x) : DSSideCovered x := by
  obtain ⟨hab, hac, hbc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rcases hab with ⟨k, i, r, hR, hS⟩ | ⟨k, i, r, hR, hS⟩
    · exact Or.inl ⟨k, i, r, hR, hS.dsSafeQ⟩
    · exact Or.inr ⟨k, i, r, hR, hS.dsSafeQ⟩
  · rcases hac with ⟨k, i, r, hR, hS⟩ | ⟨k, i, r, hR, hS⟩
    · refine Or.inl ⟨k, i, r, hR, ?_⟩
      intro g p q hg _ h2 hinj
      have e : (fun i => oblX6 x (r i) * g + oblX2 x (r i) * p + oblX0 x (r i) * q) =
          fun i => oblX6 x (r i) * g + oblX0 x (r i) * q + oblX2 x (r i) * p :=
        funext fun i => by ring
      rw [e] at hinj ⊢
      exact Or.inl (hS g q p hg h2 hinj)
    · refine Or.inr ⟨k, i, r, hR, ?_⟩
      intro g p q hg _ h2 hinj
      have e : (fun i => oblX0 x (r i) * g + oblX2 x (r i) * p + oblX6 x (r i) * q) =
          fun i => oblX0 x (r i) * g + oblX6 x (r i) * q + oblX2 x (r i) * p :=
        funext fun i => by ring
      rw [e] at hinj ⊢
      exact Or.inl (hS g q p hg h2 hinj)
  · rcases hbc with ⟨k, i, r, hR, hS⟩ | ⟨k, i, r, hR, hS⟩
    · refine Or.inl ⟨k, i, r, hR, ?_⟩
      intro g p q hg _ h2 hinj
      have e : (fun i => oblX2 x (r i) * g + oblX0 x (r i) * p + oblX6 x (r i) * q) =
          fun i => oblX2 x (r i) * g + oblX6 x (r i) * q + oblX0 x (r i) * p :=
        funext fun i => by ring
      rw [e] at hinj ⊢
      exact Or.inl (hS g q p hg h2 hinj)
    · exact Or.inr ⟨k, i, r, hR, hS.dsSafeQ⟩

end Type24

/-- **One region, Rupert form**: if `R_S` is covered by a DS-safe cap edge and the metric lies in
`R_S` (signs of `h_ab`, `h_ac`, `h_bc` as `S` says), `K` is Rupert. -/
theorem isRupert_type24_dsRegion {x : Fin 7 → ℝ³} (T : Type24 x) {sab sac sbc : Bool}
    (h : Type24.DSRegion x sab sac sbc) (hab : RegSign sab ⟪x 0 - x 1, x 2 - x 1⟫)
    (hac : RegSign sac ⟪x 0 - x 1, x 6 - x 1⟫) (hbc : RegSign sbc ⟪x 2 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) := by
  have c1 := real_inner_comm (x 0 - x 1) (x 2 - x 1)
  have c2 := real_inner_comm (x 0 - x 1) (x 6 - x 1)
  have c3 := real_inner_comm (x 2 - x 1) (x 6 - x 1)
  rcases h with ⟨k, _, r, hR, hS⟩ | ⟨k, _, r, hR, hS⟩ | ⟨k, _, r, hR, hS⟩
  · exact isRupert_capEdge_dsSafe T.inj T.rep2 (by decide) hR hS hab (by rw [c3]; exact hbc)
  · exact isRupert_capEdge_dsSafe T.inj T.rep6 (by decide) hR hS hbc hac
  · exact isRupert_capEdge_dsSafe T.inj T.rep (by decide) hR hS (by rw [c1]; exact hab)
      (by rw [c2]; exact hac)

/-- **Theorem 20.17 (regions), Rupert form**: if each of the seven regions `R_S` is covered by a
cap edge DS-safe on its quadrant, `K` is Rupert at every metric with some face angle at `1` acute
(the DS form of Conjecture A), off the ties and horizontal double normals carried by the rim
data. -/
theorem isRupert_type24_dsRegions {x : Fin 7 → ℝ³} (T : Type24 x) (hcov : Type24.DSRegionsCovered x)
    (hacute : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) := by
  refine isRupert_type24_dsRegion T (hcov _ _ _ ?_) (regSign_decide _) (regSign_decide _)
    (regSign_decide _)
  rcases hacute with h | h | h <;> simp [h]

/-- **Theorem 20.16 (DS side-safety), Rupert form**: if each cosine at `1` is seen on a DS-safe
side by a cap edge and some face angle at `1` is acute, `K` is Rupert. -/
theorem isRupert_type24_dsSide {x : Fin 7 → ℝ³} (T : Type24 x) (hside : Type24.DSSideCovered x)
    (hacute : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) :=
  isRupert_type24_dsRegions T hside.regions hacute

/-! ### The DS form of Conjecture A by uniform statements (20.17, 20.18, 20.19) -/

namespace Type24

/-- **Lemma 20.18's data on `R_bc`** (Y0)–(Y2): `E_2` with the rim `(1, 6, 3, 5, 0)`, `E_6` with
`(1, 2, 3, 4, 0)` (either orientation), the lines `34`, `35` meeting the plane of `126` as (Y1),
(Y2) say, and `θ = 126/046` (rim `(6, 4, 3, 2)`, `ω4 > 0`) or its mirror `126/025` (rim
`(2, 5, 3, 6)`, `ω5 > 0`) certified up to its depth pattern. -/
def LemmaYbc (x : Fin 7 → ℝ³) : Prop :=
  ∃ r2 r6 : ZMod 5 → Fin 7, CapRim0 x 2 6 0 5 r2 ∧
    ((r2 1 = 6 ∧ r2 2 = 3 ∧ r2 3 = 5 ∧ r2 4 = 0) ∨ (r2 1 = 0 ∧ r2 2 = 5 ∧ r2 3 = 3 ∧ r2 4 = 6)) ∧
    CapRim0 x 6 2 0 5 r6 ∧
    ((r6 1 = 2 ∧ r6 2 = 3 ∧ r6 3 = 4 ∧ r6 4 = 0) ∨ (r6 1 = 0 ∧ r6 2 = 4 ∧ r6 3 = 3 ∧ r6 4 = 2)) ∧
    YBelow (oblX2 x) (oblX6 x) (oblX0 x) 3 4 0 1 ∧ YBelow (oblX2 x) (oblX6 x) (oblX0 x) 3 5 1 0 ∧
    ((0 < omega4 x ∧
        QuadTest' (univ.image x) ((x 2 - x 1) + omega4 x • (x 6 - x 1)) (x 6) (x 4) (x 3) (x 2)) ∨
      (0 < omega5 x ∧
        QuadTest' (univ.image x) (omega5 x • (x 2 - x 1) + (x 6 - x 1)) (x 2) (x 5) (x 3) (x 6)))

/-- **The acute side covered by uniform statements** (the table of §20.31): a planar-quad test
(Corollary 20.19, every metric), or every region `R_S` covered by a DS-safe cap edge (Theorem
20.17), the single region `R_bc` possibly by Lemma 20.18 instead. -/
def AcuteCovered (x : Fin 7 → ℝ³) : Prop :=
  (Nonempty (Face16 x {0, 3, 4, 5}) ∧ ∃ u, QuadTest' (univ.image x) u (x 0) (x 4) (x 3) (x 5)) ∨
    ∀ sab sac sbc : Bool, (sab || sac || sbc) = true →
      DSRegion x sab sac sbc ∨ (sab = false ∧ sac = false ∧ sbc = true ∧ LemmaYbc x)

theorem DSRegionsCovered.acute {x : Fin 7 → ℝ³} (h : DSRegionsCovered x) : AcuteCovered x :=
  Or.inr fun sab sac sbc hS => Or.inl (h sab sac sbc hS)

end Type24

/-- **Lemma 20.18 on `R_bc`, Rupert form from its data.** -/
theorem isRupert_type24_lemmaYbc {x : Fin 7 → ℝ³} (T : Type24 x) (hY : Type24.LemmaYbc x)
    (hbc : 0 < ⟪x 2 - x 1, x 6 - x 1⟫) (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0)
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) : IsRupert (univ.image x) := by
  obtain ⟨r2, r6, hE2, hE2o, hE6, hE6o, hY1, hY2, hθ⟩ := hY
  have hab' : ⟪x 2 - x 1, x 0 - x 1⟫ ≤ 0 := by rw [real_inner_comm]; exact hab
  have hac' : ⟪x 6 - x 1, x 0 - x 1⟫ ≤ 0 := by rw [real_inner_comm]; exact hac
  rcases hθ with ⟨h4, hθ⟩ | ⟨h5, hθ⟩
  · exact isRupert_lemmaY_bc T h4 hE2 hE2o hE6 hE6o hθ hY1 hY2 hbc hab' hac'
  · exact isRupert_lemmaY_bc' T h5 hE2 hE2o hE6 hE6o hθ hY1 hY2 hbc hab' hac'

/-- **The DS form of Conjecture A from the uniform statements 20.17, 20.18, 20.19**: under
`AcuteCovered`, `K` is Rupert at every metric with some face angle at `1` acute. -/
theorem isRupert_type24_acute {x : Fin 7 → ℝ³} (T : Type24 x) (hA : Type24.AcuteCovered x)
    (hacute : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) := by
  rcases hA with ⟨⟨F⟩, u, hQ⟩ | hA
  · exact isRupert_type24_planarQuad F hQ
  have hS : (decide (0 < ⟪x 0 - x 1, x 2 - x 1⟫) || decide (0 < ⟪x 0 - x 1, x 6 - x 1⟫) ||
      decide (0 < ⟪x 2 - x 1, x 6 - x 1⟫)) = true := by
    rcases hacute with h | h | h <;> simp [h]
  rcases hA _ _ _ hS with h | ⟨h1, h2, h3, hY⟩
  · exact isRupert_type24_dsRegion T h (regSign_decide _) (regSign_decide _) (regSign_decide _)
  · simp only [decide_eq_false_iff_not, not_lt, decide_eq_true_eq] at h1 h2 h3
    exact isRupert_type24_lemmaYbc T hY h3 h1 h2

end Minimality

end
