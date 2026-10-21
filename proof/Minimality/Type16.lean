module

public import Minimality.Type29

@[expose] public section

/-!
# Type 16: Lemma 11.U, the test at `35` (`FEWER-FACES-PROOFS.md` §11 addendum)

Type 16 (labels of `typeb_lib.load('16-8f')`): the quadrilaterals `0235` (cyclic
`2, 0, 3, 5`) and `1356` (cyclic `3, 6, 1, 5`), the triangles `024`, `036`, `046`,
`145`, `146`, `245` (`Type16`, facet functions on the seven points).  The two
quadrilaterals meet in the edge `35`, the line `ℓ`.

At the view along `ℓ` (depth `z = ⟪·, x 5 − x 3⟫`), each quadrilateral projects onto a
ray from the image `p` of `3` and `5`; its two other vertices are the *far end* and a
*middle* over the chord from the axle to the far end (`MidOf`).  With far ends
`A ∈ {0, 2}`, `B ∈ {1, 6}`, the reduced polygons are `conv {v, A, 4, B}`
(`v = 3` or `5`), or the triangles `v, A, B` when `4` is hidden.

* **Lemma 11.U** (`isRupert_type16_35`): unless *35 is bad* (`Type16Bad35`: `4` a
  corner and `min (z 3, z 4) > max (z A, z B)`), one closing at `35` is unimodal, and
  Theorem 8.9 with Theorem 7.3 gives a passage (in general position, without horizontal
  double normals).  Part (b), `max (z 5, z 4) > min (z A, z B)` at a corner, is
  `lemmaU_b_real`: the face `245` lies above the chord `A B` over the crossing of the
  diagonals (only this face is needed, and the inequality is strict).
* **Corollary 11.Ua** (`type16_not_bad35_of_far`, `type16_not_bad35_of_acute`): a far
  end above `3` (`z A > z 3`), in particular an acute angle at `3` of either
  quadrilateral, rules out "35 bad".

The core works in the screen coordinates `r = f_B / f_B A`, `q = f_A / f_A B` of the
view along `ℓ` (`frame_coords`, `det3_frame`): `p = (0, 0)`, `A = (1, 0)`, `B = (0, 1)`,
the middles on the two axes, `4 = (r, q)` with `r, q > 0`; `4` is a corner iff
`r + q > 1`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Tools -/

/-- An affine function at a point given in a frame of three directions. -/
theorem affine_frame3 {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (o p q w : ℝ³) (r s t : ℝ) :
    f (o + r • (p - o) + s • (q - o) + t • (w - o)) =
      f o + r * (f p - f o) + s * (f q - f o) + t * (f w - f o) := by
  have h := hf (o + r • (p - o) + s • (q - o) + t • (w - o)) o
  rw [show o + r • (p - o) + s • (q - o) + t • (w - o) - o =
      r • (p - o) + s • (q - o) + t • (w - o) by abel,
    inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, ← hf, ← hf, ← hf] at h
  linarith

/-- The depth `⟪·, u⟫` is affine with linear part `u`. -/
theorem inner_affine (u : ℝ³) : ∀ y z : ℝ³, ⟪y, u⟫ - ⟪z, u⟫ = ⟪u, y - z⟫ := by
  intro y z; rw [← inner_sub_left, real_inner_comm]

/-- Orientations at the view `u` in a frame `o; a, b, u`: only the `a`, `b`
coordinates count. -/
theorem det3_frame (o a b u X Y Z : ℝ³) (rX qX tX rY qY tY rZ qZ tZ : ℝ)
    (hX : X = o + rX • a + qX • b + tX • u) (hY : Y = o + rY • a + qY • b + tY • u)
    (hZ : Z = o + rZ • a + qZ • b + tZ • u) :
    det3 (Y - X) (Z - X) u = ((rY - rX) * (qZ - qX) - (qY - qX) * (rZ - rX)) * det3 a b u := by
  subst hX hY hZ
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The value matrix of `g_A`, `g_B` and the depth on the frame `o; A, B, v`. -/
theorem frame_hdet {gA gB : ℝ³ → ℝ} {o v A B : ℝ³}
    (gAo : gA o = 0) (gAv : gA v = 0) (gAA : gA A = 0) (gAB : gA B ≠ 0)
    (gBo : gB o = 0) (gBv : gB v = 0) (gBB : gB B = 0) (gBA : gB A ≠ 0) (hov : o ≠ v) :
    (gA A - gA o) * ((gB B - gB o) * (⟪v, v - o⟫ - ⟪o, v - o⟫) -
        (gB v - gB o) * (⟪B, v - o⟫ - ⟪o, v - o⟫)) -
      (gA B - gA o) * ((gB A - gB o) * (⟪v, v - o⟫ - ⟪o, v - o⟫) -
        (gB v - gB o) * (⟪A, v - o⟫ - ⟪o, v - o⟫)) +
      (gA v - gA o) * ((gB A - gB o) * (⟪B, v - o⟫ - ⟪o, v - o⟫) -
        (gB B - gB o) * (⟪A, v - o⟫ - ⟪o, v - o⟫)) ≠ 0 := by
  have hU : 0 < ⟪v, v - o⟫ - ⟪o, v - o⟫ := by
    rw [← inner_sub_left]; exact real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hov))
  rw [gAo, gAv, gAA, gBo, gBv, gBB]
  simp only [sub_zero, zero_mul, zero_sub, sub_self, mul_zero, sub_zero]
  have := mul_ne_zero gAB (mul_ne_zero gBA hU.ne')
  intro h; apply this; linarith

/-- **Screen coordinates of the view along `o v`.**  If `g_A` vanishes on the plane
`o v A` and `g_B` on the plane `o v B` (and not at `B`, resp. `A`), every point is
`o + r (A − o) + q (B − o) + t (v − o)` with `r = g_B X / g_B A`, `q = g_A X / g_A B`. -/
theorem frame_coords {gA gB : ℝ³ → ℝ} {NA NB : ℝ³} (hA : ∀ y z, gA y - gA z = ⟪NA, y - z⟫)
    (hB : ∀ y z, gB y - gB z = ⟪NB, y - z⟫) {o v A B : ℝ³}
    (gAo : gA o = 0) (gAv : gA v = 0) (gAA : gA A = 0) (gAB : gA B ≠ 0)
    (gBo : gB o = 0) (gBv : gB v = 0) (gBB : gB B = 0) (gBA : gB A ≠ 0) (hov : o ≠ v)
    (X : ℝ³) :
    ∃ t : ℝ, X = o + (gB X / gB A) • (A - o) + (gA X / gA B) • (B - o) + t • (v - o) := by
  set u := v - o
  have hU : 0 < ⟪v, u⟫ - ⟪o, u⟫ := by
    rw [← inner_sub_left]; exact real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hov))
  set r := gB X / gB A
  set q := gA X / gA B
  refine ⟨(⟪X, u⟫ - ⟪o, u⟫ - r * (⟪A, u⟫ - ⟪o, u⟫) - q * (⟪B, u⟫ - ⟪o, u⟫)) /
    (⟪v, u⟫ - ⟪o, u⟫), ?_⟩
  refine eq_of_affine3 hA hB (inner_affine u) o A B v
    (frame_hdet gAo gAv gAA gAB gBo gBv gBB gBA hov) ?_ ?_ ?_
  · rw [affine_frame3 hA, gAo, gAv, gAA]; simp only [q]; field_simp; ring
  · rw [affine_frame3 hB, gBo, gBv, gBB]; simp only [r]; field_simp; ring
  · rw [affine_frame3 (inner_affine u)]; field_simp; ring

/-- The frame `o; A − o, B − o, v − o` is a basis. -/
theorem frame16_det_ne {gA gB : ℝ³ → ℝ} {NA NB : ℝ³} (hA : ∀ y z, gA y - gA z = ⟪NA, y - z⟫)
    (hB : ∀ y z, gB y - gB z = ⟪NB, y - z⟫) {o v A B : ℝ³}
    (gAo : gA o = 0) (gAv : gA v = 0) (gAA : gA A = 0) (gAB : gA B ≠ 0)
    (gBo : gB o = 0) (gBv : gB v = 0) (gBB : gB B = 0) (gBA : gB A ≠ 0) (hov : o ≠ v) :
    det3 (A - o) (B - o) (v - o) ≠ 0 :=
  det3_ne_zero_of_affine3 hA hB (inner_affine (v - o)) o A B v
    (frame_hdet gAo gAv gAA gAB gBo gBv gBB gBA hov)

/-! ### Closings at an edge view with no extra points -/

/-- Theorem 8.9 with Theorem 7.3 for a 4-cycle rim `y, A, y', B` (counterclockwise at
the view `u`, closing at `y`, the other axle end `w = y − h u`), when every point of
`V` is on the rim, a middle or `w`, and the rim's depths are not weakly separated. -/
theorem isRupert_quad_rim (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {w y y' A B : ℝ³} (h : ℝ)
    (hh : h ≠ 0) (hw : w = y - h • u) (hwV : w ∈ V) (hyV : y ∈ V) (hy'V : y' ∈ V)
    (hAV : A ∈ V) (hBV : B ∈ V) (hyM : y ∉ M) (hAM : A ∉ M) (hy'M : y' ∉ M) (hBM : B ∉ M)
    (t1 : 0 < det3 (A - y) (y' - y) u) (t2 : 0 < det3 (A - y) (B - y) u)
    (t3 : 0 < det3 (y' - A) (B - A) u) (t4 : 0 < det3 (y' - A) (y - A) u)
    (t5 : 0 < det3 (B - y') (y - y') u) (t6 : 0 < det3 (B - y') (A - y') u)
    (t7 : 0 < det3 (y - B) (A - B) u) (t8 : 0 < det3 (y - B) (y' - B) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y → z ≠ A → z ≠ y' → z ≠ B → False)
    (hinj : Function.Injective (quad ⟪y, u⟫ ⟪A, u⟫ ⟪y', u⟫ ⟪B, u⟫))
    (hN : NWS4 (quad ⟪y, u⟫ ⟪A, u⟫ ⟪y', u⟫ ⟪B, u⟫))
    (hM : ∀ m ∈ M, EdgeMiddle u y w A B h m) (hnd : NoHDNAt (V.erase w) u) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView V M u hu (k := 4) (by norm_num) (quad y A y' B) 0 w h hwV
    (by simp only [quad_0]; exact hw) hh ?_ ?_ ?_ ?_ ?_ hnd ?_
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyV, hAV, hy'V, hBV]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyM, hAM, hy'M, hBM]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [t1, t2, t3, t4, t5, t6, t7, t8]
  · intro z hz hzM hzw hzx
    exact (hrest z hz hzM hzw (hzx 0) (hzx 1) (hzx 2) (hzx 3)).elim
  · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 hinj hN
  · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
    simpa only [quad_0, quad_1, quad_3] using hM

/-! ### Lemma 11.U (b), in reals -/

/-- **Lemma 11.U (b).**  With `z P = z o + r (z A − z o) + q (z B − z o) + τ (z v − z o)`
(`r, q > 0`, `r + q > 1`: the corner `P` beyond the chord `A B`), and an affine `g`
vanishing at `v` and `P` (the face `245`), negative at `o` and weakly negative at `A`,
`B` (strictly at one of them), `max (z v, z P) > min (z A, z B)`. -/
theorem lemmaU_b_real {zo zv zA zB zP ho hA hB r q τ : ℝ} (hzv : zo < zv)
    (hzP : zP = zo + r * (zA - zo) + q * (zB - zo) + τ * (zv - zo))
    (hP : 0 = ho + r * (hA - ho) + q * (hB - ho) + τ * (0 - ho)) (hho : ho < 0)
    (hhA : hA ≤ 0) (hhB : hB ≤ 0) (hAB : hA < 0 ∨ hB < 0) (hr : 0 < r) (hq : 0 < q)
    (hrq : 1 < r + q) : ¬ max zv zP ≤ min zA zB := by
  intro hbad
  simp only [max_le_iff, le_min_iff] at hbad
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbad
  have hK : r * hA + q * hB < 0 := by
    rcases hAB with h | h
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hq.le hhB]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hr.le hhA]
  have e : ho * (τ - (1 - r - q)) = r * hA + q * hB := by linear_combination hP
  have hτ : 0 < τ - (1 - r - q) := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hho.le hc]
  have hW : 0 < zv - zo := by linarith
  rcases le_total zA zB with hab | hab
  · nlinarith [mul_pos hτ hW, mul_nonneg (show 0 ≤ r + q - 1 by linarith)
      (show 0 ≤ zA - zv by linarith), mul_nonneg hq.le (show 0 ≤ zB - zA by linarith)]
  · nlinarith [mul_pos hτ hW, mul_nonneg (show 0 ≤ r + q - 1 by linarith)
      (show 0 ≤ zB - zv by linarith), mul_nonneg hr.le (show 0 ≤ zA - zB by linarith)]

/-- The closing decision of Lemma 11.U (c): if the rim `v, A, P, B` is weakly
separated, then (by (b)) `P` and `v` are above both far ends, and unless `35` is bad
the rim `o, A, P, B` is not. -/
theorem lemmaU_nws4 {zo zv zA zB zP : ℝ}
    (hinj : zo ≠ zA ∧ zo ≠ zB ∧ zA ≠ zP ∧ zB ≠ zP)
    (hb : ¬ max zv zP ≤ min zA zB) (hbad : ¬ max zA zB < min zo zP)
    (hN : ¬ NWS4 (quad zv zA zP zB)) : NWS4 (quad zo zA zP zB) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN ⊢
  simp only [max_le_iff, le_min_iff, not_and_or, not_le, max_lt_iff, lt_min_iff,
    not_lt] at hb hbad
  obtain ⟨h1, h2, h3, h4⟩ := hinj
  rcases hN with ⟨n1, n2, n3, n4⟩ | ⟨n1, n2, n3, n4⟩
  · have hPA : zA < zP := lt_of_le_of_ne n3 h3
    have hPB : zB < zP := lt_of_le_of_ne n4 h4
    refine ⟨?_, Or.inr (Or.inr (Or.inl hPA))⟩
    rcases hbad with (h | h) | (h | h) <;>
      first
        | exact Or.inl (lt_of_le_of_ne h h1)
        | exact Or.inr (Or.inl (lt_of_le_of_ne h h2))
        | (exfalso; linarith)
  · rcases hb with (h | h) | (h | h) <;> linarith

/-! ### Lemma 11.U in screen coordinates -/

section Core

variable {o v A mA B mB P : ℝ³} {s t s' t' r q τ : ℝ}

/-- **Lemma 11.U, in the coordinates of the view along `o v`** (counterclockwise
`o, A, B`, `E > 0`).  The seven points are the axle `o, v`, the far ends `A`, `B`, the
middles `mA = o + s (A − o) + t (v − o)`, `mB = o + s' (B − o) + t' (v − o)`
(`0 < s, s' < 1`; `t, t + s − 1 ≠ 0` say that `mA` is on neither line `o A`, `v A`),
and `P = o + r (A − o) + q (B − o) + τ (v − o)` with `r, q > 0`, `r + q ≠ 1`.  Given (b)
and "not bad" at a corner (`r + q > 1`), distinct depths and no horizontal double
normals, the seven points are Rupert. -/
theorem lemmaU_coords_pos
    (hnodup : [o, v, A, mA, B, mB, P].Nodup)
    (hmA : mA = o + s • (A - o) + t • (v - o)) (hs0 : 0 < s) (hs1 : s < 1) (ht : t ≠ 0)
    (hts : t + s - 1 ≠ 0)
    (hmB : mB = o + s' • (B - o) + t' • (v - o)) (hs0' : 0 < s') (hs1' : s' < 1)
    (ht' : t' ≠ 0) (hts' : t' + s' - 1 ≠ 0)
    (hP : P = o + r • (A - o) + q • (B - o) + τ • (v - o)) (hr : 0 < r) (hq : 0 < q)
    (hrq : r + q ≠ 1) (hE : 0 < det3 (A - o) (B - o) (v - o))
    (hinj : ∀ X Y, (X = o ∨ X = v ∨ X = A ∨ X = B ∨ X = P) → (Y = A ∨ Y = B ∨ Y = P) →
      X ≠ Y → ⟪X, v - o⟫ ≠ ⟪Y, v - o⟫)
    (hb : 1 < r + q → ¬ max ⟪v, v - o⟫ ⟪P, v - o⟫ ≤ min ⟪A, v - o⟫ ⟪B, v - o⟫)
    (hbad : 1 < r + q → ¬ max ⟪A, v - o⟫ ⟪B, v - o⟫ < min ⟪o, v - o⟫ ⟪P, v - o⟫)
    (hnd : NoHDNAt (({o, v, A, mA, B, mB, P} : Finset ℝ³).erase o) (v - o) ∧
      NoHDNAt (({o, v, A, mA, B, mB, P} : Finset ℝ³).erase v) (v - o)) :
    IsRupert ({o, v, A, mA, B, mB, P} : Finset ℝ³) := by
  classical
  have hnd' := hnodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hov, hoA, homA, hoB, homB, hoP⟩, ⟨hvA, hvmA, hvB, hvmB, hvP⟩,
    ⟨hAmA, hAB, hAmB, hAP⟩, ⟨hmAB, hmAmB, hmAP⟩, ⟨hBmB, hBP⟩, hmBP, -⟩ := hnd'
  set u := v - o with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hov)
  set V : Finset ℝ³ := {o, v, A, mA, B, mB, P} with hV
  set E := det3 (A - o) (B - o) u
  -- coordinates of the seven points
  have co : o = o + (0 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + (0 : ℝ) • u := by simp
  have cv : v = o + (0 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + (1 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul, u]; abel
  have cA : A = o + (1 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have cB : B = o + (0 : ℝ) • (A - o) + (1 : ℝ) • (B - o) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have cP : P = o + r • (A - o) + q • (B - o) + τ • u := hP
  have D := fun X Y Z rX qX tX rY qY tY rZ qZ tZ hX hY hZ =>
    det3_frame o (A - o) (B - o) u X Y Z rX qX tX rY qY tY rZ qZ tZ hX hY hZ
  -- membership
  have mo : o ∈ V := by simp [V]
  have mv : v ∈ V := by simp [V]
  have mA' : A ∈ V := by simp [V]
  have mB' : B ∈ V := by simp [V]
  have mP : P ∈ V := by simp [V]
  have hmem : ∀ z ∈ V, z = o ∨ z = v ∨ z = A ∨ z = mA ∨ z = B ∨ z = mB ∨ z = P := by
    intro z hz; simpa [V] using hz
  set M : Finset ℝ³ := {mA, mB}
  have nM : ∀ z, z ≠ mA → z ≠ mB → z ∉ M := by
    intro z h1 h2; simp only [M, mem_insert, mem_singleton, not_or]; exact ⟨h1, h2⟩
  -- the middles, for either closing
  have hEMv : ∀ m ∈ M, EdgeMiddle u v o A B 1 m := by
    intro m hm
    rcases mem_insert.mp hm with rfl | hm
    · exact ⟨v, s, t + s - 1, Or.inl rfl, hs0, hs1, hts, Or.inl (by rw [hmA]; module)⟩
    · rw [mem_singleton.mp hm]
      exact ⟨v, 1 - s', t' + s' - 1, Or.inl rfl, by linarith, by linarith, hts',
        Or.inr (by rw [hmB]; module)⟩
  have hEMo : ∀ m ∈ M, EdgeMiddle u o v A B (-1) m := by
    intro m hm
    rcases mem_insert.mp hm with rfl | hm
    · exact ⟨o, s, t, Or.inl rfl, hs0, hs1, ht, Or.inl hmA⟩
    · rw [mem_singleton.mp hm]
      exact ⟨o, 1 - s', t', Or.inl rfl, by linarith, by linarith, ht',
        Or.inr (by rw [hmB]; module)⟩
  have zne : ∀ X Y, (X = o ∨ X = v ∨ X = A ∨ X = B ∨ X = P) → (Y = A ∨ Y = B ∨ Y = P) →
      X ≠ Y → ⟪X, u⟫ ≠ ⟪Y, u⟫ := hinj
  have hEu : 0 < E := hE
  rcases lt_or_gt_of_ne hrq with hlt | hgt
  · -- `P` hidden: the triangle `v, A, B`
    refine isRupert_tri_view V M (x := o) (y := v) (A := A) (B := B) hov mo mv mA' mB'
      (nM v hvmA hvmB) (nM A hAmA hAmB) (nM B (Ne.symm hmAB) hBmB) ?_ ?_ ?_ ?_
      ⟨zne v A (by simp) (by simp) hvA, zne v B (by simp) (by simp) hvB,
        zne A B (by simp) (by simp) hAB⟩ hEMv hnd.1
    · rw [D v A B 0 0 1 1 0 0 0 1 0 cv cA cB]; nlinarith
    · rw [D A B v 1 0 0 0 1 0 0 0 1 cA cB cv]; nlinarith
    · rw [D B v A 0 1 0 0 0 1 1 0 0 cB cv cA]; nlinarith
    · intro z hz hzM hzo hzv hzA hzB
      rcases hmem z hz with h | h | h | h | h | h | h
      · exact absurd h hzo
      · exact absurd h hzv
      · exact absurd h hzA
      · exact absurd (by simp [M, h]) hzM
      · exact absurd h hzB
      · exact absurd (by simp [M, h]) hzM
      · rw [h]
        refine ⟨?_, ?_, ?_⟩
        · rw [D v A P 0 0 1 1 0 0 r q τ cv cA cP]; nlinarith
        · rw [D A B P 1 0 0 0 1 0 r q τ cA cB cP]; nlinarith
        · rw [D B v P 0 1 0 0 0 1 r q τ cB cv cP]; nlinarith
  · -- `P` a corner: the rims `v, A, P, B` and `o, A, P, B`
    have hrest : ∀ w y, (w = o ∧ y = v ∨ w = v ∧ y = o) →
        ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y → z ≠ A → z ≠ P → z ≠ B → False := by
      intro w y hwy z hz hzM hzw hzy hzA hzP hzB
      rcases hmem z hz with h | h | h | h | h | h | h
      · rcases hwy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [hzw h, hzy h]
      · rcases hwy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [hzy h, hzw h]
      · exact hzA h
      · exact hzM (by simp [M, h])
      · exact hzB h
      · exact hzM (by simp [M, h])
      · exact hzP h
    have hqi : ∀ y, (y = o ∨ y = v) → Function.Injective (quad ⟪y, u⟫ ⟪A, u⟫ ⟪P, u⟫ ⟪B, u⟫) := by
      intro y hy
      have hy' : y = o ∨ y = v ∨ y = A ∨ y = B ∨ y = P := by
        rcases hy with h | h
        exacts [Or.inl h, Or.inr (Or.inl h)]
      have yA : y ≠ A := by rcases hy with rfl | rfl <;> assumption
      have yB : y ≠ B := by rcases hy with rfl | rfl <;> assumption
      have yP : y ≠ P := by rcases hy with rfl | rfl <;> assumption
      exact quad_injective (zne y A hy' (by simp) yA) (zne y P hy' (by simp) yP)
        (zne y B hy' (by simp) yB) (zne A P (by simp) (by simp) hAP)
        (zne A B (by simp) (by simp) hAB) (zne P B (by simp) (by simp) (Ne.symm hBP))
    have tests : ∀ y : ℝ³, ∀ ty : ℝ, y = o + (0 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + ty • u →
        0 < det3 (A - y) (P - y) u ∧ 0 < det3 (A - y) (B - y) u ∧
        0 < det3 (P - A) (B - A) u ∧ 0 < det3 (P - A) (y - A) u ∧
        0 < det3 (B - P) (y - P) u ∧ 0 < det3 (B - P) (A - P) u ∧
        0 < det3 (y - B) (A - B) u ∧ 0 < det3 (y - B) (P - B) u := by
      intro y ty cy
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [D y A P 0 0 ty 1 0 0 r q τ cy cA cP]; nlinarith
      · rw [D y A B 0 0 ty 1 0 0 0 1 0 cy cA cB]; nlinarith
      · rw [D A P B 1 0 0 r q τ 0 1 0 cA cP cB]; nlinarith
      · rw [D A P y 1 0 0 r q τ 0 0 ty cA cP cy]; nlinarith
      · rw [D P B y r q τ 0 1 0 0 0 ty cP cB cy]; nlinarith
      · rw [D P B A r q τ 0 1 0 1 0 0 cP cB cA]; nlinarith
      · rw [D B y A 0 1 0 0 0 ty 1 0 0 cB cy cA]; nlinarith
      · rw [D B y P 0 1 0 0 0 ty r q τ cB cy cP]; nlinarith
    by_cases hN : NWS4 (quad ⟪v, u⟫ ⟪A, u⟫ ⟪P, u⟫ ⟪B, u⟫)
    · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := tests v 1 cv
      exact isRupert_quad_rim V M u hu 1 one_ne_zero (by rw [one_smul]; simp [u]) mo mv mP
        mA' mB' (nM v hvmA hvmB) (nM A hAmA hAmB) (nM P (Ne.symm hmAP) (Ne.symm hmBP))
        (nM B (Ne.symm hmAB) hBmB) t1 t2 t3 t4 t5 t6 t7 t8
        (hrest o v (Or.inl ⟨rfl, rfl⟩)) (hqi v (Or.inr rfl)) hN hEMv hnd.1
    · have hN' := lemmaU_nws4 ⟨zne o A (by simp) (by simp) hoA, zne o B (by simp) (by simp) hoB,
        zne A P (by simp) (by simp) hAP, zne B P (by simp) (by simp) hBP⟩ (hb hgt) (hbad hgt) hN
      obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := tests o 0 co
      exact isRupert_quad_rim V M u hu (-1) (by norm_num)
        (by simp only [neg_smul, one_smul, sub_neg_eq_add, u]; abel) mv mo mP
        mA' mB' (nM o homA homB) (nM A hAmA hAmB) (nM P (Ne.symm hmAP) (Ne.symm hmBP))
        (nM B (Ne.symm hmAB) hBmB) t1 t2 t3 t4 t5 t6 t7 t8
        (hrest v o (Or.inr ⟨rfl, rfl⟩)) (hqi o (Or.inl rfl)) hN' hEMo hnd.2

/-- **Lemma 11.U in screen coordinates**, either orientation of `o, A, B`. -/
theorem lemmaU_coords
    (hnodup : [o, v, A, mA, B, mB, P].Nodup)
    (hmA : mA = o + s • (A - o) + t • (v - o)) (hs0 : 0 < s) (hs1 : s < 1) (ht : t ≠ 0)
    (hts : t + s - 1 ≠ 0)
    (hmB : mB = o + s' • (B - o) + t' • (v - o)) (hs0' : 0 < s') (hs1' : s' < 1)
    (ht' : t' ≠ 0) (hts' : t' + s' - 1 ≠ 0)
    (hP : P = o + r • (A - o) + q • (B - o) + τ • (v - o)) (hr : 0 < r) (hq : 0 < q)
    (hrq : r + q ≠ 1) (hE : det3 (A - o) (B - o) (v - o) ≠ 0)
    (hinj : ∀ X Y, (X = o ∨ X = v ∨ X = A ∨ X = B ∨ X = P) → (Y = A ∨ Y = B ∨ Y = P) →
      X ≠ Y → ⟪X, v - o⟫ ≠ ⟪Y, v - o⟫)
    (hb : 1 < r + q → ¬ max ⟪v, v - o⟫ ⟪P, v - o⟫ ≤ min ⟪A, v - o⟫ ⟪B, v - o⟫)
    (hbad : 1 < r + q → ¬ max ⟪A, v - o⟫ ⟪B, v - o⟫ < min ⟪o, v - o⟫ ⟪P, v - o⟫)
    (hnd : NoHDNAt (({o, v, A, mA, B, mB, P} : Finset ℝ³).erase o) (v - o) ∧
      NoHDNAt (({o, v, A, mA, B, mB, P} : Finset ℝ³).erase v) (v - o)) :
    IsRupert ({o, v, A, mA, B, mB, P} : Finset ℝ³) := by
  rcases lt_or_gt_of_ne hE with hneg | hpos
  · have e : ({o, v, B, mB, A, mA, P} : Finset ℝ³) = {o, v, A, mA, B, mB, P} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> intro h <;> rcases h with h | h | h | h | h | h | h <;>
        simp only [h, true_or, or_true]
    have hnodup' : [o, v, B, mB, A, mA, P].Nodup := by
      have h := hnodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true] at h ⊢
      obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩,
        ⟨h16, h17, h18⟩, ⟨h19, h20⟩, h21, -⟩ := h
      exact ⟨⟨h1, h4, h5, h2, h3, h6⟩, ⟨h9, h10, h7, h8, h11⟩,
        ⟨h19, Ne.symm h13, Ne.symm h16, h20⟩, ⟨Ne.symm h14, Ne.symm h17, h21⟩, ⟨h12, h15⟩,
        h18, not_false⟩
    have hinj' : ∀ X Y, (X = o ∨ X = v ∨ X = B ∨ X = A ∨ X = P) → (Y = B ∨ Y = A ∨ Y = P) →
        X ≠ Y → ⟪X, v - o⟫ ≠ ⟪Y, v - o⟫ := by
      intro X Y hX hY hXY
      refine hinj X Y ?_ ?_ hXY
      · rcases hX with h | h | h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inl h))),
          Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inr h)))]
      · rcases hY with h | h | h
        exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
    have := lemmaU_coords_pos (A := B) (mA := mB) (B := A) (mB := mA) (r := q) (q := r)
      hnodup' hmB hs0' hs1' ht' hts' hmA hs0 hs1 ht hts (by rw [hP]; abel) hq hr
      (by rwa [add_comm]) (by rw [det3_swap12]; linarith)
      hinj'
      (fun h => by rw [min_comm]; exact hb (by linarith))
      (fun h => by rw [max_comm]; exact hbad (by linarith)) (by rw [e]; exact hnd)
    rwa [e] at this
  · exact lemmaU_coords_pos hnodup hmA hs0 hs1 ht hts hmB hs0' hs1' ht' hts' hP hr hq hrq hpos
      hinj hb hbad hnd

end Core

/-! ### Lemma 11.U from facet functions -/

/-- **Lemma 11.U, facet form for abstract points.**  `g_A` is the face `o v A mA`
(negative at `B`, `P`), `g_B` the face `o v B mB` (negative at `A`, `P`), `g_H` a face
through `v` and `P` (the face `245`), negative at `o` and weakly at both far ends,
strictly at one.  `P` is not on the plane through `A`, `B` parallel to `v − o`.
With distinct depths, if `P` is a corner (`P`, `o` on opposite sides of the image of
the line `A B`) only when `35` is not bad, the seven points are Rupert. -/
theorem lemmaU_facets {o v A mA B mB P : ℝ³} {gA gB gH : ℝ³ → ℝ} {NA NB NH : ℝ³}
    (hA : ∀ y z, gA y - gA z = ⟪NA, y - z⟫) (hB : ∀ y z, gB y - gB z = ⟪NB, y - z⟫)
    (hH : ∀ y z, gH y - gH z = ⟪NH, y - z⟫)
    (gAo : gA o = 0) (gAv : gA v = 0) (gAA : gA A = 0) (gAB : gA B < 0) (gAP : gA P < 0)
    (gBo : gB o = 0) (gBv : gB v = 0) (gBB : gB B = 0) (gBA : gB A < 0) (gBP : gB P < 0)
    (gHv : gH v = 0) (gHP : gH P = 0) (gHo : gH o < 0) (gHA : gH A ≤ 0) (gHB : gH B ≤ 0)
    (gHAB : gH A < 0 ∨ gH B < 0)
    (hnodup : [o, v, A, mA, B, mB, P].Nodup)
    (hmA : ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧ mA = o + s • (A - o) + t • (v - o))
    (hmB : ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧ mB = o + s • (B - o) + t • (v - o))
    (hline : det3 (B - A) (P - A) (v - o) ≠ 0)
    (hinj : ∀ X Y, (X = o ∨ X = v ∨ X = A ∨ X = B ∨ X = P) → (Y = A ∨ Y = B ∨ Y = P) →
      X ≠ Y → ⟪X, v - o⟫ ≠ ⟪Y, v - o⟫)
    (hbad : det3 (B - A) (P - A) (v - o) * det3 (B - A) (o - A) (v - o) < 0 →
      ¬ max ⟪A, v - o⟫ ⟪B, v - o⟫ < min ⟪o, v - o⟫ ⟪P, v - o⟫)
    (hnd : NoHDNAt (({o, v, A, mA, B, mB, P} : Finset ℝ³).erase o) (v - o) ∧
      NoHDNAt (({o, v, A, mA, B, mB, P} : Finset ℝ³).erase v) (v - o)) :
    IsRupert ({o, v, A, mA, B, mB, P} : Finset ℝ³) := by
  have hov : o ≠ v := by
    have := hnodup; simp only [List.nodup_cons, List.mem_cons] at this; tauto
  obtain ⟨s, t, hs0, hs1, ht, hts, hmA⟩ := hmA
  obtain ⟨s', t', hs0', hs1', ht', hts', hmB⟩ := hmB
  obtain ⟨τ, hP⟩ := frame_coords hA hB gAo gAv gAA gAB.ne gBo gBv gBB gBA.ne hov P
  have hE := frame16_det_ne hA hB gAo gAv gAA gAB.ne gBo gBv gBB gBA.ne hov
  set r := gB P / gB A
  set q := gA P / gA B
  have hr : 0 < r := div_pos_of_neg_of_neg gBP gBA
  have hq : 0 < q := div_pos_of_neg_of_neg gAP gAB
  set u := v - o
  have co : o = o + (0 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + (0 : ℝ) • u := by simp
  have cA : A = o + (1 : ℝ) • (A - o) + (0 : ℝ) • (B - o) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have cB : B = o + (0 : ℝ) • (A - o) + (1 : ℝ) • (B - o) + (0 : ℝ) • u := by
    simp only [zero_smul, add_zero, one_smul]; abel
  have d1 := det3_frame o (A - o) (B - o) u A B P 1 0 0 0 1 0 r q τ cA cB hP
  have d2 := det3_frame o (A - o) (B - o) u A B o 1 0 0 0 1 0 0 0 0 cA cB co
  have hrq : r + q ≠ 1 := by
    intro h; apply hline; rw [d1]
    rw [show (0 - 1) * (q - 0) - (1 - 0) * (r - 1) = 1 - (r + q) by ring, h, sub_self, zero_mul]
  -- (b)
  have hzv : ⟪o, u⟫ < ⟪v, u⟫ := by
    have : 0 < ⟪v, u⟫ - ⟪o, u⟫ := by
      rw [← inner_sub_left]; exact real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hov))
    linarith
  have hzP : ⟪P, u⟫ = ⟪o, u⟫ + r * (⟪A, u⟫ - ⟪o, u⟫) + q * (⟪B, u⟫ - ⟪o, u⟫) +
      τ * (⟪v, u⟫ - ⟪o, u⟫) := by
    conv_lhs => rw [hP]
    exact affine_frame3 (inner_affine u) o A B v r q τ
  have hHP : 0 = gH o + r * (gH A - gH o) + q * (gH B - gH o) + τ * (0 - gH o) := by
    have := affine_frame3 hH o A B v r q τ
    rw [← hP, gHP, gHv] at this; exact this
  refine lemmaU_coords hnodup hmA hs0 hs1 ht hts hmB hs0' hs1' ht' hts' hP hr hq hrq hE hinj
    (fun h => lemmaU_b_real hzv hzP hHP gHo gHA gHB gHAB hr hq h) (fun h => hbad ?_) hnd
  rw [d1, d2]
  have hE2 := mul_self_pos.mpr hE
  nlinarith

/-! ### Type 16 -/

/-- A facet of the seven points `x i` with index set `S`: an affine function (with its
linear part) vanishing on `S` and negative off it. -/
structure Face16 (x : Fin 7 → ℝ³) (S : Finset (Fin 7)) where
  f : ℝ³ → ℝ
  N : ℝ³
  hN : ∀ y z, f y - f z = ⟪N, y - z⟫
  zero : ∀ i ∈ S, f (x i) = 0
  neg : ∀ i ∉ S, f (x i) < 0

/-- A facet from an affine map. -/
noncomputable def Face16.ofAffine {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (f : ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ i, (i ∈ S → f (x i) = 0) ∧ (i ∉ S → f (x i) < 0)) : Face16 x S :=
  ⟨f, Classical.choose (exists_normal_of_affine f), Classical.choose_spec (exists_normal_of_affine f),
    fun i hi => (h i).1 hi, fun i hi => (h i).2 hi⟩

/-- Relabel a facet by `σ`. -/
def Face16.comp {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (σ : Fin 7 → Fin 7)
    (S' : Finset (Fin 7)) (hS : ∀ i, i ∈ S' ↔ σ i ∈ S) : Face16 (x ∘ σ) S' :=
  ⟨F.f, F.N, F.hN, fun i hi => F.zero (σ i) ((hS i).mp hi),
    fun i hi => F.neg (σ i) (fun h => hi ((hS i).mpr h))⟩

/-- **Type 16** (`typeb_lib.load('16-8f')`): seven distinct points with the facets
`0235`, `1356` (quadrilaterals, cyclic `2, 0, 3, 5` and `3, 6, 1, 5`) and `024`,
`036`, `046`, `145`, `146`, `245`. -/
structure Type16 (x : Fin 7 → ℝ³) where
  inj : Function.Injective x
  q0235 : Face16 x {0, 2, 3, 5}
  q1356 : Face16 x {1, 3, 5, 6}
  t024 : Face16 x {0, 2, 4}
  t036 : Face16 x {0, 3, 6}
  t046 : Face16 x {0, 4, 6}
  t145 : Face16 x {1, 4, 5}
  t146 : Face16 x {1, 4, 6}
  t245 : Face16 x {2, 4, 5}

/-- The automorphism `σ = (0 6)(1 2)` of type 16. -/
def sigma16 : Fin 7 → Fin 7 := ![6, 2, 1, 3, 4, 5, 0]

/-- The relabelled type-16 point set `x ∘ σ`. -/
def Type16.sigma {x : Fin 7 → ℝ³} (T : Type16 x) : Type16 (x ∘ sigma16) :=
  ⟨T.inj.comp (by intro i j h; revert i j; decide),
    T.q1356.comp sigma16 _ (by decide), T.q0235.comp sigma16 _ (by decide),
    T.t146.comp sigma16 _ (by decide), T.t036.comp sigma16 _ (by decide),
    T.t046.comp sigma16 _ (by decide), T.t245.comp sigma16 _ (by decide),
    T.t024.comp sigma16 _ (by decide), T.t145.comp sigma16 _ (by decide)⟩

/-- `m` is a *middle* over the chord from `o` to `A` at the view along `o v`: it
projects strictly between the images of `o` and `A` (and `A` is the far end). -/
def MidOf (o v A m : ℝ³) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ m = o + s • (A - o) + t • (v - o)

/-- A middle is strictly nearer to the axle than its far end, for any affine function
vanishing on the axle and negative at the far end. -/
theorem MidOf.lt {o v A m : ℝ³} (h : MidOf o v A m) {g : ℝ³ → ℝ} {N : ℝ³}
    (hg : ∀ y z, g y - g z = ⟪N, y - z⟫) (ho : g o = 0) (hv : g v = 0) (hA : g A < 0) :
    g A < g m := by
  obtain ⟨s, t, hs0, hs1, rfl⟩ := h
  rw [affine_frame hg, ho, hv]
  nlinarith

/-- **"35 is bad"** (Lemma 11.U (c)): at the view along `ℓ = 35` (depth
`z = ⟪·, x 5 − x 3⟫`), with the far ends `A` of `0235` and `B` of `1356` (the other
vertex of each is a middle, `MidOf`), the vertex `4` is a corner (its image and that of
`3` on opposite sides of the line of the images of `A`, `B`) and
`min (z 3, z 4) > max (z A, z B)`. -/
def Type16Bad35 (x : Fin 7 → ℝ³) : Prop :=
  ∃ A m B m' : ℝ³, ((A = x 0 ∧ m = x 2) ∨ (A = x 2 ∧ m = x 0)) ∧
    ((B = x 1 ∧ m' = x 6) ∨ (B = x 6 ∧ m' = x 1)) ∧
    MidOf (x 3) (x 5) A m ∧ MidOf (x 3) (x 5) B m' ∧
    det3 (B - A) (x 4 - A) (x 5 - x 3) * det3 (B - A) (x 3 - A) (x 5 - x 3) < 0 ∧
    max ⟪A, x 5 - x 3⟫ ⟪B, x 5 - x 3⟫ < min ⟪x 3, x 5 - x 3⟫ ⟪x 4, x 5 - x 3⟫

/-- **A convex plane quadrilateral `o, p, w, q`** (cyclic) in coordinates: `f₀` its
plane (nonzero at some `Z`), `f₁` vanishing on the side line `o q`, `f₂` on the side
line `o p`, `f₃` on the side line `w q`, each negative at the other two vertices.  Then
`w = o + α (p − o) + β (q − o)` with `α = f₁ w / f₁ p > 0`, `β = f₂ w / f₂ q > 0`,
`α + β > 1`. -/
theorem plane_quad_coords {f₀ f₁ f₂ f₃ : ℝ³ → ℝ} {N₀ N₁ N₂ N₃ : ℝ³}
    (h₀ : ∀ y z, f₀ y - f₀ z = ⟪N₀, y - z⟫) (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫)
    (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫) (h₃ : ∀ y z, f₃ y - f₃ z = ⟪N₃, y - z⟫)
    {o p q w Z : ℝ³} (h₀o : f₀ o = 0) (h₀p : f₀ p = 0) (h₀q : f₀ q = 0) (h₀w : f₀ w = 0)
    (h₀Z : f₀ Z ≠ 0) (h₁o : f₁ o = 0) (h₁q : f₁ q = 0) (h₁p : f₁ p < 0) (h₁w : f₁ w < 0)
    (h₂o : f₂ o = 0) (h₂p : f₂ p = 0) (h₂q : f₂ q < 0) (h₂w : f₂ w < 0)
    (h₃w : f₃ w = 0) (h₃q : f₃ q = 0) (h₃o : f₃ o < 0) (h₃p : f₃ p < 0) :
    0 < f₁ w / f₁ p ∧ 0 < f₂ w / f₂ q ∧ 1 < f₁ w / f₁ p + f₂ w / f₂ q ∧
      w = o + (f₁ w / f₁ p) • (p - o) + (f₂ w / f₂ q) • (q - o) := by
  have hco := coords_of_affine3 h₀ h₁ h₂ h₀o h₀p h₀q h₀w h₀Z h₁o h₁q h₁p.ne h₂o h₂p h₂q.ne
  set α := f₁ w / f₁ p
  set β := f₂ w / f₂ q
  have hα : 0 < α := div_pos_of_neg_of_neg h₁w h₁p
  refine ⟨hα, div_pos_of_neg_of_neg h₂w h₂q, ?_, hco⟩
  have hf := affine_frame h₃ o p q α β
  rw [← hco, h₃w, h₃q] at hf
  nlinarith [mul_pos hα (neg_pos.mpr h₃p)]

/-- The middle of a convex quadrilateral `o, p, w, q` at the view along `o q`: if
`α < 1` the far end is `p` and `w` the middle, if `α > 1` the far end is `w`; in both
cases the middle is on neither line from the axle ends to the far end. -/
theorem quad_middle {o p q w : ℝ³} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β)
    (hw : w = o + α • (p - o) + β • (q - o)) :
    (α < 1 → ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
      w = o + s • (p - o) + t • (q - o)) ∧
    (1 < α → ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
      p = o + s • (w - o) + t • (q - o)) := by
  refine ⟨fun h => ⟨α, β, hα, h, hβ.ne', by linarith, hw⟩, fun h => ?_⟩
  refine ⟨1 / α, -β / α, by positivity, (div_lt_one hα).mpr h,
    div_ne_zero (neg_ne_zero.mpr hβ.ne') hα.ne', ?_, ?_⟩
  · rw [show -β / α + 1 / α - 1 = (1 - β - α) / α by field_simp; ring]
    exact div_ne_zero (by linarith) hα.ne'
  · rw [hw]
    have : α ≠ 0 := hα.ne'
    rw [show o + (1 / α) • (o + α • (p - o) + β • (q - o) - o) + (-β / α) • (q - o) =
      o + ((1 / α) * α) • (p - o) by module]
    rw [one_div_mul_cancel this, one_smul]; abel

/-- The quadrilateral `0235` (cyclic `2, 0, 3, 5`) in the frame `3; 0, 5`. -/
theorem Type16.coords0235 {x : Fin 7 → ℝ³} (T : Type16 x) :
    0 < T.q1356.f (x 2) / T.q1356.f (x 0) ∧ 0 < T.t036.f (x 2) / T.t036.f (x 5) ∧
    1 < T.q1356.f (x 2) / T.q1356.f (x 0) + T.t036.f (x 2) / T.t036.f (x 5) ∧
    x 2 = x 3 + (T.q1356.f (x 2) / T.q1356.f (x 0)) • (x 0 - x 3) +
      (T.t036.f (x 2) / T.t036.f (x 5)) • (x 5 - x 3) :=
  plane_quad_coords T.q0235.hN T.q1356.hN T.t036.hN T.t245.hN
    (T.q0235.zero 3 (by decide)) (T.q0235.zero 0 (by decide)) (T.q0235.zero 5 (by decide))
    (T.q0235.zero 2 (by decide)) (T.q0235.neg 1 (by decide)).ne
    (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide)) (T.q1356.neg 0 (by decide))
    (T.q1356.neg 2 (by decide))
    (T.t036.zero 3 (by decide)) (T.t036.zero 0 (by decide)) (T.t036.neg 5 (by decide))
    (T.t036.neg 2 (by decide))
    (T.t245.zero 2 (by decide)) (T.t245.zero 5 (by decide)) (T.t245.neg 3 (by decide))
    (T.t245.neg 0 (by decide))

/-- The quadrilateral `1356` (cyclic `3, 6, 1, 5`) in the frame `3; 6, 5`. -/
theorem Type16.coords1356 {x : Fin 7 → ℝ³} (T : Type16 x) :
    0 < T.q0235.f (x 1) / T.q0235.f (x 6) ∧ 0 < T.t036.f (x 1) / T.t036.f (x 5) ∧
    1 < T.q0235.f (x 1) / T.q0235.f (x 6) + T.t036.f (x 1) / T.t036.f (x 5) ∧
    x 1 = x 3 + (T.q0235.f (x 1) / T.q0235.f (x 6)) • (x 6 - x 3) +
      (T.t036.f (x 1) / T.t036.f (x 5)) • (x 5 - x 3) :=
  plane_quad_coords T.q1356.hN T.q0235.hN T.t036.hN T.t145.hN
    (T.q1356.zero 3 (by decide)) (T.q1356.zero 6 (by decide)) (T.q1356.zero 5 (by decide))
    (T.q1356.zero 1 (by decide)) (T.q1356.neg 0 (by decide)).ne
    (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide)) (T.q0235.neg 6 (by decide))
    (T.q0235.neg 1 (by decide))
    (T.t036.zero 3 (by decide)) (T.t036.zero 6 (by decide)) (T.t036.neg 5 (by decide))
    (T.t036.neg 1 (by decide))
    (T.t145.zero 1 (by decide)) (T.t145.zero 5 (by decide)) (T.t145.neg 3 (by decide))
    (T.t145.neg 6 (by decide))

/-- The far end of `0235` at the view along `35` is `0` or `2` (no tie in general
position), with the other vertex a middle. -/
theorem Type16.far0235 {x : Fin 7 → ℝ³} (T : Type16 x) (hgen : GenPos (univ.image x)) :
    (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
        x 2 = x 3 + s • (x 0 - x 3) + t • (x 5 - x 3)) ∨
    (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
        x 0 = x 3 + s • (x 2 - x 3) + t • (x 5 - x 3)) := by
  obtain ⟨hα, hβ, hαβ, h2⟩ := T.coords0235
  obtain ⟨m1, m2⟩ := quad_middle hα hβ hαβ h2
  have memV : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  rcases lt_trichotomy (T.q1356.f (x 2) / T.q1356.f (x 0)) 1 with h | h | h
  · exact Or.inl (m1 h)
  · exfalso
    rw [h, one_smul] at h2
    exact hgen.ne_smul (memV 0) (memV 2) (memV 3) (memV 5) (T.inj.ne (by decide))
      (T.inj.ne (by decide)) ⟨T.inj.ne (by decide), T.inj.ne (by decide)⟩ _ (by rw [h2]; abel)
  · exact Or.inr (m2 h)

/-- The far end of `1356` at the view along `35` is `6` or `1`. -/
theorem Type16.far1356 {x : Fin 7 → ℝ³} (T : Type16 x) (hgen : GenPos (univ.image x)) :
    (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
        x 1 = x 3 + s • (x 6 - x 3) + t • (x 5 - x 3)) ∨
    (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
        x 6 = x 3 + s • (x 1 - x 3) + t • (x 5 - x 3)) := by
  obtain ⟨hα, hβ, hαβ, h1⟩ := T.coords1356
  obtain ⟨m1, m2⟩ := quad_middle hα hβ hαβ h1
  have memV : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  rcases lt_trichotomy (T.q0235.f (x 1) / T.q0235.f (x 6)) 1 with h | h | h
  · exact Or.inl (m1 h)
  · exfalso
    rw [h, one_smul] at h1
    exact hgen.ne_smul (memV 6) (memV 1) (memV 3) (memV 5) (T.inj.ne (by decide))
      (T.inj.ne (by decide)) ⟨T.inj.ne (by decide), T.inj.ne (by decide)⟩ _ (by rw [h1]; abel)
  · exact Or.inr (m2 h)

set_option maxHeartbeats 1000000 in
/-- **Lemma 11.U (type 16, the test at `35`).**  A type-16 point set in general
position (`GenPos`, `NoPlaneParallel`), without horizontal double normals at the views
along its segments, for which "35 is bad" fails (`Type16Bad35`), is Rupert: the
closing at `35` by `5` or by `3` is unimodal (Theorem 8.9 with Theorem 7.3). -/
theorem isRupert_type16_35 {x : Fin 7 → ℝ³} (T : Type16 x) (hgen : GenPos (univ.image x))
    (hpar : NoPlaneParallel (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v))
    (hbad : ¬ Type16Bad35 x) : IsRupert (univ.image x) := by
  classical
  set V := univ.image x with hV
  have memV : ∀ i, x i ∈ V := fun i => mem_image_of_mem x (mem_univ i)
  have key : ∀ A mA B mB : ℝ³, (A = x 0 ∧ mA = x 2 ∨ A = x 2 ∧ mA = x 0) →
      (B = x 1 ∧ mB = x 6 ∨ B = x 6 ∧ mB = x 1) →
      (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
        mA = x 3 + s • (A - x 3) + t • (x 5 - x 3)) →
      (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
        mB = x 3 + s • (B - x 3) + t • (x 5 - x 3)) → IsRupert V := by
    intro A mA B mB hA hB hmA hmB
    have hVeq : V = {x 3, x 5, A, mA, B, mB, x 4} := by
      rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · ext z
        simp only [V, mem_image, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
        · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
    have hnodup : [x 3, x 5, A, mA, B, mB, x 4].Nodup := by
      rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [List.Nodup.map (l := [3, 5, 0, 2, 1, 6, 4]) T.inj (by decide),
        List.Nodup.map (l := [3, 5, 0, 2, 6, 1, 4]) T.inj (by decide),
        List.Nodup.map (l := [3, 5, 2, 0, 1, 6, 4]) T.inj (by decide),
        List.Nodup.map (l := [3, 5, 2, 0, 6, 1, 4]) T.inj (by decide)]
    have hAi : ∃ i, A = x i ∧ (i = 0 ∨ i = 2) := by
      rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [⟨0, rfl, Or.inl rfl⟩, ⟨2, rfl, Or.inr rfl⟩]
    have hBi : ∃ i, B = x i ∧ (i = 1 ∨ i = 6) := by
      rcases hB with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [⟨1, rfl, Or.inl rfl⟩, ⟨6, rfl, Or.inr rfl⟩]
    obtain ⟨a, rfl, ha⟩ := hAi
    obtain ⟨b, rfl, hb⟩ := hBi
    have hinj : ∀ X Y, (X = x 3 ∨ X = x 5 ∨ X = x a ∨ X = x b ∨ X = x 4) →
        (Y = x a ∨ Y = x b ∨ Y = x 4) → X ≠ Y → ⟪X, x 5 - x 3⟫ ≠ ⟪Y, x 5 - x 3⟫ := by
      intro X Y hX hY hXY
      have hXV : X ∈ V := by rcases hX with rfl | rfl | rfl | rfl | rfl <;> exact memV _
      have hYV : Y ∈ V := by rcases hY with rfl | rfl | rfl <;> exact memV _
      refine hgen.inner_ne_of_ne hXV hYV (memV 3) (memV 5) hXY (T.inj.ne (by decide)) (Or.inl ?_)
      rcases hY with rfl | rfl | rfl <;>
        [rcases ha with rfl | rfl; rcases hb with rfl | rfl; skip] <;>
        exact ⟨T.inj.ne (by decide), T.inj.ne (by decide)⟩
    have hline : det3 (x b - x a) (x 4 - x a) (x 5 - x 3) ≠ 0 := by
      refine hpar _ (memV a) _ (memV b) _ (memV 4) _ (memV 3) _ (memV 5) ?_
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      exacts [List.Nodup.map (l := [0, 1, 4, 3, 5]) T.inj (by decide),
        List.Nodup.map (l := [0, 6, 4, 3, 5]) T.inj (by decide),
        List.Nodup.map (l := [2, 1, 4, 3, 5]) T.inj (by decide),
        List.Nodup.map (l := [2, 6, 4, 3, 5]) T.inj (by decide)]
    have hmid : ∀ (P m : ℝ³), (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ t ≠ 0 ∧ t + s - 1 ≠ 0 ∧
        m = x 3 + s • (P - x 3) + t • (x 5 - x 3)) → MidOf (x 3) (x 5) P m := by
      rintro P m ⟨s, t, h1, h2, -, -, h⟩; exact ⟨s, t, h1, h2, h⟩
    rw [hVeq]
    refine lemmaU_facets T.q0235.hN T.q1356.hN T.t245.hN (T.q0235.zero 3 (by decide))
      (T.q0235.zero 5 (by decide)) ?_ ?_ (T.q0235.neg 4 (by decide))
      (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide)) ?_ ?_
      (T.q1356.neg 4 (by decide)) (T.t245.zero 5 (by decide)) (T.t245.zero 4 (by decide))
      (T.t245.neg 3 (by decide)) ?_ ?_ (Or.inr ?_) hnodup hmA hmB hline hinj
      (fun hc hlt => hbad ⟨x a, mA, x b, mB, hA, hB, hmid _ _ hmA, hmid _ _ hmB, hc, hlt⟩) ?_
    · rcases ha with rfl | rfl <;> exact T.q0235.zero _ (by decide)
    · rcases hb with rfl | rfl <;> exact T.q0235.neg _ (by decide)
    · rcases hb with rfl | rfl <;> exact T.q1356.zero _ (by decide)
    · rcases ha with rfl | rfl <;> exact T.q1356.neg _ (by decide)
    · rcases ha with rfl | rfl
      exacts [(T.t245.neg _ (by decide)).le, (T.t245.zero _ (by decide)).le]
    · rcases hb with rfl | rfl <;> exact (T.t245.neg _ (by decide)).le
    · rcases hb with rfl | rfl <;> exact T.t245.neg _ (by decide)
    · rw [← hVeq]
      refine ⟨?_, hnd (x 3) (memV 3) (x 5) (memV 5) (T.inj.ne (by decide))⟩
      have := (hnd (x 5) (memV 5) (x 3) (memV 3) (T.inj.ne (by decide))).neg
      rwa [neg_sub] at this
  rcases T.far0235 hgen with h0 | h0 <;> rcases T.far1356 hgen with h1 | h1
  · exact key _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) h0 h1
  · exact key _ _ _ _ (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) h0 h1
  · exact key _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) h0 h1
  · exact key _ _ _ _ (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) h0 h1

/-- **Corollary 11.Ua.**  If some far end at the view along `35` (of either
quadrilateral) is above `3` (`z A > z 3`), then `35` is not bad. -/
theorem type16_not_bad35_of_far {x : Fin 7 → ℝ³} (T : Type16 x)
    (h : ∃ A m : ℝ³, ((A = x 0 ∧ m = x 2) ∨ (A = x 2 ∧ m = x 0) ∨ (A = x 1 ∧ m = x 6) ∨
      (A = x 6 ∧ m = x 1)) ∧ MidOf (x 3) (x 5) A m ∧ ⟪x 3, x 5 - x 3⟫ < ⟪A, x 5 - x 3⟫) :
    ¬ Type16Bad35 x := by
  obtain ⟨A, m, hlab, hmid, hz⟩ := h
  rintro ⟨A', m', B', mB', hA', hB', hmA', hmB', -, hlt⟩
  simp only [max_lt_iff, lt_min_iff] at hlt
  have L1 := fun {P m : ℝ³} (h : MidOf (x 3) (x 5) P m) (hP : T.q1356.f P < 0) =>
    h.lt T.q1356.hN (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide)) hP
  have L2 := fun {P m : ℝ³} (h : MidOf (x 3) (x 5) P m) (hP : T.q0235.f P < 0) =>
    h.lt T.q0235.hN (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide)) hP
  rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hA' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hB' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | linarith
      | linarith [L1 hmid (T.q1356.neg _ (by decide)), L1 hmA' (T.q1356.neg _ (by decide))]
      | linarith [L2 hmid (T.q0235.neg _ (by decide)), L2 hmB' (T.q0235.neg _ (by decide))]

/-- **Corollary 11.Ua, angle form.**  An acute angle at `3` of the quadrilateral
`0235` (`⟪x 0 − x 3, x 5 − x 3⟫ > 0`) or of `1356` (`⟪x 6 − x 3, x 5 − x 3⟫ > 0`) puts
both of its other vertices above `3`, so `35` is not bad. -/
theorem type16_not_bad35_of_acute {x : Fin 7 → ℝ³} (T : Type16 x)
    (h : 0 < ⟪x 0 - x 3, x 5 - x 3⟫ ∨ 0 < ⟪x 6 - x 3, x 5 - x 3⟫) : ¬ Type16Bad35 x := by
  have hov : x 3 ≠ x 5 := T.inj.ne (by decide)
  have hU : 0 < ⟪x 5 - x 3, x 5 - x 3⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hov))
  rintro ⟨A', m', B', mB', hA', hB', -, -, -, hlt⟩
  simp only [max_lt_iff, lt_min_iff] at hlt
  rcases h with h | h
  · obtain ⟨hα, hβ, -, h2⟩ := T.coords0235
    have e : ⟪x 2 - x 3, x 5 - x 3⟫ = (T.q1356.f (x 2) / T.q1356.f (x 0)) *
        ⟪x 0 - x 3, x 5 - x 3⟫ + (T.t036.f (x 2) / T.t036.f (x 5)) * ⟪x 5 - x 3, x 5 - x 3⟫ := by
      have e2 : x 2 - x 3 = (T.q1356.f (x 2) / T.q1356.f (x 0)) • (x 0 - x 3) + (T.t036.f (x 2) / T.t036.f (x 5)) • (x 5 - x 3) := by
        conv_lhs => rw [h2]
        abel
      rw [e2, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have h2' : 0 < ⟪x 2 - x 3, x 5 - x 3⟫ := by rw [e]; positivity
    rw [inner_sub_left] at h h2'
    rcases hA' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> linarith
  · obtain ⟨hα, hβ, -, h1⟩ := T.coords1356
    have e : ⟪x 1 - x 3, x 5 - x 3⟫ = (T.q0235.f (x 1) / T.q0235.f (x 6)) *
        ⟪x 6 - x 3, x 5 - x 3⟫ + (T.t036.f (x 1) / T.t036.f (x 5)) * ⟪x 5 - x 3, x 5 - x 3⟫ := by
      have e2 : x 1 - x 3 = (T.q0235.f (x 1) / T.q0235.f (x 6)) • (x 6 - x 3) + (T.t036.f (x 1) / T.t036.f (x 5)) • (x 5 - x 3) := by
        conv_lhs => rw [h1]
        abel
      rw [e2, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have h1' : 0 < ⟪x 1 - x 3, x 5 - x 3⟫ := by rw [e]; positivity
    rw [inner_sub_left] at h h1'
    rcases hB' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> linarith

end Minimality

end
