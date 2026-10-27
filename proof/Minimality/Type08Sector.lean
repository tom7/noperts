module

public import Minimality.HFrame
public import Minimality.HEndFinal
public import Minimality.UniformTilt

@[expose] public section

/-!
# The sector tilt at a touching (`FEWER-FACES-PROOFS.md` Proposition 29.3)

At the view `u₀` along the edge `vw` of a named closing the shadow is the quadrilateral
`(p, f₁, r, f₂)` with one vertex over each far corner; at a touching the three far corners tie in
depth.  For a tilt `u₀ + t v` whose screen direction lies in the interior of the tangent cone at
`p`, the apex `v` protrudes, `w` is hidden, the upper middle over the chord from `v` becomes a rim
corner, and the ties of the far corners are broken by `⟪·, v⟫`: if `r` is not the `v`-maximum of
the three far corners the rim is a unimodal five-cycle.  Here is the frame version
(`HFrame.sector_final`), through `isRupert_of_tilted_unimodal'`: all determinant tests are read in
the frame coordinates `(x, y, z)` of `HFrame`, as for the horizontal end.
-/

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

/-- The tilt test in frame coordinates: the tilt `v` has frame components `(px, py, 0)`. -/
def SecTest (σ px py : ℝ) (P Q S : V3) : Prop :=
  0 < σ * crossXY P Q S ∨ (crossXY P Q S = 0 ∧ 0 < σ * tst ⟨px, py, 0⟩ P Q S)

/-- The open condition on the five depths of the cycle `(c, m, f, r, f')` used for the sector:
`f` below `m`, `f'` below `c`, and `r` below `f` or `f'`. -/
def Q5 (z : ZMod 5 → ℝ) : Prop := z 2 < z 1 ∧ z 4 < z 0 ∧ (z 3 < z 2 ∨ z 3 < z 4)

theorem Q5_open : IsOpen {z : ZMod 5 → ℝ | Q5 z} := by
  have h1 : IsOpen {z : ZMod 5 → ℝ | z 2 < z 1} := isOpen_lt (continuous_apply 2) (continuous_apply 1)
  have h2 : IsOpen {z : ZMod 5 → ℝ | z 4 < z 0} := isOpen_lt (continuous_apply 4) (continuous_apply 0)
  have h3 : IsOpen {z : ZMod 5 → ℝ | z 3 < z 2} := isOpen_lt (continuous_apply 3) (continuous_apply 2)
  have h4 : IsOpen {z : ZMod 5 → ℝ | z 3 < z 4} := isOpen_lt (continuous_apply 3) (continuous_apply 4)
  exact h1.inter (h2.inter (h3.union h4))

theorem Q5_smul {z : ZMod 5 → ℝ} {c : ℝ} (hc : 0 < c) (h : Q5 z) : Q5 (fun i => c * z i) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h1 hc
  · exact mul_lt_mul_of_pos_left h2 hc
  · rcases h3 with h | h
    · exact Or.inl (mul_lt_mul_of_pos_left h hc)
    · exact Or.inr (mul_lt_mul_of_pos_left h hc)

theorem Q5_shift {z : ZMod 5 → ℝ} (k : ℝ) (h : Q5 z) : Q5 (fun i => z i + k) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by linarith, by linarith, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem Q5_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5 z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  have hne : z 0 ≠ z 1 := fun e => by
    have := hinj e; revert this; decide
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- z 0 < z 1: the top is `1`
    refine isCyclicUnimodal_of_top (by norm_num) hinj 1 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · right; rw [a0]; exact hlt
    · exact absurd rfl hi
    · left; rw [b2]; exact h1
    · rcases h3 with h | h
      · left; rw [b3]; exact h
      · right; rw [a3]; exact h
    · right; rw [a4]; exact h2
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 0 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [b1]; exact hgt
    · left; rw [b2]; exact h1
    · rcases h3 with h | h
      · left; rw [b3]; exact h
      · right; rw [a3]; exact h
    · right; rw [a4]; exact h2

namespace HFrame
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

/-- The tilt tests in frame coordinates: for a vector `w`, `tst` of the frame components
`(⟪e, w⟫, ⟪-N, w⟫, ⟪u₀, w⟫)` is `D₀ · det3 · · w`. -/
theorem tst_gen (w P Q S : ℝ³) :
    tst ⟨⟪hfE vb g u0, w⟫, ⟪-N, w⟫, ⟪u0, w⟫⟩ (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q)
      (hfΦ vb g u0 fG S) = det3 (hfE vb g u0) (-N) u0 * det3 (Q - P) (S - P) w := by
  have e1 : ∀ R T : ℝ³, (hfΦ vb g u0 fG R).x - (hfΦ vb g u0 fG T).x = ⟪R - T, hfE vb g u0⟫ := by
    intro R T; simp only [hfΦ]; rw [← inner_sub_left]; congr 1; abel
  have e2 : ∀ R T : ℝ³, (hfΦ vb g u0 fG R).y - (hfΦ vb g u0 fG T).y = ⟪-N, R - T⟫ := by
    intro R T; simp only [hfΦ]; rw [inner_neg_left, ← Fr.hN]; ring
  have e3 : ∀ R T : ℝ³, (hfΦ vb g u0 fG R).z - (hfΦ vb g u0 fG T).z = ⟪R - T, u0⟫ := by
    intro R T; simp only [hfΦ]; rw [← inner_sub_left]; congr 1; abel
  rw [← hdet_inner (hfE vb g u0) (-N) u0 (Q - P) (S - P) w]
  simp only [tst, e1, e2, e3]
  simp only [real_inner_comm (Q - P) (hfE vb g u0), real_inner_comm (S - P) (hfE vb g u0),
    real_inner_comm (Q - P) (-N), real_inner_comm (S - P) (-N),
    real_inner_comm (Q - P) u0, real_inner_comm (S - P) u0, real_inner_comm w (hfE vb g u0),
    real_inner_comm w (-N), real_inner_comm w u0]

/-- The depth of a point at the view `u₀` in frame coordinates. -/
theorem inner_u0_coord (P : ℝ³) : ⟪P, u0⟫ = (hfΦ vb g u0 fG P).z + ⟪g, u0⟫ := by
  simp only [hfΦ]; rw [← inner_add_left]; congr 1; abel

/-- The depth of a point along the tilt `α e − β N`, in frame coordinates. -/
theorem inner_w_coord (α β : ℝ) (P : ℝ³) :
    ⟪P, α • hfE vb g u0 + β • (-N)⟫ =
      α * (hfΦ vb g u0 fG P).x + β * (hfΦ vb g u0 fG P).y + ⟪vb, α • hfE vb g u0 + β • (-N)⟫ := by
  have h1 : ⟪P, α • hfE vb g u0 + β • (-N)⟫ = ⟪P - vb, α • hfE vb g u0 + β • (-N)⟫ +
      ⟪vb, α • hfE vb g u0 + β • (-N)⟫ := by
    rw [← inner_add_left]; congr 1; abel
  have h2 : ⟪P - vb, N⟫ = fG P := by rw [real_inner_comm, ← Fr.hN, Fr.hv]; ring
  rw [h1]
  simp only [inner_add_right, real_inner_smul_right, inner_neg_right, h2, hfΦ]

/-- **The sector tilt, final assembly.**  The five-cycle `x` of points of `V` (every other point of
`V` is listed in `hrest`), the frame images pass all tests `SecTest σ px py` (strictly, or at a
collinear triple through the tilt `(px, py)`), and the depths — first `z`, then the tilt value
`px/E · x + py/M · y` — satisfy lexicographically `z₂ < z₁`, `z₄ < z₀` and `z₃ < z₂` or `z₃ < z₄`.
Then `V` is Rupert. -/
theorem sector_final (V : Finset ℝ³) (x : ZMod 5 → ℝ³) (hxV : ∀ i, x i ∈ V) (σ px py : ℝ)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      SecTest σ px py (hfΦ vb g u0 fG (x i)) (hfΦ vb g u0 fG (x (i + 1))) (hfΦ vb g u0 fG (x j)))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      SecTest σ px py (hfΦ vb g u0 fG (x i)) (hfΦ vb g u0 fG (x (i + 1))) (hfΦ vb g u0 fG y))
    (hz1 : (hfΦ vb g u0 fG (x 2)).z < (hfΦ vb g u0 fG (x 1)).z)
    (hz2 : (hfΦ vb g u0 fG (x 4)).z < (hfΦ vb g u0 fG (x 0)).z)
    (hlex : (hfΦ vb g u0 fG (x 3)).z < (hfΦ vb g u0 fG (x 2)).z ∨
      ((hfΦ vb g u0 fG (x 3)).z = (hfΦ vb g u0 fG (x 2)).z ∧
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * (hfΦ vb g u0 fG (x 3)).x + py / ⟪N, N⟫ * (hfΦ vb g u0 fG (x 3)).y <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * (hfΦ vb g u0 fG (x 2)).x + py / ⟪N, N⟫ * (hfΦ vb g u0 fG (x 2)).y) ∨
      (hfΦ vb g u0 fG (x 3)).z < (hfΦ vb g u0 fG (x 4)).z ∨
      ((hfΦ vb g u0 fG (x 3)).z = (hfΦ vb g u0 fG (x 4)).z ∧
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * (hfΦ vb g u0 fG (x 3)).x + py / ⟪N, N⟫ * (hfΦ vb g u0 fG (x 3)).y <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * (hfΦ vb g u0 fG (x 4)).x + py / ⟪N, N⟫ * (hfΦ vb g u0 fG (x 4)).y)) :
    IsRupert V := by
  classical
  set e := hfE vb g u0 with he
  set E : ℝ := ⟪e, e⟫ with hE
  set M : ℝ := ⟪N, N⟫ with hM
  set U : ℝ := ⟪u0, u0⟫ with hU
  set D0 := det3 e (-N) u0 with hD0
  have hEpos : 0 < E := Fr.hee
  have hMpos : 0 < M := Fr.hNN
  have hUpos : 0 < U := Fr.hu
  have hD0ne : D0 ≠ 0 := Fr.D0_ne
  set w : ℝ³ := (px / E) • e + (py / M) • (-N) with hw
  -- the inner products of `w`
  have hwe : ⟪e, w⟫ = px := by
    have h1 : ⟪e, -N⟫ = 0 := by rw [inner_neg_right, real_inner_comm, Fr.inner_N_e]; ring
    rw [hw, inner_add_right, real_inner_smul_right, real_inner_smul_right, h1, ← hE]
    field_simp; ring
  have hwN : ⟪-N, w⟫ = py := by
    have h1 : ⟪-N, e⟫ = 0 := by rw [inner_neg_left, Fr.inner_N_e]; ring
    rw [hw, inner_add_right, real_inner_smul_right, real_inner_smul_right, h1, inner_neg_neg, ← hM]
    field_simp; ring
  have hwu : ⟪u0, w⟫ = 0 := by
    have h1 : ⟪u0, -N⟫ = 0 := by rw [inner_neg_right, real_inner_comm, Fr.hNu]; ring
    rw [hw, inner_add_right, real_inner_smul_right, real_inner_smul_right, h1,
      real_inner_comm, Fr.inner_e_u]; ring
  have hcw : ∀ P Q S : ℝ³, D0 * det3 (Q - P) (S - P) w =
      tst ⟨px, py, 0⟩ (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) := by
    intro P Q S
    have := Fr.tst_gen w P Q S
    rw [hwe, hwN, hwu] at this
    exact this.symm
  have hc0 : ∀ P Q S : ℝ³, D0 * det3 (Q - P) (S - P) u0 =
      U * crossXY (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) :=
    fun P Q S => Fr.det3_u0_coord P Q S
  -- the sign
  set t := σ * D0 with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hconv : ∀ P Q S : ℝ³,
      SecTest σ px py (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) →
      TiltSign (Q - P) (S - P) (ε • u0) (ε • w) := by
    intro P Q S h
    rcases h with h | ⟨h0, h1⟩
    · left
      rw [det3_smul_right]
      refine sgn_pos t _ ?_
      have := hc0 P Q S
      calc 0 < U * (σ * crossXY (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S)) :=
            mul_pos hUpos h
        _ = t * det3 (Q - P) (S - P) u0 := by rw [ht]; linear_combination (-σ) * this
    · right
      have hd0 : det3 (Q - P) (S - P) u0 = 0 := by
        have := hc0 P Q S
        rw [h0, mul_zero] at this
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hD0ne
        · exact h
      refine ⟨by rw [det3_smul_right, hd0, mul_zero], ?_⟩
      rw [det3_smul_right]
      refine sgn_pos t _ ?_
      have := hcw P Q S
      calc 0 < σ * tst ⟨px, py, 0⟩ (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) := h1
        _ = t * det3 (Q - P) (S - P) w := by rw [ht, ← this]; ring
  have hu0 : u0 ≠ 0 := by
    intro h0; have := Fr.hu; rw [h0] at this; simp at this
  have hu' : ε • u0 ≠ 0 := by
    intro h0
    rcases hεs with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hu0 h0
  refine isRupert_of_tilted_unimodal' V (ε • u0) (ε • w) hu' (k := 5) (by norm_num) x hxV
    (fun i j hi hj => hconv _ _ _ (hcyc i j hi hj))
    (fun y hy hyx i => hconv _ _ _ (hrest y hy hyx i))
    (fun z => Q5 (fun i => ε * z i)) ?_ ?_ ?_ ?_
  · have : {z : ZMod 5 → ℝ | Q5 (fun i => ε * z i)} = (fun z : ZMod 5 → ℝ => fun i => ε * z i) ⁻¹' {z | Q5 z} := rfl
    rw [this]
    exact Q5_open.preimage (by fun_prop)
  · intro z c hc hQ
    have := Q5_smul hc hQ
    convert this using 2 with i
    ring
  · -- the depths at the tilted views
    set zz : ZMod 5 → ℝ := fun i => (hfΦ vb g u0 fG (x i)).z with hzz
    set ww : ZMod 5 → ℝ := fun i => px / E * (hfΦ vb g u0 fG (x i)).x + py / M * (hfΦ vb g u0 fG (x i)).y with hww
    have hdep : ∀ (s : ℝ) (i : ZMod 5), ε * ⟪x i, ε • u0 + s • (ε • w)⟫ =
        (zz i + s * ww i) + (⟪g, u0⟫ + s * ⟪vb, w⟫) := by
      intro s i
      have h1 : ⟪x i, ε • u0 + s • (ε • w)⟫ = ε * (⟪x i, u0⟫ + s * ⟪x i, w⟫) := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right]; ring
      rw [h1, ← mul_assoc, hεε, one_mul, Fr.inner_u0_coord, hw, Fr.inner_w_coord (px / E) (py / M)]
      simp only [hzz, hww]
      rw [← hw]; ring
    have hl : ∀ᶠ s in 𝓝[>] (0 : ℝ), (0 < zz 2 - zz 3 + s * (ww 2 - ww 3)) ∨
        (0 < zz 4 - zz 3 + s * (ww 4 - ww 3)) := by
      rcases hlex with h | ⟨h, h'⟩ | h | ⟨h, h'⟩
      · exact (eventually_pos_affine (A := zz 2 - zz 3) (B := ww 2 - ww 3)
          (Or.inl (by simp only [hzz]; linarith))).mono fun s hs => Or.inl hs
      · exact (eventually_pos_affine (A := zz 2 - zz 3) (B := ww 2 - ww 3)
          (Or.inr ⟨by simp only [hzz]; linarith, by simp only [hww]; linarith⟩)).mono
          fun s hs => Or.inl hs
      · exact (eventually_pos_affine (A := zz 4 - zz 3) (B := ww 4 - ww 3)
          (Or.inl (by simp only [hzz]; linarith))).mono fun s hs => Or.inr hs
      · exact (eventually_pos_affine (A := zz 4 - zz 3) (B := ww 4 - ww 3)
          (Or.inr ⟨by simp only [hzz]; linarith, by simp only [hww]; linarith⟩)).mono
          fun s hs => Or.inr hs
    have h1' := eventually_pos_affine (A := zz 1 - zz 2) (B := ww 1 - ww 2)
      (Or.inl (by simp only [hzz]; linarith))
    have h2' := eventually_pos_affine (A := zz 0 - zz 4) (B := ww 0 - ww 4)
      (Or.inl (by simp only [hzz]; linarith))
    have key : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5 (fun i => zz i + s * ww i) := by
      filter_upwards [h1', h2', hl] with s a1 a2 a3
      refine ⟨by linarith, by linarith, ?_⟩
      rcases a3 with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    filter_upwards [key] with s hs
    have := Q5_shift (⟪g, u0⟫ + s * ⟪vb, w⟫) hs
    show Q5 (fun i => ε * ⟪x i, ε • u0 + s • (ε • w)⟫)
    convert this using 2 with i
    exact hdep s i
  · intro z hinj hQ
    have h1 : IsCyclicUnimodal (fun i => ε * z i) :=
      Q5_unimodal (fun i j hij => hinj (by
        rcases hεs with h | h <;> rw [h] at hij <;> simpa using hij)) hQ
    have h2 := h1.affine_sign (by norm_num) hεs 0
    convert h2 using 2 with i
    simp only [add_zero]
    rw [← mul_assoc, hεε, one_mul]

end HFrame


/-! ### The tests of the five-cycle `(c, m, f, r, f')` and the hidden apex partner -/

section Tests

/-- The five corner points `(c, m, f, r, f')` in frame coordinates: `c = (0, 0, zv)` the apex,
`m = s · f` (screen) at depth `m` the upper middle over the chord `c f`, and `f, r, f'` at depth `0`. -/
def secPts (zv s m f1 f2 r1 r2 g1 g2 : ℝ) : ZMod 5 → V3 :=
  quint ⟨0, 0, zv⟩ ⟨s * f1, s * f2, m⟩ ⟨f1, f2, 0⟩ ⟨r1, r2, 0⟩ ⟨g1, g2, 0⟩

variable {σ px py s zv m f1 f2 r1 r2 g1 g2 : ℝ}

theorem sec5_cyc (hs0 : 0 < s) (hs1 : s < 1) (hm : (1 - s) * zv < m)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1))
    (t1 : 0 < σ * (py * f1 - px * f2)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      SecTest σ px py (secPts zv s m f1 f2 r1 r2 g1 g2 i) (secPts zv s m f1 f2 r1 r2 g1 g2 (i + 1))
        (secPts zv s m f1 f2 r1 r2 g1 g2 j) := by
  have hs1' : 0 < 1 - s := by linarith
  have hK : 0 < m - (1 - s) * zv := by linarith
  have a1 := mul_pos hs0 q1
  have a2 := mul_pos hs0 q4
  have a3 := mul_pos hs1' q1
  have a4 := mul_pos hs1' q4
  have a5 := mul_pos hs1' q3
  have a6 := mul_pos hs0 q2
  have a7 := mul_pos hK t1
  intro i j h1 h2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [secPts, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, SecTest,
      crossXY, tst, hdet]
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)

/-- The partner `w` of the apex (same screen position, depth `zw < zv`) is hidden by the tilt. -/
theorem sec5_W {zw : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hm : (1 - s) * zv < m) (hzw : zw < zv)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1)) (q3 : 0 < σ * (r1 * g2 - g1 * r2))
    (t1 : 0 < σ * (py * f1 - px * f2)) (t2 : 0 < σ * (px * g2 - py * g1)) :
    ∀ i : ZMod 5,
      SecTest σ px py (secPts zv s m f1 f2 r1 r2 g1 g2 i) (secPts zv s m f1 f2 r1 r2 g1 g2 (i + 1))
        ⟨0, 0, zw⟩ := by
  have hU : 0 < zv - zw := by linarith
  have hK : 0 < m - (1 - s) * zw := by nlinarith
  have a1 := mul_pos (mul_pos hs0 hU) t1
  have a2 := mul_pos hK t1
  have a3 := mul_pos hU t2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [secPts, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, SecTest,
      crossXY, tst, hdet] <;>
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)

/-- A vertex strictly inside the shadow quadrilateral is hidden for every tilt. -/
theorem sec5_inside {a1 a2 a3 : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (u1 : 0 < σ * (f1 * a2 - f2 * a1))
    (u2 : 0 < σ * ((r1 - f1) * (a2 - f2) - (r2 - f2) * (a1 - f1)))
    (u3 : 0 < σ * ((g1 - r1) * (a2 - r2) - (g2 - r2) * (a1 - r1)))
    (u4 : 0 < σ * (g2 * a1 - g1 * a2)) :
    ∀ i : ZMod 5,
      SecTest σ px py (secPts zv s m f1 f2 r1 r2 g1 g2 i) (secPts zv s m f1 f2 r1 r2 g1 g2 (i + 1))
        ⟨a1, a2, a3⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have c1 := mul_pos hs0 u1
  have c2 := mul_pos hs1' u1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [secPts, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, SecTest,
      crossXY] <;>
    left <;> linarith

/-- **The sector tilt for a five-cycle `(c, m, f, r, f')`.**  The frame images of the seven points
are `c = (0, 0, zv)`, `m = (s f, depth m)`, `f`, `r`, `f'` at depth `0` and `w = (0, 0, zw)`; the
shadow quadrilateral `(p, f, r, f')` is strictly convex in the orientation `σ` (`q₁`–`q₄`), the
tilt `(px, py)` lies strictly inside its tangent cone at `p` (`t₁`, `t₂`), the seventh point `a`
passes its tests (`hA`), and `r` is lexicographically not the maximum of `f, r, f'`
(`hlex`, with the tilt value `px/E · x + py/M · y`).  Then `V` is Rupert. -/
theorem HFrame.sector5_main {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
    {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³} {σ px py s zv zw m f1 f2 r1 r2 g1 g2 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hmm : mP ∈ V) (hf : fP ∈ V) (hr : rP ∈ V) (hg : gP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * f1, s * f2, m⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨f1, f2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨g1, g2, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 < zv) (hm : (1 - s) * zv < m) (hzw : zw < zv)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1))
    (t1 : 0 < σ * (py * f1 - px * f2)) (t2 : 0 < σ * (px * g2 - py * g1))
    (hA : ∀ i : ZMod 5, SecTest σ px py (secPts zv s m f1 f2 r1 r2 g1 g2 i)
      (secPts zv s m f1 f2 r1 r2 g1 g2 (i + 1)) (hfΦ vb g u0 fG aP))
    (hlex : px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * f1 + py / ⟪N, N⟫ * f2 ∨
      px / ⟪hfE vb g u0, hfE vb g u0⟫ * r1 + py / ⟪N, N⟫ * r2 <
        px / ⟪hfE vb g u0, hfE vb g u0⟫ * g1 + py / ⟪N, N⟫ * g2) :
    IsRupert V := by
  have himg : ∀ i : ZMod 5, hfΦ vb g u0 fG (quint cP mP fP rP gP i) =
      secPts zv s m f1 f2 r1 r2 g1 g2 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [quint_0, Φc]; rfl
    · rw [quint_1, Φm]; rfl
    · rw [quint_2, Φf]; rfl
    · rw [quint_3, Φr]; rfl
    · rw [quint_4, Φg]; rfl
  refine Fr.sector_final V (quint cP mP fP rP gP) ?_ σ px py ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [hc, hmm, hf, hr, hg]
  · intro i j h1 h2
    rw [himg i, himg (i + 1), himg j]
    exact sec5_cyc hs0 hs1 hm q1 q2 q3 q4 t1 i j h1 h2
  · intro y hy hyx i
    rw [himg i, himg (i + 1)]
    rcases hV y hy with h | h | h | h | h | h | h
    · exact absurd h (hyx 0)
    · exact absurd h (hyx 1)
    · exact absurd h (hyx 2)
    · exact absurd h (hyx 3)
    · exact absurd h (hyx 4)
    · rw [h, Φw]; exact sec5_W hs0 hs1 hm hzw q1 q3 t1 t2 i
    · rw [h]; exact hA i
  · have h0 : 0 < (1 - s) * zv := mul_pos (by linarith) hzv
    rw [himg 2, himg 1]; simp only [secPts, quint_1, quint_2]; linarith
  · rw [himg 4, himg 0]; simp only [secPts, quint_0, quint_4]; linarith
  · rw [himg 3, himg 2, himg 4]
    simp only [secPts, quint_2, quint_3, quint_4]
    rcases hlex with h | h
    · exact Or.inr (Or.inl ⟨trivial, h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨trivial, h⟩))

/-- A small positive parameter keeps a strict sign. -/
theorem sec_small_pos {f0 f1 : ℝ} (h : 0 < f0) : ∃ ε : ℝ, 0 < ε ∧ 0 < f0 + ε * f1 := by
  have hd : 0 < |f1| + 1 := by positivity
  refine ⟨f0 / (|f1| + 1), by positivity, ?_⟩
  have h1 : -(f0 / (|f1| + 1) * |f1|) ≤ f0 / (|f1| + 1) * f1 := by
    have := neg_abs_le f1
    have h0 : 0 ≤ f0 / (|f1| + 1) := by positivity
    nlinarith
  have h2 : f0 / (|f1| + 1) * |f1| < f0 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]; nlinarith [abs_nonneg f1]
  linarith

/-- **The choice of the tilt.**  If `r` is to the left of `f' = (A, 0)` or of `h = (b₁, b₂)`
(`r₁ < A` or `r₁ < b₁`), the tilt `(A + λ b₁, λ b₂)` (inside the tangent cone at `p`, near the
direction `f'`) makes `r` lexicographically smaller than `f'` or `h` in the tilt value
`px/E · x + py/M · y`, for small `λ > 0`. -/
theorem tilt_choice {E M A b1 b2 r1 r2 : ℝ} (hE : 0 < E) (hM : 0 < M) (hAE : A = E)
    (hr : r1 < A ∨ r1 < b1) :
    ∃ lam : ℝ, 0 < lam ∧
      ((A + lam * b1) / E * r1 + (lam * b2) / M * r2 < (A + lam * b1) / E * A + (lam * b2) / M * 0 ∨
       (A + lam * b1) / E * r1 + (lam * b2) / M * r2 < (A + lam * b1) / E * b1 + (lam * b2) / M * b2) := by
  subst hAE
  rcases hr with h | h
  · obtain ⟨lam, hlam, hpos⟩ := sec_small_pos (f0 := A - r1) (f1 := -(b1 * (r1 - A) / A + b2 * r2 / M))
      (by linarith)
    refine ⟨lam, hlam, Or.inl ?_⟩
    have : (A + lam * b1) / A * r1 + (lam * b2) / M * r2 - ((A + lam * b1) / A * A + (lam * b2) / M * 0)
        = -((A - r1) + lam * (-(b1 * (r1 - A) / A + b2 * r2 / M))) := by
      field_simp; ring
    linarith
  · obtain ⟨lam, hlam, hpos⟩ := sec_small_pos (f0 := b1 - r1)
      (f1 := -(b1 * (r1 - b1) / A + b2 * (r2 - b2) / M)) (by linarith)
    refine ⟨lam, hlam, Or.inr ?_⟩
    have : (A + lam * b1) / A * r1 + (lam * b2) / M * r2 - ((A + lam * b1) / A * b1 + (lam * b2) / M * b2)
        = -((b1 - r1) + lam * (-(b1 * (r1 - b1) / A + b2 * (r2 - b2) / M))) := by
      field_simp; ring
    linarith

/-- **The sector tilt at the touching N2** (scalar form).  The cycle is `(c, d, b, c', b')`, the
partner of the apex is `a'` and `a` lies strictly inside the shadow `(p, b', c', b)`; the frame
images are as in `isRupert_touchN2`, `A = E` is the abscissa of `b'`, and `c'` is not beyond:
`r₁ < A` or `r₁ < b₁`. -/
theorem HFrame.sector5_n2 {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
    {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³} {s zv zw m A b1 b2 r1 r2 a1 a2 a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hmm : mP ∈ V) (hf : fP ∈ V) (hr : rP ∈ V) (hg : gP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨s * b1, s * b2, m⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨b1, b2, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨A, 0, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨a1, a2, a3⟩)
    (hs0 : 0 < s) (hs1 : s < 1) (hzv : 0 < zv) (hm : (1 - s) * zv < m) (hzw : zw < zv)
    (hAE : A = ⟪hfE vb g u0, hfE vb g u0⟫) (hApos : 0 < A) (hb2 : 0 < b2) (hr2 : 0 < r2)
    (ha2 : 0 < a2)
    (hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0) (hq1 : b1 * r2 - b2 * r1 < 0)
    (hTa1 : (A - r1) * (a2 - r2) + r2 * (a1 - r1) < 0)
    (hTa2 : (a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1) < 0)
    (hu1 : b1 * a2 - b2 * a1 < 0) (hr1 : r1 < A ∨ r1 < b1) : IsRupert V := by
  obtain ⟨lam, hlam, hlx⟩ := tilt_choice (E := ⟪hfE vb g u0, hfE vb g u0⟫) (M := ⟪N, N⟫)
    (A := A) (b1 := b1) (b2 := b2) (r1 := r1) (r2 := r2) Fr.hee Fr.hNN hAE hr1
  have hAb : 0 < A * b2 := mul_pos hApos hb2
  have hAr : 0 < A * r2 := mul_pos hApos hr2
  have hAa : 0 < A * a2 := mul_pos hApos ha2
  have hlb : 0 < lam * b2 * A := mul_pos (mul_pos hlam hb2) hApos
  refine Fr.sector5_main (σ := -1) (px := A + lam * b1) (py := lam * b2) (g1 := A) (g2 := 0)
    hV hc hmm hf hr hg Φc Φm Φf Φr Φg Φw hs0 hs1 hzv hm hzw (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) ?_ hlx.symm
  intro i
  rw [Φa]
  exact sec5_inside hs0 hs1 (by linarith) (by linarith) (by linarith) (by linarith) i

/-- A lower middle over the chord `p f'` (so on the side line of the cycle at `p`, with depth
below the chord from the apex) is hidden by the tilt. -/
theorem sec5_onG {mu a3 : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (q1 : 0 < σ * (f1 * r2 - f2 * r1))
    (q2 : 0 < σ * ((r1 - f1) * (g2 - f2) - (r2 - f2) * (g1 - f1)))
    (q3 : 0 < σ * (r1 * g2 - g1 * r2)) (q4 : 0 < σ * (f1 * g2 - f2 * g1))
    (t2 : 0 < σ * (px * g2 - py * g1)) (hk : a3 < (1 - mu) * zv) :
    ∀ i : ZMod 5,
      SecTest σ px py (secPts zv s m f1 f2 r1 r2 g1 g2 i) (secPts zv s m f1 f2 r1 r2 g1 g2 (i + 1))
        ⟨mu * g1, mu * g2, a3⟩ := by
  have hs1' : 0 < 1 - s := by linarith
  have hmu1' : 0 < 1 - mu := by linarith
  have c1 := mul_pos (mul_pos hs0 hmu0) q4
  have c2 := mul_pos (mul_pos hs1' hmu0) q4
  have c3 := mul_pos hmu0 q2
  have c4 := mul_pos hmu1' q1
  have c5 := mul_pos hmu1' q3
  have hk' : 0 < (1 - mu) * zv - a3 := by linarith
  have c6 := mul_pos hk' t2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [secPts, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4, SecTest,
      crossXY, tst, hdet] <;>
    first
    | (left; linarith)
    | (right; refine ⟨by ring, by linarith⟩)

/-- **The sector tilt at the touching T4** (scalar form).  The cycle is `(b, a', c, b', c')`, the
partner of the apex is `d`, and `a` lies on the side line `p c'` below the chord from the apex. -/
theorem HFrame.sector5_t4 {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
    {V : Finset ℝ³} {cP mP fP rP gP wP aP : ℝ³}
    {s zv zw za A b1 b2 r1 r2 xa ua a3 : ℝ}
    (hV : ∀ y ∈ V, y = cP ∨ y = mP ∨ y = fP ∨ y = rP ∨ y = gP ∨ y = wP ∨ y = aP)
    (hc : cP ∈ V) (hmm : mP ∈ V) (hf : fP ∈ V) (hr : rP ∈ V) (hg : gP ∈ V)
    (Φc : hfΦ vb g u0 fG cP = ⟨0, 0, zv⟩) (Φm : hfΦ vb g u0 fG mP = ⟨xa, 0, za⟩)
    (Φf : hfΦ vb g u0 fG fP = ⟨A, 0, 0⟩) (Φr : hfΦ vb g u0 fG rP = ⟨r1, r2, 0⟩)
    (Φg : hfΦ vb g u0 fG gP = ⟨b1, b2, 0⟩) (Φw : hfΦ vb g u0 fG wP = ⟨0, 0, zw⟩)
    (Φa : hfΦ vb g u0 fG aP = ⟨ua * b1, ua * b2, a3⟩)
    (hs0 : 0 < s) (hs1 : s < 1) (hxs : xa = s * A) (hzv : 0 < zv) (hm : (1 - s) * zv < za)
    (hzw : zw < zv)
    (hAE : A = ⟪hfE vb g u0, hfE vb g u0⟫) (hApos : 0 < A) (hb2 : 0 < b2) (hr2 : 0 < r2)
    (hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0) (hq3 : 0 < r1 * b2 - b1 * r2)
    (hua0 : 0 < ua) (hua1 : ua < 1) (hk : a3 < (1 - ua) * zv) (hr1 : r1 < A ∨ r1 < b1) :
    IsRupert V := by
  obtain ⟨lam, hlam, hlx⟩ := tilt_choice (E := ⟪hfE vb g u0, hfE vb g u0⟫) (M := ⟪N, N⟫)
    (A := A) (b1 := b1) (b2 := b2) (r1 := r1) (r2 := r2) Fr.hee Fr.hNN hAE hr1
  have hAb : 0 < A * b2 := mul_pos hApos hb2
  have hAr : 0 < A * r2 := mul_pos hApos hr2
  have hlb : 0 < lam * b2 * A := mul_pos (mul_pos hlam hb2) hApos
  have Φm' : hfΦ vb g u0 fG mP = ⟨s * A, s * 0, za⟩ := by rw [Φm, hxs]; simp
  refine Fr.sector5_main (σ := 1) (px := A + lam * b1) (py := lam * b2) (f1 := A) (f2 := 0)
    (g1 := b1) (g2 := b2) hV hc hmm hf hr hg Φc Φm' Φf Φr Φg Φw hs0 hs1 hzv hm hzw
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ?_ hlx
  intro i
  rw [Φa]
  exact sec5_onG hs0 hs1 hua0 hua1 (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hk i

end Tests

end Minimality
end
