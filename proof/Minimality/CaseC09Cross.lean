module

public import Minimality.CaseC09Tests
public import Minimality.HEndFinal
public import Minimality.Octahedron

@[expose] public section

/-!
# Type 09, acute case (c): the three crossing tests (`FEWER-FACES-PROOFS.md` §27, continued (2))

The bridge from frame coordinates to `isRupert_of_tilted_unimodal'`: a rim cycle of the seven
points, tilt tests in frame coordinates (`ST`), and an open depth condition (`rupert_rim`,
`rupert_rim4`, `rupert_rim5`, `rupert_rim5p`).  Then, at the frame's own metric `diag(A, g)`:

* `Frame09.t32M` (27.32^M, `c+ > b-`): the rim `(m2+, xb, xa, m1+)`; needs `A12 < A22`.
* `Frame09.t31` (27.31 for type 09): the folded-plane rims `(v, m1-, xa, m2+)` (`t- < s-`,
  `a+ < c+`), `(v, m2-, xb, m2+)` (`s- < t-`, `a+ < c+`) and `(v, m2-, xb, m2+, m1+)`
  (`s- < t-`, `a+ > c+`); needs `A12 ≤ A11` and `A12 < A22`.
* `Frame09.amM` (27.29, row `A^M`): the tests `T1` (at `m2+ xb`) and `T2` (at `m2+ xa`), chosen by
  the sign of `⟨u₁, u₂⟩_G`; no acuteness needed.
* `Frame09.tests09 (hA : A12 < A22) : Tests09 F` and `rupert_or_27_48'`.

At a right angle `A12 = A22` (at `xb`) the rims of 27.32^M and of case I-B of 27.31 are *not*
unimodal for some `g` (the tie `φ(xa) = φ(xb)` is broken by the tilt in the wrong direction).
-/

namespace Minimality.CaseC09

open Finset Filter
open scoped RealInnerProductSpace Topology

/-- Frame coordinates `(a, b, c)` of a vector `a u₁ + b u₂ + c e`. -/
structure C3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace C3
def sub (a b : C3) : C3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
end C3

/-- The determinant of three coordinate vectors (`⟪a × b, w⟫`). -/
def Dc (a b w : C3) : ℝ :=
  (a.y * b.z - a.z * b.y) * w.x + (a.z * b.x - a.x * b.z) * w.y + (a.x * b.y - a.y * b.x) * w.z

/-- The Gram form `diag(A, g)` on coordinates. -/
def Gf (A11 A12 A22 g : ℝ) (a b : C3) : ℝ :=
  A11 * (a.x * b.x) + A12 * (a.x * b.y + b.x * a.y) + A22 * (a.y * b.y) + g * (a.z * b.z)

/-- The tilt test in frame coordinates (the sign `σ` fixes the screen orientation). -/
def ST (σ : ℝ) (u v a b : C3) : Prop :=
  0 < σ * Dc a b u ∨ (Dc a b u = 0 ∧ 0 < σ * Dc a b v)

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- The vector with frame coordinates `p`. -/
noncomputable def fvC (p : C3) : ℝ³ :=
  p.x • (x 3 - x 0) + p.y • (x 5 - x 0) + p.z • F.e

/-- The frame coordinates of the point `x j` (relative to `x 0`). -/
noncomputable def ptC (j : Fin 7) : C3 := ⟨F.cx j, F.cy j, F.cz j⟩

noncomputable def kap : ℝ := det3 (x 3 - x 0) (x 5 - x 0) F.e
noncomputable def a11 (_F : Frame09 x) : ℝ := ⟪x 3 - x 0, x 3 - x 0⟫
noncomputable def a12 (_F : Frame09 x) : ℝ := ⟪x 3 - x 0, x 5 - x 0⟫
noncomputable def a22 (_F : Frame09 x) : ℝ := ⟪x 5 - x 0, x 5 - x 0⟫
noncomputable def gg : ℝ := ⟪F.e, F.e⟫

/-- The depth form of the frame. -/
noncomputable def GG (a b : C3) : ℝ := Gf F.a11 F.a12 F.a22 F.gg a b

lemma x_sub (j i : Fin 7) : x j - x i = F.fvC ((F.ptC j).sub (F.ptC i)) := by
  rw [F.x_eq j, F.x_eq i]
  simp only [fvC, ptC, C3.sub]
  module

lemma x_eq' (j : Fin 7) : x j = x 0 + F.fvC (F.ptC j) := by
  rw [F.x_eq j]
  simp only [fvC, ptC]
  module

lemma decomp (w : ℝ³) : ∃ p : C3, w = F.fvC p := by
  have h := F.basis.sum_repr w
  simp only [Fin.sum_univ_three, F.basis_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact ⟨⟨F.basis.repr w 0, F.basis.repr w 1, F.basis.repr w 2⟩, h.symm⟩

lemma det3_fvC (a b w : C3) :
    det3 (F.fvC a) (F.fvC b) (F.fvC w) = F.kap * Dc a b w := by
  simp only [det3, kap, fvC, Dc, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

lemma inner_fvC (p q : C3) : ⟪F.fvC p, F.fvC q⟫ = F.GG p q := by
  simp only [fvC, GG, Gf, a11, a12, a22, gg]
  rw [F.inner_frame]

lemma inner_x_fvC (j : Fin 7) (q : C3) : ⟪x j, F.fvC q⟫ = ⟪x 0, F.fvC q⟫ + F.GG (F.ptC j) q := by
  conv_lhs => rw [F.x_eq' j]
  rw [inner_add_left, F.inner_fvC]

lemma kap_ne : F.kap ≠ 0 := by
  intro h0
  have hN : ∀ w : ℝ³, ⟪cross (x 3 - x 0) (x 5 - x 0), w⟫ = 0 := by
    intro w
    obtain ⟨p, rfl⟩ := F.decomp w
    simp only [fvC, inner_add_right, real_inner_smul_right, inner_cross_left, inner_cross_right]
    have : ⟪cross (x 3 - x 0) (x 5 - x 0), F.e⟫ = 0 := h0
    rw [this]; ring
  have hc : cross (x 3 - x 0) (x 5 - x 0) = 0 := by
    have := hN (cross (x 3 - x 0) (x 5 - x 0))
    exact inner_self_eq_zero.mp this
  have hu1 : x 3 - x 0 ≠ 0 := by
    intro h
    have := F.coord_zero (a := 1) (b := 0) (c := 0) (by rw [h]; simp)
    exact one_ne_zero this.1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, x 5 - x 0 = r • (x 3 - x 0) := ⟨_, eq_smul_of_cross_eq_zero hu1 hc⟩
  have := F.coord_zero (a := -r) (b := 1) (c := 0) (by rw [one_smul, hr]; simp [neg_smul])
  exact one_ne_zero this.2.1

/-- **The bridge.**  A cycle `c` of the seven points, the view `u` and the tilt `v` in frame
coordinates, the determinant tests `ST` for the cycle and for the remaining points (read off
frame coordinates), and an open, positively homogeneous, shift-invariant depth condition `Q`
holding eventually at the tilted depths and forcing unimodality. -/
theorem rupert_rim {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → Fin 7) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ a : ℝ, 0 < a → Q z → Q fun i => a * z i)
    (hQsh : ∀ z : ZMod k → ℝ, ∀ a : ℝ, Q z → Q fun i => z i + a)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q fun i => F.GG (F.ptC (c i)) u + s * F.GG (F.ptC (c i)) v)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) :
    IsRupert (Finset.univ.image x) := by
  classical
  set u0 : ℝ³ := F.fvC u with hu0def
  set w : ℝ³ := F.fvC v with hwdef
  have hκ := F.kap_ne
  set t := σ * F.kap with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hconv : ∀ a b : C3, ST σ u v a b →
      TiltSign (F.fvC a) (F.fvC b) (ε • u0) (ε • w) := by
    intro a b h
    have hk2 : 0 < F.kap ^ 2 := by positivity
    rcases h with h | ⟨h0, h1⟩
    · left
      rw [det3_smul_right, hu0def, F.det3_fvC]
      refine sgn_pos t _ ?_
      have := mul_pos hk2 h
      calc 0 < F.kap ^ 2 * (σ * Dc a b u) := this
        _ = t * (F.kap * Dc a b u) := by rw [ht]; ring
    · right
      refine ⟨by rw [det3_smul_right, hu0def, F.det3_fvC, h0, mul_zero, mul_zero], ?_⟩
      rw [det3_smul_right, hwdef, F.det3_fvC]
      refine sgn_pos t _ ?_
      have := mul_pos hk2 h1
      calc 0 < F.kap ^ 2 * (σ * Dc a b v) := this
        _ = t * (F.kap * Dc a b v) := by rw [ht]; ring
  have hu0 : u0 ≠ 0 := by
    intro h0
    have := F.coord_zero (a := u.x) (b := u.y) (c := u.z) (by exact h0)
    rcases hu with h | h | h
    · exact h this.1
    · exact h this.2.1
    · exact h this.2.2
  have hu' : ε • u0 ≠ 0 := by
    intro h0
    rcases hεs with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hu0 h0
  refine isRupert_of_tilted_unimodal' (Finset.univ.image x) (ε • u0) (ε • w) hu' (k := k) hk
    (fun i => x (c i)) (fun i => Finset.mem_image_of_mem x (Finset.mem_univ _))
    (fun i j hi hj => ?_) (fun y hy hyx i => ?_)
    (fun z => Q fun i => ε * z i) ?_ ?_ ?_ ?_
  · show TiltSign (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) (ε • u0) (ε • w)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hcyc i j hi hj)
  · obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hy
    show TiltSign (x (c (i + 1)) - x (c i)) (x j' - x (c i)) (ε • u0) (ε • w)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hrest j' (fun jj h => hyx jj (by simp [h])) i)
  · have : {z : ZMod k → ℝ | Q fun i => ε * z i} =
        (fun z : ZMod k → ℝ => fun i => ε * z i) ⁻¹' {z | Q z} := rfl
    rw [this]
    exact hQo.preimage (by fun_prop)
  · intro z a ha hQ
    have := hQs _ a ha hQ
    convert this using 2 with i
    ring
  · have hdep : ∀ (s : ℝ) (i : ZMod k), ε * ⟪x (c i), ε • u0 + s • (ε • w)⟫ =
        (⟪x 0, u0⟫ + s * ⟪x 0, w⟫) +
          (F.GG (F.ptC (c i)) u + s * F.GG (F.ptC (c i)) v) := by
      intro s i
      have h1 : ⟪x (c i), ε • u0 + s • (ε • w)⟫ = ε * (⟪x (c i), u0⟫ + s * ⟪x (c i), w⟫) := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_smul_right]; ring
      rw [h1, ← mul_assoc, hεε, one_mul, hu0def, hwdef, F.inner_x_fvC (c i) u, F.inner_x_fvC (c i) v]
      ring
    filter_upwards [hQe] with s hs
    have := hQsh _ (⟪x 0, u0⟫ + s * ⟪x 0, w⟫) hs
    show Q fun i => ε * ⟪x (c i), ε • u0 + s • (ε • w)⟫
    convert this using 2 with i
    rw [hdep s i]; ring
  · intro z hinj hQ
    have h1 : IsCyclicUnimodal (fun i => ε * z i) :=
      hQu _ (fun i j hij => hinj (by
        rcases hεs with h | h <;> rw [h] at hij <;> simpa using hij)) hQ
    have h2 := h1.affine_sign (by omega) hεs 0
    convert h2 using 2 with i
    simp only [add_zero]
    rw [← mul_assoc, hεε, one_mul]

end Frame09

/-! ### The 4-cycle depth condition -/

/-- The open depth condition of a four-corner rim: the diagonal ranges overlap (the form of
`Overlap4`, without the distinctness, which injectivity supplies). -/
def Q4 (z : ZMod 4 → ℝ) : Prop :=
  (z 0 < z 1 ∨ z 0 < z 3 ∨ z 2 < z 1 ∨ z 2 < z 3) ∧
    (z 1 < z 0 ∨ z 3 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2)

theorem Q4_open : IsOpen {z : ZMod 4 → ℝ | Q4 z} := by
  have hlt : ∀ i j : ZMod 4, IsOpen {z : ZMod 4 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q4, Set.ofPred_and, Set.ofPred_or]
  exact (((hlt 0 1).union ((hlt 0 3).union ((hlt 2 1).union (hlt 2 3)))).inter
    (((hlt 1 0).union ((hlt 3 0).union ((hlt 1 2).union (hlt 3 2))))))

theorem Q4_smul {z : ZMod 4 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q4 z) : Q4 fun i => a * z i := by
  have key : ∀ {p q : ℝ}, p < q → a * p < a * q := fun h => mul_lt_mul_of_pos_left h ha
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rcases h1 with h | h | h | h
    exacts [Or.inl (key h), Or.inr (Or.inl (key h)), Or.inr (Or.inr (Or.inl (key h))),
      Or.inr (Or.inr (Or.inr (key h)))]
  · rcases h2 with h | h | h | h
    exacts [Or.inl (key h), Or.inr (Or.inl (key h)), Or.inr (Or.inr (Or.inl (key h))),
      Or.inr (Or.inr (Or.inr (key h)))]

theorem Q4_shift {z : ZMod 4 → ℝ} (a : ℝ) (h : Q4 z) : Q4 fun i => z i + a := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rcases h1 with h | h | h | h
    exacts [Or.inl (by linarith), Or.inr (Or.inl (by linarith)),
      Or.inr (Or.inr (Or.inl (by linarith))), Or.inr (Or.inr (Or.inr (by linarith)))]
  · rcases h2 with h | h | h | h
    exacts [Or.inl (by linarith), Or.inr (Or.inl (by linarith)),
      Or.inr (Or.inr (Or.inl (by linarith))), Or.inr (Or.inr (Or.inr (by linarith)))]

theorem Q4_unimodal {z : ZMod 4 → ℝ} (hinj : Function.Injective z) (h : Q4 z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2⟩ := h
  refine isCyclicUnimodal_four hinj ⟨h1, h2, ?_, ?_⟩
  · intro e; have := hinj e; revert this; decide
  · intro e; have := hinj e; revert this; decide

/-! ### 27.31, case II: `t- < s-`, `a+ < c+` (apex `xa`): the rim `(v, m1-, xa, m2+)` -/

section T31
variable {tp hp tm hm sp kp sm km : ℝ}

theorem t31II_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1, -1, 0⟩ ⟨-1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a5 := mul_pos hsp hhm
  have a6 := mul_pos htm hhm
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

/-- The three remaining points in case II, one lemma for each. -/
theorem t31II_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : hp * sp < kp * tp) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨-1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a5 := mul_pos hsp hhm
  have a6 := mul_pos htm hhm
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  have a9 := mul_pos htp hhm
  have a10 := mul_pos htp' hhm
  have a11 := mul_pos hhp htm
  have a12 := mul_pos hhp htm'
  have a13 := sub_pos.2 roof
  have a14 := sub_pos.2 H31
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t31II_rest5 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨-1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a5 := mul_pos hsp hhm
  have a6 := mul_pos htm hhm
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t31II_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (hts : tm < sm) (Km : km * (1 - tm) = (1 - sm) * hm) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨-1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a5 := mul_pos hsp hhm
  have a6 := mul_pos htm hhm
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  have a9 := mul_pos hsm hhm
  have a10 := mul_pos hsm' hhm
  have a11 := mul_pos hkm htm
  have a12 := mul_pos hkm htm'
  have a13 := mul_pos hsm hkm
  have a14 := mul_pos (sub_pos.2 hts) hkm
  have a15 := mul_pos (sub_pos.2 hts) hhm
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

end T31

/-! ### 27.31, case I-A: `s- < t-`, `a+ < c+` (apex `xb`): the rim `(v, m2-, xb, m2+)` -/

section T31A
variable {tp hp tm hm sp kp sm km : ℝ}

theorem t31IA_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t31IA_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : hp * sp < kp * tp) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hhp
  have a2 := mul_pos hkm htp
  have a3 := mul_pos hsm' hhp
  have a4 := mul_pos hkm htp'
  have a5 := sub_pos.2 roof
  have a6 := sub_pos.2 H31
  have a7 := mul_pos hsm hkp
  have a8 := mul_pos hsp hkm
  have a9 := mul_pos hsp' hkp
  have a10 := mul_pos hsm hkm
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t31IA_rest3 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t31IA_rest4 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (hst : sm < tm) (Km : km * (1 - tm) = (1 - sm) * hm) :
    ∀ i : ZMod 4,
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos htm hkm
  have a8 := mul_pos htm' hkm
  have a9 := mul_pos htm hkp
  have a10 := mul_pos htm' hkp
  have a11 := mul_pos hsm hhm
  have a12 := mul_pos (sub_pos.2 hst) hkm
  have a13 := mul_pos (sub_pos.2 hst) hhm
  have a14 := mul_pos (sub_pos.2 hst) hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

end T31A

/-! ### 27.31, case I-B: `s- < t-`, `a+ > c+` (apex `xb`): the rim `(v, m2-, xb, m2+, m1+)` -/

section T31B
variable {tp hp tm hm sp kp sm km : ℝ}

theorem t31IB_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : kp * tp < hp * sp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a10 := sub_pos.2 H31
  have a11 := mul_pos hsm hhp
  have a12 := mul_pos hkm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hkm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t31IB_rest3 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : kp * tp < hp * sp) :
    ∀ i : ZMod 5,
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a10 := sub_pos.2 H31
  have a11 := mul_pos hsm hhp
  have a12 := mul_pos hkm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hkm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t31IB_rest4 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (hst : sm < tm) (Km : km * (1 - tm) = (1 - sm) * hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) (H31 : kp * tp < hp * sp) :
    ∀ i : ZMod 5,
      ST 1 ⟨1, -1, 0⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos htm hkm
  have a8 := mul_pos htm' hkm
  have a9 := mul_pos htm hkp
  have a10 := mul_pos htm' hkp
  have a11 := mul_pos hsm hhm
  have a12 := mul_pos (sub_pos.2 hst) hkm
  have a13 := mul_pos (sub_pos.2 hst) hhm
  have a14 := mul_pos (sub_pos.2 hst) hkp
  have a15 := sub_pos.2 roof
  have a16 := sub_pos.2 H31
  have a17 := mul_pos htp hhm
  have a18 := mul_pos htp' hhm
  have a19 := mul_pos hsp hhm
  have a20 := mul_pos hsp' hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by linarith, by nlinarith⟩)

end T31B

/-! ### Corollary 27.29, row `A^M`: the pair at `m2+` -/

section AM
variable {tp hp tm hm sp kp sm km : ℝ}

/-- `T1`: the edge crossing at `m2+ xb`, view `u₁ = m2+ - xb`, rim `(v, m1-, xa, m2+)`. -/
theorem am1_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨0, sp - 1, kp⟩ ⟨1, -2 * sp, -2 * kp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a5 := mul_pos hsp hhm
  have a6 := mul_pos htm hhm
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  have a9 := mul_pos (mul_pos htm hsp') hhm
  have a10 := mul_pos (mul_pos htm' hsp') hhm
  have a11 := mul_pos (mul_pos htm hsp') hkp
  have a12 := mul_pos (mul_pos htm' hsp') hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem am1_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (roof : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i : ZMod 4,
      ST 1 ⟨0, sp - 1, kp⟩ ⟨1, -2 * sp, -2 * kp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a5 := mul_pos hsp' hhp
  have a6 := mul_pos htp hhm
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  have a9 := sub_pos.2 roof
  have a10 := mul_pos hsp' hhp
  have a11 := mul_pos (mul_pos hsp' hhm) htp
  have a12 := mul_pos (mul_pos hsp' hhm) htp'
  have a13 := mul_pos (mul_pos hsp' hhp) htm
  have a14 := mul_pos (mul_pos hsp' hhp) htm'
  have a15 := mul_pos (mul_pos hsp' hhm) hkp
  have a16 := mul_pos (mul_pos hsp' hhp) hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem am1_rest5 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) :
    ∀ i : ZMod 4,
      ST 1 ⟨0, sp - 1, kp⟩ ⟨1, -2 * sp, -2 * kp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  have a9 := mul_pos (mul_pos htm hsp') hhm
  have a10 := mul_pos (mul_pos htm' hsp') hhm
  have a11 := mul_pos (mul_pos htm hsp') hkp
  have a12 := mul_pos (mul_pos htm' hsp') hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem am1_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (A1 : (1 - sp) * km < sm * kp) :
    ∀ i : ZMod 4,
      ST 1 ⟨0, sp - 1, kp⟩ ⟨1, -2 * sp, -2 * kp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have htm' : 0 < 1 - tm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos htm hkp
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos htm' hkp
  have a4 := mul_pos hhm hsp'
  have a7 := mul_pos hsp' hkp
  have a8 := mul_pos hsp hkp
  have a9 := sub_pos.2 A1
  have a10 := mul_pos htm a9
  have a11 := mul_pos htm' a9
  have a12 := mul_pos hhm a9
  have a13 := mul_pos hsp' hkm
  have a14 := mul_pos (mul_pos htm hsp') hhm
  have a15 := mul_pos (mul_pos htm' hsp') hhm
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

/-- `T2`: the edge crossing at `m2+ xa`, view `u₂ = m2+ - xa`, rim `(m2+, m1+, v, m2-, xb)`; the
tilt `(xb - m2+) + b (m1+ - m2+)`. -/
theorem am2_cyc {b : ℝ} (hb : 0 < b) (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp)
    (htp1 : tp < 1) (hhp : 0 < hp) (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨-1, sp, kp⟩ ⟨b * tp, (1 - sp) - b * sp, -kp + b * (hp - kp)⟩
        ((quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i))
        ((quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ j).sub
          (quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos hsm hhp
  have a12 := mul_pos hkm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hkm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem am2_rest3 {b : ℝ} (hb : 0 < b) (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp)
    (htp1 : tp < 1) (hhp : 0 < hp) (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i : ZMod 5,
      ST (-1) ⟨-1, sp, kp⟩ ⟨b * tp, (1 - sp) - b * sp, -kp + b * (hp - kp)⟩
        ((quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos hsm hhp
  have a12 := mul_pos hkm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hkm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  have a19 := mul_pos hb htp
  have a20 := mul_pos hb hkp
  have a21 := mul_pos hb hhp
  have a22 := mul_pos hb hsp
  have a23 := mul_pos hb hsp'
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem am2_rest4 {b : ℝ} (hb : 0 < b) (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp)
    (htp1 : tp < 1) (hhp : 0 < hp) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (roof : hp * (1 - sp) < kp * (1 - tp))
    (A2 : hm * sm < tm * kp * sm + tm * sp * km)
    (A3 : hm * (1 - sm) < kp * tm * (1 - sm) + km * (1 - sp * tm)) :
    ∀ i : ZMod 5,
      ST (-1) ⟨-1, sp, kp⟩ ⟨b * tp, (1 - sp) - b * sp, -kp + b * (hp - kp)⟩
        ((quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub
          (quint (⟨0, sp, kp⟩ : C3) ⟨tp, 0, hp⟩ ⟨0, 0, 0⟩ ⟨0, sm, -km⟩ ⟨0, 1, 0⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hkp
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm' hkp
  have a4 := mul_pos hsp' hkm
  have a5 := mul_pos hsm hkm
  have a6 := mul_pos hsp hkp
  have a7 := mul_pos hsm' hkm
  have a8 := mul_pos hsp' hkp
  have a9 := sub_pos.2 roof
  have a11 := mul_pos hsm hhp
  have a12 := mul_pos hkm htp
  have a13 := mul_pos hsm' hhp
  have a14 := mul_pos hkm htp'
  have a15 := mul_pos htp hkp
  have a16 := mul_pos htp' hkp
  have a17 := mul_pos hsp hhp
  have a18 := mul_pos hsp' hhp
  have a19 := sub_pos.2 A2
  have a20 := sub_pos.2 A3
  have a21 := mul_pos htm hkp
  have a22 := mul_pos htm hhp
  have a23 := mul_pos htm' hhp
  have a24 := mul_pos htm hkm
  have a25 := mul_pos htm' hkm
  have a26 := mul_pos htp hhm
  have a27 := mul_pos htp' hhm
  have a28 := mul_pos hsp hhm
  have a29 := mul_pos hsp' hhm
  have a30 := mul_pos hsm hhm
  have a31 := mul_pos hsm' hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

/-- The three impossible double peaks of `T2` (`FEWER-FACES-PROOFS.md` 27.27, translated by `M`):
the depths are `z = c₀ ζ + c₂ Y + c₃ Z` on the screen coordinates `(Y, Z, ζ)`. -/
theorem am2_pair13 {c0 c2 c3 z0 z1 z2 z3 z4 : ℝ} (hc0 : 0 < c0) (htp : 0 < tp) (htp1 : tp < 1)
    (hhp : 0 < hp) (hsm1 : sm < 1) (hsm : 0 < sm) (hkm : 0 < km)
    (e0 : z0 = c2 * sp + c3 * kp) (e1 : z1 = -c0 * tp + c2 * sp * tp + c3 * (hp + kp * tp))
    (e2 : z2 = 0) (e3 : z3 = c2 * sm - c3 * km) (e4 : z4 = c2) :
    z1 < z0 ∨ z1 < z2 ∨ z3 < z2 ∨ z3 < z4 := by
  by_contra hc
  push Not at hc
  obtain ⟨c1, c2', c3', c4⟩ := hc
  subst e0 e1 e2 e3 e4
  have hm1 : 0 < km * tp := mul_pos hkm htp
  have hm2 : 0 < km * (1 - tp) := mul_pos hkm (by linarith)
  have hm3 : 0 < hp * (1 - sm) := mul_pos hhp (by linarith)
  have hm4 : 0 < hp * sm := mul_pos hhp hsm
  nlinarith [mul_nonneg hm1.le (sub_nonneg.2 c1), mul_nonneg hm2.le (sub_nonneg.2 c2'),
    mul_nonneg hm3.le (sub_nonneg.2 c3'), mul_nonneg hm4.le (sub_nonneg.2 c4),
    mul_pos hc0 (mul_pos htp hkm)]

theorem am2_pair14 {c0 c2 c3 z0 z1 z2 z3 z4 : ℝ} (hc0 : 0 < c0) (htp : 0 < tp) (htp1 : tp < 1)
    (hhp : 0 < hp) (hsp : 0 < sp) (hsp1 : sp < 1)
    (roof : hp * (1 - sp) < kp * (1 - tp))
    (e0 : z0 = c2 * sp + c3 * kp) (e1 : z1 = -c0 * tp + c2 * sp * tp + c3 * (hp + kp * tp))
    (e2 : z2 = 0) (e3 : z3 = c2 * sm - c3 * km) (e4 : z4 = c2) :
    z4 < z3 ∨ z4 < z0 ∨ z1 < z0 ∨ z1 < z2 := by
  by_contra hc
  push Not at hc
  obtain ⟨c5, c6, c1, c2'⟩ := hc
  subst e0 e1 e2 e3 e4
  have hD : 0 < kp * (1 - tp) - hp * (1 - sp) := sub_pos.2 roof
  have hm1 : 0 < hp * (1 - sp) + tp * (kp * (1 - tp) - hp * (1 - sp)) := by
    have := mul_pos htp hD
    have := mul_pos hhp (sub_pos.2 hsp1)
    linarith
  have hm2 : 0 < (1 - tp) * (kp * (1 - tp) - hp * (1 - sp)) := mul_pos (by linarith) hD
  have hm6 : 0 < hp * sp * (1 - tp) := mul_pos (mul_pos hhp hsp) (by linarith)
  nlinarith [mul_nonneg hm1.le (sub_nonneg.2 c1), mul_nonneg hm2.le (sub_nonneg.2 c2'),
    mul_nonneg hm6.le (sub_nonneg.2 c6),
    mul_pos hc0 (add_pos (mul_pos htp hm1) (mul_pos htp hm2))]

theorem am2_pair24 {c0 c2 c3 z0 z1 z2 z3 z4 : ℝ} (hc3 : 0 < c3) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp)
    (A1 : (1 - sp) * km < sm * kp)
    (e0 : z0 = c2 * sp + c3 * kp) (e1 : z1 = -c0 * tp + c2 * sp * tp + c3 * (hp + kp * tp))
    (e2 : z2 = 0) (e3 : z3 = c2 * sm - c3 * km) (e4 : z4 = c2) (hc0 : 0 < c0) (htp : 0 < tp) :
    z2 < z1 ∨ z2 < z3 ∨ z4 < z3 ∨ z4 < z0 := by
  by_contra hc
  push Not at hc
  obtain ⟨c1, c3', c5, c6⟩ := hc
  subst e0 e1 e2 e3 e4
  have hν : 0 < sm * kp - (1 - sp) * km := sub_pos.2 A1
  have hm3 : 0 < (1 - sm) * kp + (1 - sp) * km + (1 - sp) := by
    have := mul_pos (sub_pos.2 hsm1) hkp
    have := mul_pos (sub_pos.2 hsp1) hkm
    linarith
  have hm6 : 0 < km + sm := by linarith
  nlinarith [mul_nonneg hm3.le (sub_nonneg.2 c3'), mul_nonneg hν.le (sub_nonneg.2 c5),
    mul_nonneg hm6.le (sub_nonneg.2 c6), mul_pos hν hc3]

end AM

/-! ### Eventual depth comparisons -/

/-- A depth comparison at the view, broken by the tilt: eventually `a + s a' < b + s b'`. -/
theorem ev_lt {a b a' b' : ℝ} (h : a < b ∨ (a = b ∧ a' < b')) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), a + s * a' < b + s * b' := by
  have := eventually_pos_affine (A := b - a) (B := b' - a') (by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩)
  filter_upwards [this] with s hs
  linarith

/-- `Q4` holds eventually at the tilted depths if its two disjunctions hold lexicographically. -/
theorem Q4_eventually {z w : ZMod 4 → ℝ}
    (hA : (z 0 < z 1 ∨ (z 0 = z 1 ∧ w 0 < w 1)) ∨ (z 0 < z 3 ∨ (z 0 = z 3 ∧ w 0 < w 3)) ∨
      (z 2 < z 1 ∨ (z 2 = z 1 ∧ w 2 < w 1)) ∨ (z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3)))
    (hB : (z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) ∨ (z 3 < z 0 ∨ (z 3 = z 0 ∧ w 3 < w 0)) ∨
      (z 1 < z 2 ∨ (z 1 = z 2 ∧ w 1 < w 2)) ∨ (z 3 < z 2 ∨ (z 3 = z 2 ∧ w 3 < w 2))) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q4 fun i => z i + s * w i := by
  have eA : ∀ᶠ s in 𝓝[>] (0 : ℝ), (z 0 + s * w 0 < z 1 + s * w 1 ∨
      z 0 + s * w 0 < z 3 + s * w 3 ∨ z 2 + s * w 2 < z 1 + s * w 1 ∨
      z 2 + s * w 2 < z 3 + s * w 3) := by
    rcases hA with h | h | h | h
    · exact (ev_lt h).mono fun s hs => Or.inl hs
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inl hs)
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inr (Or.inl hs))
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inr (Or.inr hs))
  have eB : ∀ᶠ s in 𝓝[>] (0 : ℝ), (z 1 + s * w 1 < z 0 + s * w 0 ∨
      z 3 + s * w 3 < z 0 + s * w 0 ∨ z 1 + s * w 1 < z 2 + s * w 2 ∨
      z 3 + s * w 3 < z 2 + s * w 2) := by
    rcases hB with h | h | h | h
    · exact (ev_lt h).mono fun s hs => Or.inl hs
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inl hs)
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inr (Or.inl hs))
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inr (Or.inr hs))
  filter_upwards [eA, eB] with s a b
  exact ⟨a, b⟩

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- The bridge for four-corner rims, with the corners' frame coordinates `P₀ … P₃`. -/
theorem rupert_rim4 (c0 c1 c2 c3 : Fin 7) (P0 P1 P2 P3 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        ((quad P0 P1 P2 P3 j).sub (quad P0 P1 P2 P3 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → ∀ i : ZMod 4,
      ST σ u v ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        ((F.ptC j').sub (quad P0 P1 P2 P3 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q4 fun i => F.GG (quad P0 P1 P2 P3 i) u +
      s * F.GG (quad P0 P1 P2 P3 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quad c0 c1 c2 c3 i) = quad P0 P1 P2 P3 i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3, e0, e1, e2, e3]
  refine F.rupert_rim (k := 4) (by norm_num) (quad c0 c1 c2 c3) σ hσ u v hu ?_ ?_ Q4 Q4_open
    (fun z a ha => Q4_smul ha) (fun z a => Q4_shift a) ?_ (fun z hz hq => Q4_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hc]
    refine hrest j' ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quad_0, h])
    · exact fun h => hj' 1 (by simp [quad_1, h])
    · exact fun h => hj' 2 (by simp [quad_2, h])
    · exact fun h => hj' 3 (by simp [quad_3, h])
  · simpa only [hc] using hQe

end Frame09

/-! ### The 5-cycle depth condition -/

/-- The open depth condition of the five-corner rim `(a, b, c, d, e)` of case I-B: the chain
`b < a`, `c < b`, `c < d`, `d < e`, `a < e` (so `e` is the unique top). -/
def Q5c (z : ZMod 5 → ℝ) : Prop :=
  z 1 < z 0 ∧ z 2 < z 1 ∧ z 2 < z 3 ∧ z 3 < z 4 ∧ z 0 < z 4

theorem Q5c_open : IsOpen {z : ZMod 5 → ℝ | Q5c z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q5c, Set.ofPred_and]
  exact (hlt 1 0).inter ((hlt 2 1).inter ((hlt 2 3).inter ((hlt 3 4).inter (hlt 0 4))))

theorem Q5c_smul {z : ZMod 5 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q5c z) : Q5c fun i => a * z i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 ha,
    mul_lt_mul_of_pos_left h3 ha, mul_lt_mul_of_pos_left h4 ha, mul_lt_mul_of_pos_left h5 ha⟩

theorem Q5c_shift {z : ZMod 5 → ℝ} (a : ℝ) (h : Q5c z) : Q5c fun i => z i + a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem Q5c_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5c z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine isCyclicUnimodal_of_top (by norm_num) hinj 4 ?_
  intro i hi
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · left; rw [b0]; exact h5
  · left; rw [b1]; exact h1
  · left; rw [b2]; exact h2
  · right; rw [a3]; exact h4
  · exact absurd rfl hi

theorem Q5c_eventually {z w : ZMod 5 → ℝ}
    (h1 : z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) (h2 : z 2 < z 1 ∨ (z 2 = z 1 ∧ w 2 < w 1))
    (h3 : z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3)) (h4 : z 3 < z 4 ∨ (z 3 = z 4 ∧ w 3 < w 4))
    (h5 : z 0 < z 4 ∨ (z 0 = z 4 ∧ w 0 < w 4)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5c fun i => z i + s * w i := by
  filter_upwards [ev_lt h1, ev_lt h2, ev_lt h3, ev_lt h4, ev_lt h5] with s a b c d e
  exact ⟨a, b, c, d, e⟩

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- The bridge for five-corner rims. -/
theorem rupert_rim5 (c0 c1 c2 c3 c4 : Fin 7) (P0 P1 P2 P3 P4 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (e4 : F.ptC c4 = P4)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((quint P0 P1 P2 P3 P4 j).sub (quint P0 P1 P2 P3 P4 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → j' ≠ c4 → ∀ i : ZMod 5,
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((F.ptC j').sub (quint P0 P1 P2 P3 P4 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5c fun i => F.GG (quint P0 P1 P2 P3 P4 i) u +
      s * F.GG (quint P0 P1 P2 P3 P4 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quint c0 c1 c2 c3 c4 i) = quint P0 P1 P2 P3 P4 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, e0, e1, e2, e3, e4]
  refine F.rupert_rim (k := 5) (by norm_num) (quint c0 c1 c2 c3 c4) σ hσ u v hu ?_ ?_ Q5c
    Q5c_open (fun z a ha => Q5c_smul ha) (fun z a => Q5c_shift a) ?_
    (fun z hz hq => Q5c_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hc]
    refine hrest j' ?_ ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quint_0, h])
    · exact fun h => hj' 1 (by simp [quint_1, h])
    · exact fun h => hj' 2 (by simp [quint_2, h])
    · exact fun h => hj' 3 (by simp [quint_3, h])
    · exact fun h => hj' 4 (by simp [quint_4, h])
  · simpa only [hc] using hQe

end Frame09

theorem lex_wrap {a b c d e f g h a' b' c' d' e' f' g' h' : ℝ}
    (hh : a < b ∨ c < d ∨ e < f ∨ g < h) :
    (a < b ∨ (a = b ∧ a' < b')) ∨ (c < d ∨ (c = d ∧ c' < d')) ∨ (e < f ∨ (e = f ∧ e' < f')) ∨
      (g < h ∨ (g = h ∧ g' < h')) := by
  rcases hh with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-! ### The five-pairs depth condition of a five-corner rim -/

/-- The open depth condition "no two non-adjacent corners are both local maxima": for each of
the five non-adjacent pairs, one of the two has a strictly larger neighbour. -/
def Q5p (z : ZMod 5 → ℝ) : Prop :=
  (z 0 < z 4 ∨ z 0 < z 1 ∨ z 2 < z 1 ∨ z 2 < z 3) ∧
  (z 1 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2 ∨ z 3 < z 4) ∧
  (z 2 < z 1 ∨ z 2 < z 3 ∨ z 4 < z 3 ∨ z 4 < z 0) ∧
  (z 3 < z 2 ∨ z 3 < z 4 ∨ z 0 < z 4 ∨ z 0 < z 1) ∧
  (z 4 < z 3 ∨ z 4 < z 0 ∨ z 1 < z 0 ∨ z 1 < z 2)

theorem Q5p_open : IsOpen {z : ZMod 5 → ℝ | Q5p z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  have h4 : ∀ a b c d e f g h : ZMod 5, IsOpen {z : ZMod 5 → ℝ |
      z a < z b ∨ z c < z d ∨ z e < z f ∨ z g < z h} := fun a b c d e f g h =>
    (hlt a b).union ((hlt c d).union ((hlt e f).union (hlt g h)))
  simp only [Q5p, Set.ofPred_and]
  exact (h4 0 4 0 1 2 1 2 3).inter ((h4 1 0 1 2 3 2 3 4).inter ((h4 2 1 2 3 4 3 4 0).inter
    ((h4 3 2 3 4 0 4 0 1).inter (h4 4 3 4 0 1 0 1 2))))

theorem Q5p_smul {z : ZMod 5 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q5p z) : Q5p fun i => a * z i := by
  have key : ∀ {p q : ℝ}, p < q → a * p < a * q := fun h => mul_lt_mul_of_pos_left h ha
  obtain ⟨q0, q1, q2, q3, q4⟩ := h
  have m : ∀ {i1 j1 i2 j2 i3 j3 i4 j4 : ZMod 5},
      (z i1 < z j1 ∨ z i2 < z j2 ∨ z i3 < z j3 ∨ z i4 < z j4) →
      (a * z i1 < a * z j1 ∨ a * z i2 < a * z j2 ∨ a * z i3 < a * z j3 ∨ a * z i4 < a * z j4) := by
    intro i1 j1 i2 j2 i3 j3 i4 j4 h
    rcases h with h | h | h | h
    exacts [Or.inl (key h), Or.inr (Or.inl (key h)), Or.inr (Or.inr (Or.inl (key h))),
      Or.inr (Or.inr (Or.inr (key h)))]
  exact ⟨m q0, m q1, m q2, m q3, m q4⟩

theorem Q5p_shift {z : ZMod 5 → ℝ} (a : ℝ) (h : Q5p z) : Q5p fun i => z i + a := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := h
  have m : ∀ {i1 j1 i2 j2 i3 j3 i4 j4 : ZMod 5},
      (z i1 < z j1 ∨ z i2 < z j2 ∨ z i3 < z j3 ∨ z i4 < z j4) →
      (z i1 + a < z j1 + a ∨ z i2 + a < z j2 + a ∨ z i3 + a < z j3 + a ∨ z i4 + a < z j4 + a) := by
    intro i1 j1 i2 j2 i3 j3 i4 j4 h
    rcases h with h | h | h | h
    exacts [Or.inl (by linarith), Or.inr (Or.inl (by linarith)),
      Or.inr (Or.inr (Or.inl (by linarith))), Or.inr (Or.inr (Or.inr (by linarith)))]
  exact ⟨m q0, m q1, m q2, m q3, m q4⟩

theorem Q5p_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5p z) :
    IsCyclicUnimodal z := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := h
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4] at hi hj <;>
    first
    | rfl
    | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases q0 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases q1 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases q2 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases q3 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
    | (exfalso; rcases q4 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])

theorem Q5p_eventually {z w : ZMod 5 → ℝ}
    (h0 : (z 0 < z 4 ∨ (z 0 = z 4 ∧ w 0 < w 4)) ∨ (z 0 < z 1 ∨ (z 0 = z 1 ∧ w 0 < w 1)) ∨
      (z 2 < z 1 ∨ (z 2 = z 1 ∧ w 2 < w 1)) ∨ (z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3)))
    (h1 : (z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) ∨ (z 1 < z 2 ∨ (z 1 = z 2 ∧ w 1 < w 2)) ∨
      (z 3 < z 2 ∨ (z 3 = z 2 ∧ w 3 < w 2)) ∨ (z 3 < z 4 ∨ (z 3 = z 4 ∧ w 3 < w 4)))
    (h2 : (z 2 < z 1 ∨ (z 2 = z 1 ∧ w 2 < w 1)) ∨ (z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3)) ∨
      (z 4 < z 3 ∨ (z 4 = z 3 ∧ w 4 < w 3)) ∨ (z 4 < z 0 ∨ (z 4 = z 0 ∧ w 4 < w 0)))
    (h3 : (z 3 < z 2 ∨ (z 3 = z 2 ∧ w 3 < w 2)) ∨ (z 3 < z 4 ∨ (z 3 = z 4 ∧ w 3 < w 4)) ∨
      (z 0 < z 4 ∨ (z 0 = z 4 ∧ w 0 < w 4)) ∨ (z 0 < z 1 ∨ (z 0 = z 1 ∧ w 0 < w 1)))
    (h4 : (z 4 < z 3 ∨ (z 4 = z 3 ∧ w 4 < w 3)) ∨ (z 4 < z 0 ∨ (z 4 = z 0 ∧ w 4 < w 0)) ∨
      (z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) ∨ (z 1 < z 2 ∨ (z 1 = z 2 ∧ w 1 < w 2))) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5p fun i => z i + s * w i := by
  have m : ∀ {i1 j1 i2 j2 i3 j3 i4 j4 : ZMod 5},
      ((z i1 < z j1 ∨ (z i1 = z j1 ∧ w i1 < w j1)) ∨ (z i2 < z j2 ∨ (z i2 = z j2 ∧ w i2 < w j2)) ∨
        (z i3 < z j3 ∨ (z i3 = z j3 ∧ w i3 < w j3)) ∨ (z i4 < z j4 ∨ (z i4 = z j4 ∧ w i4 < w j4))) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), (z i1 + s * w i1 < z j1 + s * w j1 ∨
        z i2 + s * w i2 < z j2 + s * w j2 ∨ z i3 + s * w i3 < z j3 + s * w j3 ∨
        z i4 + s * w i4 < z j4 + s * w j4) := by
    intro i1 j1 i2 j2 i3 j3 i4 j4 h
    rcases h with h | h | h | h
    · exact (ev_lt h).mono fun s hs => Or.inl hs
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inl hs)
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inr (Or.inl hs))
    · exact (ev_lt h).mono fun s hs => Or.inr (Or.inr (Or.inr hs))
  filter_upwards [m h0, m h1, m h2, m h3, m h4] with s a b c d e
  exact ⟨a, b, c, d, e⟩

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- The bridge for five-corner rims, with the five-pairs condition `Q5p`. -/
theorem rupert_rim5p (c0 c1 c2 c3 c4 : Fin 7) (P0 P1 P2 P3 P4 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (e4 : F.ptC c4 = P4)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((quint P0 P1 P2 P3 P4 j).sub (quint P0 P1 P2 P3 P4 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → j' ≠ c4 → ∀ i : ZMod 5,
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((F.ptC j').sub (quint P0 P1 P2 P3 P4 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5p fun i => F.GG (quint P0 P1 P2 P3 P4 i) u +
      s * F.GG (quint P0 P1 P2 P3 P4 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quint c0 c1 c2 c3 c4 i) = quint P0 P1 P2 P3 P4 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, e0, e1, e2, e3, e4]
  refine F.rupert_rim (k := 5) (by norm_num) (quint c0 c1 c2 c3 c4) σ hσ u v hu ?_ ?_ Q5p
    Q5p_open (fun z a ha => Q5p_smul ha) (fun z a => Q5p_shift a) ?_
    (fun z hz hq => Q5p_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hc]
    refine hrest j' ?_ ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quint_0, h])
    · exact fun h => hj' 1 (by simp [quint_1, h])
    · exact fun h => hj' 2 (by simp [quint_2, h])
    · exact fun h => hj' 3 (by simp [quint_3, h])
    · exact fun h => hj' 4 (by simp [quint_4, h])
  · simpa only [hc] using hQe

end Frame09

/-! ### 27.32^M: the edge crossing at `m2+ v` (apex `m2+`) -/

section T32
variable {tp hp tm hm sp kp sm km : ℝ}

theorem t32_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (roof : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨0, sp, kp⟩ ⟨tp, 1 - 2 * sp, hp - 2 * kp⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        ((quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ j).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  have htp' : 0 < 1 - tp := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos hkp htp
  have a2 := mul_pos hhp hsp
  have a3 := mul_pos hkp htp'
  have a4 := mul_pos hhp hsp'
  have a5 := mul_pos htp hhp
  have a6 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t32_rest0 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) :
    ∀ i : ZMod 4,
      ST (-1) ⟨0, sp, kp⟩ ⟨tp, 1 - 2 * sp, hp - 2 * kp⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  have htp' : 0 < 1 - tp := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have a1 := mul_pos hkp htp
  have a2 := mul_pos hhp hsp
  have a3 := mul_pos hkp htp'
  have a4 := mul_pos hhp hsp'
  have a5 := mul_pos htp hhp
  have a6 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

/-- `m1-` is strictly inside the shadow (needs `c+ > b-`). -/
theorem t32_rest4 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm)
    (H32 : hm * sp < kp * (1 - tm)) :
    ∀ i : ZMod 4,
      ST (-1) ⟨0, sp, kp⟩ ⟨tp, 1 - 2 * sp, hp - 2 * kp⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  have htp' : 0 < 1 - tp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hkp htm
  have a2 := mul_pos hhm hsp
  have a3 := mul_pos hkp htp
  have a4 := mul_pos hhp hsp
  have a5 := mul_pos hsp hhp
  have a6 := mul_pos hsp hhm
  have a7 := mul_pos hhm htp
  have a8 := mul_pos hhp htm
  have a9 := mul_pos hsp (mul_pos htp' hhm)
  have a10 := mul_pos hsp (mul_pos htm' hhp)
  have a11 := mul_pos hsp (mul_pos htp hhm)
  have a12 := mul_pos hsp (mul_pos htm hhp)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

/-- `m2-` lies on the side `[m2+, xb]` of the shadow (the face `0256` is seen edge-on). -/
theorem t32_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (hy6 : kp * sm + sp * km < kp) :
    ∀ i : ZMod 4,
      ST (-1) ⟨0, sp, kp⟩ ⟨tp, 1 - 2 * sp, hp - 2 * kp⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ i)) := by
  have htp' : 0 < 1 - tp := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have hy : 0 < kp - (kp * sm + sp * km) := by linarith
  have a1 := mul_pos htp hy
  have a2 := mul_pos htp' hy
  have a3 := mul_pos hhp hsp
  have a4 := mul_pos htp (mul_pos hsp' hkm)
  have a5 := mul_pos htp (mul_pos hkp hsm')
  have a6 := mul_pos htp' (mul_pos hkp hsm)
  have a7 := mul_pos htp' (mul_pos hsp hkm)
  have a8 := mul_pos htp (mul_pos hkp hsm)
  have a9 := mul_pos htp (mul_pos hsp hkm)
  have a10 := mul_pos hsp hhp
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end T32

theorem B_of_neg {p q r z0 z1 z2 z3 : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p * z1 + (q + r) * z3 - (q + p) * z0 - r * z2 < 0) :
    z1 < z0 ∨ z3 < z0 ∨ z1 < z2 ∨ z3 < z2 := by
  by_contra hc
  push Not at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  nlinarith [mul_nonneg hp.le (sub_nonneg.2 c1), mul_nonneg hq.le (sub_nonneg.2 c2),
    mul_nonneg hr.le (sub_nonneg.2 c4)]

theorem B_lex {z w : ZMod 4 → ℝ} {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p * z 1 + (q + r) * z 3 - (q + p) * z 0 - r * z 2 < 0) :
    (z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) ∨ (z 3 < z 0 ∨ (z 3 = z 0 ∧ w 3 < w 0)) ∨
      (z 1 < z 2 ∨ (z 1 = z 2 ∧ w 1 < w 2)) ∨ (z 3 < z 2 ∨ (z 3 = z 2 ∧ w 3 < w 2)) := by
  rcases B_of_neg hp hq hr h with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem B_of_neg4 {p q r s z0 z1 z2 z3 : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hT : p + q = r + s) (h : p * z1 + q * z3 - r * z2 - s * z0 < 0) :
    z1 < z0 ∨ z3 < z0 ∨ z1 < z2 ∨ z3 < z2 := by
  by_contra hc
  push Not at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  have hq' : q = r + s - p := by linarith
  have iden : p * s * (z1 - z0) + p * r * (z1 - z2) + q * s * (z3 - z0) + q * r * (z3 - z2) =
      (r + s) * (p * z1 + q * z3 - r * z2 - s * z0) := by
    rw [hq']; ring
  have h' : (r + s) * (p * z1 + q * z3 - r * z2 - s * z0) < 0 :=
    mul_neg_of_pos_of_neg (add_pos hr hs) h
  nlinarith [mul_nonneg (mul_pos hp hs).le (sub_nonneg.2 c1),
    mul_nonneg (mul_pos hp hr).le (sub_nonneg.2 c3),
    mul_nonneg (mul_pos hq hs).le (sub_nonneg.2 c2),
    mul_nonneg (mul_pos hq hr).le (sub_nonneg.2 c4)]

theorem B_lex4 {z w : ZMod 4 → ℝ} {p q r s : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) (hT : p + q = r + s) (h : p * z 1 + q * z 3 - r * z 2 - s * z 0 < 0) :
    (z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) ∨ (z 3 < z 0 ∨ (z 3 = z 0 ∧ w 3 < w 0)) ∨
      (z 1 < z 2 ∨ (z 1 = z 2 ∧ w 1 < w 2)) ∨ (z 3 < z 2 ∨ (z 3 = z 2 ∧ w 3 < w 2)) := by
  rcases B_of_neg4 hp hq hr hs hT h with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-! ### The frame-level statements -/

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

lemma fin7_cases (j : Fin 7) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
  revert j; decide

lemma ptC_eq (j : Fin 7) : F.ptC j = ⟨F.cx j, F.cy j, F.cz j⟩ := rfl

lemma roof' : F.S.hp * (1 - F.S.sp) < F.S.kp * (1 - F.S.tp) := by
  have h := F.S.bp_lt_dp
  have e1 := F.S.bp_mul; have e2 := F.S.dp_mul
  have hs := F.S.sp_lt; have ht := F.S.tp_lt
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos (sub_pos.2 ht) (sub_pos.2 hs))]

lemma H32_of (h : F.S.bm < F.S.cp) : F.S.hm * F.S.sp < F.S.kp * (1 - F.S.tm) := by
  have e1 := F.S.bm_mul; have e2 := F.S.cp_mul
  have hs := F.S.sp_pos; have ht := F.S.tm_lt
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos (sub_pos.2 ht) hs)]

lemma hy6_of (h : F.S.bm < F.S.cp) : F.S.kp * F.S.sm + F.S.sp * F.S.km < F.S.kp := by
  have e1 := F.S.km_eq; have e2 := F.S.cp_mul
  have hs := F.S.sp_pos; have hm := F.S.sm_lt
  nlinarith [mul_lt_mul_of_pos_left h (mul_pos hs (sub_pos.2 hm))]

/-- **27.32's `M`-image** (Proposition 27.32, `c+ > d- = b-`): the edge crossing at `m2+ v` with
apex `m2+`; the rim is `(m2+, xb, xa, m1+)`, and the only failure pattern needs
`φ(xa - xb) ≥ 0`, but `φ(xa - xb) = s+ (A12 - A22) < 0`. -/
theorem t32M (hA : F.a12 < F.a22) (h : F.S.bm < F.S.cp) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have H32 := F.H32_of h
  have hy6 := F.hy6_of h
  have p0 : F.ptC 0 = ⟨0, 0, 0⟩ := by simp [ptC_eq, cx, cy, cz]
  have p4 : F.ptC 4 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [ptC_eq, cx, cy, cz]
  have p6 : F.ptC 6 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [ptC_eq, cx, cy, cz]
  refine F.rupert_rim4 2 5 3 1 ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩
    (by simp [ptC_eq, cx, cy, cz]) (by simp [ptC_eq, cx, cy, cz]) (by simp [ptC_eq, cx, cy, cz])
    (by simp [ptC_eq, cx, cy, cz]) (-1) (Or.inr rfl) ⟨0, F.S.sp, F.S.kp⟩
    ⟨F.S.tp, 1 - 2 * F.S.sp, F.S.hp - 2 * F.S.kp⟩ (Or.inr (Or.inl hsp.ne')) ?_ ?_ ?_
  · exact t32_cyc hsp hsp1 htp htp1 hhp hkp roof
  · intro j' h2 h5 h3 h1 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact t32_rest0 hsp hsp1 htp htp1 hhp hkp i
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h3
    · rw [p4]; exact t32_rest4 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm H32 i
    · exact absurd rfl h5
    · rw [p6]; exact t32_rest6 hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm hy6 i
  · have hA22 : 0 < F.a22 := lt_of_lt_of_le F.A12_pos F.A12_le_A22
    have hg := F.g_pos
    have hgg : 0 < F.gg := hg
    set Pq : ZMod 4 → C3 := quad ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ with hPq
    set zz : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨0, F.S.sp, F.S.kp⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨F.S.tp, 1 - 2 * F.S.sp, F.S.hp - 2 * F.S.kp⟩
      with hww
    refine Q4_eventually (z := zz) (w := ww)
      (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      (B_lex (z := zz) (w := ww) (p := F.S.sp * F.S.hp) (q := F.S.kp * (1 - F.S.tp)) (r := F.S.kp * F.S.tp)
        (mul_pos hsp hhp) (mul_pos hkp (by linarith)) (mul_pos hkp htp) ?_)
    · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos hsp (sub_pos.2 hA)]
    · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos (mul_pos hsp hsp) hA22, mul_pos (mul_pos hkp hkp) hgg,
        mul_pos (sub_pos.2 roof) (mul_pos (mul_pos hsp hsp) hA22)]

lemma H31_of (h : F.S.ap < F.S.cp) : F.S.hp * F.S.sp < F.S.kp * F.S.tp := by
  have e1 := F.S.ap_mul; have e2 := F.S.cp_mul
  have hs := F.S.sp_pos; have ht := F.S.tp_pos
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos ht hs)]

lemma Km_eq : F.S.km * (1 - F.S.tm) = (1 - F.S.sm) * F.S.hm := by
  have e := F.S.km_eq; have e1 := F.S.bm_mul
  rw [e]; linear_combination (1 - F.S.sm) * e1

lemma ptC_pts :
    F.ptC 0 = ⟨0, 0, 0⟩ ∧ F.ptC 1 = ⟨F.S.tp, 0, F.S.hp⟩ ∧ F.ptC 2 = ⟨0, F.S.sp, F.S.kp⟩ ∧
    F.ptC 3 = ⟨1, 0, 0⟩ ∧ F.ptC 4 = ⟨F.S.tm, 0, -F.S.hm⟩ ∧ F.ptC 5 = ⟨0, 1, 0⟩ ∧
    F.ptC 6 = ⟨0, F.S.sm, -F.S.km⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [ptC_eq, cx, cy, cz]

/-- **27.31, case II** (`t- < s-`, `a+ < c+`; the edge crossing at `xa xb`, apex `xa`): the rim
`(v, m1-, xa, m2+)` of the folded plane, the tilt `-u₁`. -/
theorem t31II (hA1 : F.a12 ≤ F.a11) (hts : F.S.tm < F.S.sm) (hac : F.S.ap < F.S.cp) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have H31 := F.H31_of hac
  have Km := F.Km_eq
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim4 0 4 3 2 ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p4 p3 p2 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨-1, 0, 0⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t31II_cyc hsp hsp1 htp htp1 hhp hkp htm htm1 hhm
  · intro j' h0 h4 h3 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact t31II_rest1 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof H31 i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · rw [p5]; exact t31II_rest5 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm i
    · rw [p6]; exact t31II_rest6 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm hts Km i
  · set Pq : ZMod 4 → C3 := quad ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      with hPq
    set zz : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨-1, 0, 0⟩ with hww
    have h11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
    rcases lt_or_eq_of_le hA1 with hlt | heq
    · have hd : 0 < F.a11 - F.a12 := sub_pos.2 hlt
      refine Q4_eventually (z := zz) (w := ww) (Or.inl (Or.inl ?_))
        (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
        nlinarith [mul_pos htm hd]
      · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
        nlinarith [mul_pos (sub_pos.2 htm1) hd]
    · -- a right angle at `xa`: the ties are broken by the tilt `-u₁`
      have hz : F.a11 - F.a12 = 0 := by linarith
      refine Q4_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inr ⟨?_, ?_⟩))))
        (Or.inl (Or.inr ⟨?_, ?_⟩))
      · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
        linear_combination (1 - F.S.tm) * hz
      · simp only [hww, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
        nlinarith [mul_pos h11 (sub_pos.2 htm1)]
      · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
        linear_combination F.S.tm * hz
      · simp only [hww, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
        nlinarith [mul_pos h11 htm]

/-- **27.31, case I-A** (`s- < t-`, `a+ < c+`; apex `xb`): the rim `(v, m2-, xb, m2+)`, the tilt
`+u₁`. -/
theorem t31IA (hA2 : F.a12 < F.a22) (hst : F.S.sm < F.S.tm) (hac : F.S.ap < F.S.cp) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have H31 := F.H31_of hac
  have Km := F.Km_eq
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim4 0 6 5 2 ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p6 p5 p2 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨1, 0, 0⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t31IA_cyc hsp hsp1 hkp hsm hsm1 hkm
  · intro j' h0 h6 h5 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact t31IA_rest1 hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm roof H31 i
    · exact absurd rfl h2
    · rw [p3]; exact t31IA_rest3 hsp hsp1 hkp hsm hsm1 hkm i
    · rw [p4]; exact t31IA_rest4 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm hst Km i
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set Pq : ZMod 4 → C3 := quad ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      with hPq
    set zz : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨1, 0, 0⟩ with hww
    have hd : 0 < F.a22 - F.a12 := sub_pos.2 hA2
    refine Q4_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      (Or.inl (Or.inl ?_))
    · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos (sub_pos.2 hsm1) hd]
    · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos hsm hd]

lemma H31'_of (h : F.S.cp < F.S.ap) : F.S.kp * F.S.tp < F.S.hp * F.S.sp := by
  have e1 := F.S.ap_mul; have e2 := F.S.cp_mul
  have hs := F.S.sp_pos; have ht := F.S.tp_pos
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos ht hs)]

/-- **27.31, case I-B** (`s- < t-`, `a+ > c+`; apex `xb`): the rim `(v, m2-, xb, m2+, m1+)`,
the tilt `+u₁`. -/
theorem t31IB (hA1 : F.a12 ≤ F.a11) (hA2 : F.a12 < F.a22) (hst : F.S.sm < F.S.tm)
    (hac : F.S.cp < F.S.ap) : IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have H31 := F.H31'_of hac
  have Km := F.Km_eq
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim5 0 6 5 2 1 ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    ⟨F.S.tp, 0, F.S.hp⟩ p0 p6 p5 p2 p1 1 (Or.inl rfl) ⟨1, -1, 0⟩ ⟨1, 0, 0⟩ (Or.inl one_ne_zero)
    ?_ ?_ ?_
  · exact t31IB_cyc hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm roof H31
  · intro j' h0 h6 h5 h2 h1 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [p3]; exact t31IB_rest3 hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm roof H31 i
    · rw [p4]; exact t31IB_rest4 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm hst Km
        roof H31 i
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set Pq : ZMod 5 → C3 := quint ⟨0, 0, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      ⟨F.S.tp, 0, F.S.hp⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨1, 0, 0⟩ with hww
    have hd1 : 0 ≤ F.a11 - F.a12 := sub_nonneg.2 hA1
    have h11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
    have hd2 : 0 < F.a22 - F.a12 := sub_pos.2 hA2
    refine Q5c_eventually (z := zz) (w := ww) (Or.inl ?_) (Or.inl ?_) (Or.inl ?_) (Or.inl ?_) ?_
    · simp only [hzz, hPq, GG, Gf, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos hsm hd2]
    · simp only [hzz, hPq, GG, Gf, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 hsm1) hd2]
    · simp only [hzz, hPq, GG, Gf, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 hsp1) hd2]
    · simp only [hzz, hPq, GG, Gf, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos hsp hd2, mul_nonneg htp.le hd1]
    · rcases lt_or_eq_of_le hA1 with hlt | heq
      · left
        simp only [hzz, hPq, GG, Gf, quint_0, quint_1, quint_2, quint_3, quint_4]
        nlinarith [mul_pos htp (sub_pos.2 hlt)]
      · right
        have hz : F.a11 - F.a12 = 0 := by linarith
        constructor
        · simp only [hzz, hPq, GG, Gf, quint_0, quint_1, quint_2, quint_3, quint_4]
          linear_combination (-F.S.tp) * hz
        · simp only [hww, hPq, GG, Gf, quint_0, quint_1, quint_2, quint_3, quint_4]
          nlinarith [mul_pos h11 htp]

/-- **Theorem 27.31 for type 09** (off the special positions `t- = s-`, `a+ = c+`). -/
theorem t31 (hA1 : F.a12 ≤ F.a11) (hA2 : F.a12 < F.a22) :
    F.S.tm ≠ F.S.sm → F.S.ap ≠ F.S.cp → (¬ F.S.tm < F.S.sm ∨ ¬ F.S.cp < F.S.ap) →
      IsRupert (Finset.univ.image x) := by
  intro h1 h2 h3
  rcases lt_or_gt_of_ne h1 with hts | hst
  · -- `t- < s-`: then `¬ c+ < a+`
    have hac : F.S.ap < F.S.cp := by
      rcases h3 with h | h
      · exact absurd hts h
      · exact lt_of_le_of_ne (not_lt.mp h) h2
    exact F.t31II hA1 hts hac
  · rcases lt_or_gt_of_ne h2 with hac | hac
    · exact F.t31IA hA2 hst hac
    · exact F.t31IB hA1 hA2 hst hac

lemma A1_of (h : F.S.cm < F.S.dp) : (1 - F.S.sp) * F.S.km < F.S.sm * F.S.kp := by
  have e1 := F.S.cm_mul; have e2 := F.S.dp_mul
  have hs := F.S.sm_pos; have hs1 := F.S.sp_lt
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos hs (sub_pos.2 hs1))]

/-- The pairing `⟨u₁, u₂⟩_G` of the two views of `A^M` (`u₁ = m2+ - xb`, `u₂ = m2+ - xa`). -/
noncomputable def g12 : ℝ :=
  F.a12 * (1 - F.S.sp) - F.a22 * F.S.sp * (1 - F.S.sp) + F.gg * F.S.kp ^ 2

/-- **`A^M`, the test `T1`** (edge crossing at `m2+ xb`): unimodal when `⟨u₁, u₂⟩ > 0`. -/
theorem amT1 (hg : 0 < F.g12) (A1 : F.S.cm < F.S.dp) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have A1' := F.A1_of A1
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  have hg0 : 0 < F.gg := F.g_pos
  refine F.rupert_rim4 0 4 3 2 ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p4 p3 p2 1 (Or.inl rfl) ⟨0, F.S.sp - 1, F.S.kp⟩ ⟨1, -2 * F.S.sp, -2 * F.S.kp⟩
    (Or.inr (Or.inl (by linarith))) ?_ ?_ ?_
  · exact am1_cyc hsp hsp1 hkp htm htm1 hhm
  · intro j' h0 h4 h3 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact am1_rest1 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm roof i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · rw [p5]; exact am1_rest5 hsp hsp1 hkp htm htm1 hhm i
    · rw [p6]; exact am1_rest6 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm A1' i
  · set Pq : ZMod 4 → C3 := quad ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      with hPq
    set zz : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨0, F.S.sp - 1, F.S.kp⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨1, -2 * F.S.sp, -2 * F.S.kp⟩ with hww
    have hc1 : 0 < (1 - F.S.sp) * F.S.hm := mul_pos (sub_pos.2 hsp1) hhm
    have hnu : 0 < F.a22 * (F.S.sp - 1) ^ 2 + F.gg * F.S.kp ^ 2 := by
      have hA22 : 0 < F.a22 := lt_of_lt_of_le F.A12_pos F.A12_le_A22
      have : 0 < (F.S.sp - 1) ^ 2 := by nlinarith
      positivity
    refine Q4_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      (B_lex4 (z := zz) (w := ww) (p := F.S.kp) (q := (1 - F.S.sp) * F.S.hm)
        (r := F.S.tm * F.S.kp) (s := F.S.kp + (1 - F.S.sp) * F.S.hm - F.S.tm * F.S.kp)
        hkp hc1 (mul_pos htm hkp) (by nlinarith [mul_pos (sub_pos.2 htm1) hkp]) (by ring) ?_)
    · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3, g12] at hg ⊢
      nlinarith
    · simp only [hzz, hPq, GG, Gf, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos hsp (mul_pos hhm hnu)]

lemma GG_self_pos (p : C3) (hp : p.x ≠ 0 ∨ p.y ≠ 0 ∨ p.z ≠ 0) : 0 < F.GG p p := by
  rw [← F.inner_fvC]
  apply real_inner_self_pos.mpr
  intro h0
  have := F.coord_zero (a := p.x) (b := p.y) (c := p.z) (by exact h0)
  rcases hp with h | h | h
  · exact h this.1
  · exact h this.2.1
  · exact h this.2.2

lemma A2_of (h : F.S.hm < F.S.tm * (F.S.kp + F.S.sp * F.S.cm)) :
    F.S.hm * F.S.sm < F.S.tm * F.S.kp * F.S.sm + F.S.tm * F.S.sp * F.S.km := by
  have e := F.S.cm_mul
  have hs := F.S.sm_pos
  have := mul_lt_mul_of_pos_right h hs
  have e' : F.S.tm * (F.S.kp + F.S.sp * F.S.cm) * F.S.sm =
      F.S.tm * F.S.kp * F.S.sm + F.S.tm * F.S.sp * F.S.km := by rw [← e]; ring
  linarith

lemma A3_of (h : F.S.hm < F.S.kp * F.S.tm + F.S.dm * (1 - F.S.sp * F.S.tm)) :
    F.S.hm * (1 - F.S.sm) < F.S.kp * F.S.tm * (1 - F.S.sm) + F.S.km * (1 - F.S.sp * F.S.tm) := by
  have e1 := F.S.dm_eq; have e2 := F.S.km_eq
  have hs := F.S.sm_lt
  have := mul_lt_mul_of_pos_right h (sub_pos.2 hs)
  have e3 : F.S.dm * (1 - F.S.sm) = F.S.km := by rw [e1, e2]
  have e' : (F.S.kp * F.S.tm + F.S.dm * (1 - F.S.sp * F.S.tm)) * (1 - F.S.sm) =
      F.S.kp * F.S.tm * (1 - F.S.sm) + F.S.km * (1 - F.S.sp * F.S.tm) := by rw [← e3]; ring
  linarith

/-- **`A^M`, the test `T2`** (edge crossing at `m2+ xa`): unimodal when `⟨u₁, u₂⟩ ≤ 0`. -/
theorem amT2 (hg : F.g12 ≤ 0) (A1 : F.S.cm < F.S.dp)
    (A2 : F.S.hm < F.S.tm * (F.S.kp + F.S.sp * F.S.cm))
    (A3 : F.S.hm < F.S.kp * F.S.tm + F.S.dm * (1 - F.S.sp * F.S.tm)) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have roof := F.roof'
  have A1' := F.A1_of A1
  have A2' := F.A2_of A2
  have A3' := F.A3_of A3
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  have hgg : 0 < F.gg := F.g_pos
  -- the tilt parameter
  set nu : ℝ := F.GG ⟨0, F.S.sp - 1, F.S.kp⟩ ⟨0, F.S.sp - 1, F.S.kp⟩ with hnu
  set X : ℝ := F.GG ⟨0, F.S.sp - 1, F.S.kp⟩ ⟨F.S.tp, -F.S.sp, F.S.hp - F.S.kp⟩ with hX
  have hnu0 : 0 < nu := F.GG_self_pos _ (Or.inr (Or.inl (by linarith)))
  set b : ℝ := nu / (2 * (|X| + 1)) with hbdef
  have hb : 0 < b := by positivity
  have hbX : b * X < nu := by
    have h1 : b * X ≤ b * |X| := mul_le_mul_of_nonneg_left (le_abs_self X) hb.le
    have h2 : b * |X| < nu := by
      rw [hbdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg X]
    linarith
  refine F.rupert_rim5p 2 1 0 6 5 ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, 0, 0⟩
    ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ p2 p1 p0 p6 p5 (-1) (Or.inr rfl) ⟨-1, F.S.sp, F.S.kp⟩
    ⟨b * F.S.tp, (1 - F.S.sp) - b * F.S.sp, -F.S.kp + b * (F.S.hp - F.S.kp)⟩
    (Or.inr (Or.inl (by linarith))) ?_ ?_ ?_
  · exact am2_cyc hb hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm roof
  · intro j' h2 h1 h0 h6 h5 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [p3]; exact am2_rest3 hb hsp hsp1 htp htp1 hhp hkp hsm hsm1 hkm roof i
    · rw [p4]; exact am2_rest4 hb hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm roof A2' A3' i
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set Pq : ZMod 5 → C3 := quint ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, 0, 0⟩
      ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ with hPq
    set u2c : C3 := ⟨-1, F.S.sp, F.S.kp⟩ with hu2c
    set vt : C3 := ⟨b * F.S.tp, (1 - F.S.sp) - b * F.S.sp, -F.S.kp + b * (F.S.hp - F.S.kp)⟩
      with hvt
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) u2c with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) vt with hww
    have hc0 : 0 < F.GG u2c u2c := F.GG_self_pos _ (Or.inl (by simp [hu2c]))
    have hc3 : 0 < F.gg * F.S.kp := mul_pos hgg hkp
    have e0 : zz 0 = (F.a22 * F.S.sp - F.a12) * F.S.sp + (F.gg * F.S.kp) * F.S.kp := by
      simp only [hzz, hPq, hu2c, GG, Gf, quint_0]; ring
    have e1 : zz 1 = -(F.GG u2c u2c) * F.S.tp + (F.a22 * F.S.sp - F.a12) * F.S.sp * F.S.tp +
        (F.gg * F.S.kp) * (F.S.hp + F.S.kp * F.S.tp) := by
      simp only [hzz, hPq, hu2c, GG, Gf, quint_1]; ring
    have e2 : zz 2 = 0 := by
      simp only [hzz, hPq, hu2c, GG, Gf, quint_2]; ring
    have e3 : zz 3 = (F.a22 * F.S.sp - F.a12) * F.S.sm - (F.gg * F.S.kp) * F.S.km := by
      simp only [hzz, hPq, hu2c, GG, Gf, quint_3]; ring
    have e4 : zz 4 = (F.a22 * F.S.sp - F.a12) := by
      simp only [hzz, hPq, hu2c, GG, Gf, quint_4]; ring
    have hz04 : zz 0 < zz 4 ∨ (zz 0 = zz 4 ∧ ww 0 < ww 4) := by
      have hdiff : zz 4 - zz 0 = -F.g12 := by
        simp only [hzz, hPq, hu2c, GG, Gf, quint_0, quint_4, g12]; ring
      have hw : ww 4 - ww 0 = nu - b * X := by
        simp only [hww, hPq, hvt, hnu, hX, GG, Gf, quint_0, quint_4]; ring
      rcases lt_or_eq_of_le hg with h | h
      · left; linarith
      · right; constructor
        · linarith
        · linarith
    refine Q5p_eventually (z := zz) (w := ww) (Or.inl hz04) ?_ ?_ (Or.inr (Or.inr (Or.inl hz04))) ?_
    · exact lex_wrap (am2_pair13 hc0 htp htp1 hhp hsm1 hsm hkm e0 e1 e2 e3 e4)
    · exact lex_wrap (am2_pair24 hc3 hsm hsm1 hkm hsp hsp1 hkp A1' e0 e1 e2 e3 e4 hc0 htp)
    · exact lex_wrap (am2_pair14 hc0 htp htp1 hhp hsp hsp1 roof e0 e1 e2 e3 e4)

/-- **Corollary 27.29, row `A^M`** (type 09): at the frame's metric, the pair of tests at `m2+`
(`T1` at `m2+ xb`, `T2` at `m2+ xa`) — one of them is unimodal according to the sign of
`⟨u₁, u₂⟩_G`.  No acuteness is needed. -/
theorem amM (h : F.S.AM) : IsRupert (Finset.univ.image x) := by
  obtain ⟨A1, A2, A3⟩ := h
  by_cases hg : 0 < F.g12
  · exact F.amT1 hg A1
  · exact F.amT2 (not_lt.mp hg) A1 A2 A3

/-- **The three crossing tests of type 09's case (c)**, at the frame's metric.  The hypothesis
`A12 < A22` is the strict acuteness of the far angle at `xb` (the triangle `v xa xb` has a right
angle at `xb` iff `A12 = A22`); it is used by 27.32^M and by 27.31 (cases I-A, I-B), and is
exactly where these two tests stop being unimodal (see the module docstring). -/
theorem tests09 (hA : F.a12 < F.a22) : Tests09 F where
  am := fun h => F.amM h
  t31 := fun h1 h2 h3 => F.t31 F.A12_le_A11 hA h1 h2 h3
  t32 := fun h1 h2 => F.t32M hA (lt_of_le_of_ne (not_lt.mp h2) h1.symm)

/-- **In the frame, off the special positions, either `V` is Rupert or the five conditions of
Theorem 27.48 hold** (27.58), now without the hypothesis `T`, for a frame whose far angle at
`xb` is acute. -/
theorem rupert_or_27_48' (hx : Function.Injective x) (hA : F.a12 < F.a22)
    (sp0 : F.S.tm ≠ F.S.sm) (sp4 : F.S.ap ≠ F.S.cp) (sp5 : F.S.cp ≠ F.S.bm)
    (sp1 : F.S.am ≠ F.S.bp) (sp2 : F.S.am ≠ F.S.dp) (sp3 : F.S.bp ≠ F.S.sp * F.S.A2) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.tm < F.S.sm ∧ F.S.bp < F.S.am ∧ F.S.am < F.S.dp ∧ F.S.cm < F.S.dp ∧
        F.S.bp < F.S.sp * F.S.A2) :=
  F.rupert_or_27_48 hx (F.tests09 hA) sp0 sp4 sp5 sp1 sp2 sp3

end Frame09

end Minimality.CaseC09

end
