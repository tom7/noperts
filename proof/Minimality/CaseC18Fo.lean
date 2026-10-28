module

public import Minimality.CaseC18Bridge
public import Minimality.FirstOrder

@[expose] public section

/-!
# Type 18, acute case (c): the first-order (spin) bridge in frame coordinates

All PROVED.  Notes: `nopert229/out/bottleneck/sp18d/handoff_lean.md`.  Paper: `FEWER-FACES-PROOFS.md` "## 38."

`isRupert_of_tiltCert` (`Tilt.lean`) is Lemma 1 in the *frame-free local-certificate form*: for
each vertex either a corner whose velocity points into the (convex) angle it makes with two other
vertices, or a vertex strictly inside a triangle of three others, all read as determinants
`det3 a b w` at the view `w`.  This file transports it to frame coordinates `C3` (`Dc`), for a
first-order motion `(ω, τ)` *with spin*: `ω = fvC ωc`, and the velocity of the frame point `p` is
the frame vector `V p = crossC ωc p + m` (`cross (fvC ωc) (fvC p) = fvC (crossC ωc p)`,
`τ = fvC m - cross ω base`).  No rim (hexagon) bookkeeping is needed: the certificate is local,
and every test is affine in the tilt parameter `ε` of the view `u_ε = u + ε d`.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-- Sum of frame vectors. -/
def _root_.Minimality.CaseC09.C3.add (a b : C3) : C3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/-- The tilted view `u + ε d`. -/
def _root_.Minimality.CaseC09.C3.tilt (u d : C3) (ε : ℝ) : C3 := ⟨u.x + ε * d.x, u.y + ε * d.y, u.z + ε * d.z⟩

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-! ### Group F0: the cross product in frame coordinates -/

theorem gg_pos : 0 < F.gg := by
  have h := F.GG_self_pos ⟨0, 0, 1⟩ (Or.inr (Or.inr one_ne_zero))
  simpa [GG, Gf] using h

/-- The Gram determinant of `u₁, u₂` (positive by independence). -/
theorem gram_pos : 0 < F.a11 * F.a22 - F.a12 ^ 2 := by
  have h1 : 0 < F.a11 := by
    have h := F.GG_self_pos ⟨1, 0, 0⟩ (Or.inl one_ne_zero)
    simpa [GG, Gf] using h
  have h2 := F.GG_self_pos ⟨-F.a12, F.a11, 0⟩ (Or.inr (Or.inl h1.ne'))
  have h3 : F.GG ⟨-F.a12, F.a11, 0⟩ ⟨-F.a12, F.a11, 0⟩ = F.a11 * (F.a11 * F.a22 - F.a12 ^ 2) := by
    simp only [GG, Gf]; ring
  rw [h3] at h2
  exact (mul_pos_iff_of_pos_left h1).mp h2

lemma fvC_add (a b : C3) : F.fvC (a.add b) = F.fvC a + F.fvC b := by
  simp only [fvC, C3.add]; module

lemma fvC_sub (a b : C3) : F.fvC (a.sub b) = F.fvC a - F.fvC b := by
  simp only [fvC, C3.sub]; module

/-- Frame coordinates of `ω × p` for `ω = fvC ωc`, `p` given in frame coordinates:
`κ · G⁻¹ (ωc × p)` with `G = diag-block(a11 a12; a12 a22, gg)` and `κ = det (u₁, u₂, e)`. -/
noncomputable def crossC (ωc p : C3) : C3 :=
  ⟨F.kap * (F.a22 * (ωc.y * p.z - ωc.z * p.y) - F.a12 * (ωc.z * p.x - ωc.x * p.z)) /
      (F.a11 * F.a22 - F.a12 ^ 2),
   F.kap * (F.a11 * (ωc.z * p.x - ωc.x * p.z) - F.a12 * (ωc.y * p.z - ωc.z * p.y)) /
      (F.a11 * F.a22 - F.a12 ^ 2),
   F.kap * (ωc.x * p.y - ωc.y * p.x) / F.gg⟩

/-- Proof: both sides have the same inner product with every `fvC r`
(`⟪cross a b, c⟫ = det3 a b c`, `det3_fvC`, `inner_fvC`); `Frame7.gram_pos`, `gg_pos`. -/
theorem cross_fvC (ωc p : C3) : cross (F.fvC ωc) (F.fvC p) = F.fvC (F.crossC ωc p) := by
  have hΔ := F.gram_pos.ne'
  have hg := F.gg_pos.ne'
  have key : ∀ r : C3, ⟪cross (F.fvC ωc) (F.fvC p) - F.fvC (F.crossC ωc p), F.fvC r⟫ = 0 := by
    intro r
    rw [inner_sub_left, F.inner_fvC]
    have h : ⟪cross (F.fvC ωc) (F.fvC p), F.fvC r⟫ = F.kap * Dc ωc p r := F.det3_fvC ωc p r
    rw [h]
    simp only [GG, Gf, crossC, Dc]
    field_simp
    ring
  obtain ⟨q, hq⟩ := F.decomp (cross (F.fvC ωc) (F.fvC p) - F.fvC (F.crossC ωc p))
  have h := key q
  rw [← hq] at h
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h)

/-- The velocity (frame coordinates) of the frame point `p` under the motion `(ωc, m)`. -/
noncomputable def velC (ωc m p : C3) : C3 := (F.crossC ωc p).add m

/-! ### Group F1: the local first-order certificate and the bridge -/

/-- The local certificate at the vertex `j` (view `u`, orientation sign `σ`, motion `(ωc, m)`):
`j` is a corner whose velocity points strictly into the convex angle with the neighbours `j0`
(before) and `j1` (after), or `j` lies strictly inside the triangle `a b c`.  Frame form of
`TiltCert`; `σ = ±1` is the sign of `κ`-orientation of the screen (as in `ST`). -/
def FoCert (σ : ℝ) (u ωc m : C3) (j : Fin 7) : Prop :=
  (∃ j0 j1 : Fin 7,
      0 < σ * Dc ((F.ptC j1).sub (F.ptC j)) ((F.ptC j0).sub (F.ptC j)) u ∧
      0 < σ * Dc ((F.ptC j1).sub (F.ptC j)) (F.velC ωc m (F.ptC j)) u ∧
      0 < σ * Dc ((F.ptC j).sub (F.ptC j0)) (F.velC ωc m (F.ptC j)) u) ∨
  (∃ a b c : Fin 7,
      0 < σ * Dc ((F.ptC b).sub (F.ptC a)) ((F.ptC c).sub (F.ptC a)) u ∧
      0 < σ * Dc ((F.ptC b).sub (F.ptC a)) ((F.ptC j).sub (F.ptC a)) u ∧
      0 < σ * Dc ((F.ptC c).sub (F.ptC b)) ((F.ptC j).sub (F.ptC b)) u ∧
      0 < σ * Dc ((F.ptC a).sub (F.ptC c)) ((F.ptC j).sub (F.ptC c)) u)

/-- **The bridge, fixed view.**  A frame vector `u ≠ 0`, `σ = ±1`, a motion `(ωc, m)` (spin
`ω = fvC ωc`, translation `fvC m` at the base point) and a local certificate at every vertex
give a passage.  Proof: `isRupert_of_tiltCert` with `w = ε • fvC u` (`ε = sign (σ κ)` as in
`rupert_rim`), `ω = ε' • fvC ωc`, `τ = fvC m - cross ω base`; `det3_fvC`, `cross_fvC`. -/
theorem rupert_of_foCert (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u ωc m : C3)
    (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0) (h : ∀ j, F.FoCert σ u ωc m j) :
    IsRupert (Finset.univ.image x) := by
  classical
  have hκ := F.kap_ne
  set t := σ * F.kap with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hconv : ∀ a b : C3, 0 < σ * Dc a b u →
      0 < det3 (F.fvC a) (F.fvC b) (ε • F.fvC u) := by
    intro a b hab
    rw [det3_smul_right, F.det3_fvC]
    refine sgn_pos t _ ?_
    have hk2 : 0 < F.kap ^ 2 := by positivity
    have := mul_pos hk2 hab
    calc 0 < F.kap ^ 2 * (σ * Dc a b u) := this
      _ = t * (F.kap * Dc a b u) := by rw [ht]; ring
  have hu0 : F.fvC u ≠ 0 := by
    intro h0
    have := F.coord_zero (a := u.x) (b := u.y) (c := u.z) (by exact h0)
    rcases hu with h | h | h
    · exact h this.1
    · exact h this.2.1
    · exact h this.2.2
  have hu' : ε • F.fvC u ≠ 0 := by
    intro h0
    rcases hεs with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hu0 h0
  refine isRupert_of_tiltCert _ (ε • F.fvC u) hu' (F.fvC ωc)
    (F.fvC m - cross (F.fvC ωc) F.base) ?_
  intro y hy
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
  have hv : cross (F.fvC ωc) (x j) + (F.fvC m - cross (F.fvC ωc) F.base) =
      F.fvC (F.velC ωc m (F.ptC j)) := by
    rw [velC, F.fvC_add, ← F.cross_fvC, F.x_eq' j]
    have e : ∀ a b c : ℝ³, cross a (b + c) = cross a b + cross a c := by
      intro a b c
      ext i; fin_cases i <;> simp [cross] <;> ring
    rw [e]; abel
  have hm : ∀ i : Fin 7, x i ∈ Finset.univ.image x := fun i =>
    Finset.mem_image_of_mem x (Finset.mem_univ _)
  rcases h j with ⟨j0, j1, h0, h1, h2⟩ | ⟨a, b, c, h0, h1, h2, h3⟩
  · left
    refine ⟨x j0, hm _, x j1, hm _, ?_, ?_, ?_⟩
    · rw [F.x_sub, F.x_sub]; exact hconv _ _ h0
    · rw [F.x_sub, hv]; exact hconv _ _ h1
    · rw [F.x_sub, hv]; exact hconv _ _ h2
  · right
    refine ⟨x a, hm _, x b, hm _, x c, hm _, ?_, ?_, ?_, ?_⟩
    · rw [F.x_sub, F.x_sub]; exact hconv _ _ h0
    · rw [F.x_sub, F.x_sub]; exact hconv _ _ h1
    · rw [F.x_sub, F.x_sub]; exact hconv _ _ h2
    · rw [F.x_sub, F.x_sub]; exact hconv _ _ h3

/-- **The bridge, tilted view.**  The certificate at `u + ε d` for all small `ε > 0` (each test
is `A + ε B` with `A, B` constants: `eventually_pos_affine` from `Tilt.lean`). -/
theorem rupert_of_foCert_eventually (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u d ωc m : C3)
    (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, F.FoCert σ (C3.tilt u d ε) ωc m j) :
    IsRupert (Finset.univ.image x) := by
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (C3.tilt u d ε).x ≠ 0 ∨ (C3.tilt u d ε).y ≠ 0 ∨ (C3.tilt u d ε).z ≠ 0 := by
    rcases hu with hx | hy | hz
    · have : ∀ᶠ ε in 𝓝 (0 : ℝ), u.x + ε * d.x ≠ 0 :=
        (by fun_prop : Continuous fun ε : ℝ => u.x + ε * d.x).continuousAt.eventually_ne
          (by simpa using hx)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun ε h => Or.inl h
    · have : ∀ᶠ ε in 𝓝 (0 : ℝ), u.y + ε * d.y ≠ 0 :=
        (by fun_prop : Continuous fun ε : ℝ => u.y + ε * d.y).continuousAt.eventually_ne
          (by simpa using hy)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun ε h => Or.inr (Or.inl h)
    · have : ∀ᶠ ε in 𝓝 (0 : ℝ), u.z + ε * d.z ≠ 0 :=
        (by fun_prop : Continuous fun ε : ℝ => u.z + ε * d.z).continuousAt.eventually_ne
          (by simpa using hz)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun ε h => Or.inr (Or.inr h)
  obtain ⟨ε, hε, hne'⟩ := (h.and hne).exists
  exact F.rupert_of_foCert σ hσ _ ωc m hne' hε

/-! ### Group F2: rescaling `e` -/

/-- Replace `e` by `c • e` (`c > 0`): the same seven points, `z`-coordinates divided by `c`,
`gg` multiplied by `c ^ 2`, `a11, a12, a22` unchanged.  Used to normalise `h = 1` on the family E. -/
noncomputable def scaleE (c : ℝ) (hc : 0 < c) : Frame7 x where
  base := F.base
  u1 := F.u1
  u2 := F.u2
  e := c • F.e
  indep := by
    have h := Fintype.linearIndependent_iff.mp F.indep
    refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have h' := h ![g 0, g 1, g 2 * c] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← hg]; module)
    have a0 := h' 0
    have a1 := h' 1
    have a2 := h' 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at a0 a1 a2
    intro i
    fin_cases i
    · exact a0
    · exact a1
    · exact (mul_eq_zero.mp a2).resolve_right hc.ne'
  inner_u1_e := by rw [real_inner_smul_right, F.inner_u1_e, mul_zero]
  inner_u2_e := by rw [real_inner_smul_right, F.inner_u2_e, mul_zero]
  ptC := fun j => ⟨(F.ptC j).x, (F.ptC j).y, (F.ptC j).z / c⟩
  x_eq := fun j => by
    rw [F.x_eq j, smul_smul, div_mul_cancel₀ _ hc.ne']

theorem scaleE_ptC (c : ℝ) (hc : 0 < c) (j : Fin 7) :
    (F.scaleE c hc).ptC j = ⟨(F.ptC j).x, (F.ptC j).y, (F.ptC j).z / c⟩ := rfl
theorem scaleE_a11 (c : ℝ) (hc : 0 < c) : (F.scaleE c hc).a11 = F.a11 := rfl
theorem scaleE_a12 (c : ℝ) (hc : 0 < c) : (F.scaleE c hc).a12 = F.a12 := rfl
theorem scaleE_a22 (c : ℝ) (hc : 0 < c) : (F.scaleE c hc).a22 = F.a22 := rfl
theorem scaleE_gg (c : ℝ) (hc : 0 < c) : (F.scaleE c hc).gg = c ^ 2 * F.gg := by
  show ⟪c • F.e, c • F.e⟫ = c ^ 2 * ⟪F.e, F.e⟫
  rw [real_inner_smul_left, real_inner_smul_right]; ring

end Frame7

end Minimality.CaseC18

end
