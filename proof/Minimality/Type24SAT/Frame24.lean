module

public import Minimality.Type24SAT.Sem24

@[expose] public section

/-!
# Type 24, SAT bridge layer 3: the WLOG affine frame

For a configuration `x` with an invertible matrix `M = [x_ia - x_0, x_ib - x_0, SG (x_ap - x_0)]` (`SG = ±1`),
the frame coordinates `U i = M⁻¹ (x_i - x_0)` satisfy `x_i = x_0 + M U_i`, and every literal value is a
positive power of `det M` times the value at `U`: `br lv mv fc` scale by `det M`, `nv` by `det M ^ 2`, and the
`kv` literals on a facet whose points have `U`-height 0 by `|c1 × c2|²` (a positive number).  The identities are
`ring` once per literal kind over any commutative ring (the cofactor matrix `capp`), not per atom.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality

/-- A matrix by columns. -/
structure Mat3 (R : Type) where
  c1 : V3 R
  c2 : V3 R
  c3 : V3 R

theorem V3.ext' {R : Type} {a b : V3 R} (h1 : a.x = b.x) (h2 : a.y = b.y) (h3 : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

/-- Sum. -/
def V3.add {R : Type} [CommRing R] (a b : V3 R) : V3 R := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

section Alg
variable {R : Type} [CommRing R]

/-- `M u`. -/
def Mat3.app (M : Mat3 R) (u : V3 R) : V3 R :=
  ⟨u.x * M.c1.x + u.y * M.c2.x + u.z * M.c3.x, u.x * M.c1.y + u.y * M.c2.y + u.z * M.c3.y,
    u.x * M.c1.z + u.y * M.c2.z + u.z * M.c3.z⟩
/-- The cofactor matrix applied: `cof M n`, with `cross (M a) (M b) = cof M (cross a b)`. -/
def Mat3.capp (M : Mat3 R) (n : V3 R) : V3 R :=
  V3.add (V3.add (V3.smul n.x (V3.cr M.c2 M.c3)) (V3.smul n.y (V3.cr M.c3 M.c1))) (V3.smul n.z (V3.cr M.c1 M.c2))
/-- Determinant. -/
def Mat3.det (M : Mat3 R) : R := V3.det M.c1 M.c2 M.c3
/-- The affine image of a frame configuration. -/
def aff (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (i : Nat) : V3 R := V3.add x0 (M.app (U i))

theorem sub_aff (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (a b : Nat) :
    V3.sub (aff x0 M U a) (aff x0 M U b) = M.app (V3.sub (U a) (U b)) := by
  apply V3.ext' <;> simp only [aff, V3.add, V3.sub, Mat3.app] <;> ring

theorem det_app (M : Mat3 R) (a b c : V3 R) :
    V3.det (M.app a) (M.app b) (M.app c) = M.det * V3.det a b c := by
  simp only [V3.det, V3.dot, V3.cr, Mat3.app, Mat3.det]; ring

theorem cr_app (M : Mat3 R) (a b : V3 R) : V3.cr (M.app a) (M.app b) = M.capp (V3.cr a b) := by
  apply V3.ext' <;> simp only [V3.cr, Mat3.app, Mat3.capp, V3.add, V3.smul] <;> ring

theorem dot_capp_app (M : Mat3 R) (n d : V3 R) : V3.dot (M.capp n) (M.app d) = M.det * V3.dot n d := by
  simp only [V3.dot, V3.cr, Mat3.app, Mat3.capp, V3.add, V3.smul, Mat3.det, V3.det]; ring

theorem det_capp (M : Mat3 R) (a b c : V3 R) :
    V3.det (M.capp a) (M.capp b) (M.capp c) = M.det ^ 2 * V3.det a b c := by
  simp only [V3.det, V3.dot, V3.cr, Mat3.capp, V3.add, V3.smul, Mat3.det]; ring

theorem dot_capp_capp (M : Mat3 R) (p n : V3 R) (hp1 : p.x = 0) (hp2 : p.y = 0) (hn1 : n.x = 0) (hn2 : n.y = 0) :
    V3.dot (M.capp p) (M.capp n) = V3.dot (V3.cr M.c1 M.c2) (V3.cr M.c1 M.c2) * V3.dot p n := by
  simp only [V3.dot, Mat3.capp, V3.add, V3.smul, hp1, hp2, hn1, hn2]; ring

theorem smul_capp (M : Mat3 R) (k : R) (n : V3 R) : V3.smul k (M.capp n) = M.capp (V3.smul k n) := by
  apply V3.ext' <;> simp only [Mat3.capp, V3.add, V3.smul] <;> ring

theorem nrm3_aff (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (t : Nat) :
    nrm3 (aff x0 M U) t = M.capp (nrm3 U t) := by
  simp only [nrm3, sub_aff, cr_app, smul_capp]

theorem val3_aff_br (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (a b c d : Nat) :
    val3 (aff x0 M U) (.br a b c d) = M.det * val3 U (.br a b c d) := by
  simp only [val3, sub_aff, det_app]
theorem val3_aff_lv (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (a b c d e : Nat) :
    val3 (aff x0 M U) (.lv a b c d e) = M.det * val3 U (.lv a b c d e) := by
  simp only [val3, sub_aff, det_app]
theorem val3_aff_mv (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (a b c d e f : Nat) :
    val3 (aff x0 M U) (.mv a b c d e f) = M.det * val3 U (.mv a b c d e f) := by
  simp only [val3, sub_aff, det_app]
theorem val3_aff_fc (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (t p q : Nat) :
    val3 (aff x0 M U) (.fc t p q) = M.det * val3 U (.fc t p q) := by
  simp only [val3, sub_aff, nrm3_aff, dot_capp_app]
theorem val3_aff_nv (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (r s t : Nat) :
    val3 (aff x0 M U) (.nv r s t) = M.det ^ 2 * val3 U (.nv r s t) := by
  simp only [val3, nrm3_aff, det_capp]
theorem cv3_aff (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (t v : Nat) :
    cv3 (aff x0 M U) t v = M.det * cv3 U t v := by
  simp only [cv3, sub_aff, nrm3_aff, dot_capp_app]; ring

/-- `kv` on a facet whose frame points all have height 0. -/
theorem val3_aff_kv (x0 : V3 R) (M : Mat3 R) (U : Nat → V3 R) (t a b c d : Nat)
    (ha : (U a).z = 0) (hb : (U b).z = 0) (hc : (U c).z = 0) (hd : (U d).z = 0)
    (h1 : (U (fa t)).z = 0) (h2 : (U (fb t)).z = 0) (h3 : (U (fc' t)).z = 0) :
    val3 (aff x0 M U) (.kv t a b c d) =
      V3.dot (V3.cr M.c1 M.c2) (V3.cr M.c1 M.c2) * val3 U (.kv t a b c d) := by
  have hn : (nrm3 U t).x = 0 ∧ (nrm3 U t).y = 0 := by
    simp only [nrm3, V3.smul, V3.cr, V3.sub, h1, h2, h3]; constructor <;> ring
  have hp : (V3.cr (V3.sub (U a) (U b)) (V3.sub (U c) (U d))).x = 0 ∧
      (V3.cr (V3.sub (U a) (U b)) (V3.sub (U c) (U d))).y = 0 := by
    simp only [V3.cr, V3.sub, ha, hb, hc, hd]; constructor <;> ring
  simp only [val3, sub_aff, cr_app, nrm3_aff]
  exact dot_capp_capp M _ _ hp.1 hp.2 hn.1 hn.2

end Alg

/-! ### The inverse and the real frame -/

/-- `M⁻¹ v` (Cramer). -/
noncomputable def minv (M : Mat3 ℝ) (v : V3 ℝ) : V3 ℝ :=
  ⟨V3.dot v (V3.cr M.c2 M.c3) / M.det, V3.dot v (V3.cr M.c3 M.c1) / M.det, V3.dot v (V3.cr M.c1 M.c2) / M.det⟩

theorem app_minv (M : Mat3 ℝ) (hD : M.det ≠ 0) (v : V3 ℝ) : M.app (minv M v) = v := by
  apply V3.ext' <;> simp only [Mat3.app, minv] <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div, div_eq_iff hD] <;>
    simp only [V3.dot, V3.cr, Mat3.det, V3.det] <;> ring

theorem minv_c1 (M : Mat3 ℝ) (hD : M.det ≠ 0) : minv M M.c1 = ⟨1, 0, 0⟩ := by
  apply V3.ext' <;> simp only [minv] <;> (first | rw [div_eq_iff hD] | skip) <;>
    simp only [V3.dot, V3.cr, Mat3.det, V3.det] <;> ring
theorem minv_c2 (M : Mat3 ℝ) (hD : M.det ≠ 0) : minv M M.c2 = ⟨0, 1, 0⟩ := by
  apply V3.ext' <;> simp only [minv] <;> (first | rw [div_eq_iff hD] | skip) <;>
    simp only [V3.dot, V3.cr, Mat3.det, V3.det] <;> ring
theorem minv_c3 (M : Mat3 ℝ) (hD : M.det ≠ 0) : minv M M.c3 = ⟨0, 0, 1⟩ := by
  apply V3.ext' <;> simp only [minv] <;> (first | rw [div_eq_iff hD] | skip) <;>
    simp only [V3.dot, V3.cr, Mat3.det, V3.det] <;> ring
theorem minv_zero (M : Mat3 ℝ) : minv M ⟨0, 0, 0⟩ = ⟨0, 0, 0⟩ := by
  apply V3.ext' <;> simp [minv, V3.dot]
theorem minv_smul (M : Mat3 ℝ) (k : ℝ) (v : V3 ℝ) : minv M (V3.smul k v) = V3.smul k (minv M v) := by
  apply V3.ext' <;> simp only [minv, V3.smul, V3.dot] <;> ring

/-- The frame of a configuration `P` (coordinates). -/
structure IsFrame (P : Nat → V3 ℝ) (U : Nat → V3 ℝ) (D : ℝ) : Prop where
  pos : 0 < D
  br : ∀ a b c d, val3 P (.br a b c d) = D * val3 U (.br a b c d)
  lv : ∀ a b c d e, val3 P (.lv a b c d e) = D * val3 U (.lv a b c d e)
  mv : ∀ a b c d e f, val3 P (.mv a b c d e f) = D * val3 U (.mv a b c d e f)
  fc : ∀ t p q, val3 P (.fc t p q) = D * val3 U (.fc t p q)
  nv : ∀ r s t, val3 P (.nv r s t) = D ^ 2 * val3 U (.nv r s t)
  cv : ∀ t v, cv3 P t v = D * cv3 U t v
  kv : ∃ Q : ℝ, 0 < Q ∧ ∀ t a b c d, (U a).z = 0 → (U b).z = 0 → (U c).z = 0 → (U d).z = 0 →
      (U (fa t)).z = 0 → (U (fb t)).z = 0 → (U (fc' t)).z = 0 →
      val3 P (.kv t a b c d) = Q * val3 U (.kv t a b c d)

/-- **The frame lemma.**  `ia ib ap w` indices, `SG = ±1`; `det (c1, c2, SG (x_ap - x_0)) > 0`; `w` lies in the plane
of `0, ia, ib`.  Then the frame coordinates exist with `U 0 = 0`, `U ia = e1`, `U ib = e2`, `U ap = (0, 0, SG)`,
`(U w).z = 0`, and the covariance of every literal. -/
theorem frame_exists (P : Nat → V3 ℝ) (ia ib ap w : Nat) (SG : ℝ) (hSG : SG * SG = 1)
    (hD : 0 < V3.det (V3.sub (P ia) (P 0)) (V3.sub (P ib) (P 0)) (V3.smul SG (V3.sub (P ap) (P 0))))
    (hw : V3.det (V3.sub (P ia) (P 0)) (V3.sub (P ib) (P 0)) (V3.sub (P w) (P 0)) = 0) :
    ∃ (U : Nat → V3 ℝ) (D : ℝ), IsFrame P U D ∧ U 0 = ⟨0, 0, 0⟩ ∧ U ia = ⟨1, 0, 0⟩ ∧ U ib = ⟨0, 1, 0⟩ ∧
      U ap = ⟨0, 0, SG⟩ ∧ (U w).z = 0 := by
  let M : Mat3 ℝ := ⟨V3.sub (P ia) (P 0), V3.sub (P ib) (P 0), V3.smul SG (V3.sub (P ap) (P 0))⟩
  have hM : M.det = V3.det (V3.sub (P ia) (P 0)) (V3.sub (P ib) (P 0)) (V3.smul SG (V3.sub (P ap) (P 0))) := rfl
  have hD' : 0 < M.det := hM ▸ hD
  have hne : M.det ≠ 0 := hD'.ne'
  let U : Nat → V3 ℝ := fun i => minv M (V3.sub (P i) (P 0))
  have hP : P = aff (P 0) M U := by
    funext i
    have := app_minv M hne (V3.sub (P i) (P 0))
    have h2 : aff (P 0) M U i = V3.add (P 0) (V3.sub (P i) (P 0)) := by simp only [aff, U, this]
    rw [h2]; apply V3.ext' <;> simp only [V3.add, V3.sub] <;> ring
  refine ⟨U, M.det, ⟨hD', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d; conv_lhs => rw [hP]
    exact val3_aff_br _ _ _ a b c d
  · intro a b c d e; conv_lhs => rw [hP]
    exact val3_aff_lv _ _ _ a b c d e
  · intro a b c d e f; conv_lhs => rw [hP]
    exact val3_aff_mv _ _ _ a b c d e f
  · intro t p q; conv_lhs => rw [hP]
    exact val3_aff_fc _ _ _ t p q
  · intro r s t; conv_lhs => rw [hP]
    exact val3_aff_nv _ _ _ r s t
  · intro t v; conv_lhs => rw [hP]
    exact cv3_aff _ _ _ t v
  · refine ⟨V3.dot (V3.cr M.c1 M.c2) (V3.cr M.c1 M.c2), ?_, ?_⟩
    · by_contra hle
      have h0 : V3.dot (V3.cr M.c1 M.c2) (V3.cr M.c1 M.c2) = 0 := by
        have : 0 ≤ V3.dot (V3.cr M.c1 M.c2) (V3.cr M.c1 M.c2) := by
          simp only [V3.dot]; nlinarith [mul_self_nonneg (V3.cr M.c1 M.c2).x, mul_self_nonneg (V3.cr M.c1 M.c2).y, mul_self_nonneg (V3.cr M.c1 M.c2).z]
        linarith [not_lt.mp hle]
      have hx : (V3.cr M.c1 M.c2).x = 0 := by simp only [V3.dot] at h0; nlinarith [sq_nonneg (V3.cr M.c1 M.c2).x, sq_nonneg (V3.cr M.c1 M.c2).y, sq_nonneg (V3.cr M.c1 M.c2).z]
      have hy : (V3.cr M.c1 M.c2).y = 0 := by simp only [V3.dot] at h0; nlinarith [sq_nonneg (V3.cr M.c1 M.c2).x, sq_nonneg (V3.cr M.c1 M.c2).y, sq_nonneg (V3.cr M.c1 M.c2).z]
      have hz : (V3.cr M.c1 M.c2).z = 0 := by simp only [V3.dot] at h0; nlinarith [sq_nonneg (V3.cr M.c1 M.c2).x, sq_nonneg (V3.cr M.c1 M.c2).y, sq_nonneg (V3.cr M.c1 M.c2).z]
      have : M.det = 0 := by simp only [Mat3.det, V3.det, V3.dot, hx, hy, hz]; ring
      exact hne this
    · intro t a b c d ha hb hc hd h1 h2 h3; conv_lhs => rw [hP]
      exact val3_aff_kv _ _ _ t a b c d ha hb hc hd h1 h2 h3
  · simp only [U, V3.sub, sub_self]; exact minv_zero M
  · show minv M M.c1 = _
    exact minv_c1 M hne
  · exact minv_c2 M hne
  · have : V3.sub (P ap) (P 0) = V3.smul SG M.c3 := by
      apply V3.ext' <;> simp only [V3.smul, V3.sub, M] <;> first | linear_combination (-((P ap).x - (P 0).x)) * hSG | linear_combination (-((P ap).y - (P 0).y)) * hSG | linear_combination (-((P ap).z - (P 0).z)) * hSG
    show minv M (V3.sub (P ap) (P 0)) = _
    rw [this, minv_smul, minv_c3 M hne]
    apply V3.ext' <;> simp [V3.smul]
  · show V3.dot (V3.sub (P w) (P 0)) (V3.cr M.c1 M.c2) / M.det = 0
    have : V3.dot (V3.sub (P w) (P 0)) (V3.cr M.c1 M.c2) = 0 := by
      have := hw; simp only [V3.det, V3.dot, V3.cr] at this ⊢; linarith
    rw [this]; simp

end Minimality.T24.SAT
