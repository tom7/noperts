module

public import Minimality.Type24Circle

@[expose] public section

/-!
# Type 24 link edges 06: rim determinants and transversality (nopert229 report LINKRIM24).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Link24R

open Finset

/-- The determinant part of `EdgeRim` (everything but depth injectivity and `NoHDNAt`). -/
def EdgeRimDet (x : Fin 7 → ℝ³) (u : ℝ³) (d : Fin 7) (h : ℝ) (k : ℕ) [NeZero k]
    (r : ZMod k → Fin 7) : Prop :=
  3 ≤ k ∧ h ≠ 0 ∧ x d = x (r 0) - h • u ∧
    (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u) ∧
    (∀ v, v ≠ d → (∀ j, v ≠ r j) → ∀ i,
      0 < det3 (x (r (i + 1)) - x (r i)) (x v - x (r i)) u)

/-- Vectors orthogonal to `w ≠ 0` have a cross product parallel to `w`. -/
theorem cross_par_of_orth (p q w : ℝ³) (hw : w ≠ 0) (hp : ⟪p, w⟫ = 0) (hq : ⟪q, w⟫ = 0) :
    ∃ κ : ℝ, cross p q = κ • w := by
  have hww : ⟪w, w⟫ ≠ 0 := (real_inner_self_pos.mpr hw).ne'
  refine ⟨⟪cross p q, w⟫ / ⟪w, w⟫, ?_⟩
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hp hq hww ⊢
  ext i
  fin_cases i <;>
  · simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply, smul_eq_mul,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    rw [div_mul_eq_mul_div, eq_div_iff hww]
    first
    | linear_combination (w 1 * q 2 - w 2 * q 1) * hp - (w 1 * p 2 - w 2 * p 1) * hq
    | linear_combination (w 2 * q 0 - w 0 * q 2) * hp - (w 2 * p 0 - w 0 * p 2) * hq
    | linear_combination (w 0 * q 1 - w 1 * q 0) * hp - (w 0 * p 1 - w 1 * p 0) * hq

/-- The edge identity: `κ det3 (b-a) (y-a) u = ⟪NF,y-a⟫⟪NG,u⟫ - ⟪NF,u⟫⟪NG,y-a⟫`. -/
theorem edge_ident (NF NG w z u : ℝ³) (κ : ℝ) (hκ : cross NF NG = κ • w) :
    κ * det3 w z u = ⟪NF, z⟫ * ⟪NG, u⟫ - ⟪NF, u⟫ * ⟪NG, z⟫ := by
  have h0 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) hκ) 0
  have h1 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) hκ) 1
  have h2 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) hκ) 2
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply,
    smul_eq_mul] at h0 h1 h2
  simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  linear_combination -(z 1 * u 2 - z 2 * u 1) * h0 - (z 2 * u 0 - z 0 * u 2) * h1 -
    (z 0 * u 1 - z 1 * u 0) * h2

theorem Rpos {fF fG sF sG : ℝ} (hF : fF ≤ 0) (hG : fG ≤ 0) (hsF : 0 < sF) (hsG : sG ≤ 0)
    (h : fG < 0 ∨ (fF < 0 ∧ sG < 0)) : 0 < fF * sG - sF * fG := by
  rcases h with h | ⟨h1, h2⟩
  · nlinarith [mul_nonneg (neg_nonneg.mpr hF) (neg_nonneg.mpr hsG), mul_pos hsF (neg_pos.mpr h)]
  · nlinarith [mul_pos (neg_pos.mpr h1) (neg_pos.mpr h2), mul_nonneg hsF.le (neg_nonneg.mpr hG)]

/-- **Edge step.** A common edge `a b` of the facets `F` (facing away, `⟪NF,u⟫ > 0`) and `G`
(`⟪NG,u⟫ ≤ 0`); if the triple `(a,b,w)` is positive at the view `u` and `w`, `v` are strictly
beneath `G` (or beneath `F` with `G` strictly facing), then `(a,b,v)` is positive. -/
theorem edgeStep {x : Fin 7 → ℝ³} {S1 S2 : Finset (Fin 7)} (F : Face16 x S1) (G : Face16 x S2)
    (u : ℝ³) {a b w v : Fin 7} (ha1 : a ∈ S1) (hb1 : b ∈ S1) (ha2 : a ∈ S2) (hb2 : b ∈ S2)
    (hab : x a ≠ x b) (sF : 0 < ⟪F.N, u⟫) (sG : ⟪G.N, u⟫ ≤ 0)
    (hw : 0 < det3 (x b - x a) (x w - x a) u)
    (hGw : w ∉ S2 ∨ (w ∉ S1 ∧ ⟪G.N, u⟫ < 0)) (hGv : v ∉ S2 ∨ (v ∉ S1 ∧ ⟪G.N, u⟫ < 0)) :
    0 < det3 (x b - x a) (x v - x a) u := by
  have hFw : ⟪F.N, x b - x a⟫ = 0 := by
    rw [Type24.f_eq_inner F, F.zero b hb1, F.zero a ha1]; simp
  have hGw' : ⟪G.N, x b - x a⟫ = 0 := by
    rw [Type24.f_eq_inner G, G.zero b hb2, G.zero a ha2]; simp
  obtain ⟨κ, hκ⟩ := cross_par_of_orth F.N G.N (x b - x a) (sub_ne_zero.mpr hab.symm) hFw hGw'
  have key : ∀ y, κ * det3 (x b - x a) (y - x a) u =
      ⟪F.N, y - x a⟫ * ⟪G.N, u⟫ - ⟪F.N, u⟫ * ⟪G.N, y - x a⟫ := fun y =>
    edge_ident F.N G.N _ _ u κ hκ
  have R : ∀ y : Fin 7, (y ∉ S2 ∨ (y ∉ S1 ∧ ⟪G.N, u⟫ < 0)) →
      0 < κ * det3 (x b - x a) (x y - x a) u := by
    intro y hy
    rw [key, Type24.f_eq_inner F, Type24.f_eq_inner G, F.zero a ha1, G.zero a ha2]
    simp only [sub_zero]
    refine Rpos (Type24.f_le F y) (Type24.f_le G y) sF sG ?_
    rcases hy with h | ⟨h1, h2⟩
    · exact Or.inl (G.neg y h)
    · exact Or.inr ⟨F.neg y h1, h2⟩
  have hκ0 : 0 < κ := by
    have := R w hGw
    by_contra hc; push Not at hc
    nlinarith
  have := R v hGv
  by_contra hc; push Not at hc
  nlinarith



theorem tcyc (x : Fin 7 → ℝ³) (u : ℝ³) (a b c : Fin 7) :
    det3 (x b - x a) (x c - x a) u = det3 (x c - x b) (x a - x b) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_shift (a b c u : ℝ³) (s1 s2 s3 : ℝ) :
    det3 ((a + s1 • u) - (b + s2 • u)) ((c + s3 • u) - (b + s2 • u)) u = det3 (a - b) (c - b) u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem inner_in0 {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (h0 : 0 ∈ S)
    (h6 : 6 ∉ S) : ⟪F.N, x 6 - x 0⟫ < 0 := by
  rw [Type24.f_eq_inner F 6 0, F.zero 0 h0]; have := F.neg 6 h6; linarith

theorem inner_in6 {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (h0 : 0 ∉ S)
    (h6 : 6 ∈ S) : 0 < ⟪F.N, x 6 - x 0⟫ := by
  rw [Type24.f_eq_inner F 6 0, F.zero 6 h6]; have := F.neg 0 h0; linarith

theorem inner_both {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (h0 : 0 ∈ S)
    (h6 : 6 ∈ S) : ⟪F.N, x 6 - x 0⟫ = 0 := by
  rw [Type24.f_eq_inner F 6 0, F.zero 6 h6, F.zero 0 h0]; simp




/-- Transfer from the end `q` to the end `p` of the link edge: `x p = x q - u`. -/
theorem EdgeRimDet.transfer {k : ℕ} [NeZero k] {x : Fin 7 → ℝ³} {p q : Fin 7}
    {r6 r0 : ZMod k → Fin 7}
    (hr : ∀ i, i ≠ 0 → r0 i = r6 i) (h0 : r0 0 = p) (h6 : r6 0 = q)
    (h : EdgeRimDet x (x q - x p) p 1 k r6) : EdgeRimDet x (x q - x p) q (-1) k r0 := by
  obtain ⟨hk, -, -, hc, hrest⟩ := h
  have hs : ∀ i, ∃ s : ℝ, x (r0 i) = x (r6 i) + s • (x q - x p) := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [h0, h6]; exact ⟨-1, by module⟩
    · exact ⟨0, by rw [hr i hi]; simp⟩
  refine ⟨hk, by norm_num, ?_, ?_, ?_⟩
  · rw [h0]; module
  · intro i j hj1 hj2
    obtain ⟨s1, e1⟩ := hs (i + 1)
    obtain ⟨s2, e2⟩ := hs i
    obtain ⟨s3, e3⟩ := hs j
    rw [e1, e2, e3, det3_shift]
    exact hc i j hj1 hj2
  · intro v hv hvr i
    have hv0 : v ≠ p := by have := hvr 0; rwa [h0] at this
    have hv6 : ∀ j, v ≠ r6 j := by
      intro j
      by_cases hj : j = 0
      · subst hj; rw [h6]; exact hv
      · rw [← hr j hj]; exact hvr j
    obtain ⟨s1, e1⟩ := hs (i + 1)
    obtain ⟨s2, e2⟩ := hs i
    have : det3 (x (r0 (i + 1)) - x (r0 i)) (x v - x (r0 i)) (x q - x p) =
        det3 ((x (r6 (i + 1)) + s1 • (x q - x p)) - (x (r6 i) + s2 • (x q - x p)))
          ((x v + (0:ℝ) • (x q - x p)) - (x (r6 i) + s2 • (x q - x p))) (x q - x p) := by
      rw [e1, e2]; simp
    rw [this, det3_shift]
    exact hrest v hv0 hv6 i





/-! ### The covering triangle `026` (Lemma T for the link triangle) -/




theorem tri_pt {x : Fin 7 → ℝ³} {v : Fin 7} {c0 c2 c6 d0 d2 d6 t : ℝ}
    (hx : x v = x 1 + c0 • (x 0 - x 1) + c2 • (x 2 - x 1) + c6 • (x 6 - x 1))
    (h0 : 0 < c0 + t * d0) (h2 : 0 < c2 + t * d2) (h6 : 0 < c6 + t * d6)
    (hs : (c0 + t * d0) + (c2 + t * d2) + (c6 + t * d6) = 1) :
    ∃ t α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
      x v + t • (d0 • (x 0 - x 1) + d2 • (x 2 - x 1) + d6 • (x 6 - x 1)) =
        α • x 0 + β • x 2 + γ • x 6 := by
  refine ⟨t, c0 + t * d0, c2 + t * d2, c6 + t * d6, h0, h2, h6, hs, ?_⟩
  have key : x 1 = ((c0 + t * d0) + (c2 + t * d2) + (c6 + t * d6)) • x 1 := by
    rw [hs, one_smul]
  rw [hx]
  linear_combination (norm := module) key

theorem core_real {a b c δ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ : 0 < δ)
    (hab : a + b ≤ 1) (h1 : δ * (a + b + c) ≤ a) (h2 : δ * (a + b + c) ≤ b) :
    0 < a + (1 - (a + b + c)) / (1 + 2 * δ) * δ ∧ 0 < b + (1 - (a + b + c)) / (1 + 2 * δ) * δ ∧
      0 < c + (1 - (a + b + c)) / (1 + 2 * δ) := by
  have hD : 0 < 1 + 2 * δ := by linarith
  have e : ∀ y : ℝ, y + (1 - (a + b + c)) / (1 + 2 * δ) * δ =
      (y * (1 + 2 * δ) + δ * (1 - (a + b + c))) / (1 + 2 * δ) := by
    intro y; field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; apply div_pos _ hD; nlinarith
  · rw [e]; apply div_pos _ hD; nlinarith
  · have : c + (1 - (a + b + c)) / (1 + 2 * δ) =
        (2 * δ * c + (1 - a - b)) / (1 + 2 * δ) := by field_simp; ring
    rw [this]; apply div_pos _ hD; nlinarith









end Link24R
end Minimality
