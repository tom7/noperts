module

public import Minimality.FaceChordLeaf

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.FaceChord
open Minimality Minimality.H21

/-- **The on-face-circle chord-middle leaf for an arbitrary facet.**
A view `u` on the face circle of facet `t` of an `S0xFac` solid (`⟪F.N t, u⟫ = 0`), with rim
edge `r a → r (a + 1)` in facet `t`: the rim is strictly convex at `u` (`hcyc`), every point off
the facet and off the rim is strictly inside (`hin`), every point of `S t` off the rim is a chord
middle over `r a → r (a + 1)` (`hmid`), the rim depths are distinct (`hinj`) and unimodal or
depth-separated (`hz`), the rim vertex `r w` minimizes `F.f t` on the rim (`hfar`), and its foot
is off the chord (`hoff`). Then `x` is Rupert. -/
theorem isRupert_faceChord_fac {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) {u : ℝ³} (hnu : ⟪F.N t, u⟫ = 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (r : ZMod k → Fin N) {a : ZMod k}
    (hA : r a ∈ S t) (hB : r (a + 1) ∈ S t) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u)
    (hin : ∀ q, q ∉ S t → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u)
    (hmid : ∀ q ∈ S t, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u)
    (hinj : Function.Injective fun i => ⟪x (r i), u⟫) (hz : UniOrSep (fun i => x (r i)) u)
    {w : ZMod k} (hwS : r w ∉ S t)
    (hfar : ∀ m, m ≠ w → r m ∉ S t → F.f t (x (r w)) < F.f t (x (r m)))
    (hoff : ⟪F.N t, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ ≠ 0 ∨
      ⟪x (r w) - x (r a), x (r (a + 1)) - x (r a)⟫ < 0 ∨
      ⟪x (r w) - x (r (a + 1)), x (r a) - x (r (a + 1))⟫ < 0) :
    IsRupert (univ.image x) := by
  classical
  set n := F.N t with hn
  have Nsub : ∀ i j : Fin N, ⟪n, x i - x j⟫ = F.f t (x i) - F.f t (x j) := F.inner_sub t
  have fA : F.f t (x (r a)) = 0 := F.zero t _ hA
  have fB : F.f t (x (r (a + 1))) = 0 := F.zero t _ hB
  have fw : F.f t (x (r w)) < 0 := F.neg t _ hwS
  set M : Finset ℝ³ := ((S t).filter (fun q => ∀ j, q ≠ r j)).image x
  have hle : ∀ z ∈ univ.image x, ⟪n, z⟫ ≤ ⟪n, x (r a)⟫ := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := mem_image.mp hz
    have := Nsub j (r a)
    rw [inner_sub_right, fA] at this
    linarith [F.le t j]
  have hA_inner : ⟪n, x (r a)⟫ = ⟪n, x (r a)⟫ := rfl
  have hB_inner : ⟪n, x (r (a + 1))⟫ = ⟪n, x (r a)⟫ := by
    have := Nsub (r (a + 1)) (r a)
    rw [inner_sub_right, fB, fA, sub_self] at this
    linarith
  have hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
    rw [mem_filter] at hq
    exact hmid q hq.1 hq.2
  have hfar' : ∀ m, m ≠ w → ⟪n, x (r w)⟫ < ⟪n, x (r m)⟫ := by
    intro m hm
    have := Nsub (r w) (r m)
    rw [inner_sub_right] at this
    by_cases hmS : r m ∈ S t
    · have fm0 : F.f t (x (r m)) = 0 := F.zero t _ hmS
      linarith
    · have hlt := hfar m hm hmS
      linarith
  refine isRupert_faceChord (M := M) hk (fun i => x (r i))
    (fun i => mem_image_of_mem x (mem_univ _)) hle hA_inner hB_inner hnu hρ hcyc ?_ hM hinj hz hfar' hoff
  intro y hy hyM hyc i
  obtain ⟨q, -, rfl⟩ := mem_image.mp hy
  have hq_not_r : ∀ j, q ≠ r j := fun j hj => hyc j (by rw [hj])
  have hq_not_S : q ∉ S t := by
    intro hqS
    apply hyM
    rw [mem_image]
    exact ⟨q, mem_filter.mpr ⟨hqS, hq_not_r⟩, rfl⟩
  exact hin q hq_not_S hq_not_r i

/-- **Corollary: Triangle-facet chord leaf via `isRupert_faceChord_fac`.**
Exactly the statement of `isRupert_faceChord_tri`, deduced from `isRupert_faceChord_fac`. -/
theorem isRupert_faceChord_tri' {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) {P Q R : Fin N} (hP : P ∈ S t) (hQ : Q ∈ S t)
    (hR : R ∈ S t) {α β : ℝ} (hαβ : α * β < 0) (hαβ' : 0 < α * (α + β)) {u : ℝ³}
    (hu : u = α • (x R - x P) + β • (x R - x Q)) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (r : ZMod k → Fin N) {a : ZMod k}
    (hQR : (r a = Q ∧ r (a + 1) = R) ∨ (r a = R ∧ r (a + 1) = Q)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u)
    (hin : ∀ q, q ≠ P → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u)
    (hinj : Function.Injective fun i => ⟪x (r i), u⟫) (hz : UniOrSep (fun i => x (r i)) u)
    {w : ZMod k} (hwS : r w ∉ S t)
    (hfar : ∀ m, m ≠ w → r m ∉ S t →
      det3 (x R - x Q) (x R - x P) (x (r m) - x (r w)) *
        det3 (x R - x Q) (x R - x P) (x (r w) - x Q) < 0)
    (hoff : det3 (x R - x Q) (x R - x P) (cross (x R - x Q) (x (r w) - x Q)) ≠ 0 ∨
      ⟪x (r w) - x Q, x R - x Q⟫ < 0 ∨ ⟪x (r w) - x R, x Q - x R⟫ < 0) :
    IsRupert (univ.image x) := by
  classical
  set n := F.N t with hn
  have Nsub : ∀ i j : Fin N, ⟪n, x i - x j⟫ = F.f t (x i) - F.f t (x j) := F.inner_sub t
  have fP := F.zero t P hP
  have fQ := F.zero t Q hQ
  have fR := F.zero t R hR
  have fw := F.neg t _ hwS
  have hα : α ≠ 0 := by rintro rfl; simp at hαβ
  set E : ℝ³ := x R - x Q with hE
  set U : ℝ³ := x R - x P with hU
  have hnE : ⟪n, E⟫ = 0 := by rw [hE, Nsub, fR, fQ, sub_self]
  have hnU : ⟪n, U⟫ = 0 := by rw [hU, Nsub, fR, fP, sub_self]
  have hnu : ⟪n, u⟫ = 0 := by
    rw [hu, inner_add_right, real_inner_smul_right, real_inner_smul_right, hnE, hnU]
    ring
  set Zw : ℝ³ := x (r w) - x Q with hZw
  have hζ : ⟪n, Zw⟫ < 0 := by rw [hZw, Nsub, fQ, sub_zero]; exact fw
  have hn0 : n ≠ 0 := by intro h; rw [h, inner_zero_left] at hζ; linarith
  have key : ∀ Y, det3 E U Y * ⟪n, Zw⟫ = det3 E U Zw * ⟪n, Y⟫ := by
    intro Y
    linear_combination det3_perp_ratio n E U Y Zw + det3 Y Zw U * hnE - det3 Y Zw E * hnU
  have hchi : det3 E U (cross E Zw) ≠ 0 → ⟪n, cross E Zw⟫ ≠ 0 := by
    intro h h0
    apply h
    have := key (cross E Zw)
    rw [h0, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hζ.ne
  have hA : r a ∈ S t := by
    rcases hQR with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> assumption
  have hB : r (a + 1) ∈ S t := by
    rcases hQR with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> assumption
  have hfar_f : ∀ m, m ≠ w → r m ∉ S t → F.f t (x (r w)) < F.f t (x (r m)) := by
    intro m hm hmS
    have h := hfar m hm hmS
    set Y := x (r m) - x (r w)
    have h1 : 0 < det3 E U Y * det3 E U Zw * ⟪n, Zw⟫ := mul_pos_of_neg_of_neg h hζ
    have h2 : det3 E U Y * det3 E U Zw * ⟪n, Zw⟫ = det3 E U Zw ^ 2 * ⟪n, Y⟫ := by
      linear_combination det3 E U Zw * key Y
    rw [h2] at h1
    have h3 := pos_of_mul_pos_right h1 (sq_nonneg _)
    have := Nsub (r m) (r w)
    linarith
  have hPmid : ∀ A B : Fin N, (A = Q ∧ B = R) ∨ (A = R ∧ B = Q) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧
      δ ≠ 0 ∧ x P = x A + s • (x B - x A) + δ • u := by
    intro A B h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨(α + β) / α, -1 / α, ?_, ?_, div_ne_zero (by norm_num) hα, ?_⟩
      · have : (α + β) / α = α * (α + β) / (α * α) := by field_simp
        rw [this]; exact div_pos hαβ' (mul_self_pos.mpr hα)
      · have : (α + β) / α = 1 + α * β / (α * α) := by field_simp
        rw [this]
        have := div_neg_of_neg_of_pos hαβ (mul_self_pos.mpr hα)
        linarith
      · rw [hu, hU, hE]; ext j
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp; ring
    · refine ⟨-β / α, -1 / α, ?_, ?_, div_ne_zero (by norm_num) hα, ?_⟩
      · have : -β / α = -(α * β) / (α * α) := by field_simp
        rw [this]; exact div_pos (by linarith) (mul_self_pos.mpr hα)
      · have : -β / α = 1 - α * (α + β) / (α * α) := by field_simp; ring
        rw [this]
        have := div_pos hαβ' (mul_self_pos.mpr hα)
        linarith
      · rw [hu, hU, hE]; ext j
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp; ring
  have hmid : ∀ q ∈ S t, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u := by
    intro q hqS hqr
    by_cases hqP : q = P
    · subst hqP
      exact hPmid (r a) (r (a + 1)) hQR
    · -- if q ≠ P, hin q gives a strict positive determinant, but q ∈ S t and edge in S t
      -- makes all three vectors perp to n, so det3 is 0, contradiction!
      have hpos := hin q hqP hqr a
      have h_edge : ⟪n, x (r (a + 1)) - x (r a)⟫ = 0 := by
        rw [Nsub, F.zero t _ hB, F.zero t _ hA, sub_self]
      have h_q : ⟪n, x q - x (r a)⟫ = 0 := by
        rw [Nsub, F.zero t _ hqS, F.zero t _ hA, sub_self]
      have hzero : det3 (x (r (a + 1)) - x (r a)) (x q - x (r a)) u = 0 :=
        det3_eq_zero_of_perp hn0 h_edge h_q hnu
      rw [hzero, mul_zero] at hpos
      exact False.elim (lt_irrefl _ hpos)
  have hoff' : ⟪n, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ ≠ 0 ∨
      ⟪x (r w) - x (r a), x (r (a + 1)) - x (r a)⟫ < 0 ∨
      ⟪x (r w) - x (r (a + 1)), x (r a) - x (r (a + 1))⟫ < 0 := by
    rcases hQR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      rcases hoff with h | h | h
      · exact Or.inl (hchi h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [h1, h2]
      rcases hoff with h | h | h
      · left
        have e1 : cross (x Q - x R) (x (r w) - x R) = -cross E Zw := by
          rw [hE, hZw]; ext j; fin_cases j <;> simp [cross] <;> ring
        rw [e1, inner_neg_right, neg_ne_zero]
        exact hchi h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  refine isRupert_faceChord_fac F t hnu hk r hA hB hρ hcyc ?_ hmid hinj hz hwS hfar_f hoff'
  intro q hqS hqr i
  exact hin q (fun h => hqS (h ▸ hP)) hqr i

end Minimality.FaceChord
