module

public import Minimality.FaceChordLeaf
public import Minimality.Quad05Leaf

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

/-- The hypotheses of `isRupert_faceChord_fac` for facet `t`, packaged as one existential. -/
def FaceChordView {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) : Prop :=
  ∃ (u : ℝ³) (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin N) (a w : ZMod k) (ρ : ℝ),
    ⟪F.N t, u⟫ = 0 ∧ 3 ≤ k ∧ r a ∈ S t ∧ r (a + 1) ∈ S t ∧ ρ ≠ 0 ∧
    (∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u) ∧
    (∀ q, q ∉ S t → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u) ∧
    (∀ q ∈ S t, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u) ∧
    Function.Injective (fun i => ⟪x (r i), u⟫) ∧ UniOrSep (fun i => x (r i)) u ∧
    r w ∉ S t ∧
    (∀ m, m ≠ w → r m ∉ S t → F.f t (x (r w)) < F.f t (x (r m))) ∧
    (⟪F.N t, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ ≠ 0 ∨
      ⟪x (r w) - x (r a), x (r (a + 1)) - x (r a)⟫ < 0 ∨
      ⟪x (r w) - x (r (a + 1)), x (r a) - x (r (a + 1))⟫ < 0)

theorem isRupert_of_faceChordView {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) {t : Fin nf} (h : FaceChordView F t) : IsRupert (univ.image x) := by
  rcases h with ⟨u, k, hne, r, a, w, ρ, hnu, hk, hA, hB, hρ, hcyc, hin, hmid, hinj, hz, hwS, hfar, hoff⟩
  have : NeZero k := hne
  exact isRupert_faceChord_fac F t hnu hk r hA hB hρ hcyc hin hmid hinj hz hwS hfar hoff

end Minimality.FaceChord

namespace Minimality.T24.FaceChord
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Quad05

/-- Five-circle cover {012, 016, 025, 0345, 046} (facet indices 0, 1, 2, 3, 4). -/
theorem isRupert_cover24_S5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h : FaceChordView F 0 ∨ FaceChordView F 1 ∨ FaceChordView F 2 ∨
         FaceChordView F 3 ∨ FaceChordView F 4) :
    IsRupert (univ.image x) := by
  rcases h with h0 | h1 | h2 | h3 | h4
  · exact isRupert_of_faceChordView F h0
  · exact isRupert_of_faceChordView F h1
  · exact isRupert_of_faceChordView F h2
  · exact isRupert_of_faceChordView F h3
  · exact isRupert_of_faceChordView F h4

/-- Type-24 wiring of the three-circle cover {012, 016, 0345} (facet indices 0, 1, 3).
Deduced as a corollary of `isRupert_cover24_S5`. -/
theorem isRupert_cover24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h : FaceChordView F 0 ∨ FaceChordView F 1 ∨ FaceChordView F 3) :
    IsRupert (univ.image x) := by
  rcases h with h0 | h1 | h3
  · exact isRupert_cover24_S5 F (Or.inl h0)
  · exact isRupert_cover24_S5 F (Or.inr (Or.inl h1))
  · exact isRupert_cover24_S5 F (Or.inr (Or.inr (Or.inr (Or.inl h3))))

/-- **The quad-chord leaf as a corollary of `isRupert_faceChord_fac`** (facet `3`, `0 < η`).
Same statement as `Minimality.T24.Quad05.isRupert_quadChord` except `0 ≤ η` is replaced by `0 < η`
so that vertex `o` is strictly inside the chord interval (middle with `s = 1 / (1 + η)`). -/
theorem isRupert_quadChord' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {o t A B P Q I : Fin 7}
    (hcov : ∀ j : Fin 7, j = o ∨ j = t ∨ j = A ∨ j = B ∨ j = P ∨ j = Q ∨ j = I)
    (hlab : [o, t, A, B, P, Q].Nodup)
    (hoS : o ∈ s0x_S24 3) (hAS : A ∈ s0x_S24 3) (hBS : B ∈ s0x_S24 3)
    (hPS : P ∉ s0x_S24 3) (hQS : Q ∉ s0x_S24 3) (hIS : I ∉ s0x_S24 3)
    {η : ℝ} (hη : 0 < η) {u : ℝ³} (hu : u = (x B - x o) + η • (x A - x o)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
        (quad (x P) (x A) (x B) (x Q) j - quad (x P) (x A) (x B) (x Q) i) u)
    (hI : ∀ i : ZMod 4,
      0 < ρ * det3 (quad (x P) (x A) (x B) (x Q) (i + 1) - quad (x P) (x A) (x B) (x Q) i)
        (x I - quad (x P) (x A) (x B) (x Q) i) u)
    {s₃ δ₃ : ℝ} (h3 : x t = x B + s₃ • (x A - x B) + δ₃ • u) (hs₀ : 0 < s₃) (hs₁ : s₃ < 1)
    (hδ : δ₃ ≠ 0)
    (hPA : ⟪x P, u⟫ < ⟪x A, u⟫) (hAB : ⟪x A, u⟫ < ⟪x B, u⟫)
    (hQP : ⟪x Q, u⟫ ≠ ⟪x P, u⟫) (hQA : ⟪x Q, u⟫ ≠ ⟪x A, u⟫) (hQB : ⟪x Q, u⟫ ≠ ⟪x B, u⟫)
    {w w' : Fin 7} (hw : (w = Q ∧ w' = P) ∨ (w = P ∧ w' = Q))
    (hfar : 0 < det3 (x B - x o) (x A - x o) (x w - x w') *
      det3 (x B - x o) (x A - x o) (x I - x o))
    (hoff : det3 (x B - x o) (x A - x o) (cross (x B - x A) (x w - x A)) ≠ 0 ∨
      ⟪x w - x A, x B - x A⟫ < 0 ∨ ⟪x w - x B, x A - x B⟫ < 0) :
    IsRupert (univ.image x) := by
  classical
  have _ := hlab
  set e : ℝ³ := x A - x o with he
  have fo := F.zero 3 o hoS
  have fA := F.zero 3 A hAS
  have fB := F.zero 3 B hBS
  have fP := F.neg 3 P hPS
  have fQ := F.neg 3 Q hQS
  have fI := F.neg 3 I hIS
  have Nsub : ∀ a b : Fin 7, ⟪F.N 3, x a - x b⟫ = F.f 3 (x a) - F.f 3 (x b) := F.inner_sub 3
  have hNu : ⟪F.N 3, u⟫ = 0 := by
    rw [hu, inner_add_right, real_inner_smul_right, Nsub, Nsub, fB, fo, fA]; ring
  have hNe : ⟪F.N 3, e⟫ = 0 := by rw [he, Nsub, fA, fo]; ring
  have hN0 : F.N 3 ≠ 0 := by
    intro h0
    have := Nsub I o
    rw [h0, inner_zero_left, fo] at this
    linarith
  have key : ∀ Y : ℝ³, det3 (x B - x A) Y u = -(1 + η) * ⟪cross u e, Y⟫ := by
    intro Y
    rw [hu, he]
    simp only [det3_expand, q5ip, cross_apply_zero, cross_apply_one, cross_apply_two,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hc2 : ∀ Z : ℝ³, det3 (x B - x o) (x A - x o) Z = ⟪cross u e, Z⟫ := by
    intro Z
    rw [hu, he]
    simp only [det3_expand, q5ip, cross_apply_zero, cross_apply_one, cross_apply_two,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hcross : cross u e ≠ 0 := by
    intro h0
    have := hcyc 1 3 (by decide) (by decide)
    rw [show (1 : ZMod 4) + 1 = 2 by decide] at this
    change 0 < ρ * det3 (x B - x A) (x Q - x A) u at this
    rw [key, h0, inner_zero_left, mul_zero, mul_zero] at this
    exact lt_irrefl _ this
  obtain ⟨r_scale, hr⟩ : ∃ r : ℝ, cross u e = r • F.N 3 :=
    ⟨_, eq_smul_of_cross_eq_zero hN0 (cross_eq_zero_of_perp2 hNu hNe (inner_cross_left u e)
      (inner_cross_right u e) hcross)⟩
  have hfarN : F.f 3 (x w) < F.f 3 (x w') := by
    rw [hc2, hc2, hr, real_inner_smul_left, real_inner_smul_left, Nsub, Nsub, fo] at hfar
    by_contra hcon
    push Not at hcon
    have h1 : 0 ≤ r_scale ^ 2 * (F.f 3 (x w) - F.f 3 (x w')) :=
      mul_nonneg (sq_nonneg r_scale) (by linarith)
    have h2 : r_scale * (F.f 3 (x w) - F.f 3 (x w')) * (r_scale * (F.f 3 (x I) - 0)) =
        r_scale ^ 2 * (F.f 3 (x w) - F.f 3 (x w')) * F.f 3 (x I) := by ring
    rw [h2] at hfar
    linarith [mul_nonpos_of_nonneg_of_nonpos h1 fI.le]
  have htS : t ∈ s0x_S24 3 := by
    by_contra ht
    have hsub : s0x_S24 3 ⊆ {o, A, B} := by
      intro j hj
      rcases hcov j with hj_o | hj_t | hj_A | hj_B | hj_P | hj_Q | hj_I
      · rw [hj_o]; exact Finset.mem_insert_self o _
      · rw [hj_t] at hj; exact False.elim (ht hj)
      · rw [hj_A]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self A _)
      · rw [hj_B]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self B))
      · rw [hj_P] at hj; exact False.elim (hPS hj)
      · rw [hj_Q] at hj; exact False.elim (hQS hj)
      · rw [hj_I] at hj; exact False.elim (hIS hj)
    have hcard : (s0x_S24 3).card ≤ ({o, A, B} : Finset (Fin 7)).card := Finset.card_le_card hsub
    have h3card : (s0x_S24 3).card = 4 := by decide
    have h3le : ({o, A, B} : Finset (Fin 7)).card ≤ 3 :=
      (Finset.card_insert_le o _).trans (by
        have := Finset.card_insert_le A {B}
        linarith [Finset.card_singleton B])
    linarith
  set r_rim : ZMod 4 → Fin 7 := quad P A B Q
  have hr_x : ∀ i : ZMod 4, x (r_rim i) = quad (x P) (x A) (x B) (x Q) i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have hz4 : (fun i => ⟪x (r_rim i), u⟫) = quad ⟪x P, u⟫ ⟪x A, u⟫ ⟪x B, u⟫ ⟪x Q, u⟫ := by
    funext i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have hinj0 : Function.Injective (fun i => ⟪x (r_rim i), u⟫) := by
    rw [hz4]
    exact quad_injective (ne_of_lt hPA) (ne_of_lt (hPA.trans hAB)) (Ne.symm hQP) (ne_of_lt hAB)
      (Ne.symm hQA) (Ne.symm hQB)
  have hz : UniOrSep (fun i => x (r_rim i)) u :=
    Or.inl (strictUnimodal_of_cyclic (by norm_num)
      (isCyclicUnimodal_four (z := fun i => ⟪x (r_rim i), u⟫) hinj0
        ⟨Or.inl hPA, Or.inr (Or.inr (Or.inl hAB)), ne_of_lt (hPA.trans hAB), Ne.symm hQA⟩))
  obtain ⟨w_zmod, hw_zmod, hw'_zmod⟩ : ∃ (w_zmod : ZMod 4),
      r_rim w_zmod = w ∧ (∀ m : ZMod 4, m ≠ w_zmod → r_rim m ∉ s0x_S24 3 → r_rim m = w') := by
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨3, rfl, ?_⟩
      intro m hm hmS
      rcases zmod4_cases m with rfl | rfl | rfl | rfl
      · rfl
      · exact False.elim (hmS hAS)
      · exact False.elim (hmS hBS)
      · exact False.elim (hm rfl)
    · refine ⟨0, rfl, ?_⟩
      intro m hm hmS
      rcases zmod4_cases m with rfl | rfl | rfl | rfl
      · exact False.elim (hm rfl)
      · exact False.elim (hmS hAS)
      · exact False.elim (hmS hBS)
      · rfl
  have hfar_f : ∀ m : ZMod 4, m ≠ w_zmod → r_rim m ∉ s0x_S24 3 → F.f 3 (x (r_rim w_zmod)) < F.f 3 (x (r_rim m)) := by
    intro m hm hmS
    rw [hw_zmod, hw'_zmod m hm hmS]
    exact hfarN
  have hoff' : ⟪F.N 3, cross (x (r_rim (1 + 1)) - x (r_rim 1)) (x (r_rim w_zmod) - x (r_rim 1))⟫ ≠ 0 ∨
      ⟪x (r_rim w_zmod) - x (r_rim 1), x (r_rim (1 + 1)) - x (r_rim 1)⟫ < 0 ∨
      ⟪x (r_rim w_zmod) - x (r_rim (1 + 1)), x (r_rim 1) - x (r_rim (1 + 1))⟫ < 0 := by
    rw [show (1 : ZMod 4) + 1 = 2 by decide]
    change ⟪F.N 3, cross (x B - x A) (x (r_rim w_zmod) - x A)⟫ ≠ 0 ∨
      ⟪x (r_rim w_zmod) - x A, x B - x A⟫ < 0 ∨
      ⟪x (r_rim w_zmod) - x B, x A - x B⟫ < 0
    rw [hw_zmod]
    rcases hoff with h | h | h
    · left
      intro h0
      apply h
      rw [hc2, hr, real_inner_smul_left, h0, mul_zero]
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hwS : r_rim w_zmod ∉ s0x_S24 3 := by
    rw [hw_zmod]
    rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  refine isRupert_faceChord_fac F (3 : Fin 9) hNu (k := 4) (by decide) r_rim (a := 1)
    (hA := hAS) (hB := hBS) (hρ := hρ) ?_ ?_ ?_ hinj0 hz (w := w_zmod) hwS hfar_f hoff'
  · intro i j hj1 hj2
    have h := hcyc i j hj1 hj2
    rw [← hr_x (i + 1), ← hr_x i, ← hr_x j] at h
    exact h
  · intro q hqS hqr i
    rcases hcov q with hq_o | hq_t | hq_A | hq_B | hq_P | hq_Q | hq_I
    · rw [hq_o] at hqS; exact False.elim (hqS hoS)
    · rw [hq_t] at hqS; exact False.elim (hqS htS)
    · exact False.elim (hqr 1 hq_A)
    · exact False.elim (hqr 2 hq_B)
    · exact False.elim (hqr 0 hq_P)
    · exact False.elim (hqr 3 hq_Q)
    · rw [hq_I]
      have h := hI i
      rw [← hr_x (i + 1), ← hr_x i] at h
      exact h
  · intro q hqS hqr
    rcases hcov q with hq_o | hq_t | hq_A | hq_B | hq_P | hq_Q | hq_I
    · refine ⟨1 / (1 + η), -1 / (1 + η), by positivity, ?_, ?_, ?_⟩
      · rw [div_lt_one (by linarith)]; linarith
      · exact div_ne_zero (by norm_num) (by linarith)
      · change x q = x A + (1 / (1 + η)) • (x B - x A) + (-1 / (1 + η)) • u
        rw [hq_o, hu, he]
        ext j
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        have : 1 + η ≠ 0 := by linarith
        field_simp
        ring
    · refine ⟨1 - s₃, δ₃, by linarith, by linarith, hδ, ?_⟩
      change x q = x A + (1 - s₃) • (x B - x A) + δ₃ • u
      rw [hq_t, h3]
      ext j
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    · exact False.elim (hqr 1 hq_A)
    · exact False.elim (hqr 2 hq_B)
    · exact False.elim (hqr 0 hq_P)
    · exact False.elim (hqr 3 hq_Q)
    · rw [hq_I] at hqS; exact False.elim (hIS hqS)

end Minimality.T24.FaceChord
