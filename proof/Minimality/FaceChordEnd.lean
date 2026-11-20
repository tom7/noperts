module

public import Minimality.FaceChordLeaf
public import Minimality.Quad05Leaf

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.FaceChord
open Minimality Minimality.H21

/-- Transfer lemma: persistent double normals along `e` are unchanged under scaling by `σ ≠ 0`. -/
theorem noPersistHDN_smul {k : ℕ} (x : ZMod k → ℝ³) (u₀ e : ℝ³) {σ : ℝ} (hσ : σ ≠ 0)
    (h : NoPersistHDN x u₀ e) : NoPersistHDN x u₀ (σ • e) := by
  intro i j Y hY Y' hY' hne hu he'
  rw [real_inner_smul_right, mul_eq_zero] at he'
  have he0 : ⟪Y' - Y, e⟫ = 0 := he'.resolve_left hσ
  exact h i j Y hY Y' hY' hne hu he0

/-- **The on-face-circle chord-middle leaf with chord endpoints allowed.**
Generalizes `isRupert_faceChord` to allow middles at `s = 0` or `s = 1`, provided the
depth offset `δ` has the appropriate sign for slide direction `σ • (c (a + 1) - c a)`:
`s = 0` requires `σ * δ < 0` (sliding inwards), and `s = 1` requires `0 < σ * δ`
(also sliding inwards). -/
theorem isRupert_faceChord_end {V M : Finset ℝ³} {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → ℝ³)
    (hcV : ∀ i, c i ∈ V) {n : ℝ³} {κ : ℝ} (hle : ∀ z ∈ V, ⟪n, z⟫ ≤ κ) {a : ZMod k}
    (hA : ⟪n, c a⟫ = κ) (hB : ⟪n, c (a + 1)⟫ = κ) {u : ℝ³} (hnu : ⟪n, u⟫ = 0) {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (c (i + 1) - c i) (c j - c i) u)
    (hin : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ c j) → ∀ i,
      0 < ρ * det3 (c (i + 1) - c i) (y - c i) u)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ δ ≠ 0 ∧ (s = 0 → σ * δ < 0) ∧
      (s = 1 → 0 < σ * δ) ∧ m = c a + s • (c (a + 1) - c a) + δ • u)
    (hinj : Function.Injective fun i => ⟪c i, u⟫) (hz : UniOrSep c u) {w : ZMod k}
    (hfar : ∀ m, m ≠ w → ⟪n, c w⟫ < ⟪n, c m⟫)
    (hoff : ⟪n, cross (c (a + 1) - c a) (c w - c a)⟫ ≠ 0 ∨
      ⟪c w - c a, c (a + 1) - c a⟫ < 0 ∨ ⟪c w - c (a + 1), c a - c (a + 1)⟫ < 0) :
    IsRupert V := by
  classical
  have hk2 : 2 ≤ k := by omega
  set e : ℝ³ := c (a + 1) - c a with he
  have hcinj : Function.Injective c := fun i j h => hinj (by simp only [h])
  have hu0 : u ≠ 0 := by
    intro h0
    apply zmod_ne_add_one hk2 0
    exact hinj (by simp [h0])
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfar (w + 1) (fun h => zmod_ne_add_one hk2 w h.symm)
    simp at this
  have hne : ⟪n, e⟫ = 0 := by rw [he, inner_sub_right, hA, hB, sub_self]
  have ha2 : a + 2 ≠ a := by
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) a
    simpa using this
  have ha21 : a + 2 ≠ a + 1 := by
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) a
    simpa using this
  have hcross : cross u e ≠ 0 := by
    intro h0
    have := hcyc a (a + 2) ha2 ha21
    rw [← he, det3_e_u, h0, inner_zero_left, mul_zero] at this
    exact lt_irrefl _ this
  have htop : ∀ m, ⟪n, c m⟫ = κ → c m = c a ∨ c m = c (a + 1) := by
    intro m hm
    by_contra hcon
    push Not at hcon
    have hma : m ≠ a := fun h => hcon.1 (by rw [h])
    have hma1 : m ≠ a + 1 := fun h => hcon.2 (by rw [h])
    have := hcyc a m hma hma1
    rw [det3_eq_zero_of_perp hn0 hne (by rw [inner_sub_right, hm, hA, sub_self]) hnu,
      mul_zero] at this
    exact lt_irrefl _ this
  have hcM : ∀ i, c i ∉ M := by
    intro i hi
    obtain ⟨s, δ, hs0, hs1, hδ, -, -, hm⟩ := hM _ hi
    have hnc : ⟪n, c i⟫ = κ := by
      have : ⟪n, c i⟫ = ⟪n, c a + s • e + δ • u⟫ := by rw [hm]
      rw [this, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        hne, hnu, hA, mul_zero, mul_zero, add_zero, add_zero]
    rcases htop i hnc with hia | hia1
    · rw [hia] at hm
      have h1 : s • e + δ • u = 0 := by
        have : s • e + δ • u = (c a + s • e + δ • u) - c a := by abel
        rw [this, ← hm, sub_self]
      have := cross_comb u e s δ
      rw [h1] at this
      have h2 : s • cross u e = 0 := by rw [← this]; ext j; fin_cases j <;> simp [cross]
      have hs : s = 0 := (smul_eq_zero.mp h2).resolve_right hcross
      rw [hs, zero_smul, zero_add] at h1
      have : δ = 0 := by
        by_contra hd
        exact hu0 (smul_eq_zero.mp h1 |>.resolve_left hd)
      exact hδ this
    · have h2 : c (a + 1) = c a + e := by rw [he]; abel
      rw [hia1, h2] at hm
      have h1 : (s - 1) • e + δ • u = 0 := by
        have : (s - 1) • e + δ • u = (c a + s • e + δ • u) - (c a + e) := by module
        rw [this, ← hm, sub_self]
      have := cross_comb u e (s - 1) δ
      rw [h1] at this
      have h2 : (s - 1) • cross u e = 0 := by rw [← this]; ext j; fin_cases j <;> simp [cross]
      have hs : s = 1 := by linarith [(smul_eq_zero.mp h2).resolve_right hcross]
      rw [hs, sub_self, zero_smul, zero_add] at h1
      have : δ = 0 := by
        by_contra hd
        exact hu0 (smul_eq_zero.mp h1 |>.resolve_left hd)
      exact hδ this
  have hM' : ∀ m ∈ M, ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s' δ' : ℝ,
      0 < s' ∧ s' < 1 ∧ δ' ≠ 0 ∧ m = c i + s' • (c (i + 1) - c i) + δ' • (u + τ • (σ • e)) := by
    intro m hm_in
    obtain ⟨s, δ, hs0, hs1, hδ, hs_zero, hs_one, hm⟩ := hM m hm_in
    have hcont : ContinuousAt (fun τ : ℝ => s - σ * δ * τ) 0 := by fun_prop
    have hlim : Tendsto (fun τ : ℝ => s - σ * δ * τ) (𝓝[>] 0) (𝓝 s) := by
      have h := hcont.tendsto
      simp only [mul_zero, sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    rcases lt_or_eq_of_le hs0 with hs0_pos | rfl
    · rcases lt_or_eq_of_le hs1 with hs1_lt | rfl
      · filter_upwards [self_mem_nhdsWithin, hlim.eventually (Ioo_mem_nhds hs0_pos hs1_lt)] with τ (hτ : 0 < τ) hg
        refine ⟨a, s - σ * δ * τ, δ, hg.1, hg.2, hδ, ?_⟩
        rw [← he]
        ext j
        have hj := congrArg (fun v : ℝ³ => v j) hm
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
        rw [hj]
        ring
      · have hC : 0 < σ * δ := hs_one rfl
        have hgt : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < 1 - σ * δ * τ :=
          hlim.eventually (Ioi_mem_nhds zero_lt_one)
        filter_upwards [self_mem_nhdsWithin, hgt] with τ (hτ : 0 < τ) h0
        refine ⟨a, 1 - σ * δ * τ, δ, h0, by linarith [mul_pos hC hτ], hδ, ?_⟩
        rw [← he]
        ext j
        have hj := congrArg (fun v : ℝ³ => v j) hm
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
        rw [hj]
        ring
    · have hC : σ * δ < 0 := hs_zero rfl
      have hlt : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 - σ * δ * τ < 1 :=
        hlim.eventually (Iio_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, hlt] with τ (hτ : 0 < τ) h1
      have hpos : 0 < 0 - σ * δ * τ := by
        have : 0 < - (σ * δ) := by linarith
        have := mul_pos this hτ
        linarith
      refine ⟨a, 0 - σ * δ * τ, δ, hpos, h1, hδ, ?_⟩
      rw [← he]
      ext j
      have hj := congrArg (fun v : ℝ³ => v j) hm
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
      rw [hj]
      ring
  have hσ_ne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hbad_e : NoPersistHDN c u e :=
    noPersistHDN_of_far_offChord (V := V) hk2 c hcinj hcV hle hA hB ⟨a, rfl⟩ htop ⟨w, rfl⟩
      (fun m hm => hfar m fun h => hm (by rw [h])) hnu hne hcross hoff
  have hbad : NoPersistHDN c u (σ • e) := noPersistHDN_smul c u e hσ_ne hbad_e
  exact isRupert_of_slideP V M u (σ • e) hu0 c hcV hcM hk ρ hρ
    (fun i j h1 h2 => Or.inl (hcyc i j h1 h2))
    (fun y hy hyM hyc i => Or.inl (hin y hy hyM hyc i))
    hM' hinj hz hbad

/-- **The generic on-face-circle chord-middle leaf with chord endpoints allowed.**
Generalizes `isRupert_faceChord_fac` to allow middles at `s = 0` or `s = 1` under
slide direction `σ = ±1`. -/
theorem isRupert_faceChord_fac_end {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) {u : ℝ³} (hnu : ⟪F.N t, u⟫ = 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (r : ZMod k → Fin N) {a : ZMod k}
    (hA : r a ∈ S t) (hB : r (a + 1) ∈ S t) {ρ : ℝ} (hρ : ρ ≠ 0)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u)
    (hin : ∀ q, q ∉ S t → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u)
    (hmid : ∀ q ∈ S t, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ δ ≠ 0 ∧
      (s = 0 → σ * δ < 0) ∧ (s = 1 → 0 < σ * δ) ∧
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
    rw [inner_sub_right, fB, fA, sub_zero] at this
    linarith
  have hfar' : ∀ m, m ≠ w → ⟪n, x (r w)⟫ < ⟪n, x (r m)⟫ := by
    intro m hm
    have := Nsub (r w) (r m)
    rw [inner_sub_right] at this
    by_cases hmS : r m ∈ S t
    · have fm : F.f t (x (r m)) = 0 := F.zero t _ hmS
      linarith
    · have := hfar m hm hmS
      linarith
  have hM' : ∀ m ∈ M, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ δ ≠ 0 ∧
      (s = 0 → σ * δ < 0) ∧ (s = 1 → 0 < σ * δ) ∧
      m = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
    rw [mem_filter] at hq
    exact hmid q hq.1 hq.2
  have hin' : ∀ y ∈ univ.image x, y ∉ M → (∀ j, y ≠ x (r j)) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (y - x (r i)) u := by
    intro y hy hyM hyr i
    obtain ⟨q, -, rfl⟩ := mem_image.mp hy
    have hqS : q ∉ S t := by
      intro hq
      apply hyM
      apply mem_image.mpr
      refine ⟨q, mem_filter.mpr ⟨hq, fun j hj => hyr j (congrArg x hj)⟩, rfl⟩
    exact hin q hqS (fun j hj => hyr j (congrArg x hj)) i
  exact isRupert_faceChord_end hk (fun i => x (r i)) (fun i => mem_image_of_mem x (mem_univ _))
    hle hA_inner hB_inner hnu hρ hcyc hin' hσ hM' hinj hz hfar' hoff

end Minimality.FaceChord

namespace Minimality.T24.FaceChord
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Quad05

/-- **The quad-chord leaf at `η = 0` as a corollary of `isRupert_faceChord_fac_end`**.
Same statement as `Minimality.T24.Quad05.isRupert_quadChord` with `η` replaced by `0`
and `hη` removed. Vertex `o` is at chord endpoint `B` (`s = 1`) with `δ = -1`, so
the slide direction is `σ = -1` (`σ * δ = 1 > 0`). -/
theorem isRupert_quadChord_eta0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {o t A B P Q I : Fin 7}
    (hcov : ∀ j : Fin 7, j = o ∨ j = t ∨ j = A ∨ j = B ∨ j = P ∨ j = Q ∨ j = I)
    (hlab : [o, t, A, B, P, Q].Nodup)
    (hoS : o ∈ s0x_S24 3) (hAS : A ∈ s0x_S24 3) (hBS : B ∈ s0x_S24 3)
    (hPS : P ∉ s0x_S24 3) (hQS : Q ∉ s0x_S24 3) (hIS : I ∉ s0x_S24 3)
    {u : ℝ³} (hu : u = (x B - x o) + (0 : ℝ) • (x A - x o)) {ρ : ℝ} (hρ : ρ ≠ 0)
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
  have key : ∀ Y : ℝ³, det3 (x B - x A) Y u = -(1 + (0 : ℝ)) * ⟪cross u e, Y⟫ := by
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
  refine isRupert_faceChord_fac_end F (3 : Fin 9) hNu (k := 4) (by decide) r_rim (a := 1)
    (hA := hAS) (hB := hBS) (hρ := hρ) (σ := -1) (Or.inr rfl) ?_ ?_ ?_ hinj0 hz (w := w_zmod) hwS hfar_f hoff'
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
    · refine ⟨1, -1, by norm_num, by norm_num, by norm_num, fun hs => by linarith, fun _ => by norm_num, ?_⟩
      change x q = x A + (1 : ℝ) • (x B - x A) + (-1 : ℝ) • u
      rw [hq_o, hu, he]
      ext j
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    · refine ⟨1 - s₃, δ₃, by linarith, by linarith, hδ, fun hs => by linarith, fun hs => by linarith, ?_⟩
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
