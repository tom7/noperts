module

public import Minimality.FaceChordFac

@[expose] public section

/-!
# The face-chord leaf with a far PAIR (job OSPEC3, nopert229 notes/OPENSPECIAL-STRATEGY.md)

`isRupert_faceChord` (FaceChordLeaf.lean) needs a strict farthest rim vertex `w` from the face (Lemma H,
`noPersistHDN_of_far_offChord`): the only possible persistent double normal along the slide is along the face
normal `n`, from the chord `[A, B]` to the farthest feature.  When two rim vertices `c`, `b` tie for farthest (the
far feature is an EDGE parallel to the face, e.g. type 24 stratum S3: edge 26 parallel to 0345) the same argument
works with the far segment: by `classify_face` the far foot lies on `[c, b]`, so a double normal needs the projection
of `[c, b]` along `n` to meet `[A, B]`.  It cannot if the line `A B` strictly separates `c` and `b` from nothing
(both strictly on one side: `0 < χ(c) χ(b)`, `χ(Y) = ⟪n, (B - A) × (Y - A)⟫`), or the line `c b` has `A` and `B`
strictly on one side.  No tie is assumed: `min ⟪n, c⟫ ⟪n, b⟫` covers a strict farthest vertex too.

* `noPersistHDN_of_farPair_offChord`: Lemma H with a far pair.
* `isRupert_faceChord_pair`: `isRupert_faceChord` with a far pair (`n ≠ 0` as a hypothesis).
* `isRupert_faceChord_fac_pair`: the same on facet `t` of an `S0xFac` solid.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

/-- **Lemma H with a far pair.**  As `noPersistHDN_of_far_offChord`, with the farthest feature among the rim
vertices `c`, `b` (all others strictly nearer than `min`), off the chord in the segment sense: both `c`, `b`
strictly on one side of the line `A B` in the face plane, or `A`, `B` strictly on one side of the line `c b`. -/
theorem noPersistHDN_of_farPair_offChord {V : Finset ℝ³} {k : ℕ} (hk : 2 ≤ k) (x : ZMod k → ℝ³)
    (hxinj : Function.Injective x) (hxV : ∀ i, x i ∈ V) {n : ℝ³} {κ : ℝ} {A B c b : ℝ³}
    (hle : ∀ z ∈ V, ⟪n, z⟫ ≤ κ) (hA : ⟪n, A⟫ = κ) (hB : ⟪n, B⟫ = κ) (hAR : ∃ i, x i = A)
    (htop : ∀ m, ⟪n, x m⟫ = κ → x m = A ∨ x m = B) (hcR : ∃ i, x i = c) (hbR : ∃ i, x i = b)
    (hlow : ∀ m, x m ≠ c → x m ≠ b → min ⟪n, c⟫ ⟪n, b⟫ < ⟪n, x m⟫) {u₀ e : ℝ³} (hu : ⟪n, u₀⟫ = 0)
    (he : ⟪n, e⟫ = 0) (hind : cross u₀ e ≠ 0)
    (hoff : 0 < ⟪n, cross (B - A) (c - A)⟫ * ⟪n, cross (B - A) (b - A)⟫ ∨
      0 < ⟪n, cross (b - c) (A - c)⟫ * ⟪n, cross (b - c) (B - c)⟫) :
    NoPersistHDN x u₀ e := by
  intro i j Y hY Y' hY' hne hYu hYe hext
  have hn0 : n ≠ 0 := by
    rintro rfl
    rcases hoff with h | h <;> simp at h
  have h1 : cross n (Y' - Y) = 0 :=
    cross_eq_zero_of_perp2 hu he hYu hYe hind
  obtain ⟨r, hr⟩ : ∃ r : ℝ, Y' - Y = r • n :=
    ⟨_, eq_smul_of_cross_eq_zero hn0 h1⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hne (by rw [zero_smul] at hr; exact (sub_eq_zero.mp hr))
  obtain ⟨Z, hZ, F, hF, r', -, hFZ, -⟩ := classify_face (V := V) hk x hxinj hxV hle hA hAR htop
    hcR hbR hlow hY hY' hr0 hr hext
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hZ
  obtain ⟨γ, δ, hγ, hδ, hγδ, rfl⟩ := hF
  have hα' : α = 1 - β := by linarith
  have hγ' : γ = 1 - δ := by linarith
  subst hα' hγ'
  have ip : ∀ p q : ℝ³, ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := fun p q => by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring
  have hc : ∀ j : Fin 3, (1 - δ) * c j + δ * b j = (1 - β) * A j + β * B j + r' * n j := by
    intro j
    have := congrArg (fun v : ℝ³ => v j) hFZ
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    linarith
  rcases hoff with h | h
  · -- `χ` is affine, `χ(F) = 0` (F is over the line `A B`), and `χ(c)`, `χ(b)` have one strict sign
    have key : (1 - δ) * ⟪n, cross (B - A) (c - A)⟫ + δ * ⟪n, cross (B - A) (b - A)⟫ = 0 := by
      simp only [ip, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply]
      have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
      linear_combination (n 1 * (B 2 - A 2) - n 2 * (B 1 - A 1)) * h0 +
        (n 2 * (B 0 - A 0) - n 0 * (B 2 - A 2)) * h1 + (n 0 * (B 1 - A 1) - n 1 * (B 0 - A 0)) * h2
    set p := ⟪n, cross (B - A) (c - A)⟫
    set q := ⟪n, cross (B - A) (b - A)⟫
    have hp : p ≠ 0 := by rintro hp; rw [hp, zero_mul] at h; exact lt_irrefl _ h
    have e2 : (1 - δ) * (p * p) + δ * (p * q) = 0 := by linear_combination p * key
    have := mul_self_pos.mpr hp
    nlinarith [mul_nonneg hγ this.le, mul_nonneg hδ h.le]
  · -- the line `c b` has `A`, `B` strictly on one side, and `Z` (under `F`, on that line) is between them
    have key : (1 - β) * ⟪n, cross (b - c) (A - c)⟫ + β * ⟪n, cross (b - c) (B - c)⟫ = 0 := by
      simp only [ip, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply]
      have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
      linear_combination (-(n 1 * (b 2 - c 2) - n 2 * (b 1 - c 1))) * h0 +
        (-(n 2 * (b 0 - c 0) - n 0 * (b 2 - c 2))) * h1 + (-(n 0 * (b 1 - c 1) - n 1 * (b 0 - c 0))) * h2
    set p := ⟪n, cross (b - c) (A - c)⟫
    set q := ⟪n, cross (b - c) (B - c)⟫
    have hp : p ≠ 0 := by rintro hp; rw [hp, zero_mul] at h; exact lt_irrefl _ h
    have e2 : (1 - β) * (p * p) + β * (p * q) = 0 := by linear_combination p * key
    have := mul_self_pos.mpr hp
    nlinarith [mul_nonneg hα this.le, mul_nonneg hβ h.le]

namespace FaceChord
open Minimality.H21

/-- **The on-face-circle chord-middle leaf with a far pair.**  `isRupert_faceChord` with the strict farthest rim
vertex replaced by two rim vertices `c w`, `c w'` (every other rim vertex strictly nearer to the face than their
`min`; a tie is allowed) whose segment is off the chord in the sense of `noPersistHDN_of_farPair_offChord`. -/
theorem isRupert_faceChord_pair {V M : Finset ℝ³} {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → ℝ³)
    (hcV : ∀ i, c i ∈ V) {n : ℝ³} {κ : ℝ} (hle : ∀ z ∈ V, ⟪n, z⟫ ≤ κ) {a : ZMod k}
    (hA : ⟪n, c a⟫ = κ) (hB : ⟪n, c (a + 1)⟫ = κ) {u : ℝ³} (hnu : ⟪n, u⟫ = 0) {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (c (i + 1) - c i) (c j - c i) u)
    (hin : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ c j) → ∀ i,
      0 < ρ * det3 (c (i + 1) - c i) (y - c i) u)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c a + s • (c (a + 1) - c a) + δ • u)
    (hinj : Function.Injective fun i => ⟪c i, u⟫) (hz : UniOrSep c u) (hn0 : n ≠ 0) {w w' : ZMod k}
    (hlow : ∀ m, m ≠ w → m ≠ w' → min ⟪n, c w⟫ ⟪n, c w'⟫ < ⟪n, c m⟫)
    (hoff : 0 < ⟪n, cross (c (a + 1) - c a) (c w - c a)⟫ * ⟪n, cross (c (a + 1) - c a) (c w' - c a)⟫ ∨
      0 < ⟪n, cross (c w' - c w) (c a - c w)⟫ * ⟪n, cross (c w' - c w) (c (a + 1) - c w)⟫) :
    IsRupert V := by
  classical
  have hk2 : 2 ≤ k := by omega
  set e : ℝ³ := c (a + 1) - c a with he
  have hcinj : Function.Injective c := fun i j h => hinj (by simp only [h])
  have hu0 : u ≠ 0 := by
    intro h0
    apply zmod_ne_add_one hk2 0
    exact hinj (by simp [h0])
  have hne : ⟪n, e⟫ = 0 := by rw [he, inner_sub_right, hA, hB, sub_self]
  -- the third rim vertex after `a`
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
  -- the rim meets the face only in `A`, `B`
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
  -- no rim vertex is a middle
  have hcM : ∀ i, c i ∉ M := by
    intro i hi
    obtain ⟨s, δ, hs0, hs1, -, hm⟩ := hM _ hi
    by_cases hia : i = a
    · rw [hia] at hm
      have h1 : s • e + δ • u = 0 := by
        have : s • e + δ • u = (c a + s • e + δ • u) - c a := by abel
        rw [this, ← hm, sub_self]
      have := cross_comb u e s δ
      rw [h1] at this
      have h2 : s • cross u e = 0 := by rw [← this]; ext j; fin_cases j <;> simp [cross]
      exact hs0.ne' ((smul_eq_zero.mp h2).resolve_right hcross)
    by_cases hia1 : i = a + 1
    · have h2 : c (a + 1) = c a + e := by rw [he]; abel
      rw [hia1, h2] at hm
      have h1 : (s - 1) • e + δ • u = 0 := by
        have : (s - 1) • e + δ • u = (c a + s • e + δ • u) - (c a + e) := by module
        rw [this, ← hm, sub_self]
      have := cross_comb u e (s - 1) δ
      rw [h1] at this
      have h2 : (s - 1) • cross u e = 0 := by rw [← this]; ext j; fin_cases j <;> simp [cross]
      have := (smul_eq_zero.mp h2).resolve_right hcross
      linarith
    · have := hcyc a i hia hia1
      rw [← he, hm, show c a + s • e + δ • u - c a = s • e + δ • u by abel, det3_e_u,
        inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_cross_left,
        inner_cross_right] at this
      simp at this
  -- the middles along the slide `u + τ e`
  have hM' : ∀ m ∈ M, ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∃ i : ZMod k, ∃ s δ : ℝ,
      0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c i + s • (c (i + 1) - c i) + δ • (u + τ • e) := by
    intro m hm
    obtain ⟨s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
    have hlim : Tendsto (fun τ : ℝ => s - δ * τ) (𝓝[>] 0) (𝓝 s) := by
      have : Continuous (fun τ : ℝ => s - δ * τ) := by fun_prop
      have h := this.tendsto 0
      simp only [mul_zero, sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    filter_upwards [hlim.eventually (Ioo_mem_nhds hs0 hs1)] with τ hτ
    refine ⟨a, s - δ * τ, δ, hτ.1, hτ.2, hδ, ?_⟩
    rw [← he, smul_add, smul_smul, sub_smul]
    abel
  have hbad : NoPersistHDN c u e :=
    noPersistHDN_of_farPair_offChord (V := V) hk2 c hcinj hcV hle hA hB ⟨a, rfl⟩ htop ⟨w, rfl⟩
      ⟨w', rfl⟩ (fun m h1 h2 => hlow m (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))) hnu hne hcross
      hoff
  exact isRupert_of_slideP V M u e hu0 c hcV hcM hk ρ hρ
    (fun i j h1 h2 => Or.inl (hcyc i j h1 h2)) (fun y hy hyM hyc i => Or.inl (hin y hy hyM hyc i))
    hM' hinj hz hbad

/-- **The far-pair chord leaf for an arbitrary facet** (`isRupert_faceChord_fac` with a far pair).  Facet `t` of
an `S0xFac` solid, view `u` on its face circle, rim edge `r a → r (a + 1)` in the facet, the rim tests at `u`;
the two off-facet rim vertices `r w`, `r w'` are at least as far from the facet as every other off-facet rim
vertex, strictly farther than their `min`, and their segment is off the chord. -/
theorem isRupert_faceChord_fac_pair {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
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
    {w w' : ZMod k} (hwS : r w ∉ S t) (hw'S : r w' ∉ S t)
    (hlow : ∀ m, m ≠ w → m ≠ w' → r m ∉ S t → min (F.f t (x (r w))) (F.f t (x (r w'))) < F.f t (x (r m)))
    (hoff : 0 < ⟪F.N t, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ *
          ⟪F.N t, cross (x (r (a + 1)) - x (r a)) (x (r w') - x (r a))⟫ ∨
      0 < ⟪F.N t, cross (x (r w') - x (r w)) (x (r a) - x (r w))⟫ *
          ⟪F.N t, cross (x (r w') - x (r w)) (x (r (a + 1)) - x (r w))⟫) :
    IsRupert (univ.image x) := by
  classical
  set n := F.N t with hn
  have Nsub : ∀ i j : Fin N, ⟪n, x i - x j⟫ = F.f t (x i) - F.f t (x j) := F.inner_sub t
  have fA : F.f t (x (r a)) = 0 := F.zero t _ hA
  have fB : F.f t (x (r (a + 1))) = 0 := F.zero t _ hB
  have fw : F.f t (x (r w)) < 0 := F.neg t _ hwS
  have fw' : F.f t (x (r w')) < 0 := F.neg t _ hw'S
  set M : Finset ℝ³ := ((S t).filter (fun q => ∀ j, q ≠ r j)).image x
  have hle : ∀ z ∈ univ.image x, ⟪n, z⟫ ≤ ⟪n, x (r a)⟫ := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := mem_image.mp hz
    have := Nsub j (r a)
    rw [inner_sub_right, fA] at this
    linarith [F.le t j]
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
  have hn0 : n ≠ 0 := by
    intro h0
    have := Nsub (r w) (r a)
    rw [h0, inner_zero_left, fA] at this
    linarith
  have hlow' : ∀ m, m ≠ w → m ≠ w' → min ⟪n, x (r w)⟫ ⟪n, x (r w')⟫ < ⟪n, x (r m)⟫ := by
    intro m hm hm'
    have ew := Nsub (r w) (r a)
    have ew' := Nsub (r w') (r a)
    have em := Nsub (r m) (r a)
    rw [inner_sub_right, fA, sub_zero] at ew ew' em
    have hmin : min ⟪n, x (r w)⟫ ⟪n, x (r w')⟫ =
        min (F.f t (x (r w))) (F.f t (x (r w'))) + ⟪n, x (r a)⟫ := by
      rw [show ⟪n, x (r w)⟫ = F.f t (x (r w)) + ⟪n, x (r a)⟫ by linarith,
        show ⟪n, x (r w')⟫ = F.f t (x (r w')) + ⟪n, x (r a)⟫ by linarith, min_add_add_right]
    rw [hmin]
    by_cases hmS : r m ∈ S t
    · have fm0 : F.f t (x (r m)) = 0 := F.zero t _ hmS
      have : min (F.f t (x (r w))) (F.f t (x (r w'))) < 0 := lt_of_le_of_lt (min_le_left _ _) fw
      linarith
    · have hlt := hlow m hm hm' hmS
      linarith
  refine isRupert_faceChord_pair (M := M) hk (fun i => x (r i))
    (fun i => mem_image_of_mem x (mem_univ _)) hle rfl hB_inner hnu hρ hcyc ?_ hM hinj hz hn0 hlow' hoff
  intro y hy hyM hyc i
  obtain ⟨q, -, rfl⟩ := mem_image.mp hy
  have hq_not_r : ∀ j, q ≠ r j := fun j hj => hyc j (by rw [hj])
  have hq_not_S : q ∉ S t := by
    intro hqS
    apply hyM
    rw [mem_image]
    exact ⟨q, mem_filter.mpr ⟨hqS, hq_not_r⟩, rfl⟩
  exact hin q hq_not_S hq_not_r i

end FaceChord
end Minimality
