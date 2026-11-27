module

public import Minimality.FaceChordEdge

@[expose] public section

/-!
# The far-pair face chord with a depth-separated pair (job OSPEC7, nopert229 notes/OPENSPECIAL-STRATEGY.md)

`isRupert_faceChord_pair` (FaceChordEdge.lean) slides from a view `u` on the face circle by `isRupert_of_slideP`,
which needs injective rim depths at `u` in both of its rim branches.  The depth-separated branch does not:
`isRupert_of_slideP_uos'` (SlideE.lean) asks for injectivity only on the strictly unimodal branch.  So with a
`DepthSepAt` pair at `u` (strict, hence it persists along the slide) the chord leaf tolerates depth ties at `u`
that the pair leaves alone, e.g. a tie of two rim vertices on the same side of the separating depth.

* `injective_of_cyc`: the rim tests at `u` make the rim injective (`3 ≤ k`).
* `isRupert_faceChord_pair_ds`: `isRupert_faceChord_pair` with `DepthSepAt` in place of injective depths and
  `UniOrSep`.
* `isRupert_faceChord_fac_pair_ds`: the same on facet `t` of an `S0xFac` solid.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace FaceChord
open Minimality.H21

/-- The rim tests at `u` (every non-adjacent vertex strictly on one side of each rim edge) force an injective rim. -/
theorem injective_of_cyc {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → ℝ³) {u : ℝ³} {ρ : ℝ}
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (c (i + 1) - c i) (c j - c i) u) :
    Function.Injective c := by
  intro i j hij
  by_contra hne
  by_cases h1 : j = i + 1
  · have hi2 : i + 2 ≠ i := by
      have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) i
      simpa using this
    have hi21 : i + 2 ≠ i + 1 := by
      have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) i
      simpa using this
    have := hcyc i (i + 2) hi2 hi21
    have e : c (i + 1) - c i = 0 := by rw [← h1, ← hij, sub_self]
    rw [e] at this
    simp [det3_expand] at this
  · have := hcyc i j (Ne.symm hne) h1
    rw [← hij, sub_self] at this
    simp [det3_expand] at this

/-- **The far-pair chord leaf with a depth-separated pair.**  `isRupert_faceChord_pair` with the injective rim
depths and `UniOrSep` at `u` replaced by a `DepthSepAt` pair at `u` (rim depths may tie). -/
theorem isRupert_faceChord_pair_ds {V M : Finset ℝ³} {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → ℝ³)
    (hcV : ∀ i, c i ∈ V) {n : ℝ³} {κ : ℝ} (hle : ∀ z ∈ V, ⟪n, z⟫ ≤ κ) {a : ZMod k}
    (hA : ⟪n, c a⟫ = κ) (hB : ⟪n, c (a + 1)⟫ = κ) {u : ℝ³} (hnu : ⟪n, u⟫ = 0) {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (c (i + 1) - c i) (c j - c i) u)
    (hin : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ c j) → ∀ i,
      0 < ρ * det3 (c (i + 1) - c i) (y - c i) u)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = c a + s • (c (a + 1) - c a) + δ • u)
    (hds : ∃ a₁ c₁, DepthSepAt c u a₁ c₁) (hn0 : n ≠ 0) {w w' : ZMod k}
    (hlow : ∀ m, m ≠ w → m ≠ w' → min ⟪n, c w⟫ ⟪n, c w'⟫ < ⟪n, c m⟫)
    (hoff : 0 < ⟪n, cross (c (a + 1) - c a) (c w - c a)⟫ * ⟪n, cross (c (a + 1) - c a) (c w' - c a)⟫ ∨
      0 < ⟪n, cross (c w' - c w) (c a - c w)⟫ * ⟪n, cross (c w' - c w) (c (a + 1) - c w)⟫) :
    IsRupert V := by
  classical
  have hk2 : 2 ≤ k := by omega
  set e : ℝ³ := c (a + 1) - c a with he
  have hcinj : Function.Injective c := injective_of_cyc hk c hcyc
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
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hcross (by ext j; fin_cases j <;> simp [cross])
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
  exact isRupert_of_slideP_uos' V M u e hu0 c hcV hcM hk ρ hρ
    (fun i j h1 h2 => Or.inl (hcyc i j h1 h2)) (fun y hy hyM hyc i => Or.inl (hin y hy hyM hyc i))
    hM' (Or.inr hds) hbad

/-- **The far-pair chord leaf for an arbitrary facet, with a depth-separated pair** (`isRupert_faceChord_fac_pair`
with `DepthSepAt` at `u` in place of injective rim depths and `UniOrSep`). -/
theorem isRupert_faceChord_fac_pair_ds {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) {u : ℝ³} (hnu : ⟪F.N t, u⟫ = 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (r : ZMod k → Fin N) {a : ZMod k}
    (hA : r a ∈ S t) (hB : r (a + 1) ∈ S t) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u)
    (hin : ∀ q, q ∉ S t → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u)
    (hmid : ∀ q ∈ S t, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u)
    (hds : ∃ a₁ c₁, DepthSepAt (fun i => x (r i)) u a₁ c₁)
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
  refine isRupert_faceChord_pair_ds (M := M) hk (fun i => x (r i))
    (fun i => mem_image_of_mem x (mem_univ _)) hle rfl hB_inner hnu hρ hcyc ?_ hM hds hn0 hlow' hoff
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
