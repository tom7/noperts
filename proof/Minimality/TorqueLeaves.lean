module

public import Minimality.FaceCircle
public import Minimality.LeafB24c
public import Minimality.CaseC18Step4

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Filter Topology

/-! # Torque forms of the face-circle leaf, Leaf A and Leaf B

`isRupert_of_chordView_torque` (CaseC18Step4) with `M = ∅`: the no-HDN hypothesis `NoHDNRim` is
replaced by `pairTorque ≠ 0` of the single depth-separated pair, which is `⟪W, u⟫ ≠ 0` for
`W = ⟪V,E⟫ E - |E|² V` (`E` the pair edge, `V` the far corner from its start). -/

namespace Minimality
open HDNApex LeafB24 FaceCircle

/-- The torque vector of a pair (edge `E`, corner `V` from the edge start): the pair torque at the
view `u` is `⟪Wv E V, u⟫ / ⟪E, u⟫`. -/
noncomputable def Wv (E V : ℝ³) : ℝ³ := ⟪V, E⟫ • E - ⟪E, E⟫ • V

theorem inner_Wv (E V u : ℝ³) : ⟪Wv E V, u⟫ = ⟪V, E⟫ * ⟪E, u⟫ - ⟪E, E⟫ * ⟪V, u⟫ := by
  simp only [Wv, inner_sub_left, real_inner_smul_left]

/-- **Bridge**: `torque3 · ⟪E,u⟫ = ⟪W, u⟫`. -/
theorem torque3_mul_inner {k : ℕ} (x : ZMod k → ℝ³) (u : ℝ³) (a c : ZMod k)
    (hden : ⟪x (a + 1) - x a, u⟫ ≠ 0) :
    torque3 x u a c * ⟪x (a + 1) - x a, u⟫ = ⟪Wv (x (a + 1) - x a) (x c - x a), u⟫ := by
  unfold torque3
  rw [inner_Wv]
  set E := x (a + 1) - x a
  set V := x c - x a
  have e : x c - (x a + (⟪V, u⟫ / ⟪E, u⟫) • E) = V - (⟪V, u⟫ / ⟪E, u⟫) • E := by
    simp only [V]; abel
  rw [e, inner_sub_left, real_inner_smul_left]
  field_simp

/-- A depth-separated pair has a nonconstant edge depth. -/
theorem inner_edge_ne_of_depthSepAt {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : ZMod k → ℝ³} {u : ℝ³} {a c : ZMod k}
    (hds : DepthSepAt x u a c) : ⟪x (a + 1) - x a, u⟫ ≠ 0 := by
  obtain ⟨hn, hz⟩ := hds
  have hc1 : c + 1 ≠ c := by
    intro h
    have h1 : c + 1 - c = c - c := by rw [h]
    simp at h1
    have : Fact (1 < k) := ⟨by omega⟩
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_one, ZMod.val_zero] at h2; omega
  have hca : c ≠ a := by
    rintro rfl
    have := hn (c + 1) hc1
    rw [sub_self, show det3 (x (c + 1) - x c) 0 u = 0 by simp [det3_expand], mul_zero] at this
    exact lt_irrefl _ this
  have hca1 : c ≠ a + 1 := by
    rintro rfl
    have := hn (a + 1 + 1) hc1
    rw [show det3 (x (a + 1) - x a) (x (a + 1) - x a) u = 0 by simp only [det3_expand]; ring,
      mul_zero] at this
    exact lt_irrefl _ this
  have hv0 : (a - c).val ≠ 0 := by
    intro h; exact hca (by have := (ZMod.val_eq_zero _).1 h; exact (sub_eq_zero.1 this).symm)
  have hlt : (a - c).val + 1 < k := by
    have h1 := ZMod.val_lt (a - c)
    by_contra hge
    have : (a - c).val + 1 = k := by omega
    apply hca1
    have h2 : ((a - c).val : ZMod k) + 1 = 0 := by
      have := congrArg (fun n : ℕ => (n : ZMod k)) this
      simpa using this
    rw [ZMod.natCast_zmod_val] at h2
    linear_combination -h2
  have e1 : c + (((a - c).val : ℕ) : ZMod k) = a := by
    rw [ZMod.natCast_zmod_val]; ring
  have e2 : c + (((a - c).val + 1 : ℕ) : ZMod k) = a + 1 := by
    push_cast; rw [ZMod.natCast_zmod_val]; ring
  intro h0
  have h3 : ⟪x a, u⟫ = ⟪x (a + 1), u⟫ := by
    rw [inner_sub_left] at h0; linarith
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 := h1 _ (Nat.pos_of_ne_zero hv0) le_rfl
    have a2 := h2 _ (Nat.lt_succ_self _) hlt
    rw [e1] at a1; rw [e2] at a2; linarith
  · have a1 := h1 _ (Nat.pos_of_ne_zero hv0) le_rfl
    have a2 := h2 _ (Nat.lt_succ_self _) hlt
    rw [e1] at a1; rw [e2] at a2; linarith

/-- **Theorem 8.10 at a rim view, torque form** (`M = ∅`): a depth-separated pair whose torque
vector `W` is not orthogonal to `u`; no horizontal-double-normal hypothesis. -/
theorem isRupert_of_rimView_depthSeparated_torque (V : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³) (hpV : ∀ i, p i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u)
    (hrest : ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i, 0 < det3 (p (i + 1) - p i) (v - p i) u)
    {a c : ZMod k} (hds : DepthSepAt p u a c)
    (hW : ⟪Wv (p (a + 1) - p a) (p c - p a), u⟫ ≠ 0) : IsRupert V := by
  have hden := inner_edge_ne_of_depthSepAt hk hds
  refine isRupert_of_chordView_torque V ∅ u hu p hpV (fun i => Finset.notMem_empty _) hk hcyc
    (fun y hy _ hyp i => hrest y hy hyp i) hds ?_ (fun m hm => absurd hm (Finset.notMem_empty _))
  intro h0
  apply hW
  rw [← torque3_mul_inner p u a c hden, h0, zero_mul]

theorem ev_Wv_ne {E V u e : ℝ³} (h : ⟪Wv E V, u⟫ ≠ 0 ∨ ⟪Wv E V, e⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪Wv E V, u + ε • e⟫ ≠ 0 := by
  by_cases h0 : ⟪Wv E V, u⟫ = 0
  · have he : ⟪Wv E V, e⟫ ≠ 0 := h.resolve_left (not_not.2 h0)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [inner_add_right, real_inner_smul_right, h0, zero_add]
    exact mul_ne_zero (ne_of_gt hε) he
  · have hc : ContinuousAt (fun ε : ℝ => ⟪Wv E V, u + ε • e⟫) 0 := by fun_prop
    have := hc.eventually_ne (by simpa using h0)
    exact this.filter_mono nhdsWithin_le_nhds

/-- **Tilted rim, torque form**: the pair, the rim tests and the depth separation hold eventually
along `u + ε e`; the torque vector is not orthogonal to `u` or to `e`. -/
theorem isRupert_rimTilt_torque (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³)
    (hpV : ∀ i, p i ∈ V) {u e : ℝ³} (hu0 : u ≠ 0) {a c : ZMod k}
    (hpp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ParPairAt p (u + ε • e) a c)
    (hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepZ (fun i => ⟪p i, u + ε • e⟫) a c)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (p (i + 1) - p i) (p j - p i) (u + ε • e))
    (hrest : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) (u + ε • e))
    (hW : ⟪Wv (p (a + 1) - p a) (p c - p a), u⟫ ≠ 0 ∨
      ⟪Wv (p (a + 1) - p a) (p c - p a), e⟫ ≠ 0) : IsRupert V := by
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u + ε • e ≠ 0 := by
    have hc : ContinuousAt (fun ε : ℝ => u + ε • e) 0 := by fun_prop
    exact (ContinuousAt.eventually_ne hc (by simpa using hu0)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, h0, h1, h2, h3, h4, h5⟩ :=
    (hne.and (hpp.and (hz.and (hcyc.and (hrest.and (ev_Wv_ne hW)))))).exists
  exact isRupert_of_rimView_depthSeparated_torque V _ h0 hk p hpV h3 h4 (depthSepAt_of h1 h2) h5


/-! ### Face circle -/

namespace FaceCircle

/-- `⟪W, n⟫ = -|E|² ⟪V, n⟫` when the edge `E` lies in the face `n`. -/
theorem inner_Wv_face {E V n : ℝ³} (hE : ⟪n, E⟫ = 0) :
    ⟪Wv E V, n⟫ = -(⟪E, E⟫ * ⟪V, n⟫) := by
  rw [inner_Wv, real_inner_comm n E, hE]; ring

/-- **Face-circle leaf, torque form**: `isRupert_faceCircle_ev` without `NoHDNRim`; the torque vector
`W` of the pair must not be orthogonal to `u` or to the tilt `e`. -/
theorem isRupert_faceCircle_ev' (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³)
    (hpV : ∀ i, p i ∈ V) {u e n : ℝ³} (hu0 : u ≠ 0) (hu : ⟪n, u⟫ = 0) {a c : ZMod k}
    (hA : ⟪n, p (a + 1) - p a⟫ = 0) (hD : det3 (p (a + 1) - p a) n u ≠ 0)
    (hfar : ∀ j, j ≠ c → ⟪n, p c⟫ < ⟪n, p j⟫)
    (hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepZ (fun i => ⟪p i, u + ε • e⟫) a c)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (p (i + 1) - p i) (p j - p i) (u + ε • e))
    (hrest : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) (u + ε • e))
    (hW : ⟪Wv (p (a + 1) - p a) (p c - p a), u⟫ ≠ 0 ∨
      ⟪Wv (p (a + 1) - p a) (p c - p a), e⟫ ≠ 0) : IsRupert V :=
  isRupert_rimTilt_torque V hk p hpV hu0 (ev_parPairAt e (parPairAt_of_faceCircle hk hA hu hD hfar))
    hz hcyc hrest hW

/-- **Face-circle leaf, torque form, tilt along the face normal**: no `hnd`, no `hW`: the tilt
`e = t n` (`t ≠ 0`) gives `⟪W, e⟫ = -t |E|² ⟪V, n⟫ ≠ 0` since `C` is strictly off the face. -/
theorem isRupert_faceCircle' (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³)
    (hpV : ∀ i, p i ∈ V) {u n : ℝ³} (t : ℝ) (ht : t ≠ 0) (hu0 : u ≠ 0) (hu : ⟪n, u⟫ = 0)
    {a c : ZMod k}
    (hA : ⟪n, p (a + 1) - p a⟫ = 0) (hD : det3 (p (a + 1) - p a) n u ≠ 0)
    (hfar : ∀ j, j ≠ c → ⟪n, p c⟫ < ⟪n, p j⟫)
    (hz : DepthSepZ (fun i => ⟪p i, u⟫) a c)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (p (i + 1) - p i) (p j - p i) (u + ε • t • n))
    (hrest : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) (u + ε • t • n)) : IsRupert V := by
  refine isRupert_faceCircle_ev' V hk p hpV hu0 hu hA hD hfar (ev_depthSepZ (t • n) hz) hcyc hrest
    (Or.inr ?_)
  have hn : 0 < ⟪n, n⟫ := by
    apply real_inner_self_pos.2
    rintro rfl
    apply hD; simp only [det3_expand]; simp
  have hE : 0 < ⟪p (a + 1) - p a, p (a + 1) - p a⟫ := by
    apply real_inner_self_pos.2
    intro h0
    apply hD; rw [h0]; simp only [det3_expand]; simp
  have hca : c ≠ a := by
    intro h
    have h1 := hfar (a + 1) (by
      rw [h]; intro h2
      have : (1 : ZMod k) = 0 := by simpa using h2
      have : Fact (1 < k) := ⟨by omega⟩
      have h3 := congrArg ZMod.val ‹(1 : ZMod k) = 0›
      rw [ZMod.val_one, ZMod.val_zero] at h3; omega)
    rw [h] at h1
    rw [inner_sub_right] at hA
    linarith
  have hneg : ⟪n, p c - p a⟫ < 0 := by
    rw [inner_sub_right]; linarith [hfar a (Ne.symm hca)]
  rw [real_inner_smul_right, inner_Wv_face hA, real_inner_comm n (p c - p a)]
  exact mul_ne_zero ht (neg_ne_zero.2 (mul_ne_zero hE.ne' hneg.ne))

/-! ### Type 24, Leaf A: rim `0 4 6 1 2 5` -/

/-- **Leaf A (type 24), torque form.**  `isRupert_leafA_046125` without `hfoot12` and without the
function `c`, `hanti`, `hc*` rows (only the one pair row `hpp` is used) and without the six depth
inequalities `n04 ... n61` (injectivity of the rim depths is not needed).  The foot hypothesis is
replaced by `hW`: the torque vector of (edge `1 → 2`, corner `5`) is not orthogonal to `u` or to
the tilt `e` (the hypothesis lives at the tilt: `e = 0` gives the strict leaf at `u`). The rows at `u`
persist along `u + ε e`. -/
theorem isRupert_leafA_046125' {x : Fin 7 → ℝ³} {u e : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimA (i + 1)) - x (rimA i)) (x (rimA j) - x (rimA i)) u)
    (hrest : ∀ i, 0 < det3 (x (rimA (i + 1)) - x (rimA i)) (x 3 - x (rimA i)) u)
    (r1 : ⟪x 2, u⟫ < ⟪x 5, u⟫) (r2 : ⟪x 5, u⟫ < ⟪x 1, u⟫) (r3 : ⟪x 5, u⟫ < ⟪x 4, u⟫)
    (r4 : ⟪x 5, u⟫ < ⟪x 6, u⟫) (r5 : ⟪x 5, u⟫ < ⟪x 0, u⟫)
    (hpp : ParPairAt (fun i => x (rimA i)) u 3 5)
    (hW : ⟪Wv (x 2 - x 1) (x 5 - x 1), u⟫ ≠ 0 ∨ ⟪Wv (x 2 - x 1) (x 5 - x 1), e⟫ ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  classical
  have hz : DepthSepZ (fun i => ⟪x (rimA i), u⟫) 3 5 :=
    ds_A (z := fun i => ⟪x (rimA i), u⟫) (by simpa [rimA] using r1) (by simpa [rimA] using r2)
      (by simpa [rimA] using r5) (by simpa [rimA] using r3) (by simpa [rimA] using r4)
  refine isRupert_rimTilt_torque _ (by norm_num) (fun i => x (rimA i)) ?_ hu (a := 3) (c := 5)
    (ev_parPairAt e hpp) (ev_depthSepZ e hz)
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ev_imp fun h1 => ev_imp fun h2 => ev_det_pos e (hcyc i j h1 h2)) ?_ hW
  · intro i; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · filter_upwards [Filter.eventually_all.2 fun i => ev_det_pos e (hrest i)] with ε hε v hv hvp i
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hv
    have hm : m = 3 := by
      by_contra hne
      obtain ⟨j, hj⟩ := exists_rimA m hne
      exact hvp j (by rw [hj])
    subst hm
    exact hε i

end FaceCircle

end Minimality
