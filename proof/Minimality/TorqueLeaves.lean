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

/-! ### Type 24, Leaf B: rim `0 4 6 2 5` -/

namespace LeafB24

/-- The far corner of the pair rows `1 → 2` (corner `3`) and `3 → 4` (corner `2`) of the pentagon
from `hcyc` and the key row alone: no genericity (`g0`, `g4`, `h62`) is involved. -/
theorem pent_pairs {p : ZMod 5 → ℝ³} {u : ℝ³}
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u)
    (key : det3 (p 2 - p 1) (p 4 - p 3) u < 0) :
    ParPairAt p u 1 3 ∧ ParPairAt p u 3 2 := by
  have e1 : (0 : ZMod 5) + 1 = 1 := rfl
  have e2 : (1 : ZMod 5) + 1 = 2 := rfl
  have e3 : (2 : ZMod 5) + 1 = 3 := rfl
  have e4 : (3 : ZMod 5) + 1 = 4 := rfl
  have e5 : (4 : ZMod 5) + 1 = 0 := rfl
  have c01 := hcyc 0 2 (by decide) (by decide)
  have c02 := hcyc 0 3 (by decide) (by decide)
  have c03 := hcyc 0 4 (by decide) (by decide)
  have c04 := hcyc 2 0 (by decide) (by decide)
  have c05 := hcyc 4 2 (by decide) (by decide)
  have c06 := hcyc 3 0 (by decide) (by decide)
  have c07 := hcyc 1 3 (by decide) (by decide)
  have c08 := hcyc 1 4 (by decide) (by decide)
  have c09 := hcyc 3 1 (by decide) (by decide)
  have c10 := hcyc 2 4 (by decide) (by decide)
  simp only [e1, e2, e3, e4, e5] at c01 c02 c03 c04 c05 c06 c07 c08 c09 c10
  -- the R-table: every row as a bracket
  have t01 : det3 (p 1 - p 0) (p 1 - p 0) u = 0 := by simp [det3_expand]; ring
  have t02 : det3 (p 1 - p 0) (p 0 - p 0) u = 0 := by simp [det3_expand]
  have t10 : det3 (p 2 - p 1) (p 0 - p 1) u = det3 (p 1 - p 0) (p 2 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t11 : det3 (p 2 - p 1) (p 1 - p 1) u = 0 := by simp [det3_expand]
  have t12 : det3 (p 2 - p 1) (p 2 - p 1) u = 0 := by simp [det3_expand]; ring
  have t20 : det3 (p 3 - p 2) (p 0 - p 2) u = det3 (p 2 - p 0) (p 3 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t21 : det3 (p 3 - p 2) (p 1 - p 2) u = det3 (p 2 - p 1) (p 3 - p 1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t30 : det3 (p 4 - p 3) (p 0 - p 3) u = det3 (p 3 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t31 : det3 (p 4 - p 3) (p 1 - p 3) u = det3 (p 3 - p 1) (p 4 - p 1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t32 : det3 (p 4 - p 3) (p 2 - p 3) u = det3 (p 3 - p 2) (p 4 - p 2) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t41 : det3 (p 0 - p 4) (p 1 - p 4) u = det3 (p 1 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t42 : det3 (p 0 - p 4) (p 2 - p 4) u = det3 (p 2 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have t43 : det3 (p 0 - p 4) (p 3 - p 4) u = det3 (p 3 - p 0) (p 4 - p 0) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- brackets
  have s0123 : det3 (p 1 - p 0) (p 2 - p 0) u - det3 (p 1 - p 0) (p 3 - p 0) u
      + det3 (p 2 - p 0) (p 3 - p 0) u - det3 (p 2 - p 1) (p 3 - p 1) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s0124 : det3 (p 1 - p 0) (p 2 - p 0) u - det3 (p 1 - p 0) (p 4 - p 0) u
      + det3 (p 2 - p 0) (p 4 - p 0) u - det3 (p 2 - p 1) (p 4 - p 1) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s0134 : det3 (p 1 - p 0) (p 3 - p 0) u - det3 (p 1 - p 0) (p 4 - p 0) u
      + det3 (p 3 - p 0) (p 4 - p 0) u - det3 (p 3 - p 1) (p 4 - p 1) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s0234 : det3 (p 2 - p 0) (p 3 - p 0) u - det3 (p 2 - p 0) (p 4 - p 0) u
      + det3 (p 3 - p 0) (p 4 - p 0) u - det3 (p 3 - p 2) (p 4 - p 2) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have s1234 : det3 (p 2 - p 1) (p 3 - p 1) u - det3 (p 2 - p 1) (p 4 - p 1) u
      + det3 (p 3 - p 1) (p 4 - p 1) u - det3 (p 3 - p 2) (p 4 - p 2) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have gp : det3 (p 1 - p 0) (p 2 - p 0) u * det3 (p 3 - p 0) (p 4 - p 0) u
      - det3 (p 1 - p 0) (p 3 - p 0) u * det3 (p 2 - p 0) (p 4 - p 0) u
      + det3 (p 1 - p 0) (p 4 - p 0) u * det3 (p 2 - p 0) (p 3 - p 0) u = 0 := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have kk : det3 (p 2 - p 1) (p 4 - p 3) u
      = det3 (p 2 - p 1) (p 4 - p 1) u - det3 (p 2 - p 1) (p 3 - p 1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have c04' : 0 < det3 (p 2 - p 0) (p 3 - p 0) u := by rw [← t20]; exact c04
  have c05' : 0 < det3 (p 2 - p 0) (p 4 - p 0) u := by rw [← t42]; exact c05
  have c06' : 0 < det3 (p 3 - p 0) (p 4 - p 0) u := by rw [← t30]; exact c06
  have c09' : 0 < det3 (p 3 - p 1) (p 4 - p 1) u := by rw [← t31]; exact c09
  have c10' : 0 < det3 (p 3 - p 2) (p 4 - p 2) u := by exact c10
  obtain ⟨k1, k2, k3, k4, k5⟩ := pent_core _ _ _ _ _ _ _ _ _ c01 c02 c03 c04' c05' c06' c07 c08 c09'
    s0123 s0124 s0134 (d234 := det3 (p 3 - p 2) (p 4 - p 2) u) (by linarith) gp (by linarith)
  have hz : ∀ a : ℝ³, det3 a a u = 0 := fun a => by simp [det3_expand]; ring
  have hz2 : ∀ a : ℝ³, det3 a 0 u = 0 := fun a => by simp [det3_expand]
  have hdd : ∀ a : ℝ³, det3 a a u = 0 := hz
  have hd0 : ∀ a : ℝ³, det3 a 0 u = 0 := hz2
  have P1 : ∀ l, l ≠ 3 → det3 (p (1 + 1) - p 1) (p l - p 1) u
      < det3 (p (1 + 1) - p 1) (p 3 - p 1) u := by
    intro l hl
    rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
    · show det3 (p 2 - p 1) (p 0 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      linarith
    · show det3 (p 2 - p 1) (p 1 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      simp only [sub_self, hz2]; linarith
    · show det3 (p 2 - p 1) (p 2 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      simp only [hz]; linarith
    · show det3 (p 2 - p 1) (p 4 - p 1) u < det3 (p 2 - p 1) (p 3 - p 1) u
      linarith
  have P3 : ∀ l, l ≠ 2 → det3 (p (3 + 1) - p 3) (p l - p 3) u
      < det3 (p (3 + 1) - p 3) (p 2 - p 3) u := by
    intro l hl
    rcases zmod5_cases l with rfl | rfl | rfl | rfl | rfl <;> try exact absurd rfl hl
    · show det3 (p 4 - p 3) (p 0 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      linarith
    · show det3 (p 4 - p 3) (p 1 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      linarith
    · show det3 (p 4 - p 3) (p 3 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      simp only [sub_self, hz2]; linarith
    · show det3 (p 4 - p 3) (p 4 - p 3) u < det3 (p 4 - p 3) (p 2 - p 3) u
      simp only [hz]; linarith
  have pp : ∀ (a c : ZMod 5), 0 < det3 (p (a + 1) - p a) (p c - p a) u →
      (∀ l, l ≠ c → det3 (p (a + 1) - p a) (p l - p a) u
        < det3 (p (a + 1) - p a) (p c - p a) u) → ParPairAt p u a c := by
    intro a c hpos h j hj
    have e : p j - p c = (p j - p a) - (p c - p a) := by abel
    have hd : det3 (p (a + 1) - p a) (p j - p c) u
        = det3 (p (a + 1) - p a) (p j - p a) u - det3 (p (a + 1) - p a) (p c - p a) u := by
      rw [e]; simp only [det3_expand, PiLp.sub_apply]; ring
    rw [hd]
    exact mul_neg_of_neg_of_pos (by linarith [h j hj]) hpos
  exact ⟨pp 1 3 (hcyc 1 3 (by decide) (by decide)) P1,
    pp 3 2 (hcyc 3 2 (by decide) (by decide)) P3⟩

theorem rest_ev_B {x : Fin 7 → ℝ³} {u : ℝ³} (e : ℝ³)
    (hrest : ∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v ∈ Finset.univ.image x, (∀ j, v ≠ x (rimB j)) → ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (v - x (rimB i)) (u + ε • e) := by
  filter_upwards [(Filter.eventually_all_finset _).2 fun v hv => Filter.eventually_all.2 fun i =>
    ev_det_pos e (hrest v hv i)] with ε hε v hv hvp i
  obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hv
  have hm : m = 1 ∨ m = 3 := by
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := exists_rimB m hne.1 hne.2
    exact hvp j (by rw [hj])
  exact hε m (by rcases hm with rfl | rfl <;> simp) i

/-- **Leaf B, wedge `z6 < z2 < z0`, torque form**: pair (edge `4 → 6`, corner `2`); no foot rows, no
`hanti`, no `r5`. -/
theorem isRupert_leafB_04625_w1' {x : Fin 7 → ℝ³} {u e : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB j) - x (rimB i)) u)
    (hrest : ∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) u)
    (t0 : ⟪x 2, u⟫ = ⟪x 0, u⟫) (t6 : ⟪x 2, u⟫ = ⟪x 6, u⟫)
    (h4 : ⟪x 2, u⟫ < ⟪x 4, u⟫) (h5 : ⟪x 2, u⟫ < ⟪x 5, u⟫)
    (hpp : ParPairAt (fun i => x (rimB i)) u 1 3)
    (he : ⟪x 6, e⟫ < ⟪x 2, e⟫ ∧ ⟪x 2, e⟫ < ⟪x 0, e⟫)
    (hW : ⟪Wv (x 6 - x 4) (x 2 - x 4), u⟫ ≠ 0 ∨ ⟪Wv (x 6 - x 4) (x 2 - x 4), e⟫ ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  classical
  have a1 := ev_inner_lt (a := x 6) (b := x 2) (u := u) e (Or.inr ⟨t6.symm, he.1⟩)
  have a2 := ev_inner_lt (a := x 2) (b := x 0) (u := u) e (Or.inr ⟨t0, he.2⟩)
  have a3 := ev_inner_lt (a := x 0) (b := x 4) (u := u) e (Or.inl (by rw [← t0]; exact h4))
  have a4 := ev_inner_lt (a := x 0) (b := x 5) (u := u) e (Or.inl (by rw [← t0]; exact h5))
  refine isRupert_rimTilt_torque _ (by norm_num) (fun i => x (rimB i)) ?_ hu (a := 1) (c := 3)
    (ev_parPairAt e hpp) ?_
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ev_imp fun h1 => ev_imp fun h2 => ev_det_pos e (hcyc i j h1 h2))
    (rest_ev_B e hrest) hW
  · intro i; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · filter_upwards [a1.and (a2.and (a3.and a4))] with ε ⟨b1, b2, b3, b4⟩
    exact ds_B (z := fun i => ⟪x (rimB i), u + ε • e⟫) (by simpa [rimB] using b2.trans b4)
      (by simpa [rimB] using b2) (by simpa [rimB] using b2.trans b3) (by simpa [rimB] using b1)

/-- **Leaf B, wedge `z2 < z6 < z0`, torque form**: pair (edge `2 → 5`, corner `6`). -/
theorem isRupert_leafB_04625_w2' {x : Fin 7 → ℝ³} {u e : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB j) - x (rimB i)) u)
    (hrest : ∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) u)
    (t0 : ⟪x 2, u⟫ = ⟪x 0, u⟫) (t6 : ⟪x 2, u⟫ = ⟪x 6, u⟫)
    (h4 : ⟪x 2, u⟫ < ⟪x 4, u⟫) (h5 : ⟪x 2, u⟫ < ⟪x 5, u⟫)
    (hpp : ParPairAt (fun i => x (rimB i)) u 3 2)
    (he : ⟪x 2, e⟫ < ⟪x 6, e⟫ ∧ ⟪x 6, e⟫ < ⟪x 0, e⟫)
    (hW : ⟪Wv (x 5 - x 2) (x 6 - x 2), u⟫ ≠ 0 ∨ ⟪Wv (x 5 - x 2) (x 6 - x 2), e⟫ ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  classical
  have a1 := ev_inner_lt (a := x 2) (b := x 6) (u := u) e (Or.inr ⟨t6, he.1⟩)
  have a2 := ev_inner_lt (a := x 6) (b := x 0) (u := u) e (Or.inr ⟨t6.symm.trans t0, he.2⟩)
  have a3 := ev_inner_lt (a := x 0) (b := x 4) (u := u) e (Or.inl (by rw [← t0]; exact h4))
  have a4 := ev_inner_lt (a := x 0) (b := x 5) (u := u) e (Or.inl (by rw [← t0]; exact h5))
  refine isRupert_rimTilt_torque _ (by norm_num) (fun i => x (rimB i)) ?_ hu (a := 3) (c := 2)
    (ev_parPairAt e hpp) ?_
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ev_imp fun h1 => ev_imp fun h2 => ev_det_pos e (hcyc i j h1 h2))
    (rest_ev_B e hrest) hW
  · intro i; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · filter_upwards [a1.and (a2.and (a3.and a4))] with ε ⟨b1, b2, b3, b4⟩
    exact ds_B' (z := fun i => ⟪x (rimB i), u + ε • e⟫) (by simpa [rimB] using b1)
      (by simpa [rimB] using b2.trans b4) (by simpa [rimB] using b2)
      (by simpa [rimB] using b2.trans b3)

/-- **Leaf B at the orthocentre limit, from the key determinant, torque form.**
`isRupert_leafB_04625_of_det` without `r5`, `g0`, `g4`, `c2`/`h62`, `hf0`, `hfL`.  What remains: the
rim tests, the tie `z0 = z2 = z6 < z4, z5`, the key row `A > 0`, and `hang`: not both the angle of
`2 6 4` at `6` and the angle of `6 2 5` at `2` are right angles (in space).  Reason for `hang`: at
the tie, `⟪W,u⟫ = ⟪E,u⟫ ⟪x2 - x6, x6 - x4⟫` (wedge 1) resp. `⟪x6 - x2, x5 - x2⟫ ⟪E,u⟫` (wedge 2). -/
theorem isRupert_leafB_04625_of_det' {x : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB j) - x (rimB i)) u)
    (hrest : ∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) u)
    (t0 : ⟪x 2, u⟫ = ⟪x 0, u⟫) (t6 : ⟪x 2, u⟫ = ⟪x 6, u⟫)
    (h4 : ⟪x 2, u⟫ < ⟪x 4, u⟫) (h5 : ⟪x 2, u⟫ < ⟪x 5, u⟫)
    (key : det3 (x 6 - x 4) (x 5 - x 2) u < 0)
    (hang : ⟪x 2 - x 6, x 6 - x 4⟫ ≠ 0 ∨ ⟪x 6 - x 2, x 5 - x 2⟫ ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨pp1, pp3⟩ := pent_pairs (p := fun i => x (rimB i)) hcyc (by simpa [rimB] using key)
  rcases hang with h | h
  · have hd : det3 (x 2 - x 6) (x 0 - x 2) u ≠ 0 := by
      have : 0 < det3 (x 2 - x 6) (x 0 - x 6) u := hcyc 2 0 (by decide) (by decide)
      have e : det3 (x 2 - x 6) (x 0 - x 2) u = det3 (x 2 - x 6) (x 0 - x 6) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e]; exact ne_of_gt this
    obtain ⟨e, he1, he2⟩ := exists_tilt hd
    have hV : ⟪x 2 - x 4, u⟫ = ⟪x 6 - x 4, u⟫ := by
      simp only [inner_sub_left]; rw [t6]
    have hVE : ⟪x 2 - x 4, x 6 - x 4⟫ = ⟪x 2 - x 6, x 6 - x 4⟫ + ⟪x 6 - x 4, x 6 - x 4⟫ := by
      rw [← inner_add_left]; congr 1; abel
    have hEu : ⟪x 6 - x 4, u⟫ ≠ 0 := by
      simp only [inner_sub_left]; linarith
    refine isRupert_leafB_04625_w1' (e := e) hu hcyc hrest t0 t6 h4 h5 pp1 ⟨?_, ?_⟩ (Or.inl ?_)
    · rw [inner_sub_left] at he1; linarith
    · rw [inner_sub_left] at he2; linarith
    · rw [inner_Wv, hVE, hV]
      have : (⟪x 2 - x 6, x 6 - x 4⟫ + ⟪x 6 - x 4, x 6 - x 4⟫) * ⟪x 6 - x 4, u⟫
          - ⟪x 6 - x 4, x 6 - x 4⟫ * ⟪x 6 - x 4, u⟫ = ⟪x 2 - x 6, x 6 - x 4⟫ * ⟪x 6 - x 4, u⟫ := by ring
      rw [this]; exact mul_ne_zero h hEu
  · have hd : det3 (x 6 - x 2) (x 0 - x 6) u ≠ 0 := by
      have : 0 < det3 (x 2 - x 6) (x 0 - x 6) u := hcyc 2 0 (by decide) (by decide)
      have e : det3 (x 6 - x 2) (x 0 - x 6) u = -det3 (x 2 - x 6) (x 0 - x 6) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e]; exact neg_ne_zero.2 (ne_of_gt this)
    obtain ⟨e, he1, he2⟩ := exists_tilt hd
    have hV : ⟪x 6 - x 2, u⟫ = 0 := by
      simp only [inner_sub_left]; rw [t6]; ring
    have hEu : ⟪x 5 - x 2, u⟫ ≠ 0 := by
      simp only [inner_sub_left]; linarith
    refine isRupert_leafB_04625_w2' (e := e) hu hcyc hrest t0 t6 h4 h5 pp3 ⟨?_, ?_⟩ (Or.inl ?_)
    · rw [inner_sub_left] at he1; linarith
    · rw [inner_sub_left] at he2; linarith
    · rw [inner_Wv, hV]
      rw [mul_zero, sub_zero]; exact mul_ne_zero h hEu

end LeafB24
end Minimality
