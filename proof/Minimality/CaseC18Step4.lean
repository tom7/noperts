module

public import Minimality.CaseC18VSlide
public import Minimality.DepthSepTorque
public import Minimality.SlideDS

@[expose] public section

/-!
# Type 18: `V` on the hyperplane `ClassH`, Theorem 27.41 Step 4 (stage M6)

The summary and the open special position are in the comment at the end.

Setting.  Labels `(v, xa, m1+, m1-, xb, m2+, m2-) = (5, 3, 0, 6, 4, 1, 2)`.  On `ClassH` the
perpendicular from `xb` to the line `m1+ m1-` is horizontal at `uV`, so `F1`'s circle has a persistent
double normal.  Step 4 slides along `Δ = 014`'s circle instead: `u_η = uV + η eD`,
`eD = m1+ - xb` (the sign that shows `v`, hides `xa`).  `m2+` is `Δ`'s middle, hidden, exactly:
`m2+ = (1 - s') m1+ + s' xb - u_η`, `s' = sp - η`.  The rim of `conv(V - {m2+})` at `u_η` is
`(m1+, v, m1-, m2-, xb)` (rim `N4`, `D2p < 0`) or `(m1+, v, m1-, xb)` (rim `Nt`, `D2p > 0`).
At `η = 0` the antipodal corner `xb` and the edge `e` of the chain `m1+, v, m1-` that crosses the
level of `xb` form a depth-separated pair; by `isRupert_of_chordView_torque` it suffices that the
torque of this pair is nonzero for small `η`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Generic part (space form of the torque) -/

/-- The torque of the parallel pair `(e, c)`, `e = [x a, x (a+1)]`, at the view `u`, in space:
`⟪x c - q, d_e⟫`, `d_e = x (a+1) - x a`, `q` the point of `e` at depth `⟪·, u⟫ = ⟪x c, u⟫`.  Invariant
under `u ↦ r u` (`r ≠ 0`). -/
noncomputable def torque3 {k : ℕ} (x : ZMod k → ℝ³) (u : ℝ³) (a c : ZMod k) : ℝ :=
  ⟪x c - (x a + (⟪x c - x a, u⟫ / ⟪x (a + 1) - x a, u⟫) • (x (a + 1) - x a)), x (a + 1) - x a⟫

/-- The screen torque of the rotated polygon is `torque3` (a rotation preserves inner products;
the vertical component of `R (x c - q)` is `⟪x c - q, u⟫ / r = 0`). -/
theorem pairTorque_rot_eq {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ}
    (hr : 0 < r) (hRu : R.toEuclideanLin u = r • ez) {k : ℕ} (x : ZMod k → ℝ³) (a c : ZMod k)
    (hden : ⟪x (a + 1) - x a, u⟫ ≠ 0) :
    pairTorque (fun i => proj_xy (R.toEuclideanLin (x i))) (fun i => (R.toEuclideanLin (x i)) 2) a c
      = torque3 x u a c := by
  have hdepth := depth_rot hR hr.ne' hRu
  set d := x (a + 1) - x a with hd
  set t : ℝ := ⟪x c - x a, u⟫ / ⟪d, u⟫ with ht
  have htd : t * ⟪d, u⟫ = ⟪x c - x a, u⟫ := by rw [ht]; field_simp
  have hz : ((R.toEuclideanLin (x c)) 2 - (R.toEuclideanLin (x a)) 2) /
      ((R.toEuclideanLin (x (a + 1))) 2 - (R.toEuclideanLin (x a)) 2) = t := by
    simp only [hdepth]
    have : r⁻¹ * ⟪x (a + 1), u⟫ - r⁻¹ * ⟪x a, u⟫ = r⁻¹ * ⟪d, u⟫ := by
      rw [hd, inner_sub_left]; ring
    have h2 : r⁻¹ * ⟪x c, u⟫ - r⁻¹ * ⟪x a, u⟫ = r⁻¹ * ⟪x c - x a, u⟫ := by
      rw [inner_sub_left]; ring
    rw [this, h2, ht]
    field_simp
  unfold pairTorque torque3
  rw [hz]
  set w := x c - (x a + t • d) with hw
  have hproj : proj_xy (R.toEuclideanLin w) =
      proj_xy (R.toEuclideanLin (x c)) - (proj_xy (R.toEuclideanLin (x a)) +
        t • (proj_xy (R.toEuclideanLin (x (a + 1))) - proj_xy (R.toEuclideanLin (x a)))) := by
    rw [hw, hd]
    simp only [map_sub, map_add, map_smul, proj_xy_sub', proj_xy_add', proj_xy_smul']
  have hprojd : proj_xy (R.toEuclideanLin d) =
      proj_xy (R.toEuclideanLin (x (a + 1))) - proj_xy (R.toEuclideanLin (x a)) := by
    rw [hd]; simp only [map_sub, proj_xy_sub']
  rw [← hproj, ← hprojd]
  have hw2 : (R.toEuclideanLin w) 2 = 0 := by
    rw [hdepth, hw, inner_sub_left, inner_add_left, real_inner_smul_left]
    have : ⟪x c - x a, u⟫ = ⟪x c, u⟫ - ⟪x a, u⟫ := inner_sub_left _ _ _
    rw [← htd] at this
    rw [show ⟪x c, u⟫ - (⟪x a, u⟫ + t * ⟪d, u⟫) = 0 by linarith]; simp
  rw [← inner_toEuclideanLin_SO3 hR]
  have := inner_proj_xy_of_horizontal hw2 (R.toEuclideanLin d)
  exact this

/-- `DepthSepAt` (the first conjunct, `c` strictly farthest from the line of `e`) gives
`PairInterior` of the screen polygon: both neighbours of `c` have `⟪n_e, ·⟫` larger. -/
theorem pairInterior_of_depthSepAt {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ}
    (hr : 0 < r) (hRu : R.toEuclideanLin u = r • ez) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³)
    (hk : 3 ≤ k)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    {a c : ZMod k} (hds : DepthSepAt x u a c) :
    PairInterior (fun i => proj_xy (R.toEuclideanLin (x i))) a c := by
  classical
  obtain ⟨hn, hz⟩ := hds
  have hc1 : c + 1 ≠ c := by
    intro h
    have : Fact (1 < k) := ⟨by omega⟩
    have h1 : c + 1 - c = c - c := by rw [h]
    simp at h1
  have hc2 : c - 1 ≠ c := by
    intro h
    have : Fact (1 < k) := ⟨by omega⟩
    have h1 : c - 1 - c = c - c := by rw [h]
    simp at h1
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
  have hpos := hcyc a c hca hca1
  have key : ∀ j, j ≠ c → 0 < ⟪outNormal (proj_xy (R.toEuclideanLin (x a)))
      (proj_xy (R.toEuclideanLin (x (a + 1)))),
      proj_xy (R.toEuclideanLin (x j)) - proj_xy (R.toEuclideanLin (x c))⟫ := by
    intro j hj
    have h1 := hn j hj
    have hneg : det3 (x (a + 1) - x a) (x j - x c) u < 0 := neg_of_mul_neg_left h1 hpos.le
    rw [inner_outNormal, proj_rot_sub, proj_rot_sub]
    have e := cross2_proj_rot hR hRu (x (a + 1) - x a) (x j - x c)
    rw [← proj_rot_sub, ← proj_rot_sub] at e
    have : cross2 (proj_xy (R.toEuclideanLin (x (a + 1))) - proj_xy (R.toEuclideanLin (x a)))
        (proj_xy (R.toEuclideanLin (x j)) - proj_xy (R.toEuclideanLin (x c))) < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hr.le hh]
    rw [proj_rot_sub, proj_rot_sub] at this
    linarith
  exact ⟨key _ hc1, key _ hc2⟩

/-- **The torque is nonzero along the slide if it is at `u₀`** (continuity: the denominator
`⟪x (a+1) - x a, u₀⟫` is nonzero). -/
theorem eventually_torque3_ne_zero {k : ℕ} (x : ZMod k → ℝ³) (u₀ e : ℝ³) (a c : ZMod k)
    (hden : ⟪x (a + 1) - x a, u₀⟫ ≠ 0) (h0 : torque3 x u₀ a c ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪x (a + 1) - x a, u₀ + t • e⟫ ≠ 0 ∧ torque3 x (u₀ + t • e) a c ≠ 0 := by
  have hlin : ∀ l : ℝ³, ∀ t : ℝ, ⟪l, u₀ + t • e⟫ = ⟪l, u₀⟫ + t * ⟪l, e⟫ := by
    intro l t; rw [inner_add_right, real_inner_smul_right]
  have hden' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪x (a + 1) - x a, u₀ + t • e⟫ ≠ 0 := by
    have hc : Continuous fun t : ℝ => ⟪x (a + 1) - x a, u₀ + t • e⟫ := by fun_prop
    exact (hc.continuousAt.eventually (isOpen_ne.mem_nhds
      (show ⟪x (a + 1) - x a, u₀ + (0 : ℝ) • e⟫ ≠ 0 by simpa using hden))).filter_mono
      nhdsWithin_le_nhds
  have hτ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), torque3 x (u₀ + t • e) a c ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ => torque3 x (u₀ + t • e) a c) 0 := by
      unfold torque3
      have : ContinuousAt (fun t : ℝ => ⟪x c - x a, u₀ + t • e⟫ / ⟪x (a + 1) - x a, u₀ + t • e⟫) 0 := by
        apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · simpa using hden
      fun_prop
    exact (hc.eventually (isOpen_ne.mem_nhds (by simpa using h0))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hden', hτ'] with t h1 h2 using ⟨h1, h2⟩

theorem torque3_smul {k : ℕ} (x : ZMod k → ℝ³) (u : ℝ³) (a c : ZMod k) {ε : ℝ} (hε : ε ≠ 0) :
    torque3 x (ε • u) a c = torque3 x u a c := by
  unfold torque3
  simp only [real_inner_smul_right]
  rw [mul_div_mul_left _ _ hε]

/-- **Proposition 8.8 at a view, depth-separated with nonzero torque** (no `pairDirs`/`NoFeet`
hypothesis: `isRupert_of_chordViewG` with the `DepthSepAt` branch and `hnd` replaced by the torque).
Proof: `exists_rotation_to_ez_pos`, `isDepthSeparatedPair_of_depthSepAt`, `pairInterior_of_depthSepAt`
(below), `pairTorque_rot_eq` (below), `isRupert_of_chords_depthSeparated_torque`; the first five
hypotheses are those of `isRupert_of_chordViewG` (~80 lines of copy). -/
theorem isRupert_of_chordView_torque (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M) (hk : 3 ≤ k)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    {a c : ZMod k} (hds : DepthSepAt x u a c) (hτ : torque3 x u a c ≠ 0)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth := depth_rot hR hr.ne' hRu
  have hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))) := by
    intro y hy hyM hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyx i)
  have hds' := isDepthSeparatedPair_of_depthSepAt hR hr hRu x hk hcyc hds
  have hint := pairInterior_of_depthSepAt hR hr hRu x hk hcyc hds
  have hden : ⟪x (a + 1) - x a, u⟫ ≠ 0 := by
    intro h0
    have hz := hint.depth_between hds'
    simp only [hdepth] at hz
    rw [inner_sub_left] at h0
    have e : ⟪x (a + 1), u⟫ = ⟪x a, u⟫ := by linarith
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [e] at h2 <;> linarith
  have hτ' : pairTorque (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c ≠ 0 := by
    rw [pairTorque_rot_eq hR hr hRu x a c hden]; exact hτ
  exact isRupert_of_chords_depthSeparated_torque V M R hR hr hRu x hxV hxM hp hin hds' hint hτ' hM

end Minimality

/-! ### Frame form of the view theorem -/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09 Minimality.CaseC20
open scoped RealInnerProductSpace Topology

/-- The pentagon `c0 c1 c2 c3 c4` as a 5-cycle. -/
def pent {α : Type*} (c0 c1 c2 c3 c4 : α) : ZMod 5 → α := ![c0, c1, c2, c3, c4]

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- **`rupert_vertex_or_rim` with the torque of a depth-separated pair** instead of `hz` and `hnd`:
the rim `x ∘ c` has a `DepthSepAt` pair `(a, c₀)` at `fvC u` (strict, orientation-free, so the sign `ε`
of `rupert_vertex_or_rim` is harmless, `DepthSepAt.neg`) and nonzero `torque3` (scale invariant).
Proof: copy of `rupert_vertex_or_rim` replacing the last call by `isRupert_of_chordView_torque`
(~120 lines). -/
theorem rupert_vertex_torque (hx : Function.Injective x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (M : Finset (Fin 7)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : C3)
    (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0) (hMc : ∀ m ∈ M, ∀ i, m ≠ c i)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, j' ∉ M → (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    {a c₀ : ZMod k} (hds : DepthSepAt (fun i => x (c i)) (F.fvC u) a c₀)
    (hτ : torque3 (fun i => x (c i)) (F.fvC u) a c₀ ≠ 0)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.ptC m).x = (F.ptC (c i)).x + s * ((F.ptC (c (i + 1))).x - (F.ptC (c i)).x) + δ * u.x ∧
      (F.ptC m).y = (F.ptC (c i)).y + s * ((F.ptC (c (i + 1))).y - (F.ptC (c i)).y) + δ * u.y ∧
      (F.ptC m).z = (F.ptC (c i)).z + s * ((F.ptC (c (i + 1))).z - (F.ptC (c i)).z) + δ * u.z) :
    IsRupert (Finset.univ.image x) := by
  classical
  set u0 : ℝ³ := F.fvC u with hu0def
  have hκ := F.kap_ne
  set t := σ * F.kap with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hu0 : u0 ≠ 0 := by
    intro h0
    have := F.coord_zero (a := u.x) (b := u.y) (c := u.z) (by exact h0)
    rcases hu with h | h | h
    · exact h this.1
    · exact h this.2.1
    · exact h this.2.2
  have hu' : ε • u0 ≠ 0 := by
    intro h0
    rcases hεs with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hu0 h0
  have hconv : ∀ a b : C3, 0 < σ * Dc a b u → 0 < det3 (F.fvC a) (F.fvC b) (ε • u0) := by
    intro a b h
    have hk2 : 0 < F.kap ^ 2 := by positivity
    rw [det3_smul_right, hu0def, F.det3_fvC]
    refine sgn_pos t _ ?_
    have := mul_pos hk2 h
    calc 0 < F.kap ^ 2 * (σ * Dc a b u) := this
      _ = t * (F.kap * Dc a b u) := by rw [ht]; ring
  have hds' : DepthSepAt (fun i => x (c i)) (ε • u0) a c₀ := by
    rcases hεs with h | h
    · rw [h, one_smul]; exact hds
    · rw [h, neg_one_smul]; exact hds.neg
  have hτ' : torque3 (fun i => x (c i)) (ε • u0) a c₀ ≠ 0 := by
    have hε0 : ε ≠ 0 := by rcases hεs with h | h <;> rw [h] <;> norm_num
    rw [torque3_smul _ _ _ _ hε0]; exact hτ
  refine isRupert_of_chordView_torque (Finset.univ.image x) (M.image x) (ε • u0) hu' (k := k)
    (fun i => x (c i)) (fun i => Finset.mem_image_of_mem x (Finset.mem_univ _)) ?_ hk ?_ ?_ hds' hτ' ?_
  · intro i hi
    obtain ⟨m, hm, hmi⟩ := Finset.mem_image.mp hi
    exact hMc m hm i (hx hmi)
  · intro i j hi hj
    show 0 < det3 (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) (ε • u0)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hcyc i j hi hj)
  · intro y hy hyM hyx i
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hy
    show 0 < det3 (x (c (i + 1)) - x (c i)) (x j' - x (c i)) (ε • u0)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hrest j' (fun h => hyM (Finset.mem_image_of_mem x h))
      (fun jj h => hyx jj (by simp [h])) i)
  · intro m hm
    obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨i, s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hM m0 hm0
    refine ⟨i, s, ε * δ, hs0, hs1, ?_, ?_⟩
    · rcases hεs with h | h <;> rw [h] <;> simp [hδ]
    · have key : F.fvC ((F.ptC m0).sub (F.ptC (c i))) =
          s • F.fvC ((F.ptC (c (i + 1))).sub (F.ptC (c i))) + δ • u0 := by
        rw [← F.fvC_lin ((F.ptC (c (i + 1))).sub (F.ptC (c i))) u s δ]
        congr 1
        simp only [C3.sub]
        congr 1 <;> linarith
      rw [← F.x_sub, ← F.x_sub] at key
      show x m0 = x (c i) + s • (x (c (i + 1)) - x (c i)) + (ε * δ) • (ε • u0)
      rw [smul_smul, show ε * δ * ε = δ * (ε * ε) by ring, hεε, mul_one]
      have : x m0 = x (c i) + (x m0 - x (c i)) := by abel
      rw [this, key]; abel

end Frame7

/-! ### Type 18: the slide on `Δ`'s circle -/

theorem Dc_slide (a b u e : C3) (η : ℝ) :
    Dc a b (C3.slide u e η) = Dc a b u + η * Dc a b e := by
  simp only [Dc, C3.slide]; ring

/-- A test that is positive at `u`, or zero with positive derivative along `e`, is positive for small
`η > 0`. -/
theorem PS_ev' (u e a b : C3) (h : 0 < Dc a b u ∨ (Dc a b u = 0 ∧ 0 < Dc a b e)) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), PS 1 (C3.slide u e η) a b := by
  filter_upwards [eventually_pos_affine (A := Dc a b u) (B := Dc a b e) h] with η hη
  unfold PS; rw [one_mul, Dc_slide]; exact hη

theorem zmod5_cases (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide

theorem zmod5_add_one : (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧
    (3 : ZMod 5) + 1 = 4 ∧ (4 : ZMod 5) + 1 = 0 := by decide

section pent
variable {α : Type*} (c0 c1 c2 c3 c4 : α)
theorem pent_0 : pent c0 c1 c2 c3 c4 0 = c0 := rfl
theorem pent_1 : pent c0 c1 c2 c3 c4 1 = c1 := rfl
theorem pent_2 : pent c0 c1 c2 c3 c4 2 = c2 := rfl
theorem pent_3 : pent c0 c1 c2 c3 c4 3 = c3 := rfl
theorem pent_4 : pent c0 c1 c2 c3 c4 4 = c4 := rfl
end pent

namespace Shape18
variable (S : Shape18)

/-- The slide direction on `Δ = 014`'s circle: `m1+ - xb`, in frame coordinates.  This sign shows `v`
and hides `xa`: for the edge `[m1+, v]` and the corner `m1-` the test is
`Dc (v - m1+) (m1- - m1+) eD = (hp tm + tp hm)` (> 0), and for `xa` it is `hp > 0`. -/
def eD : C3 := ⟨S.tp, -1, S.hp⟩

end Shape18

namespace Shape18
variable (S : Shape18)

end Shape18

namespace Shape18
variable (S : Shape18)

/-- Splitting `xa` over the chord at `uV`: tests of `xa` are convex combinations of those of `m1±`. -/
theorem Dc_xa_split (E Q : C3) (s δ : ℝ)
    (e1 : 1 = S.tp + s * (S.tm - S.tp) + δ * S.uV.x)
    (e2 : 0 = S.hp + s * (-S.hm - S.hp) + δ * S.uV.z) :
    Dc E ((⟨1, 0, 0⟩ : C3).sub Q) S.uV =
      (1 - s) * Dc E ((⟨S.tp, 0, S.hp⟩ : C3).sub Q) S.uV +
        s * Dc E ((⟨S.tm, 0, -S.hm⟩ : C3).sub Q) S.uV := by
  simp only [Shape18.uV] at e1 e2
  simp only [Dc, C3.sub, Shape18.uV]
  linear_combination (-E.y * (-S.hp * S.sp + S.hp - S.kp)) * e1 +
    (E.y * (-S.sp * S.tp + S.tp)) * e2

end Shape18

namespace Shape18
variable (S : Shape18)

end Shape18

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- `DepthSepAt` of a rim from its frame data (the determinants are `kap · Dc`, the depths differ
from `GG` by a constant). -/
theorem depthSepAt_of_frame {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (u : C3) (a c0 : ZMod k)
    (h1 : ∀ j, j ≠ c0 →
      Dc ((F.ptC (c (a + 1))).sub (F.ptC (c a))) ((F.ptC (c j)).sub (F.ptC (c c0))) u *
        Dc ((F.ptC (c (a + 1))).sub (F.ptC (c a))) ((F.ptC (c c0)).sub (F.ptC (c a))) u < 0)
    (h2 : ((∀ s : ℕ, 0 < s → s ≤ (a - c0).val →
          F.GG (F.ptC (c c0)) u < F.GG (F.ptC (c (c0 + s))) u) ∧
        ∀ s : ℕ, (a - c0).val < s → s < k →
          F.GG (F.ptC (c (c0 + s))) u < F.GG (F.ptC (c c0)) u) ∨
      ((∀ s : ℕ, 0 < s → s ≤ (a - c0).val →
          F.GG (F.ptC (c (c0 + s))) u < F.GG (F.ptC (c c0)) u) ∧
        ∀ s : ℕ, (a - c0).val < s → s < k →
          F.GG (F.ptC (c c0)) u < F.GG (F.ptC (c (c0 + s))) u)) :
    DepthSepAt (fun i => x (c i)) (F.fvC u) a c0 := by
  have key : ∀ i j : ZMod k, ⟪x (c i), F.fvC u⟫ < ⟪x (c j), F.fvC u⟫ ↔
      F.GG (F.ptC (c i)) u < F.GG (F.ptC (c j)) u := by
    intro i j
    rw [F.inner_x_fvC, F.inner_x_fvC]
    constructor <;> intro h <;> linarith
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h1 j hj
    show det3 (x (c (a + 1)) - x (c a)) (x (c j) - x (c c0)) (F.fvC u) *
      det3 (x (c (a + 1)) - x (c a)) (x (c c0) - x (c a)) (F.fvC u) < 0
    simp only [F.x_sub, F.det3_fvC]
    have hk := F.kap_ne
    nlinarith [sq_pos_of_ne_zero hk, mul_pos (sq_pos_of_ne_zero hk) (neg_pos.2 this)]
  · rcases h2 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact Or.inl ⟨fun s hs hs' => (key _ _).2 (g1 s hs hs'), fun s hs hs' => (key _ _).2 (g2 s hs hs')⟩
    · exact Or.inr ⟨fun s hs hs' => (key _ _).2 (g1 s hs hs'), fun s hs hs' => (key _ _).2 (g2 s hs hs')⟩

/-- The torque of the pair in frame coordinates. -/
theorem torque3_frame {k : ℕ} (c : ZMod k → Fin 7) (u : C3) (a c0 : ZMod k) :
    torque3 (fun i => x (c i)) (F.fvC u) a c0 =
      F.GG ((F.ptC (c c0)).sub (F.ptC (c a))) ((F.ptC (c (a + 1))).sub (F.ptC (c a))) -
        (F.GG ((F.ptC (c c0)).sub (F.ptC (c a))) u /
          F.GG ((F.ptC (c (a + 1))).sub (F.ptC (c a))) u) *
          F.GG ((F.ptC (c (a + 1))).sub (F.ptC (c a))) ((F.ptC (c (a + 1))).sub (F.ptC (c a))) := by
  unfold torque3
  set d := x (c (a + 1)) - x (c a) with hdd
  set w := x (c c0) - x (c a) with hww
  have e : x (c c0) - (x (c a) + (⟪w, F.fvC u⟫ / ⟪d, F.fvC u⟫) • d) =
      w - (⟪w, F.fvC u⟫ / ⟪d, F.fvC u⟫) • d := by rw [hww]; abel
  rw [e, inner_sub_left, real_inner_smul_left]
  have hw : w = F.fvC ((F.ptC (c c0)).sub (F.ptC (c a))) := F.x_sub _ _
  have hd : d = F.fvC ((F.ptC (c (a + 1))).sub (F.ptC (c a))) := F.x_sub _ _
  rw [hw, hd, F.inner_fvC, F.inner_fvC, F.inner_fvC, F.inner_fvC]

end Frame7

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-! The triangle rim `Nt` (`D2p > 0`): on `Δ`'s circle the rim of `conv(V - {m2+})` is the
4-cycle `(m1+, v, m1-, xb) = (0, 5, 6, 4)`; `m2-` (vertex 2) and `xa` (vertex 3) are interior. -/

end Frame18

end Minimality.CaseC18

/-!
## Summary

Paper: FEWER-FACES-PROOFS.md Theorem 27.41 Step 4 (~16932), Lemma 22.4, Theorem D.

* Generic: `torque3` (the pair's torque in space), `pairTorque_rot_eq`, `pairInterior_of_depthSepAt`,
  `eventually_torque3_ne_zero`, `isRupert_of_chordView_torque` (Proposition 8.8 at a view with a
  depth-separated pair of nonzero torque; no hypothesis on other double normals).
* `Frame7.rupert_vertex_torque`: the frame form (`rupert_vertex_or_rim` with `DepthSepAt` and the
  torque instead of robust unimodality and `NoHDNRim`), `depthSepAt_of_frame`, `torque3_frame`.
* The slide is `u_η = uV + η eD`, `eD = m1+ - xb` (it shows `v`, hides `xa`; `m2+` is hidden exactly,
  `mid_m2p_D`).  Tests: `N4D_cyc_ev`/`N4D_rest_ev` (pentagon `(m1+, v, m1-, m2-, xb)`),
  `NtD_cyc_ev`/`NtD_rest_ev` (4-cycle `(m1+, v, m1-, xb)`); at `η = 0` exactly the tests with `v` (or `xa`)
  collinear with the chord vanish, with derivative `hp tm + tp hm`, `hm tp + tm hp`, `hp`, `hm`.
* `classH_depth_trichotomy`: on `ClassH`, `(hp + hm)(dV 0 - dV 4) = hp B`, `(hp + hm)(dV 4 - dV 6) = hm B`
  with `B = A11 tp (1 - sp)(tp - tm) + g (hp + hm)(hp (1 - sp) - kp)`.  `N4D_pair`/`NtD_pair`: the pair
  (`c = xb`; `e = [m1+, v]` if `B > 0`, `e = [v, m1-]` if `B < 0`) is depth-separated at `uV` and its torque
  satisfies `torque * G(D, uV) = -a12 g hp tp kp` resp. `-a12 g hm Vp` (an identity; `ClassH` is used only
  for the depth order).  `z(m2-)` vs `z(xb)` comes from `vN4_A` and `hB`.
* `vN4_classH_rupert`, `vNt_classH_rupert`, `Vside_classH`.  The final `CaseC18Special'` and
  `Frame18.isRupert_of_not_special'` are in `CaseC18M.lean` (the section 35 versions were removed).

## The level chord

`ClassH` with `dV 0 = dV 6` (the chord `m1+ m1-` level at `uV`, hence also `xb`): there `xb` is not
strictly between `m1+` and `m1-`, `DepthSepAt` fails at `η = 0`.  For the 4-cycle rim `hA ∧ hB` exclude
it.  For the triangle rim this slide cannot remove it (the depths split at first order by
`G(·, eD)`, `G(m1- - xb, eD) = a11 tm tp - a12 (tm + tp) + a22 - g hm hp`, and `xb` need not lie between).
It is closed by Theorem LC in `CaseC18Level.lean` (`vNt_level_rupert`, a tilt along `F1`'s circle plus
`e_y`), which gives `Vside_classH_any` without the `hlev` hypothesis.
-/

end
