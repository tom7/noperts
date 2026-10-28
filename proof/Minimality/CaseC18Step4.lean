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

/-- The pentagon tests, in terms of the shape alone. -/
theorem N4D_cyc_ev_S
    (hD2 : 0 < -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp +
      S.hm * S.sp * S.tp + S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp -
      S.kp * S.sm * S.tm - S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm)
    (hV : 0 < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      PS 1 (C3.slide S.uV S.eD η)
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩
            (i + 1)).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i))
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ j).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i)) := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have htm1 := S.tm_lt
  have hsp := S.sp_pos; have hsp1 := S.sp_lt; have hsm := S.sm_pos; have hsm1 := S.sm_lt
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have hV' : 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := hV
  have hsp' : 0 < 1 - S.sp := sub_pos.2 hsp1
  have hsm' : 0 < 1 - S.sm := sub_pos.2 hsm1
  have f1 : 0 < S.sm * S.tp * S.kp := by positivity
  have f2 : 0 < S.tp * S.kp := by positivity
  have f3 : 0 < S.sm * ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) := by positivity
  have f5 : 0 < ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp := by
    have := mul_pos hkp htp; linarith
  have f4 : 0 < S.sm * (((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp) :=
    mul_pos hsm f5
  have f6 : 0 < S.tp * (S.km * (1 - S.sp) + S.kp * (1 - S.sm)) := by positivity
  have f7 : 0 < S.km * S.tp * (1 - S.sp) := by positivity
  have f8 : 0 < S.hp * S.tm + S.hm * S.tp := by positivity
  refine eventually_forall_cycle fun i j h1 h2 => ?_
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    apply PS_ev'
    simp only [b0, b1, b2, b3, b4, pent_0, pent_1, pent_2, pent_3, pent_4, Dc, C3.sub,
      Shape18.uV, Shape18.eD]
    first
    | (left; linarith [f1, f2, f3, f4, f5, f6, f7, hD2])
    | (right; exact ⟨by ring, by linarith [f8]⟩)

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

theorem N4D_rest_ev_S
    (hD2 : 0 < -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp +
      S.hm * S.sp * S.tp + S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp -
      S.kp * S.sm * S.tm - S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm)
    (hV : 0 < S.Vp) (hW : S.Wp < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 5,
      PS 1 (C3.slide S.uV S.eD η)
        ((pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩
            (i + 1)).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (pent (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i)) := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have htm1 := S.tm_lt
  have hsp := S.sp_pos; have hsp1 := S.sp_lt; have hsm := S.sm_pos; have hsm1 := S.sm_lt
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have hV' : 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := hV
  have hsp' : 0 < 1 - S.sp := sub_pos.2 hsp1
  have hsm' : 0 < 1 - S.sm := sub_pos.2 hsm1
  have f5 : 0 < ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp := by
    have := mul_pos hkp htp; linarith
  have f4 : 0 < S.sm * (((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp) :=
    mul_pos hsm f5
  have f6 : 0 < S.tp * (S.km * (1 - S.sp) + S.kp * (1 - S.sm)) := by positivity
  obtain ⟨s, δ, hs0, hs1, -, e1, e2⟩ := S.mid_xa hV hW
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  refine eventually_all.2 fun i => ?_
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · apply PS_ev'
    simp only [b0, pent_0, pent_1]
    right
    exact ⟨by simp only [Dc, C3.sub, Shape18.uV]; ring,
      by simp only [Dc, C3.sub, Shape18.eD]; linarith⟩
  · apply PS_ev'
    simp only [b1, pent_1, pent_2]
    right
    exact ⟨by simp only [Dc, C3.sub, Shape18.uV]; ring,
      by simp only [Dc, C3.sub, Shape18.eD]; linarith⟩
  · apply PS_ev'
    simp only [b2, pent_2, pent_3]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape18.uV]
    nlinarith [mul_pos hs1' f4]
  · apply PS_ev'
    simp only [b3, pent_3, pent_4]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape18.uV]
    nlinarith [mul_pos hs1' f6, mul_pos hs0 hD2]
  · apply PS_ev'
    simp only [b4, pent_4, pent_0]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape18.uV]
    nlinarith [mul_pos hs0 f5]

end Shape18

namespace Shape18
variable (S : Shape18)

theorem NtD_cyc_ev_S (hV : 0 < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      PS 1 (C3.slide S.uV S.eD η)
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ j).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hhp := S.hp_pos; have hhm := S.hm_pos
  have hkp := S.kp_pos
  have hV' : 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := hV
  have f2 : 0 < S.tp * S.kp := by positivity
  have f5 : 0 < ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp := by
    have := mul_pos hkp htp; linarith
  have f8 : 0 < S.hp * S.tm + S.hm * S.tp := by positivity
  refine eventually_forall_cycle fun i j h1 h2 => ?_
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    apply PS_ev'
    simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, Dc, C3.sub, Shape18.uV, Shape18.eD]
    first
    | (left; linarith [f2, hV', f5])
    | (right; exact ⟨by ring, by linarith [f8]⟩)

theorem NtD_rest2_ev_S
    (hD2 : 0 < S.hm * S.sm * S.sp * S.tp + S.hp * S.sm * S.sp * S.tm - S.hm * S.sm * S.tp -
      S.hm * S.sp * S.tp - S.hp * S.sm * S.tm - S.hp * S.sp * S.tm + S.km * S.sp * S.tp +
      S.kp * S.sm * S.tm + S.hm * S.tp + S.hp * S.tm - S.km * S.tp - S.kp * S.tm)
    (hV : 0 < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 4,
      PS 1 (C3.slide S.uV S.eD η)
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hhp := S.hp_pos; have hhm := S.hm_pos
  have hkp := S.kp_pos; have hsm := S.sm_pos; have hsp1 := S.sp_lt; have hsm1 := S.sm_lt
  have hkm := S.km_pos
  have hV' : 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := hV
  have hsp' : 0 < 1 - S.sp := sub_pos.2 hsp1
  have hsm' : 0 < 1 - S.sm := sub_pos.2 hsm1
  have f1 : 0 < S.sm * S.tp * S.kp := by positivity
  have f3 : 0 < S.sm * ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) := by positivity
  have f6 : 0 < S.tp * (S.km * (1 - S.sp) + S.kp * (1 - S.sm)) := by positivity
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  refine eventually_all.2 fun i => ?_
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · apply PS_ev'
    simp only [b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3, Dc, C3.sub, Shape18.uV]
    left
    linarith [f1, f3, f6, hD2]

theorem NtD_restxa_ev_S (hV : 0 < S.Vp) (hW : S.Wp < S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 4,
      PS 1 (C3.slide S.uV S.eD η)
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hhp := S.hp_pos; have hhm := S.hm_pos
  have hkp := S.kp_pos
  have hV' : 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := hV
  have f5 : 0 < ((1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm) + S.kp * S.tp := by
    have := mul_pos hkp htp; linarith
  obtain ⟨s, δ, hs0, hs1, -, e1, e2⟩ := S.mid_xa hV hW
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  refine eventually_all.2 fun i => ?_
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · apply PS_ev'
    simp only [b0, quad_0, quad_1]
    right
    exact ⟨by simp only [Dc, C3.sub, Shape18.uV]; ring,
      by simp only [Dc, C3.sub, Shape18.eD]; linarith⟩
  · apply PS_ev'
    simp only [b1, quad_1, quad_2]
    right
    exact ⟨by simp only [Dc, C3.sub, Shape18.uV]; ring,
      by simp only [Dc, C3.sub, Shape18.eD]; linarith⟩
  · apply PS_ev'
    simp only [b2, quad_2, quad_3]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape18.uV]
    nlinarith [mul_pos hs1' f5]
  · apply PS_ev'
    simp only [b3, quad_3, quad_0]
    left
    rw [S.Dc_xa_split _ _ s δ e1 e2]
    simp only [Dc, C3.sub, Shape18.uV]
    nlinarith [mul_pos hs0 f5]

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

/-- **Depth order at `uV` on `ClassH`.**  With `B = A11 tp (1 - sp) (tp - tm) + g (hp + hm) (hp (1 - sp) - kp)`
one has `dV 0 - dV 4 = hp B/(hp + hm)` and `dV 4 - dV 6 = hm B/(hp + hm)` (the foot
`Y0 = (hm m1+ + hp m1-)/(hp + hm)` of the perpendicular from `xb` has the depth of `xb`), so
`xb` is strictly between `m1+` and `m1-` unless the three depths are equal. -/
theorem classH_depth_trichotomy (hH : F.ClassH) :
    (F.dV 6 < F.dV 4 ∧ F.dV 4 < F.dV 0) ∨ (F.dV 0 < F.dV 4 ∧ F.dV 4 < F.dV 6) ∨
      (F.dV 0 = F.dV 4 ∧ F.dV 4 = F.dV 6) := by
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos
  have hux : 0 < F.S.tp * (1 - F.S.sp) := mul_pos F.S.tp_pos (sub_pos.2 F.S.sp_lt)
  set B : ℝ := F.a11 * (F.S.tp * (1 - F.S.sp)) * (F.S.tp - F.S.tm) +
    F.gg * (F.S.hp + F.S.hm) * (F.S.hp * (1 - F.S.sp) - F.S.kp) with hB
  have hH' : F.a12 * (F.S.hp + F.S.hm) = F.a11 * (F.S.tp * F.S.hm + F.S.tm * F.S.hp) := hH
  have e1 : (F.S.hp + F.S.hm) * (F.dV 0 - F.dV 4) = F.S.hp * B := by
    rw [F.dV_0, F.dV_4, hB]
    linear_combination (-(F.S.tp * (1 - F.S.sp))) * hH'
  have e2 : (F.S.hp + F.S.hm) * (F.dV 4 - F.dV 6) = F.S.hm * B := by
    rw [F.dV_6, F.dV_4, hB]
    linear_combination (F.S.tp * (1 - F.S.sp)) * hH'
  have hs : 0 < F.S.hp + F.S.hm := by linarith
  rcases lt_trichotomy B 0 with h | h | h
  · right; left
    have a1 : F.dV 0 - F.dV 4 < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le hh, mul_pos hhp (neg_pos.2 h)]
    have a2 : F.dV 4 - F.dV 6 < 0 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le hh, mul_pos hhm (neg_pos.2 h)]
    constructor <;> linarith
  · right; right
    rw [h] at e1 e2
    have a1 : F.dV 0 - F.dV 4 = 0 := by
      have := mul_eq_zero.mp (by linarith : (F.S.hp + F.S.hm) * (F.dV 0 - F.dV 4) = 0)
      rcases this with h' | h'
      · linarith
      · exact h'
    have a2 : F.dV 4 - F.dV 6 = 0 := by
      have := mul_eq_zero.mp (by linarith : (F.S.hp + F.S.hm) * (F.dV 4 - F.dV 6) = 0)
      rcases this with h' | h'
      · linarith
      · exact h'
    constructor <;> linarith
  · left
    have a1 : 0 < F.dV 0 - F.dV 4 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le (neg_nonneg.2 hh), mul_pos hhp h]
    have a2 : 0 < F.dV 4 - F.dV 6 := by
      by_contra hh; push Not at hh
      nlinarith [mul_nonneg hs.le (neg_nonneg.2 hh), mul_pos hhm h]
    constructor <;> linarith

/-- `v` is strictly shallower than `xb` at `uV`: `dV 5 = 0 < a12 · ux = dV 4`. -/
theorem dV_v_lt_xb (hV : 0 < F.S.Vp) : F.dV 5 < F.dV 4 := by
  have h5 : F.dV 5 = 0 := by simp only [dV, ptC_5, GG_eq, Shape18.uV]; ring
  have hux : 0 < F.S.tp * (1 - F.S.sp) := mul_pos F.S.tp_pos (sub_pos.2 F.S.sp_lt)
  rw [h5, F.dV_4, show -F.S.sp * F.S.tp + F.S.tp = F.S.tp * (1 - F.S.sp) by ring]
  exact mul_pos F.A12_pos hux

/-- **Exact hiding of `m2+`** (the middle over the rim side `[xb, m1+]`, index `4 → 0` of the
pentagon, and of the 4-cycle `(0, 5, 6, 4)`): `m2+ = xb + (1 - sp + η)(m1+ - xb) - u_η`, `u_η = uV + η eD`
(`Dc_m2p`: `m2+ = sp xb + (1 - sp) m1+ - uV`), so `δ = -1`, `s = 1 - sp + η ∈ (0, 1)` for small `η`. -/
theorem mid_m2p_D :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.toFrame7.ptC 1).x = (F.toFrame7.ptC 4).x +
        s * ((F.toFrame7.ptC 0).x - (F.toFrame7.ptC 4).x) + δ * (C3.slide F.S.uV F.S.eD η).x ∧
      (F.toFrame7.ptC 1).y = (F.toFrame7.ptC 4).y +
        s * ((F.toFrame7.ptC 0).y - (F.toFrame7.ptC 4).y) + δ * (C3.slide F.S.uV F.S.eD η).y ∧
      (F.toFrame7.ptC 1).z = (F.toFrame7.ptC 4).z +
        s * ((F.toFrame7.ptC 0).z - (F.toFrame7.ptC 4).z) + δ * (C3.slide F.S.uV F.S.eD η).z := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt
  filter_upwards [Ioo_mem_nhdsGT hsp] with η hη
  refine ⟨1 - F.S.sp + η, -1, by linarith [hη.1, hη.2], by linarith [hη.1, hη.2], by norm_num,
    ?_, ?_, ?_⟩ <;>
  · simp only [F.ptC_1, F.ptC_4, F.ptC_0, C3.slide, Shape18.uV, Shape18.eD]
    ring

/-- **The slide tests for the pentagon rim `(m1+, v, m1-, m2-, xb) = (0, 5, 6, 2, 4)`** (`N4`, `D2p < 0`)
along `eD`: all 15 determinant tests are strict for small `η > 0`.  At `η = 0` exactly two vanish
(`[m1+, v]` against `m1-`, `[v, m1-]` against `m1+`: `v` and the chord are screen-collinear), and the
`η`-derivative is `hp tm + tp hm > 0` resp. the same; the other 13 are strict at `η = 0` (the strict
tests of `vN4_cyc` with `v` inserted, `v` having `y = 0` like `m1±`).  Hypotheses as `vN4_pcyc`. -/
theorem N4D_cyc_ev
    (hD2 : 0 < -F.S.hm * F.S.sm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.sp * F.S.tm +
      F.S.hm * F.S.sm * F.S.tp + F.S.hm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.tm +
      F.S.hp * F.S.sp * F.S.tm - F.S.km * F.S.sp * F.S.tp - F.S.kp * F.S.sm * F.S.tm -
      F.S.hm * F.S.tp - F.S.hp * F.S.tm + F.S.km * F.S.tp + F.S.kp * F.S.tm)
    (hV : 0 < F.S.Vp) (hA1z : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp)
    (hA1 : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      PS 1 (C3.slide F.S.uV F.S.eD η)
        ((pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
            (F.toFrame7.ptC 4) (i + 1)).sub
          (pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
            (F.toFrame7.ptC 4) i))
        ((pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
            (F.toFrame7.ptC 4) j).sub
          (pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
            (F.toFrame7.ptC 4) i)) := by
  simpa only [F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_2, F.ptC_4] using F.S.N4D_cyc_ev_S hD2 hV

/-- `xa` (vertex `3`) stays strictly inside the pentagon rim `N4`: tests against all five sides are
strict for small `η > 0`; the two against `[m1+, v]`, `[v, m1-]` vanish at `η = 0` (`xa` over the chord)
and have derivative `hp`, resp. `hm`-type positive values (`xa` is on the other side of the chord
from `v`, `F1` non-realizable). -/
theorem N4D_rest_ev
    (hD2 : 0 < -F.S.hm * F.S.sm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.sp * F.S.tm +
      F.S.hm * F.S.sm * F.S.tp + F.S.hm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.tm +
      F.S.hp * F.S.sp * F.S.tm - F.S.km * F.S.sp * F.S.tp - F.S.kp * F.S.sm * F.S.tm -
      F.S.hm * F.S.tp - F.S.hp * F.S.tm + F.S.km * F.S.tp + F.S.kp * F.S.tm)
    (hV : 0 < F.S.Vp) (hA1z : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp)
    (hA1 : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm) (hW : F.S.Wp < F.S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i : ZMod 5,
      PS 1 (C3.slide F.S.uV F.S.eD η)
        ((pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
            (F.toFrame7.ptC 4) (i + 1)).sub
          (pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
            (F.toFrame7.ptC 4) i))
        ((F.toFrame7.ptC 3).sub
          (pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
            (F.toFrame7.ptC 4) i)) := by
  simpa only [F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_2, F.ptC_4, F.ptC_3] using
    F.S.N4D_rest_ev_S hD2 hV hW

/-- **The depth-separated pair of the pentagon rim at `uV`, with nonzero torque** (the heart of
Step 4).  On `ClassH`, with `xb` strictly between `m1+` and `m1-` in depth and the robust-unimodality
inequalities `hA`, `hB` of the 4-cycle `(m1+, m1-, m2-, xb)`:
* if `dV 6 < dV 4 < dV 0`: `c = xb` (index 4), `a = m1+` (index 0), `e = [m1+, v]`: chain `{m1+}` above,
  `{v, m1-, m2-}` below (`dV 5 < dV 4`, `dV 6 < dV 4`, `dV 2 < dV 4` from `hA`);
* if `dV 0 < dV 4 < dV 6`: `a = v` (index 1), `e = [v, m1-]`: chain `{m1+, v}` below, `{m1-, m2-}`
  above (`dV 4 < dV 2` from `hB`);
* the equal case contradicts `hA ∧ hB`.
The first conjunct of `DepthSepAt` is `y_j < y_c = 1` for the other rim corners (`y = 0, 0, 0, sm`).
The torque is `λ · A11 · g · (tp kp)` resp. `λ · A11 · g · Vp`, where `Y0 - q0 = λ ℓ`, `ℓ` the level
direction in `F1`'s plane (`(g uz, -A11 ux)`), `λ ≠ 0` since the lines `m1+ m1-`, `m1+ v` are distinct
and `dV 0 ≠ dV 4` (G-orthogonality of `xb - Y0` to `F1`'s plane is `ClassH`). -/
theorem N4D_pair (hH : F.ClassH) (hV : 0 < F.S.Vp)
    (hA : F.dV 0 < F.dV 6 ∨ F.dV 0 < F.dV 4 ∨ F.dV 2 < F.dV 6 ∨ F.dV 2 < F.dV 4)
    (hB : F.dV 6 < F.dV 0 ∨ F.dV 4 < F.dV 0 ∨ F.dV 6 < F.dV 2 ∨ F.dV 4 < F.dV 2) :
    ∃ a c : ZMod 5, DepthSepAt (fun i => x (pent 0 5 6 2 4 i)) (F.toFrame7.fvC F.S.uV) a c ∧
      ⟪x (pent 0 5 6 2 4 (a + 1)) - x (pent 0 5 6 2 4 a), F.toFrame7.fvC F.S.uV⟫ ≠ 0 ∧
      torque3 (fun i => x (pent 0 5 6 2 4 i)) (F.toFrame7.fvC F.S.uV) a c ≠ 0 := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos
  have hsp1 := F.S.sp_lt; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have hgg := F.g_pos
  have hsp' : 0 < 1 - F.S.sp := sub_pos.2 hsp1
  have hsm' : 0 < 1 - F.S.sm := sub_pos.2 hsm1
  have hV' : 0 < (1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) - F.S.kp * F.S.tm := hV
  have hux : 0 < F.S.tp * (1 - F.S.sp) := mul_pos htp hsp'
  have hd4 : 0 < F.dV 4 := by
    rw [F.dV_4, show -F.S.sp * F.S.tp + F.S.tp = F.S.tp * (1 - F.S.sp) by ring]
    exact mul_pos F.A12_pos hux
  have d5 : F.dV 5 = 0 := by simp only [dV, ptC_5, GG_eq, Shape18.uV]; ring
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have hT : 0 < F.S.tp * F.S.kp := mul_pos htp hkp
  have hVV : 0 < ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) - F.S.kp * F.S.tm) := hV'
  rcases F.classH_depth_trichotomy hH with ⟨h6, h0⟩ | ⟨h0, h6⟩ | ⟨e0, e6⟩
  · -- `dV 6 < dV 4 < dV 0`: `a = m1+`, `c = xb`
    have h2 : F.dV 2 < F.dV 4 := by
      rcases hA with h | h | h | h <;> first | linarith | skip
    have hv : ((0 : ZMod 5) - 4).val = 1 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (0 + 1))).sub
        (F.toFrame7.ptC (pent 0 5 6 2 4 0))) F.S.uV ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (0 + 1))).sub
          (F.toFrame7.ptC (pent 0 5 6 2 4 0))) F.S.uV = F.dV 5 - F.dV 0 := by
        simp only [b0, pent_0, pent_1, dV, C3.sub, Shape18.uV, F.ptC_0, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨0, 4, F.toFrame7.depthSepAt_of_frame (pent 0 5 6 2 4) F.S.uV 0 4 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · simp only [b0, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_4, Dc, C3.sub,
          Shape18.uV]
        nlinarith [mul_pos hT hT]
      · simp only [b0, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_4, Dc, C3.sub,
          Shape18.uV]
        nlinarith [mul_pos hT hT]
      · simp only [b0, pent_0, pent_1, pent_2, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_4, Dc,
          C3.sub, Shape18.uV]
        nlinarith [mul_pos hT hT]
      · simp only [b0, pent_0, pent_1, pent_3, pent_4, F.ptC_0, F.ptC_5, F.ptC_2, F.ptC_4, Dc,
          C3.sub, Shape18.uV]
        nlinarith [mul_pos (mul_pos hsm' hT) hT]
      · exact absurd rfl hj
    · left
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · have : s = 1 := by rw [hv] at hs1; omega
        subst this
        have e : (4 : ZMod 5) + ((1 : ℕ) : ZMod 5) = 0 := by decide
        simp only [e, pent_0, pent_4, dV, F.ptC_0, F.ptC_4] at h0 ⊢
        exact h0
      · rw [hv] at hs1
        interval_cases s
        · have e : (4 : ZMod 5) + ((2 : ℕ) : ZMod 5) = 1 := by decide
          simp only [e, pent_1, pent_4, dV, F.ptC_5, F.ptC_4] at d5 hd4 ⊢
          linarith
        · have e : (4 : ZMod 5) + ((3 : ℕ) : ZMod 5) = 2 := by decide
          simp only [e, pent_2, pent_4, dV, F.ptC_6, F.ptC_4] at h6 ⊢
          linarith
        · have e : (4 : ZMod 5) + ((4 : ℕ) : ZMod 5) = 3 := by decide
          simp only [e, pent_3, pent_4, dV, F.ptC_2, F.ptC_4] at h2 ⊢
          linarith
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 4)).sub
            (F.toFrame7.ptC (pent 0 5 6 2 4 0)))
            ((F.toFrame7.ptC (pent 0 5 6 2 4 (0 + 1))).sub (F.toFrame7.ptC (pent 0 5 6 2 4 0))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 4)).sub
            (F.toFrame7.ptC (pent 0 5 6 2 4 0))) F.S.uV /
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (0 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 6 2 4 0))) F.S.uV) *
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (0 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 6 2 4 0)))
              ((F.toFrame7.ptC (pent 0 5 6 2 4 (0 + 1))).sub (F.toFrame7.ptC (pent 0 5 6 2 4 0)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (0 + 1))).sub
            (F.toFrame7.ptC (pent 0 5 6 2 4 0))) F.S.uV =
          -(F.a12 * F.gg * F.S.hp * F.S.tp * F.S.kp) := by
        field_simp
        simp only [b0, pent_0, pent_1, pent_4, F.ptC_0, F.ptC_5, F.ptC_4, GG_eq, C3.sub,
          Shape18.uV]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * F.S.hp * F.S.tp * F.S.kp := by
        have := F.A12_pos; positivity
      linarith
  · -- `dV 0 < dV 4 < dV 6`: `a = v`, `c = xb`
    have h2 : F.dV 4 < F.dV 2 := by
      rcases hB with h | h | h | h <;> first | linarith | skip
    have hv : ((1 : ZMod 5) - 4).val = 2 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (1 + 1))).sub
        (F.toFrame7.ptC (pent 0 5 6 2 4 1))) F.S.uV ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (1 + 1))).sub
          (F.toFrame7.ptC (pent 0 5 6 2 4 1))) F.S.uV = F.dV 6 - F.dV 5 := by
        simp only [b1, pent_1, pent_2, dV, C3.sub, Shape18.uV, F.ptC_6, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨1, 4, F.toFrame7.depthSepAt_of_frame (pent 0 5 6 2 4) F.S.uV 1 4 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · simp only [b1, pent_0, pent_1, pent_2, pent_4, F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_4, Dc,
          C3.sub, Shape18.uV]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, pent_1, pent_2, pent_4, F.ptC_5, F.ptC_6, F.ptC_4, Dc, C3.sub,
          Shape18.uV]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, pent_1, pent_2, pent_4, F.ptC_5, F.ptC_6, F.ptC_4, Dc, C3.sub,
          Shape18.uV]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, pent_1, pent_2, pent_3, pent_4, F.ptC_5, F.ptC_6, F.ptC_2, F.ptC_4, Dc,
          C3.sub, Shape18.uV]
        nlinarith [mul_pos (mul_pos hsm' hVV) hVV]
      · exact absurd rfl hj
    · right
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · rw [hv] at hs1
        interval_cases s
        · have e : (4 : ZMod 5) + ((1 : ℕ) : ZMod 5) = 0 := by decide
          simp only [e, pent_0, pent_4, dV, F.ptC_0, F.ptC_4] at h0 ⊢
          exact h0
        · have e : (4 : ZMod 5) + ((2 : ℕ) : ZMod 5) = 1 := by decide
          simp only [e, pent_1, pent_4, dV, F.ptC_5, F.ptC_4] at d5 hd4 ⊢
          linarith
      · rw [hv] at hs1
        interval_cases s
        · have e : (4 : ZMod 5) + ((3 : ℕ) : ZMod 5) = 2 := by decide
          simp only [e, pent_2, pent_4, dV, F.ptC_6, F.ptC_4] at h6 ⊢
          exact h6
        · have e : (4 : ZMod 5) + ((4 : ℕ) : ZMod 5) = 3 := by decide
          simp only [e, pent_3, pent_4, dV, F.ptC_2, F.ptC_4] at h2 ⊢
          exact h2
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 4)).sub
            (F.toFrame7.ptC (pent 0 5 6 2 4 1)))
            ((F.toFrame7.ptC (pent 0 5 6 2 4 (1 + 1))).sub (F.toFrame7.ptC (pent 0 5 6 2 4 1))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 4)).sub
            (F.toFrame7.ptC (pent 0 5 6 2 4 1))) F.S.uV /
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (1 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 6 2 4 1))) F.S.uV) *
            F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (1 + 1))).sub
              (F.toFrame7.ptC (pent 0 5 6 2 4 1)))
              ((F.toFrame7.ptC (pent 0 5 6 2 4 (1 + 1))).sub (F.toFrame7.ptC (pent 0 5 6 2 4 1)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (pent 0 5 6 2 4 (1 + 1))).sub
            (F.toFrame7.ptC (pent 0 5 6 2 4 1))) F.S.uV =
          -(F.a12 * F.gg * F.S.hm * ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) -
            F.S.kp * F.S.tm)) := by
        field_simp
        simp only [b1, pent_1, pent_2, pent_4, F.ptC_5, F.ptC_6, F.ptC_4, GG_eq, C3.sub,
          Shape18.uV]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * F.S.hm * ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) -
          F.S.kp * F.S.tm) := by
        have := F.A12_pos; positivity
      linarith
  · exfalso
    rcases hA with h | h | h | h <;> rcases hB with h' | h' | h' | h' <;> linarith

/-- **`V` with the 4-cycle rim, on the hyperplane `ClassH`** (Theorem 27.41 Step 4).  The hypotheses of
`vN4_slide_rupert` with `F.ClassH` instead of `¬ F.ClassH`. -/
theorem vN4_classH_rupert (hx : Function.Injective x) (hD2 : F.S.D2p < 0) (hV : 0 < F.S.Vp)
    (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp)) (hH : F.ClassH)
    (hB : F.dV 6 < F.dV 0 ∨ F.dV 4 < F.dV 0 ∨ F.dV 6 < F.dV 2 ∨ F.dV 4 < F.dV 2) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hV' : 0 < -F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sp * F.S.tm + F.S.hm * F.S.tp +
      F.S.hp * F.S.tm - F.S.kp * F.S.tm := by unfold Shape18.Vp at hV; linarith
  have hA1z' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp := by linarith
  have hA1' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm := by linarith
  have hW : F.S.Wp < F.S.Vp := by
    unfold Shape18.Wp Shape18.Vp
    have := F.S.roof_p'
    nlinarith [mul_pos hA1z (sub_pos.2 (F.S.sp_lt)), F.S.kp_pos, F.S.tm_lt, F.S.tm_pos]
  have efv : ∀ η : ℝ, F.toFrame7.fvC (C3.slide F.S.uV F.S.eD η) =
      F.toFrame7.fvC F.S.uV + η • F.toFrame7.fvC F.S.eD := by
    intro η; simp only [Frame7.fvC, C3.slide]; module
  have hD2' : 0 < -F.S.hm * F.S.sm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.sp * F.S.tm +
      F.S.hm * F.S.sm * F.S.tp + F.S.hm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.tm +
      F.S.hp * F.S.sp * F.S.tm - F.S.km * F.S.sp * F.S.tp - F.S.kp * F.S.sm * F.S.tm -
      F.S.hm * F.S.tp - F.S.hp * F.S.tm + F.S.km * F.S.tp + F.S.kp * F.S.tm := by
    unfold Shape18.D2p at hD2; linarith
  have hAq := F.vN4_A hV
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  have hcomm : ∀ j : ZMod 5, F.toFrame7.ptC (pent 0 5 6 2 4 j) =
      pent (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 2)
        (F.toFrame7.ptC 4) j := by
    intro j; rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨a, c0, hds, hden, hτ⟩ := F.N4D_pair hH hV hAq hB
  have hpos : ∀ᶠ η in 𝓝[>] (0 : ℝ), (0 : ℝ) < η := by
    filter_upwards [self_mem_nhdsWithin] with η hη using hη
  have hev := (eventually_depthSepAt (e := F.toFrame7.fvC F.S.eD) hds).and
    (eventually_torque3_ne_zero (fun i => x (pent 0 5 6 2 4 i)) (F.toFrame7.fvC F.S.uV)
      (F.toFrame7.fvC F.S.eD) a c0 hden hτ)
  obtain ⟨η, hη0, hc, hr, hm, hds', -, hτ'⟩ :=
    (hpos.and ((F.N4D_cyc_ev hD2' hV hA1z' hA1').and
      ((F.N4D_rest_ev hD2' hV hA1z' hA1' hW).and (F.mid_m2p_D.and hev)))).exists
  refine F.toFrame7.rupert_vertex_torque hx (k := 5) (by norm_num) (pent 0 5 6 2 4) {1} 1
    (Or.inl rfl) (C3.slide F.S.uV F.S.eD η)
    (Or.inl (ne_of_gt (by simp only [C3.slide, Shape18.uV, Shape18.eD]; nlinarith [mul_pos hη0 htp]))) ?_ ?_ ?_
    (a := a) (c₀ := c0) ?_ ?_ ?_
  · intro m hm' i
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [pent_0, pent_1, pent_2, pent_3, pent_4]
  · intro i j h1 h2
    simp only [hcomm]; exact hc i j h1 h2
  · intro j' hj' hjc i
    simp only [Finset.mem_singleton] at hj'
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [pent_0]) (hjc 0)
    · exact absurd rfl hj'
    · exact absurd (by simp [pent_3]) (hjc 3)
    · simp only [hcomm]; exact hr i
    · exact absurd (by simp [pent_4]) (hjc 4)
    · exact absurd (by simp [pent_1]) (hjc 1)
    · exact absurd (by simp [pent_2]) (hjc 2)
  · rw [efv]; exact hds'
  · rw [efv]; exact hτ'
  · intro m hm'
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm
    refine ⟨4, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
      simp only [b4, pent_4, pent_0] <;> assumption

/-! The triangle rim `Nt` (`D2p > 0`): on `Δ`'s circle the rim of `conv(V - {m2+})` is the
4-cycle `(m1+, v, m1-, xb) = (0, 5, 6, 4)`; `m2-` (vertex 2) and `xa` (vertex 3) are interior. -/

theorem NtD_cyc_ev
    (hD2 : 0 < F.S.hm * F.S.sm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.sp * F.S.tm -
      F.S.hm * F.S.sm * F.S.tp - F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.tm -
      F.S.hp * F.S.sp * F.S.tm + F.S.km * F.S.sp * F.S.tp + F.S.kp * F.S.sm * F.S.tm +
      F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.km * F.S.tp - F.S.kp * F.S.tm)
    (hV : 0 < F.S.Vp) (hA1z : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp)
    (hA1 : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      PS 1 (C3.slide F.S.uV F.S.eD η)
        ((quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4)
            (i + 1)).sub
          (quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4) i))
        ((quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4) j).sub
          (quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4) i)) := by
  simpa only [F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_4] using F.S.NtD_cyc_ev_S hV

/-- `m2-` (vertex 2) and `xa` (vertex 3) stay strictly inside the 4-cycle `(m1+, v, m1-, xb)`. -/
theorem NtD_rest_ev
    (hD2 : 0 < F.S.hm * F.S.sm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.sp * F.S.tm -
      F.S.hm * F.S.sm * F.S.tp - F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.tm -
      F.S.hp * F.S.sp * F.S.tm + F.S.km * F.S.sp * F.S.tp + F.S.kp * F.S.sm * F.S.tm +
      F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.km * F.S.tp - F.S.kp * F.S.tm)
    (hV : 0 < F.S.Vp) (hA1z : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp)
    (hA1 : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm) (hW : F.S.Wp < F.S.Vp) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ j' : Fin 7, (j' = 2 ∨ j' = 3) → ∀ i : ZMod 4,
      PS 1 (C3.slide F.S.uV F.S.eD η)
        ((quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4)
            (i + 1)).sub
          (quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4) i))
        ((F.toFrame7.ptC j').sub
          (quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4) i)) := by
  filter_upwards [F.S.NtD_rest2_ev_S hD2 hV, F.S.NtD_restxa_ev_S hV hW] with η h2 h3 j' hj' i
  rcases hj' with rfl | rfl
  · simpa only [F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_4, F.ptC_2] using h2 i
  · simpa only [F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_4, F.ptC_3] using h3 i

/-- The pair for the triangle rim.  The equal-depth case `dV 0 = dV 4 = dV 6` is NOT excluded here
(no `hA`, `hB`): see the hypothesis `hlev`.  Chains: if `dV 6 < dV 4 < dV 0`, `a = m1+`, `e = [m1+, v]`,
`{m1+}` above and `{v, m1-}` below; if `dV 0 < dV 4 < dV 6`, `a = v`, `e = [v, m1-]`. -/
theorem NtD_pair (hH : F.ClassH) (hV : 0 < F.S.Vp) (hlev : F.dV 0 ≠ F.dV 6) :
    ∃ a c : ZMod 4, DepthSepAt (fun i => x (quad 0 5 6 4 i)) (F.toFrame7.fvC F.S.uV) a c ∧
      ⟪x (quad 0 5 6 4 (a + 1)) - x (quad 0 5 6 4 a), F.toFrame7.fvC F.S.uV⟫ ≠ 0 ∧
      torque3 (fun i => x (quad 0 5 6 4 i)) (F.toFrame7.fvC F.S.uV) a c ≠ 0 := by
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos
  have hsp1 := F.S.sp_lt
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos
  have hgg := F.g_pos
  have hsp' : 0 < 1 - F.S.sp := sub_pos.2 hsp1
  have hV' : 0 < (1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) - F.S.kp * F.S.tm := hV
  have hux : 0 < F.S.tp * (1 - F.S.sp) := mul_pos htp hsp'
  have hd4 : 0 < F.dV 4 := by
    rw [F.dV_4, show -F.S.sp * F.S.tp + F.S.tp = F.S.tp * (1 - F.S.sp) by ring]
    exact mul_pos F.A12_pos hux
  have d5 : F.dV 5 = 0 := by simp only [dV, ptC_5, GG_eq, Shape18.uV]; ring
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  have hT : 0 < F.S.tp * F.S.kp := mul_pos htp hkp
  have hVV : 0 < ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) - F.S.kp * F.S.tm) := hV'
  rcases F.classH_depth_trichotomy hH with ⟨h6, h0⟩ | ⟨h0, h6⟩ | ⟨e0, e6⟩
  · have hv : ((0 : ZMod 4) - 3).val = 1 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (0 + 1))).sub
        (F.toFrame7.ptC (quad 0 5 6 4 0))) F.S.uV ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (0 + 1))).sub
          (F.toFrame7.ptC (quad 0 5 6 4 0))) F.S.uV = F.dV 5 - F.dV 0 := by
        simp only [b0, quad_0, quad_1, dV, C3.sub, Shape18.uV, F.ptC_0, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨0, 3, F.toFrame7.depthSepAt_of_frame (quad 0 5 6 4) F.S.uV 0 3 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod4_cases j with rfl | rfl | rfl | rfl
      · simp only [b0, quad_0, quad_1, quad_3, F.ptC_0, F.ptC_5, F.ptC_4, Dc, C3.sub, Shape18.uV]
        nlinarith [mul_pos hT hT]
      · simp only [b0, quad_0, quad_1, quad_3, F.ptC_0, F.ptC_5, F.ptC_4, Dc, C3.sub, Shape18.uV]
        nlinarith [mul_pos hT hT]
      · simp only [b0, quad_0, quad_1, quad_2, quad_3, F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_4, Dc,
          C3.sub, Shape18.uV]
        nlinarith [mul_pos hT hT]
      · exact absurd rfl hj
    · left
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · have : s = 1 := by rw [hv] at hs1; omega
        subst this
        have e : (3 : ZMod 4) + ((1 : ℕ) : ZMod 4) = 0 := by decide
        simp only [e, quad_0, quad_3, dV, F.ptC_0, F.ptC_4] at h0 ⊢
        exact h0
      · rw [hv] at hs1
        interval_cases s
        · have e : (3 : ZMod 4) + ((2 : ℕ) : ZMod 4) = 1 := by decide
          simp only [e, quad_1, quad_3, dV, F.ptC_5, F.ptC_4] at d5 hd4 ⊢
          linarith
        · have e : (3 : ZMod 4) + ((3 : ℕ) : ZMod 4) = 2 := by decide
          simp only [e, quad_2, quad_3, dV, F.ptC_6, F.ptC_4] at h6 ⊢
          linarith
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 3)).sub
            (F.toFrame7.ptC (quad 0 5 6 4 0)))
            ((F.toFrame7.ptC (quad 0 5 6 4 (0 + 1))).sub (F.toFrame7.ptC (quad 0 5 6 4 0))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 3)).sub
            (F.toFrame7.ptC (quad 0 5 6 4 0))) F.S.uV /
            F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (0 + 1))).sub
              (F.toFrame7.ptC (quad 0 5 6 4 0))) F.S.uV) *
            F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (0 + 1))).sub
              (F.toFrame7.ptC (quad 0 5 6 4 0)))
              ((F.toFrame7.ptC (quad 0 5 6 4 (0 + 1))).sub (F.toFrame7.ptC (quad 0 5 6 4 0)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (0 + 1))).sub
            (F.toFrame7.ptC (quad 0 5 6 4 0))) F.S.uV =
          -(F.a12 * F.gg * F.S.hp * F.S.tp * F.S.kp) := by
        field_simp
        simp only [b0, quad_0, quad_1, quad_3, F.ptC_0, F.ptC_5, F.ptC_4, GG_eq, C3.sub,
          Shape18.uV]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * F.S.hp * F.S.tp * F.S.kp := by
        have := F.A12_pos; positivity
      linarith
  · have hv : ((1 : ZMod 4) - 3).val = 2 := by decide
    have hden : F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (1 + 1))).sub
        (F.toFrame7.ptC (quad 0 5 6 4 1))) F.S.uV ≠ 0 := by
      have : F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (1 + 1))).sub
          (F.toFrame7.ptC (quad 0 5 6 4 1))) F.S.uV = F.dV 6 - F.dV 5 := by
        simp only [b1, quad_1, quad_2, dV, C3.sub, Shape18.uV, F.ptC_6, F.ptC_5, GG_eq]; ring
      rw [this]; linarith
    refine ⟨1, 3, F.toFrame7.depthSepAt_of_frame (quad 0 5 6 4) F.S.uV 1 3 ?_ ?_, ?_, ?_⟩
    · intro j hj
      rcases zmod4_cases j with rfl | rfl | rfl | rfl
      · simp only [b1, quad_0, quad_1, quad_2, quad_3, F.ptC_0, F.ptC_5, F.ptC_6, F.ptC_4, Dc,
          C3.sub, Shape18.uV]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_6, F.ptC_4, Dc, C3.sub,
          Shape18.uV]
        nlinarith [mul_pos hVV hVV]
      · simp only [b1, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_6, F.ptC_4, Dc, C3.sub,
          Shape18.uV]
        nlinarith [mul_pos hVV hVV]
      · exact absurd rfl hj
    · right
      refine ⟨fun s hs hs1 => ?_, fun s hs1 hs2 => ?_⟩
      · rw [hv] at hs1
        interval_cases s
        · have e : (3 : ZMod 4) + ((1 : ℕ) : ZMod 4) = 0 := by decide
          simp only [e, quad_0, quad_3, dV, F.ptC_0, F.ptC_4] at h0 ⊢
          exact h0
        · have e : (3 : ZMod 4) + ((2 : ℕ) : ZMod 4) = 1 := by decide
          simp only [e, quad_1, quad_3, dV, F.ptC_5, F.ptC_4] at d5 hd4 ⊢
          linarith
      · rw [hv] at hs1
        interval_cases s
        have e : (3 : ZMod 4) + ((3 : ℕ) : ZMod 4) = 2 := by decide
        simp only [e, quad_2, quad_3, dV, F.ptC_6, F.ptC_4] at h6 ⊢
        exact h6
    · rw [F.toFrame7.x_sub, F.toFrame7.inner_fvC]; exact hden
    · rw [F.toFrame7.torque3_frame]
      have key : (F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 3)).sub
            (F.toFrame7.ptC (quad 0 5 6 4 1)))
            ((F.toFrame7.ptC (quad 0 5 6 4 (1 + 1))).sub (F.toFrame7.ptC (quad 0 5 6 4 1))) -
          (F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 3)).sub
            (F.toFrame7.ptC (quad 0 5 6 4 1))) F.S.uV /
            F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (1 + 1))).sub
              (F.toFrame7.ptC (quad 0 5 6 4 1))) F.S.uV) *
            F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (1 + 1))).sub
              (F.toFrame7.ptC (quad 0 5 6 4 1)))
              ((F.toFrame7.ptC (quad 0 5 6 4 (1 + 1))).sub (F.toFrame7.ptC (quad 0 5 6 4 1)))) *
          F.toFrame7.GG ((F.toFrame7.ptC (quad 0 5 6 4 (1 + 1))).sub
            (F.toFrame7.ptC (quad 0 5 6 4 1))) F.S.uV =
          -(F.a12 * F.gg * F.S.hm * ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) -
            F.S.kp * F.S.tm)) := by
        field_simp
        simp only [b1, quad_1, quad_2, quad_3, F.ptC_5, F.ptC_6, F.ptC_4, GG_eq, C3.sub,
          Shape18.uV]
        ring
      intro h
      rw [h, zero_mul] at key
      have : 0 < F.a12 * F.gg * F.S.hm * ((1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) -
          F.S.kp * F.S.tm) := by
        have := F.A12_pos; positivity
      linarith
  · exact absurd (by linarith) hlev

/-- **`V` with the triangle rim, on the hyperplane `ClassH`**, away from the level chord
`dV 0 = dV 6` (`B = 0`: `m1+, m1-, xb` level at `uV`, a codimension-2 position inside `ClassH`, closed
by Theorem LC, `vNt_level_rupert` in `CaseC18Level.lean`). -/
theorem vNt_classH_rupert (hx : Function.Injective x) (hD2 : 0 < F.S.D2p) (hV : 0 < F.S.Vp)
    (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp)) (hH : F.ClassH)
    (hlev : F.dV 0 ≠ F.dV 6) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hV' : 0 < -F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sp * F.S.tm + F.S.hm * F.S.tp +
      F.S.hp * F.S.tm - F.S.kp * F.S.tm := by unfold Shape18.Vp at hV; linarith
  have hA1z' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp := by linarith
  have hA1' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm := by linarith
  have hW : F.S.Wp < F.S.Vp := by
    unfold Shape18.Wp Shape18.Vp
    have := F.S.roof_p'
    nlinarith [mul_pos hA1z (sub_pos.2 (F.S.sp_lt)), F.S.kp_pos, F.S.tm_lt, F.S.tm_pos]
  have efv : ∀ η : ℝ, F.toFrame7.fvC (C3.slide F.S.uV F.S.eD η) =
      F.toFrame7.fvC F.S.uV + η • F.toFrame7.fvC F.S.eD := by
    intro η; simp only [Frame7.fvC, C3.slide]; module
  have hD2' : 0 < F.S.hm * F.S.sm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.sp * F.S.tm -
      F.S.hm * F.S.sm * F.S.tp - F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.tm -
      F.S.hp * F.S.sp * F.S.tm + F.S.km * F.S.sp * F.S.tp + F.S.kp * F.S.sm * F.S.tm +
      F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.km * F.S.tp - F.S.kp * F.S.tm := by
    unfold Shape18.D2p at hD2; linarith
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  have hcomm : ∀ j : ZMod 4, F.toFrame7.ptC (quad 0 5 6 4 j) =
      quad (F.toFrame7.ptC 0) (F.toFrame7.ptC 5) (F.toFrame7.ptC 6) (F.toFrame7.ptC 4) j := by
    intro j; rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨a, c0, hds, hden, hτ⟩ := F.NtD_pair hH hV hlev
  have hpos : ∀ᶠ η in 𝓝[>] (0 : ℝ), (0 : ℝ) < η := by
    filter_upwards [self_mem_nhdsWithin] with η hη using hη
  have hev := (eventually_depthSepAt (e := F.toFrame7.fvC F.S.eD) hds).and
    (eventually_torque3_ne_zero (fun i => x (quad 0 5 6 4 i)) (F.toFrame7.fvC F.S.uV)
      (F.toFrame7.fvC F.S.eD) a c0 hden hτ)
  obtain ⟨η, hη0, hc, hr, hm, hds', -, hτ'⟩ :=
    (hpos.and ((F.NtD_cyc_ev hD2' hV hA1z' hA1').and
      ((F.NtD_rest_ev hD2' hV hA1z' hA1' hW).and (F.mid_m2p_D.and hev)))).exists
  refine F.toFrame7.rupert_vertex_torque hx (k := 4) (by norm_num) (quad 0 5 6 4) {1} 1
    (Or.inl rfl) (C3.slide F.S.uV F.S.eD η)
    (Or.inl (ne_of_gt (by simp only [C3.slide, Shape18.uV, Shape18.eD]; nlinarith [mul_pos hη0 htp]))) ?_ ?_ ?_
    (a := a) (c₀ := c0) ?_ ?_ ?_
  · intro m hm' i
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]
  · intro i j h1 h2
    simp only [hcomm]; exact hc i j h1 h2
  · intro j' hj' hjc i
    simp only [Finset.mem_singleton] at hj'
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [quad_0]) (hjc 0)
    · exact absurd rfl hj'
    · simp only [hcomm]; exact hr 2 (Or.inl rfl) i
    · simp only [hcomm]; exact hr 3 (Or.inr rfl) i
    · exact absurd (by simp [quad_3]) (hjc 3)
    · exact absurd (by simp [quad_1]) (hjc 1)
    · exact absurd (by simp [quad_2]) (hjc 2)
  · rw [efv]; exact hds'
  · rw [efv]; exact hτ'
  · intro m hm'
    simp only [Finset.mem_singleton] at hm'
    subst hm'
    obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hm
    refine ⟨3, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
      simp only [b3, quad_3, quad_0] <;> assumption

/-- **The `V` side of 27.59 on `ClassH`** (the case `hH : F.ClassH` of `Vside_slide`).  For `D2p > 0`
the extra hypothesis `dV 0 ≠ dV 6` is needed here; `Vside_classH_any` (`CaseC18Level.lean`) removes it by
Theorem LC. -/
theorem Vside_classH (hx : Function.Injective x) (hVp : F.S.dp < F.S.A1 * F.S.tp)
    (h1 : F.S.am < F.S.bp) (h2 : F.S.ap < F.S.bm) (hD2 : F.S.D2p ≠ 0) (hH : F.ClassH)
    (hlev : 0 < F.S.D2p → F.dV 0 ≠ F.dV 6) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have hsp1 := F.S.sp_lt
  have hV := F.dV_pos_of hVp
  have hA1 := sub_pos.2 (F.A1_of h1)
  have hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm) := sub_pos.2 (F.zFrame.A1_of h2)
  rcases lt_or_gt_of_ne hD2 with hneg | hpos
  · rcases F.tA_or hx (F.A1_of h1) with h | ⟨f1, f2, f3, f4⟩
    · exact h
    · refine F.vN4_classH_rupert hx hneg hV hA1z hA1 hH ?_
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      rw [F.dA_0, F.dA_4] at f1
      rw [F.dV_0, F.dV_4] at c2
      have hgg : 0 < F.gg := F.g_pos
      have hroof := F.S.roof_p'
      nlinarith [mul_nonneg (mul_pos htp (sub_pos.2 hsp1)).le (sub_nonneg.2 f1),
        mul_nonneg (sub_pos.2 htp1).le (sub_nonneg.2 c2),
        mul_pos (mul_pos hgg F.S.hp_pos) (sub_pos.2 hroof)]
  · exact F.vNt_classH_rupert hx hpos hV hA1z hA1 hH (hlev hpos)

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
* `vN4_classH_rupert`, `vNt_classH_rupert`, `Vside_classH`.  `CaseC18Special'` and
  `Frame18.isRupert_of_not_special'` are in `CaseC18Level.lean`.

## The level chord

`ClassH` with `dV 0 = dV 6` (the chord `m1+ m1-` level at `uV`, hence also `xb`): there `xb` is not
strictly between `m1+` and `m1-`, `DepthSepAt` fails at `η = 0`.  For the 4-cycle rim `hA ∧ hB` exclude
it.  For the triangle rim this slide cannot remove it (the depths split at first order by
`G(·, eD)`, `G(m1- - xb, eD) = a11 tm tp - a12 (tm + tp) + a22 - g hm hp`, and `xb` need not lie between).
It is closed by Theorem LC in `CaseC18Level.lean` (`vNt_level_rupert`, a tilt along `F1`'s circle plus
`e_y`), which gives `Vside_classH_any` without the `hlev` hypothesis.
-/

end
