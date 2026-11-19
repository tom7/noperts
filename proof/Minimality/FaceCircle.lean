module

public import Minimality.LeafB24b

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Filter Topology

namespace Minimality
open HDNApex LeafB24

namespace FaceCircle

theorem det3_faceCircle {n a u w : ℝ³} (ha : ⟪n, a⟫ = 0) (hu : ⟪n, u⟫ = 0) :
    det3 a w u * ⟪n, n⟫ = ⟪n, w⟫ * det3 a n u := by
  simp only [det3_expand] at *
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three] at *
  simp at *
  linear_combination (-(w 0 * (n 1 * u 2 - n 2 * u 1)) - w 1 * (n 2 * u 0 - n 0 * u 2) - w 2 * (n 0 * u 1 - n 1 * u 0)) * ha + (w 0 * (n 1 * a 2 - n 2 * a 1) + w 1 * (n 2 * a 0 - n 0 * a 2) + w 2 * (n 0 * a 1 - n 1 * a 0)) * hu


/-- **Far corner from the plane distance** (LEAFA 1.1, ParPairAt form). -/
theorem parPairAt_of_faceCircle {k : ℕ} [NeZero k] (hk : 3 ≤ k) {p : ZMod k → ℝ³} {u n : ℝ³}
    {a c : ZMod k} (hA : ⟪n, p (a + 1) - p a⟫ = 0) (hu : ⟪n, u⟫ = 0)
    (hD : det3 (p (a + 1) - p a) n u ≠ 0)
    (hfar : ∀ j, j ≠ c → ⟪n, p c⟫ < ⟪n, p j⟫) : ParPairAt p u a c := by
  have hn : 0 < ⟪n, n⟫ := by
    apply real_inner_self_pos.2
    rintro rfl
    apply hD; simp only [det3_expand]; simp
  have hne : a + 1 ≠ a := by
    intro h
    have : (1 : ZMod k) = 0 := by simpa using h
    have h1 := congrArg ZMod.val this
    have : Fact (1 < k) := ⟨by omega⟩
    rw [ZMod.val_one, ZMod.val_zero] at h1; omega
  have hca : c ≠ a := by
    intro h
    have h1 := hfar (a + 1) (by rw [h]; exact hne)
    rw [h] at h1
    rw [inner_sub_right] at hA
    linarith
  have hneg : ⟪n, p c - p a⟫ < 0 := by
    rw [inner_sub_right]; linarith [hfar a (Ne.symm hca)]
  intro j hj
  have hpos : 0 < ⟪n, p j - p c⟫ := by
    rw [inner_sub_right]; linarith [hfar j hj]
  have e1 := det3_faceCircle (w := p j - p c) hA hu
  have e2 := det3_faceCircle (w := p c - p a) hA hu
  set D := det3 (p (a + 1) - p a) n u
  have hD2 : 0 < D * D := mul_self_pos.2 hD
  have : det3 (p (a + 1) - p a) (p j - p c) u * det3 (p (a + 1) - p a) (p c - p a) u * (⟪n, n⟫ * ⟪n, n⟫)
      = (D * D) * (⟪n, p j - p c⟫ * ⟪n, p c - p a⟫) := by
    calc _ = (det3 (p (a + 1) - p a) (p j - p c) u * ⟪n, n⟫) * (det3 (p (a + 1) - p a) (p c - p a) u * ⟪n, n⟫) := by ring
      _ = _ := by rw [e1, e2]; ring
  have hlt : (D * D) * (⟪n, p j - p c⟫ * ⟪n, p c - p a⟫) < 0 :=
    mul_neg_of_pos_of_neg hD2 (mul_neg_of_pos_of_neg hpos hneg)
  rw [← this] at hlt
  by_contra hge
  push Not at hge
  exact absurd hlt (not_lt.2 (mul_nonneg hge (mul_self_nonneg _)))

/-! ### Persistence along the tilt `u + ε e` -/

theorem ev_parPairAt {k : ℕ} [NeZero k] {p : ZMod k → ℝ³} {u : ℝ³} (e : ℝ³) {a c : ZMod k}
    (h : ParPairAt p u a c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ParPairAt p (u + ε • e) a c := by
  refine Filter.eventually_all.2 fun j => ev_imp fun hj => ?_
  have hc : ContinuousAt (fun ε : ℝ =>
      det3 (p (a + 1) - p a) (p j - p c) (u + ε • e) * det3 (p (a + 1) - p a) (p c - p a) (u + ε • e)) 0 := by
    simp only [det3_add_smul]; fun_prop
  have := hc.eventually_lt (continuousAt_const (y := (0 : ℝ))) (by simpa [det3_add_smul] using h j hj)
  exact this.filter_mono nhdsWithin_le_nhds

theorem ev_depthSepZ {k : ℕ} [NeZero k] {p : ZMod k → ℝ³} {u : ℝ³} (e : ℝ³) {a c : ZMod k}
    (h : DepthSepZ (fun i => ⟪p i, u⟫) a c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepZ (fun i => ⟪p i, u + ε • e⟫) a c := by
  unfold DepthSepZ at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := (Filter.eventually_all_finset (Finset.range k)).2 fun s _ =>
      (ev_imp fun h3 => ev_imp fun h4 => ev_inner_lt (a := p c) (b := p (c + s)) (u := u) e (Or.inl (h1 s h3 h4))).and
        (ev_imp fun h3 => ev_imp fun h4 => ev_inner_lt (a := p (c + s)) (b := p c) (u := u) e (Or.inl (h2 s h3 h4)))
    filter_upwards [this] with ε hε
    left
    exact ⟨fun s hs1 hs2 => (hε s (Finset.mem_range.2 (lt_of_le_of_lt hs2 (ZMod.val_lt _)))).1 hs1 hs2,
      fun s hs1 hs2 => (hε s (Finset.mem_range.2 hs2)).2 hs1 hs2⟩
  · have := (Filter.eventually_all_finset (Finset.range k)).2 fun s _ =>
      (ev_imp fun h3 => ev_imp fun h4 => ev_inner_lt (a := p (c + s)) (b := p c) (u := u) e (Or.inl (h1 s h3 h4))).and
        (ev_imp fun h3 => ev_imp fun h4 => ev_inner_lt (a := p c) (b := p (c + s)) (u := u) e (Or.inl (h2 s h3 h4)))
    filter_upwards [this] with ε hε
    right
    exact ⟨fun s hs1 hs2 => (hε s (Finset.mem_range.2 (lt_of_le_of_lt hs2 (ZMod.val_lt _)))).1 hs1 hs2,
      fun s hs1 hs2 => (hε s (Finset.mem_range.2 hs2)).2 hs1 hs2⟩

/-- **Theorem 8.10 at a small tilt of an edge-on view** (face-circle lemma; LEAFA 1.4), eventual form:
the chain `hz` only has to hold eventually along the tilt (lex ties). -/
theorem isRupert_faceCircle_ev (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³)
    (hpV : ∀ i, p i ∈ V) {u e n : ℝ³} (hu0 : u ≠ 0) (hu : ⟪n, u⟫ = 0) {a c : ZMod k}
    (hA : ⟪n, p (a + 1) - p a⟫ = 0) (hD : det3 (p (a + 1) - p a) n u ≠ 0)
    (hfar : ∀ j, j ≠ c → ⟪n, p c⟫ < ⟪n, p j⟫)
    (hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepZ (fun i => ⟪p i, u + ε • e⟫) a c)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (p (i + 1) - p i) (p j - p i) (u + ε • e))
    (hrest : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) (u + ε • e))
    (hnd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), NoHDNRim p (u + ε • e)) : IsRupert V := by
  have hpp := ev_parPairAt (a := a) (c := c) e (parPairAt_of_faceCircle hk hA hu hD hfar)
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u + ε • e ≠ 0 := by
    have hc : ContinuousAt (fun ε : ℝ => u + ε • e) 0 := by fun_prop
    exact (ContinuousAt.eventually_ne hc (by simpa using hu0)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, h0, h1, h2, h3, h4, h5⟩ := (hne.and (hpp.and (hz.and (hcyc.and (hrest.and hnd))))).exists
  exact isRupert_of_rimView_depthSeparated_rim V _ h0 hk p hpV h3 h4 (depthSepAt_of h1 h2) h5

/-- **Theorem 8.10 at a small tilt of an edge-on view**, strict chain at `u`. -/
theorem isRupert_faceCircle (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³)
    (hpV : ∀ i, p i ∈ V) {u e n : ℝ³} (hu0 : u ≠ 0) (hu : ⟪n, u⟫ = 0) {a c : ZMod k}
    (hA : ⟪n, p (a + 1) - p a⟫ = 0) (hD : det3 (p (a + 1) - p a) n u ≠ 0)
    (hfar : ∀ j, j ≠ c → ⟪n, p c⟫ < ⟪n, p j⟫)
    (hz : DepthSepZ (fun i => ⟪p i, u⟫) a c)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (p (i + 1) - p i) (p j - p i) (u + ε • e))
    (hrest : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) (u + ε • e))
    (hnd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), NoHDNRim p (u + ε • e)) : IsRupert V :=
  isRupert_faceCircle_ev V hk p hpV hu0 hu hA hD hfar (ev_depthSepZ e hz) hcyc hrest hnd


/-! ### Type 24, Leaf A: rim `0 4 6 1 2 5` -/

/-- Antipodality from the unique far corners, any rim length (`LeafB24.parPair_of_anti` for `ZMod k`). -/
theorem parPair_of_anti6 {p : ZMod 6 → ℝ³} {u : ℝ³} {c : ZMod 6 → ZMod 6}
    (hanti : ∀ i l, l ≠ c i → det3 (p (i + 1) - p i) (p l - p i) u
        < det3 (p (i + 1) - p i) (p (c i) - p i) u) (i : ZMod 6) : ParPairAt p u i (c i) := by
  have hdd : det3 (p (i + 1) - p i) (p (i + 1) - p i) u = 0 := by simp only [det3_expand]; ring
  have hd0 : det3 (p (i + 1) - p i) (p i - p i) u = 0 := by
    rw [sub_self]; simp only [det3_expand]; simp
  have hne : ∀ i : ZMod 6, i + 1 ≠ i := by decide
  have hpos : 0 < det3 (p (i + 1) - p i) (p (c i) - p i) u := by
    by_cases h : c i = i
    · have := hanti i (i + 1) (by rw [h]; exact hne i)
      rw [h, hdd, hd0] at this
      exact absurd this (lt_irrefl _)
    · have := hanti i i (Ne.symm h)
      rwa [hd0] at this
  intro j hj
  have e : p j - p (c i) = (p j - p i) - (p (c i) - p i) := by abel
  have hd : det3 (p (i + 1) - p i) (p j - p (c i)) u
      = det3 (p (i + 1) - p i) (p j - p i) u - det3 (p (i + 1) - p i) (p (c i) - p i) u := by
    rw [e]; simp only [det3_expand, PiLp.sub_apply]; ring
  rw [hd]
  exact mul_neg_of_neg_of_pos (by linarith [hanti i j hj]) hpos

/-- The rim `0 4 6 1 2 5`. -/
def rimA : ZMod 6 → Fin 7 := ![0, 4, 6, 1, 2, 5]

theorem exists_rimA (m : Fin 7) (h3 : m ≠ 3) : ∃ j, m = rimA j := by
  revert m; decide

/-- `DepthSepZ z 3 5` in the wedge `z2 < z5 < z0, z4, z6, z1`. -/
theorem ds_A {z : ZMod 6 → ℝ} (r1 : z 4 < z 5) (r2 : z 5 < z 3) (r3 : z 5 < z 0)
    (r4 : z 5 < z 1) (r5 : z 5 < z 2) : DepthSepZ z 3 5 := by
  have hv : ((3 : ZMod 6) - 5).val = 4 := by decide
  unfold DepthSepZ; left; rw [hv]
  refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
  · interval_cases s
    · exact r3
    · exact r4
    · exact r5
    · exact r2
  · interval_cases s
    exact r1

/-- **Leaf A (type 24), rim `0 4 6 1 2 5`, pair (edge `1 → 2`, far corner `5`), wedge
`z2 < z5 < z0, z1, z4, z6`.**  The far corners are the strict `hanti` rows; the only open foot row is
`hfoot12` (edge `1 → 2`, corner `5`). -/
theorem isRupert_leafA_046125 {x : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimA (i + 1)) - x (rimA i)) (x (rimA j) - x (rimA i)) u)
    (hrest : ∀ i, 0 < det3 (x (rimA (i + 1)) - x (rimA i)) (x 3 - x (rimA i)) u)
    (r1 : ⟪x 2, u⟫ < ⟪x 5, u⟫) (r2 : ⟪x 5, u⟫ < ⟪x 1, u⟫) (r3 : ⟪x 5, u⟫ < ⟪x 4, u⟫)
    (r4 : ⟪x 5, u⟫ < ⟪x 6, u⟫) (r5 : ⟪x 5, u⟫ < ⟪x 0, u⟫)
    (n04 : ⟪x 0, u⟫ ≠ ⟪x 4, u⟫) (n06 : ⟪x 0, u⟫ ≠ ⟪x 6, u⟫) (n01 : ⟪x 0, u⟫ ≠ ⟪x 1, u⟫)
    (n46 : ⟪x 4, u⟫ ≠ ⟪x 6, u⟫) (n41 : ⟪x 4, u⟫ ≠ ⟪x 1, u⟫) (n61 : ⟪x 6, u⟫ ≠ ⟪x 1, u⟫)
    (c : ZMod 6 → ZMod 6) (hc3 : c 3 = 5) (hc2 : c 2 = 5) (hc0 : c 0 = 4) (hc5 : c 5 = 4)
    (hc1 : c 1 = 4 ∨ c 1 = 5) (hc4 : c 4 = 1 ∨ c 4 = 2)
    (hanti : ∀ i l, l ≠ c i → det3 (x (rimA (i + 1)) - x (rimA i)) (x (rimA l) - x (rimA i)) u
        < det3 (x (rimA (i + 1)) - x (rimA i)) (x (rimA (c i)) - x (rimA i)) u)
    (hfoot12 : 0 < scr u (x 5 - x 1) (x 2 - x 1) → scr u (x 5 - x 1) (x 2 - x 1) < scr u (x 2 - x 1) (x 2 - x 1) →
      scr u (x 2 - x 1) (x 2 - x 1) * ⟪x 5, u⟫ ≠
        (scr u (x 2 - x 1) (x 2 - x 1) - scr u (x 5 - x 1) (x 2 - x 1)) * ⟪x 1, u⟫
          + scr u (x 5 - x 1) (x 2 - x 1) * ⟪x 2, u⟫) :
    IsRupert (Finset.univ.image x) := by
  classical
  have hk : 3 ≤ 6 := by norm_num
  have hpp : ParPairAt (fun i => x (rimA i)) u 3 5 := by
    have := parPair_of_anti6 (p := fun i => x (rimA i)) (c := c) hanti 3
    rwa [hc3] at this
  have hz : DepthSepZ (fun i => ⟪x (rimA i), u⟫) 3 5 :=
    ds_A (z := fun i => ⟪x (rimA i), u⟫) (by simpa [rimA] using r1) (by simpa [rimA] using r2)
      (by simpa [rimA] using r5) (by simpa [rimA] using r3) (by simpa [rimA] using r4)
  have hi6 : ∀ i : ZMod 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
  have hinj : Function.Injective fun i => ⟪x (rimA i), u⟫ := by
    intro i j h
    have e0 : ⟪x (rimA 0), u⟫ = ⟪x 0, u⟫ := rfl
    have e1 : ⟪x (rimA 1), u⟫ = ⟪x 4, u⟫ := rfl
    have e2 : ⟪x (rimA 2), u⟫ = ⟪x 6, u⟫ := rfl
    have e3 : ⟪x (rimA 3), u⟫ = ⟪x 1, u⟫ := rfl
    have e4 : ⟪x (rimA 4), u⟫ = ⟪x 2, u⟫ := rfl
    have e5 : ⟪x (rimA 5), u⟫ = ⟪x 5, u⟫ := rfl
    simp only at h
    rcases hi6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hi6 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3, e4, e5] at h <;>
      first | rfl | (exfalso; linarith) | exact absurd h (by assumption) | exact absurd h.symm (by assumption)
  have hnd : NoHDNRim (fun i => x (rimA i)) u := by
    refine HDNRim.noHDNRim_of_anti hk hcyc hinj c hanti ?_
    intro i h0 h1
    rcases hi6 i with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hc0] at h0 h1 ⊢
      exact foot_below h0 h1 (by show ⟪x 2, u⟫ < ⟪x 0, u⟫; linarith)
        (by show ⟪x 2, u⟫ < ⟪x 4, u⟫; linarith)
    · rcases hc1 with h | h <;> rw [h] at h0 h1 ⊢
      · exact foot_below h0 h1 (by show ⟪x 2, u⟫ < ⟪x 4, u⟫; linarith)
          (by show ⟪x 2, u⟫ < ⟪x 6, u⟫; linarith)
      · exact foot_below h0 h1 (by show ⟪x 5, u⟫ < ⟪x 4, u⟫; linarith)
          (by show ⟪x 5, u⟫ < ⟪x 6, u⟫; linarith)
    · rw [hc2] at h0 h1 ⊢
      exact foot_below h0 h1 (by show ⟪x 5, u⟫ < ⟪x 6, u⟫; linarith)
        (by show ⟪x 5, u⟫ < ⟪x 1, u⟫; linarith)
    · rw [hc3] at h0 h1 ⊢
      exact hfoot12 h0 h1
    · rcases hc4 with h | h <;> rw [h] at h0 h1 ⊢
      · exact foot_above h0 h1 (by show ⟪x 2, u⟫ < ⟪x 4, u⟫; linarith)
          (by show ⟪x 5, u⟫ < ⟪x 4, u⟫; linarith)
      · exact foot_above h0 h1 (by show ⟪x 2, u⟫ < ⟪x 6, u⟫; linarith)
          (by show ⟪x 5, u⟫ < ⟪x 6, u⟫; linarith)
    · rw [hc5] at h0 h1 ⊢
      exact foot_below h0 h1 (by show ⟪x 2, u⟫ < ⟪x 5, u⟫; linarith)
        (by show ⟪x 2, u⟫ < ⟪x 0, u⟫; linarith)
  refine isRupert_of_rimView_depthSeparated_rim _ u hu hk (fun i => x (rimA i)) ?_ hcyc ?_
    (depthSepAt_of hpp hz) hnd
  · intro i; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro v hv hvp i
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hv
    have hm : m = 3 := by
      by_contra hne
      obtain ⟨j, hj⟩ := exists_rimA m hne
      exact hvp j (by rw [hj])
    subst hm
    exact hrest i

end FaceCircle
end Minimality
