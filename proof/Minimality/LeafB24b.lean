module

public import Minimality.LeafB24

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Filter Topology

namespace Minimality
open HDNApex

namespace LeafB24

/-- Antipodality from the unique far corners: if `c i` is the strictly farthest corner of the edge
`i → i+1` (`hanti`), then `(i, c i)` is a parallel pair (`ParPairAt`).  So `hpp` of `isRupert_leafB_04625`
is a consequence of `hanti`. -/
theorem parPair_of_anti {p : ZMod 5 → ℝ³} {u : ℝ³} {c : ZMod 5 → ZMod 5}
    (hanti : ∀ i l, l ≠ c i → det3 (p (i + 1) - p i) (p l - p i) u
        < det3 (p (i + 1) - p i) (p (c i) - p i) u) (i : ZMod 5) : ParPairAt p u i (c i) := by
  have hdd : det3 (p (i + 1) - p i) (p (i + 1) - p i) u = 0 := by simp only [det3_expand]; ring
  have hd0 : det3 (p (i + 1) - p i) (p i - p i) u = 0 := by
    rw [sub_self]; simp only [det3_expand]; simp
  have hne : ∀ i : ZMod 5, i + 1 ≠ i := by decide
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

/-- `DepthSepZ z 3 2` for the rim `0 4 6 2 5` in the wedge `z2 < z6 < z0`. -/
theorem ds_B' {z : ZMod 5 → ℝ} (r1 : z 3 < z 2) (r2 : z 2 < z 4) (r3 : z 2 < z 0) (r4 : z 2 < z 1) :
    DepthSepZ z 3 2 := by
  have hv : ((3 : ZMod 5) - 2).val = 1 := by decide
  unfold DepthSepZ; right; rw [hv]
  refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩ <;> interval_cases s <;>
    first | exact r1 | exact r2 | exact r3 | exact r4

/-! ### Persistence along the tilt `u + ε e` -/

theorem inner_tilt (a u e : ℝ³) (ε : ℝ) : ⟪a, u + ε • e⟫ = ⟪a, u⟫ + ε * ⟪a, e⟫ := by
  rw [inner_add_right, real_inner_smul_right]

theorem ev_inner_lt {a b u : ℝ³} (e : ℝ³)
    (h : ⟪a, u⟫ < ⟪b, u⟫ ∨ (⟪a, u⟫ = ⟪b, u⟫ ∧ ⟪a, e⟫ < ⟪b, e⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪a, u + ε • e⟫ < ⟪b, u + ε • e⟫ := by
  have := eventually_pos_affine (A := ⟪b, u⟫ - ⟪a, u⟫) (B := ⟪b, e⟫ - ⟪a, e⟫) (by
    rcases h with h | ⟨h1, h2⟩
    · left; linarith
    · right; constructor <;> linarith)
  filter_upwards [this] with ε hε
  rw [inner_tilt, inner_tilt]; simp only [mul_sub] at hε; linarith

theorem ev_inner_ne {a b u : ℝ³} (e : ℝ³) (h : ⟪a, u⟫ ≠ ⟪b, u⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪a, u + ε • e⟫ ≠ ⟪b, u + ε • e⟫ := by
  rcases lt_or_gt_of_ne h with h | h
  · exact (ev_inner_lt e (Or.inl h)).mono fun ε hε => hε.ne
  · exact (ev_inner_lt e (Or.inl h)).mono fun ε hε => hε.ne'

theorem ev_det_lt {a b a' b' u : ℝ³} (e : ℝ³) (h : det3 a b u < det3 a' b' u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), det3 a b (u + ε • e) < det3 a' b' (u + ε • e) := by
  have := eventually_pos_affine (A := det3 a' b' u - det3 a b u)
    (B := det3 a' b' e - det3 a b e) (Or.inl (by linarith))
  filter_upwards [this] with ε hε
  rw [det3_add_smul, det3_add_smul]; simp only [mul_sub] at hε; linarith

theorem ev_det_pos {a b u : ℝ³} (e : ℝ³) (h : 0 < det3 a b u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 a b (u + ε • e) := by
  have := eventually_pos_affine (A := det3 a b u) (B := det3 a b e) (Or.inl h)
  filter_upwards [this] with ε hε
  rwa [det3_add_smul]

theorem ev_imp {p : Prop} {q : ℝ → Prop} {l : Filter ℝ} (h : p → ∀ᶠ ε in l, q ε) :
    ∀ᶠ ε in l, p → q ε := by
  by_cases hp : p
  · exact (h hp).mono fun _ h _ => h
  · exact Eventually.of_forall fun _ h => absurd h hp

/-- Everything that is strict at `u` and does not involve the depth ties persists along `u + ε e`:
nonvanishing, the rim tests `hcyc`, `hrest`, and the unique-far-corner rows `hanti`. -/
theorem ev_common {x : Fin 7 → ℝ³} {u : ℝ³} (e : ℝ³) (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB j) - x (rimB i)) u)
    (hrest : ∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
      0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) u)
    (c : ZMod 5 → ZMod 5)
    (hanti : ∀ i l, l ≠ c i → det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB l) - x (rimB i)) u
        < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB (c i)) - x (rimB i)) u) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), u + ε • e ≠ 0 ∧
      (∀ i j, j ≠ i → j ≠ i + 1 →
        0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB j) - x (rimB i)) (u + ε • e)) ∧
      (∀ v ∈ ({1, 3} : Finset (Fin 7)), ∀ i,
        0 < det3 (x (rimB (i + 1)) - x (rimB i)) (x v - x (rimB i)) (u + ε • e)) ∧
      (∀ i l, l ≠ c i → det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB l) - x (rimB i)) (u + ε • e)
        < det3 (x (rimB (i + 1)) - x (rimB i)) (x (rimB (c i)) - x (rimB i)) (u + ε • e)) := by
  refine Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ ?_))
  · have hc : ContinuousAt (fun ε : ℝ => u + ε • e) 0 := by fun_prop
    have := ContinuousAt.eventually_ne hc (by simpa using hu)
    exact this.filter_mono nhdsWithin_le_nhds
  · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ev_imp fun h1 => ev_imp fun h2 => ev_det_pos e (hcyc i j h1 h2)
  · exact (Filter.eventually_all_finset _).2 fun v hv => Filter.eventually_all.2 fun i =>
      ev_det_pos e (hrest v hv i)
  · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
      ev_imp fun h => ev_det_lt e (hanti i l h)

/-- A foot row persists along the tilt: if the foot of `c` on the edge `a b` is not at an end of the
edge at `u`, and the row holds at `u` (when the foot is inside), then the row holds at `u + ε e`
for all small `ε > 0`. -/
theorem foot_ev {u e a b c : ℝ³} (hu : u ≠ 0)
    (h0 : scr u (c - a) (b - a) ≠ 0) (hL : scr u (c - a) (b - a) ≠ scr u (b - a) (b - a))
    (hc : 0 < scr u (c - a) (b - a) → scr u (c - a) (b - a) < scr u (b - a) (b - a) →
      scr u (b - a) (b - a) * ⟪c, u⟫ <
        (scr u (b - a) (b - a) - scr u (c - a) (b - a)) * ⟪a, u⟫ + scr u (c - a) (b - a) * ⟪b, u⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < scr (u + ε • e) (c - a) (b - a) →
      scr (u + ε • e) (c - a) (b - a) < scr (u + ε • e) (b - a) (b - a) →
      scr (u + ε • e) (b - a) (b - a) * ⟪c, u + ε • e⟫ <
        (scr (u + ε • e) (b - a) (b - a) - scr (u + ε • e) (c - a) (b - a)) * ⟪a, u + ε • e⟫
          + scr (u + ε • e) (c - a) (b - a) * ⟪b, u + ε • e⟫ := by
  have e0 : u + (0 : ℝ) • e = u := by simp
  have hS : ∀ p q : ℝ³, ContinuousAt (fun ε : ℝ => scr (u + ε • e) p q) 0 := by
    intro p q; unfold scr
    have hden : ⟪u + (0 : ℝ) • e, u + (0 : ℝ) • e⟫ ≠ 0 := by
      rw [e0]; exact inner_self_ne_zero.2 hu
    exact ContinuousAt.sub (by fun_prop) (ContinuousAt.div (by fun_prop) (by fun_prop) hden)
  have hI : ∀ w : ℝ³, ContinuousAt (fun ε : ℝ => ⟪w, u + ε • e⟫) 0 := fun w => by fun_prop
  have hSc := hS (c - a) (b - a)
  have hLc := hS (b - a) (b - a)
  have key : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < scr (u + ε • e) (c - a) (b - a) →
      scr (u + ε • e) (c - a) (b - a) < scr (u + ε • e) (b - a) (b - a) →
      scr (u + ε • e) (b - a) (b - a) * ⟪c, u + ε • e⟫ <
        (scr (u + ε • e) (b - a) (b - a) - scr (u + ε • e) (c - a) (b - a)) * ⟪a, u + ε • e⟫
          + scr (u + ε • e) (c - a) (b - a) * ⟪b, u + ε • e⟫ := by
    rcases lt_or_gt_of_ne h0 with h | h
    · have := hSc.eventually_lt (continuousAt_const (y := (0 : ℝ))) (by simpa [e0] using h)
      exact this.mono fun ε hε h1 _ => absurd h1 (not_lt.2 hε.le)
    · rcases lt_or_gt_of_ne hL with h' | h'
      · have hF := ((hLc.mul (hI c)).sub (((hLc.sub hSc).mul (hI a)).add (hSc.mul (hI b)))).eventually_lt
          (continuousAt_const (y := (0 : ℝ))) (by
            simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, zero_smul, add_zero]
            linarith [hc h h'])
        exact hF.mono fun ε hε _ _ => by
          simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply] at hε; linarith
      · have := hLc.eventually_lt hSc (by simpa [e0] using h')
        exact this.mono fun ε hε _ h2 => absurd h2 (not_lt.2 hε.le)
  exact key.filter_mono nhdsWithin_le_nhds

/-- The key row of `hanti` (edge `4 → 6`, far corner `2` against vertex `5`) is one determinant:
`det3 (x6 - x4) (x5 - x2) u < 0` (the linear form `A(c*)` of LEAFB24.md, up to the orientation sign). -/
theorem hanti_key_iff {x : Fin 7 → ℝ³} {u : ℝ³} :
    det3 (x (rimB (1 + 1)) - x (rimB 1)) (x (rimB 4) - x (rimB 1)) u
        < det3 (x (rimB (1 + 1)) - x (rimB 1)) (x (rimB 3) - x (rimB 1)) u ↔
      det3 (x 6 - x 4) (x 5 - x 2) u < 0 := by
  have e : x 5 - x 2 = (x 5 - x 4) - (x 2 - x 4) := by abel
  have h : det3 (x 6 - x 4) (x 5 - x 2) u
      = det3 (x 6 - x 4) (x 5 - x 4) u - det3 (x 6 - x 4) (x 2 - x 4) u := by
    rw [e]; simp only [det3_expand, PiLp.sub_apply]; ring
  have r1 : rimB (1 + 1) = 6 := by decide
  have r0 : rimB 1 = 4 := by decide
  have r4 : rimB 4 = 5 := by decide
  have r3 : rimB 3 = 2 := by decide
  rw [r1, r0, r4, r3, h]; constructor <;> intro h <;> linarith

end LeafB24
end Minimality
