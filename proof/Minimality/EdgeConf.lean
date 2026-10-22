module

public import Minimality.SlideE
public import Minimality.Sector

@[expose] public section

/-!
# An edge view with two faces and a four-corner closing (`FEWER-FACES-PROOFS.md` §22.0–22.2)

The setting of §22 for an edge crossing at the limit shape: the view `u` along the axle
(`w = v + h u`), the faces `F_a ∋ v, w, a` and `F_b ∋ v, w, b` (facets, with their other vertices
`M_a`, `M_b`: the *middles*), and the closing `K_v` with the four-corner rim `v a c b`
(counterclockwise at `u`, every point weakly inside).  At the limit the rim is only weakly
convex; (G1) at `u` (`G1At`: every point over a support line lies on a face with the line's
ends, and only the axle is seen end-on, `ParOnly`) makes it strictly convex.

* `G1At`, `EdgeConf`: the data.
* `EdgeConf.det_a`, `EdgeConf.det_b`: the screen tests along the sides on the faces are
  multiples of the face functionals, so a point is over the side `v a` (`b v`) iff it lies on
  `F_a` (`F_b`).
* `EdgeConf.mid_coords`: a middle of `F_a` is `v + s (a − v) + δ u` with `0 < s < 1`.
* `EdgeConf.strict`: the eight tests of the rim are strict.
* `EdgeConf.isRupert_twoCircle` (**Proposition 22.2** for this closing): if the closing is
  realized on both circles (the middles of each face lie on the side of `w` of the chord), a
  robustly unimodal `K_v` makes the set Rupert, whatever its horizontal double normals.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **(G1) at the view `u` with two faces `SA`, `SB`** (point sets): every point of `V` over a
support line `pq` of the shadow, other than `p` and `q`, lies with `p` and `q` on one of the
faces. -/
def G1At (V : Finset ℝ³) (u : ℝ³) (SA SB : Finset ℝ³) : Prop :=
  ∀ p ∈ V, ∀ q ∈ V, ∀ y ∈ V, cross (q - p) u ≠ 0 → (∀ z ∈ V, 0 ≤ det3 (q - p) (z - p) u) →
    det3 (q - p) (y - p) u = 0 → y ≠ p → y ≠ q →
      (p ∈ SA ∧ q ∈ SA ∧ y ∈ SA) ∨ (p ∈ SB ∧ q ∈ SB ∧ y ∈ SB)

/-- **An edge view with two faces and a four-corner closing** (at the limit shape).  The view
`u` is along the axle `w = v + h u`; the faces `F_a` (`⟪N_a, ·⟫ = κ_a` exactly at `v, w, a` and
the middles `M_a`, below elsewhere) and `F_b`; the rim `v a c b` with every point weakly left of
its sides at `u`; only the axle seen end-on (`ParOnly`); and (G1) at `u`. -/
structure EdgeConf (V : Finset ℝ³) (u v w a b c : ℝ³) (h : ℝ) (Na Nb : ℝ³) (κa κb : ℝ)
    (Ma Mb : Finset ℝ³) : Prop where
  hu : u ≠ 0
  hh : h ≠ 0
  hw : w = v + h • u
  hv : v ∈ V
  hwV : w ∈ V
  ha : a ∈ V
  hb : b ∈ V
  hc : c ∈ V
  hMa : Ma ⊆ V
  hMb : Mb ⊆ V
  faceA : ∀ z ∈ V, (z = v ∨ z = w ∨ z = a ∨ z ∈ Ma) ↔ ⟪Na, z⟫ = κa
  faceA_le : ∀ z ∈ V, ⟪Na, z⟫ ≤ κa
  faceB : ∀ z ∈ V, (z = v ∨ z = w ∨ z = b ∨ z ∈ Mb) ↔ ⟪Nb, z⟫ = κb
  faceB_le : ∀ z ∈ V, ⟪Nb, z⟫ ≤ κb
  hbA : b ≠ v ∧ b ≠ w ∧ b ≠ a ∧ b ∉ Ma
  hcA : c ≠ v ∧ c ≠ w ∧ c ≠ a ∧ c ∉ Ma
  haB : a ≠ v ∧ a ≠ w ∧ a ∉ Mb
  hcB : c ≠ b ∧ c ∉ Mb
  hMa' : ∀ m ∈ Ma, m ≠ v ∧ m ≠ w ∧ m ≠ a
  hMb' : ∀ m ∈ Mb, m ≠ v ∧ m ≠ w ∧ m ≠ b
  left : ∀ z ∈ V, 0 ≤ det3 (a - v) (z - v) u ∧ 0 ≤ det3 (c - a) (z - a) u ∧
    0 ≤ det3 (b - c) (z - c) u ∧ 0 ≤ det3 (v - b) (z - b) u
  par : ParOnly V u v w
  g1 : G1At V u (insert v (insert w (insert a Ma))) (insert v (insert w (insert b Mb)))
  noSeg : ∀ p ∈ V, ∀ q ∈ V, ∀ y ∈ V, y ≠ p → y ≠ q → ∀ s : ℝ, 0 < s → s < 1 →
    y ≠ p + s • (q - p)
  supp : ∀ z ∈ V, SuppIn u (quad v a c b) z

namespace EdgeConf

variable {V : Finset ℝ³} {u v w a b c : ℝ³} {h : ℝ} {Na Nb : ℝ³} {κa κb : ℝ}
  {Ma Mb : Finset ℝ³}

theorem det3_sub_left_self (A X U : ℝ³) (t : ℝ) : det3 A (X + t • A) U = det3 A X U := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem det3_shift_u (A X U : ℝ³) (t : ℝ) : det3 A (X + t • U) U = det3 A X U := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem det3_self_left (A U : ℝ³) : det3 A A U = 0 := by
  simp only [det3_expand]; ring

theorem det3_cross_self (A U : ℝ³) : det3 A (cross A U) U = -⟪cross A U, cross A U⟫ := by
  simp only [det3_expand, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]
  simp; ring

theorem inner_Na_v (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Na, v⟫ = κa :=
  (E.faceA v E.hv).mp (Or.inl rfl)

theorem inner_Na_w (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Na, w⟫ = κa :=
  (E.faceA w E.hwV).mp (Or.inr (Or.inl rfl))

theorem inner_Na_a (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Na, a⟫ = κa :=
  (E.faceA a E.ha).mp (Or.inr (Or.inr (Or.inl rfl)))

theorem inner_Nb_v (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Nb, v⟫ = κb :=
  (E.faceB v E.hv).mp (Or.inl rfl)

theorem inner_Nb_w (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Nb, w⟫ = κb :=
  (E.faceB w E.hwV).mp (Or.inr (Or.inl rfl))

theorem inner_Nb_b (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Nb, b⟫ = κb :=
  (E.faceB b E.hb).mp (Or.inr (Or.inr (Or.inl rfl)))

theorem Na_u (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Na, u⟫ = 0 := by
  have h1 := E.inner_Na_w
  rw [E.hw, inner_add_right, real_inner_smul_right, E.inner_Na_v] at h1
  exact (mul_eq_zero.mp (by linarith : h * ⟪Na, u⟫ = 0)).resolve_left E.hh

theorem Nb_u (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Nb, u⟫ = 0 := by
  have h1 := E.inner_Nb_w
  rw [E.hw, inner_add_right, real_inner_smul_right, E.inner_Nb_v] at h1
  exact (mul_eq_zero.mp (by linarith : h * ⟪Nb, u⟫ = 0)).resolve_left E.hh

theorem Na_av (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Na, a - v⟫ = 0 := by
  rw [inner_sub_right, E.inner_Na_a, E.inner_Na_v, sub_self]

theorem Nb_bv (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Nb, b - v⟫ = 0 := by
  rw [inner_sub_right, E.inner_Nb_b, E.inner_Nb_v, sub_self]

/-- A point of `V` off the face `F_a` lies strictly below it. -/
theorem Na_lt (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ w) (h3 : z ≠ a) (h4 : z ∉ Ma) : ⟪Na, z⟫ < κa :=
  lt_of_le_of_ne (E.faceA_le z hz) fun e => by
    rcases (E.faceA z hz).mpr e with e | e | e | e
    exacts [h1 e, h2 e, h3 e, h4 e]

theorem Nb_lt (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ w) (h3 : z ≠ b) (h4 : z ∉ Mb) : ⟪Nb, z⟫ < κb :=
  lt_of_le_of_ne (E.faceB_le z hz) fun e => by
    rcases (E.faceB z hz).mpr e with e | e | e | e
    exacts [h1 e, h2 e, h3 e, h4 e]

theorem Na_bv (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Na, b - v⟫ < 0 := by
  have := E.Na_lt E.hb E.hbA.1 E.hbA.2.1 E.hbA.2.2.1 E.hbA.2.2.2
  rw [inner_sub_right, E.inner_Na_v]; linarith

theorem Nb_av (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : ⟪Nb, a - v⟫ < 0 := by
  have := E.Nb_lt E.ha E.haB.1 E.haB.2.1 (fun e => E.hbA.2.2.1 e.symm) E.haB.2.2
  rw [inner_sub_right, E.inner_Nb_v]; linarith

/-- No other point of `V` lies over `v` or over `w`; in particular `a`, `b`, `c` and the middles
are not over the axle. -/
theorem cross_ne_of_par (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {y y' : ℝ³}
    (hy : y ∈ V) (hy' : y' ∈ V) (hne : y ≠ y') (h1 : ¬ (y = v ∧ y' = w)) (h2 : ¬ (y = w ∧ y' = v)) :
    cross (y' - y) u ≠ 0 := fun h0 => by
  rcases E.par y hy y' hy' hne h0 with h | h
  exacts [h1 h, h2 h]

theorem cross_av (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : cross (a - v) u ≠ 0 :=
  E.cross_ne_of_par E.hv E.ha (Ne.symm E.haB.1) (fun h => E.haB.2.1 h.2)
    (fun h => E.haB.1 h.2)

theorem cross_bv (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : cross (b - v) u ≠ 0 :=
  E.cross_ne_of_par E.hv E.hb (Ne.symm E.hbA.1) (fun h => E.hbA.2.1 h.2)
    (fun h => E.hbA.1 h.2)

/-- The test along the side `v a` is a multiple of the face functional of `F_a`. -/
theorem det_a_rel (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) (X : ℝ³) :
    det3 (a - v) X u * ⟪Na, b - v⟫ = det3 (a - v) (b - v) u * ⟪Na, X⟫ := by
  have := det3_mul_inner_sub (a - v) u X (b - v) Na
  rw [real_inner_comm Na u, E.Na_u, real_inner_comm Na (a - v), E.Na_av] at this
  linarith

theorem det_b_rel (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) (X : ℝ³) :
    det3 (v - b) X u * ⟪Nb, a - v⟫ = det3 (v - b) (a - v) u * ⟪Nb, X⟫ := by
  have hbv : ⟪Nb, v - b⟫ = 0 := by rw [inner_sub_right, E.inner_Nb_b, E.inner_Nb_v, sub_self]
  have := det3_mul_inner_sub (v - b) u X (a - v) Nb
  rw [real_inner_comm Nb u, E.Nb_u, real_inner_comm Nb (v - b), hbv] at this
  linarith

theorem dab_pos (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    0 < det3 (a - v) (b - v) u := by
  have hle := (E.left b E.hb).1
  refine lt_of_le_of_ne hle fun h0 => ?_
  have key := E.det_a_rel (cross (a - v) u)
  rw [← h0, zero_mul, det3_cross_self] at key
  have hpos : 0 < ⟪cross (a - v) u, cross (a - v) u⟫ := real_inner_self_pos.mpr E.cross_av
  have := E.Na_bv
  nlinarith

theorem dba_pos (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    0 < det3 (v - b) (a - v) u := by
  have hle : 0 ≤ det3 (v - b) (a - v) u := by
    have := (E.left a E.ha).2.2.2
    have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    linarith
  refine lt_of_le_of_ne hle fun h0 => ?_
  have hcb : cross (v - b) u ≠ 0 := by
    intro h0'; apply E.cross_bv
    have : cross (b - v) u = -cross (v - b) u := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    rw [this, h0', neg_zero]
  have key := E.det_b_rel (cross (v - b) u)
  rw [← h0, zero_mul, det3_cross_self] at key
  have hpos : 0 < ⟪cross (v - b) u, cross (v - b) u⟫ := real_inner_self_pos.mpr hcb
  have := E.Nb_av
  nlinarith

/-- **Over the side `v a` means on `F_a`**: the test of the side `v a` at a point of `V`
vanishes iff the point is `v`, `w`, `a` or a middle of `F_a`, and is positive otherwise. -/
theorem det_a_pos (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ w) (h3 : z ≠ a) (h4 : z ∉ Ma) : 0 < det3 (a - v) (z - v) u := by
  have key := E.det_a_rel (z - v)
  have hlt : ⟪Na, z - v⟫ < 0 := by
    rw [inner_sub_right, E.inner_Na_v]; linarith [E.Na_lt hz h1 h2 h3 h4]
  have := E.dab_pos
  have := E.Na_bv
  nlinarith

theorem det_a_zero (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h0 : det3 (a - v) (z - v) u = 0) : z = v ∨ z = w ∨ z = a ∨ z ∈ Ma := by
  by_contra hc
  push Not at hc
  exact absurd h0 (E.det_a_pos hz hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).ne'

theorem det_b_pos (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ w) (h3 : z ≠ b) (h4 : z ∉ Mb) : 0 < det3 (v - b) (z - b) u := by
  have e : det3 (v - b) (z - b) u = det3 (v - b) (z - v) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]
  have key := E.det_b_rel (z - v)
  have hlt : ⟪Nb, z - v⟫ < 0 := by
    rw [inner_sub_right, E.inner_Nb_v]; linarith [E.Nb_lt hz h1 h2 h3 h4]
  have := E.dba_pos
  have := E.Nb_av
  nlinarith

theorem det_b_zero (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h0 : det3 (v - b) (z - b) u = 0) : z = v ∨ z = w ∨ z = b ∨ z ∈ Mb := by
  by_contra hc
  push Not at hc
  exact absurd h0 (E.det_b_pos hz hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).ne'

/-- The far sides `a c` and `c b` carry no other point of `V` (G1). -/
theorem det_ac_pos (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ a) (h2 : z ≠ c) : 0 < det3 (c - a) (z - a) u := by
  refine lt_of_le_of_ne (E.left z hz).2.1 fun h0 => ?_
  have hca : cross (c - a) u ≠ 0 :=
    E.cross_ne_of_par E.ha E.hc (Ne.symm E.hcA.2.2.1) (fun h => E.haB.1 h.1)
      (fun h => E.haB.2.1 h.1)
  rcases E.g1 a E.ha c E.hc z hz hca (fun z hz => (E.left z hz).2.1) h0.symm h1 h2 with
    ⟨-, hc', -⟩ | ⟨ha', -, -⟩
  · simp only [mem_insert] at hc'
    rcases hc' with e | e | e | e
    exacts [E.hcA.1 e, E.hcA.2.1 e, E.hcA.2.2.1 e, E.hcA.2.2.2 e]
  · simp only [mem_insert] at ha'
    rcases ha' with e | e | e | e
    exacts [E.haB.1 e, E.haB.2.1 e, E.hbA.2.2.1 e.symm, E.haB.2.2 e]

theorem det_cb_pos (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ c) (h2 : z ≠ b) : 0 < det3 (b - c) (z - c) u := by
  refine lt_of_le_of_ne (E.left z hz).2.2.1 fun h0 => ?_
  have hcb : cross (b - c) u ≠ 0 :=
    E.cross_ne_of_par E.hc E.hb E.hcB.1 (fun h => E.hcA.1 h.1) (fun h => E.hcA.2.1 h.1)
  rcases E.g1 c E.hc b E.hb z hz hcb (fun z hz => (E.left z hz).2.2.1) h0.symm h1 h2 with
    ⟨hc', -, -⟩ | ⟨hc', -, -⟩
  · simp only [mem_insert] at hc'
    rcases hc' with e | e | e | e
    exacts [E.hcA.1 e, E.hcA.2.1 e, E.hcA.2.2.1 e, E.hcA.2.2.2 e]
  · simp only [mem_insert] at hc'
    rcases hc' with e | e | e | e
    exacts [E.hcA.1 e, E.hcA.2.1 e, E.hcB.1 e, E.hcB.2 e]

/-- The rim `v a c b` is injective. -/
theorem quad_injective (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    Function.Injective (quad v a c b) := by
  have hav : a ≠ v := E.haB.1
  have hcv : c ≠ v := E.hcA.1
  have hbv : b ≠ v := E.hbA.1
  have hca : c ≠ a := E.hcA.2.2.1
  have hba : b ≠ a := E.hbA.2.2.1
  have hcb : c ≠ b := E.hcB.1
  intro i j hij
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [quad_0, quad_1, quad_2, quad_3] at hij <;> first | rfl | (exfalso; simp_all)

/-- The eight tests of the rim `v a c b` at `u` are strict. -/
theorem cyc (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < det3 (quad v a c b (i + 1) - quad v a c b i) (quad v a c b j - quad v a c b i) u := by
  have hav : a ≠ v := E.haB.1
  have hcv : c ≠ v := E.hcA.1
  have hbv : b ≠ v := E.hbA.1
  have hca : c ≠ a := E.hcA.2.2.1
  have hba : b ≠ a := E.hbA.2.2.1
  have hcb : c ≠ b := E.hcB.1
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_pairs i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
  · exact E.det_a_pos E.hc hcv E.hcA.2.1 hca E.hcA.2.2.2
  · exact E.dab_pos
  · exact E.det_ac_pos E.hb hba hcb.symm
  · exact E.det_ac_pos E.hv hav.symm hcv.symm
  · exact E.det_cb_pos E.hv hcv.symm hbv.symm
  · exact E.det_cb_pos E.ha hca.symm hba.symm
  · have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact E.dba_pos
  · exact E.det_b_pos E.hc hcv E.hcA.2.1 hcb E.hcB.2

/-- Every point of `V` is weakly left of every side of the rim. -/
theorem left_quad (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    ∀ z ∈ V, ∀ i : ZMod 4,
      0 ≤ det3 (quad v a c b (i + 1) - quad v a c b i) (z - quad v a c b i) u := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  intro z hz i
  obtain ⟨l1, l2, l3, l4⟩ := E.left z hz
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;> assumption

/-- Coordinates in a plane: a vector perpendicular to `N` with `A`, `U` perpendicular to `N`
and `A × U ≠ 0` is a combination of `A` and `U`. -/
theorem exists_coords_of_perp {N A U X : ℝ³} (hA : ⟪N, A⟫ = 0) (hU : ⟪N, U⟫ = 0)
    (hX : ⟪N, X⟫ = 0) (hAU : cross A U ≠ 0) (hN : N ≠ 0) : ∃ s δ : ℝ, X = s • A + δ • U := by
  set C := cross A U with hC
  have hCN : cross C N = 0 := by
    rw [hC, cross_cross_eq, real_inner_comm, hA, real_inner_comm, hU, zero_smul, zero_smul,
      sub_zero]
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, N = ν • C := ⟨_, eq_smul_of_cross_eq_zero hAU hCN⟩
  have hν0 : ν ≠ 0 := by rintro rfl; rw [zero_smul] at hν; exact hN hν
  have hXC : ⟪X, C⟫ = 0 := by
    rw [hν, real_inner_smul_left] at hX
    rw [real_inner_comm]; exact (mul_eq_zero.mp hX).resolve_left hν0
  have hCC : 0 < ⟪C, C⟫ := real_inner_self_pos.mpr hAU
  have key : ⟪C, C⟫ • X = ⟪cross X U, C⟫ • A + ⟪cross A X, C⟫ • U + ⟪X, C⟫ • C := by
    rw [hC]
    ext j; fin_cases j <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
        Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, cross_apply_zero, cross_apply_one,
        cross_apply_two, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> ring
  rw [hXC, zero_smul, add_zero] at key
  refine ⟨⟪cross X U, C⟫ / ⟪C, C⟫, ⟪cross A X, C⟫ / ⟪C, C⟫, ?_⟩
  have hne : ⟪C, C⟫ ≠ 0 := hCC.ne'
  calc X = ⟪C, C⟫⁻¹ • (⟪C, C⟫ • X) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [key, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

theorem Na_ne (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : Na ≠ 0 := by
  intro h0; have := E.Na_bv; rw [h0, inner_zero_left] at this; exact lt_irrefl _ this

theorem Nb_ne (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) : Nb ≠ 0 := by
  intro h0; have := E.Nb_av; rw [h0, inner_zero_left] at this; exact lt_irrefl _ this

/-- **A middle of `F_a`** lies over the open side `(v, a)`: `m = v + s (a − v) + δ u` with
`0 < s < 1`. -/
theorem midA_coords (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Ma) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ m = v + s • (a - v) + δ • u := by
  have hmV := E.hMa hm
  obtain ⟨hmv, hmw, hma⟩ := E.hMa' m hm
  have hNm : ⟪Na, m - v⟫ = 0 := by
    rw [inner_sub_right, (E.faceA m hmV).mp (Or.inr (Or.inr (Or.inr hm))), E.inner_Na_v,
      sub_self]
  obtain ⟨s, δ, hsd⟩ := exists_coords_of_perp E.Na_av E.Na_u hNm E.cross_av E.Na_ne
  have hmeq : m = v + s • (a - v) + δ • u := by rw [add_assoc, ← hsd]; abel
  refine ⟨s, δ, ?_, ?_, hmeq⟩
  · have hle := (E.left m hmV).2.2.2
    have e : det3 (v - b) (m - b) u = s * det3 (v - b) (a - v) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hle
    have hs0 : 0 ≤ s := nonneg_of_mul_nonneg_left hle E.dba_pos
    refine lt_of_le_of_ne hs0 fun h0 => ?_
    rw [← h0, zero_smul, add_zero] at hmeq
    apply E.cross_ne_of_par E.hv hmV (Ne.symm hmv) (fun h => hmw h.2) (fun h => hmv h.2)
    rw [hmeq, add_sub_cancel_left, cross_smul_left_self]
  · have hle := (E.left m hmV).2.1
    have e : det3 (c - a) (m - a) u = (1 - s) * det3 (c - a) (v - a) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hle
    have hpos := E.det_ac_pos E.hv E.haB.1.symm E.hcA.1.symm
    have hs1 : 0 ≤ 1 - s := nonneg_of_mul_nonneg_left hle hpos
    refine lt_of_le_of_ne (by linarith) fun h1 => ?_
    have hmeq' : m = a + δ • u := by rw [hmeq, h1, one_smul]; abel
    apply E.cross_ne_of_par E.ha hmV (Ne.symm hma) (fun h => E.haB.1 h.1)
      (fun h => E.haB.2.1 h.1)
    rw [hmeq', add_sub_cancel_left, cross_smul_left_self]

/-- **A middle of `F_b`** lies over the open side `(b, v)`: `m = v + s (b − v) + δ u` with
`0 < s < 1`. -/
theorem midB_coords (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) {m : ℝ³} (hm : m ∈ Mb) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ m = v + s • (b - v) + δ • u := by
  have hmV := E.hMb hm
  obtain ⟨hmv, hmw, hmb⟩ := E.hMb' m hm
  have hNm : ⟪Nb, m - v⟫ = 0 := by
    rw [inner_sub_right, (E.faceB m hmV).mp (Or.inr (Or.inr (Or.inr hm))), E.inner_Nb_v,
      sub_self]
  obtain ⟨s, δ, hsd⟩ := exists_coords_of_perp E.Nb_bv E.Nb_u hNm E.cross_bv E.Nb_ne
  have hmeq : m = v + s • (b - v) + δ • u := by rw [add_assoc, ← hsd]; abel
  refine ⟨s, δ, ?_, ?_, hmeq⟩
  · have hle := (E.left m hmV).1
    have e : det3 (a - v) (m - v) u = s * det3 (a - v) (b - v) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hle
    have hs0 : 0 ≤ s := nonneg_of_mul_nonneg_left hle E.dab_pos
    refine lt_of_le_of_ne hs0 fun h0 => ?_
    rw [← h0, zero_smul, add_zero] at hmeq
    apply E.cross_ne_of_par E.hv hmV (Ne.symm hmv) (fun h => hmw h.2) (fun h => hmv h.2)
    rw [hmeq, add_sub_cancel_left, cross_smul_left_self]
  · have hle := (E.left m hmV).2.2.1
    have e : det3 (b - c) (m - c) u = (1 - s) * det3 (b - c) (v - c) u + s * 0 := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e, mul_zero, add_zero] at hle
    have hpos := E.det_cb_pos E.hv E.hcA.1.symm E.hbA.1.symm
    have hs1 : 0 ≤ 1 - s := nonneg_of_mul_nonneg_left hle hpos
    refine lt_of_le_of_ne (by linarith) fun h1 => ?_
    have hmeq' : m = b + δ • u := by rw [hmeq, h1, one_smul]; abel
    apply E.cross_ne_of_par E.hb hmV (Ne.symm hmb) (fun h => E.hbA.1 h.1)
      (fun h => E.hbA.2.1 h.1)
    rw [hmeq', add_sub_cancel_left, cross_smul_left_self]

/-- **The closing is realized on `F_b`'s circle** (the middles of `F_a` lie on `w`'s side of the
chord `v a`). -/
def RealA (v w a : ℝ³) (Ma : Finset ℝ³) : Prop :=
  ∀ m ∈ Ma, ∃ k : ℝ, 0 < k ∧ cross (a - v) (m - v) = k • cross (a - v) (w - v)

/-- **The closing is realized on `F_a`'s circle** (the middles of `F_b` lie on `w`'s side of the
chord `b v`). -/
def RealB (v w b : ℝ³) (Mb : Finset ℝ³) : Prop :=
  ∀ m ∈ Mb, ∃ k : ℝ, 0 < k ∧ cross (v - b) (m - b) = k • cross (v - b) (w - b)

theorem cross_smul_left'' (k : ℝ) (A B : ℝ³) : cross (k • A) B = k • cross A B := by
  ext j; fin_cases j <;> simp [cross] <;> ring

theorem cross_cross_u (A B U : ℝ³) : cross (cross A U) (cross B U) = det3 A B U • U := by
  ext j; fin_cases j <;> simp [cross, det3_expand] <;> ring

/-- **Proposition 22.2 for a four-corner closing at an edge view** (two realizing circles): with
the middles of each face on `w`'s side of its chord (`RealA`, `RealB`) and `K_v` robustly
unimodal at `u`, the set is Rupert, whatever its horizontal double normals and ties. -/
theorem isRupert_twoCircle (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb)
    (hRA : RealA v w a Ma) (hRB : RealB v w b Mb)
    (hz : IsRobustUnimodal (fun i => ⟪quad v a c b i, u⟫)) : IsRupert V := by
  classical
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hav : a ≠ v := E.haB.1
  have hcv : c ≠ v := E.hcA.1
  have hbv : b ≠ v := E.hbA.1
  have hca : c ≠ a := E.hcA.2.2.1
  have hba : b ≠ a := E.hbA.2.2.1
  have hcb : c ≠ b := E.hcB.1
  have hW : cross (cross (a - v) (w - v)) (cross (v - b) (w - b)) ≠ 0 := by
    have e1 : w - v = h • u := by rw [E.hw]; abel
    have e2 : w - b = (v - b) + h • u := by rw [E.hw]; abel
    have e3 : cross (v - b) ((v - b) + h • u) = h • cross (v - b) u := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    have e4 : cross (cross (a - v) (h • u)) (h • cross (v - b) u) =
        (h * h * det3 (a - v) (v - b) u) • u := by
      ext j; fin_cases j <;> simp [cross, det3_expand] <;> ring
    rw [e1, e2, e3, e4]
    refine smul_ne_zero (mul_ne_zero (mul_ne_zero E.hh E.hh) ?_) E.hu
    have : det3 (a - v) (v - b) u = -det3 (a - v) (b - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [this, neg_ne_zero]; exact E.dab_pos.ne'
  obtain ⟨d, hd⟩ := exists_tiltHides_of_normals V u (quad v a c b) hW fun z hz i hz1 hz2 h0 => by
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] at hz1 hz2 h0 ⊢
    · rcases E.det_a_zero hz h0 with e | e | e | e
      · exact absurd e hz1
      · exact ⟨1, one_pos, Or.inl (by rw [e, one_smul])⟩
      · exact absurd e hz2
      · obtain ⟨k, hk, hk'⟩ := hRA z e
        exact ⟨k, hk, Or.inl hk'⟩
    · exact absurd h0 (E.det_ac_pos hz hz1 hz2).ne'
    · exact absurd h0 (E.det_cb_pos hz hz1 hz2).ne'
    · rcases E.det_b_zero hz h0 with e | e | e | e
      · exact absurd e hz2
      · exact ⟨1, one_pos, Or.inr (by rw [e, one_smul])⟩
      · exact absurd e hz1
      · obtain ⟨k, hk, hk'⟩ := hRB z e
        exact ⟨k, hk, Or.inr hk'⟩
  refine isRupert_of_tiltHides V u d E.hu (by norm_num) (quad v a c b) (fun i => ?_)
    E.quad_injective E.left_quad hd hz
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  exacts [E.hv, E.ha, E.hc, E.hb]

/-! ### Symmetries: the mirror (exchange the faces) and the swap (exchange the axle ends) -/

theorem G1At.neg {V : Finset ℝ³} {u : ℝ³} {SA SB : Finset ℝ³} (hG : G1At V u SA SB) :
    G1At V (-u) SB SA := by
  intro p hp q hq y hy hc hl h0 hyp hyq
  have hc' : cross (p - q) u ≠ 0 := by
    intro e; apply hc
    have : cross (q - p) (-u) = cross (p - q) u := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    rw [this]; exact e
  have hl' : ∀ z ∈ V, 0 ≤ det3 (p - q) (z - q) u := by
    intro z hz
    have := hl z hz
    rw [det3_neg_right] at this
    rw [det3_swap_base]; linarith
  have h0' : det3 (p - q) (y - q) u = 0 := by
    rw [det3_neg_right, neg_eq_zero] at h0
    rw [det3_swap_base, h0, neg_zero]
  rcases hG q hq p hp y hy hc' hl' h0' hyq hyp with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · exact Or.inr ⟨a2, a1, a3⟩
  · exact Or.inl ⟨a2, a1, a3⟩

theorem ParOnly.neg' {V : Finset ℝ³} {u e₁ e₂ : ℝ³} (h : ParOnly V u e₁ e₂) :
    ParOnly V (-u) e₁ e₂ := by
  have := h.smul (c := -1) (by norm_num)
  rwa [neg_one_smul] at this

theorem ParOnly.symm {V : Finset ℝ³} {u e₁ e₂ : ℝ³} (h : ParOnly V u e₁ e₂) :
    ParOnly V u e₂ e₁ := fun y hy y' hy' hne h0 => (h y hy y' hy' hne h0).symm

/-- **The mirror**: exchanging the faces `F_a`, `F_b` and reversing the view gives the
configuration with the rim `v b c a`. -/
theorem mirror (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    EdgeConf V (-u) v w b a c (-h) Nb Na κb κa Mb Ma where
  hu := neg_ne_zero.mpr E.hu
  hh := neg_ne_zero.mpr E.hh
  hw := by rw [E.hw, neg_smul, smul_neg, neg_neg]
  hv := E.hv
  hwV := E.hwV
  ha := E.hb
  hb := E.ha
  hc := E.hc
  hMa := E.hMb
  hMb := E.hMa
  faceA := E.faceB
  faceA_le := E.faceB_le
  faceB := E.faceA
  faceB_le := E.faceA_le
  hbA := ⟨E.haB.1, E.haB.2.1, fun e => E.hbA.2.2.1 e.symm, E.haB.2.2⟩
  hcA := ⟨E.hcA.1, E.hcA.2.1, E.hcB.1, E.hcB.2⟩
  haB := ⟨E.hbA.1, E.hbA.2.1, E.hbA.2.2.2⟩
  hcB := ⟨E.hcA.2.2.1, E.hcA.2.2.2⟩
  hMa' := E.hMb'
  hMb' := E.hMa'
  left := by
    intro z hz
    obtain ⟨l1, l2, l3, l4⟩ := E.left z hz
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e : det3 (b - v) (z - v) (-u) = det3 (v - b) (z - b) u := by
        simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
      rw [e]; exact l4
    · have e : det3 (c - b) (z - b) (-u) = det3 (b - c) (z - c) u := by
        simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
      rw [e]; exact l3
    · have e : det3 (a - c) (z - c) (-u) = det3 (c - a) (z - a) u := by
        simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
      rw [e]; exact l2
    · have e : det3 (v - a) (z - a) (-u) = det3 (a - v) (z - v) u := by
        simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
      rw [e]; exact l1
  par := ParOnly.neg' E.par
  g1 := G1At.neg E.g1
  noSeg := E.noSeg
  supp := by
    intro z hz ℓ hℓ
    rw [inner_neg_right, neg_eq_zero] at hℓ
    obtain ⟨i, hi⟩ := E.supp z hz ℓ hℓ
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · exact ⟨0, hi⟩
    · exact ⟨3, hi⟩
    · exact ⟨2, hi⟩
    · exact ⟨1, hi⟩

theorem insert_swap (v w : ℝ³) (S : Finset ℝ³) :
    insert w (insert v S) = insert v (insert w S) := Finset.insert_comm w v S

/-- **The swap**: the closing `K_w` of the same crossing (`v = w + (−h) u`). -/
theorem swap (E : EdgeConf V u v w a b c h Na Nb κa κb Ma Mb) :
    EdgeConf V u w v a b c (-h) Na Nb κa κb Ma Mb where
  hu := E.hu
  hh := neg_ne_zero.mpr E.hh
  hw := by rw [E.hw, neg_smul]; abel
  hv := E.hwV
  hwV := E.hv
  ha := E.ha
  hb := E.hb
  hc := E.hc
  hMa := E.hMa
  hMb := E.hMb
  faceA := fun z hz => by rw [← E.faceA z hz]; tauto
  faceA_le := E.faceA_le
  faceB := fun z hz => by rw [← E.faceB z hz]; tauto
  faceB_le := E.faceB_le
  hbA := ⟨E.hbA.2.1, E.hbA.1, E.hbA.2.2.1, E.hbA.2.2.2⟩
  hcA := ⟨E.hcA.2.1, E.hcA.1, E.hcA.2.2.1, E.hcA.2.2.2⟩
  haB := ⟨E.haB.2.1, E.haB.1, E.haB.2.2⟩
  hcB := E.hcB
  hMa' := fun m hm => ⟨(E.hMa' m hm).2.1, (E.hMa' m hm).1, (E.hMa' m hm).2.2⟩
  hMb' := fun m hm => ⟨(E.hMb' m hm).2.1, (E.hMb' m hm).1, (E.hMb' m hm).2.2⟩
  left := by
    intro z hz
    obtain ⟨l1, l2, l3, l4⟩ := E.left z hz
    have hw := E.hw
    refine ⟨?_, l2, l3, ?_⟩
    · have e : det3 (a - w) (z - w) u = det3 (a - v) (z - v) u := by
        rw [hw]; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [e]; exact l1
    · have e : det3 (w - b) (z - b) u = det3 (v - b) (z - b) u := by
        rw [hw]; simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [e]; exact l4
  par := ParOnly.symm E.par
  g1 := by rw [insert_swap v w, insert_swap v w]; exact E.g1
  noSeg := E.noSeg
  supp := by
    intro z hz ℓ hℓ
    obtain ⟨i, hi⟩ := E.supp z hz ℓ hℓ
    have hwv : ⟪ℓ, w⟫ = ⟪ℓ, v⟫ := by
      rw [E.hw, inner_add_right, real_inner_smul_right, hℓ, mul_zero, add_zero]
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp only [quad_0] at hi ⊢; rw [hwv]; exact hi⟩
    · exact ⟨1, hi⟩
    · exact ⟨2, hi⟩
    · exact ⟨3, hi⟩

end EdgeConf

end Minimality

end
