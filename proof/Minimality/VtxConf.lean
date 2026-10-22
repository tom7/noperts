module

public import Minimality.EdgeLimit

@[expose] public section

/-!
# A vertex view with a quadrilateral and a triangle (`FEWER-FACES-PROOFS.md` §22.0, §22.9)

The setting of §22 for a vertex crossing at the limit shape (Lemmas 22.9, 22.10): the view `u`
along the line of the planes of two faces through their common vertex `v`; the face
`F_a ∋ v, a, p, q` is a quadrilateral whose vertices `v` and `a` (its far end) are opposite, so
its middles `p`, `q` lie on opposite sides of the chord `v a` (`p` above, `q` below in the
orientation of `u`); the face `F_b ∋ v, b, n` is a triangle (far end `b`, middle `n`); the
closing has the four-corner rim `v a c b` (counterclockwise at `u`, every point weakly inside).
(G1) at `u` (`G1At`, and no two points over one point, `NoParAt`) makes the rim strictly convex.
The closing is realized on `F_a`'s circle only (Lemma 22.1).

* `VtxConf`: the data.
* `VtxConf.det_a_pos`, `VtxConf.det_b_pos`, `VtxConf.det_ac_pos`, `VtxConf.det_cb_pos`: the
  screen tests of the rim.
* `VtxConf.p_coords`, `VtxConf.q_coords`, `VtxConf.n_coords`: the middles over their sides.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **A vertex view with a quadrilateral and a triangle, and a four-corner closing** (at the
limit shape).  The view `u` lies in the planes of the faces `F_a` (`⟪N_a, ·⟫ = κ_a` exactly at
`v, a, p, q`, below elsewhere) and `F_b` (exactly at `v, b, n`); `p` lies above and `q` below
the chord `v a` along `u`; the rim `v a c b` has every point weakly left of its sides at `u`;
no two points lie over one point (`NoParAt`); and (G1) at `u`. -/
structure VtxConf (V : Finset ℝ³) (u v a c b p q n Na Nb : ℝ³) (κa κb : ℝ) : Prop where
  hu : u ≠ 0
  hv : v ∈ V
  ha : a ∈ V
  hb : b ∈ V
  hc : c ∈ V
  hp : p ∈ V
  hq : q ∈ V
  hn : n ∈ V
  faceA : ∀ z ∈ V, (z = v ∨ z = a ∨ z = p ∨ z = q) ↔ ⟪Na, z⟫ = κa
  faceA_le : ∀ z ∈ V, ⟪Na, z⟫ ≤ κa
  faceB : ∀ z ∈ V, (z = v ∨ z = b ∨ z = n) ↔ ⟪Nb, z⟫ = κb
  faceB_le : ∀ z ∈ V, ⟪Nb, z⟫ ≤ κb
  Na_u : ⟪Na, u⟫ = 0
  Nb_u : ⟪Nb, u⟫ = 0
  nodup : [v, a, c, b, p, q, n].Nodup
  left : ∀ z ∈ V, 0 ≤ det3 (a - v) (z - v) u ∧ 0 ≤ det3 (c - a) (z - a) u ∧
    0 ≤ det3 (b - c) (z - c) u ∧ 0 ≤ det3 (v - b) (z - b) u
  par : NoParAt V u
  g1 : G1At V u {v, a, p, q} {v, b, n}
  noSeg : ∀ p' ∈ V, ∀ q' ∈ V, ∀ y ∈ V, y ≠ p' → y ≠ q' → ∀ s : ℝ, 0 < s → s < 1 →
    y ≠ p' + s • (q' - p')
  supp : ∀ z ∈ V, SuppIn u (quad v a c b) z
  hpu : ∃ s δ : ℝ, 0 < δ ∧ p = v + s • (a - v) + δ • u
  hqu : ∃ s δ : ℝ, δ < 0 ∧ q = v + s • (a - v) + δ • u

namespace VtxConf

variable {V : Finset ℝ³} {u v a c b p q n Na Nb : ℝ³} {κa κb : ℝ}

/-- The seven points are distinct. -/
theorem ne7 (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    v ≠ a ∧ v ≠ c ∧ v ≠ b ∧ v ≠ p ∧ v ≠ q ∧ v ≠ n ∧ a ≠ c ∧ a ≠ b ∧ a ≠ p ∧ a ≠ q ∧ a ≠ n ∧
      c ≠ b ∧ c ≠ p ∧ c ≠ q ∧ c ≠ n ∧ b ≠ p ∧ b ≠ q ∧ b ≠ n ∧ p ≠ q ∧ p ≠ n ∧ q ≠ n := by
  have h := E.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩,
    ⟨h16, h17, h18⟩, ⟨h19, h20⟩, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩

theorem inner_Na_v (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Na, v⟫ = κa :=
  (E.faceA v E.hv).mp (Or.inl rfl)

theorem inner_Na_a (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Na, a⟫ = κa :=
  (E.faceA a E.ha).mp (Or.inr (Or.inl rfl))

theorem inner_Na_p (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Na, p⟫ = κa :=
  (E.faceA p E.hp).mp (Or.inr (Or.inr (Or.inl rfl)))

theorem inner_Na_q (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Na, q⟫ = κa :=
  (E.faceA q E.hq).mp (Or.inr (Or.inr (Or.inr rfl)))

theorem inner_Nb_v (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Nb, v⟫ = κb :=
  (E.faceB v E.hv).mp (Or.inl rfl)

theorem inner_Nb_b (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Nb, b⟫ = κb :=
  (E.faceB b E.hb).mp (Or.inr (Or.inl rfl))

theorem inner_Nb_n (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Nb, n⟫ = κb :=
  (E.faceB n E.hn).mp (Or.inr (Or.inr rfl))

theorem Na_av (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Na, a - v⟫ = 0 := by
  rw [inner_sub_right, E.inner_Na_a, E.inner_Na_v, sub_self]

theorem Nb_bv (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Nb, b - v⟫ = 0 := by
  rw [inner_sub_right, E.inner_Nb_b, E.inner_Nb_v, sub_self]

/-- A point of `V` off the face `F_a` lies strictly below it. -/
theorem Na_lt (E : VtxConf V u v a c b p q n Na Nb κa κb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ a) (h3 : z ≠ p) (h4 : z ≠ q) : ⟪Na, z⟫ < κa :=
  lt_of_le_of_ne (E.faceA_le z hz) fun e => by
    rcases (E.faceA z hz).mpr e with e | e | e | e
    exacts [h1 e, h2 e, h3 e, h4 e]

theorem Nb_lt (E : VtxConf V u v a c b p q n Na Nb κa κb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ b) (h3 : z ≠ n) : ⟪Nb, z⟫ < κb :=
  lt_of_le_of_ne (E.faceB_le z hz) fun e => by
    rcases (E.faceB z hz).mpr e with e | e | e
    exacts [h1 e, h2 e, h3 e]

theorem Na_bv (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Na, b - v⟫ < 0 := by
  obtain ⟨-, -, hvb, -, -, -, -, hab, -, -, -, -, -, -, -, hbp, hbq, -⟩ := E.ne7
  have := E.Na_lt E.hb (Ne.symm hvb) (Ne.symm hab) hbp hbq
  rw [inner_sub_right, E.inner_Na_v]; linarith

theorem Nb_av (E : VtxConf V u v a c b p q n Na Nb κa κb) : ⟪Nb, a - v⟫ < 0 := by
  obtain ⟨hva, -, -, -, -, -, -, hab, -, -, han, -⟩ := E.ne7
  have := E.Nb_lt E.ha (Ne.symm hva) hab han
  rw [inner_sub_right, E.inner_Nb_v]; linarith

theorem cross_ne (E : VtxConf V u v a c b p q n Na Nb κa κb) {y y' : ℝ³} (hy : y ∈ V)
    (hy' : y' ∈ V) (hne : y ≠ y') : cross (y' - y) u ≠ 0 :=
  E.par y hy y' hy' hne

theorem cross_av (E : VtxConf V u v a c b p q n Na Nb κa κb) : cross (a - v) u ≠ 0 :=
  E.cross_ne E.hv E.ha E.ne7.1

theorem cross_bv (E : VtxConf V u v a c b p q n Na Nb κa κb) : cross (b - v) u ≠ 0 :=
  E.cross_ne E.hv E.hb E.ne7.2.2.1

/-- The test along the side `v a` is a multiple of the face functional of `F_a`. -/
theorem det_a_rel (E : VtxConf V u v a c b p q n Na Nb κa κb) (X : ℝ³) :
    det3 (a - v) X u * ⟪Na, b - v⟫ = det3 (a - v) (b - v) u * ⟪Na, X⟫ := by
  have := det3_mul_inner_sub (a - v) u X (b - v) Na
  rw [real_inner_comm Na u, E.Na_u, real_inner_comm Na (a - v), E.Na_av] at this
  linarith

theorem det_b_rel (E : VtxConf V u v a c b p q n Na Nb κa κb) (X : ℝ³) :
    det3 (v - b) X u * ⟪Nb, a - v⟫ = det3 (v - b) (a - v) u * ⟪Nb, X⟫ := by
  have hbv : ⟪Nb, v - b⟫ = 0 := by rw [inner_sub_right, E.inner_Nb_b, E.inner_Nb_v, sub_self]
  have := det3_mul_inner_sub (v - b) u X (a - v) Nb
  rw [real_inner_comm Nb u, E.Nb_u, real_inner_comm Nb (v - b), hbv] at this
  linarith

theorem dab_pos (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    0 < det3 (a - v) (b - v) u := by
  have hle := (E.left b E.hb).1
  refine lt_of_le_of_ne hle fun h0 => ?_
  have key := E.det_a_rel (cross (a - v) u)
  rw [← h0, zero_mul, EdgeConf.det3_cross_self] at key
  have hpos : 0 < ⟪cross (a - v) u, cross (a - v) u⟫ := real_inner_self_pos.mpr E.cross_av
  have := E.Na_bv
  nlinarith

theorem dba_pos (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    0 < det3 (v - b) (a - v) u := by
  have hle : 0 ≤ det3 (v - b) (a - v) u := by
    have := (E.left a E.ha).2.2.2
    have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    linarith
  refine lt_of_le_of_ne hle fun h0 => ?_
  have hcb : cross (v - b) u ≠ 0 := E.cross_ne E.hb E.hv (Ne.symm E.ne7.2.2.1)
  have key := E.det_b_rel (cross (v - b) u)
  rw [← h0, zero_mul, EdgeConf.det3_cross_self] at key
  have hpos : 0 < ⟪cross (v - b) u, cross (v - b) u⟫ := real_inner_self_pos.mpr hcb
  have := E.Nb_av
  nlinarith

/-- **Over the side `v a` means on `F_a`.** -/
theorem det_a_pos (E : VtxConf V u v a c b p q n Na Nb κa κb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ a) (h3 : z ≠ p) (h4 : z ≠ q) : 0 < det3 (a - v) (z - v) u := by
  have key := E.det_a_rel (z - v)
  have hlt : ⟪Na, z - v⟫ < 0 := by
    rw [inner_sub_right, E.inner_Na_v]; linarith [E.Na_lt hz h1 h2 h3 h4]
  have := E.dab_pos
  have := E.Na_bv
  nlinarith

theorem det_b_pos (E : VtxConf V u v a c b p q n Na Nb κa κb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ v) (h2 : z ≠ b) (h3 : z ≠ n) : 0 < det3 (v - b) (z - b) u := by
  have e : det3 (v - b) (z - b) u = det3 (v - b) (z - v) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]
  have key := E.det_b_rel (z - v)
  have hlt : ⟪Nb, z - v⟫ < 0 := by
    rw [inner_sub_right, E.inner_Nb_v]; linarith [E.Nb_lt hz h1 h2 h3]
  have := E.dba_pos
  have := E.Nb_av
  nlinarith

/-- The far sides `a c` and `c b` carry no other point of `V` (G1). -/
theorem det_ac_pos (E : VtxConf V u v a c b p q n Na Nb κa κb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ a) (h2 : z ≠ c) : 0 < det3 (c - a) (z - a) u := by
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, -⟩ := E.ne7
  refine lt_of_le_of_ne (E.left z hz).2.1 fun h0 => ?_
  have hca : cross (c - a) u ≠ 0 := E.cross_ne E.ha E.hc hac
  rcases E.g1 a E.ha c E.hc z hz hca (fun z hz => (E.left z hz).2.1) h0.symm h1 h2 with
    ⟨-, hc', -⟩ | ⟨ha', -, -⟩
  · simp only [mem_insert, mem_singleton] at hc'
    rcases hc' with e | e | e | e
    exacts [hvc e.symm, hac e.symm, hcp e, hcq e]
  · simp only [mem_insert, mem_singleton] at ha'
    rcases ha' with e | e | e
    exacts [hva e.symm, hab e, han e]

theorem det_cb_pos (E : VtxConf V u v a c b p q n Na Nb κa κb) {z : ℝ³} (hz : z ∈ V)
    (h1 : z ≠ c) (h2 : z ≠ b) : 0 < det3 (b - c) (z - c) u := by
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, -⟩ := E.ne7
  refine lt_of_le_of_ne (E.left z hz).2.2.1 fun h0 => ?_
  have hcb' : cross (b - c) u ≠ 0 := E.cross_ne E.hc E.hb hcb
  rcases E.g1 c E.hc b E.hb z hz hcb' (fun z hz => (E.left z hz).2.2.1) h0.symm h1 h2 with
    ⟨hc', -, -⟩ | ⟨hc', -, -⟩
  · simp only [mem_insert, mem_singleton] at hc'
    rcases hc' with e | e | e | e
    exacts [hvc e.symm, hac e.symm, hcp e, hcq e]
  · simp only [mem_insert, mem_singleton] at hc'
    rcases hc' with e | e | e
    exacts [hvc e.symm, hcb e, hcn e]

theorem quad_mem (E : VtxConf V u v a c b p q n Na Nb κa κb) (i : ZMod 4) :
    quad v a c b i ∈ V := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  exacts [E.hv, E.ha, E.hc, E.hb]

/-- The rim `v a c b` is injective. -/
theorem quad_injective (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    Function.Injective (quad v a c b) := by
  obtain ⟨hva, hvc, hvb, -, -, -, hac, hab, -, -, -, hcb, -⟩ := E.ne7
  intro i j hij
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [quad_0, quad_1, quad_2, quad_3] at hij <;> first | rfl | (exfalso; simp_all)

/-- The eight tests of the rim `v a c b` at `u` are strict. -/
theorem cyc (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < det3 (quad v a c b (i + 1) - quad v a c b i) (quad v a c b j - quad v a c b i) u := by
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, -⟩ := E.ne7
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_pairs i j h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
  · exact E.det_a_pos E.hc hvc.symm hac.symm hcp hcq
  · exact E.dab_pos
  · exact E.det_ac_pos E.hb hab.symm hcb.symm
  · exact E.det_ac_pos E.hv hva hvc
  · exact E.det_cb_pos E.hv hvc hvb
  · exact E.det_cb_pos E.ha hac hab
  · have e : det3 (v - b) (a - b) u = det3 (v - b) (a - v) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; exact E.dba_pos
  · exact E.det_b_pos E.hc hvc.symm hcb hcn

theorem Na_ne (E : VtxConf V u v a c b p q n Na Nb κa κb) : Na ≠ 0 := by
  intro h0; have := E.Na_bv; rw [h0, inner_zero_left] at this; exact lt_irrefl _ this

theorem Nb_ne (E : VtxConf V u v a c b p q n Na Nb κa κb) : Nb ≠ 0 := by
  intro h0; have := E.Nb_av; rw [h0, inner_zero_left] at this; exact lt_irrefl _ this

/-- A point of `F_a` over the open side `(v, a)`, from its coordinates in the face. -/
theorem side_s (E : VtxConf V u v a c b p q n Na Nb κa κb) {m : ℝ³} (hmV : m ∈ V)
    (hmv : m ≠ v) (hma : m ≠ a) {s δ : ℝ} (hmeq : m = v + s • (a - v) + δ • u) :
    0 < s ∧ s < 1 := by
  obtain ⟨hva, hvc, hvb, -, -, -, hac, hab, -⟩ := E.ne7
  constructor
  · have hle := (E.left m hmV).2.2.2
    have e : det3 (v - b) (m - b) u = s * det3 (v - b) (a - v) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hle
    have hs0 : 0 ≤ s := nonneg_of_mul_nonneg_left hle E.dba_pos
    refine lt_of_le_of_ne hs0 fun h0 => ?_
    rw [← h0, zero_smul, add_zero] at hmeq
    apply E.cross_ne E.hv hmV (Ne.symm hmv)
    rw [hmeq, add_sub_cancel_left, cross_smul_left_self]
  · have hle := (E.left m hmV).2.1
    have e : det3 (c - a) (m - a) u = (1 - s) * det3 (c - a) (v - a) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hle
    have hpos := E.det_ac_pos E.hv hva hvc
    have hs1 : 0 ≤ 1 - s := nonneg_of_mul_nonneg_left hle hpos
    refine lt_of_le_of_ne (by linarith) fun h1 => ?_
    have hmeq' : m = a + δ • u := by rw [hmeq, h1, one_smul]; abel
    apply E.cross_ne E.ha hmV (Ne.symm hma)
    rw [hmeq', add_sub_cancel_left, cross_smul_left_self]

/-- **The upper middle `p`**: `p = v + s (a − v) + δ u` with `0 < s < 1`, `δ > 0`. -/
theorem p_coords (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ p = v + s • (a - v) + δ • u := by
  obtain ⟨s, δ, hδ, hmeq⟩ := E.hpu
  obtain ⟨-, -, -, hvp, -, -, -, -, hap, -⟩ := E.ne7
  obtain ⟨hs0, hs1⟩ := E.side_s E.hp (Ne.symm hvp) (Ne.symm hap) hmeq
  exact ⟨s, δ, hs0, hs1, hδ, hmeq⟩

/-- **The lower middle `q`**: `q = v + s (a − v) + δ u` with `0 < s < 1`, `δ < 0`. -/
theorem q_coords (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ < 0 ∧ q = v + s • (a - v) + δ • u := by
  obtain ⟨s, δ, hδ, hmeq⟩ := E.hqu
  obtain ⟨-, -, -, -, hvq, -, -, -, -, haq, -⟩ := E.ne7
  obtain ⟨hs0, hs1⟩ := E.side_s E.hq (Ne.symm hvq) (Ne.symm haq) hmeq
  exact ⟨s, δ, hs0, hs1, hδ, hmeq⟩

/-- **The middle `n` of `F_b`** lies over the open side `(b, v)`: `n = v + s (b − v) + δ u` with
`0 < s < 1` and `δ ≠ 0`. -/
theorem n_coords (E : VtxConf V u v a c b p q n Na Nb κa κb) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ n = v + s • (b - v) + δ • u := by
  obtain ⟨hva, hvc, hvb, hvp, hvq, hvn, hac, hab, hap, haq, han, hcb, hcp, hcq, hcn, hbp,
    hbq, hbn, -⟩ := E.ne7
  have hNm : ⟪Nb, n - v⟫ = 0 := by
    rw [inner_sub_right, E.inner_Nb_n, E.inner_Nb_v, sub_self]
  obtain ⟨s, δ, hsd⟩ := EdgeConf.exists_coords_of_perp E.Nb_bv E.Nb_u hNm E.cross_bv E.Nb_ne
  have hmeq : n = v + s • (b - v) + δ • u := by rw [add_assoc, ← hsd]; abel
  have hs0 : 0 < s := by
    have hle := (E.left n E.hn).1
    have e : det3 (a - v) (n - v) u = s * det3 (a - v) (b - v) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hle
    have hs0 : 0 ≤ s := nonneg_of_mul_nonneg_left hle E.dab_pos
    refine lt_of_le_of_ne hs0 fun h0 => ?_
    rw [← h0, zero_smul, add_zero] at hmeq
    apply E.cross_ne E.hv E.hn hvn
    rw [hmeq, add_sub_cancel_left, cross_smul_left_self]
  have hs1 : s < 1 := by
    have hle := (E.left n E.hn).2.2.1
    have e : det3 (b - c) (n - c) u = (1 - s) * det3 (b - c) (v - c) u := by
      rw [hmeq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e] at hle
    have hpos := E.det_cb_pos E.hv hvc hvb
    have hs1 : 0 ≤ 1 - s := nonneg_of_mul_nonneg_left hle hpos
    refine lt_of_le_of_ne (by linarith) fun h1 => ?_
    have hmeq' : n = b + δ • u := by rw [hmeq, h1, one_smul]; abel
    apply E.cross_ne E.hb E.hn hbn
    rw [hmeq', add_sub_cancel_left, cross_smul_left_self]
  refine ⟨s, δ, hs0, hs1, ?_, hmeq⟩
  rintro rfl
  rw [zero_smul, add_zero] at hmeq
  exact E.noSeg v E.hv b E.hb n E.hn (Ne.symm hvn) (Ne.symm hbn) s hs0 hs1 hmeq

/-- A vector perpendicular to `u` and to the chord `a − v` is a multiple of `N_a`. -/
theorem eq_smul_Na (E : VtxConf V u v a c b p q n Na Nb κa κb) {X : ℝ³}
    (hXu : ⟪X, u⟫ = 0) (hXa : ⟪X, a - v⟫ = 0) : ∃ r : ℝ, X = r • Na := by
  set C := cross (a - v) u with hC
  have hC0 : C ≠ 0 := E.cross_av
  have h1 : cross C X = 0 := by
    rw [hC, cross_cross_eq, real_inner_comm, hXa, real_inner_comm, hXu, zero_smul, zero_smul,
      sub_zero]
  have h2 : cross C Na = 0 := by
    rw [hC, cross_cross_eq, real_inner_comm, E.Na_av, real_inner_comm, E.Na_u, zero_smul,
      zero_smul, sub_zero]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, X = t • C := ⟨_, eq_smul_of_cross_eq_zero hC0 h1⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ℝ, Na = t' • C := ⟨_, eq_smul_of_cross_eq_zero hC0 h2⟩
  have ht'0 : t' ≠ 0 := by rintro rfl; rw [zero_smul] at ht'; exact E.Na_ne ht'
  refine ⟨t / t', ?_⟩
  rw [ht, ht', smul_smul, div_mul_cancel₀ _ ht'0]

end VtxConf

end Minimality

end
