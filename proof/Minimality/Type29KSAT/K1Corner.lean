module

public import Minimality.Type29TSAT.TTop
public import Minimality.LevelCorner
public import Minimality.Oct9Par
public import Minimality.BadViews
public import Minimality.Type29SAT.Nf
public import Minimality.Type29SAT.Mir
public import Minimality.Type29Bridge
public import Minimality.Type29Faces

@[expose] public section

/-!
# Type 29, the trirectangular corner stratum `Z`: corner geometry and the clause bridges

Geometry (`par_id`, `csl29`, `lcsl29`): an edge parallel to a facet normal at a trirectangular corner transfers signs.
Literal bridges (`cslC`, `lcslC`, `cslC_true`, `lcslC_true`) turn these into SAT literals, giving the unit and clause
lists `unitsK1a`, `clausesK1` and the reduction `nf29_K1_Z_of_core` of the stratum to an unsatisfiable core.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K1
open Minimality.H29T.SAT

variable {x : Fin 7 → ℝ³}

/-- **The corner stratum `Z`**: vertex `6` is trirectangular (its three edges `63, 64, 65` pairwise orthogonal). -/
def CornerZ (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 3 - x 6, x 4 - x 6⟫ = 0 ∧ ⟪x 3 - x 6, x 5 - x 6⟫ = 0 ∧ ⟪x 4 - x 6, x 5 - x 6⟫ = 0

/-! ### Part 1: geometry -/

theorem cross_ne_zero_of_orth {a b : ℝ³} (ha : a ≠ 0) (hb : b ≠ 0) (hab : ⟪a, b⟫ = 0) :
    cross a b ≠ 0 := by
  intro h
  have hb' := eq_smul_of_cross_eq_zero ha h
  have hba : ⟪b, a⟫ = 0 := by rw [real_inner_comm]; exact hab
  rw [hba, zero_div, zero_smul] at hb'
  exact hb hb'

/-- Two vectors orthogonal to the same independent pair are parallel, in the form of an identity. -/
theorem par_id {a b e N : ℝ³} (hc : cross a b ≠ 0) (he1 : ⟪e, a⟫ = 0) (he2 : ⟪e, b⟫ = 0)
    (hN1 : ⟪N, a⟫ = 0) (hN2 : ⟪N, b⟫ = 0) (y : ℝ³) :
    ⟪y, e⟫ * ⟪e, N⟫ = ⟪e, e⟫ * ⟪y, N⟫ := by
  obtain ⟨s, rfl⟩ := eq_smul_cross_of_perp hc he1 he2
  obtain ⟨t, rfl⟩ := eq_smul_cross_of_perp hc hN1 hN2
  simp only [real_inner_smul_left, real_inner_smul_right]; ring

theorem fac_zero (F : S0xFac 9 s0x_S29 x) {t : Fin 9} {i j : Fin 7} (hi : i ∈ s0x_S29 t)
    (hj : j ∈ s0x_S29 t) : ⟪F.N t, x i - x j⟫ = 0 := by
  rw [F.inner_sub, F.zero t i hi, F.zero t j hj]; ring

theorem fac_neg (F : S0xFac 9 s0x_S29 x) {t : Fin 9} {i j : Fin 7} (hi : i ∉ s0x_S29 t)
    (hj : j ∈ s0x_S29 t) : ⟪F.N t, x i - x j⟫ < 0 := by
  rw [F.inner_sub, F.zero t j hj]; have := F.neg t i hi; linarith

theorem fac_le (F : S0xFac 9 s0x_S29 x) {t : Fin 9} (i : Fin 7) {j : Fin 7}
    (hj : j ∈ s0x_S29 t) : ⟪F.N t, x i - x j⟫ ≤ 0 := by
  rw [F.inner_sub, F.zero t j hj]; have := F.le t i; linarith

theorem sub_ne_of_ne (F : S0xFac 9 s0x_S29 x) {i j : Fin 7} (h : i ≠ j) : x i - x j ≠ 0 :=
  sub_ne_zero.2 (fun e => h (inj_of_fac F e))

/-- The edge `x J - x 6` of the corner is parallel to the normal of a facet `t` through `6, M, K` that misses `J`:
signs transfer (`⟪y, e⟫` has the sign opposite to `⟪N t, y⟫`). -/
theorem edge_par (F : S0xFac 9 s0x_S29 x) (J M K : Fin 7) (t : Fin 9) (hM6 : M ≠ 6) (hK6 : K ≠ 6)
    (hJK : ⟪x J - x 6, x K - x 6⟫ = 0) (hJM : ⟪x J - x 6, x M - x 6⟫ = 0)
    (hMK : ⟪x M - x 6, x K - x 6⟫ = 0)
    (hM : M ∈ s0x_S29 t) (hK : K ∈ s0x_S29 t) (h6 : (6 : Fin 7) ∈ s0x_S29 t) (hJ : J ∉ s0x_S29 t) :
    ⟪x J - x 6, F.N t⟫ < 0 ∧
      ∀ y : ℝ³, ⟪y, x J - x 6⟫ * ⟪x J - x 6, F.N t⟫ = ⟪x J - x 6, x J - x 6⟫ * ⟪y, F.N t⟫ := by
  have hc := cross_ne_zero_of_orth (sub_ne_of_ne F hM6) (sub_ne_of_ne F hK6) hMK
  have hlt : ⟪x J - x 6, F.N t⟫ < 0 := by rw [real_inner_comm]; exact fac_neg F hJ h6
  refine ⟨hlt, par_id hc hJM hJK ?_ ?_⟩
  · exact fac_zero F hM h6
  · exact fac_zero F hK h6

/-- Sign transfer, in the three forms used. -/
theorem sign_tr {a b c d : ℝ} (h : a * b = c * d) (hb : b < 0) (hc : 0 < c) :
    (d ≤ 0 → 0 ≤ a) ∧ (d < 0 → 0 < a) ∧ (d = 0 → a = 0) := by
  refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
  · by_contra ha; rw [not_le] at ha; nlinarith [mul_pos_of_neg_of_neg ha hb, mul_nonpos_of_nonneg_of_nonpos hc.le hd]
  · by_contra ha; rw [not_lt] at ha; nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb.le, mul_neg_of_pos_of_neg hc hd]
  · rw [hd, mul_zero] at h; rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd h hb.ne

/-- **The Corner Slide Lemma at the trirectangular corner `6` of a type 29 shape.**  `J, M, K` are the three
corner neighbours, `tg` the triangular facet `6 J M`, `te` a facet through `6, M, K` missing `J` (so its normal is
parallel to `x J - x 6`), `tf` a facet through `6, J, K` missing `M`.  If every deep vertex `i < 3` off `te`
is strictly short of `J` along `6 → J`, and some vertex `q` is beyond `M` along `6 → M`, the shape is Rupert. -/
theorem csl29 (F : S0xFac 9 s0x_S29 x) (J M K : Fin 7) (tg te tf : Fin 9)
    (hJ6 : J ≠ 6) (hM6 : M ≠ 6) (hK6 : K ≠ 6)
    (hJM : ⟪x J - x 6, x M - x 6⟫ = 0) (hJK : ⟪x J - x 6, x K - x 6⟫ = 0)
    (hMK : ⟪x M - x 6, x K - x 6⟫ = 0)
    (hg : ∀ i, i ∈ s0x_S29 tg ↔ i = J ∨ i = M ∨ i = 6) (hKg : K ∉ s0x_S29 tg)
    (hte : M ∈ s0x_S29 te ∧ K ∈ s0x_S29 te ∧ (6 : Fin 7) ∈ s0x_S29 te ∧ J ∉ s0x_S29 te)
    (htf : J ∈ s0x_S29 tf ∧ K ∈ s0x_S29 tf ∧ (6 : Fin 7) ∈ s0x_S29 tf ∧ M ∉ s0x_S29 tf)
    (hte3 : ∀ i : Fin 7, 3 ≤ i.val → i ∉ s0x_S29 te → i = J)
    (hNj : ∀ i : Fin 7, i.val < 3 → i ∉ s0x_S29 te → ⟪x i - x J, x J - x 6⟫ < 0)
    (q : Fin 7) (hOm : 0 < ⟪x q - x M, x M - x 6⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨heN, hepar⟩ := edge_par F J M K te hM6 hK6 hJK hJM hMK hte.1 hte.2.1 hte.2.2.1 hte.2.2.2
  have hMJ : ⟪x M - x 6, x J - x 6⟫ = 0 := by rw [real_inner_comm]; exact hJM
  obtain ⟨hfN, hfpar⟩ := edge_par F M J K tf hJ6 hK6 hMK hMJ hJK htf.1 htf.2.1 htf.2.2.1 htf.2.2.2
  have hee : 0 < ⟪x J - x 6, x J - x 6⟫ := real_inner_self_pos.2 (sub_ne_of_ne F hJ6)
  have hff : 0 < ⟪x M - x 6, x M - x 6⟫ := real_inner_self_pos.2 (sub_ne_of_ne F hM6)
  have hgJ : J ∈ s0x_S29 tg := (hg J).2 (Or.inl rfl)
  have hgM : M ∈ s0x_S29 tg := (hg M).2 (Or.inr (Or.inl rfl))
  have hg6 : (6 : Fin 7) ∈ s0x_S29 tg := (hg 6).2 (Or.inr (Or.inr rfl))
  refine Minimality.Split.Corner.corner_euclid x 6 J M (x J - x 6) (x M - x 6) (-F.N tg) rfl rfl
    (sub_ne_of_ne F hJ6) (sub_ne_of_ne F hM6) ?_ hJM ?_ ?_ ?_ ?_ ?_ ⟨q, ?_⟩
  · intro h
    have := fac_neg F hKg hg6
    rw [neg_eq_zero.1 h, inner_zero_left] at this
    exact lt_irrefl 0 this
  · rw [inner_neg_right, real_inner_comm, fac_zero F hgJ hg6, neg_zero]
  · rw [inner_neg_right, real_inner_comm, fac_zero F hgM hg6, neg_zero]
  · intro i h1 h2 h3
    have hi : i ∉ s0x_S29 tg := by
      rw [hg]; rintro (h | h | h)
      exacts [h2 h, h3 h, h1 h]
    rw [inner_neg_right, real_inner_comm]; linarith [fac_neg F hi hg6]
  · intro i
    refine ⟨(sign_tr (hepar _) heN hee).1 ?_, (sign_tr (hfpar _) hfN hff).1 ?_⟩
    · rw [real_inner_comm]; exact fac_le F i hte.2.2.1
    · rw [real_inner_comm]; exact fac_le F i htf.2.2.1
  · intro i hiJ
    have key : ⟪x i - x 6, x J - x 6⟫ - ⟪x J - x 6, x J - x 6⟫ = ⟪x i - x J, x J - x 6⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    by_cases hi : i ∈ s0x_S29 te
    · have : ⟪x i - x 6, x J - x 6⟫ = 0 := (sign_tr (hepar _) heN hee).2.2 (by
        rw [real_inner_comm]; exact fac_zero F hi hte.2.2.1)
      linarith
    · by_cases h3 : i.val < 3
      · linarith [hNj i h3 hi]
      · exact absurd (hte3 i (by omega) hi) hiJ
  · have key : ⟪x q - x 6, x M - x 6⟫ - ⟪x M - x 6, x M - x 6⟫ = ⟪x q - x M, x M - x 6⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith

/-- **The Level Corner Slide Lemma at the trirectangular corner `6`.**  As `csl29`, and: the wall facet `te` is
exactly `{Wv, M, K, 6}`; the deep vertex `P < 3` (off `te` and off `tf`) is level with `J` (`⟪N te, x P - x J⟫ = 0`);
every other deep vertex `i < 3` off `te` is strictly short of `J`; the wall vertex `Wv` is beyond `M`. -/
theorem lcsl29 (F : S0xFac 9 s0x_S29 x) (J M K P Wv : Fin 7) (tg te tf : Fin 9)
    (hJ6 : J ≠ 6) (hM6 : M ≠ 6) (hK6 : K ≠ 6)
    (hJM : ⟪x J - x 6, x M - x 6⟫ = 0) (hJK : ⟪x J - x 6, x K - x 6⟫ = 0)
    (hMK : ⟪x M - x 6, x K - x 6⟫ = 0)
    (hg : ∀ i, i ∈ s0x_S29 tg ↔ i = J ∨ i = M ∨ i = 6) (hKg : K ∉ s0x_S29 tg)
    (hte : ∀ i, i ∈ s0x_S29 te ↔ i = Wv ∨ i = M ∨ i = K ∨ i = 6) (hJte : J ∉ s0x_S29 te)
    (htf : J ∈ s0x_S29 tf ∧ K ∈ s0x_S29 tf ∧ (6 : Fin 7) ∈ s0x_S29 tf ∧ M ∉ s0x_S29 tf)
    (hte3 : ∀ i : Fin 7, 3 ≤ i.val → i ∉ s0x_S29 te → i = J)
    (hPtf : P ∉ s0x_S29 tf)
    (hlev : ⟪F.N te, x P - x J⟫ = 0)
    (hNj : ∀ i : Fin 7, i.val < 3 → i ∉ s0x_S29 te → i ≠ P → ⟪x i - x J, x J - x 6⟫ < 0)
    (hWf : 0 < ⟪x Wv - x M, x M - x 6⟫) :
    IsRupert (univ.image x) := by
  have hteM : M ∈ s0x_S29 te := (hte M).2 (Or.inr (Or.inl rfl))
  have hteK : K ∈ s0x_S29 te := (hte K).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hte6 : (6 : Fin 7) ∈ s0x_S29 te := (hte 6).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hteW : Wv ∈ s0x_S29 te := (hte Wv).2 (Or.inl rfl)
  obtain ⟨heN, hepar⟩ := edge_par F J M K te hM6 hK6 hJK hJM hMK hteM hteK hte6 hJte
  have hMJ : ⟪x M - x 6, x J - x 6⟫ = 0 := by rw [real_inner_comm]; exact hJM
  obtain ⟨hfN, hfpar⟩ := edge_par F M J K tf hJ6 hK6 hMK hMJ hJK htf.1 htf.2.1 htf.2.2.1 htf.2.2.2
  have hee : 0 < ⟪x J - x 6, x J - x 6⟫ := real_inner_self_pos.2 (sub_ne_of_ne F hJ6)
  have hff : 0 < ⟪x M - x 6, x M - x 6⟫ := real_inner_self_pos.2 (sub_ne_of_ne F hM6)
  have hgJ : J ∈ s0x_S29 tg := (hg J).2 (Or.inl rfl)
  have hgM : M ∈ s0x_S29 tg := (hg M).2 (Or.inr (Or.inl rfl))
  have hg6 : (6 : Fin 7) ∈ s0x_S29 tg := (hg 6).2 (Or.inr (Or.inr rfl))
  refine Minimality.Split.LevelCorner.level_corner_euclid x 6 J M P Wv (x J - x 6) (x M - x 6) (-F.N tg)
    rfl rfl (sub_ne_of_ne F hJ6) (sub_ne_of_ne F hM6) ?_ hJM ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h
    have := fac_neg F hKg hg6
    rw [neg_eq_zero.1 h, inner_zero_left] at this
    exact lt_irrefl 0 this
  · rw [inner_neg_right, real_inner_comm, fac_zero F hgJ hg6, neg_zero]
  · rw [inner_neg_right, real_inner_comm, fac_zero F hgM hg6, neg_zero]
  · intro i h1 h2 h3
    have hi : i ∉ s0x_S29 tg := by
      rw [hg]; rintro (h | h | h)
      exacts [h2 h, h3 h, h1 h]
    rw [inner_neg_right, real_inner_comm]; linarith [fac_neg F hi hg6]
  · intro i
    refine ⟨(sign_tr (hepar _) heN hee).1 ?_, (sign_tr (hfpar _) hfN hff).1 ?_⟩
    · rw [real_inner_comm]; exact fac_le F i hte6
    · rw [real_inner_comm]; exact fac_le F i htf.2.2.1
  · -- hPe: P level with J
    have h0 : ⟪x P - x J, x J - x 6⟫ = 0 := (sign_tr (hepar _) heN hee).2.2 (by
      rw [real_inner_comm]; exact hlev)
    have : ⟪x P - x 6, x J - x 6⟫ = ⟪x P - x J, x J - x 6⟫ + ⟪x J - x 6, x J - x 6⟫ := by
      rw [← inner_add_left]; congr 1; abel
    linarith
  · -- hPf: P off the floor wall
    exact (sign_tr (hfpar _) hfN hff).2.1 (by rw [real_inner_comm]; exact fac_neg F hPtf htf.2.2.1)
  · intro i hiJ hiP
    have key : ⟪x i - x 6, x J - x 6⟫ - ⟪x J - x 6, x J - x 6⟫ = ⟪x i - x J, x J - x 6⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    by_cases hi : i ∈ s0x_S29 te
    · have : ⟪x i - x 6, x J - x 6⟫ = 0 := (sign_tr (hepar _) heN hee).2.2 (by
        rw [real_inner_comm]; exact fac_zero F hi hte6)
      linarith
    · by_cases h3 : i.val < 3
      · linarith [hNj i h3 hi hiP]
      · exact absurd (hte3 i (by omega) hi) hiJ
  · exact (sign_tr (hepar _) heN hee).2.2 (by rw [real_inner_comm]; exact fac_zero F hteW hte6)
  · have key : ⟪x Wv - x 6, x M - x 6⟫ - ⟪x M - x 6, x M - x 6⟫ = ⟪x Wv - x M, x M - x 6⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith
  · intro i hiW h0
    by_cases hi : i ∈ s0x_S29 te
    · rcases (hte i).1 hi with h | h | h | h
      · exact absurd h hiW
      · rw [h]
      · rw [h, real_inner_comm, hMK]; exact hff.le
      · rw [h, sub_self, inner_zero_left]; exact hff.le
    · have := (sign_tr (hepar _) heN hee).2.1 (by rw [real_inner_comm]; exact fac_neg F hi hte6)
      linarith

/-! ### Part 2: the clause bridges -/

/-- An edge `a < b` of the 21: its index, ends and difference. -/
theorem EI_ok : ∀ a b : Fin 7, a < b → EA (EI a.val b.val) = a.val ∧ EB (EI a.val b.val) = b.val ∧
    EI a.val b.val < 21 := by decide

theorem dv_EI (F : S0xFac 9 s0x_S29 x) (a b : Fin 7) (h : a < b) :
    (geoF F).dv (EI a.val b.val) = x a - x b := by
  obtain ⟨h1, h2, -⟩ := EI_ok a b h
  simp only [Geo.dv, h1, h2, geoF_x]

/-- A false `T:e.f~-` literal (`(false, tq e f)`) says `⟪d_e, d_f⟫ < 0`. -/
theorem tq_false {g : Geo} {e f : Nat} (he : e < 21) (hf : f < 21)
    (h : evalW (rhoW g) (false, W.base (V.tq e f)) ≠ true) : ⟪g.dv e, g.dv f⟫ < 0 := by
  simp only [evalW, rhoW_base, rho, vv_lt g he, vv_lt g hf] at h
  simpa using h

/-- A false `T:e.f~+` literal (`(false, tp e f)`) says `0 < ⟪d_e, d_f⟫`. -/
theorem tp_false {g : Geo} {e f : Nat} (he : e < 21) (hf : f < 21)
    (h : evalW (rhoW g) (false, W.base (V.tp e f)) ≠ true) : 0 < ⟪g.dv e, g.dv f⟫ := by
  simp only [evalW, rhoW_base, rho, vv_lt g he, vv_lt g hf] at h
  simpa using h

/-- False `F:pq+` and `F:pq-` literals say that the facing atom `⟪N t, x p - x q⟫` is zero. -/
theorem fv_false {g : Geo} {t p q : Nat}
    (h1 : evalW (rhoW g) (true, W.base (V.fv t p q)) ≠ true)
    (h2 : evalW (rhoW g) (true, W.base (V.ng (V.fv t p q))) ≠ true) :
    ⟪g.N t, g.x p - g.x q⟫ = 0 := by
  change (true == rho g (V.fv t p q)) ≠ true at h1
  change (true == rho g (V.ng (V.fv t p q))) ≠ true at h2
  simp only [rho, Geo.atom] at h1 h2
  simp only [ne_eq, beq_iff_eq] at h1 h2
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact h2 (by simp [h])
  · exact h1 (by simp [h])

theorem cornerZ_pair (hZ : CornerZ x) (a b : Fin 7) (ha : 3 ≤ a.val ∧ a.val ≤ 5)
    (hb : 3 ≤ b.val ∧ b.val ≤ 5) (hab : a ≠ b) : ⟪x a - x 6, x b - x 6⟫ = 0 := by
  obtain ⟨z1, z2, z3⟩ := hZ
  fin_cases a <;> fin_cases b <;> simp at ha hb hab ⊢ <;>
    first | exact z1 | exact z2 | exact z3 | (rw [real_inner_comm]; first | exact z1 | exact z2 | exact z3)

open V W in
/-- The CSL clause at `(k; j, m) = (K; J, M)` with the point `q` beyond `M`:
`T:d0J.dJ6~- T:d1J.dJ6~- T:d2J.dJ6~- T:dqM.dM6~+`. -/
def cslC (J M q : Nat) : List LitW :=
  [(false, base (tq (EI 0 J) (EI J 6))), (false, base (tq (EI 1 J) (EI J 6))),
   (false, base (tq (EI 2 J) (EI J 6))), (false, base (tp (EI q M) (EI M 6)))]

open V W in
/-- The LCSL clause with `P` level with `J` (facet `F = 5`), `R` the other deep vertex, the wall vertex `Wv`
beyond `M`: `F:PJ+ F:PJ- T:dRJ.dJ6~- T:dWM.dM6~+`. -/
def lcslC (P R J M Wv : Nat) : List LitW :=
  [(true, base (fv 5 P J)), (true, base (ng (fv 5 P J))), (false, base (tq (EI R J) (EI J 6))),
   (false, base (tp (EI Wv M) (EI M 6)))]

/-- The four CSL orderings `(J, M, K, tg, te, tf)` at the corner `6`. -/
def cslOrds : List (Fin 7 × Fin 7 × Fin 7 × Fin 9 × Fin 9 × Fin 9) :=
  [(3, 4, 5, 7, 5, 8), (4, 3, 5, 7, 8, 5), (3, 5, 4, 8, 5, 7), (5, 3, 4, 8, 7, 5)]

/-- The structural facts `csl29` needs, for one ordering. -/
def OrdOK (J M K : Fin 7) (tg te tf : Fin 9) : Prop :=
  J ≠ 6 ∧ M ≠ 6 ∧ K ≠ 6 ∧ (3 ≤ J.val ∧ J.val ≤ 5) ∧ (3 ≤ M.val ∧ M.val ≤ 5) ∧ (3 ≤ K.val ∧ K.val ≤ 5) ∧
    J ≠ M ∧ J ≠ K ∧ M ≠ K ∧
    (∀ i, i ∈ s0x_S29 tg ↔ i = J ∨ i = M ∨ i = 6) ∧ K ∉ s0x_S29 tg ∧
    (M ∈ s0x_S29 te ∧ K ∈ s0x_S29 te ∧ (6 : Fin 7) ∈ s0x_S29 te ∧ J ∉ s0x_S29 te) ∧
    (J ∈ s0x_S29 tf ∧ K ∈ s0x_S29 tf ∧ (6 : Fin 7) ∈ s0x_S29 tf ∧ M ∉ s0x_S29 tf) ∧
    (∀ i : Fin 7, 3 ≤ i.val → i ∉ s0x_S29 te → i = J)

theorem cslOrds_ok : ∀ o ∈ cslOrds, OrdOK o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2.1 o.2.2.2.2.2 := by
  unfold OrdOK; decide

/-- **CSL clause bridge.**  On `Z`, a non-Rupert type 29 shape satisfies every CSL clause. -/
theorem cslC_true (F : S0xFac 9 s0x_S29 x) (hZ : CornerZ x) (hNR : ¬ IsRupert (univ.image x))
    (J M K : Fin 7) (tg te tf : Fin 9) (ho : (J, M, K, tg, te, tf) ∈ cslOrds) (q : Fin 7) (hq : q.val < 3) :
    HoldsW (rhoW (geoF F)) (cslC J.val M.val q.val) := by
  have hok := cslOrds_ok _ ho
  dsimp only at hok
  obtain ⟨hJ6, hM6, hK6, hJ, hM, hK, hJM, hJK, hMK, hg, hKg, hte, htf, hte3⟩ := hok
  by_contra hC
  have hl : ∀ l ∈ cslC J.val M.val q.val, evalW (rhoW (geoF F)) l ≠ true :=
    fun l hl he => hC ⟨l, hl, he⟩
  have hJ6' : J < 6 := Fin.lt_def.2 (by simp; omega)
  have hM6' : M < 6 := Fin.lt_def.2 (by simp; omega)
  have eJ6 : (geoF F).dv (EI J.val 6) = x J - x 6 := by simpa using dv_EI F J 6 hJ6'
  have eM6 : (geoF F).dv (EI M.val 6) = x M - x 6 := by simpa using dv_EI F M 6 hM6'
  have lJ6 : EI J.val 6 < 21 := by simpa using (EI_ok J 6 hJ6').2.2
  have lM6 : EI M.val 6 < 21 := by simpa using (EI_ok M 6 hM6').2.2
  have tJ : ∀ i : Fin 7, i.val < 3 → evalW (rhoW (geoF F)) (false, W.base (V.tq (EI i.val J.val) (EI J.val 6)))
      ≠ true → ⟪x i - x J, x J - x 6⟫ < 0 := by
    intro i hi h
    have hiJ : i < J := Fin.lt_def.2 (by omega)
    have := tq_false (EI_ok i J hiJ).2.2 lJ6 h
    rwa [dv_EI F i J hiJ, eJ6] at this
  refine hNR (csl29 F J M K tg te tf hJ6 hM6 hK6 (cornerZ_pair hZ J M hJ hM hJM)
    (cornerZ_pair hZ J K hJ hK hJK) (cornerZ_pair hZ M K hM hK hMK) hg hKg hte htf hte3 ?_ q ?_)
  · intro i hi _
    apply tJ i hi
    apply hl
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [cslC]
  · have hqM : q < M := Fin.lt_def.2 (by omega)
    have := tp_false (EI_ok q M hqM).2.2 lM6 (hl _ (by simp [cslC]))
    rwa [dv_EI F q M hqM, eM6] at this

/-- The four LCSL orderings `(J, M, K, P, R, Wv, tg, te, tf)`: `P` level with `J = 3`, `R` the other deep vertex, the
wall `te = F = 1456` with the wall vertex `Wv = 1` beyond `M`. -/
def lcslOrds : List (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 9 × Fin 9 × Fin 9) :=
  [(3, 4, 5, 0, 2, 1, 7, 5, 8), (3, 5, 4, 0, 2, 1, 8, 5, 7), (3, 4, 5, 2, 0, 1, 7, 5, 8), (3, 5, 4, 2, 0, 1, 8, 5, 7)]

/-- The structural facts `lcsl29` needs, for one ordering. -/
def LOrdOK (J M K P R Wv : Fin 7) (tg te tf : Fin 9) : Prop :=
  OrdOK J M K tg te tf ∧ te = 5 ∧ (∀ i, i ∈ s0x_S29 te ↔ i = Wv ∨ i = M ∨ i = K ∨ i = 6) ∧
    P ∉ s0x_S29 tf ∧ P.val < 3 ∧ R.val < 3 ∧ Wv.val < 3 ∧
    (∀ i : Fin 7, i.val < 3 → i ∉ s0x_S29 te → i ≠ P → i = R)

theorem lcslOrds_ok : ∀ o ∈ lcslOrds, LOrdOK o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2.1 o.2.2.2.2.2.1
    o.2.2.2.2.2.2.1 o.2.2.2.2.2.2.2.1 o.2.2.2.2.2.2.2.2 := by
  intro o ho
  simp only [lcslOrds, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold LOrdOK OrdOK
  rcases ho with rfl | rfl | rfl | rfl <;>
    (dsimp only; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **LCSL clause bridge.**  On `Z`, a non-Rupert type 29 shape satisfies every LCSL clause. -/
theorem lcslC_true (F : S0xFac 9 s0x_S29 x) (hZ : CornerZ x) (hNR : ¬ IsRupert (univ.image x))
    (J M K P R Wv : Fin 7) (tg te tf : Fin 9) (ho : (J, M, K, P, R, Wv, tg, te, tf) ∈ lcslOrds) :
    HoldsW (rhoW (geoF F)) (lcslC P.val R.val J.val M.val Wv.val) := by
  have hok := lcslOrds_ok _ ho
  dsimp only at hok
  obtain ⟨⟨hJ6, hM6, hK6, hJ, hM, hK, hJM, hJK, hMK, hg, hKg, -, htf, hte3⟩, rfl, hte, hPtf, hP, hR, hWv,
    hPR⟩ := hok
  have hJte : J ∉ s0x_S29 5 := by
    rw [hte]; rintro (h | h | h | h)
    · subst h; omega
    · exact hJM h
    · exact hJK h
    · exact hJ6 h
  by_contra hC
  have hl : ∀ l ∈ lcslC P.val R.val J.val M.val Wv.val, evalW (rhoW (geoF F)) l ≠ true :=
    fun l hl he => hC ⟨l, hl, he⟩
  have hJ6' : J < 6 := Fin.lt_def.2 (by simp; omega)
  have hM6' : M < 6 := Fin.lt_def.2 (by simp; omega)
  have eJ6 : (geoF F).dv (EI J.val 6) = x J - x 6 := by simpa using dv_EI F J 6 hJ6'
  have eM6 : (geoF F).dv (EI M.val 6) = x M - x 6 := by simpa using dv_EI F M 6 hM6'
  have lJ6 : EI J.val 6 < 21 := by simpa using (EI_ok J 6 hJ6').2.2
  have lM6 : EI M.val 6 < 21 := by simpa using (EI_ok M 6 hM6').2.2
  have hlev : ⟪F.N 5, x P - x J⟫ = 0 := by
    have := fv_false (t := 5) (p := P.val) (q := J.val) (hl _ (by simp [lcslC])) (hl _ (by simp [lcslC]))
    rwa [show (5 : Nat) = (5 : Fin 9).val from rfl, geoF_N, geoF_x, geoF_x] at this
  refine hNR (lcsl29 F J M K P Wv tg 5 tf hJ6 hM6 hK6 (cornerZ_pair hZ J M hJ hM hJM)
    (cornerZ_pair hZ J K hJ hK hJK) (cornerZ_pair hZ M K hM hK hMK) hg hKg hte hJte htf hte3 hPtf hlev ?_ ?_)
  · intro i hi hite hiP
    have hiR := hPR i hi hite hiP
    subst hiR
    have hiJ : i < J := Fin.lt_def.2 (by omega)
    have := tq_false (EI_ok i J hiJ).2.2 lJ6 (hl _ (by simp [lcslC]))
    rwa [dv_EI F i J hiJ, eJ6] at this
  · have hWM : Wv < M := Fin.lt_def.2 (by omega)
    have := tp_false (EI_ok Wv M hWM).2.2 lM6 (hl _ (by simp [lcslC]))
    rwa [dv_EI F Wv M hWM, eM6] at this

/-! ### Part 3: the class literals, the clause list, the frame -/

open V W in
/-- The class literals of class K1a on `Z`: `[0134]+ [0245]- [1235]-` and the six zero literals of
`T:d36.d46`, `T:d36.d56`, `T:d46.d56` (edges `17 = 36`, `19 = 46`, `20 = 56`). -/
def unitsK1a : List LitW :=
  [(true, base (br 0 1 3 4)), (true, base (ng (br 0 2 4 5))), (true, base (ng (br 1 2 3 5))),
   (false, base (tp 17 19)), (false, base (tq 17 19)), (false, base (tp 17 20)), (false, base (tq 17 20)),
   (false, base (tp 19 20)), (false, base (tq 19 20))]

/-- **All corner clauses**: the 12 CSL clauses (4 orderings, `q = 0, 1, 2`) and the 4 LCSL clauses.  A core may use
any subset (`rowKs` accepts a family 26 row covering one of them). -/
def clausesK1 : List (List LitW) :=
  [cslC 3 4 0, cslC 3 4 1, cslC 3 4 2, cslC 4 3 0, cslC 4 3 1, cslC 4 3 2,
   cslC 3 5 0, cslC 3 5 1, cslC 3 5 2, cslC 5 3 0, cslC 5 3 1, cslC 5 3 2,
   lcslC 0 2 3 4 1, lcslC 0 2 3 5 1, lcslC 2 0 3 4 1, lcslC 2 0 3 5 1]

/-- **The soundness obligation of `rowKs` for the corner clauses**: every one holds on a non-Rupert shape on `Z`. -/
theorem clausesK1_true (F : S0xFac 9 s0x_S29 x) (hZ : CornerZ x) (hNR : ¬ IsRupert (univ.image x)) :
    ∀ C ∈ clausesK1, HoldsW (rhoW (geoF F)) C := by
  intro C hC
  simp only [clausesK1, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cslC_true F hZ hNR 3 4 5 7 5 8 (by decide) 0 (by decide)
  · exact cslC_true F hZ hNR 3 4 5 7 5 8 (by decide) 1 (by decide)
  · exact cslC_true F hZ hNR 3 4 5 7 5 8 (by decide) 2 (by decide)
  · exact cslC_true F hZ hNR 4 3 5 7 8 5 (by decide) 0 (by decide)
  · exact cslC_true F hZ hNR 4 3 5 7 8 5 (by decide) 1 (by decide)
  · exact cslC_true F hZ hNR 4 3 5 7 8 5 (by decide) 2 (by decide)
  · exact cslC_true F hZ hNR 3 5 4 8 5 7 (by decide) 0 (by decide)
  · exact cslC_true F hZ hNR 3 5 4 8 5 7 (by decide) 1 (by decide)
  · exact cslC_true F hZ hNR 3 5 4 8 5 7 (by decide) 2 (by decide)
  · exact cslC_true F hZ hNR 5 3 4 8 7 5 (by decide) 0 (by decide)
  · exact cslC_true F hZ hNR 5 3 4 8 7 5 (by decide) 1 (by decide)
  · exact cslC_true F hZ hNR 5 3 4 8 7 5 (by decide) 2 (by decide)
  · exact lcslC_true F hZ hNR 3 4 5 0 2 1 7 5 8 (by decide)
  · exact lcslC_true F hZ hNR 3 5 4 0 2 1 8 5 7 (by decide)
  · exact lcslC_true F hZ hNR 3 4 5 2 0 1 7 5 8 (by decide)
  · exact lcslC_true F hZ hNR 3 5 4 2 0 1 8 5 7 (by decide)

/-- The class literals of K1a hold for the brackets `[0134] > 0`, `[0245] < 0`, `[1235] < 0` on `Z`. -/
theorem unitsK1a_true (F : S0xFac 9 s0x_S29 x) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0))
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hZ : CornerZ x) : ∀ l ∈ unitsK1a, evalW (rhoW (geoF F)) l = true := by
  obtain ⟨z1, z2, z3⟩ := hZ
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have v17 : (geoF F).vv 17 = x 3 - x 6 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e3, e6]
  have v19 : (geoF F).vv 19 = x 4 - x 6 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e4, e6]
  have v20 : (geoF F).vv 20 = x 5 - x 6 := by simp [Geo.vv, Geo.dv, EA, EB, edges, e5, e6]
  intro l hl
  simp only [unitsK1a, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show evalL (rho (geoF F)) (true, V.br 0 1 3 4) = true
    simp [evalL, rho, Geo.atom, e0, e1, e3, e4, h0]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 0 2 4 5)) = true
    simp [evalL, rho, Geo.atom, e0, e2, e4, e5, h1]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 2 3 5)) = true
    simp [evalL, rho, Geo.atom, e1, e2, e3, e5, h2]
  all_goals simp [evalW, rhoW_base, rho, v17, v19, v20, z1, z2, z3]

theorem cornerZ_mir (hZ : CornerZ x) : CornerZ (fun i => mir (x i)) := by
  obtain ⟨z1, z2, z3⟩ := hZ
  refine ⟨?_, ?_, ?_⟩ <;> simp only [← mir_sub, mir_inner] <;> assumption

theorem cornerZ_sigma (hZ : CornerZ x) : CornerZ (x ∘ sigma29) := by
  obtain ⟨z1, z2, z3⟩ := hZ
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Function.comp_apply, sigma29] <;> simp
  · exact z2
  · exact z1
  · rw [real_inner_comm]; exact z3

/-- **K1a on `Z` from the core theorem** (as `nf29_K2a_Z1_caseA_of_core`; mirror for `D < 0`). -/
theorem nf29_K1a_Z_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³}, S0xFac 9 s0x_S29 y →
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → 0 < det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      CornerZ y → IsRupert (univ.image y))
    (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0) (hV : N.V < 0) (hZ : CornerZ x) :
    IsRupert (univ.image x) := by
  obtain ⟨i0, i1, i2, i3⟩ := nf29_brackets N
  have hDD := N.hDD
  let F := s0x_fac29 N.facets
  rcases lt_or_gt_of_ne N.hD with hD | hD
  · refine isRupert_of_mir (hcore (mirFac F) ?_ ?_ ?_ ?_ (cornerZ_mir hZ))
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 2) - mir (x 0)) (mir (x 3) - mir (x 0))
      rw [mir_br, i0]; have := mul_neg_of_neg_of_pos hD hDD; linarith
    · show 0 < det3 (mir (x 1) - mir (x 0)) (mir (x 3) - mir (x 0)) (mir (x 4) - mir (x 0))
      rw [mir_br, i1]; have := mul_neg_of_neg_of_pos hD hb0; linarith
    · show det3 (mir (x 2) - mir (x 0)) (mir (x 4) - mir (x 0)) (mir (x 5) - mir (x 0)) < 0
      rw [mir_br, i2]; have := mul_pos_of_neg_of_neg hD hV; linarith
    · show det3 (mir (x 2) - mir (x 1)) (mir (x 3) - mir (x 1)) (mir (x 5) - mir (x 1)) < 0
      rw [mir_br, i3]; have := mul_pos_of_neg_of_neg hD ha2; linarith
  · exact hcore F (by rw [i0]; exact mul_pos hD hDD) (by rw [i1]; exact mul_pos hD hb0)
      (by rw [i2]; exact mul_neg_of_pos_of_neg hD hV) (by rw [i3]; exact mul_neg_of_pos_of_neg hD ha2) hZ

/-- **K1 on `Z` from the K1a core theorem**: K1b is the `σ`-image of K1a (`σ = (0 2)(4 5)` fixes `6` and `Z`). -/
theorem nf29_K1_Z_of_core
    (hcore : ∀ {y : Fin 7 → ℝ³}, S0xFac 9 s0x_S29 y →
      0 < det3 (y 1 - y 0) (y 2 - y 0) (y 3 - y 0) → 0 < det3 (y 1 - y 0) (y 3 - y 0) (y 4 - y 0) →
      det3 (y 2 - y 0) (y 4 - y 0) (y 5 - y 0) < 0 → det3 (y 2 - y 1) (y 3 - y 1) (y 5 - y 1) < 0 →
      CornerZ y → IsRupert (univ.image y))
    (N : NF29 x) (hK1 : (N.a2 < 0 ∧ 0 < N.b0 ∧ N.V < 0) ∨ (0 < N.a2 ∧ N.b0 < 0 ∧ 0 < N.V))
    (hZ : CornerZ x) : IsRupert (univ.image x) := by
  rcases hK1 with ⟨ha2, hb0, hV⟩ | ⟨ha2, hb0, hV⟩
  · exact nf29_K1a_Z_of_core hcore N ha2 hb0 hV hZ
  · have hv : N.sigma.V = -N.V := by simp only [NF29.sigma, NF29.V]; ring
    have := nf29_K1a_Z_of_core hcore N.sigma (by exact hb0) (by exact ha2) (by linarith)
      (cornerZ_sigma hZ)
    rwa [image_sigma29] at this


end Minimality.H29K1
