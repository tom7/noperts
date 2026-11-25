module

public import Minimality.WeakChord
public import Minimality.Type24HiddenCone
public import Minimality.SplitRim4
public import Minimality.AdjTie4
public import Minimality.MonoCorner
public import Minimality.RimOrder
public import Minimality.Type21SAT.Lex2

/-!
# GenRev24: generalization lemmas for the type-24 hole review

Combines the S3 (`robUni_of_strictUnimodal`, `weakChordArc_of_faceChordView`,
`anyFaceChord_iff_quad`) and S4 (`robUni_of_noAlt`, `RobUniO`, `robUni_iff_O`, `robUniLex_iff_O`,
`mono_at_c_of_splitRows`, `lexAny_of_splitAny_four`, `SplitLexAny`, `splitLexAny_isRupert`,
`splitLexAny_of_splitAny`, `exists_view_of_zeta`, `robUniLex_metric_free`, `cone_iff_back`)
lemmas in `Minimality.GenRev`.
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.GenRev

open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT
open Minimality.LexCell Minimality.Split

/-! ## S3: StrictUnimodal & FaceChordView -/

/-- Item 4a: strict unimodality (adjacent distinct, one strict local max) gives `RobUni`, any `k`. -/
theorem robUni_of_strictUnimodal {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (h : StrictUnimodal z) :
    RobUni z := by
  classical
  obtain ⟨hne, hcard⟩ := h
  let Mx := univ.filter fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i
  refine robUni_of_noAlt univ Mx (fun v hv => (hv (mem_univ v)).elim) (fun v hv => ?_)
    (fun B b c d hb hbc hcd hdk ⟨hBMx, _, hBcMx, _⟩ => ?_)
  · simp only [Mx, mem_filter, mem_univ, true_and, not_and, not_lt] at hv
    have h1 : z v ≠ z (v - 1) := by
      have := hne (v - 1)
      rw [sub_add_cancel] at this
      exact this.symm
    have h2 : z v ≠ z (v + 1) := hne v
    by_cases hlt1 : z v < z (v - 1)
    · exact Or.inl hlt1
    · right
      have hle : z (v - 1) ≤ z v := not_lt.mp hlt1
      have hlt' : z (v - 1) < z v := lt_of_le_of_ne hle h1.symm
      exact lt_of_le_of_ne (hv hlt') h2
  · have heq : B = B + (c : ZMod k) := Finset.card_le_one.mp hcard.le B hBMx (B + c) hBcMx
    have hc0 : (c : ZMod k) = 0 := by linear_combination -heq
    have hlt_k : c < k := lt_trans hcd hdk
    have hval : c = 0 := by
      have := congrArg ZMod.val hc0
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt_k, ZMod.val_zero] at this
      exact this
    omega

/-- Item 4b: on a triangle facet of type 24 a face-chord view is a weak chord arc
(drop `hfar`, `hoff`; `r` injective from `hinj`; the third vertex is off the rim because a rim
vertex in the facet plane would make `hcyc` at edge `a` a zero determinant). -/
theorem weakChordArc_of_faceChordView {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {t : Fin 9}
    (ht : t ≠ 3) (h : FaceChordView F t) : GenPlus.WeakChordArc F t := by
  obtain ⟨u, k, hne, r, a, w, ρ, hnu, hk, hA, hB, hρ, hcyc, hin, hmid, hinj, hz, hwS, -, -⟩ := h
  have : NeZero k := hne
  have hr : Function.Injective r := fun i j e =>
    hinj (show (fun i => ⟪x (r i), u⟫) i = (fun i => ⟪x (r i), u⟫) j by simp only [e])
  have hN0 : F.N t ≠ 0 := by
    obtain ⟨j, i, hj, hi⟩ := s24_off t
    intro h0
    have hneg := F.neg t i hi
    have hz := F.zero t j hj
    have hsub := F.inner_sub t i j
    rw [h0, inner_zero_left, hz, sub_zero] at hsub
    linarith
  have hNN : 0 < ⟪F.N t, F.N t⟫ := real_inner_self_pos.2 hN0
  have hdet0 : ∀ p q : Fin 7, p ∈ s0x_S24 t → q ∈ s0x_S24 t → p ≠ q →
      det3 (x p - x (r a)) (x q - x (r a)) u = 0 := by
    intro p q hp hq _
    have hp0 : ⟪F.N t, x p - x (r a)⟫ = 0 := by
      rw [F.inner_sub, F.zero t p hp, F.zero t (r a) hA, sub_self]
    have hq0 : ⟪F.N t, x q - x (r a)⟫ = 0 := by
      rw [F.inner_sub, F.zero t q hq, F.zero t (r a) hA, sub_self]
    have e := det_perp' (x p - x (r a)) (x q - x (r a)) u (F.N t) hp0 hq0
    rw [hnu, mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_right hNN.ne'
  have hcard3 : (s0x_S24 t).card = 3 := by
    fin_cases t <;> first | exact absurd rfl ht | decide
  have hne_a1 : a + 1 ≠ a := by
    have : Fact (1 < k) := ⟨by omega⟩
    intro h0
    have h1 : (1 : ZMod k) = 0 := by linear_combination h0
    have := congrArg ZMod.val h1
    rw [ZMod.val_one, ZMod.val_zero] at this
    exact absurd this one_ne_zero
  have hr_ne : r a ≠ r (a + 1) := fun h0 => hne_a1 (hr h0).symm
  have hsub2 : ({r a, r (a + 1)} : Finset (Fin 7)) ⊆ s0x_S24 t := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hcard_sdiff : (s0x_S24 t \ {r a, r (a + 1)}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub2, hcard3, Finset.card_pair hr_ne]
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hcard_sdiff
  have hq_mem : q ∈ s0x_S24 t \ {r a, r (a + 1)} := hq_eq ▸ Finset.mem_singleton_self q
  obtain ⟨hqS, hq_not⟩ := Finset.mem_sdiff.mp hq_mem
  simp only [mem_insert, mem_singleton, not_or] at hq_not
  have hq_off : ∀ j : ZMod k, q ≠ r j := by
    intro j hj
    have hj_ne_a : j ≠ a := by rintro rfl; exact hq_not.1 hj
    have hj_ne_a1 : j ≠ a + 1 := by rintro rfl; exact hq_not.2 hj
    have hpos := hcyc a j hj_ne_a hj_ne_a1
    have h0 := hdet0 (r (a + 1)) q hB hqS (fun e => hq_not.2 e.symm)
    rw [← hj, h0, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨u, k, hne, r, a, ρ, hnu, hk, hr, hA, hB, hρ, ?_, hcyc, hin, hmid, ?_⟩
  · exact ⟨q, hqS, hq_off⟩
  · rcases hz with hSU | ⟨p, q', hds⟩
    · by_cases h3 : k = 3
      · exact Or.inr (Or.inr ⟨h3, hinj⟩)
      · exact Or.inl ⟨by omega, robUni_of_strictUnimodal hSU⟩
    · exact Or.inr (Or.inl ⟨p, q', hds⟩)

/-- Item 4c: in the hole, only the quad facet `3` (0345) can carry a face-chord view that is
not already a lex or split cell. -/
theorem anyFaceChord_iff_quad {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hL : ¬ Gen.LexAny F) (hS : ¬ T24.RCell.SplitAny24 F) :
    Gen.AnyFaceChord F ↔ FaceChordView F 3 := by
  refine ⟨fun ⟨t, ht⟩ => ?_, fun h => ⟨3, h⟩⟩
  by_cases h3 : t = 3
  · subst h3; exact ht
  · rcases GenPlus.lexAny_or_splitAny24_of_weakChordArc F h3
      (weakChordArc_of_faceChordView F h3 ht) with h | h
    · exact (hL h).elim
    · exact (hS h).elim

/-! ## Item 6: `mono_at_c_of_splitRows` -/

/-- Item 6: split rows on a strict rim make `c` a strict monotone corner (any `k ≥ 3`);
with `robUni_of_monoCorners` (k = 4) this is `robUni_of_splitRows4`. -/
theorem mono_at_c_of_splitRows {k : ℕ} [NeZero k] (hk : 3 ≤ k) {X : ZMod k → ℝ³} {w : ℝ³} {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (X (i + 1) - X i) (X j - X i) w)
    {a c : ZMod k} {σ : ℝ} (hca : c ≠ a) (hca1 : c ≠ a + 1) (hS : SplitRows X w a c σ) :
    0 < (⟪X c, w⟫ - ⟪X (c - 1), w⟫) * (⟪X (c + 1), w⟫ - ⟪X c, w⟫) := by
  let z : ZMod k → ℝ := fun i => ⟪X i, w⟫
  let h : ZMod k → ℝ := fun m => ρ * det3 (X (a + 1) - X a) (X m - X a) w
  let rise : ZMod k → ℝ := fun i => Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  have : Fact (1 < k) := ⟨by omega⟩
  have ha1_ne_a : a + 1 ≠ a := by
    intro h0; have : (1 : ZMod k) = 0 := by linear_combination h0
    have := congrArg ZMod.val this; rw [ZMod.val_one, ZMod.val_zero] at this; exact one_ne_zero this
  have hrise_diff : ∀ i : ZMod k, ρ * rise i = -(h (i + 1) - h i) := by
    intro i
    have heq : Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w =
        -(det3 (X (a + 1) - X a) (X (i + 1) - X a) w -
          det3 (X (a + 1) - X a) (X i - X a) w) := by
      simp only [Split.det3, det3_expand, PiLp.sub_apply]; ring
    dsimp [rise, h]; rw [heq]; ring
  have ha0 : h a = 0 := by
    dsimp [h]; simp only [det3_expand, PiLp.sub_apply]; ring
  have ha1 : h (a + 1) = 0 := by
    dsimp [h]; simp only [det3_expand, PiLp.sub_apply]; ring
  have h_pos_off : ∀ m : ZMod k, m ≠ a → m ≠ a + 1 → 0 < h m := hcyc a
  have h_off_ne : ({c} : Finset (ZMod k)).Nonempty := ⟨c, mem_singleton_self c⟩
  let S_off : Finset (ZMod k) := univ.filter fun m => m ≠ a ∧ m ≠ a + 1
  have hS_ne : S_off.Nonempty := ⟨c, mem_filter.2 ⟨mem_univ c, hca, hca1⟩⟩
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image S_off h hS_ne
  obtain ⟨hma, hma1⟩ := (mem_filter.1 hm_mem).2
  have hm_pos : 0 < h m := h_pos_off m hma hma1
  have hm_le_all : ∀ j : ZMod k, h j ≤ h m := by
    intro j
    by_cases hj : j = a ∨ j = a + 1
    · rcases hj with rfl | rfl
      · rw [ha0]; exact hm_pos.le
      · rw [ha1]; exact hm_pos.le
    · push Not at hj
      exact hm_max j (mem_filter.2 ⟨mem_univ j, hj.1, hj.2⟩)
  have hm1_ne_a : m - 1 ≠ a := by
    intro h0; exact hma1 (by linear_combination h0)
  have hm_ne_a : m ≠ a := hma
  have hm_lt_prev : h (m - 1) < h m := by
    rcases (hm_le_all (m - 1)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hrise0 : rise (m - 1) = 0 := by
        have h1 := hrise_diff (m - 1)
        rw [sub_add_cancel, heq, sub_self, neg_zero] at h1
        exact (mul_eq_zero.mp h1).resolve_left hρ
      have hpick : ∃ j : ZMod k, (j = m - 1 ∨ j = m - 1 + 1) ∧ j ≠ c := by
        by_cases hmc : m = c
        · refine ⟨m - 1, Or.inl rfl, ?_⟩
          intro h0; have : (1 : ZMod k) = 0 := by linear_combination -h0 + hmc
          have := congrArg ZMod.val this; rw [ZMod.val_one, ZMod.val_zero] at this; exact one_ne_zero this
        · exact ⟨m, Or.inr (sub_add_cancel m 1).symm, hmc⟩
      obtain ⟨j, hj1, hjc⟩ := hpick
      have hs := hS (m - 1) j hm1_ne_a hj1 hjc
      change 0 < σ * (⟪X j - X c, w⟫ * rise (m - 1)) at hs
      rw [hrise0, mul_zero, mul_zero] at hs
      exact lt_irrefl 0 hs
  have hm_lt_next : h (m + 1) < h m := by
    rcases (hm_le_all (m + 1)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hrise0 : rise m = 0 := by
        have h1 := hrise_diff m
        rw [heq, sub_self, neg_zero] at h1
        exact (mul_eq_zero.mp h1).resolve_left hρ
      have hpick : ∃ j : ZMod k, (j = m ∨ j = m + 1) ∧ j ≠ c := by
        by_cases hmc : m = c
        · refine ⟨m + 1, Or.inr rfl, ?_⟩
          intro h0; have : (1 : ZMod k) = 0 := by linear_combination h0 - hmc
          have := congrArg ZMod.val this; rw [ZMod.val_one, ZMod.val_zero] at this; exact one_ne_zero this
        · exact ⟨m, Or.inl rfl, hmc⟩
      obtain ⟨j, hj1, hjc⟩ := hpick
      have hs := hS m j hm_ne_a hj1 hjc
      change 0 < σ * (⟪X j - X c, w⟫ * rise m) at hs
      rw [hrise0, mul_zero, mul_zero] at hs
      exact lt_irrefl 0 hs
  have hmc : m = c := by
    by_contra hne
    have hs1 := hS (m - 1) m hm1_ne_a (Or.inr (sub_add_cancel m 1).symm) hne
    have hs2 := hS m m hm_ne_a (Or.inl rfl) hne
    rw [inner_sub_left, ← mul_assoc] at hs1 hs2
    have hr1 : ρ * rise (m - 1) < 0 := by
      have := hrise_diff (m - 1); rw [sub_add_cancel] at this; linarith
    have hr2 : 0 < ρ * rise m := by
      have := hrise_diff m; linarith
    have hprod : (σ * (z m - z c) * rise (m - 1)) * (σ * (z m - z c) * rise m) > 0 :=
      mul_pos hs1 hs2
    have hneg : (σ * (z m - z c)) ^ 2 * ((ρ * rise (m - 1)) * (ρ * rise m)) > 0 := by
      have : (σ * (z m - z c)) ^ 2 * ((ρ * rise (m - 1)) * (ρ * rise m)) =
          ρ ^ 2 * ((σ * (z m - z c) * rise (m - 1)) * (σ * (z m - z c) * rise m)) := by ring
      rw [this]; exact mul_pos (sq_pos_of_ne_zero hρ) hprod
    have hle : (σ * (z m - z c)) ^ 2 * ((ρ * rise (m - 1)) * (ρ * rise m)) ≤ 0 := by
      have : (ρ * rise (m - 1)) * (ρ * rise m) < 0 := mul_neg_of_neg_of_pos hr1 hr2
      nlinarith [sq_nonneg (σ * (z m - z c))]
    linarith
  subst hmc
  have hc1_ne_c : m - 1 ≠ m := by
    intro h0; have : (1 : ZMod k) = 0 := by linear_combination -h0
    have := congrArg ZMod.val this; rw [ZMod.val_one, ZMod.val_zero] at this; exact one_ne_zero this
  have hc2_ne_c : m + 1 ≠ m := by
    intro h0; have : (1 : ZMod k) = 0 := by linear_combination h0
    have := congrArg ZMod.val this; rw [ZMod.val_one, ZMod.val_zero] at this; exact one_ne_zero this
  have hs1 := hS (m - 1) (m - 1) hm1_ne_a (Or.inl rfl) hc1_ne_c
  have hs2 := hS m (m + 1) hm_ne_a (Or.inr rfl) hc2_ne_c
  rw [inner_sub_left, ← mul_assoc] at hs1 hs2
  have hr1 : ρ * rise (m - 1) < 0 := by
    have := hrise_diff (m - 1); rw [sub_add_cancel] at this; linarith
  have hr2 : 0 < ρ * rise m := by
    have := hrise_diff m; linarith
  have hprod : (σ * (z (m - 1) - z m) * rise (m - 1)) * (σ * (z (m + 1) - z m) * rise m) > 0 :=
    mul_pos hs1 hs2
  have hcomb : ρ ^ 2 * (σ ^ 2 * ((z (m - 1) - z m) * (z (m + 1) - z m)) *
      ((ρ * rise (m - 1)) * (ρ * rise m))) > 0 := by
    have : ρ ^ 2 * (σ ^ 2 * ((z (m - 1) - z m) * (z (m + 1) - z m)) *
        ((ρ * rise (m - 1)) * (ρ * rise m))) =
        ρ ^ 4 * ((σ * (z (m - 1) - z m) * rise (m - 1)) * (σ * (z (m + 1) - z m) * rise m)) := by ring
    rw [this]; exact mul_pos (by positivity) hprod
  have hσ0 : σ ≠ 0 := by
    rintro rfl; simp at hs2
  have h_opp : (z (m - 1) - z m) * (z (m + 1) - z m) < 0 := by
    by_contra hle; push Not at hle
    have hmul : (ρ * rise (m - 1)) * (ρ * rise m) < 0 := mul_neg_of_neg_of_pos hr1 hr2
    have h1 : 0 ≤ σ ^ 2 * ((z (m - 1) - z m) * (z (m + 1) - z m)) :=
      mul_nonneg (sq_nonneg _) hle
    have h2 : σ ^ 2 * ((z (m - 1) - z m) * (z (m + 1) - z m)) * (ρ * rise (m - 1) * (ρ * rise m)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1 hmul.le
    have h3 : ρ ^ 2 * (σ ^ 2 * ((z (m - 1) - z m) * (z (m + 1) - z m)) *
        (ρ * rise (m - 1) * (ρ * rise m))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h2
    linarith
  have heq : (z m - z (m - 1)) * (z (m + 1) - z m) = -((z (m - 1) - z m) * (z (m + 1) - z m)) := by ring
  dsimp [z] at heq h_opp
  linarith

/-! ## Item 7: `lexAny_of_splitAny_four` -/

/-- Item 7: a split cell on a 4-rim is a lex cell (Hole24 needs `SplitAny` only for k = 3 and k ≥ 5). -/
theorem lexAny_of_splitAny_four {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} {pat : Fin m → Bool} {u v : ℝ³} (hc : Function.Injective c)
    (hcyc : S0xCycOK S c pat) (hfac : S0xFacOK F pat u v)
    (a cc : ZMod 4) (σ : ℝ) (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hrows : SplitRows (fun i => x (c i)) u a cc σ) : Gen.LexAny F := by
  classical
  let _ := hca; let _ := hca1
  obtain ⟨D⟩ := s0x_silL F hcyc hfac
  choose μ hμ0 hd using fun i => h21b_exists_mu (by decide) hx hc D i
  have hsign := h21b_sign_agree (by decide) hx hc D μ hμ0 hd
  let ρ : ℝ := if 0 < μ 0 then 1 else -1
  have hρ : ρ ≠ 0 := by dsimp [ρ]; split_ifs <;> norm_num
  have hρμ : ∀ i : ZMod 4, 0 < ρ * μ i := by
    intro i; dsimp [ρ]
    rcases hsign with hpos | hneg <;> split_ifs with h0
    · exact mul_pos one_pos (hpos i)
    · exact absurd (hpos 0) h0
    · exact absurd h0 (not_lt.mpr (hneg 0).le)
    · nlinarith [hneg i]
  have hev_fac : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t : Fin m,
      (pat t = true → 0 < ⟪F.N t, u + ε • v⟫) ∧
      (pat t = false → ⟪F.N t, u + ε • v⟫ < 0) := by
    refine eventually_all.2 fun t => eventually_and.2 ⟨?_, ?_⟩
    · by_cases ht : pat t = true
      · filter_upwards [eventually_pos_affine ((hfac t).1 ht)] with ε hε _
        rw [inner_add_right, real_inner_smul_right]; exact hε
      · exact Filter.Eventually.of_forall fun _ h => absurd h ht
    · by_cases ht : pat t = false
      · filter_upwards [eventually_pos_affine ((hfac t).2 ht)] with ε hε _
        rw [inner_add_right, real_inner_smul_right]; linarith
      · exact Filter.Eventually.of_forall fun _ h => absurd h ht
  have hev_cyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) (u + ε • v) := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ev_imp fun hji => ev_imp fun hj1 => ?_
    have h0 : c j ≠ c i := fun h => hji (hc h)
    have h1 : c j ≠ c (i + 1) := fun h => hj1 (hc h)
    have Q := h21b_Q_pos D i (c j) h0 h1
    have hQ' : h21b_LP
        (ρ * μ i * (D.fA i (x (c j)) * ⟪D.B i, u⟫ - D.fB i (x (c j)) * ⟪D.A i, u⟫))
        (ρ * μ i * (D.fA i (x (c j)) * ⟪D.B i, v⟫ - D.fB i (x (c j)) * ⟪D.A i, v⟫)) := by
      rcases Q with h | ⟨h, h'⟩
      · exact Or.inl (mul_pos (hρμ i) h)
      · exact Or.inr ⟨by rw [h, mul_zero], mul_pos (hρμ i) h'⟩
    filter_upwards [eventually_pos_affine hQ'] with ε hε
    rw [det3_add_smul, h21b_det_eq D i (μ i) (hd i) (c j) u,
      h21b_det_eq D i (μ i) (hd i) (c j) v]
    linarith
  have hev_rows : ∀ᶠ ε in 𝓝[>] (0 : ℝ), SplitRows (fun i => x (c i)) (u + ε • v) a cc σ := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ev_imp fun hi => ev_imp fun hj =>
      ev_imp fun hjc => ?_
    have hs := hrows i j hi hj hjc
    have heq : ∀ ε : ℝ, σ * (⟪x (c j) - x (c cc), u + ε • v⟫ *
        Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (u + ε • v)) =
        σ * (⟪x (c j) - x (c cc), u⟫ * Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) u) +
        ε * (σ * (⟪x (c j) - x (c cc), u⟫ * Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) v +
          ⟪x (c j) - x (c cc), v⟫ * Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) u)) +
        ε ^ 2 * (σ * (⟪x (c j) - x (c cc), v⟫ *
          Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) v)) := by
      intro ε
      simp only [Split.det3, inner_add_right, real_inner_smul_right,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    set A := σ * (⟪x (c j) - x (c cc), u⟫ * Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) u)
    set B := σ * (⟪x (c j) - x (c cc), u⟫ * Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) v +
      ⟪x (c j) - x (c cc), v⟫ * Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) u)
    set C := σ * (⟪x (c j) - x (c cc), v⟫ * Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) v)
    have ht1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A / 2 + ε * B :=
      eventually_pos_affine (Or.inl (by linarith))
    have ht2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A / 2 + ε * (ε * C) := by
      have hc0 : Continuous (fun ε : ℝ => A / 2 + ε * (ε * C)) := by continuity
      have h0 : 0 < A / 2 + (0 : ℝ) * (0 * C) := by simpa using half_pos hs
      exact hc0.continuousAt.eventually (lt_mem_nhds h0) |>.filter_mono nhdsWithin_le_nhds
    filter_upwards [ht1, ht2] with ε h1 h2
    rw [heq ε, show ε ^ 2 * C = ε * (ε * C) by ring]; linarith
  obtain ⟨ε, hfac', hcyc', hrows'⟩ :=
    (hev_fac.and (hev_cyc.and hev_rows)).exists
  have hrob : RobUni (fun i => ⟪x (c i), u + ε • v⟫) :=
    GenPlus.robUni_of_splitRows4 hρ hcyc' hrows'
  let U : Finset (Fin m) := univ.filter fun t => pat t = true
  let Dn : Finset (Fin m) := univ.filter fun t => pat t = false
  refine ⟨4, inferInstance, c, U, Dn, u + ε • v, 0, 0, le_rfl, hc, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨ea, eb, hea, heb, h0a, h0b, h1a, h1b, hs⟩ := hcyc i
    exact ⟨ea, mem_filter.2 ⟨mem_univ _, hea⟩, eb, mem_filter.2 ⟨mem_univ _, heb⟩,
      h0a, h0b, h1a, h1b, hs⟩
  · intro t ht
    exact Or.inl ((hfac' t).1 (mem_filter.1 ht).2)
  · intro t ht
    exact Or.inl (by linarith [(hfac' t).2 (mem_filter.1 ht).2])
  · intro B b c' d hb hbc hcd hdk
    by_contra hnot
    have hle : ∀ p q : ℝ, ¬ LexLt3 (p, (0 : ℝ), (0 : ℝ)) (q, 0, 0) → q ≤ p := fun p q hn =>
      not_lt.mp fun hlt => hn (Or.inl (sub_pos.mpr hlt))
    push Not at hnot
    simp only [inner_zero_right] at hnot
    exact hrob B b c' d hb hbc hcd hdk
      ⟨hle _ _ hnot.1, hle _ _ hnot.2.1, hle _ _ hnot.2.2.1, hle _ _ hnot.2.2.2⟩

/-! ## Item 8: `SplitLexAny` and `splitLexAny_of_splitAny` -/

/-- Item 8: the stronger split leaf (tie view; `split_lex2_rupert`, proved, used by the type-16 SAT). -/
def SplitLexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin n) (pat : Fin m → Bool) (u d w : ℝ³)
    (a cc : ZMod k) (σ : ℝ),
    3 ≤ k ∧ Function.Injective c ∧ S0xCycOK S c pat ∧
    (∀ t, (pat t = true → H21.LP3 ⟪F.N t, u⟫ ⟪F.N t, d⟫ ⟪F.N t, w⟫) ∧
      (pat t = false → H21.LP3 (-⟪F.N t, u⟫) (-⟪F.N t, d⟫) (-⟪F.N t, w⟫))) ∧
    cc ≠ a ∧ cc ≠ a + 1 ∧ LexRows (fun i => x (c i)) u d a cc σ

theorem splitLexAny_isRupert {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x)
    (hsep : ∀ i j : Fin n, j ≠ i → ∃ t : Fin m, i ∈ S t ∧ j ∉ S t)
    (h : SplitLexAny F) : IsRupert (univ.image x) := by
  rcases h with ⟨k, hne, c, pat, u, d, w, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩
  exact split_lex2_rupert F hx (noBetween_of_fac F hsep) hc hk hcyc hfac a cc σ hca hca1 hrows

theorem splitLexAny_of_splitAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (h : Gen.SplitAny F) : SplitLexAny F := by
  rcases h with ⟨k, hne, c, pat, u, v, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩
  refine ⟨k, hne, c, pat, u, v, 0, a, cc, σ, hk, hc, hcyc, ?_, hca, hca1, ?_⟩
  · intro t
    constructor
    · intro ht
      rcases (hfac t).1 ht with h0 | ⟨h0, h1⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h0, Or.inl h1⟩
    · intro ht
      rcases (hfac t).2 ht with h0 | ⟨h0, h1⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h0, Or.inl h1⟩
  · intro i j hi hj hjc
    have hs := hrows i j hi hj hjc
    set A := ⟪x (c j) - x (c cc), u⟫
    set Δ := Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) u
    have hA0 : A ≠ 0 := by
      intro h0; rw [h0, zero_mul, mul_zero] at hs; exact lt_irrefl 0 hs
    let s : ℝ := if 0 < A then 1 else -1
    have hsA : 0 < s * A := by
      dsimp [s]; split_ifs with h0
      · simpa using h0
      · have : A < 0 := lt_of_le_of_ne (not_lt.mp h0) hA0
        linarith
    have hsΔ : 0 < σ * s * Δ := by
      have hprod : 0 < (s * A) * (σ * s * Δ) := by
        have heq : (s * A) * (σ * s * Δ) = s ^ 2 * (σ * (A * Δ)) := by ring
        rw [heq]
        have hs2 : 0 < s ^ 2 := by dsimp [s]; split_ifs <;> norm_num
        exact mul_pos hs2 hs
      exact pos_of_mul_pos_right hprod hsA.le
    exact ⟨s, Or.inl hsA, hsΔ⟩

/-! ## Item 9: `exists_view_of_zeta` and `robUniLex_metric_free` -/

/-- Item 9: realisability of any covector on the corner frame (no OB1, no sign);
`cone24_of_zeta` = this + `pos_of_gram_solve`. -/
theorem exists_view_of_zeta {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) (ζ0 ζ1 ζ2 : ℝ) :
    ∃ u : ℝ³, ⟪x 0 - x 1, u⟫ = ζ0 ∧ ⟪x 2 - x 1, u⟫ = ζ1 ∧ ⟪x 6 - x 1, u⟫ = ζ2 := by
  have hD := T24.HC.det3_e026_ne F
  set a := x 0 - x 1
  set b := x 2 - x 1
  set c := x 6 - x 1
  set D := det3 a b c
  let u : ℝ³ := D⁻¹ • (ζ0 • cross b c + ζ1 • cross c a + ζ2 • cross a b)
  have iu : ∀ d : ℝ³, ⟪d, u⟫ = D⁻¹ * (ζ0 * det3 b c d + ζ1 * det3 c a d + ζ2 * det3 a b d) := by
    intro d
    dsimp [u]
    simp only [real_inner_smul_right, inner_add_right, T24.HC.inner_cross_right]
  have d1 : det3 b c a = D := by simp only [D, det3_expand]; ring
  have d2 : det3 c a b = D := by simp only [D, det3_expand]; ring
  have z1 : det3 c a a = 0 := by simp only [det3_expand]; ring
  have z2 : det3 a b a = 0 := by simp only [det3_expand]; ring
  have z3 : det3 b c b = 0 := by simp only [det3_expand]; ring
  have z4 : det3 a b b = 0 := by simp only [det3_expand]; ring
  have z5 : det3 b c c = 0 := by simp only [det3_expand]; ring
  have z6 : det3 c a c = 0 := by simp only [det3_expand]; ring
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [iu, d1, z1, z2]; field_simp [hD]; ring
  · rw [iu, z3, d2, z4]; field_simp [hD]; ring
  · rw [iu, z5, z6]; change D⁻¹ * (ζ0 * 0 + ζ1 * 0 + ζ2 * D) = ζ2; field_simp [hD]; ring

/-- Item 9: a lex view built from three frame covectors; the rim order is metric free. -/
theorem robUniLex_metric_free {x : Fin 7 → ℝ³} (F : S0xFac 9 T24.SAT.s0x_S24 x) {k : ℕ}
    (c : ZMod k → Fin 7) (b d1 d2 : ℝ³) (ζ ξ η : Fin 3 → ℝ)
    (hb : ⟪x 0 - x 1, b⟫ = ζ 0 ∧ ⟪x 2 - x 1, b⟫ = ζ 1 ∧ ⟪x 6 - x 1, b⟫ = ζ 2)
    (h1 : ⟪x 0 - x 1, d1⟫ = ξ 0 ∧ ⟪x 2 - x 1, d1⟫ = ξ 1 ∧ ⟪x 6 - x 1, d1⟫ = ξ 2)
    (h2 : ⟪x 0 - x 1, d2⟫ = η 0 ∧ ⟪x 2 - x 1, d2⟫ = η 1 ∧ ⟪x 6 - x 1, d2⟫ = η 2) :
    RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫)) ↔
      RobUniLex (fun i =>
        (oblX0 x (c i) * ζ 0 + oblX2 x (c i) * ζ 1 + oblX6 x (c i) * ζ 2,
         oblX0 x (c i) * ξ 0 + oblX2 x (c i) * ξ 1 + oblX6 x (c i) * ξ 2,
         oblX0 x (c i) * η 0 + oblX2 x (c i) * η 1 + oblX6 x (c i) * η 2)) := by
  have hdiff : ∀ i j : ZMod k,
      LexLt3 (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫)
        (⟪x (c j), b⟫, ⟪x (c j), d1⟫, ⟪x (c j), d2⟫) ↔
      LexLt3
        (oblX0 x (c i) * ζ 0 + oblX2 x (c i) * ζ 1 + oblX6 x (c i) * ζ 2,
         oblX0 x (c i) * ξ 0 + oblX2 x (c i) * ξ 1 + oblX6 x (c i) * ξ 2,
         oblX0 x (c i) * η 0 + oblX2 x (c i) * η 1 + oblX6 x (c i) * η 2)
        (oblX0 x (c j) * ζ 0 + oblX2 x (c j) * ζ 1 + oblX6 x (c j) * ζ 2,
         oblX0 x (c j) * ξ 0 + oblX2 x (c j) * ξ 1 + oblX6 x (c j) * ξ 2,
         oblX0 x (c j) * η 0 + oblX2 x (c j) * η 1 + oblX6 x (c j) * η 2) := by
    intro i j
    have eb := T24.HC.depth24_metric_free F b (ζ 0) (ζ 1) (ζ 2) hb.1 hb.2.1 hb.2.2
    have e1 := T24.HC.depth24_metric_free F d1 (ξ 0) (ξ 1) (ξ 2) h1.1 h1.2.1 h1.2.2
    have e2 := T24.HC.depth24_metric_free F d2 (η 0) (η 1) (η 2) h2.1 h2.2.1 h2.2.2
    have sb : ⟪x (c j), b⟫ - ⟪x (c i), b⟫ =
        (oblX0 x (c j) * ζ 0 + oblX2 x (c j) * ζ 1 + oblX6 x (c j) * ζ 2) -
        (oblX0 x (c i) * ζ 0 + oblX2 x (c i) * ζ 1 + oblX6 x (c i) * ζ 2) := by
      rw [← eb (c j), ← eb (c i)]; simp only [inner_sub_left]; ring
    have s1 : ⟪x (c j), d1⟫ - ⟪x (c i), d1⟫ =
        (oblX0 x (c j) * ξ 0 + oblX2 x (c j) * ξ 1 + oblX6 x (c j) * ξ 2) -
        (oblX0 x (c i) * ξ 0 + oblX2 x (c i) * ξ 1 + oblX6 x (c i) * ξ 2) := by
      rw [← e1 (c j), ← e1 (c i)]; simp only [inner_sub_left]; ring
    have s2 : ⟪x (c j), d2⟫ - ⟪x (c i), d2⟫ =
        (oblX0 x (c j) * η 0 + oblX2 x (c j) * η 1 + oblX6 x (c j) * η 2) -
        (oblX0 x (c i) * η 0 + oblX2 x (c i) * η 1 + oblX6 x (c i) * η 2) := by
      rw [← e2 (c j), ← e2 (c i)]; simp only [inner_sub_left]; ring
    simp only [LexLt3, sb, s1, s2]
  simp only [RobUniLex, hdiff]

/-! ## Item 10: `cone_iff_back` -/

/-- Item 10: the hidden-cap cone is a facet-sign cell, generically: a simple vertex `v` with
facets `t₁ ∋ v,b,c`, `t₂ ∋ v,a,c`, `t₃ ∋ v,a,b` and independent edges. -/
theorem cone_iff_back {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) {v a b c : Fin n} {t₁ t₂ t₃ : Fin m}
    (h₁ : v ∈ S t₁ ∧ b ∈ S t₁ ∧ c ∈ S t₁ ∧ a ∉ S t₁) (h₂ : v ∈ S t₂ ∧ a ∈ S t₂ ∧ c ∈ S t₂ ∧ b ∉ S t₂)
    (h₃ : v ∈ S t₃ ∧ a ∈ S t₃ ∧ b ∈ S t₃ ∧ c ∉ S t₃)
    (hli : LinearIndependent ℝ ![x a - x v, x b - x v, x c - x v]) (u : ℝ³) :
    (⟪F.N t₁, u⟫ < 0 ∧ ⟪F.N t₂, u⟫ < 0 ∧ ⟪F.N t₃, u⟫ < 0) ↔
      ∃ ca cb cc : ℝ, 0 < ca ∧ 0 < cb ∧ 0 < cc ∧
        u = ca • (x a - x v) + cb • (x b - x v) + cc • (x c - x v) := by
  have b1 : ⟪F.N t₁, x b - x v⟫ = 0 := by rw [F.inner_sub, F.zero t₁ b h₁.2.1, F.zero t₁ v h₁.1, sub_self]
  have c1 : ⟪F.N t₁, x c - x v⟫ = 0 := by rw [F.inner_sub, F.zero t₁ c h₁.2.2.1, F.zero t₁ v h₁.1, sub_self]
  have a1 : ⟪F.N t₁, x a - x v⟫ < 0 := by
    rw [F.inner_sub, F.zero t₁ v h₁.1, sub_zero]; exact F.neg t₁ a h₁.2.2.2
  have a2 : ⟪F.N t₂, x a - x v⟫ = 0 := by rw [F.inner_sub, F.zero t₂ a h₂.2.1, F.zero t₂ v h₂.1, sub_self]
  have c2 : ⟪F.N t₂, x c - x v⟫ = 0 := by rw [F.inner_sub, F.zero t₂ c h₂.2.2.1, F.zero t₂ v h₂.1, sub_self]
  have b2 : ⟪F.N t₂, x b - x v⟫ < 0 := by
    rw [F.inner_sub, F.zero t₂ v h₂.1, sub_zero]; exact F.neg t₂ b h₂.2.2.2
  have a3 : ⟪F.N t₃, x a - x v⟫ = 0 := by rw [F.inner_sub, F.zero t₃ a h₃.2.1, F.zero t₃ v h₃.1, sub_self]
  have b3 : ⟪F.N t₃, x b - x v⟫ = 0 := by rw [F.inner_sub, F.zero t₃ b h₃.2.2.1, F.zero t₃ v h₃.1, sub_self]
  have c3 : ⟪F.N t₃, x c - x v⟫ < 0 := by
    rw [F.inner_sub, F.zero t₃ v h₃.1, sub_zero]; exact F.neg t₃ c h₃.2.2.2
  constructor
  · rintro ⟨hu1, hu2, hu3⟩
    obtain ⟨ca, cb, cc, hu⟩ := span_of_indep3 hli u
    have e1 : ⟪F.N t₁, u⟫ = ca * ⟪F.N t₁, x a - x v⟫ := by
      rw [hu]; simp only [inner_add_right, real_inner_smul_right, b1, c1]; ring
    have e2 : ⟪F.N t₂, u⟫ = cb * ⟪F.N t₂, x b - x v⟫ := by
      rw [hu]; simp only [inner_add_right, real_inner_smul_right, a2, c2]; ring
    have e3 : ⟪F.N t₃, u⟫ = cc * ⟪F.N t₃, x c - x v⟫ := by
      rw [hu]; simp only [inner_add_right, real_inner_smul_right, a3, b3]; ring
    refine ⟨ca, cb, cc, ?_, ?_, ?_, hu⟩
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  · rintro ⟨ca, cb, cc, hca, hcb, hcc, rfl⟩
    simp only [inner_add_right, real_inner_smul_right, b1, c1, a2, c2, a3, b3]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end Minimality.GenRev
