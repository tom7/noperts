module

public import Minimality.Type24WallsAll2

/-!
# Type24WallsTwin: `π_24` image of `Cell24` and `CellWall`, and one-sided `CellCoverEmptyAll2S` (Task GE)

* **GE1:** `symCell24 c`, `unsymCellWall F c W`, `cellAt_sym24`, `cellCert_sym_iff`,
  `wallE_unsymCellWall`, and `wallE_selfDual_iff` (invariance of `WallE` under rim reversal
  and positive-orientation scalar change on self-dual cells).
* **GE2:** `cells28` is not closed under `π_24` (4 cells are self-dual: `cellB0`, `cell0236`,
  `cellP`, `cell046125`; the other 11 map outside `cells28`). Closing the 594 walls of
  `AllWallE2` under `π_24` adds `429` mirror walls (for the `165` self-dual walls, the `π_24`
  image is already in the `594`-wall list), giving a one-sided conjunction `AllWallE2S` of
  `1023 < 1188 = 2 × 594` walls and `CellCoverEmptyAll2S L ↔ CellCoverEmptyAll2 L`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## GE1: `π_24` image of `Cell24`, `CellWall`, `CellCert`, and `WallE` -/

private lemma sig24_invol (t : Fin 9) : Sym.sig24 (Sym.sig24 t) = t := by
  fin_cases t <;> rfl

private lemma mem_image_sig24_iff (U : Finset (Fin 9)) (t : Fin 9) :
    t ∈ U.image Sym.sig24 ↔ Sym.sig24 t ∈ U := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 h
    simpa [sig24_invol] using ha
  · intro h
    exact mem_image.2 ⟨Sym.sig24 t, h, sig24_invol t⟩

/-- The `π_24` image of a `Cell24`: rim relabelled by `Sym.pi24 = (2 6)(4 5)` and up-set
relabelled by `Sym.sig24 = (0 1)(2 4)(6 8)`. -/
def symCell24 (c : Cell24) : Cell24 where
  k := c.k
  hk := c.hk
  r := fun i => Sym.pi24 (c.r i)
  U := c.U.image Sym.sig24
  inj := Sym.pi24.injective.comp c.inj
  cyc := by
    intro i
    obtain ⟨a, haU, b, hbDn, ha0, hb0, ha1, hb1, huniv⟩ := c.cyc i
    have hbU : b ∉ c.U := (mem_sdiff.1 hbDn).2
    refine ⟨Sym.sig24 a, (mem_image_sig24_iff c.U _).2 (by simpa [sig24_invol] using haU),
      Sym.sig24 b, mem_sdiff.2 ⟨mem_univ _, fun h => hbU (by simpa [sig24_invol] using (mem_image_sig24_iff c.U _).1 h)⟩,
      (Sym.s24_sym a (c.r i)).1 ha0, (Sym.s24_sym b (c.r i)).1 hb0,
      (Sym.s24_sym a (c.r (i + 1))).1 ha1, (Sym.s24_sym b (c.r (i + 1))).1 hb1, ?_⟩
    intro q hq0 hq1
    obtain ⟨q', rfl⟩ := Sym.pi24.surjective q
    have hq0' : q' ≠ c.r i := fun h => hq0 (congrArg Sym.pi24 h)
    have hq1' : q' ≠ c.r (i + 1) := fun h => hq1 (congrArg Sym.pi24 h)
    rcases huniv q' hq0' hq1' with h | h
    · exact Or.inl (fun h' => h ((Sym.s24_sym a q').2 h'))
    · exact Or.inr (fun h' => h ((Sym.s24_sym b q').2 h'))

/-- Open-cell membership transfers between `(Sym.sym24 F, c)` and `(F, symCell24 c)`. -/
theorem cellAt_sym24 (F : S0xFac 9 s0x_S24 x) (c : Cell24) (w : ℝ³) :
    CellAt (Sym.sym24 F) c.U (univ \ c.U) w ↔
      CellAt F (symCell24 c).U (univ \ (symCell24 c).U) w := by
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simpa [Sym.sym24_N, sig24_invol] using h1 (Sym.sig24 t) ((mem_image_sig24_iff c.U t).1 ht)
    · have ht' : Sym.sig24 t ∉ c.U := fun h => (mem_sdiff.1 ht).2 ((mem_image_sig24_iff c.U t).2 h)
      simpa [Sym.sym24_N, sig24_invol] using h2 (Sym.sig24 t) (mem_sdiff.2 ⟨mem_univ _, ht'⟩)
  · intro ⟨h1, h2⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : Sym.sig24 t ∈ (symCell24 c).U :=
        (mem_image_sig24_iff c.U (Sym.sig24 t)).2 (by simpa [sig24_invol] using ht)
      simpa [Sym.sym24_N, sig24_invol] using h1 (Sym.sig24 t) ht'
    · have ht' : Sym.sig24 t ∉ (symCell24 c).U := by
        dsimp only [symCell24]
        rw [mem_image_sig24_iff, sig24_invol]
        exact (mem_sdiff.1 ht).2
      simpa [Sym.sym24_N, sig24_invol] using h2 (Sym.sig24 t) (mem_sdiff.2 ⟨mem_univ _, ht'⟩)

/-- `CellCert` on the twin `(x ∘ π_24, sym24 F)` at `c` (for the `RobUni` and `ApexCert`
branches, and `CellAt` equivalence). -/
theorem cellCert_sym_rob_iff (F : S0xFac 9 s0x_S24 x) (c : Cell24) (w : ℝ³) :
    (CellAt (Sym.sym24 F) c.U (univ \ c.U) w ∧ RobUni (fun i => ⟪(x ∘ Sym.pi24) (c.r i), w⟫)) ↔
      (CellAt F (symCell24 c).U (univ \ (symCell24 c).U) w ∧ RobUni (fun i => ⟪x ((symCell24 c).r i), w⟫)) := by
  simp only [cellAt_sym24]; rfl

theorem cellCert_sym_apex_iff (F : S0xFac 9 s0x_S24 x) (c : Cell24) (w : ℝ³) :
    (CellAt (Sym.sym24 F) c.U (univ \ c.U) w ∧ ApexCert (fun i => (x ∘ Sym.pi24) (c.r i)) w) ↔
      (CellAt F (symCell24 c).U (univ \ (symCell24 c).U) w ∧ ApexCert (fun i => x ((symCell24 c).r i)) w) := by
  simp only [cellAt_sym24]; rfl

/-- Pull back a `CellWall (Sym.sym24 F) c` to a `CellWall F (symCell24 c)`. -/
noncomputable def unsymCellWall (F : S0xFac 9 s0x_S24 x) (c : Cell24)
    (W : CellWall (Sym.sym24 F) c) : CellWall F (symCell24 c) where
  n := W.n
  E0 := W.E0
  E1 := W.E1
  v := W.v
  fac := W.fac
  face := by
    intro l hl0 hl1 hfac
    obtain ⟨h1, h2⟩ := W.face l hl0 hl1 hfac
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simpa [Sym.sym24_N, sig24_invol] using h1 (Sym.sig24 t) ((mem_image_sig24_iff c.U t).1 ht)
    · simpa [Sym.sym24_N, sig24_invol] using h2 (Sym.sig24 t) (fun h => ht ((mem_image_sig24_iff c.U t).2 h))

/-- `WallE` of `unsymCellWall F c W` on `(x, F)` is definitionally `WallE` of `W` on the twin. -/
theorem wallE_unsymCellWall (F : S0xFac 9 s0x_S24 x) (c : Cell24)
    (W : CellWall (Sym.sym24 F) c) (s : ℝ) :
    WallE F (symCell24 c) (unsymCellWall F c W) s ↔ WallE (Sym.sym24 F) c W s :=
  Iff.rfl

/-! ## Self-dual cell `WallE` equivalence under rim reversal -/

private lemma zmod_neg_sub_one_val {k : ℕ} [NeZero k] (u : ZMod k) :
    (-1 - u).val = k - 1 - u.val := by
  rcases eq_or_ne k 1 with rfl | hk1
  · have : u = 0 := Subsingleton.elim u 0
    subst this; simp
  · have hpos : 0 < k := NeZero.pos k
    have h1lt : 1 < k := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hpos.ne', hk1⟩
    have : Fact (1 < k) := ⟨h1lt⟩
    have hk := ZMod.val_lt u
    have e : -1 - u = -(u + 1) := by ring
    rw [e]
    by_cases hu : u.val + 1 = k
    · have hzero : u + 1 = 0 := by
        rw [← ZMod.val_eq_zero, ZMod.val_add, ZMod.val_one, hu, Nat.mod_self]
      rw [hzero, neg_zero, ZMod.val_zero]; omega
    · have hlt : u.val + 1 < k := by omega
      have hval : (u + 1).val = u.val + 1 := by
        rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hlt]
      have hne : u + 1 ≠ 0 := by
        intro h0
        have := congrArg ZMod.val h0
        rw [hval, ZMod.val_zero] at this
        omega
      rw [ZMod.neg_val]
      simp only [hne, ↓reduceIte, hval]
      omega

private lemma rForm_rev {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (i0 : ZMod k) (L : ℕ) :
    ∃ (i0' : ZMod k) (L' : ℕ) (e : ZMod k ≃ ZMod k),
      ∀ j, rForm (fun i => X (-i)) i0 L j = rForm X i0' L' (e j) := by
  by_cases hL0 : L = 0
  · refine ⟨-i0, k, ⟨fun j => -j - 1, fun j => -j - 1, by intro j; ring, by intro j; ring⟩, ?_⟩
    intro j
    have hval : ((-j - 1) - (-i0)).val < k := ZMod.val_lt _
    simp only [rForm, hL0, Nat.not_lt_zero, ↓reduceIte, hval, Equiv.coe_fn_mk]
    have e1 : -(j + 1) = -j - 1 := by ring
    have e2 : (-j - 1) + 1 = -j := by ring
    rw [e1, e2]
  · by_cases hLk : L < k
    · refine ⟨-i0, k - L,
        ⟨fun j => -j - 1, fun j => -j - 1, by intro j; ring, by intro j; ring⟩, ?_⟩
      intro j
      simp only [rForm, Equiv.coe_fn_mk]
      have e1 : -(j + 1) = -j - 1 := by ring
      have e2 : (-j - 1) + 1 = -j := by ring
      have hsub : (-j - 1) - (-i0) = -1 - (j - i0) := by ring
      have hval : ((-j - 1) - (-i0)).val = k - 1 - (j - i0).val := by
        rw [hsub, zmod_neg_sub_one_val]
      have hlt := ZMod.val_lt (j - i0)
      rw [hval]
      by_cases h : (j - i0).val < L
      · have h' : ¬ (k - 1 - (j - i0).val < k - L) := by omega
        simp only [h, ↓reduceIte, h', e1, e2]
      · have h' : k - 1 - (j - i0).val < k - L := by omega
        simp only [h, ↓reduceIte, h', e1, e2]
    · refine ⟨-i0, 0, ⟨fun j => -j - 1, fun j => -j - 1, by intro j; ring, by intro j; ring⟩, ?_⟩
      intro j
      have h1 : (j - i0).val < L := lt_of_lt_of_le (ZMod.val_lt _) (not_lt.1 hLk)
      simp only [rForm, h1, ↓reduceIte, Nat.not_lt_zero, Equiv.coe_fn_mk]
      have e1 : -(j + 1) = -j - 1 := by ring
      have e2 : (-j - 1) + 1 = -j := by ring
      rw [e1, e2]

private lemma dForm_rev {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (a m : ZMod k) (σ : ℝ)
    (j : {j : ZMod k // j ≠ m}) :
    dForm (fun i => X (-i)) a m σ j =
      dForm X (-a - 1) (-m) (-σ) ⟨-j.1, fun h => j.2 (by linear_combination -h)⟩ := by
  simp only [dForm]
  have h1 : -j.1 - (-a - 1) - 1 = -1 - (j.1 - a - 1) := by ring
  have h2 : -m - (-a - 1) - 1 = -1 - (m - a - 1) := by ring
  rw [h1, h2, zmod_neg_sub_one_val, zmod_neg_sub_one_val]
  have hne : (j.1 - a - 1).val ≠ (m - a - 1).val := by
    intro h
    apply j.2
    have := ZMod.val_injective k h
    linear_combination this
  have hlt1 := ZMod.val_lt (j.1 - a - 1)
  have hlt2 := ZMod.val_lt (m - a - 1)
  by_cases h : (j.1 - a - 1).val < (m - a - 1).val
  · have h' : ¬ (k - 1 - (j.1 - a - 1).val < k - 1 - (m - a - 1).val) := by omega
    simp only [h, ↓reduceIte, h']
    module
  · have h' : k - 1 - (j.1 - a - 1).val < k - 1 - (m - a - 1).val := by omega
    simp only [h, ↓reduceIte, h']
    module

private lemma hForm_rev {k : ℕ} (X : ZMod k → ℝ³) (s : ℝ) (a m : ZMod k)
    (j : {j : ZMod k // j ≠ a ∧ j ≠ a + 1 ∧ j ≠ m}) :
    hForm (fun i => X (-i)) s a m j =
      hForm X (-s) (-a - 1) (-m)
        ⟨-j.1, fun h => j.2.2.1 (by linear_combination -h),
               fun h => j.2.1 (by linear_combination -h),
               fun h => j.2.2.2 (by linear_combination -h)⟩ := by
  have e1 : -a - 1 + 1 = -a := by ring
  have e0 : -(a + 1) = -a - 1 := by ring
  simp only [hForm, e1, e0]
  ext idx
  fin_cases idx <;> simp [Split.cross_0, Split.cross_1, Split.cross_2] <;> ring

private lemma wallE_rev_imp {x1 x2 : Fin 7 → ℝ³}
    (F1 : S0xFac 9 s0x_S24 x1) (F2 : S0xFac 9 s0x_S24 x2) (c : Cell24)
    (hcell : ∀ w : ℝ³, CellAt F1 c.U (univ \ c.U) w → CellAt F2 c.U (univ \ c.U) w)
    (hr : ∀ i : ZMod c.k, x1 (c.r i) = x2 (c.r (-i)))
    (W1 : CellWall F1 c) (W2 : CellWall F2 c)
    (hseg : (W1.E0 = W2.E0 ∧ W1.E1 = W2.E1) ∨ (W1.E0 = W2.E1 ∧ W1.E1 = W2.E0))
    (hfac : ∀ w : ℝ³, (∀ i, 0 < ⟪W1.fac i, w⟫) → (∀ i, 0 < ⟪W2.fac i, w⟫))
    {s1 s2 : ℝ}
    (hs1 : ∀ w : ℝ³, CellAt F1 c.U (univ \ c.U) w → ∀ ρ : ℝ, (ρ = 1 ∨ ρ = -1) →
      (∀ i j : ZMod c.k, j ≠ i → j ≠ i + 1 →
        0 < ρ * Split.det3 (x1 (c.r (i + 1)) - x1 (c.r i)) (x1 (c.r j) - x1 (c.r i)) w) → 0 < ρ * s1)
    (hs2 : ∀ w : ℝ³, CellAt F2 c.U (univ \ c.U) w → ∀ ρ : ℝ, (ρ = 1 ∨ ρ = -1) →
      (∀ i j : ZMod c.k, j ≠ i → j ≠ i + 1 →
        0 < ρ * Split.det3 (x2 (c.r (i + 1)) - x2 (c.r i)) (x2 (c.r j) - x2 (c.r i)) w) → 0 < ρ * s2)
    (hW2 : WallE F2 c W2 s2) :
    WallE F1 c W1 s1 := by
  have hr' : (fun i => x1 (c.r i)) = fun i => x2 (c.r (-i)) := funext hr
  refine ⟨fun i0 L hseg1 => ?_, fun a m σ hma hma1 hσ hseg1 => ?_⟩
  · rw [hr'] at hseg1
    obtain ⟨i0', L', e, he⟩ := rForm_rev (fun i => x2 (c.r i)) i0 L
    rw [segLet_iff] at hseg1
    obtain ⟨l, hl0, hl1, hall⟩ := hseg1
    let w := (1 - l) • W1.E0 + l • W1.E1
    have hfac2 : ∀ i, 0 < ⟪W2.fac i, w⟫ := hfac w (fun i => hall (Sum.inl i))
    have hr2 : ∀ j, 0 < ⟪rForm (fun i => x2 (c.r i)) i0' L' j, w⟫ := by
      intro j
      have := hall (Sum.inr (e.symm j))
      simp only [Sum.elim_inr] at this
      rw [he (e.symm j), e.apply_symm_apply] at this
      exact this
    have hseg2 : SegLet (Sum.elim W2.fac (rForm (fun i => x2 (c.r i)) i0' L')) W2.E0 W2.E1 := by
      rcases hseg with ⟨hE0, hE1⟩ | ⟨hE0, hE1⟩
      · rw [segLet_iff]
        refine ⟨l, hl0, hl1, fun i => ?_⟩
        rw [← hE0, ← hE1]
        rcases i with i | i
        · exact hfac2 i
        · exact hr2 i
      · rw [segLet_iff]
        refine ⟨1 - l, by linarith, by linarith, fun i => ?_⟩
        have hw : (1 - (1 - l)) • W2.E0 + (1 - l) • W2.E1 = w := by
          simp only [w, hE0, hE1]; module
        rw [hw]
        rcases i with i | i
        · exact hfac2 i
        · exact hr2 i
    exact hW2.1 i0' L' hseg2
  · rw [hr'] at hseg1
    obtain ⟨l, hl0, hl1, hall⟩ := (segLet_iff _ _ _).1 hseg1
    obtain ⟨hU1, hD1⟩ := W1.face l hl0 hl1 (fun i => hall (Sum.inl i))
    have evC1 := cellAt_eventually_of_wall F1 c.U hU1 hD1
    have evL1 : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ i, 0 < ⟪Sum.elim (hForm (fun i => x2 (c.r (-i))) s1 a m)
        (dForm (fun i => x2 (c.r (-i))) a m σ) i, (1 - l) • W1.E0 + l • W1.E1 + η • W1.v⟫ := by
      rw [eventually_all]
      intro i
      exact ev_inner_pos (hall (Sum.inr i))
    obtain ⟨η, hc1, hl1'⟩ := (evC1.and evL1).exists
    obtain ⟨ρ1, hρ1, hrim1⟩ := rimSign_of_cell F1 c hc1
    have hρ1s1 : 0 < ρ1 * s1 := hs1 _ hc1 ρ1 hρ1 hrim1
    have hc2 : CellAt F2 c.U (univ \ c.U) ((1 - l) • W1.E0 + l • W1.E1 + η • W1.v) := hcell _ hc1
    obtain ⟨ρ2, hρ2, hrim2⟩ := rimSign_of_cell F2 c hc2
    have hρ2s2 : 0 < ρ2 * s2 := hs2 _ hc2 ρ2 hρ2 hrim2
    have hρ12 : ρ2 = -ρ1 := by
      have h1lt : 1 < c.k := by have := c.hk; omega
      have : Fact (1 < c.k) := ⟨h1lt⟩
      have h1ne0 : (1 : ZMod c.k) ≠ 0 := by
        intro h; have := congrArg ZMod.val h; rw [ZMod.val_one, ZMod.val_zero] at this; omega
      have h2ne0 : (2 : ZMod c.k) ≠ 0 := by
        intro h
        have hlt : 2 < c.k := by have := c.hk; omega
        have hv : (2 : ZMod c.k).val = 2 := by
          change ((2 : ℕ) : ZMod c.k).val = 2; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        have := congrArg ZMod.val h; rw [hv, ZMod.val_zero] at this; omega
      have ha := hrim1 0 2 h2ne0 (fun h => h1ne0 (by linear_combination h))
      have hb := hrim2 (-1) (-2) (fun h => h1ne0 (by linear_combination -h))
        (fun h => h2ne0 (by linear_combination -h))
      have edet : Split.det3 (x1 (c.r (0 + 1)) - x1 (c.r 0)) (x1 (c.r 2) - x1 (c.r 0))
          ((1 - l) • W1.E0 + l • W1.E1 + η • W1.v) =
          -Split.det3 (x2 (c.r (-1 + 1)) - x2 (c.r (-1))) (x2 (c.r (-2)) - x2 (c.r (-1)))
          ((1 - l) • W1.E0 + l • W1.E1 + η • W1.v) := by
        rw [hr (0 + 1), hr 0, hr 2]
        have e0 : -(0 + 1 : ZMod c.k) = -1 := by ring
        have e1 : (-0 : ZMod c.k) = -1 + 1 := by ring
        rw [e0, e1]
        simp only [Split.det3, PiLp.sub_apply]; ring
      rw [edet] at ha
      rcases hρ1 with rfl | rfl <;> rcases hρ2 with rfl | rfl <;> nlinarith
    have hs12 : 0 < (-s1) * s2 := by
      rw [hρ12] at hρ2s2
      rcases hρ1 with rfl | rfl <;> nlinarith
    have hs1_ne : -s1 ≠ 0 := by rintro h; rw [h, zero_mul] at hs12; exact lt_irrefl 0 hs12
    have hpos_ratio : 0 < s2 / (-s1) := by
      have hsq : 0 < (-s1)⁻¹ ^ 2 := by positivity
      have heq : s2 / (-s1) = (-s1)⁻¹ ^ 2 * ((-s1) * s2) := by field_simp
      rw [heq]; exact mul_pos hsq hs12
    let w := (1 - l) • W1.E0 + l • W1.E1
    have hfac2 : ∀ i, 0 < ⟪W2.fac i, w⟫ := hfac w (fun i => hall (Sum.inl i))
    have ha' : -m ≠ -a - 1 := fun h => hma1 (by linear_combination -h)
    have ha1' : -m ≠ (-a - 1) + 1 := fun h => hma (by linear_combination -h)
    have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> simp
    have hh2 : ∀ j : {j : ZMod c.k // j ≠ -a - 1 ∧ j ≠ (-a - 1) + 1 ∧ j ≠ -m},
        0 < ⟪hForm (fun i => x2 (c.r i)) s2 (-a - 1) (-m) j, w⟫ := by
      intro j
      let j0 : {j : ZMod c.k // j ≠ a ∧ j ≠ a + 1 ∧ j ≠ m} :=
        ⟨-j.1, fun h => j.2.2.1 (by linear_combination -h),
               fun h => j.2.1 (by linear_combination -h),
               fun h => j.2.2.2 (by linear_combination -h)⟩
      have h0 := hall (Sum.inr (Sum.inl j0))
      simp only [Sum.elim_inr, Sum.elim_inl] at h0
      have hh := hForm_rev (fun i => x2 (c.r i)) s1 a m j0
      rw [hh] at h0
      have hsc : hForm (fun i => x2 (c.r i)) s2 (-a - 1) (-m) j =
          (s2 / (-s1)) • hForm (fun i => x2 (c.r i)) (-s1) (-a - 1) (-m)
            ⟨-j0.1, fun h => j0.2.2.1 (by linear_combination -h),
                    fun h => j0.2.1 (by linear_combination -h),
                    fun h => j0.2.2.2 (by linear_combination -h)⟩ := by
        simp only [hForm, smul_smul, div_mul_cancel₀ _ hs1_ne]
        congr 2; ext; simp [j0]
      rw [hsc, real_inner_smul_left]
      exact mul_pos hpos_ratio (by simpa [j0] using h0)
    have hd2 : ∀ j : {j : ZMod c.k // j ≠ -m},
        0 < ⟪dForm (fun i => x2 (c.r i)) (-a - 1) (-m) (-σ) j, w⟫ := by
      intro j
      let j0 : {j : ZMod c.k // j ≠ m} := ⟨-j.1, fun h => j.2 (by linear_combination -h)⟩
      have h0 := hall (Sum.inr (Sum.inr j0))
      simp only [Sum.elim_inr] at h0
      have hd := dForm_rev (fun i => x2 (c.r i)) a m σ j0
      rw [hd] at h0
      simpa [j0] using h0
    have hseg2 : SegLet (Sum.elim W2.fac (Sum.elim (hForm (fun i => x2 (c.r i)) s2 (-a - 1) (-m))
        (dForm (fun i => x2 (c.r i)) (-a - 1) (-m) (-σ)))) W2.E0 W2.E1 := by
      rcases hseg with ⟨hE0, hE1⟩ | ⟨hE0, hE1⟩
      · rw [segLet_iff]
        refine ⟨l, hl0, hl1, fun i => ?_⟩
        rw [← hE0, ← hE1]
        rcases i with i | (j | j)
        · exact hfac2 i
        · exact hh2 j
        · exact hd2 j
      · rw [segLet_iff]
        refine ⟨1 - l, by linarith, by linarith, fun i => ?_⟩
        have hw : (1 - (1 - l)) • W2.E0 + (1 - l) • W2.E1 = w := by
          simp only [w, hE0, hE1]; module
        rw [hw]
        rcases i with i | (j | j)
        · exact hfac2 i
        · exact hh2 j
        · exact hd2 j
    exact hW2.2 (-a - 1) (-m) (-σ) ha' ha1' hσ' hseg2

/-- On a self-dual cell `c` (`c.U.image sig24 = c.U` and `pi24 (c.r i) = c.r (-i)`),
`WallE` on the twin `(x ∘ π_24, sym24 F)` at `W1` is equivalent to `WallE` on `(x, F)` at `W2`. -/
theorem wallE_selfDual_iff (F : S0xFac 9 s0x_S24 x) (c : Cell24)
    (hU : c.U.image Sym.sig24 = c.U)
    (hrev : ∀ i : ZMod c.k, Sym.pi24 (c.r i) = c.r (-i))
    (W1 : CellWall (Sym.sym24 F) c) (W2 : CellWall F c)
    (hseg : (W1.E0 = W2.E0 ∧ W1.E1 = W2.E1) ∨ (W1.E0 = W2.E1 ∧ W1.E1 = W2.E0))
    (hfac : ∀ w : ℝ³, (∀ i, 0 < ⟪W1.fac i, w⟫) ↔ (∀ i, 0 < ⟪W2.fac i, w⟫))
    {s1 s2 : ℝ}
    (hs1 : ∀ w : ℝ³, CellAt (Sym.sym24 F) c.U (univ \ c.U) w → ∀ ρ : ℝ, (ρ = 1 ∨ ρ = -1) →
      (∀ i j : ZMod c.k, j ≠ i → j ≠ i + 1 →
        0 < ρ * Split.det3 (x (Sym.pi24 (c.r (i + 1))) - x (Sym.pi24 (c.r i)))
          (x (Sym.pi24 (c.r j)) - x (Sym.pi24 (c.r i))) w) → 0 < ρ * s1)
    (hs2 : ∀ w : ℝ³, CellAt F c.U (univ \ c.U) w → ∀ ρ : ℝ, (ρ = 1 ∨ ρ = -1) →
      (∀ i j : ZMod c.k, j ≠ i → j ≠ i + 1 →
        0 < ρ * Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r j) - x (c.r i)) w) → 0 < ρ * s2) :
    WallE (Sym.sym24 F) c W1 s1 ↔ WallE F c W2 s2 := by
  have hcell12 : ∀ w, CellAt (Sym.sym24 F) c.U (univ \ c.U) w → CellAt F c.U (univ \ c.U) w := by
    intro w hc
    have := (cellAt_sym24 F c w).1 hc
    simpa only [symCell24, hU] using this
  have hcell21 : ∀ w, CellAt F c.U (univ \ c.U) w → CellAt (Sym.sym24 F) c.U (univ \ c.U) w := by
    intro w hc
    apply (cellAt_sym24 F c w).2
    simpa only [symCell24, hU] using hc
  have hseg' : (W2.E0 = W1.E0 ∧ W2.E1 = W1.E1) ∨ (W2.E0 = W1.E1 ∧ W2.E1 = W1.E0) := by
    rcases hseg with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨h0.symm, h1.symm⟩
    · exact Or.inr ⟨h1.symm, h0.symm⟩
  have hr21 : ∀ i : ZMod c.k, x (c.r i) = (x ∘ Sym.pi24) (c.r (-i)) := by
    intro i; simp only [Function.comp_apply, hrev (-i), neg_neg]
  exact ⟨wallE_rev_imp F (Sym.sym24 F) c hcell21 hr21 W2 W1 hseg' (fun w => (hfac w).2) hs2 hs1,
         wallE_rev_imp (Sym.sym24 F) F c hcell12 (fun i => congrArg x (hrev i)) W1 W2 hseg (fun w => (hfac w).1) hs1 hs2⟩

private lemma cellWallOf_fac_sym_iff {F : S0xFac 9 s0x_S24 x} {c1 c2 : Cell24}
    {tw1 tw2 : Fin 9} {forms1 forms2 : List (Fin 9 × Bool)}
    {a0 b0 a1 b1 vp vq a0' b0' a1' b1' vp' vq' : Fin 7}
    {hok1 : wallOK c1.U tw1 forms1 a0 b0 a1 b1 vp vq = true}
    {hok2 : wallOK c2.U tw2 forms2 a0' b0' a1' b1' vp' vq' = true}
    (h12 : forms1.all (fun p => forms2.any (fun q => q.1 == Sym.sig24 p.1 && q.2 == p.2)) = true)
    (h21 : forms2.all (fun p => forms1.any (fun q => q.1 == Sym.sig24 p.1 && q.2 == p.2)) = true)
    (w : ℝ³) :
    (∀ i, 0 < ⟪(cellWallOf (Sym.sym24 F) c1 tw1 forms1 a0 b0 a1 b1 vp vq hok1).fac i, w⟫) ↔
      (∀ i, 0 < ⟪(cellWallOf F c2 tw2 forms2 a0' b0' a1' b1' vp' vq' hok2).fac i, w⟫) := by
  constructor
  · intro h1 i
    have hmem : forms2[i.1] ∈ forms2 := List.getElem_mem i.2
    have hany := (List.all_eq_true.1 h21) _ hmem
    obtain ⟨q, hqmem, hqeq⟩ := List.any_eq_true.1 hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hqeq
    obtain ⟨j, hjlt, hj⟩ := List.mem_iff_getElem.1 hqmem
    have h1j := h1 ⟨j, hjlt⟩
    change 0 < ⟪if forms1[j].2 then F.N (Sym.sig24 forms1[j].1) else -F.N (Sym.sig24 forms1[j].1), w⟫ at h1j
    change 0 < ⟪if forms2[i.1].2 then F.N forms2[i.1].1 else -F.N forms2[i.1].1, w⟫
    rw [hj, hqeq.2, hqeq.1, sig24_invol] at h1j
    exact h1j
  · intro h2 i
    have hmem : forms1[i.1] ∈ forms1 := List.getElem_mem i.2
    have hany := (List.all_eq_true.1 h12) _ hmem
    obtain ⟨q, hqmem, hqeq⟩ := List.any_eq_true.1 hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hqeq
    obtain ⟨j, hjlt, hj⟩ := List.mem_iff_getElem.1 hqmem
    have h2j := h2 ⟨j, hjlt⟩
    change 0 < ⟪if forms2[j].2 then F.N forms2[j].1 else -F.N forms2[j].1, w⟫ at h2j
    change 0 < ⟪if forms1[i.1].2 then F.N (Sym.sig24 forms1[i.1].1) else -F.N (Sym.sig24 forms1[i.1].1), w⟫
    rw [hj, hqeq.2, hqeq.1] at h2j
    exact h2j


/-! ## GE2: Mirror cells, 429 mirror walls, 165 self-dual wall equivalences, and `AllWallE2S` -/

def sym_cellC : Cell24 := symCell24 cellC
def sym_cellD : Cell24 := symCell24 cellD
def sym_cellD6 : Cell24 := symCell24 cellD6
def sym_cellA2 : Cell24 := symCell24 cellA2
def sym_cellB2 : Cell24 := symCell24 cellB2
def sym_cellA0 : Cell24 := symCell24 cellA0
def sym_cellCp : Cell24 := symCell24 cellC'
def sym_cell0536 : Cell24 := symCell24 cell0536
def sym_cell0164 : Cell24 := symCell24 cell0164
def sym_cell01634 : Cell24 := symCell24 cell01634
def sym_cell05326 : Cell24 := symCell24 cell05326

noncomputable def symWall_cellC_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t1_01_61 (Sym.sym24 F))

def SymWallE_cellC_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t1_01_61 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t1_01_61 x F := by
  rcases cert_cellC_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t2_50_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t2_50_52 (Sym.sym24 F))

def SymWallE_cellC_t2_50_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t2_50_52 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t2_50_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t2_50_52 x F := by
  rcases cert_cellC_t2_50_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t4_40_46 (Sym.sym24 F))

def SymWallE_cellC_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t4_40_46 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t4_40_46 x F := by
  rcases cert_cellC_t4_40_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t6_32_52 (Sym.sym24 F))

def SymWallE_cellC_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t6_32_52 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t6_32_52 x F := by
  rcases cert_cellC_t6_32_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t7_32_36 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t7_32_36 (Sym.sym24 F))

def SymWallE_cellC_t7_32_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t7_32_36 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t7_32_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t7_32_36 x F := by
  rcases cert_cellC_t7_32_36 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t8_43_46 (Sym.sym24 F))

def SymWallE_cellC_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t8_43_46 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t8_43_46 x F := by
  rcases cert_cellC_t8_43_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t0_10_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t0_10_12 (Sym.sym24 F))

def SymWallE_cellD_t0_10_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t0_10_12 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t0_10_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t0_10_12 x F := by
  rcases cert_cellD_t0_10_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t1_10_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t1_10_60 (Sym.sym24 F))

def SymWallE_cellD_t1_10_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t1_10_60 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t1_10_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t1_10_60 x F := by
  rcases cert_cellD_t1_10_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t4_04_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t4_04_64 (Sym.sym24 F))

def SymWallE_cellD_t4_04_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t4_04_64 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t4_04_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t4_04_64 x F := by
  rcases cert_cellD_t4_04_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t6_25_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t6_25_35 (Sym.sym24 F))

def SymWallE_cellD_t6_25_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t6_25_35 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t6_25_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t6_25_35 x F := by
  rcases cert_cellD_t6_25_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t8_34_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t8_34_64 (Sym.sym24 F))

def SymWallE_cellD_t8_34_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t8_34_64 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t8_34_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t8_34_64 x F := by
  rcases cert_cellD_t8_34_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t0_10_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t0_10_12 (Sym.sym24 F))

def SymWallE_cellD6_t0_10_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t0_10_12 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t0_10_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t0_10_12 x F := by
  rcases cert_cellD6_t0_10_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t1_10_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t1_10_60 (Sym.sym24 F))

def SymWallE_cellD6_t1_10_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t1_10_60 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t1_10_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t1_10_60 x F := by
  rcases cert_cellD6_t1_10_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t4_60_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t4_60_64 (Sym.sym24 F))

def SymWallE_cellD6_t4_60_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t4_60_64 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t4_60_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t4_60_64 x F := by
  rcases cert_cellD6_t4_60_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t6_25_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t6_25_35 (Sym.sym24 F))

def SymWallE_cellD6_t6_25_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t6_25_35 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t6_25_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t6_25_35 x F := by
  rcases cert_cellD6_t6_25_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t8_34_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t8_34_64 (Sym.sym24 F))

def SymWallE_cellD6_t8_34_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t8_34_64 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t8_34_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t8_34_64 x F := by
  rcases cert_cellD6_t8_34_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t0_02_12 (Sym.sym24 F))

def SymWallE_cellA2_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t0_02_12 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t0_02_12 x F := by
  rcases cert_cellA2_t0_02_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t1_01_61 (Sym.sym24 F))

def SymWallE_cellA2_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t1_01_61 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t1_01_61 x F := by
  rcases cert_cellA2_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t2_02_52 (Sym.sym24 F))

def SymWallE_cellA2_t2_02_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t2_02_52 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t2_02_52 x F := by
  rcases cert_cellA2_t2_02_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_05_35 (Sym.sym24 F))

def SymWallE_cellA2_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_05_35 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_05_35 x F := by
  rcases cert_cellA2_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_05_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_05_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_05_45 x F := by
  rcases cert_cellA2_t3_05_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_35_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_35_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_35_45 x F := by
  rcases cert_cellA2_t3_35_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_40_43 (Sym.sym24 F))

def SymWallE_cellA2_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_40_43 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_40_43 x F := by
  rcases cert_cellA2_t3_40_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_40_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_40_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_40_45 x F := by
  rcases cert_cellA2_t3_40_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_43_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_43_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_43_45 x F := by
  rcases cert_cellA2_t3_43_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t5_12_62 (Sym.sym24 F))

def SymWallE_cellA2_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t5_12_62 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t5_12_62 x F := by
  rcases cert_cellA2_t5_12_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t6_32_52 (Sym.sym24 F))

def SymWallE_cellA2_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t6_32_52 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t6_32_52 x F := by
  rcases cert_cellA2_t6_32_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t7_32_62 (Sym.sym24 F))

def SymWallE_cellA2_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t7_32_62 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t7_32_62 x F := by
  rcases cert_cellA2_t7_32_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t8_43_46 (Sym.sym24 F))

def SymWallE_cellA2_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t8_43_46 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t8_43_46 x F := by
  rcases cert_cellA2_t8_43_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t0_02_12 (Sym.sym24 F))

def SymWallE_cellB2_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t0_02_12 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t0_02_12 x F := by
  rcases cert_cellB2_t0_02_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t1_01_61 (Sym.sym24 F))

def SymWallE_cellB2_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t1_01_61 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t1_01_61 x F := by
  rcases cert_cellB2_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t2_02_52 (Sym.sym24 F))

def SymWallE_cellB2_t2_02_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t2_02_52 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t2_02_52 x F := by
  rcases cert_cellB2_t2_02_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_03_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_03_43 (Sym.sym24 F))

def SymWallE_cellB2_t3_03_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_03_43 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_03_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_03_43 x F := by
  rcases cert_cellB2_t3_03_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_05_35 (Sym.sym24 F))

def SymWallE_cellB2_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_05_35 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_05_35 x F := by
  rcases cert_cellB2_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_05_45 (Sym.sym24 F))

def SymWallE_cellB2_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_05_45 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_05_45 x F := by
  rcases cert_cellB2_t3_05_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_43_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_43_53 (Sym.sym24 F))

def SymWallE_cellB2_t3_43_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_43_53 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_43_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_43_53 x F := by
  rcases cert_cellB2_t3_43_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t5_12_62 (Sym.sym24 F))

def SymWallE_cellB2_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t5_12_62 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t5_12_62 x F := by
  rcases cert_cellB2_t5_12_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t6_32_52 (Sym.sym24 F))

def SymWallE_cellB2_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t6_32_52 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t6_32_52 x F := by
  rcases cert_cellB2_t6_32_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t8_43_46 (Sym.sym24 F))

def SymWallE_cellB2_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t8_43_46 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t8_43_46 x F := by
  rcases cert_cellB2_t8_43_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t0_10_20 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t0_10_20 (Sym.sym24 F))

def SymWallE_cellA0_t0_10_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t0_10_20 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t0_10_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t0_10_20 x F := by
  rcases cert_cellA0_t0_10_20 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t1_10_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t1_10_60 (Sym.sym24 F))

def SymWallE_cellA0_t1_10_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t1_10_60 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t1_10_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t1_10_60 x F := by
  rcases cert_cellA0_t1_10_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t2_20_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t2_20_50 (Sym.sym24 F))

def SymWallE_cellA0_t2_20_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t2_20_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t2_20_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t2_20_50 x F := by
  rcases cert_cellA0_t2_20_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_04_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_04_34 (Sym.sym24 F))

def SymWallE_cellA0_t3_04_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_04_34 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_04_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_04_34 x F := by
  rcases cert_cellA0_t3_04_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_30_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_30_50 (Sym.sym24 F))

def SymWallE_cellA0_t3_30_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_30_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_30_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_30_50 x F := by
  rcases cert_cellA0_t3_30_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_34_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_34_54 (Sym.sym24 F))

def SymWallE_cellA0_t3_34_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_34_54 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_34_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_34_54 x F := by
  rcases cert_cellA0_t3_34_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_40_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_40_50 (Sym.sym24 F))

def SymWallE_cellA0_t3_40_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_40_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_40_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_40_50 x F := by
  rcases cert_cellA0_t3_40_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t5_21_61 (Sym.sym24 F))

def SymWallE_cellA0_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t5_21_61 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t5_21_61 x F := by
  rcases cert_cellA0_t5_21_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t6_25_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t6_25_35 (Sym.sym24 F))

def SymWallE_cellA0_t6_25_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t6_25_35 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t6_25_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t6_25_35 x F := by
  rcases cert_cellA0_t6_25_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t8_34_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t8_34_64 (Sym.sym24 F))

def SymWallE_cellA0_t8_34_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t8_34_64 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t8_34_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t8_34_64 x F := by
  rcases cert_cellA0_t8_34_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t1_01_61 (Sym.sym24 F))

def SymWallE_cellCp_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t1_01_61 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t1_01_61 x F := by
  rcases cert_cellCp_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_30_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_30_35 (Sym.sym24 F))

def SymWallE_cellCp_t3_30_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_30_35 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_30_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_30_35 x F := by
  rcases cert_cellCp_t3_30_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_34_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_34_35 (Sym.sym24 F))

def SymWallE_cellCp_t3_34_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_34_35 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_34_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_34_35 x F := by
  rcases cert_cellCp_t3_34_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_40_43 (Sym.sym24 F))

def SymWallE_cellCp_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_40_43 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_40_43 x F := by
  rcases cert_cellCp_t3_40_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_40_45 (Sym.sym24 F))

def SymWallE_cellCp_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_40_45 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_40_45 x F := by
  rcases cert_cellCp_t3_40_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t4_40_46 (Sym.sym24 F))

def SymWallE_cellCp_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t4_40_46 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t4_40_46 x F := by
  rcases cert_cellCp_t4_40_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t5_21_61 (Sym.sym24 F))

def SymWallE_cellCp_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t5_21_61 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t5_21_61 x F := by
  rcases cert_cellCp_t5_21_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t6_32_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t6_32_35 (Sym.sym24 F))

def SymWallE_cellCp_t6_32_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t6_32_35 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t6_32_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t6_32_35 x F := by
  rcases cert_cellCp_t6_32_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t7_32_36 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t7_32_36 (Sym.sym24 F))

def SymWallE_cellCp_t7_32_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t7_32_36 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t7_32_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t7_32_36 x F := by
  rcases cert_cellCp_t7_32_36 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t1_01_61 (Sym.sym24 F))

def SymWallE_cell0536_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t1_01_61 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t1_01_61 x F := by
  rcases cert_cell0536_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t2_02_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t2_02_52 (Sym.sym24 F))

def SymWallE_cell0536_t2_02_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t2_02_52 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t2_02_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t2_02_52 x F := by
  rcases cert_cell0536_t2_02_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_05_35 (Sym.sym24 F))

def SymWallE_cell0536_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_05_35 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_05_35 x F := by
  rcases cert_cell0536_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_05_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_05_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_05_45 x F := by
  rcases cert_cell0536_t3_05_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_35_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_35_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_35_45 x F := by
  rcases cert_cell0536_t3_35_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_40_43 (Sym.sym24 F))

def SymWallE_cell0536_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_40_43 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_40_43 x F := by
  rcases cert_cell0536_t3_40_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_40_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_40_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_40_45 x F := by
  rcases cert_cell0536_t3_40_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_43_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_43_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_43_45 x F := by
  rcases cert_cell0536_t3_43_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t4_40_46 (Sym.sym24 F))

def SymWallE_cell0536_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t4_40_46 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t4_40_46 x F := by
  rcases cert_cell0536_t4_40_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t6_32_52 (Sym.sym24 F))

def SymWallE_cell0536_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t6_32_52 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t6_32_52 x F := by
  rcases cert_cell0536_t6_32_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t7_32_62 (Sym.sym24 F))

def SymWallE_cell0536_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t7_32_62 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t7_32_62 x F := by
  rcases cert_cell0536_t7_32_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t8_43_46 (Sym.sym24 F))

def SymWallE_cell0536_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t8_43_46 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t8_43_46 x F := by
  rcases cert_cell0536_t8_43_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t0_02_12 (Sym.sym24 F))

def SymWallE_cell0164_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t0_02_12 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t0_02_12 x F := by
  rcases cert_cell0164_t0_02_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t1_01_61 (Sym.sym24 F))

def SymWallE_cell0164_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t1_01_61 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t1_01_61 x F := by
  rcases cert_cell0164_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_03_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_03_43 (Sym.sym24 F))

def SymWallE_cell0164_t3_03_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_03_43 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_03_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_03_43 x F := by
  rcases cert_cell0164_t3_03_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_05_35 (Sym.sym24 F))

def SymWallE_cell0164_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_05_35 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_05_35 x F := by
  rcases cert_cell0164_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_05_45 (Sym.sym24 F))

def SymWallE_cell0164_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_05_45 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_05_45 x F := by
  rcases cert_cell0164_t3_05_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_43_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_43_53 (Sym.sym24 F))

def SymWallE_cell0164_t3_43_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_43_53 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_43_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_43_53 x F := by
  rcases cert_cell0164_t3_43_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t5_12_62 (Sym.sym24 F))

def SymWallE_cell0164_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t5_12_62 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t5_12_62 x F := by
  rcases cert_cell0164_t5_12_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t8_43_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t8_43_63 (Sym.sym24 F))

def SymWallE_cell0164_t8_43_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t8_43_63 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t8_43_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t8_43_63 x F := by
  rcases cert_cell0164_t8_43_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t0_02_12 (Sym.sym24 F))

def SymWallE_cell01634_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t0_02_12 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t0_02_12 x F := by
  rcases cert_cell01634_t0_02_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t1_01_61 (Sym.sym24 F))

def SymWallE_cell01634_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t1_01_61 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t1_01_61 x F := by
  rcases cert_cell01634_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_05_35 (Sym.sym24 F))

def SymWallE_cell01634_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_05_35 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_05_35 x F := by
  rcases cert_cell01634_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_05_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_05_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_05_45 x F := by
  rcases cert_cell01634_t3_05_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_35_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_35_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_35_45 x F := by
  rcases cert_cell01634_t3_35_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_40_43 (Sym.sym24 F))

def SymWallE_cell01634_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_40_43 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_40_43 x F := by
  rcases cert_cell01634_t3_40_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_40_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_40_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_40_45 x F := by
  rcases cert_cell01634_t3_40_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_43_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_43_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_43_45 x F := by
  rcases cert_cell01634_t3_43_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t5_12_62 (Sym.sym24 F))

def SymWallE_cell01634_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t5_12_62 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t5_12_62 x F := by
  rcases cert_cell01634_t5_12_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t7_32_62 (Sym.sym24 F))

def SymWallE_cell01634_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t7_32_62 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t7_32_62 x F := by
  rcases cert_cell01634_t7_32_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t8_43_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t8_43_63 (Sym.sym24 F))

def SymWallE_cell01634_t8_43_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t8_43_63 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t8_43_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t8_43_63 x F := by
  rcases cert_cell01634_t8_43_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t1_01_61 (Sym.sym24 F))

def SymWallE_cell05326_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t1_01_61 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t1_01_61 x F := by
  rcases cert_cell05326_t1_01_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_05_35 (Sym.sym24 F))

def SymWallE_cell05326_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_05_35 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_05_35 x F := by
  rcases cert_cell05326_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_35_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_35_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_35_45 x F := by
  rcases cert_cell05326_t3_35_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_40_43 (Sym.sym24 F))

def SymWallE_cell05326_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_40_43 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_40_43 x F := by
  rcases cert_cell05326_t3_40_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_40_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_40_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_40_45 x F := by
  rcases cert_cell05326_t3_40_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t4_40_46 (Sym.sym24 F))

def SymWallE_cell05326_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t4_40_46 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t4_40_46 x F := by
  rcases cert_cell05326_t4_40_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t5_21_61 (Sym.sym24 F))

def SymWallE_cell05326_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t5_21_61 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t5_21_61 x F := by
  rcases cert_cell05326_t5_21_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t6_32_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t6_32_35 (Sym.sym24 F))

def SymWallE_cell05326_t6_32_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t6_32_35 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t6_32_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t6_32_35 x F := by
  rcases cert_cell05326_t6_32_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t7_32_62 (Sym.sym24 F))

def SymWallE_cell05326_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t7_32_62 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t7_32_62 x F := by
  rcases cert_cell05326_t7_32_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t1_01_60 (Sym.sym24 F))

def SymWallE_cellC_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t1_01_60 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t1_01_60 x F := by
  rcases cert_cellC_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t1_06_61 (Sym.sym24 F))

def SymWallE_cellC_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t1_06_61 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t1_06_61 x F := by
  rcases cert_cellC_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t2_02_50 (Sym.sym24 F))

def SymWallE_cellC_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t2_02_50 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t2_02_50 x F := by
  rcases cert_cellC_t2_02_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t2_20_52 (Sym.sym24 F))

def SymWallE_cellC_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t2_20_52 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t2_20_52 x F := by
  rcases cert_cellC_t2_20_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_03_40 (Sym.sym24 F))

def SymWallE_cellC_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_03_40 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_03_40 x F := by
  rcases cert_cellC_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_04_35 (Sym.sym24 F))

def SymWallE_cellC_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_04_35 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_04_35 x F := by
  rcases cert_cellC_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_04_45 (Sym.sym24 F))

def SymWallE_cellC_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_04_45 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_04_45 x F := by
  rcases cert_cellC_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_05_30 (Sym.sym24 F))

def SymWallE_cellC_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_05_30 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_05_30 x F := by
  rcases cert_cellC_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_05_34 (Sym.sym24 F))

def SymWallE_cellC_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_05_34 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_05_34 x F := by
  rcases cert_cellC_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_05_40 (Sym.sym24 F))

def SymWallE_cellC_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_05_40 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_05_40 x F := by
  rcases cert_cellC_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_30_43 (Sym.sym24 F))

def SymWallE_cellC_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_30_43 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_30_43 x F := by
  rcases cert_cellC_t3_30_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_30_45 (Sym.sym24 F))

def SymWallE_cellC_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_30_45 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_30_45 x F := by
  rcases cert_cellC_t3_30_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_30_53 (Sym.sym24 F))

def SymWallE_cellC_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_30_53 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_30_53 x F := by
  rcases cert_cellC_t3_30_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_34_45 (Sym.sym24 F))

def SymWallE_cellC_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_34_45 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_34_45 x F := by
  rcases cert_cellC_t3_34_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_35_40 (Sym.sym24 F))

def SymWallE_cellC_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_35_40 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_35_40 x F := by
  rcases cert_cellC_t3_35_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_35_50 (Sym.sym24 F))

def SymWallE_cellC_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_35_50 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_35_50 x F := by
  rcases cert_cellC_t3_35_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_35_54 (Sym.sym24 F))

def SymWallE_cellC_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_35_54 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_35_54 x F := by
  rcases cert_cellC_t3_35_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_40_43 (Sym.sym24 F))

def SymWallE_cellC_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_40_43 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_40_43 x F := by
  rcases cert_cellC_t3_40_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_40_45 (Sym.sym24 F))

def SymWallE_cellC_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_40_45 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_40_45 x F := by
  rcases cert_cellC_t3_40_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_40_53 (Sym.sym24 F))

def SymWallE_cellC_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_40_53 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_40_53 x F := by
  rcases cert_cellC_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_43_50 (Sym.sym24 F))

def SymWallE_cellC_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_43_50 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_43_50 x F := by
  rcases cert_cellC_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t3_45_50 (Sym.sym24 F))

def SymWallE_cellC_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t3_45_50 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t3_45_50 x F := by
  rcases cert_cellC_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t4_06_40 (Sym.sym24 F))

def SymWallE_cellC_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t4_06_40 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t4_06_40 x F := by
  rcases cert_cellC_t4_06_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t4_46_60 (Sym.sym24 F))

def SymWallE_cellC_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t4_46_60 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t4_46_60 x F := by
  rcases cert_cellC_t4_46_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t6_32_53 (Sym.sym24 F))

def SymWallE_cellC_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t6_32_53 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t6_32_53 x F := by
  rcases cert_cellC_t6_32_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t6_35_52 (Sym.sym24 F))

def SymWallE_cellC_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t6_35_52 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t6_35_52 x F := by
  rcases cert_cellC_t6_35_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t7_26_32 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t7_26_32 (Sym.sym24 F))

def SymWallE_cellC_t7_26_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t7_26_32 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t7_26_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t7_26_32 x F := by
  rcases cert_cellC_t7_26_32 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t7_36_62 (Sym.sym24 F))

def SymWallE_cellC_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t7_36_62 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t7_36_62 x F := by
  rcases cert_cellC_t7_36_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t8_36_43 (Sym.sym24 F))

def SymWallE_cellC_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t8_36_43 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t8_36_43 x F := by
  rcases cert_cellC_t8_36_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellC_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellC :=
  unsymCellWall F cellC (wall_cellC_t8_46_63 (Sym.sym24 F))

def SymWallE_cellC_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellC (symWall_cellC_t8_46_63 F) (cellRimScalar cellC 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellC_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellC_t8_46_63 x F := by
  rcases cert_cellC_t8_46_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t0_02_10 (Sym.sym24 F))

def SymWallE_cellD_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t0_02_10 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t0_02_10 x F := by
  rcases cert_cellD_t0_02_10 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t0_12_20 (Sym.sym24 F))

def SymWallE_cellD_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t0_12_20 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t0_12_20 x F := by
  rcases cert_cellD_t0_12_20 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t1_10_61 (Sym.sym24 F))

def SymWallE_cellD_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t1_10_61 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t1_10_61 x F := by
  rcases cert_cellD_t1_10_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t1_16_60 (Sym.sym24 F))

def SymWallE_cellD_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t1_16_60 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t1_16_60 x F := by
  rcases cert_cellD_t1_16_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_03_34 (Sym.sym24 F))

def SymWallE_cellD_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_03_34 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_03_34 x F := by
  rcases cert_cellD_t3_03_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_03_35 (Sym.sym24 F))

def SymWallE_cellD_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_03_35 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_03_35 x F := by
  rcases cert_cellD_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_04_30 (Sym.sym24 F))

def SymWallE_cellD_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_04_30 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_04_30 x F := by
  rcases cert_cellD_t3_04_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_04_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_04_34 (Sym.sym24 F))

def SymWallE_cellD_t3_04_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_04_34 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_04_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_04_34 x F := by
  rcases cert_cellD_t3_04_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_04_35 (Sym.sym24 F))

def SymWallE_cellD_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_04_35 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_04_35 x F := by
  rcases cert_cellD_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_05_30 (Sym.sym24 F))

def SymWallE_cellD_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_05_30 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_05_30 x F := by
  rcases cert_cellD_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_05_34 (Sym.sym24 F))

def SymWallE_cellD_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_05_34 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_05_34 x F := by
  rcases cert_cellD_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_05_35 (Sym.sym24 F))

def SymWallE_cellD_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_05_35 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_05_35 x F := by
  rcases cert_cellD_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_40_53 (Sym.sym24 F))

def SymWallE_cellD_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_40_53 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_40_53 x F := by
  rcases cert_cellD_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_40_54 (Sym.sym24 F))

def SymWallE_cellD_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_40_54 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_40_54 x F := by
  rcases cert_cellD_t3_40_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_43_50 (Sym.sym24 F))

def SymWallE_cellD_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_43_50 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_43_50 x F := by
  rcases cert_cellD_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_43_54 (Sym.sym24 F))

def SymWallE_cellD_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_43_54 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_43_54 x F := by
  rcases cert_cellD_t3_43_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_45_50 (Sym.sym24 F))

def SymWallE_cellD_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_45_50 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_45_50 x F := by
  rcases cert_cellD_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t3_45_53 (Sym.sym24 F))

def SymWallE_cellD_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t3_45_53 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t3_45_53 x F := by
  rcases cert_cellD_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t4_04_60 (Sym.sym24 F))

def SymWallE_cellD_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t4_04_60 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t4_04_60 x F := by
  rcases cert_cellD_t4_04_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t4_06_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t4_06_64 (Sym.sym24 F))

def SymWallE_cellD_t4_06_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t4_06_64 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t4_06_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t4_06_64 x F := by
  rcases cert_cellD_t4_06_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t5_12_61 (Sym.sym24 F))

def SymWallE_cellD_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t5_12_61 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t5_12_61 x F := by
  rcases cert_cellD_t5_12_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t5_21_62 (Sym.sym24 F))

def SymWallE_cellD_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t5_21_62 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t5_21_62 x F := by
  rcases cert_cellD_t5_21_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t6_23_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t6_23_35 (Sym.sym24 F))

def SymWallE_cellD_t6_23_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t6_23_35 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t6_23_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t6_23_35 x F := by
  rcases cert_cellD_t6_23_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t6_25_32 (Sym.sym24 F))

def SymWallE_cellD_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t6_25_32 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t6_25_32 x F := by
  rcases cert_cellD_t6_25_32 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t7_23_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t7_23_62 (Sym.sym24 F))

def SymWallE_cellD_t7_23_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t7_23_62 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t7_23_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t7_23_62 x F := by
  rcases cert_cellD_t7_23_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t7_23_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t7_23_63 (Sym.sym24 F))

def SymWallE_cellD_t7_23_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t7_23_63 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t7_23_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t7_23_63 x F := by
  rcases cert_cellD_t7_23_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t7_26_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t7_26_63 (Sym.sym24 F))

def SymWallE_cellD_t7_26_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t7_26_63 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t7_26_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t7_26_63 x F := by
  rcases cert_cellD_t7_26_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t8_34_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t8_34_63 (Sym.sym24 F))

def SymWallE_cellD_t8_34_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t8_34_63 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t8_34_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t8_34_63 x F := by
  rcases cert_cellD_t8_34_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD :=
  unsymCellWall F cellD (wall_cellD_t8_36_64 (Sym.sym24 F))

def SymWallE_cellD_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD (symWall_cellD_t8_36_64 F) (cellRimScalar cellD 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD_t8_36_64 x F := by
  rcases cert_cellD_t8_36_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t0_02_10 (Sym.sym24 F))

def SymWallE_cellD6_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t0_02_10 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t0_02_10 x F := by
  rcases cert_cellD6_t0_02_10 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t0_12_20 (Sym.sym24 F))

def SymWallE_cellD6_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t0_12_20 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t0_12_20 x F := by
  rcases cert_cellD6_t0_12_20 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t1_10_61 (Sym.sym24 F))

def SymWallE_cellD6_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t1_10_61 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t1_10_61 x F := by
  rcases cert_cellD6_t1_10_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t1_16_60 (Sym.sym24 F))

def SymWallE_cellD6_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t1_16_60 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t1_16_60 x F := by
  rcases cert_cellD6_t1_16_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_03_35 (Sym.sym24 F))

def SymWallE_cellD6_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_03_35 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_03_35 x F := by
  rcases cert_cellD6_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_04_30 (Sym.sym24 F))

def SymWallE_cellD6_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_04_30 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_04_30 x F := by
  rcases cert_cellD6_t3_04_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_04_35 (Sym.sym24 F))

def SymWallE_cellD6_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_04_35 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_04_35 x F := by
  rcases cert_cellD6_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_05_30 (Sym.sym24 F))

def SymWallE_cellD6_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_05_30 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_05_30 x F := by
  rcases cert_cellD6_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_05_34 (Sym.sym24 F))

def SymWallE_cellD6_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_05_34 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_05_34 x F := by
  rcases cert_cellD6_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_05_35 (Sym.sym24 F))

def SymWallE_cellD6_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_05_35 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_05_35 x F := by
  rcases cert_cellD6_t3_05_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_30_43 (Sym.sym24 F))

def SymWallE_cellD6_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_30_43 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_30_43 x F := by
  rcases cert_cellD6_t3_30_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_30_45 (Sym.sym24 F))

def SymWallE_cellD6_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_30_45 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_30_45 x F := by
  rcases cert_cellD6_t3_30_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_34_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_34_40 (Sym.sym24 F))

def SymWallE_cellD6_t3_34_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_34_40 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_34_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_34_40 x F := by
  rcases cert_cellD6_t3_34_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_34_45 (Sym.sym24 F))

def SymWallE_cellD6_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_34_45 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_34_45 x F := by
  rcases cert_cellD6_t3_34_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_35_40 (Sym.sym24 F))

def SymWallE_cellD6_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_35_40 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_35_40 x F := by
  rcases cert_cellD6_t3_35_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_35_43 (Sym.sym24 F))

def SymWallE_cellD6_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_35_43 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_35_43 x F := by
  rcases cert_cellD6_t3_35_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_35_45 (Sym.sym24 F))

def SymWallE_cellD6_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_35_45 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_35_45 x F := by
  rcases cert_cellD6_t3_35_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_40_53 (Sym.sym24 F))

def SymWallE_cellD6_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_40_53 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_40_53 x F := by
  rcases cert_cellD6_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_40_54 (Sym.sym24 F))

def SymWallE_cellD6_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_40_54 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_40_54 x F := by
  rcases cert_cellD6_t3_40_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_43_50 (Sym.sym24 F))

def SymWallE_cellD6_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_43_50 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_43_50 x F := by
  rcases cert_cellD6_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_45_50 (Sym.sym24 F))

def SymWallE_cellD6_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_45_50 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_45_50 x F := by
  rcases cert_cellD6_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t3_45_53 (Sym.sym24 F))

def SymWallE_cellD6_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t3_45_53 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t3_45_53 x F := by
  rcases cert_cellD6_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t4_04_60 (Sym.sym24 F))

def SymWallE_cellD6_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t4_04_60 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t4_04_60 x F := by
  rcases cert_cellD6_t4_04_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t4_40_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t4_40_64 (Sym.sym24 F))

def SymWallE_cellD6_t4_40_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t4_40_64 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t4_40_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t4_40_64 x F := by
  rcases cert_cellD6_t4_40_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t5_12_61 (Sym.sym24 F))

def SymWallE_cellD6_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t5_12_61 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t5_12_61 x F := by
  rcases cert_cellD6_t5_12_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t5_21_62 (Sym.sym24 F))

def SymWallE_cellD6_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t5_21_62 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t5_21_62 x F := by
  rcases cert_cellD6_t5_21_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t6_23_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t6_23_35 (Sym.sym24 F))

def SymWallE_cellD6_t6_23_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t6_23_35 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t6_23_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t6_23_35 x F := by
  rcases cert_cellD6_t6_23_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t6_25_32 (Sym.sym24 F))

def SymWallE_cellD6_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t6_25_32 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t6_25_32 x F := by
  rcases cert_cellD6_t6_25_32 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t7_23_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t7_23_62 (Sym.sym24 F))

def SymWallE_cellD6_t7_23_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t7_23_62 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t7_23_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t7_23_62 x F := by
  rcases cert_cellD6_t7_23_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t7_32_63 (Sym.sym24 F))

def SymWallE_cellD6_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t7_32_63 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t7_32_63 x F := by
  rcases cert_cellD6_t7_32_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t8_34_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t8_34_63 (Sym.sym24 F))

def SymWallE_cellD6_t8_34_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t8_34_63 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t8_34_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t8_34_63 x F := by
  rcases cert_cellD6_t8_34_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellD6_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellD6 :=
  unsymCellWall F cellD6 (wall_cellD6_t8_36_64 (Sym.sym24 F))

def SymWallE_cellD6_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellD6 (symWall_cellD6_t8_36_64 F) (cellRimScalar cellD6 0 2 0 3 (x ∘ Sym.pi24))

theorem symCert_cellD6_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellD6_t8_36_64 x F := by
  rcases cert_cellD6_t8_36_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t0_01_12 (Sym.sym24 F))

def SymWallE_cellA2_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t0_01_12 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t0_01_12 x F := by
  rcases cert_cellA2_t0_01_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t0_02_10 (Sym.sym24 F))

def SymWallE_cellA2_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t0_02_10 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t0_02_10 x F := by
  rcases cert_cellA2_t0_02_10 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t1_01_60 (Sym.sym24 F))

def SymWallE_cellA2_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t1_01_60 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t1_01_60 x F := by
  rcases cert_cellA2_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t1_06_61 (Sym.sym24 F))

def SymWallE_cellA2_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t1_06_61 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t1_06_61 x F := by
  rcases cert_cellA2_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t2_02_50 (Sym.sym24 F))

def SymWallE_cellA2_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t2_02_50 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t2_02_50 x F := by
  rcases cert_cellA2_t2_02_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t2_05_52 (Sym.sym24 F))

def SymWallE_cellA2_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t2_05_52 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t2_05_52 x F := by
  rcases cert_cellA2_t2_05_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_03_35 (Sym.sym24 F))

def SymWallE_cellA2_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_03_35 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_03_35 x F := by
  rcases cert_cellA2_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_03_40 (Sym.sym24 F))

def SymWallE_cellA2_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_03_40 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_03_40 x F := by
  rcases cert_cellA2_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_03_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_03_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_03_45 x F := by
  rcases cert_cellA2_t3_03_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_04_35 (Sym.sym24 F))

def SymWallE_cellA2_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_04_35 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_04_35 x F := by
  rcases cert_cellA2_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_04_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_04_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_04_45 x F := by
  rcases cert_cellA2_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_05_30 (Sym.sym24 F))

def SymWallE_cellA2_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_05_30 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_05_30 x F := by
  rcases cert_cellA2_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_05_34 (Sym.sym24 F))

def SymWallE_cellA2_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_05_34 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_05_34 x F := by
  rcases cert_cellA2_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_05_40 (Sym.sym24 F))

def SymWallE_cellA2_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_05_40 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_05_40 x F := by
  rcases cert_cellA2_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_05_43 (Sym.sym24 F))

def SymWallE_cellA2_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_05_43 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_05_43 x F := by
  rcases cert_cellA2_t3_05_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_30_43 (Sym.sym24 F))

def SymWallE_cellA2_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_30_43 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_30_43 x F := by
  rcases cert_cellA2_t3_30_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_30_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_30_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_30_45 x F := by
  rcases cert_cellA2_t3_30_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_34_45 (Sym.sym24 F))

def SymWallE_cellA2_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_34_45 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_34_45 x F := by
  rcases cert_cellA2_t3_34_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_35_40 (Sym.sym24 F))

def SymWallE_cellA2_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_35_40 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_35_40 x F := by
  rcases cert_cellA2_t3_35_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_35_43 (Sym.sym24 F))

def SymWallE_cellA2_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_35_43 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_35_43 x F := by
  rcases cert_cellA2_t3_35_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_40_53 (Sym.sym24 F))

def SymWallE_cellA2_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_40_53 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_40_53 x F := by
  rcases cert_cellA2_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_43_50 (Sym.sym24 F))

def SymWallE_cellA2_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_43_50 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_43_50 x F := by
  rcases cert_cellA2_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_45_50 (Sym.sym24 F))

def SymWallE_cellA2_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_45_50 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_45_50 x F := by
  rcases cert_cellA2_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t3_45_53 (Sym.sym24 F))

def SymWallE_cellA2_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t3_45_53 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t3_45_53 x F := by
  rcases cert_cellA2_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t5_12_61 (Sym.sym24 F))

def SymWallE_cellA2_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t5_12_61 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t5_12_61 x F := by
  rcases cert_cellA2_t5_12_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t5_16_62 (Sym.sym24 F))

def SymWallE_cellA2_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t5_16_62 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t5_16_62 x F := by
  rcases cert_cellA2_t5_16_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t6_32_53 (Sym.sym24 F))

def SymWallE_cellA2_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t6_32_53 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t6_32_53 x F := by
  rcases cert_cellA2_t6_32_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t6_35_52 (Sym.sym24 F))

def SymWallE_cellA2_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t6_35_52 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t6_35_52 x F := by
  rcases cert_cellA2_t6_35_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t7_32_63 (Sym.sym24 F))

def SymWallE_cellA2_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t7_32_63 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t7_32_63 x F := by
  rcases cert_cellA2_t7_32_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t7_36_62 (Sym.sym24 F))

def SymWallE_cellA2_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t7_36_62 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t7_36_62 x F := by
  rcases cert_cellA2_t7_36_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t8_36_43 (Sym.sym24 F))

def SymWallE_cellA2_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t8_36_43 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t8_36_43 x F := by
  rcases cert_cellA2_t8_36_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA2 :=
  unsymCellWall F cellA2 (wall_cellA2_t8_46_63 (Sym.sym24 F))

def SymWallE_cellA2_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA2 (symWall_cellA2_t8_46_63 F) (cellRimScalar cellA2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellA2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA2_t8_46_63 x F := by
  rcases cert_cellA2_t8_46_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t0_01_12 (Sym.sym24 F))

def SymWallE_cellB2_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t0_01_12 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t0_01_12 x F := by
  rcases cert_cellB2_t0_01_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t0_02_10 (Sym.sym24 F))

def SymWallE_cellB2_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t0_02_10 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t0_02_10 x F := by
  rcases cert_cellB2_t0_02_10 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t1_01_60 (Sym.sym24 F))

def SymWallE_cellB2_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t1_01_60 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t1_01_60 x F := by
  rcases cert_cellB2_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t1_06_61 (Sym.sym24 F))

def SymWallE_cellB2_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t1_06_61 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t1_06_61 x F := by
  rcases cert_cellB2_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t2_02_50 (Sym.sym24 F))

def SymWallE_cellB2_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t2_02_50 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t2_02_50 x F := by
  rcases cert_cellB2_t2_02_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t2_05_52 (Sym.sym24 F))

def SymWallE_cellB2_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t2_05_52 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t2_05_52 x F := by
  rcases cert_cellB2_t2_05_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_03_34 (Sym.sym24 F))

def SymWallE_cellB2_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_03_34 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_03_34 x F := by
  rcases cert_cellB2_t3_03_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_03_35 (Sym.sym24 F))

def SymWallE_cellB2_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_03_35 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_03_35 x F := by
  rcases cert_cellB2_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_03_40 (Sym.sym24 F))

def SymWallE_cellB2_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_03_40 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_03_40 x F := by
  rcases cert_cellB2_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_03_45 (Sym.sym24 F))

def SymWallE_cellB2_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_03_45 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_03_45 x F := by
  rcases cert_cellB2_t3_03_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_04_35 (Sym.sym24 F))

def SymWallE_cellB2_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_04_35 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_04_35 x F := by
  rcases cert_cellB2_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_04_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_04_43 (Sym.sym24 F))

def SymWallE_cellB2_t3_04_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_04_43 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_04_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_04_43 x F := by
  rcases cert_cellB2_t3_04_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_04_45 (Sym.sym24 F))

def SymWallE_cellB2_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_04_45 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_04_45 x F := by
  rcases cert_cellB2_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_05_30 (Sym.sym24 F))

def SymWallE_cellB2_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_05_30 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_05_30 x F := by
  rcases cert_cellB2_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_05_34 (Sym.sym24 F))

def SymWallE_cellB2_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_05_34 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_05_34 x F := by
  rcases cert_cellB2_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_05_40 (Sym.sym24 F))

def SymWallE_cellB2_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_05_40 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_05_40 x F := by
  rcases cert_cellB2_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_05_43 (Sym.sym24 F))

def SymWallE_cellB2_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_05_43 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_05_43 x F := by
  rcases cert_cellB2_t3_05_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_40_53 (Sym.sym24 F))

def SymWallE_cellB2_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_40_53 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_40_53 x F := by
  rcases cert_cellB2_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_43_50 (Sym.sym24 F))

def SymWallE_cellB2_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_43_50 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_43_50 x F := by
  rcases cert_cellB2_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_43_54 (Sym.sym24 F))

def SymWallE_cellB2_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_43_54 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_43_54 x F := by
  rcases cert_cellB2_t3_43_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_45_50 (Sym.sym24 F))

def SymWallE_cellB2_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_45_50 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_45_50 x F := by
  rcases cert_cellB2_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t3_45_53 (Sym.sym24 F))

def SymWallE_cellB2_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t3_45_53 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t3_45_53 x F := by
  rcases cert_cellB2_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t4_04_46 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t4_04_46 (Sym.sym24 F))

def SymWallE_cellB2_t4_04_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t4_04_46 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t4_04_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t4_04_46 x F := by
  rcases cert_cellB2_t4_04_46 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t4_06_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t4_06_64 (Sym.sym24 F))

def SymWallE_cellB2_t4_06_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t4_06_64 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t4_06_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t4_06_64 x F := by
  rcases cert_cellB2_t4_06_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t5_12_61 (Sym.sym24 F))

def SymWallE_cellB2_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t5_12_61 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t5_12_61 x F := by
  rcases cert_cellB2_t5_12_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t5_16_62 (Sym.sym24 F))

def SymWallE_cellB2_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t5_16_62 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t5_16_62 x F := by
  rcases cert_cellB2_t5_16_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t6_32_53 (Sym.sym24 F))

def SymWallE_cellB2_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t6_32_53 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t6_32_53 x F := by
  rcases cert_cellB2_t6_32_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t6_35_52 (Sym.sym24 F))

def SymWallE_cellB2_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t6_35_52 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t6_35_52 x F := by
  rcases cert_cellB2_t6_35_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t8_36_43 (Sym.sym24 F))

def SymWallE_cellB2_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t8_36_43 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t8_36_43 x F := by
  rcases cert_cellB2_t8_36_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellB2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellB2 :=
  unsymCellWall F cellB2 (wall_cellB2_t8_46_63 (Sym.sym24 F))

def SymWallE_cellB2_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellB2 (symWall_cellB2_t8_46_63 F) (cellRimScalar cellB2 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cellB2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellB2_t8_46_63 x F := by
  rcases cert_cellB2_t8_46_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t0_10_21 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t0_10_21 (Sym.sym24 F))

def SymWallE_cellA0_t0_10_21 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t0_10_21 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t0_10_21 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t0_10_21 x F := by
  rcases cert_cellA0_t0_10_21 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t0_12_20 (Sym.sym24 F))

def SymWallE_cellA0_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t0_12_20 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t0_12_20 x F := by
  rcases cert_cellA0_t0_12_20 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t1_10_61 (Sym.sym24 F))

def SymWallE_cellA0_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t1_10_61 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t1_10_61 x F := by
  rcases cert_cellA0_t1_10_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t1_16_60 (Sym.sym24 F))

def SymWallE_cellA0_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t1_16_60 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t1_16_60 x F := by
  rcases cert_cellA0_t1_16_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t2_20_52 (Sym.sym24 F))

def SymWallE_cellA0_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t2_20_52 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t2_20_52 x F := by
  rcases cert_cellA0_t2_20_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t2_25_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t2_25_50 (Sym.sym24 F))

def SymWallE_cellA0_t2_25_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t2_25_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t2_25_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t2_25_50 x F := by
  rcases cert_cellA0_t2_25_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_03_34 (Sym.sym24 F))

def SymWallE_cellA0_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_03_34 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_03_34 x F := by
  rcases cert_cellA0_t3_03_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_04_30 (Sym.sym24 F))

def SymWallE_cellA0_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_04_30 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_04_30 x F := by
  rcases cert_cellA0_t3_04_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_04_35 (Sym.sym24 F))

def SymWallE_cellA0_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_04_35 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_04_35 x F := by
  rcases cert_cellA0_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_05_30 (Sym.sym24 F))

def SymWallE_cellA0_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_05_30 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_05_30 x F := by
  rcases cert_cellA0_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_05_34 (Sym.sym24 F))

def SymWallE_cellA0_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_05_34 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_05_34 x F := by
  rcases cert_cellA0_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_30_53 (Sym.sym24 F))

def SymWallE_cellA0_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_30_53 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_30_53 x F := by
  rcases cert_cellA0_t3_30_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_30_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_30_54 (Sym.sym24 F))

def SymWallE_cellA0_t3_30_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_30_54 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_30_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_30_54 x F := by
  rcases cert_cellA0_t3_30_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_34_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_34_50 (Sym.sym24 F))

def SymWallE_cellA0_t3_34_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_34_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_34_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_34_50 x F := by
  rcases cert_cellA0_t3_34_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_34_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_34_53 (Sym.sym24 F))

def SymWallE_cellA0_t3_34_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_34_53 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_34_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_34_53 x F := by
  rcases cert_cellA0_t3_34_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_35_50 (Sym.sym24 F))

def SymWallE_cellA0_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_35_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_35_50 x F := by
  rcases cert_cellA0_t3_35_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_35_54 (Sym.sym24 F))

def SymWallE_cellA0_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_35_54 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_35_54 x F := by
  rcases cert_cellA0_t3_35_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_40_53 (Sym.sym24 F))

def SymWallE_cellA0_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_40_53 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_40_53 x F := by
  rcases cert_cellA0_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_40_54 (Sym.sym24 F))

def SymWallE_cellA0_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_40_54 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_40_54 x F := by
  rcases cert_cellA0_t3_40_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_43_50 (Sym.sym24 F))

def SymWallE_cellA0_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_43_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_43_50 x F := by
  rcases cert_cellA0_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_43_54 (Sym.sym24 F))

def SymWallE_cellA0_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_43_54 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_43_54 x F := by
  rcases cert_cellA0_t3_43_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t3_45_50 (Sym.sym24 F))

def SymWallE_cellA0_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t3_45_50 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t3_45_50 x F := by
  rcases cert_cellA0_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t5_21_62 (Sym.sym24 F))

def SymWallE_cellA0_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t5_21_62 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t5_21_62 x F := by
  rcases cert_cellA0_t5_21_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t5_26_61 (Sym.sym24 F))

def SymWallE_cellA0_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t5_26_61 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t5_26_61 x F := by
  rcases cert_cellA0_t5_26_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t6_23_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t6_23_35 (Sym.sym24 F))

def SymWallE_cellA0_t6_23_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t6_23_35 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t6_23_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t6_23_35 x F := by
  rcases cert_cellA0_t6_23_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t6_25_32 (Sym.sym24 F))

def SymWallE_cellA0_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t6_25_32 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t6_25_32 x F := by
  rcases cert_cellA0_t6_25_32 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t7_23_36 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t7_23_36 (Sym.sym24 F))

def SymWallE_cellA0_t7_23_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t7_23_36 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t7_23_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t7_23_36 x F := by
  rcases cert_cellA0_t7_23_36 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t7_26_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t7_26_63 (Sym.sym24 F))

def SymWallE_cellA0_t7_26_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t7_26_63 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t7_26_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t7_26_63 x F := by
  rcases cert_cellA0_t7_26_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t8_34_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t8_34_63 (Sym.sym24 F))

def SymWallE_cellA0_t8_34_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t8_34_63 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t8_34_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t8_34_63 x F := by
  rcases cert_cellA0_t8_34_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellA0_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellA0 :=
  unsymCellWall F cellA0 (wall_cellA0_t8_36_64 (Sym.sym24 F))

def SymWallE_cellA0_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellA0 (symWall_cellA0_t8_36_64 F) (cellRimScalar cellA0 0 4 5 0 (x ∘ Sym.pi24))

theorem symCert_cellA0_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellA0_t8_36_64 x F := by
  rcases cert_cellA0_t8_36_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t1_01_60 (Sym.sym24 F))

def SymWallE_cellCp_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t1_01_60 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t1_01_60 x F := by
  rcases cert_cellCp_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t1_06_61 (Sym.sym24 F))

def SymWallE_cellCp_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t1_06_61 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t1_06_61 x F := by
  rcases cert_cellCp_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t2_02_50 (Sym.sym24 F))

def SymWallE_cellCp_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t2_02_50 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t2_02_50 x F := by
  rcases cert_cellCp_t2_02_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t2_20_52 (Sym.sym24 F))

def SymWallE_cellCp_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t2_20_52 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t2_20_52 x F := by
  rcases cert_cellCp_t2_20_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t2_50_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t2_50_52 (Sym.sym24 F))

def SymWallE_cellCp_t2_50_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t2_50_52 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t2_50_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t2_50_52 x F := by
  rcases cert_cellCp_t2_50_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_03_40 (Sym.sym24 F))

def SymWallE_cellCp_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_03_40 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_03_40 x F := by
  rcases cert_cellCp_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_04_35 (Sym.sym24 F))

def SymWallE_cellCp_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_04_35 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_04_35 x F := by
  rcases cert_cellCp_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_04_45 (Sym.sym24 F))

def SymWallE_cellCp_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_04_45 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_04_45 x F := by
  rcases cert_cellCp_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_05_30 (Sym.sym24 F))

def SymWallE_cellCp_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_05_30 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_05_30 x F := by
  rcases cert_cellCp_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_05_34 (Sym.sym24 F))

def SymWallE_cellCp_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_05_34 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_05_34 x F := by
  rcases cert_cellCp_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_05_40 (Sym.sym24 F))

def SymWallE_cellCp_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_05_40 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_05_40 x F := by
  rcases cert_cellCp_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_30_43 (Sym.sym24 F))

def SymWallE_cellCp_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_30_43 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_30_43 x F := by
  rcases cert_cellCp_t3_30_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_30_45 (Sym.sym24 F))

def SymWallE_cellCp_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_30_45 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_30_45 x F := by
  rcases cert_cellCp_t3_30_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_30_53 (Sym.sym24 F))

def SymWallE_cellCp_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_30_53 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_30_53 x F := by
  rcases cert_cellCp_t3_30_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_34_45 (Sym.sym24 F))

def SymWallE_cellCp_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_34_45 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_34_45 x F := by
  rcases cert_cellCp_t3_34_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_35_40 (Sym.sym24 F))

def SymWallE_cellCp_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_35_40 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_35_40 x F := by
  rcases cert_cellCp_t3_35_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_35_50 (Sym.sym24 F))

def SymWallE_cellCp_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_35_50 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_35_50 x F := by
  rcases cert_cellCp_t3_35_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_35_54 (Sym.sym24 F))

def SymWallE_cellCp_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_35_54 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_35_54 x F := by
  rcases cert_cellCp_t3_35_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_40_53 (Sym.sym24 F))

def SymWallE_cellCp_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_40_53 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_40_53 x F := by
  rcases cert_cellCp_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_43_50 (Sym.sym24 F))

def SymWallE_cellCp_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_43_50 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_43_50 x F := by
  rcases cert_cellCp_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t3_45_50 (Sym.sym24 F))

def SymWallE_cellCp_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t3_45_50 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t3_45_50 x F := by
  rcases cert_cellCp_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t4_06_40 (Sym.sym24 F))

def SymWallE_cellCp_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t4_06_40 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t4_06_40 x F := by
  rcases cert_cellCp_t4_06_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t4_46_60 (Sym.sym24 F))

def SymWallE_cellCp_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t4_46_60 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t4_46_60 x F := by
  rcases cert_cellCp_t4_46_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t5_21_62 (Sym.sym24 F))

def SymWallE_cellCp_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t5_21_62 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t5_21_62 x F := by
  rcases cert_cellCp_t5_21_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t5_26_61 (Sym.sym24 F))

def SymWallE_cellCp_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t5_26_61 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t5_26_61 x F := by
  rcases cert_cellCp_t5_26_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t6_25_32 (Sym.sym24 F))

def SymWallE_cellCp_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t6_25_32 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t6_25_32 x F := by
  rcases cert_cellCp_t6_25_32 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t6_35_52 (Sym.sym24 F))

def SymWallE_cellCp_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t6_35_52 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t6_35_52 x F := by
  rcases cert_cellCp_t6_35_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t7_26_32 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t7_26_32 (Sym.sym24 F))

def SymWallE_cellCp_t7_26_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t7_26_32 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t7_26_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t7_26_32 x F := by
  rcases cert_cellCp_t7_26_32 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cellCp_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cellCp :=
  unsymCellWall F cellC' (wall_cellCp_t7_36_62 (Sym.sym24 F))

def SymWallE_cellCp_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cellCp (symWall_cellCp_t7_36_62 F) (cellRimScalar cellC' 0 2 2 1 (x ∘ Sym.pi24))

theorem symCert_cellCp_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cellCp_t7_36_62 x F := by
  rcases cert_cellCp_t7_36_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t1_01_60 (Sym.sym24 F))

def SymWallE_cell0536_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t1_01_60 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t1_01_60 x F := by
  rcases cert_cell0536_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t1_06_61 (Sym.sym24 F))

def SymWallE_cell0536_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t1_06_61 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t1_06_61 x F := by
  rcases cert_cell0536_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t2_02_50 (Sym.sym24 F))

def SymWallE_cell0536_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t2_02_50 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t2_02_50 x F := by
  rcases cert_cell0536_t2_02_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t2_05_52 (Sym.sym24 F))

def SymWallE_cell0536_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t2_05_52 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t2_05_52 x F := by
  rcases cert_cell0536_t2_05_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_03_35 (Sym.sym24 F))

def SymWallE_cell0536_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_03_35 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_03_35 x F := by
  rcases cert_cell0536_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_03_40 (Sym.sym24 F))

def SymWallE_cell0536_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_03_40 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_03_40 x F := by
  rcases cert_cell0536_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_03_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_03_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_03_45 x F := by
  rcases cert_cell0536_t3_03_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_04_35 (Sym.sym24 F))

def SymWallE_cell0536_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_04_35 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_04_35 x F := by
  rcases cert_cell0536_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_04_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_04_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_04_45 x F := by
  rcases cert_cell0536_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_05_30 (Sym.sym24 F))

def SymWallE_cell0536_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_05_30 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_05_30 x F := by
  rcases cert_cell0536_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_05_34 (Sym.sym24 F))

def SymWallE_cell0536_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_05_34 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_05_34 x F := by
  rcases cert_cell0536_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_05_40 (Sym.sym24 F))

def SymWallE_cell0536_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_05_40 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_05_40 x F := by
  rcases cert_cell0536_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_05_43 (Sym.sym24 F))

def SymWallE_cell0536_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_05_43 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_05_43 x F := by
  rcases cert_cell0536_t3_05_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_30_43 (Sym.sym24 F))

def SymWallE_cell0536_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_30_43 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_30_43 x F := by
  rcases cert_cell0536_t3_30_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_30_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_30_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_30_45 x F := by
  rcases cert_cell0536_t3_30_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_34_45 (Sym.sym24 F))

def SymWallE_cell0536_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_34_45 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_34_45 x F := by
  rcases cert_cell0536_t3_34_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_35_40 (Sym.sym24 F))

def SymWallE_cell0536_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_35_40 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_35_40 x F := by
  rcases cert_cell0536_t3_35_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_35_43 (Sym.sym24 F))

def SymWallE_cell0536_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_35_43 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_35_43 x F := by
  rcases cert_cell0536_t3_35_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_40_53 (Sym.sym24 F))

def SymWallE_cell0536_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_40_53 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_40_53 x F := by
  rcases cert_cell0536_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_43_50 (Sym.sym24 F))

def SymWallE_cell0536_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_43_50 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_43_50 x F := by
  rcases cert_cell0536_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_45_50 (Sym.sym24 F))

def SymWallE_cell0536_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_45_50 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_45_50 x F := by
  rcases cert_cell0536_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t3_45_53 (Sym.sym24 F))

def SymWallE_cell0536_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t3_45_53 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t3_45_53 x F := by
  rcases cert_cell0536_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t4_06_40 (Sym.sym24 F))

def SymWallE_cell0536_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t4_06_40 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t4_06_40 x F := by
  rcases cert_cell0536_t4_06_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t4_46_60 (Sym.sym24 F))

def SymWallE_cell0536_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t4_46_60 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t4_46_60 x F := by
  rcases cert_cell0536_t4_46_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t6_32_53 (Sym.sym24 F))

def SymWallE_cell0536_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t6_32_53 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t6_32_53 x F := by
  rcases cert_cell0536_t6_32_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t6_35_52 (Sym.sym24 F))

def SymWallE_cell0536_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t6_35_52 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t6_35_52 x F := by
  rcases cert_cell0536_t6_35_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t7_32_63 (Sym.sym24 F))

def SymWallE_cell0536_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t7_32_63 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t7_32_63 x F := by
  rcases cert_cell0536_t7_32_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t7_36_62 (Sym.sym24 F))

def SymWallE_cell0536_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t7_36_62 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t7_36_62 x F := by
  rcases cert_cell0536_t7_36_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t8_36_43 (Sym.sym24 F))

def SymWallE_cell0536_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t8_36_43 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t8_36_43 x F := by
  rcases cert_cell0536_t8_36_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0536_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0536 :=
  unsymCellWall F cell0536 (wall_cell0536_t8_46_63 (Sym.sym24 F))

def SymWallE_cell0536_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0536 (symWall_cell0536_t8_46_63 F) (cellRimScalar cell0536 2 0 3 1 (x ∘ Sym.pi24))

theorem symCert_cell0536_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0536_t8_46_63 x F := by
  rcases cert_cell0536_t8_46_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t0_01_12 (Sym.sym24 F))

def SymWallE_cell0164_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t0_01_12 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t0_01_12 x F := by
  rcases cert_cell0164_t0_01_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t0_02_10 (Sym.sym24 F))

def SymWallE_cell0164_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t0_02_10 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t0_02_10 x F := by
  rcases cert_cell0164_t0_02_10 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t1_01_60 (Sym.sym24 F))

def SymWallE_cell0164_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t1_01_60 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t1_01_60 x F := by
  rcases cert_cell0164_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t1_06_61 (Sym.sym24 F))

def SymWallE_cell0164_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t1_06_61 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t1_06_61 x F := by
  rcases cert_cell0164_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_03_34 (Sym.sym24 F))

def SymWallE_cell0164_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_03_34 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_03_34 x F := by
  rcases cert_cell0164_t3_03_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_03_35 (Sym.sym24 F))

def SymWallE_cell0164_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_03_35 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_03_35 x F := by
  rcases cert_cell0164_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_03_40 (Sym.sym24 F))

def SymWallE_cell0164_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_03_40 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_03_40 x F := by
  rcases cert_cell0164_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_03_45 (Sym.sym24 F))

def SymWallE_cell0164_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_03_45 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_03_45 x F := by
  rcases cert_cell0164_t3_03_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_04_35 (Sym.sym24 F))

def SymWallE_cell0164_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_04_35 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_04_35 x F := by
  rcases cert_cell0164_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_04_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_04_43 (Sym.sym24 F))

def SymWallE_cell0164_t3_04_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_04_43 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_04_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_04_43 x F := by
  rcases cert_cell0164_t3_04_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_04_45 (Sym.sym24 F))

def SymWallE_cell0164_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_04_45 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_04_45 x F := by
  rcases cert_cell0164_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_05_30 (Sym.sym24 F))

def SymWallE_cell0164_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_05_30 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_05_30 x F := by
  rcases cert_cell0164_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_05_34 (Sym.sym24 F))

def SymWallE_cell0164_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_05_34 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_05_34 x F := by
  rcases cert_cell0164_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_05_40 (Sym.sym24 F))

def SymWallE_cell0164_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_05_40 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_05_40 x F := by
  rcases cert_cell0164_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_05_43 (Sym.sym24 F))

def SymWallE_cell0164_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_05_43 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_05_43 x F := by
  rcases cert_cell0164_t3_05_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_40_53 (Sym.sym24 F))

def SymWallE_cell0164_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_40_53 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_40_53 x F := by
  rcases cert_cell0164_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_43_50 (Sym.sym24 F))

def SymWallE_cell0164_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_43_50 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_43_50 x F := by
  rcases cert_cell0164_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_43_54 (Sym.sym24 F))

def SymWallE_cell0164_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_43_54 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_43_54 x F := by
  rcases cert_cell0164_t3_43_54 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_45_50 (Sym.sym24 F))

def SymWallE_cell0164_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_45_50 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_45_50 x F := by
  rcases cert_cell0164_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t3_45_53 (Sym.sym24 F))

def SymWallE_cell0164_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t3_45_53 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t3_45_53 x F := by
  rcases cert_cell0164_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t4_04_60 (Sym.sym24 F))

def SymWallE_cell0164_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t4_04_60 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t4_04_60 x F := by
  rcases cert_cell0164_t4_04_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t4_04_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t4_04_64 (Sym.sym24 F))

def SymWallE_cell0164_t4_04_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t4_04_64 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t4_04_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t4_04_64 x F := by
  rcases cert_cell0164_t4_04_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t4_06_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t4_06_64 (Sym.sym24 F))

def SymWallE_cell0164_t4_06_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t4_06_64 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t4_06_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t4_06_64 x F := by
  rcases cert_cell0164_t4_06_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t5_12_61 (Sym.sym24 F))

def SymWallE_cell0164_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t5_12_61 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t5_12_61 x F := by
  rcases cert_cell0164_t5_12_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t5_16_62 (Sym.sym24 F))

def SymWallE_cell0164_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t5_16_62 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t5_16_62 x F := by
  rcases cert_cell0164_t5_16_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t8_43_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t8_43_64 (Sym.sym24 F))

def SymWallE_cell0164_t8_43_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t8_43_64 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t8_43_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t8_43_64 x F := by
  rcases cert_cell0164_t8_43_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell0164_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell0164 :=
  unsymCellWall F cell0164 (wall_cell0164_t8_46_63 (Sym.sym24 F))

def SymWallE_cell0164_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell0164 (symWall_cell0164_t8_46_63 F) (cellRimScalar cell0164 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell0164_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell0164_t8_46_63 x F := by
  rcases cert_cell0164_t8_46_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t0_01_12 (Sym.sym24 F))

def SymWallE_cell01634_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t0_01_12 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t0_01_12 x F := by
  rcases cert_cell01634_t0_01_12 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t0_02_10 (Sym.sym24 F))

def SymWallE_cell01634_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t0_02_10 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t0_02_10 x F := by
  rcases cert_cell01634_t0_02_10 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t1_01_60 (Sym.sym24 F))

def SymWallE_cell01634_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t1_01_60 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t1_01_60 x F := by
  rcases cert_cell01634_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t1_06_61 (Sym.sym24 F))

def SymWallE_cell01634_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t1_06_61 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t1_06_61 x F := by
  rcases cert_cell01634_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_03_35 (Sym.sym24 F))

def SymWallE_cell01634_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_03_35 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_03_35 x F := by
  rcases cert_cell01634_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_03_40 (Sym.sym24 F))

def SymWallE_cell01634_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_03_40 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_03_40 x F := by
  rcases cert_cell01634_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_03_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_03_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_03_45 x F := by
  rcases cert_cell01634_t3_03_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_04_35 (Sym.sym24 F))

def SymWallE_cell01634_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_04_35 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_04_35 x F := by
  rcases cert_cell01634_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_04_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_04_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_04_45 x F := by
  rcases cert_cell01634_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_05_30 (Sym.sym24 F))

def SymWallE_cell01634_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_05_30 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_05_30 x F := by
  rcases cert_cell01634_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_05_34 (Sym.sym24 F))

def SymWallE_cell01634_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_05_34 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_05_34 x F := by
  rcases cert_cell01634_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_05_40 (Sym.sym24 F))

def SymWallE_cell01634_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_05_40 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_05_40 x F := by
  rcases cert_cell01634_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_05_43 (Sym.sym24 F))

def SymWallE_cell01634_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_05_43 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_05_43 x F := by
  rcases cert_cell01634_t3_05_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_30_43 (Sym.sym24 F))

def SymWallE_cell01634_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_30_43 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_30_43 x F := by
  rcases cert_cell01634_t3_30_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_30_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_30_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_30_45 x F := by
  rcases cert_cell01634_t3_30_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_34_45 (Sym.sym24 F))

def SymWallE_cell01634_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_34_45 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_34_45 x F := by
  rcases cert_cell01634_t3_34_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_35_40 (Sym.sym24 F))

def SymWallE_cell01634_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_35_40 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_35_40 x F := by
  rcases cert_cell01634_t3_35_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_35_43 (Sym.sym24 F))

def SymWallE_cell01634_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_35_43 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_35_43 x F := by
  rcases cert_cell01634_t3_35_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_40_53 (Sym.sym24 F))

def SymWallE_cell01634_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_40_53 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_40_53 x F := by
  rcases cert_cell01634_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_43_50 (Sym.sym24 F))

def SymWallE_cell01634_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_43_50 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_43_50 x F := by
  rcases cert_cell01634_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_45_50 (Sym.sym24 F))

def SymWallE_cell01634_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_45_50 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_45_50 x F := by
  rcases cert_cell01634_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t3_45_53 (Sym.sym24 F))

def SymWallE_cell01634_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t3_45_53 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t3_45_53 x F := by
  rcases cert_cell01634_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t4_04_60 (Sym.sym24 F))

def SymWallE_cell01634_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t4_04_60 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t4_04_60 x F := by
  rcases cert_cell01634_t4_04_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t4_40_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t4_40_64 (Sym.sym24 F))

def SymWallE_cell01634_t4_40_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t4_40_64 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t4_40_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t4_40_64 x F := by
  rcases cert_cell01634_t4_40_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t5_12_61 (Sym.sym24 F))

def SymWallE_cell01634_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t5_12_61 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t5_12_61 x F := by
  rcases cert_cell01634_t5_12_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t5_16_62 (Sym.sym24 F))

def SymWallE_cell01634_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t5_16_62 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t5_16_62 x F := by
  rcases cert_cell01634_t5_16_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t7_32_63 (Sym.sym24 F))

def SymWallE_cell01634_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t7_32_63 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t7_32_63 x F := by
  rcases cert_cell01634_t7_32_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t7_36_62 (Sym.sym24 F))

def SymWallE_cell01634_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t7_36_62 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t7_36_62 x F := by
  rcases cert_cell01634_t7_36_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t8_43_64 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t8_43_64 (Sym.sym24 F))

def SymWallE_cell01634_t8_43_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t8_43_64 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t8_43_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t8_43_64 x F := by
  rcases cert_cell01634_t8_43_64 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell01634_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell01634 :=
  unsymCellWall F cell01634 (wall_cell01634_t8_46_63 (Sym.sym24 F))

def SymWallE_cell01634_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell01634 (symWall_cell01634_t8_46_63 F) (cellRimScalar cell01634 0 2 1 2 (x ∘ Sym.pi24))

theorem symCert_cell01634_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell01634_t8_46_63 x F := by
  rcases cert_cell01634_t8_46_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t1_01_60 (Sym.sym24 F))

def SymWallE_cell05326_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t1_01_60 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t1_01_60 x F := by
  rcases cert_cell05326_t1_01_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t1_06_61 (Sym.sym24 F))

def SymWallE_cell05326_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t1_06_61 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t1_06_61 x F := by
  rcases cert_cell05326_t1_06_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t2_02_50 (Sym.sym24 F))

def SymWallE_cell05326_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t2_02_50 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t2_02_50 x F := by
  rcases cert_cell05326_t2_02_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t2_05_52 (Sym.sym24 F))

def SymWallE_cell05326_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t2_05_52 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t2_05_52 x F := by
  rcases cert_cell05326_t2_05_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_03_35 (Sym.sym24 F))

def SymWallE_cell05326_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_03_35 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_03_35 x F := by
  rcases cert_cell05326_t3_03_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_03_40 (Sym.sym24 F))

def SymWallE_cell05326_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_03_40 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_03_40 x F := by
  rcases cert_cell05326_t3_03_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_03_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_03_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_03_45 x F := by
  rcases cert_cell05326_t3_03_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_04_35 (Sym.sym24 F))

def SymWallE_cell05326_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_04_35 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_04_35 x F := by
  rcases cert_cell05326_t3_04_35 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_04_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_04_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_04_45 x F := by
  rcases cert_cell05326_t3_04_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_05_30 (Sym.sym24 F))

def SymWallE_cell05326_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_05_30 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_05_30 x F := by
  rcases cert_cell05326_t3_05_30 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_05_34 (Sym.sym24 F))

def SymWallE_cell05326_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_05_34 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_05_34 x F := by
  rcases cert_cell05326_t3_05_34 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_05_40 (Sym.sym24 F))

def SymWallE_cell05326_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_05_40 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_05_40 x F := by
  rcases cert_cell05326_t3_05_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_05_43 (Sym.sym24 F))

def SymWallE_cell05326_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_05_43 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_05_43 x F := by
  rcases cert_cell05326_t3_05_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_05_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_05_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_05_45 x F := by
  rcases cert_cell05326_t3_05_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_30_43 (Sym.sym24 F))

def SymWallE_cell05326_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_30_43 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_30_43 x F := by
  rcases cert_cell05326_t3_30_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_30_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_30_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_30_45 x F := by
  rcases cert_cell05326_t3_30_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_34_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_34_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_34_45 x F := by
  rcases cert_cell05326_t3_34_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_35_40 (Sym.sym24 F))

def SymWallE_cell05326_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_35_40 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_35_40 x F := by
  rcases cert_cell05326_t3_35_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_35_43 (Sym.sym24 F))

def SymWallE_cell05326_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_35_43 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_35_43 x F := by
  rcases cert_cell05326_t3_35_43 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_40_53 (Sym.sym24 F))

def SymWallE_cell05326_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_40_53 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_40_53 x F := by
  rcases cert_cell05326_t3_40_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_43_45 (Sym.sym24 F))

def SymWallE_cell05326_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_43_45 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_43_45 x F := by
  rcases cert_cell05326_t3_43_45 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_43_50 (Sym.sym24 F))

def SymWallE_cell05326_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_43_50 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_43_50 x F := by
  rcases cert_cell05326_t3_43_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_45_50 (Sym.sym24 F))

def SymWallE_cell05326_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_45_50 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_45_50 x F := by
  rcases cert_cell05326_t3_45_50 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t3_45_53 (Sym.sym24 F))

def SymWallE_cell05326_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t3_45_53 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t3_45_53 x F := by
  rcases cert_cell05326_t3_45_53 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t4_06_40 (Sym.sym24 F))

def SymWallE_cell05326_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t4_06_40 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t4_06_40 x F := by
  rcases cert_cell05326_t4_06_40 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t4_46_60 (Sym.sym24 F))

def SymWallE_cell05326_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t4_46_60 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t4_46_60 x F := by
  rcases cert_cell05326_t4_46_60 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t5_21_62 (Sym.sym24 F))

def SymWallE_cell05326_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t5_21_62 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t5_21_62 x F := by
  rcases cert_cell05326_t5_21_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t5_26_61 (Sym.sym24 F))

def SymWallE_cell05326_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t5_26_61 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t5_26_61 x F := by
  rcases cert_cell05326_t5_26_61 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t6_25_32 (Sym.sym24 F))

def SymWallE_cell05326_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t6_25_32 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t6_25_32 x F := by
  rcases cert_cell05326_t6_25_32 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t6_35_52 (Sym.sym24 F))

def SymWallE_cell05326_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t6_35_52 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t6_35_52 x F := by
  rcases cert_cell05326_t6_35_52 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t7_32_63 (Sym.sym24 F))

def SymWallE_cell05326_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t7_32_63 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t7_32_63 x F := by
  rcases cert_cell05326_t7_32_63 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

noncomputable def symWall_cell05326_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F sym_cell05326 :=
  unsymCellWall F cell05326 (wall_cell05326_t7_36_62 (Sym.sym24 F))

def SymWallE_cell05326_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F sym_cell05326 (symWall_cell05326_t7_36_62 F) (cellRimScalar cell05326 0 2 3 1 (x ∘ Sym.pi24))

theorem symCert_cell05326_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ SymWallE_cell05326_t7_36_62 x F := by
  rcases cert_cell05326_t7_36_62 (Sym.sym24 F) with hL | hS | hE
  · exact Or.inl (Sym.lexAny_sym F hL)
  · exact Or.inr (Or.inl (Sym.splitAny24_sym F hS))
  · exact Or.inr (Or.inr hE)

/-! ### Per-cell mirror conjunctions (429 walls across the 11 non-self-dual cells) -/

def SymAllWallE2_cellC (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cellC_t1_01_61 x F ∧
  SymWallE_cellC_t2_50_52 x F ∧
  SymWallE_cellC_t4_40_46 x F ∧
  SymWallE_cellC_t6_32_52 x F ∧
  SymWallE_cellC_t7_32_36 x F ∧
  SymWallE_cellC_t8_43_46 x F ∧
  SymWallE_cellC_t1_01_60 x F ∧
  SymWallE_cellC_t1_06_61 x F ∧
  SymWallE_cellC_t2_02_50 x F ∧
  SymWallE_cellC_t2_20_52 x F ∧
  SymWallE_cellC_t3_03_40 x F ∧
  SymWallE_cellC_t3_04_35 x F ∧
  SymWallE_cellC_t3_04_45 x F ∧
  SymWallE_cellC_t3_05_30 x F ∧
  SymWallE_cellC_t3_05_34 x F ∧
  SymWallE_cellC_t3_05_40 x F ∧
  SymWallE_cellC_t3_30_43 x F ∧
  SymWallE_cellC_t3_30_45 x F ∧
  SymWallE_cellC_t3_30_53 x F ∧
  SymWallE_cellC_t3_34_45 x F ∧
  SymWallE_cellC_t3_35_40 x F ∧
  SymWallE_cellC_t3_35_50 x F ∧
  SymWallE_cellC_t3_35_54 x F ∧
  SymWallE_cellC_t3_40_43 x F ∧
  SymWallE_cellC_t3_40_45 x F ∧
  SymWallE_cellC_t3_40_53 x F ∧
  SymWallE_cellC_t3_43_50 x F ∧
  SymWallE_cellC_t3_45_50 x F ∧
  SymWallE_cellC_t4_06_40 x F ∧
  SymWallE_cellC_t4_46_60 x F ∧
  SymWallE_cellC_t6_32_53 x F ∧
  SymWallE_cellC_t6_35_52 x F ∧
  SymWallE_cellC_t7_26_32 x F ∧
  SymWallE_cellC_t7_36_62 x F ∧
  SymWallE_cellC_t8_36_43 x F ∧
  SymWallE_cellC_t8_46_63 x F

private lemma holeLeaf_symAllWallE2_cellC {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cellC x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cellC_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t2_50_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t4_40_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t6_32_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t7_32_36 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t8_43_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t2_02_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t2_20_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_30_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_30_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_30_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_34_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_35_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_35_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_35_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_40_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_40_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t4_06_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t4_46_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t6_32_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t6_35_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t7_26_32 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t7_36_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t8_36_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellC_t8_46_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cellD (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cellD_t0_10_12 x F ∧
  SymWallE_cellD_t1_10_60 x F ∧
  SymWallE_cellD_t4_04_64 x F ∧
  SymWallE_cellD_t6_25_35 x F ∧
  SymWallE_cellD_t8_34_64 x F ∧
  SymWallE_cellD_t0_02_10 x F ∧
  SymWallE_cellD_t0_12_20 x F ∧
  SymWallE_cellD_t1_10_61 x F ∧
  SymWallE_cellD_t1_16_60 x F ∧
  SymWallE_cellD_t3_03_34 x F ∧
  SymWallE_cellD_t3_03_35 x F ∧
  SymWallE_cellD_t3_04_30 x F ∧
  SymWallE_cellD_t3_04_34 x F ∧
  SymWallE_cellD_t3_04_35 x F ∧
  SymWallE_cellD_t3_05_30 x F ∧
  SymWallE_cellD_t3_05_34 x F ∧
  SymWallE_cellD_t3_05_35 x F ∧
  SymWallE_cellD_t3_40_53 x F ∧
  SymWallE_cellD_t3_40_54 x F ∧
  SymWallE_cellD_t3_43_50 x F ∧
  SymWallE_cellD_t3_43_54 x F ∧
  SymWallE_cellD_t3_45_50 x F ∧
  SymWallE_cellD_t3_45_53 x F ∧
  SymWallE_cellD_t4_04_60 x F ∧
  SymWallE_cellD_t4_06_64 x F ∧
  SymWallE_cellD_t5_12_61 x F ∧
  SymWallE_cellD_t5_21_62 x F ∧
  SymWallE_cellD_t6_23_35 x F ∧
  SymWallE_cellD_t6_25_32 x F ∧
  SymWallE_cellD_t7_23_62 x F ∧
  SymWallE_cellD_t7_23_63 x F ∧
  SymWallE_cellD_t7_26_63 x F ∧
  SymWallE_cellD_t8_34_63 x F ∧
  SymWallE_cellD_t8_36_64 x F

private lemma holeLeaf_symAllWallE2_cellD {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cellD x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cellD_t0_10_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t1_10_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t4_04_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t6_25_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t8_34_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t0_02_10 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t0_12_20 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t1_10_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t1_16_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_03_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_04_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_04_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_40_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_43_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t4_04_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t4_06_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t5_12_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t5_21_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t6_23_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t6_25_32 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t7_23_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t7_23_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t7_26_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t8_34_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD_t8_36_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cellD6 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cellD6_t0_10_12 x F ∧
  SymWallE_cellD6_t1_10_60 x F ∧
  SymWallE_cellD6_t4_60_64 x F ∧
  SymWallE_cellD6_t6_25_35 x F ∧
  SymWallE_cellD6_t8_34_64 x F ∧
  SymWallE_cellD6_t0_02_10 x F ∧
  SymWallE_cellD6_t0_12_20 x F ∧
  SymWallE_cellD6_t1_10_61 x F ∧
  SymWallE_cellD6_t1_16_60 x F ∧
  SymWallE_cellD6_t3_03_35 x F ∧
  SymWallE_cellD6_t3_04_30 x F ∧
  SymWallE_cellD6_t3_04_35 x F ∧
  SymWallE_cellD6_t3_05_30 x F ∧
  SymWallE_cellD6_t3_05_34 x F ∧
  SymWallE_cellD6_t3_05_35 x F ∧
  SymWallE_cellD6_t3_30_43 x F ∧
  SymWallE_cellD6_t3_30_45 x F ∧
  SymWallE_cellD6_t3_34_40 x F ∧
  SymWallE_cellD6_t3_34_45 x F ∧
  SymWallE_cellD6_t3_35_40 x F ∧
  SymWallE_cellD6_t3_35_43 x F ∧
  SymWallE_cellD6_t3_35_45 x F ∧
  SymWallE_cellD6_t3_40_53 x F ∧
  SymWallE_cellD6_t3_40_54 x F ∧
  SymWallE_cellD6_t3_43_50 x F ∧
  SymWallE_cellD6_t3_45_50 x F ∧
  SymWallE_cellD6_t3_45_53 x F ∧
  SymWallE_cellD6_t4_04_60 x F ∧
  SymWallE_cellD6_t4_40_64 x F ∧
  SymWallE_cellD6_t5_12_61 x F ∧
  SymWallE_cellD6_t5_21_62 x F ∧
  SymWallE_cellD6_t6_23_35 x F ∧
  SymWallE_cellD6_t6_25_32 x F ∧
  SymWallE_cellD6_t7_23_62 x F ∧
  SymWallE_cellD6_t7_32_63 x F ∧
  SymWallE_cellD6_t8_34_63 x F ∧
  SymWallE_cellD6_t8_36_64 x F

private lemma holeLeaf_symAllWallE2_cellD6 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cellD6 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cellD6_t0_10_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t1_10_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t4_60_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t6_25_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t8_34_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t0_02_10 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t0_12_20 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t1_10_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t1_16_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_04_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_30_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_30_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_34_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_34_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_35_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_35_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_35_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_40_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t4_04_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t4_40_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t5_12_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t5_21_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t6_23_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t6_25_32 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t7_23_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t7_32_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t8_34_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellD6_t8_36_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cellA2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cellA2_t0_02_12 x F ∧
  SymWallE_cellA2_t1_01_61 x F ∧
  SymWallE_cellA2_t2_02_52 x F ∧
  SymWallE_cellA2_t3_05_35 x F ∧
  SymWallE_cellA2_t3_05_45 x F ∧
  SymWallE_cellA2_t3_35_45 x F ∧
  SymWallE_cellA2_t3_40_43 x F ∧
  SymWallE_cellA2_t3_40_45 x F ∧
  SymWallE_cellA2_t3_43_45 x F ∧
  SymWallE_cellA2_t5_12_62 x F ∧
  SymWallE_cellA2_t6_32_52 x F ∧
  SymWallE_cellA2_t7_32_62 x F ∧
  SymWallE_cellA2_t8_43_46 x F ∧
  SymWallE_cellA2_t0_01_12 x F ∧
  SymWallE_cellA2_t0_02_10 x F ∧
  SymWallE_cellA2_t1_01_60 x F ∧
  SymWallE_cellA2_t1_06_61 x F ∧
  SymWallE_cellA2_t2_02_50 x F ∧
  SymWallE_cellA2_t2_05_52 x F ∧
  SymWallE_cellA2_t3_03_35 x F ∧
  SymWallE_cellA2_t3_03_40 x F ∧
  SymWallE_cellA2_t3_03_45 x F ∧
  SymWallE_cellA2_t3_04_35 x F ∧
  SymWallE_cellA2_t3_04_45 x F ∧
  SymWallE_cellA2_t3_05_30 x F ∧
  SymWallE_cellA2_t3_05_34 x F ∧
  SymWallE_cellA2_t3_05_40 x F ∧
  SymWallE_cellA2_t3_05_43 x F ∧
  SymWallE_cellA2_t3_30_43 x F ∧
  SymWallE_cellA2_t3_30_45 x F ∧
  SymWallE_cellA2_t3_34_45 x F ∧
  SymWallE_cellA2_t3_35_40 x F ∧
  SymWallE_cellA2_t3_35_43 x F ∧
  SymWallE_cellA2_t3_40_53 x F ∧
  SymWallE_cellA2_t3_43_50 x F ∧
  SymWallE_cellA2_t3_45_50 x F ∧
  SymWallE_cellA2_t3_45_53 x F ∧
  SymWallE_cellA2_t5_12_61 x F ∧
  SymWallE_cellA2_t5_16_62 x F ∧
  SymWallE_cellA2_t6_32_53 x F ∧
  SymWallE_cellA2_t6_35_52 x F ∧
  SymWallE_cellA2_t7_32_63 x F ∧
  SymWallE_cellA2_t7_36_62 x F ∧
  SymWallE_cellA2_t8_36_43 x F ∧
  SymWallE_cellA2_t8_46_63 x F

private lemma holeLeaf_symAllWallE2_cellA2 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cellA2 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cellA2_t0_02_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t2_02_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_05_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_35_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_40_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_40_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_43_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t5_12_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t6_32_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t7_32_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t8_43_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t0_01_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t0_02_10 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t2_02_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t2_05_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_03_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_05_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_30_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_30_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_34_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_35_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_35_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t5_12_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t5_16_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t6_32_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t6_35_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t7_32_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t7_36_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t8_36_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA2_t8_46_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cellB2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cellB2_t0_02_12 x F ∧
  SymWallE_cellB2_t1_01_61 x F ∧
  SymWallE_cellB2_t2_02_52 x F ∧
  SymWallE_cellB2_t3_03_43 x F ∧
  SymWallE_cellB2_t3_05_35 x F ∧
  SymWallE_cellB2_t3_05_45 x F ∧
  SymWallE_cellB2_t3_43_53 x F ∧
  SymWallE_cellB2_t5_12_62 x F ∧
  SymWallE_cellB2_t6_32_52 x F ∧
  SymWallE_cellB2_t8_43_46 x F ∧
  SymWallE_cellB2_t0_01_12 x F ∧
  SymWallE_cellB2_t0_02_10 x F ∧
  SymWallE_cellB2_t1_01_60 x F ∧
  SymWallE_cellB2_t1_06_61 x F ∧
  SymWallE_cellB2_t2_02_50 x F ∧
  SymWallE_cellB2_t2_05_52 x F ∧
  SymWallE_cellB2_t3_03_34 x F ∧
  SymWallE_cellB2_t3_03_35 x F ∧
  SymWallE_cellB2_t3_03_40 x F ∧
  SymWallE_cellB2_t3_03_45 x F ∧
  SymWallE_cellB2_t3_04_35 x F ∧
  SymWallE_cellB2_t3_04_43 x F ∧
  SymWallE_cellB2_t3_04_45 x F ∧
  SymWallE_cellB2_t3_05_30 x F ∧
  SymWallE_cellB2_t3_05_34 x F ∧
  SymWallE_cellB2_t3_05_40 x F ∧
  SymWallE_cellB2_t3_05_43 x F ∧
  SymWallE_cellB2_t3_40_53 x F ∧
  SymWallE_cellB2_t3_43_50 x F ∧
  SymWallE_cellB2_t3_43_54 x F ∧
  SymWallE_cellB2_t3_45_50 x F ∧
  SymWallE_cellB2_t3_45_53 x F ∧
  SymWallE_cellB2_t4_04_46 x F ∧
  SymWallE_cellB2_t4_06_64 x F ∧
  SymWallE_cellB2_t5_12_61 x F ∧
  SymWallE_cellB2_t5_16_62 x F ∧
  SymWallE_cellB2_t6_32_53 x F ∧
  SymWallE_cellB2_t6_35_52 x F ∧
  SymWallE_cellB2_t8_36_43 x F ∧
  SymWallE_cellB2_t8_46_63 x F

private lemma holeLeaf_symAllWallE2_cellB2 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cellB2 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cellB2_t0_02_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t2_02_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_03_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_05_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_43_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t5_12_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t6_32_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t8_43_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t0_01_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t0_02_10 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t2_02_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t2_05_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_03_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_03_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_04_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_05_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_43_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t4_04_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t4_06_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t5_12_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t5_16_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t6_32_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t6_35_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t8_36_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellB2_t8_46_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cellA0 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cellA0_t0_10_20 x F ∧
  SymWallE_cellA0_t1_10_60 x F ∧
  SymWallE_cellA0_t2_20_50 x F ∧
  SymWallE_cellA0_t3_04_34 x F ∧
  SymWallE_cellA0_t3_30_50 x F ∧
  SymWallE_cellA0_t3_34_54 x F ∧
  SymWallE_cellA0_t3_40_50 x F ∧
  SymWallE_cellA0_t5_21_61 x F ∧
  SymWallE_cellA0_t6_25_35 x F ∧
  SymWallE_cellA0_t8_34_64 x F ∧
  SymWallE_cellA0_t0_10_21 x F ∧
  SymWallE_cellA0_t0_12_20 x F ∧
  SymWallE_cellA0_t1_10_61 x F ∧
  SymWallE_cellA0_t1_16_60 x F ∧
  SymWallE_cellA0_t2_20_52 x F ∧
  SymWallE_cellA0_t2_25_50 x F ∧
  SymWallE_cellA0_t3_03_34 x F ∧
  SymWallE_cellA0_t3_04_30 x F ∧
  SymWallE_cellA0_t3_04_35 x F ∧
  SymWallE_cellA0_t3_05_30 x F ∧
  SymWallE_cellA0_t3_05_34 x F ∧
  SymWallE_cellA0_t3_30_53 x F ∧
  SymWallE_cellA0_t3_30_54 x F ∧
  SymWallE_cellA0_t3_34_50 x F ∧
  SymWallE_cellA0_t3_34_53 x F ∧
  SymWallE_cellA0_t3_35_50 x F ∧
  SymWallE_cellA0_t3_35_54 x F ∧
  SymWallE_cellA0_t3_40_53 x F ∧
  SymWallE_cellA0_t3_40_54 x F ∧
  SymWallE_cellA0_t3_43_50 x F ∧
  SymWallE_cellA0_t3_43_54 x F ∧
  SymWallE_cellA0_t3_45_50 x F ∧
  SymWallE_cellA0_t5_21_62 x F ∧
  SymWallE_cellA0_t5_26_61 x F ∧
  SymWallE_cellA0_t6_23_35 x F ∧
  SymWallE_cellA0_t6_25_32 x F ∧
  SymWallE_cellA0_t7_23_36 x F ∧
  SymWallE_cellA0_t7_26_63 x F ∧
  SymWallE_cellA0_t8_34_63 x F ∧
  SymWallE_cellA0_t8_36_64 x F

private lemma holeLeaf_symAllWallE2_cellA0 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cellA0 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cellA0_t0_10_20 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t1_10_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t2_20_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_04_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_30_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_34_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_40_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t5_21_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t6_25_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t8_34_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t0_10_21 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t0_12_20 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t1_10_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t1_16_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t2_20_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t2_25_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_03_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_04_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_30_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_30_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_34_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_34_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_35_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_35_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_40_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_43_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t5_21_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t5_26_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t6_23_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t6_25_32 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t7_23_36 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t7_26_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t8_34_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellA0_t8_36_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cellCp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cellCp_t1_01_61 x F ∧
  SymWallE_cellCp_t3_30_35 x F ∧
  SymWallE_cellCp_t3_34_35 x F ∧
  SymWallE_cellCp_t3_40_43 x F ∧
  SymWallE_cellCp_t3_40_45 x F ∧
  SymWallE_cellCp_t4_40_46 x F ∧
  SymWallE_cellCp_t5_21_61 x F ∧
  SymWallE_cellCp_t6_32_35 x F ∧
  SymWallE_cellCp_t7_32_36 x F ∧
  SymWallE_cellCp_t1_01_60 x F ∧
  SymWallE_cellCp_t1_06_61 x F ∧
  SymWallE_cellCp_t2_02_50 x F ∧
  SymWallE_cellCp_t2_20_52 x F ∧
  SymWallE_cellCp_t2_50_52 x F ∧
  SymWallE_cellCp_t3_03_40 x F ∧
  SymWallE_cellCp_t3_04_35 x F ∧
  SymWallE_cellCp_t3_04_45 x F ∧
  SymWallE_cellCp_t3_05_30 x F ∧
  SymWallE_cellCp_t3_05_34 x F ∧
  SymWallE_cellCp_t3_05_40 x F ∧
  SymWallE_cellCp_t3_30_43 x F ∧
  SymWallE_cellCp_t3_30_45 x F ∧
  SymWallE_cellCp_t3_30_53 x F ∧
  SymWallE_cellCp_t3_34_45 x F ∧
  SymWallE_cellCp_t3_35_40 x F ∧
  SymWallE_cellCp_t3_35_50 x F ∧
  SymWallE_cellCp_t3_35_54 x F ∧
  SymWallE_cellCp_t3_40_53 x F ∧
  SymWallE_cellCp_t3_43_50 x F ∧
  SymWallE_cellCp_t3_45_50 x F ∧
  SymWallE_cellCp_t4_06_40 x F ∧
  SymWallE_cellCp_t4_46_60 x F ∧
  SymWallE_cellCp_t5_21_62 x F ∧
  SymWallE_cellCp_t5_26_61 x F ∧
  SymWallE_cellCp_t6_25_32 x F ∧
  SymWallE_cellCp_t6_35_52 x F ∧
  SymWallE_cellCp_t7_26_32 x F ∧
  SymWallE_cellCp_t7_36_62 x F

private lemma holeLeaf_symAllWallE2_cellCp {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cellCp x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cellCp_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_30_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_34_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_40_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_40_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t4_40_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t5_21_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t6_32_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t7_32_36 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t2_02_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t2_20_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t2_50_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_30_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_30_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_30_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_34_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_35_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_35_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_35_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t4_06_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t4_46_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t5_21_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t5_26_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t6_25_32 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t6_35_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t7_26_32 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cellCp_t7_36_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cell0536 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cell0536_t1_01_61 x F ∧
  SymWallE_cell0536_t2_02_52 x F ∧
  SymWallE_cell0536_t3_05_35 x F ∧
  SymWallE_cell0536_t3_05_45 x F ∧
  SymWallE_cell0536_t3_35_45 x F ∧
  SymWallE_cell0536_t3_40_43 x F ∧
  SymWallE_cell0536_t3_40_45 x F ∧
  SymWallE_cell0536_t3_43_45 x F ∧
  SymWallE_cell0536_t4_40_46 x F ∧
  SymWallE_cell0536_t6_32_52 x F ∧
  SymWallE_cell0536_t7_32_62 x F ∧
  SymWallE_cell0536_t8_43_46 x F ∧
  SymWallE_cell0536_t1_01_60 x F ∧
  SymWallE_cell0536_t1_06_61 x F ∧
  SymWallE_cell0536_t2_02_50 x F ∧
  SymWallE_cell0536_t2_05_52 x F ∧
  SymWallE_cell0536_t3_03_35 x F ∧
  SymWallE_cell0536_t3_03_40 x F ∧
  SymWallE_cell0536_t3_03_45 x F ∧
  SymWallE_cell0536_t3_04_35 x F ∧
  SymWallE_cell0536_t3_04_45 x F ∧
  SymWallE_cell0536_t3_05_30 x F ∧
  SymWallE_cell0536_t3_05_34 x F ∧
  SymWallE_cell0536_t3_05_40 x F ∧
  SymWallE_cell0536_t3_05_43 x F ∧
  SymWallE_cell0536_t3_30_43 x F ∧
  SymWallE_cell0536_t3_30_45 x F ∧
  SymWallE_cell0536_t3_34_45 x F ∧
  SymWallE_cell0536_t3_35_40 x F ∧
  SymWallE_cell0536_t3_35_43 x F ∧
  SymWallE_cell0536_t3_40_53 x F ∧
  SymWallE_cell0536_t3_43_50 x F ∧
  SymWallE_cell0536_t3_45_50 x F ∧
  SymWallE_cell0536_t3_45_53 x F ∧
  SymWallE_cell0536_t4_06_40 x F ∧
  SymWallE_cell0536_t4_46_60 x F ∧
  SymWallE_cell0536_t6_32_53 x F ∧
  SymWallE_cell0536_t6_35_52 x F ∧
  SymWallE_cell0536_t7_32_63 x F ∧
  SymWallE_cell0536_t7_36_62 x F ∧
  SymWallE_cell0536_t8_36_43 x F ∧
  SymWallE_cell0536_t8_46_63 x F

private lemma holeLeaf_symAllWallE2_cell0536 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cell0536 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cell0536_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t2_02_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_05_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_35_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_40_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_40_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_43_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t4_40_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t6_32_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t7_32_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t8_43_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t2_02_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t2_05_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_03_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_05_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_30_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_30_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_34_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_35_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_35_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t4_06_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t4_46_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t6_32_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t6_35_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t7_32_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t7_36_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t8_36_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0536_t8_46_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cell0164 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cell0164_t0_02_12 x F ∧
  SymWallE_cell0164_t1_01_61 x F ∧
  SymWallE_cell0164_t3_03_43 x F ∧
  SymWallE_cell0164_t3_05_35 x F ∧
  SymWallE_cell0164_t3_05_45 x F ∧
  SymWallE_cell0164_t3_43_53 x F ∧
  SymWallE_cell0164_t5_12_62 x F ∧
  SymWallE_cell0164_t8_43_63 x F ∧
  SymWallE_cell0164_t0_01_12 x F ∧
  SymWallE_cell0164_t0_02_10 x F ∧
  SymWallE_cell0164_t1_01_60 x F ∧
  SymWallE_cell0164_t1_06_61 x F ∧
  SymWallE_cell0164_t3_03_34 x F ∧
  SymWallE_cell0164_t3_03_35 x F ∧
  SymWallE_cell0164_t3_03_40 x F ∧
  SymWallE_cell0164_t3_03_45 x F ∧
  SymWallE_cell0164_t3_04_35 x F ∧
  SymWallE_cell0164_t3_04_43 x F ∧
  SymWallE_cell0164_t3_04_45 x F ∧
  SymWallE_cell0164_t3_05_30 x F ∧
  SymWallE_cell0164_t3_05_34 x F ∧
  SymWallE_cell0164_t3_05_40 x F ∧
  SymWallE_cell0164_t3_05_43 x F ∧
  SymWallE_cell0164_t3_40_53 x F ∧
  SymWallE_cell0164_t3_43_50 x F ∧
  SymWallE_cell0164_t3_43_54 x F ∧
  SymWallE_cell0164_t3_45_50 x F ∧
  SymWallE_cell0164_t3_45_53 x F ∧
  SymWallE_cell0164_t4_04_60 x F ∧
  SymWallE_cell0164_t4_04_64 x F ∧
  SymWallE_cell0164_t4_06_64 x F ∧
  SymWallE_cell0164_t5_12_61 x F ∧
  SymWallE_cell0164_t5_16_62 x F ∧
  SymWallE_cell0164_t8_43_64 x F ∧
  SymWallE_cell0164_t8_46_63 x F

private lemma holeLeaf_symAllWallE2_cell0164 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cell0164 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cell0164_t0_02_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_03_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_05_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_43_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t5_12_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t8_43_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t0_01_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t0_02_10 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_03_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_03_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_04_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_05_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_43_54 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t4_04_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t4_04_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t4_06_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t5_12_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t5_16_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t8_43_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell0164_t8_46_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cell01634 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cell01634_t0_02_12 x F ∧
  SymWallE_cell01634_t1_01_61 x F ∧
  SymWallE_cell01634_t3_05_35 x F ∧
  SymWallE_cell01634_t3_05_45 x F ∧
  SymWallE_cell01634_t3_35_45 x F ∧
  SymWallE_cell01634_t3_40_43 x F ∧
  SymWallE_cell01634_t3_40_45 x F ∧
  SymWallE_cell01634_t3_43_45 x F ∧
  SymWallE_cell01634_t5_12_62 x F ∧
  SymWallE_cell01634_t7_32_62 x F ∧
  SymWallE_cell01634_t8_43_63 x F ∧
  SymWallE_cell01634_t0_01_12 x F ∧
  SymWallE_cell01634_t0_02_10 x F ∧
  SymWallE_cell01634_t1_01_60 x F ∧
  SymWallE_cell01634_t1_06_61 x F ∧
  SymWallE_cell01634_t3_03_35 x F ∧
  SymWallE_cell01634_t3_03_40 x F ∧
  SymWallE_cell01634_t3_03_45 x F ∧
  SymWallE_cell01634_t3_04_35 x F ∧
  SymWallE_cell01634_t3_04_45 x F ∧
  SymWallE_cell01634_t3_05_30 x F ∧
  SymWallE_cell01634_t3_05_34 x F ∧
  SymWallE_cell01634_t3_05_40 x F ∧
  SymWallE_cell01634_t3_05_43 x F ∧
  SymWallE_cell01634_t3_30_43 x F ∧
  SymWallE_cell01634_t3_30_45 x F ∧
  SymWallE_cell01634_t3_34_45 x F ∧
  SymWallE_cell01634_t3_35_40 x F ∧
  SymWallE_cell01634_t3_35_43 x F ∧
  SymWallE_cell01634_t3_40_53 x F ∧
  SymWallE_cell01634_t3_43_50 x F ∧
  SymWallE_cell01634_t3_45_50 x F ∧
  SymWallE_cell01634_t3_45_53 x F ∧
  SymWallE_cell01634_t4_04_60 x F ∧
  SymWallE_cell01634_t4_40_64 x F ∧
  SymWallE_cell01634_t5_12_61 x F ∧
  SymWallE_cell01634_t5_16_62 x F ∧
  SymWallE_cell01634_t7_32_63 x F ∧
  SymWallE_cell01634_t7_36_62 x F ∧
  SymWallE_cell01634_t8_43_64 x F ∧
  SymWallE_cell01634_t8_46_63 x F

private lemma holeLeaf_symAllWallE2_cell01634 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cell01634 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cell01634_t0_02_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_05_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_35_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_40_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_40_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_43_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t5_12_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t7_32_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t8_43_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t0_01_12 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t0_02_10 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_03_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_05_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_30_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_30_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_34_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_35_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_35_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t4_04_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t4_40_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t5_12_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t5_16_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t7_32_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t7_36_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t8_43_64 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell01634_t8_46_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

def SymAllWallE2_cell05326 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymWallE_cell05326_t1_01_61 x F ∧
  SymWallE_cell05326_t3_05_35 x F ∧
  SymWallE_cell05326_t3_35_45 x F ∧
  SymWallE_cell05326_t3_40_43 x F ∧
  SymWallE_cell05326_t3_40_45 x F ∧
  SymWallE_cell05326_t4_40_46 x F ∧
  SymWallE_cell05326_t5_21_61 x F ∧
  SymWallE_cell05326_t6_32_35 x F ∧
  SymWallE_cell05326_t7_32_62 x F ∧
  SymWallE_cell05326_t1_01_60 x F ∧
  SymWallE_cell05326_t1_06_61 x F ∧
  SymWallE_cell05326_t2_02_50 x F ∧
  SymWallE_cell05326_t2_05_52 x F ∧
  SymWallE_cell05326_t3_03_35 x F ∧
  SymWallE_cell05326_t3_03_40 x F ∧
  SymWallE_cell05326_t3_03_45 x F ∧
  SymWallE_cell05326_t3_04_35 x F ∧
  SymWallE_cell05326_t3_04_45 x F ∧
  SymWallE_cell05326_t3_05_30 x F ∧
  SymWallE_cell05326_t3_05_34 x F ∧
  SymWallE_cell05326_t3_05_40 x F ∧
  SymWallE_cell05326_t3_05_43 x F ∧
  SymWallE_cell05326_t3_05_45 x F ∧
  SymWallE_cell05326_t3_30_43 x F ∧
  SymWallE_cell05326_t3_30_45 x F ∧
  SymWallE_cell05326_t3_34_45 x F ∧
  SymWallE_cell05326_t3_35_40 x F ∧
  SymWallE_cell05326_t3_35_43 x F ∧
  SymWallE_cell05326_t3_40_53 x F ∧
  SymWallE_cell05326_t3_43_45 x F ∧
  SymWallE_cell05326_t3_43_50 x F ∧
  SymWallE_cell05326_t3_45_50 x F ∧
  SymWallE_cell05326_t3_45_53 x F ∧
  SymWallE_cell05326_t4_06_40 x F ∧
  SymWallE_cell05326_t4_46_60 x F ∧
  SymWallE_cell05326_t5_21_62 x F ∧
  SymWallE_cell05326_t5_26_61 x F ∧
  SymWallE_cell05326_t6_25_32 x F ∧
  SymWallE_cell05326_t6_35_52 x F ∧
  SymWallE_cell05326_t7_32_63 x F ∧
  SymWallE_cell05326_t7_36_62 x F

private lemma holeLeaf_symAllWallE2_cell05326 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : SymAllWallE2_cell05326 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((symCert_cell05326_t1_01_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_05_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_35_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_40_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_40_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t4_40_46 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t5_21_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t6_32_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t7_32_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t1_01_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t1_06_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t2_02_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t2_05_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_03_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_03_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_03_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_04_35 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_04_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_05_30 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_05_34 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_05_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_05_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_05_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_30_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_30_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_34_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_35_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_35_43 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_40_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_43_45 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_43_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_45_50 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t3_45_53 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t4_06_40 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t4_46_60 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t5_21_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t5_26_61 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t6_25_32 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t6_35_52 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t7_32_63 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1
  · exact ((symCert_cell05326_t7_36_62 F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- Conjunction of the `429` mirror walls on `(x, F)` for the 11 non-self-dual cells. -/
def SymAllWallE2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  SymAllWallE2_cellC x F ∧
  SymAllWallE2_cellD x F ∧
  SymAllWallE2_cellD6 x F ∧
  SymAllWallE2_cellA2 x F ∧
  SymAllWallE2_cellB2 x F ∧
  SymAllWallE2_cellA0 x F ∧
  SymAllWallE2_cellCp x F ∧
  SymAllWallE2_cell0536 x F ∧
  SymAllWallE2_cell0164 x F ∧
  SymAllWallE2_cell01634 x F ∧
  SymAllWallE2_cell05326 x F

/-- One-sided conjunction of all `1023` walls (`594` in `AllWallE2` + `429` mirror walls). -/
def AllWallE2S (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  AllWallE2 x F ∧ SymAllWallE2 x F

/-! ### Self-dual wall transport (`165` walls across `cellB0`, `cell0236`, `cellP`, `cell046125`) -/

private lemma twin_sd_cellB0_t0_10_20 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t1_10_60 x F) : WallE_cellB0_t0_10_20 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t0_10_20 (Sym.sym24 F)) (wall_cellB0_t1_10_60 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t1_10_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t0_10_20 x F) : WallE_cellB0_t1_10_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t1_10_60 (Sym.sym24 F)) (wall_cellB0_t0_10_20 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t2_20_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t4_40_60 x F) : WallE_cellB0_t2_20_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t2_20_50 (Sym.sym24 F)) (wall_cellB0_t4_40_60 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_34 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_35 x F) : WallE_cellB0_t3_30_34 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_34 (Sym.sym24 F)) (wall_cellB0_t3_30_35 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_34 x F) : WallE_cellB0_t3_30_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_35 (Sym.sym24 F)) (wall_cellB0_t3_30_34 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_50 x F) : WallE_cellB0_t3_30_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_40 (Sym.sym24 F)) (wall_cellB0_t3_30_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_40 x F) : WallE_cellB0_t3_30_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_50 (Sym.sym24 F)) (wall_cellB0_t3_30_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_34_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_34_35 x F) : WallE_cellB0_t3_34_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_34_35 (Sym.sym24 F)) (wall_cellB0_t3_34_35 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_40_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_40_50 x F) : WallE_cellB0_t3_40_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_40_50 (Sym.sym24 F)) (wall_cellB0_t3_40_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t4_40_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t2_20_50 x F) : WallE_cellB0_t4_40_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t4_40_60 (Sym.sym24 F)) (wall_cellB0_t2_20_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t5_21_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t5_21_61 x F) : WallE_cellB0_t5_21_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t5_21_61 (Sym.sym24 F)) (wall_cellB0_t5_21_61 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t6_25_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t8_34_64 x F) : WallE_cellB0_t6_25_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t6_25_35 (Sym.sym24 F)) (wall_cellB0_t8_34_64 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t8_34_64 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t6_25_35 x F) : WallE_cellB0_t8_34_64 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t8_34_64 (Sym.sym24 F)) (wall_cellB0_t6_25_35 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t0_01_21 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t1_01_61 x F) : WallE_cell0236_t0_01_21 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t0_01_21 (Sym.sym24 F)) (wall_cell0236_t1_01_61 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t1_01_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t0_01_21 x F) : WallE_cell0236_t1_01_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t1_01_61 (Sym.sym24 F)) (wall_cell0236_t0_01_21 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t2_50_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t4_40_46 x F) : WallE_cell0236_t2_50_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t2_50_52 (Sym.sym24 F)) (wall_cell0236_t4_40_46 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t4_40_46 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t2_50_52 x F) : WallE_cell0236_t4_40_46 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t4_40_46 (Sym.sym24 F)) (wall_cell0236_t2_50_52 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t6_52_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t8_43_46 x F) : WallE_cell0236_t6_52_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t6_52_53 (Sym.sym24 F)) (wall_cell0236_t8_43_46 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t8_43_46 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t6_52_53 x F) : WallE_cell0236_t8_43_46 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t8_43_46 (Sym.sym24 F)) (wall_cell0236_t6_52_53 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t2_50_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t4_40_46 x F) : WallE_cellP_t2_50_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t2_50_52 (Sym.sym24 F)) (wall_cellP_t4_40_46 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_34 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_35 x F) : WallE_cellP_t3_30_34 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_34 (Sym.sym24 F)) (wall_cellP_t3_30_35 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_34 x F) : WallE_cellP_t3_30_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_35 (Sym.sym24 F)) (wall_cellP_t3_30_34 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_50 x F) : WallE_cellP_t3_30_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_40 (Sym.sym24 F)) (wall_cellP_t3_30_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_40 x F) : WallE_cellP_t3_30_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_50 (Sym.sym24 F)) (wall_cellP_t3_30_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_34_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_34_35 x F) : WallE_cellP_t3_34_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_34_35 (Sym.sym24 F)) (wall_cellP_t3_34_35 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_40_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_40_50 x F) : WallE_cellP_t3_40_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_40_50 (Sym.sym24 F)) (wall_cellP_t3_40_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t4_40_46 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t2_50_52 x F) : WallE_cellP_t4_40_46 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t4_40_46 (Sym.sym24 F)) (wall_cellP_t2_50_52 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t5_21_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t5_21_61 x F) : WallE_cellP_t5_21_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t5_21_61 (Sym.sym24 F)) (wall_cellP_t5_21_61 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t6_32_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t8_34_36 x F) : WallE_cellP_t6_32_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t6_32_35 (Sym.sym24 F)) (wall_cellP_t8_34_36 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t7_32_36 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t7_32_36 x F) : WallE_cellP_t7_32_36 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t7_32_36 (Sym.sym24 F)) (wall_cellP_t7_32_36 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t8_34_36 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t6_32_35 x F) : WallE_cellP_t8_34_36 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t8_34_36 (Sym.sym24 F)) (wall_cellP_t6_32_35 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t2_50_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t4_40_46 x F) : WallE_cell046125_t2_50_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t2_50_52 (Sym.sym24 F)) (wall_cell046125_t4_40_46 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_34 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_35 x F) : WallE_cell046125_t3_30_34 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_34 (Sym.sym24 F)) (wall_cell046125_t3_30_35 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_34 x F) : WallE_cell046125_t3_30_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_35 (Sym.sym24 F)) (wall_cell046125_t3_30_34 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_50 x F) : WallE_cell046125_t3_30_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_40 (Sym.sym24 F)) (wall_cell046125_t3_30_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_40 x F) : WallE_cell046125_t3_30_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_50 (Sym.sym24 F)) (wall_cell046125_t3_30_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_34_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_34_35 x F) : WallE_cell046125_t3_34_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_34_35 (Sym.sym24 F)) (wall_cell046125_t3_34_35 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_40_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_40_50 x F) : WallE_cell046125_t3_40_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_40_50 (Sym.sym24 F)) (wall_cell046125_t3_40_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t4_40_46 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t2_50_52 x F) : WallE_cell046125_t4_40_46 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t4_40_46 (Sym.sym24 F)) (wall_cell046125_t2_50_52 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t5_21_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t5_21_61 x F) : WallE_cell046125_t5_21_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t5_21_61 (Sym.sym24 F)) (wall_cell046125_t5_21_61 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t6_32_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t8_34_36 x F) : WallE_cell046125_t6_32_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t6_32_35 (Sym.sym24 F)) (wall_cell046125_t8_34_36 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t8_34_36 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t6_32_35 x F) : WallE_cell046125_t8_34_36 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t8_34_36 (Sym.sym24 F)) (wall_cell046125_t6_32_35 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t0_10_21 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t1_10_61 x F) : WallE_cellB0_t0_10_21 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t0_10_21 (Sym.sym24 F)) (wall_cellB0_t1_10_61 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t0_12_20 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t1_16_60 x F) : WallE_cellB0_t0_12_20 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t0_12_20 (Sym.sym24 F)) (wall_cellB0_t1_16_60 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t1_10_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t0_10_21 x F) : WallE_cellB0_t1_10_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t1_10_61 (Sym.sym24 F)) (wall_cellB0_t0_10_21 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t1_16_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t0_12_20 x F) : WallE_cellB0_t1_16_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t1_16_60 (Sym.sym24 F)) (wall_cellB0_t0_12_20 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t2_20_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t4_46_60 x F) : WallE_cellB0_t2_20_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t2_20_52 (Sym.sym24 F)) (wall_cellB0_t4_46_60 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t2_25_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t4_40_64 x F) : WallE_cellB0_t2_25_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t2_25_50 (Sym.sym24 F)) (wall_cellB0_t4_40_64 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_04_30 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_05_30 x F) : WallE_cellB0_t3_04_30 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_04_30 (Sym.sym24 F)) (wall_cellB0_t3_05_30 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_04_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_05_34 x F) : WallE_cellB0_t3_04_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_04_35 (Sym.sym24 F)) (wall_cellB0_t3_05_34 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_05_30 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_04_30 x F) : WallE_cellB0_t3_05_30 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_05_30 (Sym.sym24 F)) (wall_cellB0_t3_04_30 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_05_34 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_04_35 x F) : WallE_cellB0_t3_05_34 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_05_34 (Sym.sym24 F)) (wall_cellB0_t3_04_35 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_43 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_53 x F) : WallE_cellB0_t3_30_43 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_43 (Sym.sym24 F)) (wall_cellB0_t3_30_53 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_54 x F) : WallE_cellB0_t3_30_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_45 (Sym.sym24 F)) (wall_cellB0_t3_30_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_43 x F) : WallE_cellB0_t3_30_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_53 (Sym.sym24 F)) (wall_cellB0_t3_30_43 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_30_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_30_45 x F) : WallE_cellB0_t3_30_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_30_54 (Sym.sym24 F)) (wall_cellB0_t3_30_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_34_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_35_50 x F) : WallE_cellB0_t3_34_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_34_40 (Sym.sym24 F)) (wall_cellB0_t3_35_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_34_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_35_54 x F) : WallE_cellB0_t3_34_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_34_45 (Sym.sym24 F)) (wall_cellB0_t3_35_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_34_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_35_40 x F) : WallE_cellB0_t3_34_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_34_50 (Sym.sym24 F)) (wall_cellB0_t3_35_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_35_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_34_50 x F) : WallE_cellB0_t3_35_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_35_40 (Sym.sym24 F)) (wall_cellB0_t3_34_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_35_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_34_40 x F) : WallE_cellB0_t3_35_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_35_50 (Sym.sym24 F)) (wall_cellB0_t3_34_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_35_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_34_45 x F) : WallE_cellB0_t3_35_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_35_54 (Sym.sym24 F)) (wall_cellB0_t3_34_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_40_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_43_50 x F) : WallE_cellB0_t3_40_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_40_53 (Sym.sym24 F)) (wall_cellB0_t3_43_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_40_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_45_50 x F) : WallE_cellB0_t3_40_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_40_54 (Sym.sym24 F)) (wall_cellB0_t3_45_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_43_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_40_53 x F) : WallE_cellB0_t3_43_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_43_50 (Sym.sym24 F)) (wall_cellB0_t3_40_53 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t3_45_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t3_40_54 x F) : WallE_cellB0_t3_45_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t3_45_50 (Sym.sym24 F)) (wall_cellB0_t3_40_54 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t4_40_64 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t2_25_50 x F) : WallE_cellB0_t4_40_64 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t4_40_64 (Sym.sym24 F)) (wall_cellB0_t2_25_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t4_46_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t2_20_52 x F) : WallE_cellB0_t4_46_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t4_46_60 (Sym.sym24 F)) (wall_cellB0_t2_20_52 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t5_21_62 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t5_26_61 x F) : WallE_cellB0_t5_21_62 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t5_21_62 (Sym.sym24 F)) (wall_cellB0_t5_26_61 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t5_26_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t5_21_62 x F) : WallE_cellB0_t5_26_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t5_26_61 (Sym.sym24 F)) (wall_cellB0_t5_21_62 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t6_23_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t8_34_63 x F) : WallE_cellB0_t6_23_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t6_23_35 (Sym.sym24 F)) (wall_cellB0_t8_34_63 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t6_25_32 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t8_36_64 x F) : WallE_cellB0_t6_25_32 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t6_25_32 (Sym.sym24 F)) (wall_cellB0_t8_36_64 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t8_34_63 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t6_23_35 x F) : WallE_cellB0_t8_34_63 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t8_34_63 (Sym.sym24 F)) (wall_cellB0_t6_23_35 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellB0_t8_36_64 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellB0_t6_25_32 x F) : WallE_cellB0_t8_36_64 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellB0 (by decide) (by decide) (wall_cellB0_t8_36_64 (Sym.sym24 F)) (wall_cellB0_t6_25_32 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t0_01_20 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t1_01_60 x F) : WallE_cell0236_t0_01_20 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t0_01_20 (Sym.sym24 F)) (wall_cell0236_t1_01_60 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t0_02_21 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t1_06_61 x F) : WallE_cell0236_t0_02_21 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t0_02_21 (Sym.sym24 F)) (wall_cell0236_t1_06_61 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t1_01_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t0_01_20 x F) : WallE_cell0236_t1_01_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t1_01_60 (Sym.sym24 F)) (wall_cell0236_t0_01_20 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t1_06_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t0_02_21 x F) : WallE_cell0236_t1_06_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t1_06_61 (Sym.sym24 F)) (wall_cell0236_t0_02_21 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t2_02_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t4_06_40 x F) : WallE_cell0236_t2_02_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t2_02_50 (Sym.sym24 F)) (wall_cell0236_t4_06_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t2_20_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t4_46_60 x F) : WallE_cell0236_t2_20_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t2_20_52 (Sym.sym24 F)) (wall_cell0236_t4_46_60 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_03_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_03_50 x F) : WallE_cell0236_t3_03_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_03_40 (Sym.sym24 F)) (wall_cell0236_t3_03_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_03_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_03_40 x F) : WallE_cell0236_t3_03_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_03_50 (Sym.sym24 F)) (wall_cell0236_t3_03_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_04_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_05_34 x F) : WallE_cell0236_t3_04_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_04_35 (Sym.sym24 F)) (wall_cell0236_t3_05_34 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_04_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_05_54 x F) : WallE_cell0236_t3_04_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_04_45 (Sym.sym24 F)) (wall_cell0236_t3_05_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_05_34 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_04_35 x F) : WallE_cell0236_t3_05_34 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_05_34 (Sym.sym24 F)) (wall_cell0236_t3_04_35 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_05_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_04_45 x F) : WallE_cell0236_t3_05_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_05_54 (Sym.sym24 F)) (wall_cell0236_t3_04_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_30_43 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_30_53 x F) : WallE_cell0236_t3_30_43 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_30_43 (Sym.sym24 F)) (wall_cell0236_t3_30_53 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_30_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_30_43 x F) : WallE_cell0236_t3_30_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_30_53 (Sym.sym24 F)) (wall_cell0236_t3_30_43 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_34_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_35_54 x F) : WallE_cell0236_t3_34_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_34_45 (Sym.sym24 F)) (wall_cell0236_t3_35_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_35_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_34_45 x F) : WallE_cell0236_t3_35_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_35_54 (Sym.sym24 F)) (wall_cell0236_t3_34_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_40_43 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_50_53 x F) : WallE_cell0236_t3_40_43 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_40_43 (Sym.sym24 F)) (wall_cell0236_t3_50_53 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_40_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_43_50 x F) : WallE_cell0236_t3_40_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_40_53 (Sym.sym24 F)) (wall_cell0236_t3_43_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_43_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_40_53 x F) : WallE_cell0236_t3_43_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_43_50 (Sym.sym24 F)) (wall_cell0236_t3_40_53 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t3_50_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t3_40_43 x F) : WallE_cell0236_t3_50_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t3_50_53 (Sym.sym24 F)) (wall_cell0236_t3_40_43 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t4_06_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t2_02_50 x F) : WallE_cell0236_t4_06_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t4_06_40 (Sym.sym24 F)) (wall_cell0236_t2_02_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t4_46_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t2_20_52 x F) : WallE_cell0236_t4_46_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t4_46_60 (Sym.sym24 F)) (wall_cell0236_t2_20_52 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t6_23_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t8_46_63 x F) : WallE_cell0236_t6_23_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t6_23_52 (Sym.sym24 F)) (wall_cell0236_t8_46_63 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t6_32_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t8_36_43 x F) : WallE_cell0236_t6_32_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t6_32_53 (Sym.sym24 F)) (wall_cell0236_t8_36_43 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t7_26_32 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t7_36_62 x F) : WallE_cell0236_t7_26_32 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t7_26_32 (Sym.sym24 F)) (wall_cell0236_t7_36_62 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t7_32_36 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t7_32_36 x F) : WallE_cell0236_t7_32_36 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t7_32_36 (Sym.sym24 F)) (wall_cell0236_t7_32_36 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t7_36_62 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t7_26_32 x F) : WallE_cell0236_t7_36_62 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t7_36_62 (Sym.sym24 F)) (wall_cell0236_t7_26_32 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t8_36_43 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t6_32_53 x F) : WallE_cell0236_t8_36_43 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t8_36_43 (Sym.sym24 F)) (wall_cell0236_t6_32_53 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell0236_t8_46_63 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell0236_t6_23_52 x F) : WallE_cell0236_t8_46_63 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell0236 (by decide) (by decide) (wall_cell0236_t8_46_63 (Sym.sym24 F)) (wall_cell0236_t6_23_52 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t2_02_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t4_06_40 x F) : WallE_cellP_t2_02_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t2_02_50 (Sym.sym24 F)) (wall_cellP_t4_06_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t2_20_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t4_46_60 x F) : WallE_cellP_t2_20_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t2_20_52 (Sym.sym24 F)) (wall_cellP_t4_46_60 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_04_30 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_05_30 x F) : WallE_cellP_t3_04_30 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_04_30 (Sym.sym24 F)) (wall_cellP_t3_05_30 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_04_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_05_34 x F) : WallE_cellP_t3_04_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_04_35 (Sym.sym24 F)) (wall_cellP_t3_05_34 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_05_30 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_04_30 x F) : WallE_cellP_t3_05_30 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_05_30 (Sym.sym24 F)) (wall_cellP_t3_04_30 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_05_34 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_04_35 x F) : WallE_cellP_t3_05_34 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_05_34 (Sym.sym24 F)) (wall_cellP_t3_04_35 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_43 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_53 x F) : WallE_cellP_t3_30_43 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_43 (Sym.sym24 F)) (wall_cellP_t3_30_53 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_54 x F) : WallE_cellP_t3_30_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_45 (Sym.sym24 F)) (wall_cellP_t3_30_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_43 x F) : WallE_cellP_t3_30_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_53 (Sym.sym24 F)) (wall_cellP_t3_30_43 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_30_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_30_45 x F) : WallE_cellP_t3_30_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_30_54 (Sym.sym24 F)) (wall_cellP_t3_30_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_34_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_35_50 x F) : WallE_cellP_t3_34_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_34_40 (Sym.sym24 F)) (wall_cellP_t3_35_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_34_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_35_54 x F) : WallE_cellP_t3_34_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_34_45 (Sym.sym24 F)) (wall_cellP_t3_35_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_34_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_35_40 x F) : WallE_cellP_t3_34_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_34_50 (Sym.sym24 F)) (wall_cellP_t3_35_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_35_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_34_50 x F) : WallE_cellP_t3_35_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_35_40 (Sym.sym24 F)) (wall_cellP_t3_34_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_35_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_34_40 x F) : WallE_cellP_t3_35_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_35_50 (Sym.sym24 F)) (wall_cellP_t3_34_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_35_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_34_45 x F) : WallE_cellP_t3_35_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_35_54 (Sym.sym24 F)) (wall_cellP_t3_34_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_40_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_43_50 x F) : WallE_cellP_t3_40_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_40_53 (Sym.sym24 F)) (wall_cellP_t3_43_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_40_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_45_50 x F) : WallE_cellP_t3_40_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_40_54 (Sym.sym24 F)) (wall_cellP_t3_45_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_43_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_40_53 x F) : WallE_cellP_t3_43_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_43_50 (Sym.sym24 F)) (wall_cellP_t3_40_53 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t3_45_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t3_40_54 x F) : WallE_cellP_t3_45_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t3_45_50 (Sym.sym24 F)) (wall_cellP_t3_40_54 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t4_06_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t2_02_50 x F) : WallE_cellP_t4_06_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t4_06_40 (Sym.sym24 F)) (wall_cellP_t2_02_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t4_46_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t2_20_52 x F) : WallE_cellP_t4_46_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t4_46_60 (Sym.sym24 F)) (wall_cellP_t2_20_52 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t5_21_62 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t5_26_61 x F) : WallE_cellP_t5_21_62 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t5_21_62 (Sym.sym24 F)) (wall_cellP_t5_26_61 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t5_26_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t5_21_62 x F) : WallE_cellP_t5_26_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t5_26_61 (Sym.sym24 F)) (wall_cellP_t5_21_62 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t6_25_32 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t8_36_64 x F) : WallE_cellP_t6_25_32 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t6_25_32 (Sym.sym24 F)) (wall_cellP_t8_36_64 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t6_35_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t8_34_46 x F) : WallE_cellP_t6_35_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t6_35_52 (Sym.sym24 F)) (wall_cellP_t8_34_46 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t7_26_32 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t7_36_62 x F) : WallE_cellP_t7_26_32 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t7_26_32 (Sym.sym24 F)) (wall_cellP_t7_36_62 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t7_36_62 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t7_26_32 x F) : WallE_cellP_t7_36_62 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t7_36_62 (Sym.sym24 F)) (wall_cellP_t7_26_32 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t8_34_46 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t6_35_52 x F) : WallE_cellP_t8_34_46 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t8_34_46 (Sym.sym24 F)) (wall_cellP_t6_35_52 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cellP_t8_36_64 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cellP_t6_25_32 x F) : WallE_cellP_t8_36_64 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cellP (by decide) (by decide) (wall_cellP_t8_36_64 (Sym.sym24 F)) (wall_cellP_t6_25_32 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t0_10_21 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t1_10_61 x F) : WallE_cell046125_t0_10_21 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t0_10_21 (Sym.sym24 F)) (wall_cell046125_t1_10_61 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t0_12_20 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t1_16_60 x F) : WallE_cell046125_t0_12_20 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t0_12_20 (Sym.sym24 F)) (wall_cell046125_t1_16_60 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t1_10_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t0_10_21 x F) : WallE_cell046125_t1_10_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t1_10_61 (Sym.sym24 F)) (wall_cell046125_t0_10_21 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t1_16_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t0_12_20 x F) : WallE_cell046125_t1_16_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t1_16_60 (Sym.sym24 F)) (wall_cell046125_t0_12_20 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t2_02_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t4_06_40 x F) : WallE_cell046125_t2_02_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t2_02_50 (Sym.sym24 F)) (wall_cell046125_t4_06_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t2_20_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t4_46_60 x F) : WallE_cell046125_t2_20_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t2_20_52 (Sym.sym24 F)) (wall_cell046125_t4_46_60 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_04_30 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_05_30 x F) : WallE_cell046125_t3_04_30 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_04_30 (Sym.sym24 F)) (wall_cell046125_t3_05_30 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_04_35 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_05_34 x F) : WallE_cell046125_t3_04_35 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_04_35 (Sym.sym24 F)) (wall_cell046125_t3_05_34 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_05_30 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_04_30 x F) : WallE_cell046125_t3_05_30 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_05_30 (Sym.sym24 F)) (wall_cell046125_t3_04_30 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_05_34 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_04_35 x F) : WallE_cell046125_t3_05_34 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_05_34 (Sym.sym24 F)) (wall_cell046125_t3_04_35 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_43 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_53 x F) : WallE_cell046125_t3_30_43 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_43 (Sym.sym24 F)) (wall_cell046125_t3_30_53 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_54 x F) : WallE_cell046125_t3_30_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_45 (Sym.sym24 F)) (wall_cell046125_t3_30_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_43 x F) : WallE_cell046125_t3_30_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_53 (Sym.sym24 F)) (wall_cell046125_t3_30_43 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_30_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_30_45 x F) : WallE_cell046125_t3_30_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_30_54 (Sym.sym24 F)) (wall_cell046125_t3_30_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_34_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_35_50 x F) : WallE_cell046125_t3_34_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_34_40 (Sym.sym24 F)) (wall_cell046125_t3_35_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_34_45 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_35_54 x F) : WallE_cell046125_t3_34_45 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_34_45 (Sym.sym24 F)) (wall_cell046125_t3_35_54 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_34_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_35_40 x F) : WallE_cell046125_t3_34_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_34_50 (Sym.sym24 F)) (wall_cell046125_t3_35_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_35_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_34_50 x F) : WallE_cell046125_t3_35_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_35_40 (Sym.sym24 F)) (wall_cell046125_t3_34_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_35_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_34_40 x F) : WallE_cell046125_t3_35_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_35_50 (Sym.sym24 F)) (wall_cell046125_t3_34_40 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_35_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_34_45 x F) : WallE_cell046125_t3_35_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_35_54 (Sym.sym24 F)) (wall_cell046125_t3_34_45 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_40_53 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_43_50 x F) : WallE_cell046125_t3_40_53 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_40_53 (Sym.sym24 F)) (wall_cell046125_t3_43_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_40_54 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_45_50 x F) : WallE_cell046125_t3_40_54 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_40_54 (Sym.sym24 F)) (wall_cell046125_t3_45_50 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_43_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_40_53 x F) : WallE_cell046125_t3_43_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_43_50 (Sym.sym24 F)) (wall_cell046125_t3_40_53 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t3_45_50 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t3_40_54 x F) : WallE_cell046125_t3_45_50 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t3_45_50 (Sym.sym24 F)) (wall_cell046125_t3_40_54 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t4_06_40 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t2_02_50 x F) : WallE_cell046125_t4_06_40 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t4_06_40 (Sym.sym24 F)) (wall_cell046125_t2_02_50 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t4_46_60 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t2_20_52 x F) : WallE_cell046125_t4_46_60 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t4_46_60 (Sym.sym24 F)) (wall_cell046125_t2_20_52 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t5_21_62 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t5_26_61 x F) : WallE_cell046125_t5_21_62 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t5_21_62 (Sym.sym24 F)) (wall_cell046125_t5_26_61 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t5_26_61 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t5_21_62 x F) : WallE_cell046125_t5_26_61 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t5_26_61 (Sym.sym24 F)) (wall_cell046125_t5_21_62 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t6_25_32 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t8_36_64 x F) : WallE_cell046125_t6_25_32 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t6_25_32 (Sym.sym24 F)) (wall_cell046125_t8_36_64 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t6_35_52 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t8_34_46 x F) : WallE_cell046125_t6_35_52 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t6_35_52 (Sym.sym24 F)) (wall_cell046125_t8_34_46 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t8_34_46 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t6_35_52 x F) : WallE_cell046125_t8_34_46 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t8_34_46 (Sym.sym24 F)) (wall_cell046125_t6_35_52 F)
    (Or.inl ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma twin_sd_cell046125_t8_36_64 {F : S0xFac 9 s0x_S24 x}
    (h : WallE_cell046125_t6_25_32 x F) : WallE_cell046125_t8_36_64 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine (wallE_selfDual_iff F cell046125 (by decide) (by decide) (wall_cell046125_t8_36_64 (Sym.sym24 F)) (wall_cell046125_t6_25_32 F)
    (Or.inr ⟨rfl, rfl⟩) (fun w => cellWallOf_fac_sym_iff (by decide) (by decide) w)
    (fun _ hc _ _ hrim => cellRhoOf (Sym.sym24 F) cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)
    (fun _ hc _ _ hrim => cellRhoOf F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc hrim)).2 h

private lemma allWallE2_twin_of_allWallE2S {F : S0xFac 9 s0x_S24 x}
    (h : AllWallE2S x F) : AllWallE2 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  obtain ⟨h1, hsym⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.1.1
    · exact hsym.1.2.1
    · exact hsym.1.2.2.1
    · exact hsym.1.2.2.2.1
    · exact hsym.1.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.1
    · exact hsym.2.1.1
    · exact hsym.2.1.2.1
    · exact hsym.2.1.2.2.1
    · exact hsym.2.1.2.2.2.1
    · exact hsym.2.1.2.2.2.2.1
    · exact hsym.2.2.1.1
    · exact hsym.2.2.1.2.1
    · exact hsym.2.2.1.2.2.1
    · exact hsym.2.2.1.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.1.1
    · exact hsym.2.2.2.1.2.1
    · exact hsym.2.2.2.1.2.2.1
    · exact hsym.2.2.2.1.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.1
    · exact hsym.2.2.2.2.1.2.1
    · exact hsym.2.2.2.2.1.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.1
    · exact hsym.2.2.2.2.2.1.2.1
    · exact hsym.2.2.2.2.2.1.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact twin_sd_cellB0_t0_10_20 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t1_10_60 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t2_20_50 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_34 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_40 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_50 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_34_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_40_50 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t4_40_60 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t5_21_61 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t6_25_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t8_34_64 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact hsym.2.2.2.2.2.2.1.1
    · exact hsym.2.2.2.2.2.2.1.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
    · exact twin_sd_cell0236_t0_01_21 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t1_01_61 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t2_50_52 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t4_40_46 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t6_52_53 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t8_43_46 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact hsym.2.2.2.2.2.2.2.1.1
    · exact hsym.2.2.2.2.2.2.2.1.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact twin_sd_cellP_t2_50_52 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_30_34 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_30_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_30_40 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_30_50 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_34_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_40_50 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t4_40_46 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t5_21_61 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t6_32_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t7_32_36 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t8_34_36 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact hsym.2.2.2.2.2.2.2.2.1.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact twin_sd_cell046125_t2_50_52 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_34 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_40 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_50 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_34_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_40_50 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t4_40_46 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t5_21_61 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t6_32_35 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    · exact twin_sd_cell046125_t8_34_36 (h1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.1.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.1.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.1.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact twin_sd_cellB0_t0_10_21 (h1.2.2.2.2.2.2.2.1.2.2.1)
    · exact twin_sd_cellB0_t0_12_20 (h1.2.2.2.2.2.2.2.1.2.2.2.1)
    · exact twin_sd_cellB0_t1_10_61 (h1.2.2.2.2.2.2.2.1.1)
    · exact twin_sd_cellB0_t1_16_60 (h1.2.2.2.2.2.2.2.1.2.1)
    · exact twin_sd_cellB0_t2_20_52 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t2_25_50 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_04_30 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_04_35 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_05_30 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_05_34 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_43 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_45 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_53 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_30_54 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_34_40 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_34_45 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_34_50 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_35_40 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_35_50 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_35_54 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_40_53 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_40_54 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_43_50 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t3_45_50 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t4_40_64 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t4_46_60 (h1.2.2.2.2.2.2.2.1.2.2.2.2.1)
    · exact twin_sd_cellB0_t5_21_62 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t5_26_61 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t6_23_35 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t6_25_32 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    · exact twin_sd_cellB0_t8_34_63 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellB0_t8_36_64 (h1.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact twin_sd_cell0236_t0_01_20 (h1.2.2.2.2.2.2.2.2.2.1.2.2.1)
    · exact twin_sd_cell0236_t0_02_21 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.1)
    · exact twin_sd_cell0236_t1_01_60 (h1.2.2.2.2.2.2.2.2.2.1.1)
    · exact twin_sd_cell0236_t1_06_61 (h1.2.2.2.2.2.2.2.2.2.1.2.1)
    · exact twin_sd_cell0236_t2_02_50 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t2_20_52 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_03_40 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_03_50 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_04_35 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_04_45 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_05_34 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_05_54 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_30_43 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_30_53 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_34_45 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_35_54 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_40_43 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_40_53 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_43_50 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t3_50_53 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t4_06_40 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1)
    · exact twin_sd_cell0236_t4_46_60 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t6_23_52 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    · exact twin_sd_cell0236_t6_32_53 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t7_26_32 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t7_32_36 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t7_36_62 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t8_36_43 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell0236_t8_46_63 (h1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact twin_sd_cellP_t2_02_50 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t2_20_52 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_04_30 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1)
    · exact twin_sd_cellP_t3_04_35 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_05_30 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1)
    · exact twin_sd_cellP_t3_05_34 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1)
    · exact twin_sd_cellP_t3_30_43 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_30_45 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_30_53 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_30_54 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_34_40 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_34_45 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_34_50 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_35_40 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_35_50 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_35_54 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_40_53 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_40_54 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_43_50 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t3_45_50 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t4_06_40 (h1.2.2.2.2.2.2.2.2.2.2.2.1.1)
    · exact twin_sd_cellP_t4_46_60 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.1)
    · exact twin_sd_cellP_t5_21_62 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t5_26_61 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t6_25_32 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    · exact twin_sd_cellP_t6_35_52 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t7_26_32 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t7_36_62 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t8_34_46 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cellP_t8_36_64 (h1.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hsym.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact twin_sd_cell046125_t0_10_21 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t0_12_20 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t1_10_61 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t1_16_60 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t2_02_50 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t2_20_52 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_04_30 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_04_35 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_05_30 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_05_34 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_43 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_45 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_53 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_30_54 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_34_40 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_34_45 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_34_50 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_35_40 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_35_50 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_35_54 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_40_53 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_40_54 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_43_50 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t3_45_50 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t4_06_40 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t4_46_60 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t5_21_62 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t5_26_61 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t6_25_32 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    · exact twin_sd_cell046125_t6_35_52 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t8_34_46 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact twin_sd_cell046125_t8_36_64 (h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

/-- **Equivalence:** the one-sided `1023`-wall conjunction `AllWallE2S x F` is equivalent to
`AllWallE2` on both `x` and its `π_24` twin. -/
theorem allWallE2S_iff (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) :
    AllWallE2S x F ↔ AllWallE2 x F ∧ AllWallE2 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  constructor
  · intro h
    exact ⟨h.1, allWallE2_twin_of_allWallE2S h⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.1
      · exact h2.1.2.1
      · exact h2.1.2.2.1
      · exact h2.1.2.2.2.1
      · exact h2.1.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.1
      · exact h2.2.1.1
      · exact h2.2.1.2.1
      · exact h2.2.1.2.2.1
      · exact h2.2.1.2.2.2.1
      · exact h2.2.1.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.1
      · exact h2.2.2.1.2.1
      · exact h2.2.2.1.2.2.1
      · exact h2.2.2.1.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.1
      · exact h2.2.2.2.1.2.1
      · exact h2.2.2.2.1.2.2.1
      · exact h2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.1
      · exact h2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.1
      · exact h2.2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.1
      · exact h2.2.2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **Hole fact:** at a `HoleLeaf`, `AllWallE2S x F` holds. -/
theorem holeLeaf_allWallE2S {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2S x F :=
  (allWallE2S_iff x F).2 ⟨holeLeaf_allWallE2 hF, holeLeaf_allWallE2_twin hF⟩

/-- **[OPEN] `CellCoverEmptyAll2S L`** (one-sided, `1023` walls): on `CbarIn` and `OB1`, with
`AllWallE2S x F`, the point is not in the cell-cover residue of `L`. -/
def CellCoverEmptyAll2S (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → AllWallE2S x F →
    ¬ CellCoverResidue L x F

/-- `CellCoverEmptyAll2S L` is equivalent to `CellCoverEmptyAll2 L`. -/
theorem cellCoverEmptyAll2S_iff_cellCoverEmptyAll2 (L : List Cell24) :
    CellCoverEmptyAll2S L ↔ CellCoverEmptyAll2 L := by
  constructor
  · intro h x F hC hO hA hA'
    exact h x F hC hO ((allWallE2S_iff x F).2 ⟨hA, hA'⟩)
  · intro h x F hC hO hS
    have h12 := (allWallE2S_iff x F).1 hS
    exact h x F hC hO h12.1 h12.2

/-- `CellCoverEmptyAll2S L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmptyAll2S {L : List Cell24} (hN : CellCoverEmptyAll2S L)
    (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_allWallE2S h) (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmptyAll2S L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmptyAll2S {L : List Cell24} (hN : CellCoverEmptyAll2S L) : OpenOB1 :=
  fun x F hO hF => not_holeLeaf_of_cellCoverEmptyAll2S hN x F hO (holeLeaf_of_holeFull hF)

end Minimality.T24.Cell
