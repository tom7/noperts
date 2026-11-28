module

public import Minimality.Type24Wall3Cover

/-!
# Type24CellWallGen: generic `CellWall` constructor from combinatorial `s0x_S24` data (Task GA)

* `cellWallOf`: builds a `CellWall F c` from combinatorial data alone (`t_wall`, `forms`,
  corner vertices `a0, b0, a1, b1`, push vertices `vp, vq`, and `wallOK ... = true` by `decide`).
* `p126Wall'`, `cp236Wall'`, `c0536Wall'`, `c016Wall'`: 1-line re-derivations of the four walls
  from `Type24P126Cover` and `Type24Wall3Cover`, together with `WallE` equivalences and
  `_cert_or_E'` theorems.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## Generic combinatorial wall checker and constructor -/

/-- Decidable check that `[x a0 - x b0, x a1 - x b1]` with push `x vp - x vq` and explicit facet
forms `forms` forms a valid `CellWall` of `c` along wall facet `t_wall`:
- `t_wall` vanishes on both endpoints and is pushed strictly into `c.U` (or out of `c.U`);
- every `(t, sgn) ∈ forms` is off `t_wall` and has `sgn = decide (t ∈ U)`;
- every remaining facet `t ≠ t_wall` is automatic on `(a0, b0), (a1, b1)` by `comb_pos` / `comb_neg`. -/
def wallOK (U : Finset (Fin 9)) (t_wall : Fin 9) (forms : List (Fin 9 × Bool))
    (a0 b0 a1 b1 vp vq : Fin 7) : Bool :=
  decide (a0 ∈ s0x_S24 t_wall ∧ b0 ∈ s0x_S24 t_wall ∧ a1 ∈ s0x_S24 t_wall ∧ b1 ∈ s0x_S24 t_wall) &&
  (if t_wall ∈ U then decide (vp ∈ s0x_S24 t_wall ∧ vq ∉ s0x_S24 t_wall)
   else decide (vp ∉ s0x_S24 t_wall ∧ vq ∈ s0x_S24 t_wall)) &&
  forms.all (fun p => decide (p.1 ≠ t_wall) && decide (p.2 = decide (p.1 ∈ U))) &&
  (List.finRange 9).all (fun t =>
    if t == t_wall then true
    else if forms.any (fun p => p.1 == t) then true
    else if t ∈ U then
      decide (a0 ∈ s0x_S24 t ∧ a1 ∈ s0x_S24 t) &&
      (decide (b0 ∉ s0x_S24 t) || decide (b1 ∉ s0x_S24 t))
    else
      decide (b0 ∈ s0x_S24 t ∧ b1 ∈ s0x_S24 t) &&
      (decide (a0 ∉ s0x_S24 t) || decide (a1 ∉ s0x_S24 t)))

private lemma fac_nonpos (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v : Fin 7) : F.f t (x v) ≤ 0 := by
  by_cases hv : v ∈ s0x_S24 t
  · exact (F.zero t v hv).le
  · exact (F.neg t v hv).le

private lemma wall_diff_nonneg (F : S0xFac 9 s0x_S24 x) (t : Fin 9) {a b : Fin 7}
    (ha : a ∈ s0x_S24 t) : 0 ≤ F.f t (x a) - F.f t (x b) := by
  rw [F.zero t a ha, zero_sub]
  exact neg_nonneg.2 (fac_nonpos F t b)

private lemma wall_diff_pos (F : S0xFac 9 s0x_S24 x) (t : Fin 9) {a b : Fin 7}
    (ha : a ∈ s0x_S24 t) (hb : b ∉ s0x_S24 t) : 0 < F.f t (x a) - F.f t (x b) := by
  rw [F.zero t a ha, zero_sub]
  exact neg_pos.2 (F.neg t b hb)

private lemma wall_diff_nonpos (F : S0xFac 9 s0x_S24 x) (t : Fin 9) {a b : Fin 7}
    (hb : b ∈ s0x_S24 t) : F.f t (x a) - F.f t (x b) ≤ 0 := by
  rw [F.zero t b hb, sub_zero]
  exact fac_nonpos F t a

private lemma wall_diff_neg (F : S0xFac 9 s0x_S24 x) (t : Fin 9) {a b : Fin 7}
    (ha : a ∉ s0x_S24 t) (hb : b ∈ s0x_S24 t) : F.f t (x a) - F.f t (x b) < 0 := by
  rw [F.zero t b hb, sub_zero]
  exact F.neg t a ha

/-- **Generic `CellWall` constructor** from combinatorial `s0x_S24` data. -/
noncomputable def cellWallOf (F : S0xFac 9 s0x_S24 x) (c : Cell24)
    (t_wall : Fin 9) (forms : List (Fin 9 × Bool)) (a0 b0 a1 b1 vp vq : Fin 7)
    (hok : wallOK c.U t_wall forms a0 b0 a1 b1 vp vq = true) : CellWall F c where
  n := forms.length
  E0 := x a0 - x b0
  E1 := x a1 - x b1
  v := x vp - x vq
  fac := fun i => let p := forms[i.1]; if p.2 then F.N p.1 else -F.N p.1
  face := by
    intro l hl0 hl1 hf
    simp only [wallOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
    obtain ⟨⟨⟨htw_zero, htw_push⟩, hforms⟩, hauto⟩ := hok
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x a0 - x b0) + l • (x a1 - x b1)⟫ =
        (1 - l) * (F.f t (x a0) - F.f t (x b0)) + l * (F.f t (x a1) - F.f t (x b1)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have hwall_zero : ⟪F.N t_wall, (1 - l) • (x a0 - x b0) + l • (x a1 - x b1)⟫ = 0 := by
      rw [hNr, F.zero t_wall a0 htw_zero.1, F.zero t_wall b0 htw_zero.2.1,
        F.zero t_wall a1 htw_zero.2.2.1, F.zero t_wall b1 htw_zero.2.2.2]
      ring
    have hfacet : ∀ t : Fin 9,
        (t ∈ c.U → 0 < ⟪F.N t, (1 - l) • (x a0 - x b0) + l • (x a1 - x b1)⟫ ∨
          (⟪F.N t, (1 - l) • (x a0 - x b0) + l • (x a1 - x b1)⟫ = 0 ∧ 0 < ⟪F.N t, x vp - x vq⟫)) ∧
        (t ∉ c.U → ⟪F.N t, (1 - l) • (x a0 - x b0) + l • (x a1 - x b1)⟫ < 0 ∨
          (⟪F.N t, (1 - l) • (x a0 - x b0) + l • (x a1 - x b1)⟫ = 0 ∧ ⟪F.N t, x vp - x vq⟫ < 0)) := by
      intro t
      by_cases htw : t = t_wall
      · subst htw
        constructor
        · intro htU
          right
          simp only [htU, ↓reduceIte, decide_eq_true_eq] at htw_push
          exact ⟨hwall_zero, by rw [F.inner_sub]; exact wall_diff_pos F t htw_push.1 htw_push.2⟩
        · intro htU
          right
          simp only [htU, ↓reduceIte, decide_eq_true_eq] at htw_push
          exact ⟨hwall_zero, by rw [F.inner_sub]; exact wall_diff_neg F t htw_push.1 htw_push.2⟩
      · by_cases hany : forms.any (fun p => p.1 == t) = true
        · rw [List.any_eq_true] at hany
          obtain ⟨p, hp_mem, hp_eq⟩ := hany
          have ht_eq : p.1 = t := beq_iff_eq.1 hp_eq
          obtain ⟨i, hlt, hi⟩ := List.mem_iff_getElem.1 hp_mem
          have hfi := hf ⟨i, hlt⟩
          have hfp := hforms p hp_mem
          have hp2 : p.2 = decide (t ∈ c.U) := by rw [← ht_eq]; exact hfp.2
          have hget : forms[i] = p := hi
          constructor
          · intro htU
            left
            have hp2t : p.2 = true := by rw [hp2]; exact decide_eq_true htU
            simpa only [hget, hp2t, ↓reduceIte, ht_eq] using hfi
          · intro htU
            left
            have hp2f : p.2 = false := by rw [hp2]; exact decide_eq_false htU
            simp only [hget, hp2f, Bool.false_eq_true, ↓reduceIte, ht_eq, inner_neg_left] at hfi
            linarith
        · have ht_fin := hauto t (List.mem_finRange t)
          have htw_beq : (t == t_wall) = false := beq_false_of_ne htw
          have hany_f : forms.any (fun p => p.1 == t) = false := Bool.eq_false_iff.2 hany
          simp only [htw_beq, Bool.false_eq_true, ↓reduceIte, hany_f] at ht_fin
          constructor
          · intro htU
            left
            simp only [htU, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ht_fin
            rw [hNr]
            refine comb_pos hl0 hl1 (wall_diff_nonneg F t ht_fin.1.1)
              (wall_diff_nonneg F t ht_fin.1.2) ?_
            rcases ht_fin.2 with hb0 | hb1
            · exact Or.inl (wall_diff_pos F t ht_fin.1.1 hb0)
            · exact Or.inr (wall_diff_pos F t ht_fin.1.2 hb1)
          · intro htU
            left
            simp only [htU, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
              decide_eq_true_eq] at ht_fin
            rw [hNr]
            refine comb_neg hl0 hl1 (wall_diff_nonpos F t ht_fin.1.1)
              (wall_diff_nonpos F t ht_fin.1.2) ?_
            rcases ht_fin.2 with ha0 | ha1
            · exact Or.inl (wall_diff_neg F t ha0 ht_fin.1.1)
            · exact Or.inr (wall_diff_neg F t ha1 ht_fin.1.2)
    exact ⟨fun t ht => (hfacet t).1 ht, fun t ht => (hfacet t).2 ht⟩

/-! ## `WallE` congruence for matching walls -/

private lemma segLet_congr {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {f₁ : ι₁ → ℝ³} {f₂ : ι₂ → ℝ³} {E0 E1 : ℝ³}
    (h₁₂ : ∀ i₁, ∃ i₂, f₁ i₁ = f₂ i₂) (h₂₁ : ∀ i₂, ∃ i₁, f₂ i₂ = f₁ i₁) :
    SegLet f₁ E0 E1 ↔ SegLet f₂ E0 E1 := by
  rw [segLet_iff, segLet_iff]
  constructor
  · rintro ⟨l, hl0, hl1, hall⟩
    refine ⟨l, hl0, hl1, fun i₂ => ?_⟩
    obtain ⟨i₁, hi⟩ := h₂₁ i₂
    rw [hi]; exact hall i₁
  · rintro ⟨l, hl0, hl1, hall⟩
    refine ⟨l, hl0, hl1, fun i₁ => ?_⟩
    obtain ⟨i₂, hi⟩ := h₁₂ i₁
    rw [hi]; exact hall i₂

/-- Two `CellWall`s with the same endpoints and matching `fac` vectors (up to `Fin` index cast)
have equivalent `WallE` conditions. -/
theorem wallE_congr {F : S0xFac 9 s0x_S24 x} {c : Cell24} {W₁ W₂ : CellWall F c} {s : ℝ}
    (hn : W₁.n = W₂.n) (hE0 : W₁.E0 = W₂.E0) (hE1 : W₁.E1 = W₂.E1)
    (hfac : ∀ i : Fin W₁.n, W₁.fac i = W₂.fac (Fin.cast hn i)) :
    WallE F c W₁ s ↔ WallE F c W₂ s := by
  have h12 : ∀ i₁ : Fin W₁.n, ∃ i₂ : Fin W₂.n, W₁.fac i₁ = W₂.fac i₂ :=
    fun i₁ => ⟨Fin.cast hn i₁, hfac i₁⟩
  have h21 : ∀ i₂ : Fin W₂.n, ∃ i₁ : Fin W₁.n, W₂.fac i₂ = W₁.fac i₁ :=
    fun i₂ => ⟨Fin.cast hn.symm i₂, (hfac (Fin.cast hn.symm i₂)).symm ▸ by simp⟩
  have hsum : ∀ {γ : Type} [Fintype γ] (g : γ → ℝ³),
      SegLet (Sum.elim W₁.fac g) W₁.E0 W₁.E1 ↔ SegLet (Sum.elim W₂.fac g) W₂.E0 W₂.E1 := by
    intro γ _ g
    rw [hE0, hE1]
    refine segLet_congr ?_ ?_
    · rintro (i₁ | j)
      · obtain ⟨i₂, hi⟩ := h12 i₁; exact ⟨Sum.inl i₂, hi⟩
      · exact ⟨Sum.inr j, rfl⟩
    · rintro (i₂ | j)
      · obtain ⟨i₁, hi⟩ := h21 i₂; exact ⟨Sum.inl i₁, hi⟩
      · exact ⟨Sum.inr j, rfl⟩
  simp only [WallE]
  constructor
  · rintro ⟨hR, hA⟩
    exact ⟨fun i0 L => (hsum _).2.mt (hR i0 L),
      fun a m σ h1 h2 h3 => (hsum _).2.mt (hA a m σ h1 h2 h3)⟩
  · rintro ⟨hR, hA⟩
    exact ⟨fun i0 L => (hsum _).1.mt (hR i0 L),
      fun a m σ h1 h2 h3 => (hsum _).1.mt (hA a m σ h1 h2 h3)⟩

/-! ## Re-derivation of the four walls from `cellWallOf` -/

/-- Generic `P.126` wall via `cellWallOf`. -/
noncomputable def p126Wall' (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 5 [(2, false), (4, false), (3, true), (6, true), (8, true)] 2 1 6 1 0 1 (by decide)

/-- Generic `C'.236` wall via `cellWallOf`. -/
noncomputable def cp236Wall' (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 7 [(0, false), (1, false), (2, false), (4, true)] 3 2 3 6 3 1 (by decide)

/-- Generic `0536.046` wall via `cellWallOf`. -/
noncomputable def c0536Wall' (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 4 [(0, false), (2, false), (5, false), (6, false), (7, false)] 4 0 4 6 0 1 (by decide)

/-- Generic `C.016` wall via `cellWallOf`. -/
noncomputable def c016Wall' (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 1 [(2, false), (3, true), (6, true), (7, false), (8, true)] 0 1 6 1 2 1 (by decide)

theorem wallE_p126Wall'_iff (F : S0xFac 9 s0x_S24 x) :
    WallE F cellP (p126Wall' F) (-det24 x) ↔ P126E x F :=
  wallE_congr rfl rfl rfl (fun i => by fin_cases i <;> rfl)

theorem wallE_cp236Wall'_iff (F : S0xFac 9 s0x_S24 x) :
    WallE F cellC' (cp236Wall' F) (sA x) ↔ Cp236E x F :=
  wallE_congr rfl rfl rfl (fun i => by fin_cases i <;> rfl)

theorem wallE_c0536Wall'_iff (F : S0xFac 9 s0x_S24 x) :
    WallE F cell0536 (c0536Wall' F) (sB x) ↔ C0536E x F :=
  wallE_congr rfl rfl rfl (fun i => by fin_cases i <;> rfl)

theorem wallE_c016Wall'_iff (F : S0xFac 9 s0x_S24 x) :
    WallE F cellC (c016Wall' F) (sA x) ↔ C016E x F :=
  wallE_congr rfl rfl rfl (fun i => by fin_cases i <;> rfl)

theorem p126_cert_or_E' (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ P126E x F := by
  rcases wall_cert_or_E F cellP (p126Wall' F) (fun _ hc _ _ hrim => cellP_rho F hc hrim) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((wallE_p126Wall'_iff F).1 h))

theorem cp236_cert_or_E' (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ Cp236E x F := by
  rcases wall_cert_or_E F cellC' (cp236Wall' F) (fun _ hc _ _ hrim => cellCp_rho F hc hrim) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((wallE_cp236Wall'_iff F).1 h))

theorem c0536_cert_or_E' (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ C0536E x F := by
  rcases wall_cert_or_E F cell0536 (c0536Wall' F) (fun _ hc _ _ hrim => cell0536_rho F hc hrim) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((wallE_c0536Wall'_iff F).1 h))

theorem c016_cert_or_E' (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ C016E x F := by
  rcases wall_cert_or_E F cellC (c016Wall' F) (fun _ hc _ _ hrim => cellC_rho F hc hrim) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((wallE_c016Wall'_iff F).1 h))

end Minimality.T24.Cell
