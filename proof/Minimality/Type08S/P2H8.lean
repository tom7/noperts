module

public import Minimality.Type08S.P2H7
public import Minimality.Type08S.P2FIN1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H8: the external hypotheses (Lemma E (iii) weak; the SC2 cases) and N2's `K_c`

* `LemE3 x' x f r g`: Lemma E (iii), weak: `x`, `x'` weakly on opposite sides of `Π' = aff(f, r, g)`
  (`det3 (r-f) (g-f) (x-f) · det3 (r-f) (g-f) (x'-f) ≤ 0`).  `lemEF_of_3`: its frame form `LemEF`.
* `SC2N2`, `SC2Kb`, `SC2K2`: what the SC2 package must prove (chord end at `f`, parallel set), in the canonical
  frame of each closing (as `frame_N2`, `frame_Kb`, `frame_K2` give it), with robustness.
* `pers_N2`: N2's `K_c` with a persistent HDN.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Lemma E (iii), weak** (sp08d §4.1), for the closing `(x, f, r, g)` with other apex `x'`. -/
def LemE3 (xp x f r g : ℝ³) : Prop :=
  det3 (r - f) (g - f) (x - f) * det3 (r - f) (g - f) (xp - f) ≤ 0

theorem lemEF_of_3 (hF : Fr e1 e2 e3) (O : ℝ³) {κ L zf Xr Yr zr Xg Yg zg : ℝ} (hY : Yr = Yg) (hYr : 0 < Yr)
    (h : LemE3 O (O + pc e1 e2 e3 0 0 κ) (O + pc e1 e2 e3 L 0 zf) (O + pc e1 e2 e3 Xr Yr zr)
      (O + pc e1 e2 e3 Xg Yg zg)) : LemEF 0 L κ zf Xr zr Xg zg := by
  unfold LemE3 at h
  have hOd : O - (O + pc e1 e2 e3 L 0 zf) = pc e1 e2 e3 (0 - L) (0 - 0) (0 - zf) := by
    simp only [pc]; module
  rw [hOd] at h
  simp only [add_sub_add_left_eq_sub, pc_sub, det3_pc hF] at h
  subst hY
  unfold LemEF
  have key : Yr ^ 2 * (((Xr - Xg) * (κ - zf) + L * (zr - zg)) * ((Xr - Xg) * (0 - zf) + L * (zr - zg))) ≤ 0 := by
    convert h using 1; ring
  by_contra hc; push_neg at hc
  nlinarith [mul_pos (pow_pos hYr 2) hc]

/-- **SC2 cases of N2's `K_c`** (chord end at `f`, parallel set), canonical frame (`x' = a'`, `x = c`, `f = b`,
`r = c'`, `g = b'`). -/
def SC2N2 (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → c - a' = κ • e3 → ⟪b - a', e2⟫ = 0 →
    0 < ⟪b - a', e1⟫ → 0 < ⟪c' - a', e2⟫ →
    Rob4 κ ⟪b - a', e3⟫ ⟪c' - a', e3⟫ ⟪b' - a', e3⟫ →
    (CEf5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫
        ⟪b' - a', e3⟫ ∨
      Par5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫
        ⟪b' - a', e3⟫) →
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))

/-- **SC2 cases of T4's `K_b`** (`x' = d`, `x = b`, `f = c`, `r = b'`, `g = c'`). -/
def SC2Kb (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → b - d = κ • e3 → ⟪c - d, e2⟫ = 0 →
    0 < ⟪c - d, e1⟫ → 0 < ⟪b' - d, e2⟫ →
    Rob4 κ ⟪c - d, e3⟫ ⟪b' - d, e3⟫ ⟪c' - d, e3⟫ →
    (CEf5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫
        ⟪c' - d, e3⟫ ∨
      Par5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫
        ⟪c' - d, e3⟫) →
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))

/-- **SC2 cases of T4's `K_2`** (`x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`). -/
def SC2K2 (a a' b b' c c' d : ℝ³) : Prop :=
  ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → d - b = κ • e3 → ⟪c' - b, e2⟫ = 0 →
    0 < ⟪c' - b, e1⟫ → 0 < ⟪b' - b, e2⟫ →
    Rob4 κ ⟪c' - b, e3⟫ ⟪b' - b, e3⟫ ⟪c - b, e3⟫ →
    (CEf5 ⟪c' - b, e1⟫ κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫
        ⟪c - b, e3⟫ ∨
      Par5 ⟪c' - b, e1⟫ κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫
        ⟪c - b, e3⟫) →
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))

set_option maxHeartbeats 4000000 in
/-- **N2 `K_c` with a persistent HDN** (frame form of `close_hdn_pers`, N2 case). -/
theorem pers_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hce : c - a' = κ • e3)
    (hb2 : ⟪b - a', e2⟫ = 0) (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪b - a', e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' (σ j) - quad c b c' b' (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' a_ - quad c b c' b' (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad c b c' b' (σ i), u⟫))
    (hp : ¬ NoPersistHDN (fun i => quad c b c' b' (σ i)) u e)
    (hLE : LemE3 a' c b c' b') (hSC2 : SC2N2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hcr, hcg, hXd0, hXdL, hYa, hfr, hrg, hgx⟩ := pic_N2 N hreg hF hκ hce hb2 hL hr
  obtain ⟨hYg, hYd, hDp⟩ := extra_N2 N hreg hF hκ hce hb2 hL hr
  have hside := side_pos hF N.F.a'bc'.hN (xp := a') (x := c) (fp := b) (p := d) (κ := κ)
    N.F.a'bc'.hP N.F.a'bc'.hQ (N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) N.hd.a'bc'
    hce hb2 hYd hL
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : c = a' + pc e1 e2 e3 0 0 κ := by
    rw [← pc_smul_e3 hF, ← hce]; abel
  have hxf : b = a' + pc e1 e2 e3 ⟪b - a', e1⟫ 0 ⟪b - a', e3⟫ := by
    have := pc_coords hF a' b; rw [hb2] at this; exact this
  have hxr : c' = a' + pc e1 e2 e3 ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ := pc_coords hF a' c'
  have hxg : b' = a' + pc e1 e2 e3 ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ := pc_coords hF a' b'
  have hxp : d = a' + pc e1 e2 e3 ⟪d - a', e1⟫ 0 ⟪d - a', e3⟫ := by
    have := pc_coords hF a' d; rw [hYd] at this; exact this
  have hxw : a = a' + pc e1 e2 e3 ⟪a - a', e1⟫ ⟪a - a', e2⟫ ⟪a - a', e3⟫ := pc_coords hF a' a
  have hP : ∀ j, quad c b c' b' j = Qg e1 e2 e3 a' κ ⟪b - a', e1⟫ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫
      ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ (id j) := by
    intro j
    simp only [Qg, id, fpt]
    rw [← hxx, ← hxf, ← hxr, ← hxg]
  -- `a` is not on the 3-D line `b b'`
  have hnc : ¬ ((⟪b' - a', e1⟫ - ⟪b - a', e1⟫) * ⟪a - a', e2⟫ - ⟪b' - a', e2⟫ * (⟪a - a', e1⟫ - ⟪b - a', e1⟫) = 0 ∧
      ⟪b' - a', e2⟫ * (⟪a - a', e3⟫ - ⟪b - a', e3⟫) - (⟪b' - a', e3⟫ - ⟪b - a', e3⟫) * ⟪a - a', e2⟫ = 0) := by
    rintro ⟨hD0, hW0⟩
    have iexp : ∀ v : ℝ³, ⟪N.F.abc'.N, v⟫ = ⟪v, e1⟫ * ⟪N.F.abc'.N, e1⟫ + ⟪v, e2⟫ * ⟪N.F.abc'.N, e2⟫ +
        ⟪v, e3⟫ * ⟪N.F.abc'.N, e3⟫ := by
      intro v
      conv_lhs => rw [hF.expand v]
      simp only [inner_add_right, real_inner_smul_right]
    have k1 := N.F.abc'.hN a b
    have k2 := N.F.abc'.hN b' b
    rw [N.F.abc'.hP, N.F.abc'.hQ] at k1
    rw [N.F.abc'.hQ] at k2
    have k3 := N.F.abc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
    rw [iexp, inner_diff a b a', inner_diff a b a', inner_diff a b a'] at k1
    rw [iexp, inner_diff b' b a', inner_diff b' b a', inner_diff b' b a'] at k2
    rw [hb2] at k1 k2
    have k4 : ⟪b' - a', e2⟫ * (0 - 0) = ⟪a - a', e2⟫ * (N.F.abc'.f b' - 0) := by
      rw [k1, k2]
      linear_combination (-⟪N.F.abc'.N, e1⟫) * hD0 + ⟪N.F.abc'.N, e3⟫ * hW0
    nlinarith [mul_pos hYa (neg_pos.2 k3)]
  set E : Finset ℝ³ := {a' + pc e1 e2 e3 ⟪d - a', e1⟫ 0 ⟪d - a', e3⟫,
    a' + pc e1 e2 e3 ⟪a - a', e1⟫ ⟪a - a', e2⟫ ⟪a - a', e3⟫} with hEdef
  set V5 := rim5 e1 e2 e3 a' ⟪b - a', e1⟫ 0 κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫
    ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ E with hV5
  have m1 : a' + pc e1 e2 e3 0 0 0 ∈ V5 := by simp [hV5, rim5]
  have m2 : a' + pc e1 e2 e3 ⟪b - a', e1⟫ 0 ⟪b - a', e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m3 : a' + pc e1 e2 e3 ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m4 : a' + pc e1 e2 e3 ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ ∈ V5 := by simp [hV5, rim5]
  have hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V5 (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y := by
    filter_upwards [triCert_quad hF a' V5 (σ := κ) hκ m1 m2 m3 m4 hL hYg hcr hYa hfr hrg hgx hnc]
      with s hs y hy
    rw [hEdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · refine triCert_midF hF a' V5 hL hYg hXd0 hXdL m1 m2 m4 ?_
      nlinarith [hside]
    · exact hs
  have hLem : ⟪c' - a', e2⟫ = ⟪b' - a', e2⟫ → LemEF 0 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫
      ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e3⟫ := by
    intro hY
    refine lemEF_of_3 hF a' hY hr ?_
    rw [← hxx, ← hxf, ← hxr, ← hxg]; exact hLE
  rcases pers_frame hF a' E hκ hκv0 hL hr hYg hcr hcg hE hLem (quad c b c' b') id (fun _ => rfl) hP hk3 σ u e
      hu he hcyc hleft hz hp with hR | ⟨hrob, hcase⟩
  · simp only [rim5, hEdef] at hR
    rw [show a' + pc e1 e2 e3 0 0 0 = a' by simp [pc], ← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at hR
    have hset : insert d ({a, a', b, b', c, c'} : Finset ℝ³) = ({a', c, b, c', b'} : Finset ℝ³) ∪ {d, a} := by
      ext y; simp only [mem_insert, mem_singleton, mem_union]
      constructor
      · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp only [true_or, or_true]
      · rintro ((h | h | h | h | h) | (h | h)) <;> subst h <;> simp only [true_or, or_true]
    rw [hset]; exact hR
  · exact hSC2 e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hcase

end Type08Sp
end Minimality
