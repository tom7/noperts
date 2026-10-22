module

public import Minimality.Type21F1
public import Minimality.Type21Switch

@[expose] public section

/-!
# Type 21: Theorem 16.13, the cap-face class (`FEWER-FACES-PROOFS.md` §16.3)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`.

* **Theorem 16.13, normalized** — `cert_type21_capFace_norm`: Gale data of `O = K − 2` in
  the normalized cap-face class (`CapNorm`: `[3 0], [5 4], [6 1], [3 5] > 0`).  The cover:
  1. `05` or `46` a quad edge of `O` (either direction, all E-good): tier Q;
  2. else `1 → 3` a quad edge of `O`: tier H;
  3. else (the region R1: (F1)–(F6), derived here from the three non-quad conditions, the
     Plücker relations and the identities of `Type21Cover.lean`) if `δ_014(2) > δ_014(5)`:
     `Q` at `25` of `K − 6` (`cert_type21_step3`, with Lemma 16.11);
  4. else, if `0 → 4` is a quad edge of `K − 6` and `δ_014(2) < δ_014(5)`: F1
     (`cert_type21_F1`);
  5. else `Q` at `23` of `K − 6` (Lemma 16.12, `cert_type21_step5`), on `Σ` and on the
     half `H⁺` of the switch surface;
  6. on the half `H⁻` of the switch surface (`f₀₁₄(2) = f₀₁₄(5) < f₀₁₄(3)`): Theorem 16.30
     (`cert_type21_switch`, `Type21Switch.lean`).
  Special positions: `NoPlaneParallel` (it contains every tie `|[s x]| = |[s y]|` of a Gale
  comparison used: a tie is a segment parallel to a face plane, `facet_tie_det`), `GenPosTie`,
  `NoHDNEdges` (the edge views), and the special positions of `T1` at every direction of the
  line `014 ∩ 0256` (`T1Gen`).

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

/-- A segment `x y` on which a face function takes equal (nonzero) values is parallel to the
face plane. -/
theorem facet_tie_det {V : Finset ℝ³} {P Q R : ℝ³} (Fc : FacetFn V P Q R) {x y : ℝ³}
    (hx : Fc.f x ≠ 0) (hxy : Fc.f x = Fc.f y) : det3 (Q - P) (R - P) (y - x) = 0 := by
  have h1 : ⟪Fc.N, Q - P⟫ = 0 := by rw [← Fc.hN, Fc.hQ, Fc.hP, sub_self]
  have h2 : ⟪Fc.N, R - P⟫ = 0 := by rw [← Fc.hN, Fc.hR, Fc.hP, sub_self]
  have key := det3_mul_inner_eq (e := Q - P) (u := R - P) (w := y - x) (w' := x - P) h1 h2
  rw [← Fc.hN, ← Fc.hN, Fc.hP, hxy, sub_self, mul_zero, sub_zero] at key
  have : det3 (Q - P) (y - x) (R - P) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd (hxy ▸ h) hx
  rw [det3_swap23]; rw [this, neg_zero]

/-- **The special positions of `T1`** at a view `u` (the vertex crossing at `0` of `014`,
`0256`): `P(3)` is off the line `P(5) P(4)`, the ties of the rim `0, 5, 3, 4` are allowed ones
(`T1Tie`: those of `QuadTie`, or at most one tie and none along `0 − 4` if `0, 4` tie), and the
view satisfies `L` (for the old statement: no horizontal double normal of `K`). -/
def T1Gen (K : Finset ℝ³) (L : ℝ³ → Prop) (a a' b b' u : ℝ³) : Prop :=
  det3 (b - b') (a' - b') u ≠ 0 ∧ T1Tie K a a' b b' u ∧ L u

/-- **Theorem 16.13 (the cap-face class), normalized.**  `K = O ∪ {2}` of type 21
(`IsCap21`), Gale data `G` of `O = K − 2` in the normalized cap-face class (`CapNorm`).  Off
the special positions — no segment of `K` parallel to a plane through three other points
(`NoPlaneParallel`), `GenPosTie`, and the special positions of `T1` at the views along the line
`014 ∩ 0256` (`T1Gen`: the far side, the ties of `T1Tie`, the views in `L`) — `K` has a rim
certificate (`CertV`): one of the tiers Q (of `K − 2` or `K − 6`), H, F1 holds, or `K` is on the
half `H⁻` of the switch surface and Theorem 16.30 applies. -/
theorem cert_type21_capFace_norm {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CapNorm G)
    (hpp : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hT1 : ∀ u : ℝ³, u ≠ 0 → ⟪F.abc.N, u⟫ = 0 → ⟪F.ab'c'.N, u⟫ = 0 →
      T1Gen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' u) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have s30 := hN.h30; have s54 := hN.h54; have s61 := hN.h61; have s35 := hN.h35
  have anti := galeD_anti G.l G.m
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  have hKa : a ∈ K := by simp [hK]
  have hKa' : a' ∈ K := by simp [hK]
  have hKb : b ∈ K := by simp [hK]
  have hKb' : b' ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have hKc' : c' ∈ K := by simp [hK]
  -- the ties excluded by `NoPlaneParallel`
  have tie : ∀ {P Q R : ℝ³} (Fc : FacetFn {a, a', b, b', c, c'} P Q R) {x y : ℝ³},
      [P, Q, R, x, y].Nodup → P ∈ K → Q ∈ K → R ∈ K → x ∈ K → y ∈ K → Fc.f x ≠ 0 →
      Fc.f x ≠ Fc.f y := by
    intro P Q R Fc x y hnd5 hP hQ hR hx hy hx0 heq
    exact hpp P hP Q hQ R hR x hx y hy hnd5 (facet_tie_det Fc hx0 heq)
  have nd5 : ∀ {x₁ x₂ x₃ x₄ x₅ : ℝ³}, x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₁ ≠ x₅ → x₂ ≠ x₃ →
      x₂ ≠ x₄ → x₂ ≠ x₅ → x₃ ≠ x₄ → x₃ ≠ x₅ → x₄ ≠ x₅ → [x₁, x₂, x₃, x₄, x₅].Nodup := by
    intro x₁ x₂ x₃ x₄ x₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45, not_false⟩
  -- `[1 0] ≠ [5 1]`: the face `346` and `[1 ·]`
  have T_a : galeD G.l G.m c a ≠ galeD G.l G.m b' c := by
    intro h
    have r := (G.hl.galeD G.hm c).apply F.a'bc'.hN
    rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, galeD_self, anti b' c] at r
    have na := F.a'bc'.neg a (by simp) haa' hab hac'
    refine tie F.a'bc' (x := a) (y := b') (nd5 ha'b ha'c' (Ne.symm haa') ha'b' hbc'
      (Ne.symm hab) hbb' (Ne.symm hac') (Ne.symm hb'c') hab') hKa' hKb hKc' hKa hKb' na.ne ?_
    have : galeD G.l G.m c a * (F.a'bc'.f a - F.a'bc'.f b') = 0 := by
      linear_combination r - F.a'bc'.f b' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s10.ne')
  have T_b : galeD G.l G.m c' a ≠ galeD G.l G.m b' c' := by
    intro h
    have r := (G.hl.galeD G.hm c').apply F.a'bc.hN
    rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, galeD_self, anti b' c'] at r
    refine tie F.a'bc (x := a) (y := b') (nd5 ha'b ha'c (Ne.symm haa') ha'b' hbc (Ne.symm hab) hbb' (Ne.symm hac) (Ne.symm hb'c) hab')
      hKa' hKb hKc hKa hKb' (F.a'bc.neg a (by simp) haa' hab hac).ne ?_
    have : galeD G.l G.m c' a * (F.a'bc.f a - F.a'bc.f b') = 0 := by
      linear_combination r - F.a'bc.f b' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s60.ne')
  have T_c : galeD G.l G.m a b ≠ galeD G.l G.m c' a := by
    intro h
    have r := (G.hl.galeD G.hm a).apply F.a'b'c.hN
    rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, galeD_self, anti c' a] at r
    refine tie F.a'b'c (x := b) (y := c') (nd5 ha'b' ha'c ha'b ha'c' hb'c (Ne.symm hbb') hb'c' (Ne.symm hbc) hcc' hbc')
      hKa' hKb' hKc hKb hKc' (F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc).ne ?_
    have : galeD G.l G.m a b * (F.a'b'c.f b - F.a'b'c.f c') = 0 := by
      linear_combination r - F.a'b'c.f c' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s04.ne')
  have T_d : galeD G.l G.m a' b ≠ galeD G.l G.m c' a' := by
    intro h
    have r := (G.hl.galeD G.hm a').apply F.ab'c.hN
    rw [F.ab'c.hP, F.ab'c.hQ, F.ab'c.hR, galeD_self, anti c' a'] at r
    refine tie F.ab'c (x := b) (y := c') (nd5 hab' hac hab hac' hb'c (Ne.symm hbb') hb'c' (Ne.symm hbc) hcc' hbc')
      hKa hKb' hKc hKb hKc' (F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc).ne ?_
    have : galeD G.l G.m a' b * (F.ab'c.f b - F.ab'c.f c') = 0 := by
      linear_combination r - F.ab'c.f c' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s34.ne')
  have T_e : galeD G.l G.m b c ≠ galeD G.l G.m a' b := by
    intro h
    have r := (G.hl.galeD G.hm b).apply F.ab'c'.hN
    rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, galeD_self, anti a' b] at r
    refine tie F.ab'c' (x := c) (y := a') (nd5 hab' hac' hac haa' hb'c' hb'c (Ne.symm ha'b') (Ne.symm hcc') (Ne.symm ha'c') (Ne.symm ha'c))
      hKa hKb' hKc' hKc hKa' (F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc').ne ?_
    have : galeD G.l G.m b c * (F.ab'c'.f c - F.ab'c'.f a') = 0 := by
      linear_combination r - F.ab'c'.f a' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s41.ne')
  have T_f : galeD G.l G.m b' c ≠ galeD G.l G.m a' b' := by
    intro h
    have r := (G.hl.galeD G.hm b').apply F.abc'.hN
    rw [F.abc'.hP, F.abc'.hQ, F.abc'.hR, galeD_self, anti a' b'] at r
    refine tie F.abc' (x := c) (y := a') (nd5 hab hac' hac haa' hbc' hbc (Ne.symm ha'b) (Ne.symm hcc') (Ne.symm ha'c') (Ne.symm ha'c))
      hKa hKb hKc' hKc hKa' (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc').ne ?_
    have : galeD G.l G.m b' c * (F.abc'.f c - F.abc'.f a') = 0 := by
      linear_combination r - F.abc'.f a' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s51.ne')
  have T_g : galeD G.l G.m c' a' ≠ galeD G.l G.m b' c' := by
    intro h
    have r := (G.hl.galeD G.hm c').apply F.abc.hN
    rw [F.abc.hP, F.abc.hQ, F.abc.hR, galeD_self, anti b' c'] at r
    refine tie F.abc (x := a') (y := b') (nd5 hab hac haa' hab' hbc (Ne.symm ha'b) hbb' (Ne.symm ha'c) (Ne.symm hb'c) ha'b')
      hKa hKb hKc hKa' hKb' (F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c).ne ?_
    have : galeD G.l G.m c' a' * (F.abc.f a' - F.abc.f b') = 0 := by
      linear_combination r - F.abc.f b' * h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left s63.ne')
  -- Step 1: `05` or `46` a quad edge of `O` (tier Q)
  by_cases c1 : galeD G.l G.m c a < galeD G.l G.m b' c ∧ galeD G.l G.m c' a < galeD G.l G.m b' c'
  · refine cert_type21_Q F hd G hgen (Or.inl ⟨?_, ?_, mul_pos s30 s35⟩)
    · rw [anti b' c]; exact mul_neg_of_pos_of_neg s10 (by linarith [c1.1])
    · rw [anti b' c']; exact mul_neg_of_pos_of_neg s60 (by linarith [c1.2])
  by_cases c2 : galeD G.l G.m b' c < galeD G.l G.m c a ∧ galeD G.l G.m b' c' < galeD G.l G.m c' a
  · refine cert_type21_Q F hd G hgen (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
    · rw [anti b' c]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith [c2.1])
    · rw [anti b' c']; exact mul_neg_of_neg_of_pos (by linarith) (by linarith [c2.2])
    · rw [anti b' b, anti a b]; exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  by_cases c3 : galeD G.l G.m a b < galeD G.l G.m c' a ∧ galeD G.l G.m a' b < galeD G.l G.m c' a'
  · refine cert_type21_Q F hd G hgen
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, mul_pos s54 s56⟩)))))))
    · rw [anti c' a]; exact mul_neg_of_pos_of_neg s04 (by linarith [c3.1])
    · rw [anti c' a']; exact mul_neg_of_pos_of_neg s34 (by linarith [c3.2])
  by_cases c4 : galeD G.l G.m c' a < galeD G.l G.m a b ∧ galeD G.l G.m c' a' < galeD G.l G.m a' b
  · refine cert_type21_Q F hd G hgen
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))))))
    · rw [anti c' a]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith [c4.1])
    · rw [anti c' a']; exact mul_neg_of_neg_of_pos (by linarith) (by linarith [c4.2])
    · rw [anti c' c, anti b c]; exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  -- Step 2: `1 → 3` a quad edge of `O` (tier H)
  by_cases c5 : galeD G.l G.m b c < galeD G.l G.m a' b ∧ galeD G.l G.m b' c < galeD G.l G.m a' b'
  · refine cert_type21_H F hd G hgen (Or.inl ⟨?_, ?_, mul_pos s61 s63⟩)
    · rw [anti a' b]; exact mul_neg_of_pos_of_neg s41 (by linarith [c5.1])
    · rw [anti a' b']; exact mul_neg_of_pos_of_neg s51 (by linarith [c5.2])
  -- the region R1
  have P1 := type21_id_P1 G.hl G.hm
  have P2 := type21_id_P2 G.hl G.hm
  have P3 := type21_id_P3 G.hl G.hm
  have hF5 : galeD G.l G.m b' c < galeD G.l G.m c a ∧
      galeD G.l G.m c' a < galeD G.l G.m b' c' := by
    rcases lt_or_gt_of_ne T_a with h1 | h1 <;> rcases lt_or_gt_of_ne T_b with h2 | h2
    · exact absurd ⟨h1, h2⟩ c1
    · exfalso
      have := mul_lt_mul_of_pos_right h2 s10
      have := mul_lt_mul_of_pos_left h1 s60
      linarith [mul_pos s61 s05]
    · exact ⟨h1, h2⟩
    · exact absurd ⟨h1, h2⟩ c2
  have hF2 : galeD G.l G.m c' a < galeD G.l G.m a b ∧
      galeD G.l G.m a' b < galeD G.l G.m c' a' := by
    rcases lt_or_gt_of_ne T_c with h1 | h1 <;> rcases lt_or_gt_of_ne T_d with h2 | h2
    · exact absurd ⟨h1, h2⟩ c3
    · exfalso
      have := mul_lt_mul_of_pos_right h1 s63
      have := mul_lt_mul_of_pos_left h2 s60
      linarith [mul_pos s30 s46]
    · exact ⟨h1, h2⟩
    · exact absurd ⟨h1, h2⟩ c4
  have hF4 : galeD G.l G.m a' b < galeD G.l G.m b c := by
    rcases lt_or_gt_of_ne T_e with h1 | h1
    · exfalso
      rcases lt_or_gt_of_ne T_f with h2 | h2
      · exact c5 ⟨h1, h2⟩
      · have := mul_lt_mul_of_pos_right h1 s35
        have := mul_lt_mul_of_pos_left h2 s34
        linarith [mul_pos s13 s54]
    · exact h1
  have hD : 0 < galeD G.l G.m c a + galeD G.l G.m a' a + galeD G.l G.m a' b' -
      galeD G.l G.m b' c := by linarith [hF5.1]
  have hF1 : galeD G.l G.m a' b < galeD G.l G.m c a' := by
    have e := type21_id_F1 G.hl G.hm
    have : 0 < (galeD G.l G.m c a + galeD G.l G.m a' a + galeD G.l G.m a' b' -
        galeD G.l G.m b' c) * (galeD G.l G.m c a' - galeD G.l G.m a' b) := by
      rw [e]
      exact add_pos (mul_pos s13 (by linarith [hF5.2])) (mul_pos (by linarith) (by linarith))
    linarith [pos_of_mul_pos_right this hD.le]
  have hF3 : galeD G.l G.m c' a < galeD G.l G.m a b' := by
    have e := type21_id_F3 G.hl G.hm
    have : 0 < (galeD G.l G.m c a + galeD G.l G.m a' a + galeD G.l G.m a' b' -
        galeD G.l G.m b' c) * (galeD G.l G.m a b' - galeD G.l G.m c' a) := by
      rw [e]
      exact add_pos (mul_pos (by linarith) (by linarith [hF5.2])) (mul_pos s05 (by linarith))
    linarith [pos_of_mul_pos_right this hD.le]
  have hF6 : galeD G.l G.m a' b < galeD G.l G.m b c' := by
    have e := type21_id_F6 G.hl G.hm
    have : 0 < (galeD G.l G.m c a + galeD G.l G.m a' a + galeD G.l G.m a' b' -
        galeD G.l G.m b' c) * (galeD G.l G.m b c' - galeD G.l G.m a' b) := by
      rw [e]
      exact add_pos (add_pos (mul_pos (by linarith) (by linarith [hF2.2]))
        (mul_pos s46 (by linarith [hF5.1]))) (mul_pos s46 (by linarith [hF2.2]))
    linarith [pos_of_mul_pos_right this hD.le]
  -- the cap parameter
  obtain ⟨α, β, τ, hα0, hβ, hαβ, hτ, hco, hα, ht⟩ := hd.tau hN.toCross
  -- Step 3: `δ_014(2) > δ_014(5)`: `Q` at `25` of `K − 6`
  by_cases h3 : F.abc.f d < F.abc.f b'
  · exact cert_type21_step3 F hd G hN.toCross hF3 hF4 h3 hgen
  push Not at h3
  obtain ⟨e1, e2, e3⟩ := type21_f014 F G hco
  have f5 := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
  have hS : α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' ≤ galeD G.l G.m c' a' := by
    have k : galeD G.l G.m c' a' * (F.abc.f d - F.abc.f b') = F.abc.f b' *
        (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' - galeD G.l G.m c' a') := by
      rw [e3]; linear_combination -β * e2
    have : 0 ≤ F.abc.f b' *
        (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' - galeD G.l G.m c' a') := by
      rw [← k]; exact mul_nonneg s63.le (by linarith)
    by_contra hc
    push Not at hc
    linarith [mul_neg_of_neg_of_pos f5 (sub_pos.mpr hc)]
  obtain ⟨hE, hcase1, hcase2⟩ := type21_lemma1612 (F := F) hN hτ hα ht hF1 hF5.1 hF6 hS
  rcases lt_or_gt_of_ne T_g with h63 | h63
  · -- `[5 6] > [6 3]`: `Q` at `23`
    obtain ⟨hH1, hH2⟩ := hcase1 h63
    exact cert_type21_step5 F hd G hN.toCross hco hα ht hH1 hH2 hE hgen
  · obtain ⟨hB, hA⟩ := hcase2 h63
    by_cases hH12 : β * galeD G.l G.m a' b < galeD G.l G.m b c' ∧
        α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m b' c'
    · exact cert_type21_step5 F hd G hN.toCross hco hα ht hH12.1 hH12.2 hE hgen
    have hA' := hA hH12
    -- (iii) in facet form: `135` and `235` face up along `4 − 0`
    have hiii : F.a'b'c.f a < F.a'b'c.f b ∧ hd.f235.f a < hd.f235.f b := by
      constructor
      · obtain ⟨-, g2, -⟩ := type21_f135 F G hco
        have fa := F.a'b'c.neg a (by simp) haa' hab' hac
        have : 0 < galeD G.l G.m b c' * (F.a'b'c.f b - F.a'b'c.f a) := by
          have k : galeD G.l G.m b c' * (F.a'b'c.f b - F.a'b'c.f a) =
              (galeD G.l G.m c' a - galeD G.l G.m b c') * F.a'b'c.f a := by
            linear_combination -g2
          rw [k]; exact mul_pos_of_neg_of_neg (by linarith) fa
        linarith [pos_of_mul_pos_right this s46.le]
      · obtain ⟨hr, -, -⟩ := type21_r_pos hd hN.toCross hco hα ht
        obtain ⟨L, hL, Ld, Lc, Lb', Lb, La', La⟩ := type21_depO2_c hd G hco hα ht
        refine facet_lt_of_dep hL.perm₁₂.perm₂₃.perm₁₂.swap₁.swap₂ hd.f235.p12 (by simp)
          (by simp) ?_ Lc ?_
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            List.nodup_nil, and_true]
          exact ⟨⟨haa', hab, hab', Ne.symm hda, hac⟩, ⟨ha'b, ha'b', Ne.symm hda', ha'c⟩,
            ⟨hbb', Ne.symm hdb, hbc⟩, ⟨Ne.symm hdb', hb'c⟩, hdc, not_false⟩
        · rw [La, Lb, anti b c]
          have hra : 0 < (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a := mul_pos hr s10
          exact mul_neg_of_pos_of_neg hra (by linarith)
    by_cases hstrict : F.abc.f b' < F.abc.f d
    · -- Step 4: F1
      have hS' : α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' < galeD G.l G.m c' a' := by
        have k : galeD G.l G.m c' a' * (F.abc.f d - F.abc.f b') = F.abc.f b' *
            (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' - galeD G.l G.m c' a') := by
          rw [e3]; linear_combination -β * e2
        have : 0 < F.abc.f b' *
            (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' - galeD G.l G.m c' a') := by
          rw [← k]; exact mul_pos s63 (by linarith)
        by_contra hc
        push Not at hc
        linarith [mul_nonpos_of_nonpos_of_nonneg f5.le (sub_nonneg.mpr hc)]
      set u₁ := axisView G.l G.m a' a b' c' with hu₁
      have hN014 : ⟪F.abc.N, u₁⟫ = 0 := by
        simp only [hu₁, axisView, inner_add_right, real_inner_smul_right, ← F.abc.hN, F.abc.hP,
          sub_zero, anti c' a']
        linear_combination e2
      have hN056 : ⟪F.ab'c'.N, u₁⟫ = 0 := by
        simp only [hu₁, axisView, inner_add_right, real_inner_smul_right, ← F.ab'c'.hN,
          F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR]
        ring
      have hu0 : u₁ ≠ 0 := by
        intro h0
        have k : ⟪F.abc'.N, u₁⟫ = galeD G.l G.m a' b' * F.abc'.f b' := by
          simp only [hu₁, axisView, inner_add_right, real_inner_smul_right, ← F.abc'.hN,
            F.abc'.hP, F.abc'.hR]
          ring
        rw [h0, inner_zero_right] at k
        have := mul_neg_of_pos_of_neg s35 (F.abc'.neg b' (by simp) (Ne.symm hab')
          (Ne.symm hbb') hb'c')
        linarith
      obtain ⟨hP, hz, -⟩ := hT1 u₁ hu0 hN014 hN056
      refine cert_type21_F1 F hd G hN.h35 hN.h61 hα0 hβ hαβ hco hS' hiii hF1 hP hz
        (fun σ hσ => (hT1 (σ • u₁) (smul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hu0)
          (by rw [real_inner_smul_right, hN014, mul_zero])
          (by rw [real_inner_smul_right, hN056, mul_zero])).2.2) hgen
    · -- the switch surface `H⁻`: Theorem 16.30
      have hsw : F.abc.f d = F.abc.f b' := le_antisymm (by push Not at hstrict; exact hstrict) h3
      -- (F1) in facet form: `δ_056(4) < δ_056(1)`
      have r3 := (G.hl.galeD G.hm a').apply F.ab'c'.hN
      rw [F.ab'c'.hP, F.ab'c'.hQ, F.ab'c'.hR, galeD_self, anti c a'] at r3
      have f1 := F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc'
      have hF1' : F.ab'c'.f b < F.ab'c'.f c := by
        have e1 : galeD G.l G.m c a' * F.ab'c'.f c < galeD G.l G.m a' b * F.ab'c'.f c :=
          mul_lt_mul_of_neg_right hF1 f1
        have e2 : galeD G.l G.m a' b * F.ab'c'.f b < galeD G.l G.m a' b * F.ab'c'.f c := by
          linarith
        exact lt_of_mul_lt_mul_left e2 s34.le
      exact cert_type21_switch F hd G hN.toCross hsw hF1' hpp hgen

/-! ### Theorem 16.13 in general: normalization by `σ1`, `σ2` and the reflection of the Gale
diagram -/

/-- **The cap-face class** (§16.3; §9 Theorem 5's form: all three `W` have the non-quad pair):
`[3 0]`, `[5 4]`, `[6 1]` have one sign, i.e. the pattern of the octahedron is `±(+, +, +)`. -/
def CapFace {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') : Prop :=
  0 < galeD G.l G.m a' a * galeD G.l G.m b' b ∧ 0 < galeD G.l G.m a' a * galeD G.l G.m c' c

/-- The special positions of Theorem 16.13 for one labelling `F` of `K − 2` with the cap `d`:
those of `T1` at every direction of the line `014 ∩ 0256` (`T1Gen`).  (The half `H⁻` of the
switch surface is no longer excluded: Theorem 16.30.) -/
def Type21CapGen (K : Finset ℝ³) (L : ℝ³ → Prop) {a a' b b' c c' : ℝ³}
    (F : OctFacets a a' b b' c c') (_d : ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → ⟪F.abc.N, u⟫ = 0 → ⟪F.ab'c'.N, u⟫ = 0 → T1Gen K L a a' b b' u

/-- **Theorem 16.13 for `K − 2` in its cap-face class**, any Gale data: reflect the Gale diagram
(`GaleData.flip`) to make `[3 0], [5 4], [6 1] > 0`, and apply `σ1` if `ε = −1`. -/
theorem cert_type21_capFace_O {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hcf : CapFace G)
    (hpp : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hG₁ : Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F d)
    (hG₂ : Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F.perm₁₂ d) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
  wlog hpos : 0 < galeD G.l G.m a' a generalizing G with H
  · refine H G.flip ?_ ?_
    · simp only [CapFace, galeD_flip] at hcf ⊢; constructor <;> nlinarith [hcf.1, hcf.2]
    · rw [galeD_flip]
      have h0 : galeD G.l G.m a' a ≠ 0 := by
        intro h0; have := hcf.1; rw [h0, zero_mul] at this; exact lt_irrefl _ this
      push Not at hpos; exact neg_pos.mpr (lt_of_le_of_ne hpos h0)
  have hb : 0 < galeD G.l G.m b' b := pos_of_mul_pos_right hcf.1 hpos.le
  have hc : 0 < galeD G.l G.m c' c := pos_of_mul_pos_right hcf.2 hpos.le
  have hε : galeD G.l G.m a' b' ≠ 0 := galeD_ne_zero F.swap₁.swap₂ G.swap₁.swap₂
  rcases lt_or_gt_of_ne hε with hε | hε
  · rw [← (type21_set a a' b b' c c' d).2.2.2.2] at hpp hgen hG₂ ⊢
    refine cert_type21_capFace_norm F.perm₁₂ hd.sigma1 G.perm₁₂ ⟨hb, hpos, hc, ?_⟩ hpp hgen
      hG₂
    show 0 < galeD G.l G.m b' a'
    rw [galeD_anti]; linarith
  · exact cert_type21_capFace_norm F hd G ⟨hpos, hb, hc, hε⟩ hpp hgen hG₁

/-- **Theorem 16.13 (the cap-face class).**  Let `K = O ∪ {2}` be of type 21 (`IsCap21`), with
`K − 2` or `K − 6` in its cap-face class.  Off the special positions — `NoPlaneParallel`
(every tie of a Gale comparison used), `GenPosTie`, no horizontal double normal at the edge views
(`NoHDNEdges`), and, for each of the four labellings `id, σ1, σ2, σ2σ1`, the special positions
of `T1` (`Type21CapGen`) — `K` has a rim certificate (`CertV`): one of the tiers Q (`K − 2` or `K − 6`), H, F1 holds,
or Theorem 16.30 on the switch surface. -/
theorem cert_type21_capFace {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d)
    (hpp : NoPlaneParallel (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hG : Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F d ∧
      Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L F.perm₁₂ d ∧
      Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L hd.O2 c' ∧
      Type21CapGen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L hd.O2.perm₁₂ c')
    (hclass : (∃ G : GaleData a a' b b' c c', CapFace G) ∨
      (∃ G : GaleData b' b a' a c d, CapFace G)) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  rcases hclass with ⟨G, hcf⟩ | ⟨G, hcf⟩
  · exact cert_type21_capFace_O F hd G hcf hpp hgen h1 h2
  · rw [← type21_set_O2] at hpp hgen h3 h4 ⊢
    exact cert_type21_capFace_O hd.O2 hd.sigma2 G hcf hpp hgen h3 h4

end Minimality

end
