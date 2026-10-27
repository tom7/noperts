module

public import Minimality.CaseC18Tests

@[expose] public section

/-!
# Type 18, acute case (c): the algebra of Theorem 27.59 (`FEWER-FACES-PROOFS.md` §27, continued (4))

* `Shape18.exists_view_F2`: 27.59 (d), the last case: with `A1 < μ±` (`V`, `V^Z` both of class
  `Rv`), `c- ≥ h+ + t+ a-` and `c+ ≥ h- + t- a+` (the failures of families `A` and `A^Z`), Theorem 5
  holds with `W = F2`: a view `(α, γ)` puts `xa, m1+, m1-` into the open quad of `F2`.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

namespace Shape18
variable (S : Shape18)

/-- `μ+ = d+ / t+`. -/
noncomputable def mup : ℝ := S.dp / S.tp
/-- `μ- = d- / t-`. -/
noncomputable def mum : ℝ := S.dm / S.tm

lemma mup_mul : S.mup * S.tp = S.dp := by unfold mup; field_simp [S.tp_pos.ne']
lemma mum_mul : S.mum * S.tm = S.dm := by unfold mum; field_simp [S.tm_pos.ne']

/-- `μ+ < d+ + a+` (the roof `d+ < b+`). -/
lemma mup_lt : S.mup < S.dp + S.ap := by
  have htp := S.tp_pos; have htp1 := S.tp_lt
  have h1 := S.mup_mul; have h2 := S.ap_mul; have h3 := S.dp_lt_bp; have h4 := S.bp_mul
  have h5 : S.dp * (1 - S.tp) < S.hp := by
    have := mul_lt_mul_of_pos_right h3 (sub_pos.2 htp1); nlinarith
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_right hc htp.le]

/-- `μ- < d- + a-` (the roof `d- < b-`). -/
lemma mum_lt : S.mum < S.dm + S.am := by
  have htp := S.tm_pos; have htp1 := S.tm_lt
  have h1 := S.mum_mul; have h2 := S.am_mul; have h3 := S.dm_lt_bm; have h4 := S.bm_mul
  have h5 : S.dm * (1 - S.tm) < S.hm := by
    have := mul_lt_mul_of_pos_right h3 (sub_pos.2 htp1); nlinarith
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_right hc htp.le]

lemma A1_pos : 0 < S.A1 := add_pos S.ap_pos S.am_pos
lemma A2_pos : 0 < S.A2 := add_pos S.cp_pos S.cm_pos

/-- **27.59 (d), the affine system** over the reals: with `α₀ = lo = A1/A2` and
`γ(α) = ((c+ - c-) α + a- - a+)/2`, the twelve inequalities of the three crossings hold at
`α = lo + ε` for small `ε > 0`. -/
theorem view_aff {ap am cp cm tp tm lo mup mum : ℝ} (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm)
    (htm1 : tm < 1) (hap : 0 < ap) (ham : 0 < am) (hcp : 0 < cp) (hcm : 0 < cm) (hlo0 : 0 < lo)
    (hl : (cp + cm) * lo = ap + am) (hlo1 : lo * (tp + tm) ≤ 1)
    (hmup : 0 < mup) (hmum : 0 < mum)
    (s2' : (mup * tp - cm) * lo < mup - (ap + am)) (s6' : (mum * tm - cp) * lo < mum - (ap + am))
    (F1 : mup < mup * tp + ap) (F2 : mum < mum * tm + am) :
    ∃ α γ : ℝ,
      (γ < cp * α ∧ γ < mup * tp * (1 - α) ∧ -γ < cm * α ∧ -γ < mum * tm * (1 - α)) ∧
      (ap * tp + tp * γ < cp * (tp * α) ∧ ap * tp + tp * γ < mup * tp * (1 - tp * α) ∧
        -(ap * tp + tp * γ) < cm * (tp * α) ∧ -(ap * tp + tp * γ) < mum * tm * (1 - tp * α)) ∧
      (-(am * tm) + tm * γ < cp * (tm * α) ∧ -(am * tm) + tm * γ < mup * tp * (1 - tm * α) ∧
        -(-(am * tm) + tm * γ) < cm * (tm * α) ∧
        -(-(am * tm) + tm * γ) < mum * tm * (1 - tm * α)) := by
  have s2 : 0 < mup - (ap + am) - (mup * tp - cm) * lo := by linarith
  have s6 : 0 < mum - (mum * tm + cm) * lo := by nlinarith
  have s1 : 0 < mup * tp - am - (mup * tp - cm) * lo := by linarith
  have s4 : 0 < mum * tm + am - (mum * tm + cm) * lo := by linarith
  have hdp : 0 < mup * tp := mul_pos hmup htp
  have hdm : 0 < mum * tm := mul_pos hmum htm
  have hlt : tp * lo < 1 := by nlinarith [mul_pos htm hlo0]
  have hlt' : tm * lo < 1 := by nlinarith [mul_pos htp hlo0]
  have s3 : 0 < mup * tp - tm * (mup * tp - cm) * lo := by
    rcases le_or_gt (mup * tp - cm) 0 with h | h
    · nlinarith [mul_nonneg (neg_nonneg.2 h) (mul_pos htm hlo0).le]
    · nlinarith [mul_pos h (sub_pos.2 hlt'), mul_pos hcm (sub_pos.2 hlt')]
  have s5 : 0 < mum * tm + tp * (ap + am) - tp * (mum * tm + cm) * lo := by
    have e : (mum * tm + cm) * lo = (ap + am) + (mum * tm - cp) * lo := by linarith
    rcases le_or_gt (mum * tm - cp) 0 with h | h
    · nlinarith [mul_nonneg (neg_nonneg.2 h) (mul_pos htp hlo0).le]
    · nlinarith [mul_pos h (sub_pos.2 hlt), mul_pos hcp (sub_pos.2 hlt)]
  have key : ∀ (f : ℝ → ℝ) (A B : ℝ), (∀ ε, f ε = A + ε * B) → (0 < A ∨ (A = 0 ∧ 0 < B)) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < f ε := fun f A B hf h =>
    (eventually_pos_affine h).mono fun ε hε => by rw [hf ε]; exact hε
  have hB : 0 < (cp + cm) / 2 := by positivity
  have x1 := key (fun ε => cp * (lo + ε) - ((cp - cm) * (lo + ε) + am - ap) / 2) ap
    ((cp + cm) / 2) (fun ε => by linear_combination (1 / 2) * hl) (Or.inl hap)
  have x2 := key (fun ε => mup * tp * (1 - (lo + ε)) - ((cp - cm) * (lo + ε) + am - ap) / 2)
    (mup * tp - am - (mup * tp - cm) * lo) (-(mup * tp) - (cp - cm) / 2)
    (fun ε => by linear_combination (-1 / 2) * hl) (Or.inl s1)
  have x3 := key (fun ε => cm * (lo + ε) + ((cp - cm) * (lo + ε) + am - ap) / 2) am
    ((cp + cm) / 2) (fun ε => by linear_combination (1 / 2) * hl) (Or.inl ham)
  have x4 := key (fun ε => mum * tm * (1 - (lo + ε)) + ((cp - cm) * (lo + ε) + am - ap) / 2)
    (mum * tm + am - (mum * tm + cm) * lo) (-(mum * tm) + (cp - cm) / 2)
    (fun ε => by linear_combination (1 / 2) * hl) (Or.inl s4)
  have y1 := key (fun ε => cp * (tp * (lo + ε)) -
      (ap * tp + tp * (((cp - cm) * (lo + ε) + am - ap) / 2))) 0 (tp * ((cp + cm) / 2))
    (fun ε => by linear_combination (tp / 2) * hl) (Or.inr ⟨rfl, by positivity⟩)
  have y2 := key (fun ε => mup * tp * (1 - tp * (lo + ε)) -
      (ap * tp + tp * (((cp - cm) * (lo + ε) + am - ap) / 2)))
    (tp * (mup - (ap + am) - (mup * tp - cm) * lo))
    (-(mup * tp * tp) - tp * ((cp - cm) / 2))
    (fun ε => by linear_combination (-tp / 2) * hl) (Or.inl (mul_pos htp s2))
  have y3 := key (fun ε => cm * (tp * (lo + ε)) +
      (ap * tp + tp * (((cp - cm) * (lo + ε) + am - ap) / 2)))
    (tp * am + ap * tp) (tp * cm + tp * ((cp - cm) / 2))
    (fun ε => by linear_combination (tp / 2) * hl) (Or.inl (by positivity))
  have y4 := key (fun ε => mum * tm * (1 - tp * (lo + ε)) +
      (ap * tp + tp * (((cp - cm) * (lo + ε) + am - ap) / 2)))
    (mum * tm + tp * (ap + am) - tp * (mum * tm + cm) * lo)
    (-(mum * tm * tp) + tp * ((cp - cm) / 2))
    (fun ε => by linear_combination (tp / 2) * hl) (Or.inl s5)
  have z1 := key (fun ε => cp * (tm * (lo + ε)) -
      (-(am * tm) + tm * (((cp - cm) * (lo + ε) + am - ap) / 2)))
    (tm * (ap + am)) (tm * ((cp + cm) / 2))
    (fun ε => by linear_combination (tm / 2) * hl) (Or.inl (by positivity))
  have z2 := key (fun ε => mup * tp * (1 - tm * (lo + ε)) -
      (-(am * tm) + tm * (((cp - cm) * (lo + ε) + am - ap) / 2)))
    (mup * tp - tm * (mup * tp - cm) * lo) (-(mup * tp * tm) - tm * ((cp - cm) / 2))
    (fun ε => by linear_combination (-tm / 2) * hl) (Or.inl s3)
  have z3 := key (fun ε => cm * (tm * (lo + ε)) +
      (-(am * tm) + tm * (((cp - cm) * (lo + ε) + am - ap) / 2))) 0 (tm * ((cp + cm) / 2))
    (fun ε => by linear_combination (tm / 2) * hl) (Or.inr ⟨rfl, by positivity⟩)
  have z4 := key (fun ε => mum * tm * (1 - tm * (lo + ε)) +
      (-(am * tm) + tm * (((cp - cm) * (lo + ε) + am - ap) / 2)))
    (tm * (mum - (mum * tm + cm) * lo)) (-(mum * tm * tm) + tm * ((cp - cm) / 2))
    (fun ε => by linear_combination (tm / 2) * hl) (Or.inl (mul_pos htm s6))
  obtain ⟨ε, ⟨⟨⟨⟨a1, a2⟩, a3, a4⟩, ⟨b1, b2⟩, b3, b4⟩, ⟨c1, c2⟩, c3, c4⟩, hε⟩ :=
    ((((x1.and x2).and (x3.and x4)).and ((y1.and y2).and (y3.and y4))).and
      ((z1.and z2).and (z3.and z4))).and
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)) |>.exists
  refine ⟨lo + ε, ((cp - cm) * (lo + ε) + am - ap) / 2, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩⟩ <;> linarith


/-- **27.59 (d)**: with `A1 < μ±` and the failures `c- ≥ h+ + t+ a-`, `c+ ≥ h- + t- a+` of families
`A`, `A^Z`, a view `(α, γ)` puts `xa, m1+, m1-` into the open quad of `F2`. -/
theorem exists_view_F2 (hVp : S.A1 * S.tp < S.dp) (hVm : S.A1 * S.tm < S.dm)
    (hCm : S.hp + S.tp * S.am ≤ S.cm) (hCp : S.hm + S.tm * S.ap ≤ S.cp) :
    ∃ α γ : ℝ, InQuad2 S α γ ∧ InQuad2 S (S.tp * α) (S.hp + S.tp * γ) ∧
      InQuad2 S (S.tm * α) (-S.hm + S.tm * γ) := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have htm1 := S.tm_lt
  have hA1 := S.A1_pos; have hA2 := S.A2_pos
  have e1 := S.ap_mul; have e2 := S.am_mul; have g1 := S.mup_mul; have g2 := S.mum_mul
  have hA1d : S.A1 = S.ap + S.am := rfl
  have hA2d : S.A2 = S.cp + S.cm := rfl
  have hlo0 : 0 < S.A1 / S.A2 := div_pos hA1 hA2
  have hl : (S.cp + S.cm) * (S.A1 / S.A2) = S.ap + S.am := by
    rw [← hA2d, ← hA1d]; field_simp
  have hA2ge : S.A1 * (S.tp + S.tm) ≤ S.A2 := by
    rw [hA2d, hA1d]; nlinarith
  have hlo1 : S.A1 / S.A2 * (S.tp + S.tm) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hA2]; exact hA2ge
  have hmp : 0 < S.mup := div_pos S.dp_pos htp
  have hmm : 0 < S.mum := div_pos S.dm_pos htm
  have hδp : S.A1 < S.mup := by
    by_contra hc; push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc htp.le]
  have hδm : S.A1 < S.mum := by
    by_contra hc; push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc htm.le]
  have htlo : S.tp * (S.A1 / S.A2) < 1 := by
    have : S.tp * S.A1 < S.A2 := by nlinarith
    rw [mul_div_assoc', div_lt_one hA2]; exact this
  have htlo' : S.tm * (S.A1 / S.A2) < 1 := by
    have : S.tm * S.A1 < S.A2 := by nlinarith
    rw [mul_div_assoc', div_lt_one hA2]; exact this
  have s2' : (S.mup * S.tp - S.cm) * (S.A1 / S.A2) < S.mup - (S.ap + S.am) := by
    have h1 : S.mup * S.tp - S.cm ≤ S.tp * (S.mup - S.A1) := by nlinarith
    have h2 : (S.mup * S.tp - S.cm) * (S.A1 / S.A2) ≤ S.tp * (S.mup - S.A1) * (S.A1 / S.A2) :=
      mul_le_mul_of_nonneg_right h1 hlo0.le
    have h3 : S.tp * (S.mup - S.A1) * (S.A1 / S.A2) < S.mup - S.A1 := by
      have := mul_lt_mul_of_pos_left htlo (sub_pos.2 hδp)
      nlinarith
    linarith
  have s6' : (S.mum * S.tm - S.cp) * (S.A1 / S.A2) < S.mum - (S.ap + S.am) := by
    have h1 : S.mum * S.tm - S.cp ≤ S.tm * (S.mum - S.A1) := by nlinarith
    have h2 : (S.mum * S.tm - S.cp) * (S.A1 / S.A2) ≤ S.tm * (S.mum - S.A1) * (S.A1 / S.A2) :=
      mul_le_mul_of_nonneg_right h1 hlo0.le
    have h3 : S.tm * (S.mum - S.A1) * (S.A1 / S.A2) < S.mum - S.A1 := by
      have := mul_lt_mul_of_pos_left htlo' (sub_pos.2 hδm)
      nlinarith
    linarith
  have F1 : S.mup < S.mup * S.tp + S.ap := by have := S.mup_lt; rwa [← g1] at this
  have F2 : S.mum < S.mum * S.tm + S.am := by have := S.mum_lt; rwa [← g2] at this
  obtain ⟨α, γ, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3, c4⟩⟩ :=
    view_aff htp htp1 htm htm1 S.ap_pos S.am_pos S.cp_pos S.cm_pos hlo0 hl hlo1 hmp hmm s2' s6'
      F1 F2
  refine ⟨α, γ, ⟨a1, ?_, a3, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← g1]; exact a2
  · rw [← g2]; exact a4
  · rw [← e1]; exact b1
  · rw [← e1, ← g1]; exact b2
  · rw [← e1]; exact b3
  · rw [← e1, ← g2]; exact b4
  · rw [← e2]; exact c1
  · rw [← e2, ← g1]; exact c2
  · rw [← e2]; exact c3
  · rw [← e2, ← g2]; exact c4

/-- Cross-multiplication of two slopes. -/
lemma slope_lt {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a / b < c / d) : a * d < c * b :=
  (div_lt_div_iff₀ hb hd).1 h

lemma slope_lt' {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) : a / b < c / d :=
  (div_lt_div_iff₀ hb hd).2 h

/-- `¬(A2 ∧ A3)` of family `A` gives `c- ≥ h+ + t+ a-` (27.59 (d); uses `s- < t-`). -/
theorem cm_ge (hst : S.sm < S.tm)
    (h : ¬ (S.km * S.tm < S.sm * (S.hp * S.tm + S.tp * S.hm) ∧
      S.km * (1 - S.tm) < S.hp * S.sm * (1 - S.tm) + S.hm * (1 - S.tp * S.sm))) :
    S.hp + S.tp * S.am ≤ S.cm := by
  have htm := S.tm_pos; have hsm := S.sm_pos; have htp := S.tp_pos; have htp1 := S.tp_lt
  have htm1 := S.tm_lt
  have e1 := S.am_mul; have e2 := S.cm_mul
  -- `c- ≥ h+ + t+ a-` ⇔ `k- t- ≥ s- (h+ t- + t+ h-)`
  suffices hk : S.sm * (S.hp * S.tm + S.tp * S.hm) ≤ S.km * S.tm by
    have : (S.hp + S.tp * S.am) * (S.sm * S.tm) ≤ S.cm * (S.sm * S.tm) := by
      have e3 : (S.hp + S.tp * S.am) * (S.sm * S.tm) = S.sm * (S.hp * S.tm + S.tp * S.hm) := by
        rw [← e1]; ring
      have e4 : S.cm * (S.sm * S.tm) = S.km * S.tm := by rw [← e2]; ring
      rw [e3, e4]; exact hk
    exact le_of_mul_le_mul_right this (mul_pos hsm htm)
  by_contra hc
  push Not at hc
  apply h
  refine ⟨hc, ?_⟩
  -- from `k- t- < s- (h+ t- + t+ h-)`
  have hk1 : S.km * (1 - S.tm) < S.hp * S.sm * (1 - S.tm) + S.hm * (1 - S.tp * S.sm) := by
    -- multiply by `t-`: `k- t- (1 - t-) < s-(h+ t- + t+ h-)(1 - t-)`; and the right side bound
    have h1 : S.tm * (S.km * (1 - S.tm)) < S.tm * (S.hp * S.sm * (1 - S.tm) +
        S.hm * (1 - S.tp * S.sm)) := by
      have a1 := mul_lt_mul_of_pos_right hc (sub_pos.2 htm1)
      have a2 : 0 < S.hm * (S.tm - S.sm * S.tp) := mul_pos S.hm_pos (by nlinarith)
      nlinarith
    exact lt_of_mul_lt_mul_left h1 htm.le
  exact hk1

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- `famA` for the `Z`-image (`A^Z`). -/
theorem famAz (A1 : F.S.hp * (1 - F.S.tm) < F.S.hm * F.S.tp)
    (A2 : F.S.kp * F.S.tp < F.S.sp * (F.S.hm * F.S.tp + F.S.tm * F.S.hp))
    (A3 : F.S.kp * (1 - F.S.tp) < F.S.hm * F.S.sp * (1 - F.S.tp) + F.S.hp * (1 - F.S.tm * F.S.sp)) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.famA A1 A2 A3)

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **Theorem 27.59, the part without `V`**: off the equalities `a- = b+`, `a+ = b-`, `a+ = c+`,
`a- = c-` and the right angles, either `K` is Rupert (by the edge crossings `B`, `B^Z`, 27.31, the
families `A`, `A^Z` and Theorem 5 with `W = F2`), or `a- < b+`, `a+ < b-` and `V` or `V^Z` is not of
class `Rv` (`μ± ≤ A1`, i.e. `φ(m1∓) ≥ 0`): the cases that need the vertex crossings `V`, `V^Z` of
27.59 (b), (c). -/
theorem rupert_or_V (hx : Function.Injective x) (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22)
    (n1 : F.S.am ≠ F.S.bp) (n2 : F.S.ap ≠ F.S.bm) (n3 : F.S.ap ≠ F.S.cp)
    (n4 : F.S.am ≠ F.S.cm) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.am < F.S.bp ∧ F.S.ap < F.S.bm ∧
        (F.S.dp ≤ F.S.A1 * F.S.tp ∨ F.S.dm ≤ F.S.A1 * F.S.tm)) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt
  have o_tp : 0 < 1 - F.S.tp := sub_pos.2 htp1
  have o_tm : 0 < 1 - F.S.tm := sub_pos.2 htm1
  have o_sp : 0 < 1 - F.S.sp := sub_pos.2 hsp1
  have o_sm : 0 < 1 - F.S.sm := sub_pos.2 hsm1
  -- the edge crossings `B^Z` and `B`
  by_cases h1 : F.S.bp < F.S.am
  · left
    have h1d : F.S.dp < F.S.am := lt_trans F.S.dp_lt_bp h1
    exact F.tBz hα (Shape18.slope_lt o_tp htm h1) (Shape18.slope_lt o_sp htm h1d)
  have h1' : F.S.am < F.S.bp := lt_of_le_of_ne (not_lt.1 h1) n1
  by_cases h2 : F.S.bm < F.S.ap
  · left
    have h2d : F.S.dm < F.S.ap := lt_trans F.S.dm_lt_bm h2
    exact F.tB hα (Shape18.slope_lt o_tm htp h2) (Shape18.slope_lt o_sm htp h2d)
  have h2' : F.S.ap < F.S.bm := lt_of_le_of_ne (not_lt.1 h2) n2
  by_cases hd : F.S.dp ≤ F.S.A1 * F.S.tp ∨ F.S.dm ≤ F.S.A1 * F.S.tm
  · exact Or.inr ⟨h1', h2', hd⟩
  left
  push Not at hd
  obtain ⟨hVp, hVm⟩ := hd
  -- 27.31
  by_cases hc : F.S.ap < F.S.cp ∧ F.S.am < F.S.cm
  swap
  · rcases not_and_or.1 hc with h | h
    · have h' : F.S.cp < F.S.ap := lt_of_le_of_ne (not_lt.1 h) (Ne.symm n3)
      by_cases h'' : F.S.am < F.S.cm
      · exact F.t31c hα hβ (Shape18.slope_lt htm hsm h'') (Shape18.slope_lt hsp htp h')
      · have h3 : F.S.cm < F.S.am := lt_of_le_of_ne (not_lt.1 h'') (Ne.symm n4)
        exact F.t31a hα (Shape18.slope_lt hsp htp h') (Shape18.slope_lt hsm htm h3)
    · have h3 : F.S.cm < F.S.am := lt_of_le_of_ne (not_lt.1 h) (Ne.symm n4)
      by_cases h'' : F.S.ap < F.S.cp
      · exact F.t31b hα hβ (Shape18.slope_lt htp hsp h'') (Shape18.slope_lt hsm htm h3)
      · have h' : F.S.cp < F.S.ap := lt_of_le_of_ne (not_lt.1 h'') (Ne.symm n3)
        exact F.t31a hα (Shape18.slope_lt hsp htp h') (Shape18.slope_lt hsm htm h3)
  obtain ⟨hcp, hcm⟩ := hc
  -- `s- < t-`, `s+ < t+`
  have hst : F.S.sm < F.S.tm := F.S.swap.sp_lt_tp (Shape18.slope_lt htm hsm hcm)
  have hst' : F.S.sp < F.S.tp := F.S.sp_lt_tp (Shape18.slope_lt htp hsp hcp)
  -- families `A` and `A^Z`
  by_cases hfA : F.S.km * F.S.tm < F.S.sm * (F.S.hp * F.S.tm + F.S.tp * F.S.hm) ∧
      F.S.km * (1 - F.S.tm) < F.S.hp * F.S.sm * (1 - F.S.tm) + F.S.hm * (1 - F.S.tp * F.S.sm)
  · exact F.famA (F.A1_of h1') hfA.1 hfA.2
  by_cases hfZ : F.S.kp * F.S.tp < F.S.sp * (F.S.hm * F.S.tp + F.S.tm * F.S.hp) ∧
      F.S.kp * (1 - F.S.tp) < F.S.hm * F.S.sp * (1 - F.S.tp) + F.S.hp * (1 - F.S.tm * F.S.sp)
  · exact F.famAz (F.zFrame.A1_of h2') hfZ.1 hfZ.2
  have hCm := F.S.cm_ge hst hfA
  have hCp := F.S.swap.cm_ge hst' hfZ
  obtain ⟨α, γ, k1, k2, k3⟩ := F.S.exists_view_F2 hVp hVm hCm hCp
  exact F.rupert_of_F2_view hx α γ k1 k2 k3

end Frame18

end Minimality.CaseC18

end
