module

public import Minimality.Unimodal

@[expose] public section

/-!
# Theorem 7.3 with ties: robustly unimodal rims (`FEWER-FACES-PROOFS.md` §18.3)

Theorem 7.3 (`hasHorizontalDoubleNormal_of_forces`) asks for *distinct* cyclically unimodal
corner depths.  Theorem 18.3 allows ties, as long as the depths are *robustly unimodal*: every
sufficiently small perturbation with distinct entries is unimodal.  For a cyclic sequence this
means (§18.0):
* (R1) no two weak peaks: no positions `a, b, c, d` in cyclic order with `z a, z c` strictly
  above `z b, z d` (every superlevel set is a cyclic interval);
* (R2) no three equal entries;
* (R3) no level edge inside a monotone run.

`IsRobustUnimodal` states (R3) for any four positions in cyclic order (`z p < z a = z c < z q`
or the reverse), not only for adjacent `a, c`.  Under (R1) and (R2) the two forms are
equivalent (the entries between `a` and `c` would be a third equal entry), and this form is
closed under cyclic subsequences, which is what the force argument needs: the depths of the
forced corners form a cyclic subsequence of the rim.  For a triangle (R2) excludes the level
triangle, whose rim always has a horizontal double normal (§18.3); this is the only place where
`IsRobustUnimodal` is stronger than the paper's notion.

* `IsCyclicUnimodal.isRobustUnimodal`: distinct unimodal depths are robustly unimodal;
  `isRobustUnimodal_three`: a triangle with not all depths equal;
  `isRobustUnimodal_of_single_tie` (the core of Lemma 18.4 (α)): a rim with exactly one tied
  pair that is robustly unimodal after breaking the tie either way;
  `isRobustUnimodal_of_tendsto`, `isRobustUnimodal_of_tendsto_single_tie`: limits (Lemma 18.2
  (b) at the limit's own metric, and 18.4 (α));
  `IsCcwPolygon.isRobustUnimodal_affine`: planar rims (a nonconstant affine depth on a
  strictly convex polygon).
* `CycBetween`, `IsRobustUnimodal.comp`: robust unimodality passes to cyclic subsequences;
  `IsCcwPolygon.cross2_fan_pos`, `IsCcwPolygon.cross2_pos_of_cycBetween`: corners of a
  strictly convex polygon in cyclic order are in counterclockwise order.
* `deg_lemma_weak`, `forces_parallel_weak`: Steps 2–4 of Theorem 7.3 with weakly monotone runs
  (the paper's Step 4 (ii) with zero weights: a stretch of the force polygon off the
  separating line carries no weight, so two forced corners have equal depth between a strictly
  higher and a strictly lower one, against (R2) or (R3)).
* `hasHorizontalDoubleNormal_of_forces_robust` (**Theorem 18.3**, polygon form): balanced corner
  forces on a strictly convex polygon with robustly unimodal depths give a horizontal double
  normal.
* `exists_firstOrderInward_of_robustUnimodal`, `isRupert_of_robustUnimodalView`: the explicit
  view forms, as for Theorem 7.3.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-! ### Robust unimodality -/

/-- **Robust unimodality** of a cyclic sequence (§18.0, (R1)–(R3)).  Positions
`B + a, B + b, B + c, B + d` with `a < b < c < d < k` are four distinct positions in cyclic
order. -/
structure IsRobustUnimodal {k : ℕ} (z : ZMod k → ℝ) : Prop where
  /-- (R1) no two weak peaks. -/
  noPeaks : ∀ (B : ZMod k) (a b c d : ℕ), a < b → b < c → c < d → d < k →
    ¬ (z (B + b) < z (B + a) ∧ z (B + b) < z (B + c) ∧ z (B + d) < z (B + a) ∧
      z (B + d) < z (B + c))
  /-- (R2) no three equal entries. -/
  noTriple : ∀ i j l : ZMod k, i ≠ j → j ≠ l → i ≠ l → z i = z j → z j = z l → False
  /-- (R3) no level pair strictly inside a monotone run. -/
  noLevelRun : ∀ (B : ZMod k) (a b c d : ℕ), a < b → b < c → c < d → d < k →
    z (B + b) = z (B + c) →
      ¬ (z (B + a) < z (B + b) ∧ z (B + c) < z (B + d)) ∧
      ¬ (z (B + b) < z (B + a) ∧ z (B + d) < z (B + c))

theorem zmod_add_natCast_wrap {k : ℕ} (B : ZMod k) {a b : ℕ} (_hab : a < b) (hbk : b ≤ k) :
    B + (b : ZMod k) + ((k - b + a : ℕ) : ZMod k) = B + a := by
  rw [Nat.cast_add, Nat.cast_sub hbk, ZMod.natCast_self]; ring

/-- (R1) in the other phase: no two weak peaks read from a valley. -/
theorem IsRobustUnimodal.noPeaks' {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z)
    (B : ZMod k) {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hdk : d < k) :
    ¬ (z (B + a) < z (B + b) ∧ z (B + c) < z (B + b) ∧ z (B + a) < z (B + d) ∧
      z (B + c) < z (B + d)) := by
  rintro ⟨h1, h2, h3, h4⟩
  have e1 := zmod_add_natCast_sub B hbc.le
  have e2 := zmod_add_natCast_sub B (hbc.trans hcd).le
  have e3 := zmod_add_natCast_wrap B hab (by omega : b ≤ k)
  refine hz.noPeaks (B + b) 0 (c - b) (d - b) (k - b + a) (by omega) (by omega) (by omega)
    (by omega) ?_
  rw [Nat.cast_zero, add_zero, e1, e2, e3]
  exact ⟨h2, by linarith, by linarith, h3⟩

/-- Distinct unimodal depths are robustly unimodal. -/
theorem IsCyclicUnimodal.isRobustUnimodal {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) : IsRobustUnimodal z where
  noPeaks B a b c d hab hbc hcd hdk h :=
    hz.noZig B hab hbc hcd hdk (Or.inr ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩)
  noTriple i j _ hij _ _ h _ := hij (hz.1 h)
  noLevelRun B a b c d hab hbc hcd hdk h :=
    absurd (hz.1 h) (zmod_add_ne (by omega) (by omega) hbc.ne B)

/-- A triangle whose depths are not all equal is robustly unimodal. -/
theorem isRobustUnimodal_three {z : ZMod 3 → ℝ} (hz : ¬ (z 0 = z 1 ∧ z 1 = z 2)) :
    IsRobustUnimodal z where
  noPeaks _ _ _ _ _ _ _ _ _ := by omega
  noTriple i j l hij hjl hil h1 h2 := by
    have hall : ∀ i j l x : ZMod 3, i ≠ j → j ≠ l → i ≠ l → x = i ∨ x = j ∨ x = l := by decide
    have hx : ∀ x, z x = z i := fun x => by
      rcases hall i j l x hij hjl hil with rfl | rfl | rfl
      · rfl
      · exact h1.symm
      · rw [h1, h2]
    exact hz ⟨by rw [hx 0, hx 1], by rw [hx 1, hx 2]⟩
  noLevelRun _ _ _ _ _ _ _ _ _ := by omega

/-- **Lemma 18.4 (α), the sequence core.**  A cyclic sequence `z` whose only tie is the pair
`i, j` is robustly unimodal if breaking the tie either way (`z⁺ j < z⁺ i`, `z⁻ i < z⁻ j`, every
strict comparison of `z` kept) gives a robustly unimodal sequence (for instance a unimodal one,
`IsCyclicUnimodal.isRobustUnimodal`). -/
theorem isRobustUnimodal_of_single_tie {k : ℕ} {z zp zm : ZMod k → ℝ} {i j : ZMod k}
    (hone : ∀ a b, a ≠ b → z a = z b → (a = i ∧ b = j) ∨ (a = j ∧ b = i))
    (hp : IsRobustUnimodal zp) (hm : IsRobustUnimodal zm)
    (hpres : ∀ a b, z a < z b → zp a < zp b ∧ zm a < zm b)
    (hij : zp j < zp i ∧ zm i < zm j) : IsRobustUnimodal z where
  noPeaks B a b c d hab hbc hcd hdk h := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact hp.noPeaks B a b c d hab hbc hcd hdk ⟨(hpres _ _ h1).1, (hpres _ _ h2).1,
      (hpres _ _ h3).1, (hpres _ _ h4).1⟩
  noTriple a b c hab hbc hac h1 h2 := by
    rcases hone a b hab h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hone b c hbc h2 with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all
  noLevelRun B a b c d hab hbc hcd hdk h := by
    have hne := zmod_add_ne (by omega) (by omega) hbc.ne B
    -- in one of the two perturbations `B + b` is above `B + c`, in the other below
    have hsplit : (zp (B + c) < zp (B + b) ∧ zm (B + b) < zm (B + c)) ∨
        (zp (B + b) < zp (B + c) ∧ zm (B + c) < zm (B + b)) := by
      rcases hone _ _ hne h with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact Or.inl hij
      · rw [e1, e2]; exact Or.inr hij
    refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
    · have h3 : z (B + a) < z (B + d) := by linarith
      rcases hsplit with ⟨hp1, -⟩ | ⟨-, hm1⟩
      · exact hp.noPeaks' B hab hbc hcd hdk ⟨(hpres _ _ h1).1, hp1, (hpres _ _ h3).1,
          (hpres _ _ h2).1⟩
      · exact hm.noPeaks' B hab hbc hcd hdk ⟨(hpres _ _ h1).2, hm1, (hpres _ _ h3).2,
          (hpres _ _ h2).2⟩
    · have h3 : z (B + d) < z (B + a) := by linarith
      rcases hsplit with ⟨-, hm1⟩ | ⟨hp1, -⟩
      · exact hm.noPeaks B a b c d hab hbc hcd hdk ⟨(hpres _ _ h1).2, hm1, (hpres _ _ h3).2,
          (hpres _ _ h2).2⟩
      · exact hp.noPeaks B a b c d hab hbc hcd hdk ⟨(hpres _ _ h1).1, hp1, (hpres _ _ h3).1,
          (hpres _ _ h2).1⟩

/-- **Robust unimodality in the limit, distinct depths.**  If `z` has distinct entries and is a
limit of sequences that are robustly unimodal frequently (for instance unimodal: the corner
depths at nearby shapes or views), it is robustly unimodal.  Lemma 18.2 (b) at the shape's own
metric. -/
theorem isRobustUnimodal_of_tendsto {k : ℕ} {ι : Type*} {l : Filter ι}
    {zs : ι → ZMod k → ℝ} {z : ZMod k → ℝ}
    (hlim : ∀ i, Filter.Tendsto (fun n => zs n i) l (nhds (z i)))
    (hrob : ∃ᶠ n in l, IsRobustUnimodal (zs n)) (hz : Function.Injective z) :
    IsRobustUnimodal z where
  noPeaks B a b c d hab hbc hcd hdk h := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have ev : ∀ x y : ZMod k, z x < z y → ∀ᶠ n in l, zs n x < zs n y := fun x y hxy =>
      (hlim x).eventually_lt (hlim y) hxy
    obtain ⟨n, hn, e1, e2, e3, e4⟩ := (hrob.and_eventually ((ev _ _ h1).and ((ev _ _ h2).and
      ((ev _ _ h3).and (ev _ _ h4))))).exists
    exact hn.noPeaks B a b c d hab hbc hcd hdk ⟨e1, e2, e3, e4⟩
  noTriple _ _ _ hij _ _ h _ := hij (hz h)
  noLevelRun B a b c d hab hbc hcd hdk h :=
    absurd (hz h) (zmod_add_ne (by omega) (by omega) hbc.ne B)

/-- Strict comparisons survive in the limit, all at once. -/
theorem eventually_strict_order {k : ℕ} [NeZero k] {ι : Type*} {l : Filter ι}
    {zs : ι → ZMod k → ℝ} {z : ZMod k → ℝ}
    (hlim : ∀ i, Filter.Tendsto (fun n => zs n i) l (nhds (z i))) :
    ∀ᶠ n in l, ∀ a b, z a < z b → zs n a < zs n b := by
  refine Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr fun b => ?_
  by_cases h : z a < z b
  · exact ((hlim a).eventually_lt (hlim b) h).mono fun n hn _ => hn
  · exact Filter.Eventually.of_forall fun n hn => absurd hn h

/-- **Lemma 18.4 (α) in limit form.**  If `z` has exactly one tied pair `i, j`, and is a limit of
robustly unimodal sequences with `j` below `i` along one filter and with `i` below `j` along
another (the two sides of the tie), it is robustly unimodal. -/
theorem isRobustUnimodal_of_tendsto_single_tie {k : ℕ} [NeZero k] {ι κ : Type*} {l : Filter ι}
    {l' : Filter κ} {zs : ι → ZMod k → ℝ} {zs' : κ → ZMod k → ℝ}
    {z : ZMod k → ℝ} {i j : ZMod k}
    (hone : ∀ a b, a ≠ b → z a = z b → (a = i ∧ b = j) ∨ (a = j ∧ b = i))
    (hlim : ∀ i, Filter.Tendsto (fun n => zs n i) l (nhds (z i)))
    (hlim' : ∀ i, Filter.Tendsto (fun n => zs' n i) l' (nhds (z i)))
    (hrob : ∃ᶠ n in l, IsRobustUnimodal (zs n) ∧ zs n j < zs n i)
    (hrob' : ∃ᶠ n in l', IsRobustUnimodal (zs' n) ∧ zs' n i < zs' n j) :
    IsRobustUnimodal z := by
  obtain ⟨n, ⟨hn, hnij⟩, hno⟩ := (hrob.and_eventually (eventually_strict_order hlim)).exists
  obtain ⟨n', ⟨hn', hnij'⟩, hno'⟩ :=
    (hrob'.and_eventually (eventually_strict_order hlim')).exists
  exact isRobustUnimodal_of_single_tie hone hn hn' (fun a b h => ⟨hno a b h, hno' a b h⟩)
    ⟨hnij, hnij'⟩

/-! ### Cyclic order and cyclic subsequences -/

/-- `j` lies strictly between `i` and `l` going forward around `ZMod k` (`i, j, l` in cyclic
order, pairwise distinct). -/
def CycBetween {k : ℕ} (i j l : ZMod k) : Prop :=
  0 < (j - i).val ∧ (j - i).val < (l - i).val

theorem zmod_val_add_natCast_sub {k : ℕ} [NeZero k] (B : ZMod k) {a b : ℕ} (hab : a ≤ b)
    (hbk : b < k) : (B + (b : ZMod k) - (B + a)).val = b - a := by
  rw [show B + (b : ZMod k) - (B + a) = ((b - a : ℕ) : ZMod k) by
    rw [Nat.cast_sub hab]; ring, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

theorem cycBetween_of_lt {k : ℕ} [NeZero k] (B : ZMod k) {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hck : c < k) : CycBetween (B + (a : ZMod k)) (B + b) (B + c) := by
  unfold CycBetween
  rw [zmod_val_add_natCast_sub B hab.le (by omega), zmod_val_add_natCast_sub B (by omega) hck]
  omega

/-- Three distinct positions are in one of the two cyclic orders. -/
theorem cycBetween_or {k : ℕ} [NeZero k] {i j l : ZMod k} (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) : CycBetween i j l ∨ CycBetween i l j := by
  have h1 : 0 < (j - i).val := (ZMod.val_pos).mpr (sub_ne_zero.mpr hij.symm)
  have h2 : 0 < (l - i).val := (ZMod.val_pos).mpr (sub_ne_zero.mpr hil.symm)
  have h3 : (j - i).val ≠ (l - i).val := fun h => hjl (by
    have := congrArg (fun n : ℕ => (n : ZMod k)) h
    simp only [ZMod.natCast_zmod_val] at this
    linear_combination this)
  unfold CycBetween; omega

theorem CycBetween.ne {k : ℕ} [NeZero k] {i j l : ZMod k} (h : CycBetween i j l) :
    i ≠ j ∧ j ≠ l ∧ i ≠ l := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun e => by rw [e, sub_self, ZMod.val_zero] at h1; omega, fun e => by rw [e] at h2; omega,
    fun e => by rw [e, sub_self, ZMod.val_zero] at h2; omega⟩

/-- The four positions `i, j, l, n` read from `i` in cyclic order. -/
theorem exists_offsets_of_cycBetween {k : ℕ} [NeZero k] {i j l n : ZMod k}
    (h1 : CycBetween i j l) (h2 : CycBetween i l n) :
    ∃ b c d : ℕ, 0 < b ∧ b < c ∧ c < d ∧ d < k ∧ j = i + b ∧ l = i + c ∧ n = i + d :=
  ⟨(j - i).val, (l - i).val, (n - i).val, h1.1, h1.2, h2.2, ZMod.val_lt _,
    by rw [ZMod.natCast_zmod_val]; ring, by rw [ZMod.natCast_zmod_val]; ring,
    by rw [ZMod.natCast_zmod_val]; ring⟩

/-- **Robust unimodality passes to cyclic subsequences** (used in Theorem 18.3 for the forced
corners and in Lemma 18.2 for the corner rim): `σ` keeps the cyclic order of every triple. -/
theorem IsRobustUnimodal.comp {k k' : ℕ} [NeZero k] [NeZero k'] {z : ZMod k → ℝ}
    (hz : IsRobustUnimodal z) (σ : ZMod k' → ZMod k)
    (hσ : ∀ i j l, CycBetween i j l → CycBetween (σ i) (σ j) (σ l)) :
    IsRobustUnimodal (z ∘ σ) := by
  -- four positions in cyclic order go to four positions in cyclic order
  have h4 : ∀ (B : ZMod k') (a b c d : ℕ), a < b → b < c → c < d → d < k' →
      ∃ b' c' d' : ℕ, 0 < b' ∧ b' < c' ∧ c' < d' ∧ d' < k ∧
        σ (B + b) = σ (B + a) + b' ∧ σ (B + c) = σ (B + a) + c' ∧
        σ (B + d) = σ (B + a) + d' := fun B a b c d hab hbc hcd hdk =>
    exists_offsets_of_cycBetween (hσ _ _ _ (cycBetween_of_lt B hab hbc (by omega)))
      (hσ _ _ _ (cycBetween_of_lt B (hab.trans hbc) hcd hdk))
  refine ⟨fun B a b c d hab hbc hcd hdk h => ?_, fun i j l hij hjl hil e1 e2 => ?_,
    fun B a b c d hab hbc hcd hdk e => ?_⟩
  · obtain ⟨b', c', d', h0, h1, h2, h3, eb, ec, ed⟩ := h4 B a b c d hab hbc hcd hdk
    have := hz.noPeaks (σ (B + a)) 0 b' c' d' h0 h1 h2 h3
    simp only [Function.comp_apply, Nat.cast_zero, add_zero] at h this
    rw [← eb, ← ec, ← ed] at this
    exact this h
  · have hne : ∀ {i j l : ZMod k'}, CycBetween i j l → σ i ≠ σ j ∧ σ j ≠ σ l ∧ σ i ≠ σ l :=
      fun h => (hσ _ _ _ h).ne
    rcases cycBetween_or hij hjl hil with h | h
    · obtain ⟨n1, n2, n3⟩ := hne h
      exact hz.noTriple (σ i) (σ j) (σ l) n1 n2 n3 e1 e2
    · obtain ⟨n1, n2, n3⟩ := hne h
      exact hz.noTriple (σ i) (σ j) (σ l) n3 n2.symm n1 e1 e2
  · obtain ⟨b', c', d', h0, h1, h2, h3, eb, ec, ed⟩ := h4 B a b c d hab hbc hcd hdk
    have := hz.noLevelRun (σ (B + a)) 0 b' c' d' h0 h1 h2 h3
    simp only [Function.comp_apply, Nat.cast_zero, add_zero] at e ⊢ this
    rw [← eb, ← ec, ← ed] at this
    exact this e

/-- **Fan triangles of a strictly convex polygon are positive**: corners `i, i + a, i + b`
(`0 < a < b < k`) are in counterclockwise order. -/
theorem IsCcwPolygon.cross2_fan_pos {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} (hp : IsCcwPolygon p)
    (i : ZMod k) {a b : ℕ} (ha : 0 < a) (hab : a < b) (hbk : b < k) :
    0 < cross2 (p (i + a) - p i) (p (i + b) - p i) := by
  have hk := hp.1
  set v : ℕ → ℝ² := fun m => p (i + m) - p i with hv
  have hne : ∀ m : ℕ, 0 < m → m < k → i + (m : ZMod k) ≠ i := fun m h1 h2 =>
    (ne_add_natCast h1 h2 i).symm
  -- consecutive fan triangles
  have hcons : ∀ m : ℕ, 1 ≤ m → m + 1 < k → 0 < cross2 (v m) (v (m + 1)) := by
    intro m h1 h2
    have := hp.2 (i + m) i (hne m (by omega) (by omega)).symm (by
      rw [add_assoc, ← Nat.cast_succ]; exact (hne (m + 1) (by omega) h2).symm)
    rw [add_assoc, ← Nat.cast_succ] at this
    have e : cross2 (v m) (v (m + 1)) =
        cross2 (p (i + ((m + 1 : ℕ) : ZMod k)) - p (i + m)) (p i - p (i + m)) := by
      simp only [hv, cross2, PiLp.sub_apply]; ring
    rw [e]; exact this
  -- every fan vector is strictly left of `d`
  have hlast : i + ((k - 1 : ℕ) : ZMod k) + 1 = i := by
    rw [add_assoc, show ((k - 1 : ℕ) : ZMod k) + 1 = ((k - 1 + 1 : ℕ) : ZMod k) by push_cast; ring,
      show k - 1 + 1 = k by omega, ZMod.natCast_self, add_zero]
  have hfirst : ∀ m : ℕ, 2 ≤ m → m < k → 0 < cross2 (v 1) (v m) := by
    intro m h1 h2
    have := hp.2 i (i + m) (hne m (by omega) h2) (by
      have := zmod_add_ne (k := k) h2 (show 1 < k by omega) (show m ≠ 1 by omega) i
      rwa [Nat.cast_one] at this)
    simpa [hv] using this
  have hlst : ∀ m : ℕ, 1 ≤ m → m < k - 1 → 0 < cross2 (v m) (v (k - 1)) := by
    intro m h1 h2
    have := hp.2 (i + ((k - 1 : ℕ) : ZMod k)) (i + m) (by
      intro h; have := add_left_cancel h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : m < k),
        Nat.mod_eq_of_lt (by omega : k - 1 < k)] at this
      omega) (by rw [hlast]; exact hne m (by omega) (by omega))
    rw [hlast] at this
    have e : cross2 (v m) (v (k - 1)) =
        cross2 (p i - p (i + ((k - 1 : ℕ) : ZMod k)))
          (p (i + m) - p (i + ((k - 1 : ℕ) : ZMod k))) := by
      simp only [hv, cross2, PiLp.sub_apply]; ring
    rw [e]; exact this
  set d := v 1 - v (k - 1) with hd
  have hdpos : ∀ m : ℕ, 1 ≤ m → m ≤ k - 1 → 0 < cross2 d (v m) := by
    intro m h1 h2
    have e : cross2 d (v m) = cross2 (v 1) (v m) + cross2 (v m) (v (k - 1)) := by
      simp only [hd, cross2, PiLp.sub_apply]; ring
    rw [e]
    rcases eq_or_lt_of_le h1 with h | h
    · subst h
      have := hlst 1 le_rfl (by omega)
      rw [cross2_self]; linarith
    rcases eq_or_lt_of_le h2 with h' | h'
    · subst h'
      have := hfirst (k - 1) (by omega) (by omega)
      rw [cross2_self]; linarith
    linarith [hfirst m (by omega) (by omega), hlst m (by omega) h']
  -- transitivity of the orientation inside the half-plane left of `d`
  have htrans : ∀ x y w : ℝ², 0 < cross2 d x → 0 < cross2 d y → 0 < cross2 d w →
      0 < cross2 x y → 0 < cross2 y w → 0 < cross2 x w := by
    intro x y w hx hy hw hxy hyw
    have id : cross2 x y * cross2 d w + cross2 y w * cross2 d x + cross2 w x * cross2 d y = 0 := by
      simp only [cross2]; ring
    have : cross2 w x * cross2 d y < 0 := by nlinarith [mul_pos hxy hw, mul_pos hyw hx]
    have : cross2 w x < 0 := by
      by_contra hc; push Not at hc; nlinarith [mul_nonneg hc hy.le]
    rw [cross2_comm]; linarith
  have key : ∀ n : ℕ, ∀ b, b = a + 1 + n → b < k → 0 < cross2 (v a) (v b) := by
    intro n
    induction n with
    | zero => intro b hb hbk; subst hb; exact hcons a ha (by omega)
    | succ n ih =>
      intro b hb hbk
      subst hb
      have h1 := ih (a + 1 + n) rfl (by omega)
      have h2 := hcons (a + 1 + n) (by omega) (by omega)
      exact htrans _ _ _ (hdpos a ha (by omega)) (hdpos _ (by omega) (by omega))
        (hdpos _ (by omega) (by omega)) h1 (by rwa [show a + 1 + (n + 1) = a + 1 + n + 1 by omega])
  exact key (b - a - 1) b (by omega) hbk

/-- Corners in cyclic order are in counterclockwise order. -/
theorem IsCcwPolygon.cross2_pos_of_cycBetween {k : ℕ} [NeZero k] {p : ZMod k → ℝ²}
    (hp : IsCcwPolygon p) {i j l : ZMod k} (h : CycBetween i j l) :
    0 < cross2 (p j - p i) (p l - p i) := by
  have := hp.cross2_fan_pos i h.1 h.2 (ZMod.val_lt _)
  simpa only [ZMod.natCast_zmod_val, add_sub_cancel] using this

/-- The orientation of three distinct corners decides their cyclic order. -/
theorem IsCcwPolygon.cycBetween_of_cross2_pos {k : ℕ} [NeZero k] {p : ZMod k → ℝ²}
    (hp : IsCcwPolygon p) {i j l : ZMod k} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (h : 0 < cross2 (p j - p i) (p l - p i)) : CycBetween i j l := by
  rcases cycBetween_or hij hjl hil with h' | h'
  · exact h'
  · have := hp.cross2_pos_of_cycBetween h'
    rw [cross2_comm] at this; linarith

/-! ### Planar rims -/

/-- The affine dependency of four points in the plane, applied to a linear functional:
`[BCD] A − [ACD] B + [ABD] C − [ABC] D = 0` (`[XYZ] = cross2 (Y − X) (Z − X)`), and the
coefficients sum to zero. -/
theorem four_point_identity (A B C D e : ℝ²) (c : ℝ) :
    cross2 (C - B) (D - B) * (⟪e, A⟫ + c) - cross2 (C - A) (D - A) * (⟪e, B⟫ + c) +
      cross2 (B - A) (D - A) * (⟪e, C⟫ + c) - cross2 (B - A) (C - A) * (⟪e, D⟫ + c) = 0 := by
  simp only [cross2, PiLp.sub_apply, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    conj_trivial]
  ring

theorem cross2_eq_zero_of_inner {e x y : ℝ²} (he : e ≠ 0) (hx : ⟪e, x⟫ = 0) (hy : ⟪e, y⟫ = 0) :
    cross2 x y = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at hx hy
  have h0 : e 0 * cross2 x y = 0 := by simp only [cross2]; linear_combination y 1 * hx - x 1 * hy
  have h1 : e 1 * cross2 x y = 0 := by simp only [cross2]; linear_combination -(y 0) * hx + x 0 * hy
  by_contra hc
  apply he
  ext i; fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_right hc
  · exact (mul_eq_zero.mp h1).resolve_right hc

/-- **Planar rims are robustly unimodal** (Lemma 18.4, "planar and triangle rims"): on a
strictly convex polygon, a nonconstant affine depth `⟪e, p i⟫ + c` is robustly unimodal.  A
level pair lies on a level line, which can only support the polygon (no level edge inside a
run), and no three corners are collinear. -/
theorem IsCcwPolygon.isRobustUnimodal_affine {k : ℕ} [NeZero k] {p : ZMod k → ℝ²}
    (hp : IsCcwPolygon p) {e : ℝ²} (he : e ≠ 0) (c : ℝ) :
    IsRobustUnimodal (fun i => ⟪e, p i⟫ + c) := by
  -- the four triangles of four corners in cyclic order are positive
  have hpos : ∀ (B : ZMod k) (a b c d : ℕ), a < b → b < c → c < d → d < k →
      0 < cross2 (p (B + c) - p (B + b)) (p (B + d) - p (B + b)) ∧
      0 < cross2 (p (B + c) - p (B + a)) (p (B + d) - p (B + a)) ∧
      0 < cross2 (p (B + b) - p (B + a)) (p (B + d) - p (B + a)) ∧
      0 < cross2 (p (B + b) - p (B + a)) (p (B + c) - p (B + a)) :=
    fun B a b c d hab hbc hcd hdk =>
      ⟨hp.cross2_pos_of_cycBetween (cycBetween_of_lt B hbc hcd hdk),
        hp.cross2_pos_of_cycBetween (cycBetween_of_lt B (hab.trans hbc) hcd hdk),
        hp.cross2_pos_of_cycBetween (cycBetween_of_lt B hab (hbc.trans hcd) hdk),
        hp.cross2_pos_of_cycBetween (cycBetween_of_lt B hab hbc (hcd.trans hdk))⟩
  refine ⟨fun B a b c' d hab hbc hcd hdk h => ?_, fun i j l hij hjl hil e1 e2 => ?_,
    fun B a b c' d hab hbc hcd hdk hbc' => ?_⟩
  · obtain ⟨t1, t2, t3, t4⟩ := hpos B a b c' d hab hbc hcd hdk
    have id := four_point_identity (p (B + a)) (p (B + b)) (p (B + c')) (p (B + d)) e
      (c - (⟪e, p (B + b)⟫ + c) ⊔ (⟪e, p (B + d)⟫ + c))
    obtain ⟨h1, h2, h3, h4⟩ := h
    set m := (⟪e, p (B + b)⟫ + c) ⊔ (⟪e, p (B + d)⟫ + c)
    have hb : ⟪e, p (B + b)⟫ + c ≤ m := le_sup_left
    have hd : ⟪e, p (B + d)⟫ + c ≤ m := le_sup_right
    have hA : 0 < ⟪e, p (B + a)⟫ + (c - m) := by
      rcases max_cases (⟪e, p (B + b)⟫ + c) (⟪e, p (B + d)⟫ + c) with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
        simp only [m, hm] <;> linarith
    have hC : 0 < ⟪e, p (B + c')⟫ + (c - m) := by
      rcases max_cases (⟪e, p (B + b)⟫ + c) (⟪e, p (B + d)⟫ + c) with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
        simp only [m, hm] <;> linarith
    nlinarith [mul_pos t1 hA, mul_pos t3 hC, mul_nonneg t2.le (show 0 ≤ m - (⟪e, p (B + b)⟫ + c)
      by linarith), mul_nonneg t4.le (show 0 ≤ m - (⟪e, p (B + d)⟫ + c) by linarith)]
  · have hx : ⟪e, p j - p i⟫ = 0 := by rw [inner_sub_right]; linarith
    have hy : ⟪e, p l - p i⟫ = 0 := by rw [inner_sub_right]; linarith
    have h0 := cross2_eq_zero_of_inner he hx hy
    rcases cycBetween_or hij hjl hil with h | h
    · have := hp.cross2_pos_of_cycBetween h; linarith
    · have := hp.cross2_pos_of_cycBetween h; rw [cross2_comm] at this; linarith
  · obtain ⟨t1, t2, t3, t4⟩ := hpos B a b c' d hab hbc hcd hdk
    have id := four_point_identity (p (B + a)) (p (B + b)) (p (B + c')) (p (B + d)) e
      (c - (⟪e, p (B + b)⟫ + c))
    refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
    · nlinarith [mul_pos t1 (show 0 < (⟪e, p (B + b)⟫ + c) - (⟪e, p (B + a)⟫ + c) by linarith),
        mul_pos t4 (show 0 < (⟪e, p (B + d)⟫ + c) - (⟪e, p (B + c')⟫ + c) by linarith)]
    · nlinarith [mul_pos t1 (show 0 < (⟪e, p (B + a)⟫ + c) - (⟪e, p (B + b)⟫ + c) by linarith),
        mul_pos t4 (show 0 < (⟪e, p (B + c')⟫ + c) - (⟪e, p (B + d)⟫ + c) by linarith)]

/-! ### Steps 2–4 with weakly monotone runs -/

/-- **Step 4 (ii) with zero weights.**  As `deg_lemma`, with weights that may vanish at forced
corners.  Either every force is parallel to the first, or the force polygon leaves the
separating line along a stretch `(α, β)` of one arc that carries no weight, with forced corners
at both ends `α`, `β − 1`. -/
theorem deg_lemma_weak (g : ℕ → ℝ²) (m T : ℕ) (hT0 : 0 < T) (hTm : T < m)
    (h1 : ∑ s ∈ range m, g s = 0) (w : ℕ → ℝ)
    (hw : ((∀ n, 1 ≤ n → n ≤ T → 0 ≤ w n) ∧ (∀ n, T < n → n ≤ m → w n ≤ 0)) ∨
      ((∀ n, 1 ≤ n → n ≤ T → w n ≤ 0) ∧ (∀ n, T < n → n ≤ m → 0 ≤ w n)))
    (hOr : ∃ j, j ≤ m ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (g 0) (g s)) ∧
      (∀ s, j ≤ s → s < m → cross2 (g 0) (g s) ≤ 0))
    (hAbel : ∑ n ∈ Ico 1 (m + 1), w n *
      cross2 (g 0) (∑ s ∈ range n, g s - (1 / 2 : ℝ) • g 0) = 0)
    (hmid : cross2 (g 0) (∑ s ∈ range T, g s + (1 / 2 : ℝ) • g T - (1 / 2 : ℝ) • g 0) = 0) :
    (∀ s < m, cross2 (g 0) (g s) = 0) ∨
      ∃ α β, 1 ≤ α ∧ α + 1 < β ∧ β ≤ m ∧ (β ≤ T ∨ T < α) ∧ g α ≠ 0 ∧ g (β - 1) ≠ 0 ∧
        ∀ n, α < n → n < β → w n = 0 := by
  classical
  set y : ℕ → ℝ := fun s => cross2 (g 0) (g s) with hy
  have hy0 : y 0 = 0 := cross2_self _
  set Ψ : ℕ → ℝ := fun n => ∑ s ∈ range n, y s with hΨ
  have hΨeq : ∀ n, cross2 (g 0) (∑ s ∈ range n, g s - (1 / 2 : ℝ) • g 0) = Ψ n := fun n => by
    rw [cross2_sub_right, cross2_sum_right, cross2_smul_right, cross2_self]; simp [hΨ, hy]
  simp only [hΨeq] at hAbel
  have hΨ1 : Ψ 1 = 0 := by simp [hΨ, hy0]
  have hΨm : Ψ m = 0 := by
    have := congrArg (cross2 (g 0)) h1
    rw [cross2_sum_right] at this
    simpa [hΨ, hy, cross2] using this
  have hmid' : Ψ T + y T / 2 = 0 := by
    rw [cross2_sub_right, cross2_add_right, cross2_sum_right, cross2_smul_right,
      cross2_smul_right, cross2_self] at hmid
    simp only [hΨ, hy]; linarith
  have hΨT1 : Ψ (T + 1) = Ψ T + y T := by simp [hΨ, sum_range_succ]
  have hstep : ∀ n, Ψ (n + 1) = Ψ n + y n := fun n => by simp [hΨ, sum_range_succ]
  obtain ⟨j, hjm, hjpos, hjneg⟩ := hOr
  have hnonneg : ∀ n, 1 ≤ n → n ≤ m → 0 ≤ Ψ n := by
    intro n hn1 hnm
    rcases le_total n j with hnj | hnj
    · have := psum_mono hn1 (fun r hr1 hr2 => hjpos r (by omega) (by omega))
      simp only [hΨ] at hΨ1 ⊢; linarith
    · have := psum_anti hnm (fun r hr1 hr2 => hjneg r (by omega) hr2)
      simp only [hΨ] at hΨm ⊢; linarith
  have hT0' := hnonneg T hT0 hTm.le
  have hT1' := hnonneg (T + 1) (by omega) (by omega)
  have hΨT : Ψ T = 0 := by linarith
  have hΨT1' : Ψ (T + 1) = 0 := by linarith
  have hzero_part : (∀ n, 1 ≤ n → n ≤ T → Ψ n = 0) ∨ (∀ n, T < n → n ≤ m → Ψ n = 0) := by
    rcases le_total T j with hTj | hTj
    · left
      intro n hn1 hnT
      have := psum_mono hnT (fun r hr1 hr2 => hjpos r (by omega) (by omega))
      simp only [hΨ] at hΨT ⊢
      linarith [hnonneg n hn1 (by omega)]
    · right
      intro n hn1 hnm
      have := psum_anti hn1 (fun r hr1 hr2 => hjneg r (by omega) (by omega))
      simp only [hΨ] at hΨT1' ⊢
      linarith [hnonneg n (by omega) hnm]
  have hsplit : ∑ n ∈ Ico 1 (m + 1), w n * Ψ n =
      ∑ n ∈ Ico 1 (T + 1), w n * Ψ n + ∑ n ∈ Ico (T + 1) (m + 1), w n * Ψ n :=
    (sum_Ico_consecutive _ (by omega) (by omega)).symm
  -- the other arc `[L, R]`: zero at its ends, every term `w n Ψ n` zero on it
  obtain ⟨L, R, hL1, hLR, hRm, harc, hΨL, hΨR, hout, hterm⟩ : ∃ L R, 1 ≤ L ∧ L ≤ R ∧ R ≤ m ∧
      (R ≤ T ∨ T < L) ∧ Ψ L = 0 ∧ Ψ R = 0 ∧
      (∀ n, 1 ≤ n → n ≤ m → (n < L ∨ R < n) → Ψ n = 0) ∧
      ∀ n, L ≤ n → n ≤ R → w n * Ψ n = 0 := by
    rcases hzero_part with hz | hz
    · have hfirst : ∑ n ∈ Ico 1 (T + 1), w n * Ψ n = 0 :=
        sum_eq_zero fun n hn => by rw [mem_Ico] at hn; rw [hz n hn.1 (by omega), mul_zero]
      rw [hsplit, hfirst, zero_add] at hAbel
      refine ⟨T + 1, m, by omega, by omega, le_rfl, Or.inr (by omega), hΨT1', hΨm,
        fun n h1 h2 h3 => hz n h1 (by omega), fun n h1 h2 => ?_⟩
      have hn : n ∈ Ico (T + 1) (m + 1) := mem_Ico.mpr ⟨by omega, by omega⟩
      rcases hw with ⟨_, hw2⟩ | ⟨_, hw2⟩
      · exact (sum_eq_zero_iff_of_nonpos fun r hr => by
          rw [mem_Ico] at hr
          exact mul_nonpos_of_nonpos_of_nonneg (hw2 r (by omega) (by omega))
            (hnonneg r (by omega) (by omega))).mp hAbel n hn
      · exact (sum_eq_zero_iff_of_nonneg fun r hr => by
          rw [mem_Ico] at hr
          exact mul_nonneg (hw2 r (by omega) (by omega))
            (hnonneg r (by omega) (by omega))).mp hAbel n hn
    · have hsecond : ∑ n ∈ Ico (T + 1) (m + 1), w n * Ψ n = 0 :=
        sum_eq_zero fun n hn => by rw [mem_Ico] at hn; rw [hz n (by omega) (by omega), mul_zero]
      rw [hsplit, hsecond, add_zero] at hAbel
      refine ⟨1, T, le_rfl, hT0, hTm.le, Or.inl le_rfl, hΨ1, hΨT,
        fun n h1 h2 h3 => hz n (by omega) h2, fun n h1 h2 => ?_⟩
      have hn : n ∈ Ico 1 (T + 1) := mem_Ico.mpr ⟨h1, by omega⟩
      rcases hw with ⟨hw1, _⟩ | ⟨hw1, _⟩
      · exact (sum_eq_zero_iff_of_nonneg fun r hr => by
          rw [mem_Ico] at hr
          exact mul_nonneg (hw1 r hr.1 (by omega)) (hnonneg r hr.1 (by omega))).mp hAbel n hn
      · exact (sum_eq_zero_iff_of_nonpos fun r hr => by
          rw [mem_Ico] at hr
          exact mul_nonpos_of_nonpos_of_nonneg (hw1 r hr.1 (by omega))
            (hnonneg r hr.1 (by omega))).mp hAbel n hn
  by_cases hall : ∀ n, L ≤ n → n ≤ R → Ψ n = 0
  · left
    have hΨ0 : ∀ n, 1 ≤ n → n ≤ m → Ψ n = 0 := fun n h1 h2 => by
      by_cases h : n < L ∨ R < n
      · exact hout n h1 h2 h
      · exact hall n (by omega) (by omega)
    intro s hs
    show y s = 0
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · exact hy0
    have := hstep s
    rw [hΨ0 s hs0 hs.le, hΨ0 (s + 1) (by omega) (by omega)] at this
    linarith
  right
  push Not at hall
  obtain ⟨n0, hLn0, hn0R, hΨn0⟩ := hall
  have hn0L : L < n0 := lt_of_le_of_ne hLn0 (fun h => hΨn0 (h ▸ hΨL))
  have hn0R' : n0 < R := lt_of_le_of_ne hn0R (fun h => hΨn0 (h ▸ hΨR))
  -- the last zero before `n0` and the first zero after it
  set P : ℕ → Prop := fun n => L ≤ n ∧ Ψ n = 0 with hP
  set α := Nat.findGreatest P n0 with hα
  have hPα : P α := Nat.findGreatest_spec (P := P) hLn0 ⟨le_rfl, hΨL⟩
  have hαn0 : α < n0 := lt_of_le_of_ne (Nat.findGreatest_le n0) (fun h => hΨn0 (h ▸ hPα.2))
  have hex : ∃ n, n0 ≤ n ∧ Ψ n = 0 := ⟨R, hn0R, hΨR⟩
  set β := Nat.find hex with hβ
  have hβspec := Nat.find_spec hex
  have hβR : β ≤ R := Nat.find_min' hex ⟨hn0R, hΨR⟩
  have hn0β : n0 < β := lt_of_le_of_ne hβspec.1 (fun h => hΨn0 (h ▸ hβspec.2))
  have hpos : ∀ n, α < n → n < β → Ψ n ≠ 0 := by
    intro n h1 h2 h0
    rcases le_or_gt n n0 with hn | hn
    · exact Nat.findGreatest_is_greatest h1 hn ⟨by have := hPα.1; omega, h0⟩
    · exact Nat.find_min hex h2 ⟨hn.le, h0⟩
  refine ⟨α, β, by have := hPα.1; omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rcases harc with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by have := hPα.1; omega)
  · intro hg
    have := hstep α
    rw [hPα.2, show y α = 0 by simp [hy, hg, cross2]] at this
    exact hpos (α + 1) (by omega) (by omega) (by linarith)
  · intro hg
    have := hstep (β - 1)
    rw [show β - 1 + 1 = β by omega, hβspec.2, show y (β - 1) = 0 by simp [hy, hg, cross2]] at this
    exact hpos (β - 1) (by omega) (by omega) (by linarith)
  · intro n h1 h2
    have := hterm n (by have := hPα.1; omega) (by omega)
    exact (mul_eq_zero.mp this).resolve_right (hpos n h1 h2)

/-- **Theorem 7.3, Steps 2–4, with ties (Theorem 18.3).**  As `forces_parallel`, with the
depths of the forced corners only weakly rising from `0` to `T` and weakly falling back
(`ζ 0 < ζ T`), no three of them equal (`hR2`, (R2)), and no two equal ones strictly between a
lower and a higher one in cyclic order (`hR3`, (R3); the fourth position `d = m` is `0`). -/
theorem forces_parallel_weak (g : ℕ → ℝ²) (ζ : ℕ → ℝ) (m T : ℕ) (hT0 : 0 < T) (hTm : T < m)
    (hg0 : g 0 ≠ 0) (hgT : g T ≠ 0)
    (h1 : ∑ s ∈ range m, g s = 0) (h2 : ∑ s ∈ range m, ζ s • g s = 0)
    (hrise : ∀ a b, a < b → b ≤ T → g a ≠ 0 → g b ≠ 0 → ζ a ≤ ζ b)
    (hfall : ∀ a b, T ≤ a → a < b → b < m → g a ≠ 0 → g b ≠ 0 → ζ b ≤ ζ a)
    (hbot : ∀ a, 0 < a → a < m → g a ≠ 0 → ζ 0 ≤ ζ a)
    (h0T : ζ 0 < ζ T)
    (hR2 : ∀ a b c, a < b → b < c → c < m → g a ≠ 0 → g b ≠ 0 → g c ≠ 0 →
      ζ a = ζ b → ζ b = ζ c → False)
    (hR3 : ∀ a b c d, a < b → b < c → c < d → d ≤ m → g a ≠ 0 → g b ≠ 0 → g c ≠ 0 →
      g (d % m) ≠ 0 → ζ b = ζ c →
      ¬ (ζ a < ζ b ∧ ζ c < ζ (d % m)) ∧ ¬ (ζ b < ζ a ∧ ζ (d % m) < ζ c))
    (hSS : ∀ D, SSlin (fun s => cross2 D (g s)) m)
    (hOr0 : ∃ j, j ≤ m ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (g 0) (g s)) ∧
      (∀ s, j ≤ s → s < m → cross2 (g 0) (g s) ≤ 0))
    (hOrT : ∃ j, j ≤ m ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (g T) (g ((T + s) % m))) ∧
      (∀ s, j ≤ s → s < m → cross2 (g T) (g ((T + s) % m)) ≤ 0)) :
    ∀ s < m, cross2 (g 0) (g s) = 0 := by
  classical
  have hm : 0 < m := by omega
  -- fill the depths at force-free corners by the last forced depth
  set P : ℕ → Prop := fun j => g j ≠ 0 with hP
  set ζf : ℕ → ℝ := fun n => ζ (Nat.findGreatest P n) with hζf
  have hfg_self : ∀ n, g n ≠ 0 → Nat.findGreatest P n = n := fun n h => Nat.findGreatest_eq h
  have hfg_spec : ∀ n, g (Nat.findGreatest P n) ≠ 0 := fun n =>
    Nat.findGreatest_spec (P := P) (Nat.zero_le n) hg0
  have hfg_le : ∀ n, Nat.findGreatest P n ≤ n := fun n => Nat.findGreatest_le n
  have hfg_ge : ∀ n j, j ≤ n → g j ≠ 0 → j ≤ Nat.findGreatest P n := fun n j hj hg =>
    Nat.le_findGreatest hj hg
  have hfg_step : ∀ n, g (n + 1) = 0 → Nat.findGreatest P (n + 1) = Nat.findGreatest P n :=
    fun n h => Nat.findGreatest_of_not (by simpa [hP] using h)
  have e0 : Nat.findGreatest P 0 = 0 := Nat.findGreatest_eq hg0
  have hζf0 : ζf 0 = ζ 0 := by simp only [hζf, e0]
  have h2f : ∑ s ∈ range m, ζf s • g s = 0 := by
    rw [← h2]
    exact sum_congr rfl fun s _ => by
      by_cases hgs : g s = 0
      · simp [hgs]
      · simp only [hζf, hfg_self s hgs]
  set w : ℕ → ℝ := fun n => (if n = m then ζf 0 else ζf n) - ζf (n - 1) with hw
  have hwval : ∀ n, 1 ≤ n → n < m → w n = ζf n - ζf (n - 1) := fun n h1 h2 => by
    simp only [hw, ite_eq_right (show n ≠ m by omega)]
  have hw_supp : ∀ n, 1 ≤ n → n < m → g n ≠ 0 →
      w n = ζ n - ζ (Nat.findGreatest P (n - 1)) := fun n h1 h2 hg => by
    rw [hwval n h1 h2]; simp only [hζf, hfg_self n hg]
  have hw_zero : ∀ n, 1 ≤ n → n < m → g n = 0 → w n = 0 := fun n h1 h2 hg => by
    rw [hwval n h1 h2]
    simp only [hζf]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hfg_step n' hg, show n' + 1 - 1 = n' by omega, sub_self]
  have hw1 : ∀ n, 1 ≤ n → n ≤ T → 0 ≤ w n := by
    intro n h1 h2
    by_cases hg : g n = 0
    · rw [hw_zero n h1 (by omega) hg]
    · rw [hw_supp n h1 (by omega) hg]
      have := hrise (Nat.findGreatest P (n - 1)) n (by have := hfg_le (n - 1); omega) h2
        (hfg_spec _) hg
      linarith
  have hwm : w m ≤ 0 := by
    have : w m = ζ 0 - ζ (Nat.findGreatest P (m - 1)) := by
      show (if m = m then ζf 0 else ζf m) - ζf (m - 1) = _
      rw [ite_eq_left rfl, hζf0]
    rw [this]
    have hge := hfg_ge (m - 1) T (by omega) hgT
    have := hbot (Nat.findGreatest P (m - 1)) (by omega) (by have := hfg_le (m - 1); omega)
      (hfg_spec _)
    linarith
  have hw2 : ∀ n, T < n → n ≤ m → w n ≤ 0 := by
    intro n h1 h2
    rcases eq_or_lt_of_le h2 with h2 | h2
    · rw [h2]; exact hwm
    · by_cases hg : g n = 0
      · rw [hw_zero n (by omega) h2 hg]
      · rw [hw_supp n (by omega) h2 hg]
        have hge := hfg_ge (n - 1) T (by omega) hgT
        have := hfall (Nat.findGreatest P (n - 1)) n hge (by have := hfg_le (n - 1); omega) h2
          (hfg_spec _) hg
        linarith
  -- some weight on the rising run is positive (the run rises from `ζ 0` to `ζ T`)
  have hwpos : ∃ n, 1 ≤ n ∧ n ≤ T ∧ 0 < w n := by
    by_contra hcon
    push Not at hcon
    have hc : ∀ n, n ≤ T → ζf n = ζf 0 := by
      intro n hn
      induction n with
      | zero => rfl
      | succ n ih =>
        have h0 : w (n + 1) = 0 := le_antisymm (hcon (n + 1) (by omega) hn) (hw1 _ (by omega) hn)
        rw [hwval (n + 1) (by omega) (by omega), Nat.add_sub_cancel] at h0
        rw [← ih (by omega)]; linarith
    have := hc T le_rfl
    simp only [hζf, hfg_self T hgT, e0] at this
    linarith
  -- a weightless stretch with forced ends is impossible
  have hstretch : ∀ α β, 1 ≤ α → α + 1 < β → β ≤ m → (β ≤ T ∨ T < α) → g α ≠ 0 →
      g (β - 1) ≠ 0 → (∀ n, α < n → n < β → w n = 0) → False := by
    intro α β hα1 hαβ hβm harc hgα hgβ hw0
    have hconst : ∀ n, α ≤ n → n ≤ β - 1 → ζf n = ζf α := by
      intro n hn1 hn2
      induction n with
      | zero => omega
      | succ n ih =>
        rcases eq_or_lt_of_le hn1 with h | h
        · rw [h]
        · have h0 := hw0 (n + 1) (by omega) (by omega)
          rw [hwval (n + 1) (by omega) (by omega), Nat.add_sub_cancel] at h0
          rw [← ih (by omega) (by omega)]; linarith
    have hζαβ : ζ α = ζ (β - 1) := by
      have := hconst (β - 1) (by omega) le_rfl
      simp only [hζf] at this
      rw [hfg_self _ hgβ, hfg_self _ hgα] at this
      exact this.symm
    -- the previous forced corner `p`
    set p := Nat.findGreatest P (α - 1) with hpdef
    have hpα : p < α := by have := hfg_le (α - 1); omega
    have hgp : g p ≠ 0 := hfg_spec (α - 1)
    have hwα : w α = ζ α - ζ p := hw_supp α hα1 (by omega) hgα
    -- the next forced corner `q` (`q = m` stands for `0`)
    have hex : ∃ n, β ≤ n ∧ (n = m ∨ (n < m ∧ g n ≠ 0)) := ⟨m, hβm, Or.inl rfl⟩
    have hfm := Nat.find_min' hex ⟨hβm, Or.inl rfl⟩
    obtain ⟨q, ⟨hqβ, hq⟩, hfree⟩ : ∃ q, (β ≤ q ∧ (q = m ∨ (q < m ∧ g q ≠ 0))) ∧
        ∀ n, β ≤ n → n < q → g n = 0 :=
      ⟨Nat.find hex, Nat.find_spec hex, fun n h1 h2 => by
        by_contra hg; exact Nat.find_min hex h2 ⟨h1, Or.inr ⟨by omega, hg⟩⟩⟩
    have hqm : q ≤ m := by rcases hq with hq | hq <;> omega
    have hζfq : ζf (q - 1) = ζ (β - 1) := by
      have hc : ∀ n, β - 1 ≤ n → n ≤ q - 1 → ζf n = ζf (β - 1) := by
        intro n h1 h2
        induction n with
        | zero => omega
        | succ n ih =>
          rcases eq_or_lt_of_le h1 with h | h
          · rw [h]
          · have : ζf (n + 1) = ζf n := by
              simp only [hζf]; rw [hfg_step n (hfree (n + 1) (by omega) (by omega))]
            rw [this]; exact ih (by omega) (by omega)
      rw [hc (q - 1) (by omega) le_rfl]; simp only [hζf, hfg_self _ hgβ]
    have hgq : g (q % m) ≠ 0 := by
      rcases hq with hq | ⟨hqm', hgq⟩
      · rw [hq, Nat.mod_self]; exact hg0
      · rwa [Nat.mod_eq_of_lt hqm']
    have hwq : w q = ζ (q % m) - ζ (β - 1) := by
      rcases hq with hq | ⟨hqm', hgq'⟩
      · show (if q = m then ζf 0 else ζf q) - ζf (q - 1) = _
        rw [ite_eq_left hq, hζfq, hζf0, hq, Nat.mod_self]
      · rw [hwval q (by omega) hqm', hζfq, Nat.mod_eq_of_lt hqm']
        simp only [hζf, hfg_self q hgq']
    rcases harc with harc | harc
    · -- on the rising run
      have hqT : q ≤ T := by
        by_contra hc; exact hgT (hfree T (by omega) (by omega))
      have hqm' : q % m = q := Nat.mod_eq_of_lt (by omega)
      rw [hqm'] at hwq hgq
      rcases eq_or_lt_of_le (hw1 α hα1 (by omega)) with h | h
      · exact hR2 p α (β - 1) hpα (by omega) (by omega) hgp hgα hgβ (by linarith) hζαβ
      rcases eq_or_lt_of_le (hw1 q (by omega) hqT) with h' | h'
      · exact hR2 α (β - 1) q (by omega) (by omega) (by omega) hgα hgβ hgq hζαβ (by linarith)
      exact (hR3 p α (β - 1) q hpα (by omega) (by omega) hqm hgp hgα hgβ
        (by rwa [hqm']) hζαβ).1 ⟨by linarith, by rw [hqm']; linarith⟩
    · -- on the falling run
      rcases eq_or_lt_of_le (hw2 α harc (by omega)) with h | h
      · exact hR2 p α (β - 1) hpα (by omega) (by omega) hgp hgα hgβ (by linarith) hζαβ
      rcases eq_or_lt_of_le (hw2 q (by omega) hqm) with h' | h'
      · rcases hq with hq | ⟨hqm', -⟩
        · subst hq
          rw [Nat.mod_self] at hwq
          exact hR2 0 α (β - 1) (by omega) (by omega) (by omega) hg0 hgα hgβ (by linarith)
            hζαβ
        · rw [Nat.mod_eq_of_lt hqm'] at hwq hgq
          exact hR2 α (β - 1) q (by omega) (by omega) hqm' hgα hgβ hgq hζαβ (by linarith)
      exact (hR3 p α (β - 1) q hpα (by omega) (by omega) hqm hgp hgα hgβ hgq hζαβ).2
        ⟨by linarith, by linarith⟩
  set V : ℕ → ℝ² := fun n => ∑ s ∈ range n, g s with hV
  set D := V T + (1 / 2 : ℝ) • g T - (1 / 2 : ℝ) • g 0 with hD
  by_cases ha : cross2 D (g 0) = 0
  · -- the separating line contains force edge `0`
    rcases deg_lemma_weak g m T hT0 hTm h1 w (Or.inl ⟨hw1, hw2⟩) hOr0
      (abel_identity g ζf m hm h1 h2f (g 0) ((1 / 2 : ℝ) • g 0))
      (by rw [cross2_comm]; simpa [hD, hV] using ha) with
      h | ⟨α, β, h1', h2', h3', h4', h5', h6', h7'⟩
    · exact h
    · exact (hstretch α β h1' h2' h3' h4' h5' h6' h7').elim
  by_cases hb : cross2 D (g T) = 0
  · -- the separating line contains force edge `T`: rotate `T` to the front
    set g' : ℕ → ℝ² := fun s => g ((T + s) % m) with hg'
    set ζ' : ℕ → ℝ := fun s => ζf ((T + s) % m) with hζ'
    have hg'0 : g' 0 = g T := by simp [hg', Nat.mod_eq_of_lt hTm]
    have hg'T : g' (m - T) = g 0 := by simp [hg', show T + (m - T) = m by omega]
    have h1' : ∑ s ∈ range m, g' s = 0 := by rw [sum_range_rotate g m T hTm]; exact h1
    have h2' : ∑ s ∈ range m, ζ' s • g' s = 0 := by
      rw [sum_range_rotate (fun r => ζf r • g r) m T hTm]; exact h2f
    have hV' : ∑ s ∈ range (m - T), g' s = -V T := by
      have e : ∑ s ∈ range (m - T), g' s = ∑ r ∈ Ico T m, g r := by
        rw [sum_Ico_eq_sum_range]
        exact sum_congr rfl fun s hs => by
          rw [mem_range] at hs; simp [hg', Nat.mod_eq_of_lt (show T + s < m by omega)]
      rw [e]
      have := sum_range_add_sum_Ico g hTm.le
      rw [h1] at this
      simp only [hV]
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
    set w' : ℕ → ℝ := fun n => (if n = m then ζ' 0 else ζ' n) - ζ' (n - 1) with hw'
    -- the rotated weights are the weights at the rotated index
    have hw'eq : ∀ n, 1 ≤ n → n ≤ m →
        w' n = w (if T + n < m then T + n else if T + n = m then m else T + n - m) := by
      intro n h1 h2
      rcases eq_or_lt_of_le h2 with h2 | h2
      · have e1 : T % m = T := Nat.mod_eq_of_lt hTm
        have e2 : (T + (n - 1)) % m = T - 1 := by
          rw [show T + (n - 1) = (T - 1) + m by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        have e3 : (if T + n < m then T + n else if T + n = m then m else T + n - m) = T := by
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
        rw [e3]
        simp only [hw', hζ', hw]
        rw [ite_eq_left h2, ite_eq_right (by omega), Nat.add_zero, e1, e2]
      · by_cases hlt : T + n < m
        · have e1 : (T + n) % m = T + n := Nat.mod_eq_of_lt hlt
          have e2 : (T + (n - 1)) % m = T + n - 1 := by
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          simp only [hw', hζ', hw]
          rw [ite_eq_right (by omega), ite_eq_left hlt, ite_eq_right (by omega), e1, e2]
        · by_cases heq : T + n = m
          · have e1 : (T + n) % m = 0 := by rw [heq, Nat.mod_self]
            have e2 : (T + (n - 1)) % m = m - 1 := by
              rw [Nat.mod_eq_of_lt (by omega)]; omega
            simp only [hw', hζ', hw]
            rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_left heq, ite_eq_left rfl, e1,
              e2]
          · have e1 : (T + n) % m = T + n - m := by
              rw [show T + n = (T + n - m) + m by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]; omega
            have e2 : (T + (n - 1)) % m = T + n - m - 1 := by
              rw [show T + (n - 1) = (T + n - m - 1) + m by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]
            simp only [hw', hζ', hw]
            rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_right heq,
              ite_eq_right (by omega), e1, e2]
    have hwr1 : ∀ n, 1 ≤ n → n ≤ m - T → w' n ≤ 0 := by
      intro n h1 h2
      rw [hw'eq n h1 (by omega)]
      split_ifs with ha hb'
      · exact hw2 _ (by omega) (by omega)
      · exact hwm
      · omega
    have hwr2 : ∀ n, m - T < n → n ≤ m → 0 ≤ w' n := by
      intro n h1 h2
      rw [hw'eq n (by omega) h2]
      split_ifs with ha hb'
      · omega
      · omega
      · exact hw1 _ (by omega) (by omega)
    rcases deg_lemma_weak g' m (m - T) (by omega) (by omega) h1' w'
      (Or.inr ⟨hwr1, hwr2⟩) (by simpa [hg'0] using hOrT)
      (abel_identity g' ζ' m hm h1' h2' (g' 0) ((1 / 2 : ℝ) • g' 0))
      (by
        rw [hV', hg'T, hg'0]
        have : -V T + (1 / 2 : ℝ) • g 0 - (1 / 2 : ℝ) • g T = -D := by
          simp only [hD]; abel
        rw [this, cross2_neg_right, cross2_comm, neg_neg]
        simpa using hb) with hdeg | ⟨α, β, hα1, hαβ, hβm, harc, hgα, hgβ, hw0⟩
    · have hall : ∀ r < m, cross2 (g T) (g r) = 0 := by
        intro r hr
        have := hdeg ((r + (m - T)) % m) (Nat.mod_lt _ hm)
        rw [hg'0] at this
        simp only [hg'] at this
        rwa [Nat.add_mod_mod, show T + (r + (m - T)) = r + m by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hr] at this
      intro r hr
      exact cross2_trans hgT (hall 0 hm) (hall r hr)
    · -- translate the rotated stretch back
      exfalso
      rcases harc with harc | harc
      · refine hstretch (T + α) (T + β) (by omega) (by omega) (by omega) (Or.inr (by omega))
          ?_ ?_ fun n h1 h2 => ?_
        · simpa [hg', Nat.mod_eq_of_lt (show T + α < m by omega)] using hgα
        · have e : (T + (β - 1)) % m = T + β - 1 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
          simpa [hg', e] using hgβ
        · have := hw0 (n - T) (by omega) (by omega)
          rw [hw'eq (n - T) (by omega) (by omega)] at this
          split_ifs at this with h3 h4
          · rwa [show T + (n - T) = n by omega] at this
          · rwa [show n = m by omega]
          · omega
      · refine hstretch (T + α - m) (T + β - m) (by omega) (by omega) (by omega)
          (Or.inl (by omega)) ?_ ?_ fun n h1 h2 => ?_
        · have e : (T + α) % m = T + α - m := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          simpa [hg', e] using hgα
        · have e : (T + (β - 1)) % m = T + β - m - 1 := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          simpa [hg', e] using hgβ
        · have := hw0 (n + m - T) (by omega) (by omega)
          rw [hw'eq (n + m - T) (by omega) (by omega)] at this
          split_ifs at this with h3 h4
          · omega
          · omega
          · rwa [show T + (n + m - T) - m = n by omega] at this
  -- generic case: strict separation, contradicting the depth balance
  exfalso
  set x : ℕ → ℝ := fun s => cross2 D (g s) with hx
  have hsum : ∑ r ∈ range m, x r = 0 := by
    have := congrArg (cross2 D) h1
    rw [cross2_sum_right] at this
    simpa [hx, cross2] using this
  have hY : ∀ n, cross2 D (∑ s ∈ range n, g s - (1 / 2 : ℝ) • g 0) =
      ∑ r ∈ range n, x r - x 0 / 2 := by
    intro n
    rw [cross2_sub_right, cross2_sum_right, cross2_smul_right]
    simp only [hx]
    ring
  have hmid : (∑ r ∈ range T, x r - x 0 / 2) + x T / 2 = 0 := by
    rw [← hY]
    have e : (∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + (1 / 2 : ℝ) • g T = D := by
      simp only [hD, hV]; abel
    have : cross2 D (∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + x T / 2 = cross2 D D := by
      calc cross2 D (∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + x T / 2
          = cross2 D ((∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + (1 / 2 : ℝ) • g T) := by
            rw [cross2_add_right, cross2_smul_right]; simp only [hx]; ring
        _ = cross2 D D := by rw [e]
    rw [this, cross2_self]
  obtain ⟨hpos, hneg⟩ := sign_lemma x m T hT0 hTm (hSS D) hsum hmid ha hb
  have habel := abel_identity g ζf m hm h1 h2f D ((1 / 2 : ℝ) • g 0)
  simp only [hY] at habel
  obtain ⟨n₁, hn₁1, hn₁T, hwn₁⟩ := hwpos
  have : 0 < ∑ n ∈ Ico 1 (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) := by
    rw [← sum_Ico_consecutive _ (show 1 ≤ T + 1 by omega) (show T + 1 ≤ m + 1 by omega)]
    have hA : 0 < ∑ n ∈ Ico 1 (T + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) := by
      rw [← add_sum_erase _ _ (mem_Ico.mpr ⟨hn₁1, by omega⟩ : n₁ ∈ Ico 1 (T + 1))]
      have hTterm := mul_pos hwn₁ (hpos n₁ hn₁1 hn₁T)
      have hrest : 0 ≤ ∑ n ∈ (Ico 1 (T + 1)).erase n₁,
          w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) := sum_nonneg fun n hn => by
        have hn' := mem_Ico.mp (mem_of_mem_erase hn)
        exact mul_nonneg (hw1 n hn'.1 (by omega)) (hpos n hn'.1 (by omega)).le
      linarith
    have hB : 0 ≤ ∑ n ∈ Ico (T + 1) (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) :=
      sum_nonneg fun n hn => by
        rw [mem_Ico] at hn
        exact mul_nonneg_of_nonpos_of_nonpos (hw2 n (by omega) (by omega))
          (hneg n (by omega) (by omega)).le
    linarith
  have hzero : ∑ n ∈ Ico 1 (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) = 0 := by
    have : ∑ n ∈ Ico 1 (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) =
        x 0 * ∑ n ∈ Ico 1 (m + 1), w n * (∑ r ∈ range n, x r - x 0 / 2) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
    rw [this, habel, mul_zero]
  linarith

/-! ### Theorem 18.3 -/

/-- **Theorem 18.3 (Theorem 7.3 (⇒) with ties), polygon form.**  Forces in the normal cones of a
strictly convex counterclockwise polygon, not all zero, with zero sum, zero depth moment and zero
torque, at robustly unimodal depths, force a horizontal double normal. -/
theorem hasHorizontalDoubleNormal_of_forces_robust {k : ℕ} [NeZero k] (p : ZMod k → ℝ²)
    (z : ZMod k → ℝ) (hp : IsCcwPolygon p) (hz : IsRobustUnimodal z) (f : ZMod k → ℝ²)
    (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i)) (hne : ∃ i, f i ≠ 0)
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) (h3 : ∑ i, cross2 (p i) (f i) = 0) :
    HasHorizontalDoubleNormal p z := by
  classical
  have hk := hp.1
  set Sup := univ.filter (fun i => f i ≠ 0) with hSup
  have hSupne : Sup.Nonempty := by
    obtain ⟨i, hi⟩ := hne; exact ⟨i, by simp [hSup, hi]⟩
  obtain ⟨B, hBS, hBmin⟩ := Sup.exists_min_image z hSupne
  obtain ⟨T₀, hTS, hTmax⟩ := Sup.exists_max_image z hSupne
  have hfB : f B ≠ 0 := (mem_filter.mp hBS).2
  have hfT : f T₀ ≠ 0 := (mem_filter.mp hTS).2
  have hpar : ∀ i, cross2 (f B) (f i) = 0 := by
    rcases eq_or_lt_of_le (hBmin T₀ hTS) with heq | hlt
    · -- all forced depths are equal: at most two forced corners, opposite forces
      have hall : ∀ i, f i ≠ 0 → z i = z B := fun i hi => by
        have e1 := hBmin i (by simp [hSup, hi])
        have e2 := hTmax i (by simp [hSup, hi])
        linarith
      by_contra hcon
      push Not at hcon
      obtain ⟨i, hi⟩ := hcon
      have hfi : f i ≠ 0 := fun h => hi (by simp [h, cross2])
      have hiB : i ≠ B := fun h => hi (by rw [h]; exact cross2_self _)
      obtain ⟨l, hlB, hli, hfl⟩ : ∃ l, l ≠ B ∧ l ≠ i ∧ f l ≠ 0 := by
        by_contra hno
        push Not at hno
        have hs : ∑ l, f l = f B + f i := by
          rw [← add_sum_erase _ _ (mem_univ B),
            ← add_sum_erase _ _ (mem_erase.mpr ⟨hiB, mem_univ i⟩),
            sum_eq_zero fun l hl => hno l (mem_erase.mp (mem_erase.mp hl).2).1
              (mem_erase.mp hl).1, add_zero]
        have : f i = -f B := by rw [h1] at hs; rw [eq_neg_iff_add_eq_zero, add_comm]; exact hs.symm
        apply hi; rw [this, cross2_neg_right, cross2_self, neg_zero]
      exact hz.noTriple B i l hiB.symm (Ne.symm hli) (Ne.symm hlB) (hall i hfi).symm
        ((hall i hfi).trans (hall l hfl).symm)
    have hBT : B ≠ T₀ := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    set T := (T₀ - B).val with hTdef
    have hT0 : 0 < T := by
      rw [hTdef]; exact (ZMod.val_pos).mpr (sub_ne_zero.mpr hBT.symm)
    have hTk : T < k := ZMod.val_lt _
    have hBT' : B + (T : ZMod k) = T₀ := by rw [hTdef, ZMod.natCast_zmod_val]; ring
    set g : ℕ → ℝ² := fun n => f (B + n) with hg
    set ζ : ℕ → ℝ := fun n => z (B + n) with hζ
    have hg0 : g 0 = f B := by simp [hg]
    have hgT : g T = f T₀ := by simp only [hg, hBT']
    have hζ0 : ζ 0 = z B := by simp [hζ]
    have hζT : ζ T = z T₀ := by simp only [hζ, hBT']
    have hζmin : ∀ a, g a ≠ 0 → ζ 0 ≤ ζ a := fun a ha => by
      rw [hζ0]; exact hBmin _ (by simpa [hSup] using ha)
    have hζmax : ∀ a, g a ≠ 0 → ζ a ≤ ζ T := fun a ha => by
      rw [hζT]; exact hTmax _ (by simpa [hSup] using ha)
    have hζ0T : ζ 0 < ζ T := by rw [hζ0, hζT]; exact hlt
    have hmod : ∀ n : ℕ, ζ (n % k) = ζ n := fun n => by simp only [hζ, ZMod.natCast_mod]
    have hgmod : ∀ n : ℕ, g (n % k) = g n := fun n => by simp only [hg, ZMod.natCast_mod]
    have hcore := forces_parallel_weak g ζ k T hT0 hTk (by rw [hg0]; exact hfB)
      (by rw [hgT]; exact hfT)
      (by rw [← sum_zmod_eq_sum_range f B]; exact h1)
      (by rw [← sum_zmod_eq_sum_range (fun i => z i • f i) B]; exact h2)
      (by
        intro a b hab hbT ha hb
        by_contra hc; push Not at hc
        have ha0 : 0 < a := by
          by_contra h0; have : a = 0 := by omega
          subst this; linarith [hζmin b hb]
        have hbT' : b < T := by
          by_contra h0; have : b = T := by omega
          subst this; linarith [hζmax a ha]
        exact hz.noPeaks' B ha0 hab hbT' hTk ⟨by linarith [hζmin b hb], hc, hζ0T,
          by linarith [hζmax a ha]⟩)
      (by
        intro a b hTa hab hbk ha hb
        by_contra hc; push Not at hc
        have haT : T < a := by
          by_contra h0; have : a = T := by omega
          subst this; linarith [hζmax b hb]
        exact hz.noPeaks' B hT0 haT hab hbk ⟨hζ0T, by linarith [hζmax b hb],
          by linarith [hζmin a ha], hc⟩)
      (fun a _ _ ha => hζmin a ha) hζ0T
      (by
        intro a b c hab hbc hck _ _ _ e1 e2
        exact hz.noTriple (B + a) (B + b) (B + c) (zmod_add_ne (by omega) (by omega) hab.ne B)
          (zmod_add_ne (by omega) (by omega) hbc.ne B)
          (zmod_add_ne (by omega) (by omega) (hab.trans hbc).ne B) e1 e2)
      (by
        intro a b c d hab hbc hcd hdk _ _ _ _ e
        rw [hmod]
        rcases lt_or_eq_of_le hdk with hdk | hdk'
        · exact hz.noLevelRun B a b c d hab hbc hcd hdk e
        rcases Nat.eq_zero_or_pos a with rfl | ha0
        · have hk0 : ζ d = ζ 0 := by rw [← hmod d, hdk', Nat.mod_self]
          rw [hk0]
          exact ⟨fun h => by linarith [h.1, h.2], fun h => by linarith [h.1, h.2]⟩
        -- rotate so that the wrap-around position comes last
        have key := hz.noLevelRun (B + a) 0 (b - a) (c - a) (d - a) (by omega) (by omega)
          (by omega) (by omega)
        simp only [Nat.cast_zero, add_zero, zmod_add_natCast_sub B hab.le,
          zmod_add_natCast_sub B (hab.trans hbc).le,
          zmod_add_natCast_sub B (show a ≤ d by omega)] at key
        have key := key e
        exact ⟨fun h => key.1 ⟨h.1, h.2⟩, fun h => key.2 ⟨h.1, h.2⟩⟩)
      (fun D => hp.forces_SS hf B D)
      (by
        obtain ⟨j, hj, h1', h2'⟩ := hp.forces_oriented hf B
        exact ⟨j, hj, fun s a b => by rw [hg0]; exact h1' s a b,
          fun s a b => by rw [hg0]; exact h2' s a b⟩)
      (by
        obtain ⟨j, hj, h1', h2'⟩ := hp.forces_oriented hf T₀
        have hidx : ∀ s : ℕ, B + (((T + s) % k : ℕ) : ZMod k) = T₀ + (s : ZMod k) := fun s => by
          rw [ZMod.natCast_mod, Nat.cast_add, ← add_assoc, hBT']
        exact ⟨j, hj, fun s a b => by simp only [hg, hidx, hBT']; exact h1' s a b,
          fun s a b => by simp only [hg, hidx, hBT']; exact h2' s a b⟩)
    intro i
    have := hcore (i - B).val (ZMod.val_lt _)
    rwa [hg0, show g (i - B).val = f i by simp only [hg, ZMod.natCast_zmod_val]; ring_nf] at this
  have he2 : 0 < ‖f B‖ ^ 2 := by have := norm_pos_iff.mpr hfB; positivity
  refine hp.hdn_of_parallel z hf hfB (fun i => ⟪f B, f i⟫ / ‖f B‖ ^ 2) (fun i => ?_) (B := B)
    ?_ h1 h2 h3
  · have := norm_sq_smul_of_cross2 (v := f i) (e := f B) (by rw [cross2_comm, hpar i, neg_zero])
    apply smul_right_injective ℝ² he2.ne'
    simp only
    rw [this, smul_smul, mul_div_cancel₀ _ he2.ne']
  · simp only [real_inner_self_eq_norm_sq, div_self he2.ne']; exact one_pos

/-- **Theorem 18.3 at an explicit standard view.**  The silhouette is the cycle `x`, every
other point of `V` projects into the interior of the shadow, the corner depths are robustly
unimodal (ties allowed), and there is no horizontal double normal.  Then some first-order motion
is strictly inward. -/
theorem exists_firstOrderInward_of_robustUnimodal (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    (hz : IsRobustUnimodal (fun i => x i 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (x i)) (fun i => x i 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  classical
  by_contra hno
  push Not at hno
  set p : ZMod k → ℝ² := fun i => proj_xy (x i) with hpdef
  set Q := convexHull ℝ (Set.range p) with hQdef
  have hSQ : proj_xy '' convexHull ℝ (V : Set ℝ³) = Q := by
    rw [show (proj_xy : ℝ³ → ℝ²) = projL from rfl, LinearMap.image_convexHull]
    apply le_antisymm
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hc : ∃ i, v = x i
      · obtain ⟨i, rfl⟩ := hc; exact subset_convexHull ℝ _ ⟨i, rfl⟩
      · push Not at hc; exact interior_subset (hin v hv hc)
    · apply convexHull_mono
      rintro _ ⟨i, rfl⟩; exact ⟨x i, hxV i, rfl⟩
  obtain ⟨f, hfN, ⟨v₀, hv₀, hf₀⟩, hE1, hE2, hE3⟩ :=
    exists_forces_of_not_firstOrderInward V (by rw [hSQ]; exact hp.interior_nonempty) hno
  rw [hSQ] at hfN
  have hzero : ∀ v ∈ V, (∀ i, v ≠ x i) → f v = 0 := fun v hv hc =>
    normalConeAt_eq_zero_of_mem_interior (hin v hv hc) (hfN v hv)
  have hxinj : Function.Injective x := fun i j h => hp.injective (by rw [hpdef]; dsimp only; rw [h])
  have himg : univ.image x ⊆ V := fun v hv => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv; exact hxV i
  have hred : ∀ {M : Type} [AddCommMonoid M] (G : ℝ³ → M), (∀ v, f v = 0 → G v = 0) →
      ∑ v ∈ V, G v = ∑ i, G (x i) := by
    intro M _ G hG
    rw [← sum_subset himg (fun v hv hni => hG v (hzero v hv fun i h => hni (by
      rw [h]; exact mem_image_of_mem x (mem_univ i)))), sum_image (fun i _ j _ h => hxinj h)]
  refine hnd (hasHorizontalDoubleNormal_of_forces_robust p (fun i => x i 2) hp hz (fun i => f (x i))
    (fun i => hfN (x i) (hxV i)) ?_ ?_ ?_ ?_)
  · by_contra hall; push Not at hall
    by_cases hc : ∃ i, v₀ = x i
    · obtain ⟨i, rfl⟩ := hc; exact hf₀ (hall i)
    · push Not at hc; exact hf₀ (hzero v₀ hv₀ hc)
  · rw [← hred f (fun v h => h)]; exact hE1
  · rw [← hred (fun v => v 2 • f v) (fun v h => by simp [h])]; exact hE2
  · rw [← hred (fun v => cross2 (proj_xy v) (f v)) (fun v h => by simp [h, cross2])]; exact hE3

/-- **Theorem 18.3, Rupert form, at the view of a rotation `R`.** -/
theorem isRupert_of_robustUnimodalView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  classical
  obtain ⟨ω, τ, h⟩ := exists_firstOrderInward_of_robustUnimodal (V.image R.toEuclideanLin)
    (fun i => R.toEuclideanLin (x i)) (fun i => mem_image_of_mem _ (hxV i)) hp
    (by
      intro w hw hc
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact hin v hv fun i h => hc i (by rw [h]))
    hz hnd
  exact isRupert_of_firstOrderInward_image V R hR ω τ h

end Minimality

end
