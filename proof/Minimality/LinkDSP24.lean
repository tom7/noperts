module

public import Minimality.Type24Circle
public import Minimality.HDNRim24
public import Minimality.LinkRim24
public import Minimality.LaplacianNH

@[expose] public section

/-!
# Type 24 depth-separated pairs as one-level-crossing conditions (nopert229 report LINKDSP24).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Link24D

/-! ### Lemma LX: a depth-separated pair is a one-level-crossing condition -/

/-- The edge `(i, i+1)` crosses the level `t` strictly. -/
def Crosses {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (t : ℝ) (i : ZMod k) : Prop :=
  (z i - t) * (z (i + 1) - t) < 0

/-- Closed form of the depth half of a depth-separated pair `(a, c)`: `c` is not a local extremum,
the level `z c` is crossed by the edge `a` and by no other edge except the two at `c`. -/
def DSPdepth {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (a c : ZMod k) : Prop :=
  (z (c - 1) - z c) * (z (c + 1) - z c) < 0 ∧ Crosses z (z c) a ∧
    ∀ i, i ≠ c - 1 → i ≠ c → i ≠ a → ¬ Crosses z (z c) i

/-- Farthest from the line of edge `a` (closed normal cone). -/
def Antip {k : ℕ} (p : ZMod k → ℝ²) (a c : ZMod k) : Prop :=
  ∀ v, cross2 (p (a + 1) - p a) (p v - p a) ≤ cross2 (p (a + 1) - p a) (p c - p a)

/-- Core on a path `p s = z (c + s) - z c`, one side. -/
theorem lx_fwd {k n : ℕ} (p : ℕ → ℝ) (hn1 : 1 ≤ n) (hn2 : n + 2 ≤ k)
    (h1 : ∀ s, 0 < s → s ≤ n → 0 < p s) (h2 : ∀ s, n < s → s < k → p s < 0) :
    p (k - 1) * p 1 < 0 ∧ p n * p (n + 1) < 0 ∧
      ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → s ≠ n → 0 ≤ p s * p (s + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have := h2 (k - 1) (by omega) (by omega); have := h1 1 (by omega) hn1
    nlinarith
  · have := h1 n (by omega) le_rfl; have := h2 (n + 1) (by omega) (by omega); nlinarith
  · intro s hs hs2 hsn
    rcases lt_or_gt_of_ne hsn with h | h
    · have := h1 s (by omega) h.le; have := h1 (s + 1) (by omega) (by omega); nlinarith
    · have := h2 s (by omega) (by omega); have := h2 (s + 1) (by omega) (by omega); nlinarith

theorem lx_bwd {k n : ℕ} (p : ℕ → ℝ) (hn1 : 1 ≤ n) (hn2 : n + 2 ≤ k)
    (hne : ∀ s, 1 ≤ s → s < k → p s ≠ 0)
    (hx : p n * p (n + 1) < 0) (hr : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → s ≠ n → 0 ≤ p s * p (s + 1)) :
    (∀ s, 0 < s → s ≤ n → 0 < p s) ∧ (∀ s, n < s → s < k → p s < 0) ∨
      (∀ s, 0 < s → s ≤ n → p s < 0) ∧ (∀ s, n < s → s < k → 0 < p s) := by
  -- same-side propagation
  have fw : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → s ≠ n → (0 < p s → 0 < p (s + 1)) := by
    intro s hs hs2 hsn hp
    have h := hr s hs hs2 hsn
    have hne' := hne (s + 1) (by omega) (by omega)
    rcases lt_or_gt_of_ne hne' with h' | h'
    · nlinarith
    · exact h'
  have fn : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → s ≠ n → (p s < 0 → p (s + 1) < 0) := by
    intro s hs hs2 hsn hp
    have h := hr s hs hs2 hsn
    have hne' := hne (s + 1) (by omega) (by omega)
    rcases lt_or_gt_of_ne hne' with h' | h'
    · exact h'
    · nlinarith
  rcases lt_or_gt_of_ne (hne 1 le_rfl (by omega)) with h1 | h1
  · right
    have A : ∀ m, 1 ≤ m → m ≤ n → p m < 0 := by
      intro m hm hmn
      induction m, hm using Nat.le_induction with
      | base => exact h1
      | succ m hm ih => exact fn m hm (by omega) (by omega) (ih (by omega))
    have B : 0 < p (n + 1) := by have := A n hn1 le_rfl; nlinarith
    refine ⟨fun s hs hsn => A s hs hsn, fun s hs hsk => ?_⟩
    induction s, hs using Nat.le_induction with
    | base => exact B
    | succ m hm ih => exact fw m (by omega) (by omega) (by omega) (ih (by omega))
  · left
    have A : ∀ m, 1 ≤ m → m ≤ n → 0 < p m := by
      intro m hm hmn
      induction m, hm using Nat.le_induction with
      | base => exact h1
      | succ m hm ih => exact fw m hm (by omega) (by omega) (ih (by omega))
    have B : p (n + 1) < 0 := by have := A n hn1 le_rfl; nlinarith
    refine ⟨fun s hs hsn => A s hs hsn, fun s hs hsk => ?_⟩
    induction s, hs using Nat.le_induction with
    | base => exact B
    | succ m hm ih => exact fn m (by omega) (by omega) (by omega) (ih (by omega))

theorem natCast_pred {k : ℕ} [NeZero k] : ((k - 1 : ℕ) : ZMod k) = -1 := by
  have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  rw [Nat.cast_sub this]; simp

/-- **Lemma LX.**  For an injective cycle `z` and an edge `a` with `c ≠ a, a + 1`, `(a, c)` is
depth-separated (chain `c..a` strictly on one side of `z c`, chain `a+1..c` strictly on the other)
iff `c` is not a local extremum and the level `z c` is crossed by the edge `a` and by no other
edge except the two at `c`. -/
theorem dsp_iff_level {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : Function.Injective z)
    {a c : ZMod k} (ha : c ≠ a) (hb : c ≠ a + 1) : DepthSepZ z a c ↔ DSPdepth z a c := by
  set n := (a - c).val with hn
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hnk : n < k := ZMod.val_lt _
  have hac : c + (n : ZMod k) = a := zmod_add_val_sub c a
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    apply ha; rw [← hac, this]; simp
  have hn2 : n + 2 ≤ k := by
    by_contra h
    have h' : n + 1 = k := by omega
    apply hb
    have : ((n + 1 : ℕ) : ZMod k) = 0 := by rw [h']; exact ZMod.natCast_self k
    rw [← hac]; push_cast at this; linear_combination -this
  set p : ℕ → ℝ := fun s => z (c + (s : ZMod k)) - z c with hp
  have hp0 : ∀ s, 1 ≤ s → s < k → p s ≠ 0 := by
    intro s hs hsk h
    have := hz (sub_eq_zero.mp h)
    have h2 : ((s : ℕ) : ZMod k) = 0 := by simpa using this
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  have hidx : ∀ i : ZMod k, i = c + (((i - c).val : ℕ) : ZMod k) := fun i => (zmod_add_val_sub c i).symm
  have hsucc : ∀ s : ℕ, c + ((s + 1 : ℕ) : ZMod k) = (c + (s : ZMod k)) + 1 := by
    intro s; push_cast; ring
  have hCr : ∀ s : ℕ, Crosses z (z c) (c + (s : ZMod k)) ↔ p s * p (s + 1) < 0 := by
    intro s; simp only [Crosses, hp, hsucc]
  have e1 : (z (c - 1) - z c) * (z (c + 1) - z c) = p (k - 1) * p 1 := by
    simp only [hp, natCast_pred]; push_cast; ring_nf
  constructor
  · intro h
    have h' : (∀ s, 0 < s → s ≤ n → 0 < p s) ∧ (∀ s, n < s → s < k → p s < 0) ∨
        (∀ s, 0 < s → s ≤ n → p s < 0) ∧ (∀ s, n < s → s < k → 0 < p s) := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨fun s a b => by simpa [hp] using sub_pos.mpr (h1 s a b),
          fun s a b => by simpa [hp] using sub_neg.mpr (h2 s a b)⟩
      · right; exact ⟨fun s a b => by simpa [hp] using sub_neg.mpr (h1 s a b),
          fun s a b => by simpa [hp] using sub_pos.mpr (h2 s a b)⟩
    have key : p (k - 1) * p 1 < 0 ∧ p n * p (n + 1) < 0 ∧
        ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → s ≠ n → 0 ≤ p s * p (s + 1) := by
      rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact lx_fwd p hn1 hn2 h1 h2
      · have := lx_fwd (fun s => - p s) hn1 hn2 (fun s a b => by simpa using h1 s a b)
          (fun s a b => by simpa using h2 s a b)
        simpa using this
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨by rw [e1]; exact k1, ?_, ?_⟩
    · rw [← hac]; exact (hCr n).mpr k2
    · intro i hi1 hi2 hi3
      have hi : i = c + (((i - c).val : ℕ) : ZMod k) := hidx i
      have hsk' : (i - c).val < k := ZMod.val_lt _
      generalize (i - c).val = s at hi hsk'
      rw [hi, hCr]
      have hs0 : s ≠ 0 := by
        intro h0; apply hi2; rw [hi, h0]; simp
      have hsn : s ≠ n := by
        intro h0; apply hi3; rw [hi, h0, hac]
      have hsk : s ≠ k - 1 := by
        intro h0; apply hi1; rw [hi, h0, natCast_pred]; ring
      have : s < k := hsk'
      exact not_lt.mpr (k3 s (by omega) (by omega) hsn)
  · rintro ⟨d1, d2, d3⟩
    rw [e1] at d1
    rw [← hac, hCr] at d2
    have d3' : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → s ≠ n → 0 ≤ p s * p (s + 1) := by
      intro s hs hs2 hsn
      have := d3 (c + (s : ZMod k)) ?_ ?_ ?_
      · rw [hCr] at this; exact not_lt.mp this
      · intro h; have := congrArg (fun t => t - c) h
        simp only [add_sub_cancel_left] at this
        rw [show c - 1 - c = -1 by ring, ← natCast_pred] at this
        have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
      · intro h
        have : ((s : ℕ) : ZMod k) = 0 := by simpa using h
        rw [ZMod.natCast_eq_zero_iff] at this
        exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
      · intro h
        have := congrArg (fun t => t - c) h
        simp only [add_sub_cancel_left] at this
        rw [← hac] at this; simp only [add_sub_cancel_left] at this
        have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact hsn this
    have R := lx_bwd p hn1 hn2 hp0 d2 d3'
    rcases R with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨fun s a b => by have := h1 s a b; simpa [hp] using this,
        fun s a b => by have := h2 s a b; simpa [hp] using this⟩
    · right; exact ⟨fun s a b => by have := h1 s a b; simpa [hp] using this,
        fun s a b => by have := h2 s a b; simpa [hp] using this⟩


/-! ### Closing lemmas at the exact edge view -/

/-- Theorem 8.10 with 8.9 at an `EdgeRim` view: a parallel pair `(a, c)` whose depths are
separated (`DepthSepZ`) certifies `K`. -/
theorem dsp_glue {x : Fin 7 → ℝ³} {u : ℝ³} {d : Fin 7} {h : ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} {a c : ZMod k} (hR : EdgeRim x u d h k r)
    (hpp : ParPairAt (fun i => x (r i)) u a c) (hds : DepthSepZ (fun i => ⟪x (r i), u⟫) a c) :
    IsRupert (Finset.univ.image x) := by
  have hu : u ≠ 0 := by
    rintro rfl
    obtain ⟨hk, -, -, -, -, hinj, -⟩ := hR
    have : Fact (1 < k) := ⟨by omega⟩
    exact zero_ne_one (hinj (by simp))
  exact isRupert_edgeRim hu hR (Or.inr ⟨a, c, hpp, hds⟩)

/-- **`dsp_glue` with the rim-only no-HDN hypothesis** (`EdgeRim'`: `NoHDNRim` of the rim cycle,
not of its whole point set). -/
theorem dsp_glue_rim {x : Fin 7 → ℝ³} {u : ℝ³} {d : Fin 7} {h : ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} {a c : ZMod k} (hR : HDNRim.EdgeRim' x u d h k r)
    (hpp : ParPairAt (fun i => x (r i)) u a c) (hds : DepthSepZ (fun i => ⟪x (r i), u⟫) a c) :
    IsRupert (Finset.univ.image x) := by
  have hu : u ≠ 0 := by
    rintro rfl
    obtain ⟨hk, -, -, -, -, hinj, -⟩ := hR
    have : Fact (1 < k) := ⟨by omega⟩
    exact zero_ne_one (hinj (by simp))
  exact HDNRim.isRupert_edgeRim_dsp_rim hu hR hpp hds

set_option hygiene false in
macro "dsfin" : tactic => `(tactic| first | exact r1 | exact r2 | exact r3 | exact r4 | exact r5 | exact r6 | exact r7)


end Link24D
end Minimality
