module

public import MinimalityExtra
public import Minimality.SilS0XA

/-!
# Lemma AQ: robust unimodality is the absence of weak alternation
-/

@[expose] public section

namespace MinimalityExtra

/-- Four sorted positions give both alternating colourings (Lemma AQ at two bases). -/
theorem four {k : ℕ} {z : ZMod k → ℝ} (hU : WeakAlternationFree z) (n0 n1 n2 n3 : ℕ)
    (h01 : n0 < n1) (h12 : n1 < n2) (h23 : n2 < n3) (h3 : n3 < k) :
    ¬ (z (n1 : ZMod k) ≤ z (n0 : ZMod k) ∧ z (n1 : ZMod k) ≤ z (n2 : ZMod k) ∧
        z (n3 : ZMod k) ≤ z (n0 : ZMod k) ∧ z (n3 : ZMod k) ≤ z (n2 : ZMod k)) ∧
    ¬ (z (n2 : ZMod k) ≤ z (n1 : ZMod k) ∧ z (n2 : ZMod k) ≤ z (n3 : ZMod k) ∧
        z (n0 : ZMod k) ≤ z (n1 : ZMod k) ∧ z (n0 : ZMod k) ≤ z (n3 : ZMod k)) := by
  constructor
  · have r1 : (n0 : ZMod k) + ((n1 - n0 : ℕ) : ZMod k) = (n1 : ZMod k) := by
      rw [Nat.cast_sub h01.le]; ring
    have r2 : (n0 : ZMod k) + ((n2 - n0 : ℕ) : ZMod k) = (n2 : ZMod k) := by
      rw [Nat.cast_sub (by omega : n0 ≤ n2)]; ring
    have r3 : (n0 : ZMod k) + ((n3 - n0 : ℕ) : ZMod k) = (n3 : ZMod k) := by
      rw [Nat.cast_sub (by omega : n0 ≤ n3)]; ring
    have := hU (n0 : ZMod k) (n1 - n0) (n2 - n0) (n3 - n0) (by omega) (by omega) (by omega)
      (by omega)
    rw [r1, r2, r3] at this
    exact this
  · have r1 : (n1 : ZMod k) + ((n2 - n1 : ℕ) : ZMod k) = (n2 : ZMod k) := by
      rw [Nat.cast_sub (by omega : n1 ≤ n2)]; ring
    have r2 : (n1 : ZMod k) + ((n3 - n1 : ℕ) : ZMod k) = (n3 : ZMod k) := by
      rw [Nat.cast_sub (by omega : n1 ≤ n3)]; ring
    have w : (n1 : ZMod k) + ((k - n1 + n0 : ℕ) : ZMod k) = (n0 : ZMod k) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega : n1 ≤ k), ZMod.natCast_self]; ring
    have := hU (n1 : ZMod k) (n2 - n1) (n3 - n1) (k - n1 + n0) (by omega) (by omega)
      (by omega) (by omega)
    rw [r1, r2, w] at this
    exact this

/-- Three equal entries at sorted positions `I < J < L` plus a fourth position `S`. -/
theorem arcs {k : ℕ} {z : ZMod k → ℝ} (hU : WeakAlternationFree z) (I J L S : ℕ)
    (h1 : I < J) (h2 : J < L) (h3 : L < k) (hS : S < k) (hSI : S ≠ I) (hSJ : S ≠ J)
    (hSL : S ≠ L) (e1 : z (I : ZMod k) = z (J : ZMod k))
    (e2 : z (J : ZMod k) = z (L : ZMod k)) : False := by
  rcases lt_or_gt_of_ne hSI with a | a
  · obtain ⟨P1, P2⟩ := four hU S I J L (by omega) (by omega) (by omega) (by omega)
    rcases le_total (z (S : ZMod k)) (z (I : ZMod k)) with h | h <;>
      first
      | exact P1 ⟨by linarith, by linarith, by linarith, by linarith⟩
      | exact P2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  rcases lt_or_gt_of_ne hSJ with b | b
  · obtain ⟨P1, P2⟩ := four hU I S J L (by omega) (by omega) (by omega) (by omega)
    rcases le_total (z (S : ZMod k)) (z (I : ZMod k)) with h | h <;>
      first
      | exact P1 ⟨by linarith, by linarith, by linarith, by linarith⟩
      | exact P2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  rcases lt_or_gt_of_ne hSL with c | c
  · obtain ⟨P1, P2⟩ := four hU I J S L (by omega) (by omega) (by omega) (by omega)
    rcases le_total (z (S : ZMod k)) (z (I : ZMod k)) with h | h <;>
      first
      | exact P1 ⟨by linarith, by linarith, by linarith, by linarith⟩
      | exact P2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  · obtain ⟨P1, P2⟩ := four hU I J L S (by omega) (by omega) (by omega) (by omega)
    rcases le_total (z (S : ZMod k)) (z (I : ZMod k)) with h | h <;>
      first
      | exact P1 ⟨by linarith, by linarith, by linarith, by linarith⟩
      | exact P2 ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Three equal entries at sorted positions give a contradiction (k ≥ 4). -/
theorem sorted3 {k : ℕ} {z : ZMod k → ℝ} (hU : WeakAlternationFree z) (hk : 4 ≤ k)
    (I J L : ℕ) (h1 : I < J) (h2 : J < L) (h3 : L < k)
    (e1 : z (I : ZMod k) = z (J : ZMod k)) (e2 : z (J : ZMod k) = z (L : ZMod k)) : False := by
  obtain ⟨S, hS, hSI, hSJ, hSL⟩ : ∃ S, S < k ∧ S ≠ I ∧ S ≠ J ∧ S ≠ L := by
    rcases (by omega : (0 ≠ I ∧ 0 ≠ J ∧ 0 ≠ L) ∨ (1 ≠ I ∧ 1 ≠ J ∧ 1 ≠ L) ∨
        (2 ≠ I ∧ 2 ≠ J ∧ 2 ≠ L) ∨ (3 ≠ I ∧ 3 ≠ J ∧ 3 ≠ L)) with h | h | h | h
    · exact ⟨0, by omega, h.1, h.2.1, h.2.2⟩
    · exact ⟨1, by omega, h.1, h.2.1, h.2.2⟩
    · exact ⟨2, by omega, h.1, h.2.1, h.2.2⟩
    · exact ⟨3, by omega, h.1, h.2.1, h.2.2⟩
  exact arcs hU I J L S h1 h2 h3 hS hSI hSJ hSL e1 e2

theorem isRobustUnimodal_iff {k : ℕ} (hk : 4 ≤ k) (z : ZMod k → ℝ) :
    IsRobustUnimodal z ↔ WeakAlternationFree z := by
  constructor
  · intro h
    exact Minimality.H21.s0x_robUni_of_isRobustUnimodal ⟨h.1, h.2.1, h.2.2⟩
  · intro hU
    refine ⟨?_, ?_, ?_⟩
    · -- (R1) strict two-peak pattern implies the weak one
      intro B a b c d hab hbc hcd hdk ⟨e1, e2, e3, e4⟩
      have r1 : B + a + ((b - a : ℕ) : ZMod k) = B + b := by
        rw [Nat.cast_sub hab.le]; ring
      have r2 : B + a + ((c - a : ℕ) : ZMod k) = B + c := by
        rw [Nat.cast_sub (by omega : a ≤ c)]; ring
      have r3 : B + a + ((d - a : ℕ) : ZMod k) = B + d := by
        rw [Nat.cast_sub (by omega : a ≤ d)]; ring
      have := hU (B + a) (b - a) (c - a) (d - a) (by omega) (by omega) (by omega) (by omega)
      rw [r1, r2, r3] at this
      exact this ⟨e1.le, e2.le, e3.le, e4.le⟩
    · -- (R2) three equal entries: sort the three positions by their values in ℕ
      intro i j l hij hjl hil hi hj
      haveI : NeZero k := ⟨by omega⟩
      have E : ∀ x y : ZMod k, z x = z y → z ((x.val : ℕ) : ZMod k) = z ((y.val : ℕ) : ZMod k) :=
        fun x y h => by rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; exact h
      have dij : i.val ≠ j.val := fun h => hij (ZMod.val_injective k h)
      have djl : j.val ≠ l.val := fun h => hjl (ZMod.val_injective k h)
      have dil : i.val ≠ l.val := fun h => hil (ZMod.val_injective k h)
      have ki : i.val < k := ZMod.val_lt i
      have kj : j.val < k := ZMod.val_lt j
      have kl : l.val < k := ZMod.val_lt l
      have eij := E i j hi
      have ejl := E j l hj
      have eil := E i l (hi.trans hj)
      rcases lt_or_gt_of_ne dij with a | a <;> rcases lt_or_gt_of_ne djl with b | b <;>
        rcases lt_or_gt_of_ne dil with c | c <;>
        first
        | exact sorted3 hU hk i.val j.val l.val (by omega) (by omega) (by omega) (by linarith) (by linarith)
        | exact sorted3 hU hk i.val l.val j.val (by omega) (by omega) (by omega) (by linarith) (by linarith)
        | exact sorted3 hU hk j.val i.val l.val (by omega) (by omega) (by omega) (by linarith) (by linarith)
        | exact sorted3 hU hk j.val l.val i.val (by omega) (by omega) (by omega) (by linarith) (by linarith)
        | exact sorted3 hU hk l.val i.val j.val (by omega) (by omega) (by omega) (by linarith) (by linarith)
        | exact sorted3 hU hk l.val j.val i.val (by omega) (by omega) (by omega) (by linarith) (by linarith)
    · -- (R3) level pair inside a monotone run
      intro B a b c d hab hbc hcd hdk heq
      have rcb : B + b + ((c - b : ℕ) : ZMod k) = B + c := by
        rw [Nat.cast_sub (by omega : b ≤ c)]; ring
      have rdb : B + b + ((d - b : ℕ) : ZMod k) = B + d := by
        rw [Nat.cast_sub (by omega : b ≤ d)]; ring
      have wa : B + b + ((k - b + a : ℕ) : ZMod k) = B + a := by
        rw [Nat.cast_add, Nat.cast_sub (by omega : b ≤ k), ZMod.natCast_self]; ring
      have rcc : B + c + ((d - c : ℕ) : ZMod k) = B + d := by
        rw [Nat.cast_sub (by omega : c ≤ d)]; ring
      have wc : B + c + ((k - c + a : ℕ) : ZMod k) = B + a := by
        rw [Nat.cast_add, Nat.cast_sub (by omega : c ≤ k), ZMod.natCast_self]; ring
      have wb : B + c + ((k - c + b : ℕ) : ZMod k) = B + b := by
        rw [Nat.cast_add, Nat.cast_sub (by omega : c ≤ k), ZMod.natCast_self]; ring
      constructor
      · rintro ⟨h1, h2⟩
        have := hU (B + b) (c - b) (d - b) (k - b + a) (by omega) (by omega) (by omega)
          (by omega)
        rw [rcb, rdb, wa] at this
        exact this ⟨by linarith, by linarith, by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        have := hU (B + c) (d - c) (k - c + a) (k - c + b) (by omega) (by omega) (by omega)
          (by omega)
        rw [rcc, wc, wb] at this
        exact this ⟨by linarith, by linarith, by linarith, by linarith⟩


theorem robustUnimodalIffNoAlternation : RobustUnimodalIffNoAlternation :=
  fun _ _ hk z => isRobustUnimodal_iff hk z

#print axioms robustUnimodalIffNoAlternation

end MinimalityExtra
