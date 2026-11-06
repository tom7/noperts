module

public import Mathlib
public import MinimalityExtra

/-!
# Combinatorial silhouette codes of types 24 and 29

Proof of `MinimalityExtra.SilhouetteCodeCounts`, by kernel `decide`.  The sum over all `2^9`
subsets is split into 16 pieces (by membership of faces 0-3) to keep each kernel computation small;
the definitions' `Finset` operations are first replaced by explicit tables (`edgeTable`, `adjTable`).
-/

@[expose] public section

namespace MinimalityExtra

def edgeTable24 : Fin 9 → Finset (Fin 7 × Fin 7) :=
  ![{(0, 1), (0, 2), (1, 2)}, {(0, 1), (0, 6), (1, 6)}, {(0, 2), (0, 5), (2, 5)}, {(0, 4), (0, 5), (3, 4), (3, 5)}, {(0, 4), (0, 6), (4, 6)}, {(1, 2), (1, 6), (2, 6)}, {(2, 3), (2, 5), (3, 5)}, {(2, 3), (2, 6), (3, 6)}, {(3, 4), (3, 6), (4, 6)}]

def adjTable24 : Fin 9 → Fin 9 → Bool :=
  ![![true, true, true, false, false, true, false, false, false], ![true, true, false, false, true, true, false, false, false], ![true, false, true, true, false, false, true, false, false], ![false, false, true, true, true, false, true, false, true], ![false, true, false, true, true, false, false, false, true], ![true, true, false, false, false, true, false, true, false], ![false, false, true, true, false, false, true, true, false], ![false, false, false, false, false, true, true, true, true], ![false, false, false, true, true, false, false, true, true]]

def edgeTable29 : Fin 9 → Finset (Fin 7 × Fin 7) :=
  ![{(0, 1), (0, 2), (1, 2)}, {(0, 1), (0, 5), (1, 5)}, {(0, 2), (0, 3), (2, 3)}, {(0, 3), (0, 5), (3, 5)}, {(1, 2), (1, 4), (2, 4)}, {(1, 4), (1, 5), (4, 6), (5, 6)}, {(2, 3), (2, 4), (3, 4)}, {(3, 4), (3, 6), (4, 6)}, {(3, 5), (3, 6), (5, 6)}]

def adjTable29 : Fin 9 → Fin 9 → Bool :=
  ![![true, true, true, false, true, false, false, false, false], ![true, true, false, true, false, true, false, false, false], ![true, false, true, true, false, false, true, false, false], ![false, true, true, true, false, false, false, false, true], ![true, false, false, false, true, true, true, false, false], ![false, true, false, false, true, true, false, true, true], ![false, false, true, false, true, false, true, true, false], ![false, false, false, false, false, true, true, true, true], ![false, false, false, true, false, true, false, true, true]]

def FastCode (adj : Fin 9 → Fin 9 → Bool) (E : Fin 9 → Finset (Fin 7 × Fin 7))
    (S : Finset (Fin 9)) : Prop :=
  S.Nonempty ∧ Sᶜ.Nonempty ∧ IsSingleCycle ((S.biUnion E) ∩ (Sᶜ.biUnion E)) ∧
    DualConnected adj S ∧ DualConnected adj Sᶜ

instance (adj : Fin 9 → Fin 9 → Bool) (E : Fin 9 → Finset (Fin 7 × Fin 7))
    (S : Finset (Fin 9)) : Decidable (FastCode adj E S) := by
  unfold FastCode; infer_instance

theorem code_iff (F : Fin 9 → List (Fin 7)) (E : Fin 9 → Finset (Fin 7 × Fin 7))
    (adj : Fin 9 → Fin 9 → Bool)
    (hE : ∀ f, polyEdges (F f) = E f) (hA : ∀ f g, FacesAdjacent F f g = adj f g)
    (S : Finset (Fin 9)) : IsSilhouetteCode F S ↔ FastCode adj E S := by
  have h : FacesAdjacent F = adj := funext fun f => funext fun g => hA f g
  unfold IsSilhouetteCode silhouetteEdges FastCode
  simp only [hE, h]


set_option maxRecDepth 100000

theorem e24 : ∀ f, polyEdges (type24Faces f) = edgeTable24 f := by
  unfold type24Faces edgeTable24; decide +kernel
theorem a24 : ∀ f g, FacesAdjacent type24Faces f g = adjTable24 f g := by
  unfold type24Faces adjTable24 FacesAdjacent; decide +kernel
theorem e29 : ∀ f, polyEdges (type29Faces f) = edgeTable29 f := by
  unfold type29Faces edgeTable29; decide +kernel
theorem a29 : ∀ f g, FacesAdjacent type29Faces f g = adjTable29 f g := by
  unfold type29Faces adjTable29 FacesAdjacent; decide +kernel

/-- The index of the piece of `S`: membership of faces 0-3 as binary digits. -/
def pieceKey (S : Finset (Fin 9)) : ℕ := (S.filter (fun i => i.val < 4)).sum (fun i => 2 ^ i.val)

theorem pieceKey_lt : ∀ S : Finset (Fin 9), pieceKey S < 16 := by
  unfold pieceKey; decide +kernel

theorem pieceKey_odd : ∀ S : Finset (Fin 9), ((0 : Fin 9) ∈ S ↔ pieceKey S % 2 = 1) := by
  unfold pieceKey; decide +kernel

theorem split16 (P : Finset (Fin 9) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ k ∈ Finset.range 16, (Finset.univ.filter (fun S => pieceKey S = k ∧ P S)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := pieceKey) (t := Finset.range 16)
    (fun S _ => Finset.mem_range.2 (pieceKey_lt S))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.filter_filter]
  congr 1
  exact Finset.filter_congr fun S _ => and_comm

theorem leaf24_0 : (Finset.univ.filter (fun S => pieceKey S = 0 ∧
    FastCode adjTable24 edgeTable24 S)).card = 17 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_1 : (Finset.univ.filter (fun S => pieceKey S = 1 ∧
    FastCode adjTable24 edgeTable24 S)).card = 6 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_2 : (Finset.univ.filter (fun S => pieceKey S = 2 ∧
    FastCode adjTable24 edgeTable24 S)).card = 16 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_3 : (Finset.univ.filter (fun S => pieceKey S = 3 ∧
    FastCode adjTable24 edgeTable24 S)).card = 14 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_4 : (Finset.univ.filter (fun S => pieceKey S = 4 ∧
    FastCode adjTable24 edgeTable24 S)).card = 6 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_5 : (Finset.univ.filter (fun S => pieceKey S = 5 ∧
    FastCode adjTable24 edgeTable24 S)).card = 10 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_6 : (Finset.univ.filter (fun S => pieceKey S = 6 ∧
    FastCode adjTable24 edgeTable24 S)).card = 0 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_7 : (Finset.univ.filter (fun S => pieceKey S = 7 ∧
    FastCode adjTable24 edgeTable24 S)).card = 18 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_8 : (Finset.univ.filter (fun S => pieceKey S = 8 ∧
    FastCode adjTable24 edgeTable24 S)).card = 18 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_9 : (Finset.univ.filter (fun S => pieceKey S = 9 ∧
    FastCode adjTable24 edgeTable24 S)).card = 0 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_10 : (Finset.univ.filter (fun S => pieceKey S = 10 ∧
    FastCode adjTable24 edgeTable24 S)).card = 10 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_11 : (Finset.univ.filter (fun S => pieceKey S = 11 ∧
    FastCode adjTable24 edgeTable24 S)).card = 6 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_12 : (Finset.univ.filter (fun S => pieceKey S = 12 ∧
    FastCode adjTable24 edgeTable24 S)).card = 14 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_13 : (Finset.univ.filter (fun S => pieceKey S = 13 ∧
    FastCode adjTable24 edgeTable24 S)).card = 16 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_14 : (Finset.univ.filter (fun S => pieceKey S = 14 ∧
    FastCode adjTable24 edgeTable24 S)).card = 6 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem leaf24_15 : (Finset.univ.filter (fun S => pieceKey S = 15 ∧
    FastCode adjTable24 edgeTable24 S)).card = 17 := by
  unfold adjTable24 edgeTable24 pieceKey; decide +kernel
theorem half24_1 : (Finset.univ.filter (fun S => pieceKey S = 1 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 6 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 1 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 1 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_1
theorem half24_3 : (Finset.univ.filter (fun S => pieceKey S = 3 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 14 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 3 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 3 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_3
theorem half24_5 : (Finset.univ.filter (fun S => pieceKey S = 5 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 10 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 5 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 5 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_5
theorem half24_7 : (Finset.univ.filter (fun S => pieceKey S = 7 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 18 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 7 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 7 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_7
theorem half24_9 : (Finset.univ.filter (fun S => pieceKey S = 9 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 0 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 9 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 9 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_9
theorem half24_11 : (Finset.univ.filter (fun S => pieceKey S = 11 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 6 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 11 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 11 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_11
theorem half24_13 : (Finset.univ.filter (fun S => pieceKey S = 13 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 16 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 13 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 13 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_13
theorem half24_15 : (Finset.univ.filter (fun S => pieceKey S = 15 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 17 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 15 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable24 edgeTable24 S)) ↔
      (pieceKey S = 15 ∧ FastCode adjTable24 edgeTable24 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf24_15

theorem total24 : (Finset.univ.filter (IsSilhouetteCode type24Faces)).card = 174 := by
  simp only [code_iff _ _ _ e24 a24]
  rw [split16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [leaf24_0, leaf24_1, leaf24_2, leaf24_3, leaf24_4, leaf24_5, leaf24_6, leaf24_7, leaf24_8, leaf24_9, leaf24_10, leaf24_11, leaf24_12, leaf24_13, leaf24_14, leaf24_15]

theorem half24 : (Finset.univ.filter (fun S => (0 : Fin 9) ∈ S ∧ IsSilhouetteCode type24Faces S)).card
    = 87 := by
  simp only [code_iff _ _ _ e24 a24, pieceKey_odd]
  rw [split16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 : ∀ k : ℕ, k % 2 = 0 → (Finset.univ.filter (fun S => pieceKey S = k ∧
      (pieceKey S % 2 = 1 ∧ FastCode adjTable24 edgeTable24 S))).card = 0 := by
    intro k hk
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S _ h; omega
  rw [h0 0 rfl, h0 2 rfl, h0 4 rfl, h0 6 rfl, h0 8 rfl, h0 10 rfl, h0 12 rfl, h0 14 rfl,
    half24_1, half24_3, half24_5, half24_7, half24_9, half24_11, half24_13, half24_15]

theorem leaf29_0 : (Finset.univ.filter (fun S => pieceKey S = 0 ∧
    FastCode adjTable29 edgeTable29 S)).card = 23 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_1 : (Finset.univ.filter (fun S => pieceKey S = 1 ∧
    FastCode adjTable29 edgeTable29 S)).card = 12 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_2 : (Finset.univ.filter (fun S => pieceKey S = 2 ∧
    FastCode adjTable29 edgeTable29 S)).card = 14 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_3 : (Finset.univ.filter (fun S => pieceKey S = 3 ∧
    FastCode adjTable29 edgeTable29 S)).card = 15 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_4 : (Finset.univ.filter (fun S => pieceKey S = 4 ∧
    FastCode adjTable29 edgeTable29 S)).card = 12 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_5 : (Finset.univ.filter (fun S => pieceKey S = 5 ∧
    FastCode adjTable29 edgeTable29 S)).card = 12 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_6 : (Finset.univ.filter (fun S => pieceKey S = 6 ∧
    FastCode adjTable29 edgeTable29 S)).card = 0 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_7 : (Finset.univ.filter (fun S => pieceKey S = 7 ∧
    FastCode adjTable29 edgeTable29 S)).card = 11 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_8 : (Finset.univ.filter (fun S => pieceKey S = 8 ∧
    FastCode adjTable29 edgeTable29 S)).card = 11 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_9 : (Finset.univ.filter (fun S => pieceKey S = 9 ∧
    FastCode adjTable29 edgeTable29 S)).card = 0 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_10 : (Finset.univ.filter (fun S => pieceKey S = 10 ∧
    FastCode adjTable29 edgeTable29 S)).card = 12 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_11 : (Finset.univ.filter (fun S => pieceKey S = 11 ∧
    FastCode adjTable29 edgeTable29 S)).card = 12 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_12 : (Finset.univ.filter (fun S => pieceKey S = 12 ∧
    FastCode adjTable29 edgeTable29 S)).card = 15 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_13 : (Finset.univ.filter (fun S => pieceKey S = 13 ∧
    FastCode adjTable29 edgeTable29 S)).card = 14 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_14 : (Finset.univ.filter (fun S => pieceKey S = 14 ∧
    FastCode adjTable29 edgeTable29 S)).card = 12 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem leaf29_15 : (Finset.univ.filter (fun S => pieceKey S = 15 ∧
    FastCode adjTable29 edgeTable29 S)).card = 23 := by
  unfold adjTable29 edgeTable29 pieceKey; decide +kernel
theorem half29_1 : (Finset.univ.filter (fun S => pieceKey S = 1 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 12 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 1 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 1 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_1
theorem half29_3 : (Finset.univ.filter (fun S => pieceKey S = 3 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 15 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 3 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 3 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_3
theorem half29_5 : (Finset.univ.filter (fun S => pieceKey S = 5 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 12 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 5 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 5 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_5
theorem half29_7 : (Finset.univ.filter (fun S => pieceKey S = 7 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 11 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 7 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 7 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_7
theorem half29_9 : (Finset.univ.filter (fun S => pieceKey S = 9 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 0 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 9 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 9 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_9
theorem half29_11 : (Finset.univ.filter (fun S => pieceKey S = 11 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 12 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 11 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 11 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_11
theorem half29_13 : (Finset.univ.filter (fun S => pieceKey S = 13 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 14 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 13 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 13 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_13
theorem half29_15 : (Finset.univ.filter (fun S => pieceKey S = 15 ∧
    (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 23 := by
  have h : ∀ S : Finset (Fin 9), (pieceKey S = 15 ∧ (pieceKey S % 2 = 1 ∧
      FastCode adjTable29 edgeTable29 S)) ↔
      (pieceKey S = 15 ∧ FastCode adjTable29 edgeTable29 S) :=
    fun S => ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, by omega, h3⟩⟩
  exact (congrArg Finset.card (Finset.filter_congr fun S _ => h S)).trans leaf29_15

theorem total29 : (Finset.univ.filter (IsSilhouetteCode type29Faces)).card = 198 := by
  simp only [code_iff _ _ _ e29 a29]
  rw [split16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [leaf29_0, leaf29_1, leaf29_2, leaf29_3, leaf29_4, leaf29_5, leaf29_6, leaf29_7, leaf29_8, leaf29_9, leaf29_10, leaf29_11, leaf29_12, leaf29_13, leaf29_14, leaf29_15]

theorem half29 : (Finset.univ.filter (fun S => (0 : Fin 9) ∈ S ∧ IsSilhouetteCode type29Faces S)).card
    = 99 := by
  simp only [code_iff _ _ _ e29 a29, pieceKey_odd]
  rw [split16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 : ∀ k : ℕ, k % 2 = 0 → (Finset.univ.filter (fun S => pieceKey S = k ∧
      (pieceKey S % 2 = 1 ∧ FastCode adjTable29 edgeTable29 S))).card = 0 := by
    intro k hk
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S _ h; omega
  rw [h0 0 rfl, h0 2 rfl, h0 4 rfl, h0 6 rfl, h0 8 rfl, h0 10 rfl, h0 12 rfl, h0 14 rfl,
    half29_1, half29_3, half29_5, half29_7, half29_9, half29_11, half29_13, half29_15]

/-- Sanity: the cyclic vertex lists are genuine face boundaries: each of the 14 edges lies on
exactly two faces (so the face lists form a closed surface with `7 - 14 + 9 = 2`). -/
theorem edges_two_faces24 :
    (Finset.univ.biUnion fun f => polyEdges (type24Faces f)).card = 14 ∧
    ∀ e ∈ (Finset.univ.biUnion fun f => polyEdges (type24Faces f)),
      (Finset.univ.filter fun f => e ∈ polyEdges (type24Faces f)).card = 2 := by
  unfold type24Faces polyEdges; decide +kernel

theorem edges_two_faces29 :
    (Finset.univ.biUnion fun f => polyEdges (type29Faces f)).card = 14 ∧
    ∀ e ∈ (Finset.univ.biUnion fun f => polyEdges (type29Faces f)),
      (Finset.univ.filter fun f => e ∈ polyEdges (type29Faces f)).card = 2 := by
  unfold type29Faces polyEdges; decide +kernel

theorem silhouetteCodeCounts : SilhouetteCodeCounts :=
  ⟨total24, total29, half24, half29⟩

end MinimalityExtra
