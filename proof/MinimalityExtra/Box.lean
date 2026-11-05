module

public import Mathlib
public import MinimalityExtra

@[expose] public section

namespace MinimalityExtra

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


def sgZ (j : ℕ) (X : Fin 8) : ℤ := if X.val / 2 ^ j % 2 = 1 then 1 else -1

def cc0 (X Y M : Fin 8) : ℤ :=
  (sgZ 1 Y - sgZ 1 X) * (sgZ 2 M - sgZ 2 X) - (sgZ 2 Y - sgZ 2 X) * (sgZ 1 M - sgZ 1 X)
def cc1 (X Y M : Fin 8) : ℤ :=
  (sgZ 2 Y - sgZ 2 X) * (sgZ 0 M - sgZ 0 X) - (sgZ 0 Y - sgZ 0 X) * (sgZ 2 M - sgZ 2 X)
def cc2 (X Y M : Fin 8) : ℤ :=
  (sgZ 0 Y - sgZ 0 X) * (sgZ 1 M - sgZ 1 X) - (sgZ 1 Y - sgZ 1 X) * (sgZ 0 M - sgZ 0 X)

/-- sign-level necessary condition for `X → Y` to be a strict side (pairs of witnesses) -/
def Sok (e0 e1 e2 : ℤ) (X Y : Fin 8) : Prop :=
  ∀ M M' : Fin 8, M ≠ X → M ≠ Y → M' ≠ X → M' ≠ Y →
    (0 < (cc0 X Y M + cc0 X Y M') * e0 ∨ 0 < (cc1 X Y M + cc1 X Y M') * e1 ∨
      0 < (cc2 X Y M + cc2 X Y M') * e2)

instance (e0 e1 e2 : ℤ) (X Y : Fin 8) : Decidable (Sok e0 e1 e2 X Y) := by
  unfold Sok; infer_instance

def tidx (e0 e1 e2 : ℤ) : ℕ :=
  (if 0 < e0 then 1 else 0) + (if 0 < e1 then 2 else 0) + (if 0 < e2 then 4 else 0)

def Nb (σ : ℕ) (X Y : Fin 8) : Prop :=
  X.val ≠ σ ∧ X.val ≠ σ ^^^ 7 ∧ Y.val ≠ σ ∧ Y.val ≠ σ ^^^ 7 ∧
    (X.val ^^^ Y.val = 1 ∨ X.val ^^^ Y.val = 2 ∨ X.val ^^^ Y.val = 4)

instance (σ : ℕ) (X Y : Fin 8) : Decidable (Nb σ X Y) := by unfold Nb; infer_instance

def sl : List ℤ := [-1, 0, 1]

theorem C0 : ∀ e0 ∈ sl, ∀ e1 ∈ sl, ∀ e2 ∈ sl, (e0 = 0 ∨ e1 = 0 ∨ e2 = 0) →
    ∀ X Y Z : Fin 8, X ≠ Y → Y ≠ Z → Z ≠ X → Sok e0 e1 e2 X Y → ¬ Sok e0 e1 e2 Y Z := by
  decide +kernel

theorem C1 : ∀ e0 ∈ sl, ∀ e1 ∈ sl, ∀ e2 ∈ sl, e0 ≠ 0 → e1 ≠ 0 → e2 ≠ 0 →
    ∀ X Y : Fin 8, X ≠ Y → Sok e0 e1 e2 X Y → Nb (tidx e0 e1 e2) X Y := by
  decide +kernel


def sl' : List ℤ := [-1, 1]

theorem Ctid : ∀ e0 ∈ sl, ∀ e1 ∈ sl, ∀ e2 ∈ sl, tidx e0 e1 e2 < 8 := by decide +kernel

theorem Csymm : ∀ σ < 8, ∀ X Y : Fin 8, Nb σ X Y → Nb σ Y X := by decide +kernel

theorem Cex : ∀ σ < 8, ∃ A1 A2 : Fin 8, A1 ≠ A2 ∧
    (A1.val ^^^ σ = 1 ∨ A1.val ^^^ σ = 2 ∨ A1.val ^^^ σ = 4) ∧
    (A2.val ^^^ σ = 1 ∨ A2.val ^^^ σ = 2 ∨ A2.val ^^^ σ = 4) := by decide +kernel


theorem Cpeak : ∀ e0 ∈ sl', ∀ e1 ∈ sl', ∀ e2 ∈ sl', ∀ A Y : Fin 8,
    Nb (tidx e0 e1 e2) A Y →
    (A.val ^^^ tidx e0 e1 e2 = 1 ∨ A.val ^^^ tidx e0 e1 e2 = 2 ∨ A.val ^^^ tidx e0 e1 e2 = 4) →
    (sgZ 0 Y - sgZ 0 A) * e0 ≤ 0 ∧ (sgZ 1 Y - sgZ 1 A) * e1 ≤ 0 ∧ (sgZ 2 Y - sgZ 2 A) * e2 ≤ 0 ∧
    ((sgZ 0 Y - sgZ 0 A) * e0 < 0 ∨ (sgZ 1 Y - sgZ 1 A) * e1 < 0 ∨ (sgZ 2 Y - sgZ 2 A) * e2 < 0) := by
  decide +kernel


def W5 (σ : ℕ) (A x0 x1 x2 x3 x4 : Fin 8) : Prop :=
  ∀ x5 : Fin 8, Nb σ x4 x5 ∧ x5.val ≠ x3.val →
    (A = x0 ∨ A = x1 ∨ A = x2 ∨ A = x3 ∨ A = x4 ∨ A = x5)
instance (σ : ℕ) (A x0 x1 x2 x3 x4 : Fin 8) : Decidable (W5 σ A x0 x1 x2 x3 x4) := by
  unfold W5; infer_instance
def W4 (σ : ℕ) (A x0 x1 x2 x3 : Fin 8) : Prop :=
  ∀ x4 : Fin 8, Nb σ x3 x4 ∧ x4.val ≠ x2.val → W5 σ A x0 x1 x2 x3 x4
instance (σ : ℕ) (A x0 x1 x2 x3 : Fin 8) : Decidable (W4 σ A x0 x1 x2 x3) := by
  unfold W4; infer_instance
def W3 (σ : ℕ) (A x0 x1 x2 : Fin 8) : Prop :=
  ∀ x3 : Fin 8, Nb σ x2 x3 ∧ x3.val ≠ x1.val → W4 σ A x0 x1 x2 x3
instance (σ : ℕ) (A x0 x1 x2 : Fin 8) : Decidable (W3 σ A x0 x1 x2) := by
  unfold W3; infer_instance
def W2 (σ : ℕ) (A x0 x1 : Fin 8) : Prop :=
  ∀ x2 : Fin 8, Nb σ x1 x2 ∧ x2.val ≠ x0.val → W3 σ A x0 x1 x2
instance (σ : ℕ) (A x0 x1 : Fin 8) : Decidable (W2 σ A x0 x1) := by
  unfold W2; infer_instance

theorem Cwalk : ∀ σ < 8, ∀ A : Fin 8, (A.val ≠ σ ∧ A.val ≠ σ ^^^ 7) →
    ∀ x0 x1 : Fin 8, Nb σ x0 x1 → W2 σ A x0 x1 := by decide +kernel


theorem Cex' : ∀ σ < 8, ∀ A : Fin 8, (A.val ^^^ σ = 1 ∨ A.val ^^^ σ = 2 ∨ A.val ^^^ σ = 4) →
    (A.val ≠ σ ∧ A.val ≠ σ ^^^ 7) := by decide +kernel


open scoped RealInnerProductSpace

noncomputable def sgR (p : ℝ) : ℤ := if 0 < p then 1 else if p < 0 then -1 else 0

theorem sgR_mem (p : ℝ) : sgR p ∈ sl := by
  unfold sgR; split_ifs <;> simp [sl]

theorem glueLE (c : ℤ) (k p : ℝ) (hk : 0 < k) (h : c * sgR p ≤ 0) : (c : ℝ) * (k * p) ≤ 0 := by
  unfold sgR at h
  split_ifs at h with h1 h2
  · have : (c : ℝ) ≤ 0 := by exact_mod_cast (by simpa using h)
    nlinarith [mul_pos hk h1]
  · have : (0 : ℝ) ≤ c := by exact_mod_cast (by simpa using h)
    nlinarith [mul_pos hk (neg_pos.2 h2)]
  · have : p = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
    simp [this]

theorem glueLT (c : ℤ) (k p : ℝ) (hk : 0 < k) (h : c * sgR p < 0) : (c : ℝ) * (k * p) < 0 := by
  unfold sgR at h
  split_ifs at h with h1 h2
  · have : (c : ℝ) < 0 := by exact_mod_cast (by simpa using h)
    nlinarith [mul_pos hk h1]
  · have : (0 : ℝ) < c := by exact_mod_cast (by simpa using h)
    nlinarith [mul_pos hk (neg_pos.2 h2)]
  · simp at h

theorem boxSign_eq (j : ℕ) (X : Fin 8) : boxSign j X = (sgZ j X : ℝ) := by
  unfold boxSign sgZ; split_ifs <;> simp

theorem det_expand (a b c : ℝ) (u : ℝ³) (X Y M : Fin 8) :
    det3 (boxPts a b c Y - boxPts a b c X) (boxPts a b c M - boxPts a b c X) u =
      (cc0 X Y M : ℝ) * (b * c * u 0) + (cc1 X Y M : ℝ) * (a * c * u 1) +
        (cc2 X Y M : ℝ) * (a * b * u 2) := by
  simp [det3, boxPts, boxSign_eq, cc0, cc1, cc2]
  ring

theorem depth_expand (a b c : ℝ) (u : ℝ³) (X : Fin 8) :
    ⟪boxPts a b c X, u⟫ = (sgZ 0 X : ℝ) * (a * u 0) + (sgZ 1 X : ℝ) * (b * u 1) +
        (sgZ 2 X : ℝ) * (c * u 2) := by
  simp [boxPts, boxSign_eq, PiLp.inner_apply, Fin.sum_univ_three]
  ring


theorem depth_lt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (u : ℝ³) (A Y : Fin 8)
    (h0 : sgR (u 0) ∈ sl') (h1 : sgR (u 1) ∈ sl') (h2 : sgR (u 2) ∈ sl')
    (hnb : Nb (tidx (sgR (u 0)) (sgR (u 1)) (sgR (u 2))) A Y)
    (hpk : A.val ^^^ tidx (sgR (u 0)) (sgR (u 1)) (sgR (u 2)) = 1 ∨
      A.val ^^^ tidx (sgR (u 0)) (sgR (u 1)) (sgR (u 2)) = 2 ∨
      A.val ^^^ tidx (sgR (u 0)) (sgR (u 1)) (sgR (u 2)) = 4) :
    ⟪boxPts a b c Y, u⟫ < ⟪boxPts a b c A, u⟫ := by
  obtain ⟨l0, l1, l2, l3⟩ := Cpeak _ h0 _ h1 _ h2 A Y hnb hpk
  rw [depth_expand, depth_expand]
  have g0 := glueLE _ a (u 0) ha l0
  have g1 := glueLE _ b (u 1) hb l1
  have g2 := glueLE _ c (u 2) hc l2
  push_cast at g0 g1 g2
  rcases l3 with l | l | l
  · have := glueLT _ a (u 0) ha l; push_cast at this; linarith
  · have := glueLT _ b (u 1) hb l; push_cast at this; linarith
  · have := glueLT _ c (u 2) hc l; push_cast at this; linarith

theorem boxesHaveNoUnimodalView : BoxesHaveNoUnimodalView := by
  intro a b c ha hb hc u k hk lab hk3 hinj hrim ⟨_, hcard⟩
  have hk0 : 2 < k := hk3
  have hz1 : ∀ m : ℕ, 0 < m → m < k → ((m : ℕ) : ZMod k) ≠ 0 := by
    intro m hm hmk h
    have := (ZMod.natCast_eq_zero_iff m k).1 h
    exact absurd (Nat.le_of_dvd hm this) (by omega)
  have h1 : (1 : ZMod k) ≠ 0 := by simpa using hz1 1 (by omega) (by omega)
  have h2 : (2 : ZMod k) ≠ 0 := by simpa using hz1 2 (by omega) (by omega)
  set e0 := sgR (u 0) with he0
  set e1 := sgR (u 1) with he1
  set e2 := sgR (u 2) with he2
  have hS : ∀ i : ZMod k, Sok e0 e1 e2 (lab i) (lab (i + 1)) := by
    intro i M M' hM1 hM2 hM'1 hM'2
    by_contra hcon
    push_neg at hcon
    obtain ⟨c0, c1, c2⟩ := hcon
    have d1 := hrim M i hM1 hM2
    have d2 := hrim M' i hM'1 hM'2
    rw [det_expand] at d1 d2
    have g0 := glueLE _ (b * c) (u 0) (by positivity) c0
    have g1 := glueLE _ (a * c) (u 1) (by positivity) c1
    have g2 := glueLE _ (a * b) (u 2) (by positivity) c2
    push_cast at g0 g1 g2
    nlinarith
  set xs : ℕ → Fin 8 := fun n => lab (n : ZMod k) with hxs
  have hx : ∀ n : ℕ, Sok e0 e1 e2 (xs n) (xs (n + 1)) := by
    intro n
    have := hS (n : ZMod k)
    simpa [hxs, Nat.cast_succ] using this
  have hne1 : ∀ n : ℕ, xs (n + 1) ≠ xs n := by
    intro n h
    have := hinj h
    simp [Nat.cast_succ] at this
    exact h1 this
  have hne2 : ∀ n : ℕ, xs (n + 2) ≠ xs n := by
    intro n h
    have := hinj h
    simp [Nat.cast_add] at this
    exact h2 this
  by_cases hz : e0 = 0 ∨ e1 = 0 ∨ e2 = 0
  · exact C0 e0 (sgR_mem _) e1 (sgR_mem _) e2 (sgR_mem _) hz (xs 0) (xs 1) (xs 2)
      (hne1 0).symm (hne1 1).symm (hne2 0) (hx 0) (hx 1)
  push_neg at hz
  obtain ⟨z0, z1, z2⟩ := hz
  have m0 : e0 ∈ sl' := by have := sgR_mem (u 0); simp [sl, sl'] at this ⊢; omega
  have m1 : e1 ∈ sl' := by have := sgR_mem (u 1); simp [sl, sl'] at this ⊢; omega
  have m2 : e2 ∈ sl' := by have := sgR_mem (u 2); simp [sl, sl'] at this ⊢; omega
  set σ := tidx e0 e1 e2 with hσ
  have hσ8 : σ < 8 := Ctid e0 (sgR_mem _) e1 (sgR_mem _) e2 (sgR_mem _)
  have hnb : ∀ i : ZMod k, Nb σ (lab i) (lab (i + 1)) := by
    intro i
    refine C1 e0 (sgR_mem _) e1 (sgR_mem _) e2 (sgR_mem _) z0 z1 z2 _ _ ?_ (hS i)
    intro h
    have := hinj h
    simp at this
    exact h1 this
  have hnbx : ∀ n : ℕ, Nb σ (xs n) (xs (n + 1)) := by
    intro n
    simpa [hxs, Nat.cast_succ] using hnb (n : ZMod k)
  have hv : ∀ n : ℕ, (xs (n + 1)).val ≠ (xs n).val := fun n h => hne1 n (Fin.ext h)
  have hv2 : ∀ n : ℕ, (xs (n + 2)).val ≠ (xs n).val := fun n h => hne2 n (Fin.ext h)
  have cover : ∀ A : Fin 8, (A.val ^^^ σ = 1 ∨ A.val ^^^ σ = 2 ∨ A.val ^^^ σ = 4) →
      ∃ i : ZMod k, lab i = A := by
    intro A hA
    have hA' := Cex' σ hσ8 A hA
    have := Cwalk σ hσ8 A hA' (xs 0) (xs 1) (hnbx 0) (xs 2) ⟨hnbx 1, hv2 0⟩
      (xs 3) ⟨hnbx 2, hv2 1⟩ (xs 4) ⟨hnbx 3, hv2 2⟩ (xs 5) ⟨hnbx 4, hv2 3⟩
    rcases this with h | h | h | h | h | h
    · exact ⟨((0 : ℕ) : ZMod k), h.symm⟩
    · exact ⟨((1 : ℕ) : ZMod k), h.symm⟩
    · exact ⟨((2 : ℕ) : ZMod k), h.symm⟩
    · exact ⟨((3 : ℕ) : ZMod k), h.symm⟩
    · exact ⟨((4 : ℕ) : ZMod k), h.symm⟩
    · exact ⟨((5 : ℕ) : ZMod k), h.symm⟩
  have peak : ∀ i : ZMod k, ((lab i).val ^^^ σ = 1 ∨ (lab i).val ^^^ σ = 2 ∨ (lab i).val ^^^ σ = 4) →
      i ∈ Finset.univ.filter (fun i : ZMod k =>
        ⟪boxPts a b c (lab (i - 1)), u⟫ < ⟪boxPts a b c (lab i), u⟫ ∧
        ⟪boxPts a b c (lab (i + 1)), u⟫ < ⟪boxPts a b c (lab i), u⟫) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · have := hnb (i - 1)
      rw [sub_add_cancel] at this
      exact depth_lt a b c ha hb hc u _ _ m0 m1 m2 (Csymm σ hσ8 _ _ this) hi
    · exact depth_lt a b c ha hb hc u _ _ m0 m1 m2 (hnb i) hi
  obtain ⟨A1, A2, hne, hp1, hp2⟩ := Cex σ hσ8
  obtain ⟨i1, hi1⟩ := cover A1 hp1
  obtain ⟨i2, hi2⟩ := cover A2 hp2
  have f1 := peak i1 (by rw [hi1]; exact hp1)
  have f2 := peak i2 (by rw [hi2]; exact hp2)
  obtain ⟨x, hx1⟩ := Finset.card_eq_one.1 hcard
  rw [hx1, Finset.mem_singleton] at f1 f2
  exact hne (by rw [← hi1, ← hi2, f1, f2])

end MinimalityExtra
