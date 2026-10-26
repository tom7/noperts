module

public import Minimality.ParallelFar
public import Minimality.ParallelFarNM
public import Minimality.TriShadowMid
public import Minimality.TriShadowMidP
public import Minimality.TriShadow2Mid

@[expose] public section

/-!
# Both faces with a vertical far edge: the four sectors

The tilt `(-s α, s β)` of `isRupert_triShadow_tilt` has two sectors for each `s`, according to
the sign of `A β - B α` (the tilt is parallel to the far edge `A B` when it is zero).  A
vertical companion of the first face's far end is strictly inside the shadow when
`A β < B α` (`tiltOK_farComp1`), and a vertical companion of the second face's far end when
`B α < A β` (`tiltOK_farComp2`); the two cannot both hold, which is why a single sector
needed one face with a unique far end.

When both faces have a vertical far edge, the paper (FEWER-FACES-PROOFS.md Proposition 24.12,
and Proposition 23.19 (1)–(3)) takes the sector in which one of the vertical edges is a cycle
edge: the cycle is `C1, M, C2 reversed` with the middle vertex `M` the other end of the vertical
far edge of the second face (`A β < B α`, `M` above `Q` for `s = 1`) or of the first face
(`B α < A β`, `M` below `P` for `s = 1`).  `isRupert_triShadow_mid` is the frame theorem; this
file gives the `TiltOK` tests of the two new cycle edges.
-/

namespace Minimality

/-- The vertical cycle edge `M → Q` over the second ray (sector `A β < B α`): every point of
the shadow triangle off that vertical passes the test. -/
theorem tiltOK_vertB {s α β A B zM zQ a b z : ℝ} (hα : 0 < α) (hβ : 0 < β) (hA : 0 < A)
    (hr : A * β < B * α) (hz : s * (zQ - zM) < 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : a * B + b * A ≤ A * B) (hne : 0 < a ∨ b < B) :
    TiltOK 0 B zM 0 B zQ a b z (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have hB : 0 < B := by nlinarith [mul_pos hA hβ]
  have e : (zQ - zM) * ((a - 0) * (s * β) - (b - B) * (-s * α)) -
      (z - zM) * ((0 - 0) * (s * β) - (B - B) * (-s * α)) =
      (s * (zQ - zM)) * (β * a + α * (b - B)) := by ring
  rw [e]
  refine mul_pos_of_neg_of_neg hz ?_
  rcases hne with h | h
  · nlinarith [mul_pos h (sub_pos.mpr hr), mul_nonneg hα.le hb, mul_pos hα hA]
  · nlinarith [mul_pos hα (sub_pos.mpr h), mul_nonneg ha (sub_pos.mpr hr).le, mul_pos hα hA]

/-- The second face's far end tested against the edge `P → M` (sector `A β < B α`, `M` on the
vertical of `Q`). -/
theorem tiltOK_farQ {s A B zp zq zy α β : ℝ} (hc : 0 < s * (zq - zy)) (hr : A * β < B * α) :
    TiltOK A 0 zp 0 B zq 0 B zy (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have e : (zq - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) -
      (zy - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) =
      (s * (zq - zy)) * (B * α - A * β) := by ring
  rw [e]
  exact mul_pos hc (by linarith)

/-- The vertical cycle edge `P → M` over the first ray (sector `B α < A β`): every point of the
shadow triangle off that vertical passes the test. -/
theorem tiltOK_vertA {s α β A B zP zM a b z : ℝ} (hα : 0 < α) (hβ : 0 < β) (hB : 0 < B)
    (hr : B * α < A * β) (hz : s * (zM - zP) < 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : a * B + b * A ≤ A * B) (hne : a < A) :
    TiltOK A 0 zP A 0 zM a b z (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have hA : 0 < A := by nlinarith [mul_pos hB hα]
  have e : (zM - zP) * ((a - A) * (s * β) - (b - 0) * (-s * α)) -
      (z - zP) * ((A - A) * (s * β) - (0 - 0) * (-s * α)) =
      (s * (zM - zP)) * (β * (a - A) + α * b) := by ring
  rw [e]
  refine mul_pos_of_neg_of_neg hz ?_
  nlinarith [mul_pos (sub_pos.mpr hne) (sub_pos.mpr hr), mul_pos hα hB, mul_pos hα hA,
    mul_nonneg hα.le hb]

/-- The first face's far end tested against the edge `M → Q` (sector `B α < A β`, `M` on the
vertical of `P`). -/
theorem tiltOK_farComp1' {s A B zp zq zy α β : ℝ} (hc : 0 < s * (zy - zp)) (hr : B * α < A * β) :
    TiltOK A 0 zp 0 B zq A 0 zy (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have e : (zq - zp) * ((A - A) * (s * β) - (0 - 0) * (-s * α)) -
      (zy - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) =
      (s * (zy - zp)) * (A * β - B * α) := by ring
  rw [e]
  exact mul_pos hc (by linarith)

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, cycle with a middle vertex, from the tests.**  As
`vertex_core_par`, for the cycle `C1, M, C2 reversed` of `isRupert_triShadow_mid`: the tests of
the points of each face and of the interior points against the two edges `P → M`, `M → Q` are
the hypotheses `f1`, `f2`, `f3`. -/
theorem vertex_core_mid (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ} (s : ℝ) (hs : s = 1 ∨ s = -1) {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z0 s m ca cz) (C2 : ChainOKc Q2 z0 (-s) n cb dz)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (aM bM zM : ℝ)
    (hM1 : ∀ l, l ≤ m → oblPt O r1 r2 aM bM zM ≠ oblPt O r1 r2 (ca l) 0 (cz l))
    (hM2 : ∀ l, l ≤ n → oblPt O r1 r2 aM bM zM ≠ oblPt O r1 r2 0 (cb l) (dz l))
    (hmode : (s * zM < s * cz m ∧ (s * dz n < s * zM ∨ s * dz n < s * dz (n - 1))) ∨
      (s * dz n < s * zM ∧ s * cz (m - 1) < s * cz m))
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³) (hMV : oblPt O r1 r2 aM bM zM ∈ V)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n)))
    (f1 : ∀ a z, Q1 a z →
      (TiltOK (ca m) 0 (cz m) aM bM zM a 0 z (-s * α) (s * β) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 (cz m) ∨ oblPt O r1 r2 a 0 z
          = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) a 0 z (-s * α) (s * β) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 aM bM zM ∨ oblPt O r1 r2 a 0 z
          = oblPt O r1 r2 0 (cb n) (dz n)))
    (f2 : ∀ b z, Q2 b z →
      (TiltOK (ca m) 0 (cz m) aM bM zM 0 b z (-s * α) (s * β) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 (ca m) 0 (cz m) ∨ oblPt O r1 r2 0 b z
          = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) 0 b z (-s * α) (s * β) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 aM bM zM ∨ oblPt O r1 r2 0 b z
          = oblPt O r1 r2 0 (cb n) (dz n)))
    (f3 : ∀ a b z, 0 < a → 0 < b → a * cb n + b * ca m < ca m * cb n →
      (TiltOK (ca m) 0 (cz m) aM bM zM a b z (-s * α) (s * β) ∨
        oblPt O r1 r2 a b z = oblPt O r1 r2 (ca m) 0 (cz m) ∨ oblPt O r1 r2 a b z
          = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) a b z (-s * α) (s * β) ∨
        oblPt O r1 r2 a b z = oblPt O r1 r2 aM bM zM ∨ oblPt O r1 r2 a b z
          = oblPt O r1 r2 0 (cb n) (dz n))) :
    IsRupert V := by
  have c10 := C1.start; have c20 := C2.start
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      -s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have q20 : Q2 0 z0 := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
  have q10 : Q1 0 z0 := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
  have hVc' : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (TiltOK (ca m) 0 (cz m) aM bM zM a b z (-s * α) (s * β) ∨
        y = oblPt O r1 r2 (ca m) 0 (cz m) ∨ y = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) a b z (-s * α) (s * β) ∨
        y = oblPt O r1 r2 aM bM zM ∨ y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) -
          (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0) := by
    intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
    rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
    · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, (f1 a z hq).1, (f1 a z hq).2,
        fun _ => side1 a z hq, ?_⟩
      intro ha; subst ha; rw [hap1 z hq]; exact side2 0 z0 q20
    · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, (f2 b z hq).1, (f2 b z hq).2, ?_,
        fun _ => side2 b z hq⟩
      intro hb; subst hb; rw [hap2 z hq]; exact side1 0 z0 q10
    · exact ⟨a, b, z, rfl, ha.le, hb.le, (f3 a b z ha hb hin).1, (f3 a b z ha hb hin).2,
        fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩
  rcases hmode with ⟨hPM, hMQ⟩ | ⟨hMQ, hPrev⟩
  · exact isRupert_triShadow_mid O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1
      c20.1 (by rw [c10.2, c20.2]) C1.inc C2.inc V aM bM zM hMV hM1 hM2
      (fun l hl => hV1 _ _ (C1.mem l hl)) (fun l hl => hV2 _ _ (C2.mem l hl)) hVc' hPM hMQ
  · exact isRupert_triShadow_midP O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1
      c20.1 (by rw [c10.2, c20.2]) C1.inc C2.inc V aM bM zM hMV hM1 hM2
      (fun l hl => hV1 _ _ (C1.mem l hl)) (fun l hl => hV2 _ _ (C2.mem l hl)) hVc' hMQ hPrev

set_option maxHeartbeats 4000000 in
/-- **Both far ends have vertical companions, sector `A β < B α`**: the middle vertex is the
other end `T` of the second face's vertical far edge, above the far end `Q` of the chain
(`s z_Q < s z_T`) and below `P` (`s z_T < s z_P`), or else not below `P` (a tie, as in the
rectangle) with `P` above its chain predecessor (`hP`, second form: the last vertex of the chain
of a triangle; Proposition 24.12).  The first face's vertical companion of `P` is strictly inside
the shadow (`tiltOK_farComp1`). -/
theorem vertex_core_tail2 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ} (s : ℝ) (hs : s = 1 ∨ s = -1) {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z0 s m ca cz) (C2 : ChainOKc Q2 z0 (-s) n cb dz)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : ca m * β < cb n * α) {zT : ℝ}
    (hT : Q2 (cb n) zT) (hcard : ∀ z, Q2 (cb n) z → z = dz n ∨ z = zT)
    (hP : s * zT < s * cz m ∨ s * cz (m - 1) < s * cz m) (hMQ : s * dz n < s * zT)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have hne : zT ≠ dz n := fun e => by rw [e] at hMQ; exact lt_irrefl _ hMQ
  have hQz : s * (dz n - zT) < 0 := by linarith
  refine vertex_core_mid O r1 r2 hρ Q1 Q2 s hs C1 C2 hα hβ 0 (cb n) zT ?_ ?_
    (hP.imp (fun h => ⟨h, Or.inl hMQ⟩) (fun h => ⟨hMQ, h⟩)) hap1 hap2
    hpos1 hpos2 V (hV2 _ _ hT) hV1 hV2 hVc ?_ ?_ ?_
  · intro l hl he
    have := (oblPt_inj hρ he).2.1
    linarith
  · intro l hl he
    obtain ⟨-, eb, ez'⟩ := oblPt_inj hρ he
    rcases hl.lt_or_eq with hl | rfl
    · have := C2.mono l n hl le_rfl
      linarith
    · exact hne ez'
  · intro a z hq
    have hale := C1.a_le hq
    refine ⟨?_, Or.inl (tiltOK_vertB hα hβ hA0 hr hQz (hpos1 a z hq) le_rfl
      (by nlinarith) (Or.inr hB0))⟩
    by_cases h : a = ca m ∧ z = cz m
    · exact Or.inr (Or.inl (by rw [h.1, h.2]))
    left
    rcases C1.far a z hq h with hlt | ⟨ea, hc⟩
    · exact far_tiltOK (by nlinarith)
    · subst ea
      exact tiltOK_farComp1 hc hr
  · intro b z hq
    have hble := C2.a_le hq
    by_cases hb : b = cb n
    · subst hb
      rcases hcard z hq with rfl | rfl
      · exact ⟨Or.inl (tiltOK_farQ (by linarith) hr), Or.inr (Or.inr rfl)⟩
      · exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · have hlt : b < cb n := lt_of_le_of_ne hble hb
      exact ⟨Or.inl (far_tiltOK (by nlinarith)), Or.inl (tiltOK_vertB hα hβ hA0 hr hQz le_rfl
        (hpos2 b z hq) (by nlinarith) (Or.inr hlt))⟩
  · intro a b z ha hb hin
    exact ⟨Or.inl (far_tiltOK hin), Or.inl (tiltOK_vertB hα hβ hA0 hr hQz ha.le hb.le
      (by nlinarith) (Or.inl ha))⟩

set_option maxHeartbeats 4000000 in
/-- **Both far ends have vertical companions, sector `B α < A β`**: the middle vertex is the
other end `T` of the first face's vertical far edge, below `P` (`s z_T < s z_P`) and above the
far end `Q` of the second chain (`s z_Q < s z_T`), or else not above `Q` (a tie, as in the
rectangle) with `Q` below its chain predecessor (the last vertex of the chain of a triangle;
Proposition 24.12).  The second face's vertical companion of `Q` is strictly inside the shadow
(`tiltOK_farComp2`). -/
theorem vertex_core_tail1 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ} (s : ℝ) (hs : s = 1 ∨ s = -1) {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z0 s m ca cz) (C2 : ChainOKc Q2 z0 (-s) n cb dz)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : cb n * α < ca m * β) {zT : ℝ}
    (hT : Q1 (ca m) zT) (hcard : ∀ z, Q1 (ca m) z → z = cz m ∨ z = zT)
    (hPM : s * zT < s * cz m)
    (hMQ : s * dz n < s * zT ∨ s * dz n < s * dz (n - 1))
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have hne : zT ≠ cz m := fun e => by rw [e] at hPM; exact lt_irrefl _ hPM
  have hPz : s * (zT - cz m) < 0 := by linarith
  refine vertex_core_mid O r1 r2 hρ Q1 Q2 s hs C1 C2 hα hβ (ca m) 0 zT ?_ ?_ (Or.inl ⟨hPM, hMQ⟩)
    hap1 hap2
    hpos1 hpos2 V (by simpa using hV1 _ _ hT) hV1 hV2 hVc ?_ ?_ ?_
  · intro l hl he
    obtain ⟨ea, -, ez'⟩ := oblPt_inj hρ he
    rcases hl.lt_or_eq with hl | rfl
    · have := C1.mono l m hl le_rfl
      linarith
    · exact hne ez'
  · intro l hl he
    have := (oblPt_inj hρ he).1
    linarith
  · intro a z hq
    have hale := C1.a_le hq
    by_cases ha : a = ca m
    · subst ha
      rcases hcard z hq with rfl | rfl
      · exact ⟨Or.inr (Or.inl rfl), Or.inl (tiltOK_farComp1' (by linarith) hr)⟩
      · exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · have hlt : a < ca m := lt_of_le_of_ne hale ha
      exact ⟨Or.inl (tiltOK_vertA hα hβ hB0 hr hPz (hpos1 a z hq) le_rfl (by nlinarith) hlt),
        Or.inl (far_tiltOK (by nlinarith))⟩
  · intro b z hq
    have hble := C2.a_le hq
    refine ⟨Or.inl (tiltOK_vertA hα hβ hB0 hr hPz le_rfl (hpos2 b z hq) (by nlinarith) hA0), ?_⟩
    by_cases h : b = cb n ∧ z = dz n
    · exact Or.inr (Or.inr (by rw [h.1, h.2]))
    left
    rcases C2.far b z hq h with hlt | ⟨eb, hc⟩
    · exact far_tiltOK (by nlinarith)
    · subst eb
      exact tiltOK_farComp2 (by linarith) hr
  · intro a b z ha hb hin
    have hlt : a < ca m := by nlinarith
    exact ⟨Or.inl (tiltOK_vertA hα hβ hB0 hr hPz ha.le hb.le (by nlinarith) hlt),
      Or.inl (far_tiltOK hin)⟩
set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, cycle with a middle vertex, from the tests** (as `vertex_core_mid`
for `edge_core_par` and `isRupert_triShadow2_mid`). -/
theorem edge_core_mid (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s) {m n : ℕ}
    {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z1s s m ca cz) (C2 : ChainOKc Q2 z2s (-s) n cb dz)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (aM bM zM : ℝ)
    (hM1 : ∀ l, l ≤ m → oblPt O r1 r2 aM bM zM ≠ oblPt O r1 r2 (ca l) 0 (cz l))
    (hM2 : ∀ l, l ≤ n → oblPt O r1 r2 aM bM zM ≠ oblPt O r1 r2 0 (cb l) (dz l))
    (hPM : s * zM < s * cz m) (hMQ : s * dz n < s * zM)
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z1 : Q2 0 z1s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³) (hMV : oblPt O r1 r2 aM bM zM ∈ V)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n)))
    (f1 : ∀ a z, Q1 a z →
      (TiltOK (ca m) 0 (cz m) aM bM zM a 0 z (-s * α) (s * β) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 (cz m) ∨ oblPt O r1 r2 a 0 z
          = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) a 0 z (-s * α) (s * β) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 aM bM zM ∨ oblPt O r1 r2 a 0 z
          = oblPt O r1 r2 0 (cb n) (dz n)))
    (f2 : ∀ b z, Q2 b z →
      (TiltOK (ca m) 0 (cz m) aM bM zM 0 b z (-s * α) (s * β) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 (ca m) 0 (cz m) ∨ oblPt O r1 r2 0 b z
          = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) 0 b z (-s * α) (s * β) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 aM bM zM ∨ oblPt O r1 r2 0 b z
          = oblPt O r1 r2 0 (cb n) (dz n)))
    (f3 : ∀ a b z, 0 < a → 0 < b → a * cb n + b * ca m < ca m * cb n →
      (TiltOK (ca m) 0 (cz m) aM bM zM a b z (-s * α) (s * β) ∨
        oblPt O r1 r2 a b z = oblPt O r1 r2 (ca m) 0 (cz m) ∨ oblPt O r1 r2 a b z
          = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) a b z (-s * α) (s * β) ∨
        oblPt O r1 r2 a b z = oblPt O r1 r2 aM bM zM ∨ oblPt O r1 r2 a b z
          = oblPt O r1 r2 0 (cb n) (dz n))) :
    IsRupert V := by
  have c10 := C1.start; have c20 := C2.start
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      -s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have apx : ∀ z, z = z1s ∨ z = z2s → oblPt O r1 r2 0 0 z = oblPt O r1 r2 (ca 0) 0 (cz 0) ∨
      oblPt O r1 r2 0 0 z = oblPt O r1 r2 0 (cb 0) (dz 0) := by
    rintro z (rfl | rfl)
    · left; rw [c10.1, c10.2]
    · right; rw [c20.1, c20.2]
  have q1of : ∀ z, Q2 0 z → Q1 0 z := by
    intro z h; rcases hap2 z h with rfl | rfl
    · exact (by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _))
    · exact hQ1z2
  have q2of : ∀ z, Q1 0 z → Q2 0 z := by
    intro z h; rcases hap1 z h with rfl | rfl
    · exact hQ2z1
    · exact (by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _))
  refine isRupert_triShadow2_mid O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]; exact hap) C1.inc C2.inc V aM bM zM hMV hM1 hM2
    (fun l hl => hV1 _ _ (C1.mem l hl)) (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hPM hMQ
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, (f1 a z hq).1, (f1 a z hq).2, ?_,
      fun _ => side1 a z hq, ?_⟩
    · intro ha _; subst ha; exact apx z (hap1 z hq)
    · intro ha; subst ha; exact side2 0 z (q2of z hq)
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, (f2 b z hq).1, (f2 b z hq).2, ?_, ?_,
      fun _ => side2 b z hq⟩
    · intro _ hb; subst hb; exact apx z (hap2 z hq)
    · intro hb; subst hb; exact side1 0 z (q1of z hq)
  · exact ⟨a, b, z, rfl, ha.le, hb.le, (f3 a b z ha hb hin).1, (f3 a b z ha hb hin).2,
      fun h => absurd h ha.ne', fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩

set_option maxHeartbeats 4000000 in
/-- **Over an edge, both far ends have vertical companions,
  sector `A β < B α`**: the middle vertex is the
other end `T` of the second face's vertical far edge, above the far end `Q` of the chain
(`s z_Q < s z_T`) and below `P` (`s z_T < s z_P`).  The first face's vertical companion of `P`
is strictly inside the shadow (`tiltOK_farComp1`). -/
theorem edge_core_tail2 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s) {m n : ℕ}
    {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z1s s m ca cz) (C2 : ChainOKc Q2 z2s (-s) n cb dz)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : ca m * β < cb n * α) {zT : ℝ}
    (hT : Q2 (cb n) zT) (hcard : ∀ z, Q2 (cb n) z → z = dz n ∨ z = zT)
    (hPM : s * zT < s * cz m) (hMQ : s * dz n < s * zT)
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z1 : Q2 0 z1s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have hne : zT ≠ dz n := fun e => by rw [e] at hMQ; exact lt_irrefl _ hMQ
  have hQz : s * (dz n - zT) < 0 := by linarith
  refine edge_core_mid O r1 r2 hρ Q1 Q2 s hs hap C1 C2 hα hβ 0 (cb n) zT ?_ ?_ hPM hMQ hap1 hap2
    hQ1z2 hQ2z1
    hpos1 hpos2 V (hV2 _ _ hT) hV1 hV2 hVc ?_ ?_ ?_
  · intro l hl he
    have := (oblPt_inj hρ he).2.1
    linarith
  · intro l hl he
    obtain ⟨-, eb, ez'⟩ := oblPt_inj hρ he
    rcases hl.lt_or_eq with hl | rfl
    · have := C2.mono l n hl le_rfl
      linarith
    · exact hne ez'
  · intro a z hq
    have hale := C1.a_le hq
    refine ⟨?_, Or.inl (tiltOK_vertB hα hβ hA0 hr hQz (hpos1 a z hq) le_rfl
      (by nlinarith) (Or.inr hB0))⟩
    by_cases h : a = ca m ∧ z = cz m
    · exact Or.inr (Or.inl (by rw [h.1, h.2]))
    left
    rcases C1.far a z hq h with hlt | ⟨ea, hc⟩
    · exact far_tiltOK (by nlinarith)
    · subst ea
      exact tiltOK_farComp1 hc hr
  · intro b z hq
    have hble := C2.a_le hq
    by_cases hb : b = cb n
    · subst hb
      rcases hcard z hq with rfl | rfl
      · exact ⟨Or.inl (tiltOK_farQ (by linarith) hr), Or.inr (Or.inr rfl)⟩
      · exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · have hlt : b < cb n := lt_of_le_of_ne hble hb
      exact ⟨Or.inl (far_tiltOK (by nlinarith)), Or.inl (tiltOK_vertB hα hβ hA0 hr hQz le_rfl
        (hpos2 b z hq) (by nlinarith) (Or.inr hlt))⟩
  · intro a b z ha hb hin
    exact ⟨Or.inl (far_tiltOK hin), Or.inl (tiltOK_vertB hα hβ hA0 hr hQz ha.le hb.le
      (by nlinarith) (Or.inl ha))⟩

set_option maxHeartbeats 4000000 in
/-- **Over an edge, both far ends have vertical companions,
  sector `B α < A β`**: the middle vertex is the
other end `T` of the first face's vertical far edge, below `P` (`s z_T < s z_P`) and above the
far end `Q` of the second chain (`s z_Q < s z_T`).  The second face's vertical companion of
`Q` is strictly inside the shadow (`tiltOK_farComp2`). -/
theorem edge_core_tail1 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s) {m n : ℕ}
    {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z1s s m ca cz) (C2 : ChainOKc Q2 z2s (-s) n cb dz)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr : cb n * α < ca m * β) {zT : ℝ}
    (hT : Q1 (ca m) zT) (hcard : ∀ z, Q1 (ca m) z → z = cz m ∨ z = zT)
    (hPM : s * zT < s * cz m) (hMQ : s * dz n < s * zT)
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z1 : Q2 0 z1s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have hne : zT ≠ cz m := fun e => by rw [e] at hPM; exact lt_irrefl _ hPM
  have hPz : s * (zT - cz m) < 0 := by linarith
  refine edge_core_mid O r1 r2 hρ Q1 Q2 s hs hap C1 C2 hα hβ (ca m) 0 zT ?_ ?_ hPM hMQ hap1 hap2
    hQ1z2 hQ2z1
    hpos1 hpos2 V (by simpa using hV1 _ _ hT) hV1 hV2 hVc ?_ ?_ ?_
  · intro l hl he
    obtain ⟨ea, -, ez'⟩ := oblPt_inj hρ he
    rcases hl.lt_or_eq with hl | rfl
    · have := C1.mono l m hl le_rfl
      linarith
    · exact hne ez'
  · intro l hl he
    have := (oblPt_inj hρ he).1
    linarith
  · intro a z hq
    have hale := C1.a_le hq
    by_cases ha : a = ca m
    · subst ha
      rcases hcard z hq with rfl | rfl
      · exact ⟨Or.inr (Or.inl rfl), Or.inl (tiltOK_farComp1' (by linarith) hr)⟩
      · exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · have hlt : a < ca m := lt_of_le_of_ne hale ha
      exact ⟨Or.inl (tiltOK_vertA hα hβ hB0 hr hPz (hpos1 a z hq) le_rfl (by nlinarith) hlt),
        Or.inl (far_tiltOK (by nlinarith))⟩
  · intro b z hq
    have hble := C2.a_le hq
    refine ⟨Or.inl (tiltOK_vertA hα hβ hB0 hr hPz le_rfl (hpos2 b z hq) (by nlinarith) hA0), ?_⟩
    by_cases h : b = cb n ∧ z = dz n
    · exact Or.inr (Or.inr (by rw [h.1, h.2]))
    left
    rcases C2.far b z hq h with hlt | ⟨eb, hc⟩
    · exact far_tiltOK (by nlinarith)
    · subst eb
      exact tiltOK_farComp2 (by linarith) hr
  · intro a b z ha hb hin
    have hlt : a < ca m := by nlinarith
    exact ⟨Or.inl (tiltOK_vertA hα hβ hB0 hr hPz ha.le hb.le (by nlinarith) hlt),
      Or.inl (far_tiltOK hin)⟩

/-- An upper chain ends above a lower one. -/
theorem ChainOKc.low_le_up {Q : ℝ → ℝ → Prop} {z0 z0' : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ}
    (U : ChainOKc Q z0 1 m ca cz) (L : ChainOKc Q z0' (-1) m' ca' cz') : cz' m' ≤ cz m := by
  have ea := U.far_a_eq L
  by_cases e : ca' m' = ca m ∧ cz' m' = cz m
  · exact e.2.le
  rcases U.far _ _ (L.mem m' le_rfl) e with h | ⟨-, h⟩
  · exact absurd ea (by linarith)
  · linarith

/-- **A face with a vertical far edge has two far ends.**  If the vertical over the far end of
the upper chain carries a second point `c` and at most two points lie on a vertical, then the
lower chain ends at `c`, below the upper chain's end, and the vertical carries nothing else. -/
theorem ChainOKc.two_ends {Q : ℝ → ℝ → Prop} {z0 z0' : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ}
    (U : ChainOKc Q z0 1 m ca cz) (L : ChainOKc Q z0' (-1) m' ca' cz')
    (hcard : ∀ a z1 z2 z3, Q a z1 → Q a z2 → Q a z3 → z1 = z2 ∨ z1 = z3 ∨ z2 = z3) {c : ℝ}
    (hc : Q (ca m) c) (hcne : c ≠ cz m) :
    ca' m' = ca m ∧ cz' m' = c ∧ c < cz m ∧ ∀ z, Q (ca m) z → z = cz m ∨ z = c := by
  have ea := U.far_a_eq L
  have hlt : c < cz m := by
    rcases U.far _ _ hc (fun h => hcne h.2) with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · linarith
  have hL : Q (ca m) (cz' m') := by rw [ea]; exact L.mem m' le_rfl
  have hcz : cz' m' = c := by
    rcases hcard (ca m) (cz m) c (cz' m') (U.mem m le_rfl) hc hL with h | h | h
    · exact absurd h.symm hcne
    · exfalso
      have hne' : ¬ (ca m = ca' m' ∧ c = cz' m') := fun h' => hcne (h'.2.trans h.symm)
      rcases L.far _ _ hc hne' with h2 | ⟨-, h2⟩
      · exact absurd h2 (by linarith)
      · linarith
    · exact h.symm
  refine ⟨ea.symm, hcz, hlt, fun z hz => ?_⟩
  rcases hcard (ca m) z (cz m) c hz (U.mem m le_rfl) hc with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (ne_of_gt hlt)

/-- The far depths of the two faces leave room for a tilt: they are not all equal.  The four
ways the hypotheses of the frames guarantee it: all four depths different from the top-top and
top-bottom comparisons; exactly one face with a vertical far edge (its two ends differ), the
other face's far end then free to tie with either of them (FEWER-FACES-PROOFS.md Proposition
23.19 (1)); or both faces with a vertical far edge and not the rectangle (tops or bottoms
differ; Proposition 23.19, last bullet). -/
theorem hfar_of_sep {cz cz' dz dz' : ℝ} {R : Prop} (t1 : cz' ≤ cz) (t2 : dz' ≤ dz)
    (h : (cz ≠ dz ∧ cz ≠ dz') ∨ (cz' < cz ∧ dz' = dz) ∨ (cz' = cz ∧ dz' < dz) ∨
      (cz' < cz ∧ dz' < dz ∧ R)) :
    dz' < cz ∨ cz' < dz := by
  rcases h with ⟨-, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
  · rcases lt_or_gt_of_ne h2 with h | h
    · right; linarith
    · left; exact h
  · by_cases h : dz' < cz
    · left; exact h
    · right; linarith
  · by_cases h : cz' < dz
    · right; exact h
    · left; linarith
  · by_cases h : dz' < cz
    · left; exact h
    · right; linarith

/-- A face (as a set of points `(a, z)` of its plane) with at most three points: any four of its
points repeat. -/
def AtMost3 (Q : ℝ → ℝ → Prop) : Prop :=
  ∀ p1 p2 p3 p4 : ℝ × ℝ, Q p1.1 p1.2 → Q p2.1 p2.2 → Q p3.1 p3.2 → Q p4.1 p4.2 →
    p1 = p2 ∨ p1 = p3 ∨ p1 = p4 ∨ p2 = p3 ∨ p2 = p4 ∨ p3 = p4

/-- A finite set of at most three points is `AtMost3`. -/
theorem AtMost3.of_card_le {S : Finset (ℝ × ℝ)} (h : S.card ≤ 3) :
    AtMost3 (fun x z => (x, z) ∈ S) := by
  intro p1 p2 p3 p4 h1 h2 h3 h4
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n13, n14, n23, n24, n34⟩ := hcon
  have hsub : ({p1, p2, p3, p4} : Finset (ℝ × ℝ)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have c := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [n12, n13, n14]),
    Finset.card_insert_of_notMem (by simp [n23, n24]),
    Finset.card_insert_of_notMem (by simp [n34]), Finset.card_singleton] at c
  omega

/-- A face (as a set of points `(a, z)` of its plane) with at most four points: any five of its
points repeat. -/
def AtMost4 (Q : ℝ → ℝ → Prop) : Prop :=
  ∀ p1 p2 p3 p4 p5 : ℝ × ℝ, Q p1.1 p1.2 → Q p2.1 p2.2 → Q p3.1 p3.2 → Q p4.1 p4.2 →
    Q p5.1 p5.2 → p1 = p2 ∨ p1 = p3 ∨ p1 = p4 ∨ p1 = p5 ∨ p2 = p3 ∨ p2 = p4 ∨ p2 = p5 ∨
      p3 = p4 ∨ p3 = p5 ∨ p4 = p5

/-- A finite set of at most four points is `AtMost4`. -/
theorem AtMost4.of_card_le {S : Finset (ℝ × ℝ)} (h : S.card ≤ 4) :
    AtMost4 (fun x z => (x, z) ∈ S) := by
  intro p1 p2 p3 p4 p5 h1 h2 h3 h4 h5
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n13, n14, n15, n23, n24, n25, n34, n35, n45⟩ := hcon
  have hsub : ({p1, p2, p3, p4, p5} : Finset (ℝ × ℝ)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have c := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [n12, n13, n14, n15]),
    Finset.card_insert_of_notMem (by simp [n23, n24, n25]),
    Finset.card_insert_of_notMem (by simp [n34, n35]),
    Finset.card_insert_of_notMem (by simp [n45]), Finset.card_singleton] at c
  omega

/-- **A chain of a triangle has no middle**: if the vertical over the far end of a chain carries
a second point and the face has at most three points, the chain is the single segment from the
apex to the far end (FEWER-FACES-PROOFS.md Proposition 24.12: the chains of a triangle face have
no middles). -/
theorem ChainOKc.m_eq_one {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOKc Q z0 s m ca cz) (h3 : AtMost3 Q) {c : ℝ} (hc : Q (ca m) c) (hne : c ≠ cz m) :
    m = 1 := by
  by_contra hm
  have hm2 : 2 ≤ m := by have := C.one_le; omega
  have a01 := C.mono 0 1 (by omega) (by omega)
  have a1m := C.mono 1 m (by omega) le_rfl
  rcases h3 (ca 0, cz 0) (ca 1, cz 1) (ca m, cz m) (ca m, c) (C.mem 0 (by omega))
    (C.mem 1 (by omega)) (C.mem m le_rfl) hc with h | h | h | h | h | h <;>
    have := congrArg Prod.fst h <;> simp only at this
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · exact hne (congrArg Prod.snd h).symm

/-- A chain that is a single segment from the apex to a far end at the apex's depth keeps the
whole face on its side of that depth. -/
theorem ChainOKc.le_of_one {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOKc Q z0 s m ca cz) (hm : m = 1) (h : cz m = z0) :
    ∀ a z, Q a z → s * z ≤ s * z0 := by
  subst hm
  intro a z hq
  by_cases e0 : a = ca 0 ∧ z = cz 0
  · rw [e0.2, C.start.2]
  by_cases e1 : a = ca 1 ∧ z = cz 1
  · rw [e1.2, h]
  have hs := C.side a z hq 0 (by omega) (by simpa using e0) (by simpa using e1)
  have hd : 0 < ca (0 + 1) - ca 0 := sub_pos.mpr (C.inc 0 (by omega))
  have hz0 := C.start.2
  have h1 : cz (0 + 1) = z0 := h
  have e : s * ((ca (0 + 1) - ca 0) * (z - cz 0) - (cz (0 + 1) - cz 0) * (a - ca 0)) =
      (ca (0 + 1) - ca 0) * (s * z - s * z0) := by rw [h1, hz0]; ring
  rw [e] at hs
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos hd (sub_pos.mpr hcon)]

/-- **In a face with at most four points one of the two chains is a single segment.**  The upper
chain `U` (ending at the top `P` of the far vertical) and the lower chain `L` of a face with a
second point `c` below `P` on the far vertical: if both had a middle, the apex, the first
vertices of both chains, `P` and `c` would be five distinct points (if the first vertices
agreed, `P` below and `c` above the line from the apex through them would contradict `c < P`). -/
theorem ChainOKc.one_of_atMost4 {Q : ℝ → ℝ → Prop} {z0 : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ}
    (U : ChainOKc Q z0 1 m ca cz) (L : ChainOKc Q z0 (-1) m' ca' cz') (h4 : AtMost4 Q) {c : ℝ}
    (hc : Q (ca m) c) (hlt : c < cz m) : m = 1 ∨ m' = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hm, hm'⟩ := hcon
  have hm2 : 2 ≤ m := by have := U.one_le; omega
  have hm2' : 2 ≤ m' := by have := L.one_le; omega
  have ea := U.far_a_eq L
  have u0 := U.start
  have l0 := L.start
  have a1 := U.mono 0 1 (by omega) (by omega)
  have a1m := U.mono 1 m (by omega) le_rfl
  have b1 := L.mono 0 1 (by omega) (by omega)
  have b1m := L.mono 1 m' (by omega) le_rfl
  rcases h4 (ca 0, cz 0) (ca 1, cz 1) (ca m, cz m) (ca' 1, cz' 1) (ca m, c)
    (U.mem 0 (Nat.zero_le _)) (U.mem 1 (by omega)) (U.mem m le_rfl) (L.mem 1 (by omega)) hc with
    h | h | h | h | h | h | h | h | h | h <;>
    have h1 := congrArg Prod.fst h <;> simp only at h1
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · -- the first vertices of both chains agree
    have h2 := congrArg Prod.snd h
    simp only at h2
    have sU := U.side (ca m) (cz m) (U.mem m le_rfl) 0 (by omega) (fun h => by linarith [h.1])
      (fun h => by linarith [h.1])
    have sL := L.side (ca m) c hc 0 (by omega) (fun h => by linarith [h.1])
      (fun h => by linarith [h.1])
    rw [← h1, ← h2] at sL
    rw [u0.1, u0.2] at sU
    rw [l0.1, l0.2] at sL
    nlinarith [mul_pos (show 0 < ca 1 by linarith) (sub_pos.mpr hlt)]
  · linarith
  · linarith
  · have h2 := congrArg Prod.snd h
    simp only at h2
    linarith
  · linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, far companions allowed, from chains, with no unique-far-end
condition** (FEWER-FACES-PROOFS.md Proposition 24.12 and Proposition 23.19 (1)–(3)).  As
`isRupert_vertex_frame_par` without `hone`, provided at most two points of a face lie on a
vertical (`hcard`) and the far depths of the faces do not tie, except that a tie is allowed when
exactly one face has a vertical far edge (`hsep`; Proposition 23.19 (1): the far edge then
decides the sector, whatever the tied depth).  When both faces have a vertical far edge, the
four tilts are chosen by the depths: if the tops differ, `s = 1` with the second face's top as
middle vertex when it lies below the first face's top, else `s = -1` with the first face's top
as middle vertex; if the tops tie, the same with the bottoms (`s = 1`, the first face's bottom
as middle vertex, when the second face's bottom is lower; else `s = -1`, the second face's
bottom).  The full rectangle (tops and bottoms both tied) is excluded (Proposition 23.19, last
bullet; `hsep`'s fourth alternative) unless one face has at most three points (`TRI`,
`AtMost3`): its chains have no middle (`ChainOKc.m_eq_one`), so its far end, or the apex when it
is above the face, is the strict top or bottom, and the cycle with the middle vertex tied with a
far end, read as part of the chain of the triangle (`vertex_core_mid`, with
`isRupert_triShadow_midP` or the second form of `isRupert_triShadow_mid`), is unimodal whatever
the tie-break (Proposition 24.12). -/
theorem isRupert_vertex_frame_par' (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ}
    (hU1 : ∃ m ca cz, ChainOKc Q1 z0 1 m ca cz) (hL1 : ∃ m ca cz, ChainOKc Q1 z0 (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOKc Q2 z0 1 m ca cz) (hL2 : ∃ m ca cz, ChainOKc Q2 z0 (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (hcard1 : ∀ a z1 z2 z3, Q1 a z1 → Q1 a z2 → Q1 a z3 → z1 = z2 ∨ z1 = z3 ∨ z2 = z3)
    (hcard2 : ∀ a z1 z2 z3, Q2 a z1 → Q2 a z2 → Q2 a z3 → z1 = z2 ∨ z1 = z3 ∨ z2 = z3)
    {TRI : Prop} (hTRI : TRI → AtMost3 Q1 ∨ AtMost3 Q2 ∨ (AtMost4 Q1 ∧ AtMost4 Q2 ∧
      (∀ m ca cz, ChainOKc Q1 z0 1 m ca cz → cz m = z0 →
        ∃ a z, (Q1 a z ∨ Q2 a z) ∧ z0 < z) ∧
      (∀ m ca cz, ChainOKc Q1 z0 (-1) m ca cz → cz m = z0 →
        ∃ a z, (Q1 a z ∨ Q2 a z) ∧ z < z0)))
    (hsep : ∀ m ca cz m' ca' cz' n cb dz n' cb' dz', ChainOKc Q1 z0 1 m ca cz →
      ChainOKc Q1 z0 (-1) m' ca' cz' → ChainOKc Q2 z0 1 n cb dz → ChainOKc Q2 z0 (-1) n' cb' dz' →
      (cz m ≠ dz n ∧ cz m ≠ dz' n') ∨ (cz' m' < cz m ∧ dz' n' = dz n) ∨
        (cz' m' = cz m ∧ dz' n' < dz n) ∨
        (cz' m' < cz m ∧ dz' n' < dz n ∧ (cz m ≠ dz n ∨ cz' m' ≠ dz' n' ∨ TRI)))
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOKc Q1 z0 1 m ca cz → ChainOKc Q2 z0 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  by_cases hone : (∀ m ca cz, ChainOKc Q1 z0 1 m ca cz → ∀ z, Q1 (ca m) z → z = cz m) ∨
      (∀ n cb dz, ChainOKc Q2 z0 1 n cb dz → ∀ z, Q2 (cb n) z → z = dz n)
  · refine isRupert_vertex_frame_par O r1 r2 hρ Q1 Q2 hU1 hL1 hU2 hL2 hap1 hap2 hpos1 hpos2 hone
      ?_ V hV1 hV2 hVc
    intro m ca cz m' ca' cz' n cb dz n' cb' dz' U1 L1 U2 L2
    exact hfar_of_sep (U1.low_le_up L1) (U2.low_le_up L2)
      (hsep m ca cz m' ca' cz' n cb dz n' cb' dz' U1 L1 U2 L2)
  push Not at hone
  obtain ⟨⟨m0, ca0, cz0, U1, c1, hc1, hne1⟩, ⟨n0, cb0, dz0, U2, c2, hc2, hne2⟩⟩ := hone
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  obtain ⟨ea1, eb1, hlt1, hv1⟩ := U1.two_ends L1 hcard1 hc1 hne1
  obtain ⟨ea2, eb2, hlt2, hv2⟩ := U2.two_ends L2 hcard2 hc2 hne2
  have hc : cz0 m0 < dz0 n0 ∨ dz0 n0 < cz0 m0 ∨ dz1 n1 < cz1 m1 ∨ cz1 m1 < dz1 n1 ∨
      (cz0 m0 = dz0 n0 ∧ cz1 m1 = dz1 n1 ∧ TRI) := by
    rcases hsep m0 ca0 cz0 m1 ca1 cz1 n0 cb0 dz0 n1 cb1 dz1 U1 L1 U2 L2 with h | h | h | h
    · rcases lt_or_gt_of_ne h.1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exfalso; linarith [h.2, eb2, hlt2]
    · exfalso; linarith [h.1, eb1, hlt1]
    · by_cases t1 : cz0 m0 = dz0 n0
      · by_cases t2 : cz1 m1 = dz1 n1
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨t1, t2, ?_⟩)))
          rcases h.2.2 with h' | h' | h'
          · exact absurd t1 h'
          · exact absurd t2 h'
          · exact h'
        · rcases lt_or_gt_of_ne t2 with h'' | h''
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
          · exact Or.inr (Or.inr (Or.inl h''))
      · rcases lt_or_gt_of_ne t1 with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (Or.inl h'')
  rcases hc with h | h | h | h | ⟨hr1, hr2, hT⟩
  · -- the first face's top is below the second's: `s = -1`, the middle vertex the first top
    have hA0 := L1.far_pos
    have hB0 := U2.far_pos
    refine vertex_core_tail1 O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) L1 (by simpa using U2)
      (α := 1) (β := 2 * cb0 n0 / ca1 m1) one_pos (by positivity) ?_ (zT := cz0 m0)
      (by rw [ea1]; exact U1.mem m0 le_rfl) ?_ (by rw [eb1]; linarith)
      (Or.inl (by linarith)) hap1 hap2
      hpos1 hpos2 V hV1 hV2 ?_
    · rw [mul_div_assoc', mul_comm (cb0 n0) 1, one_mul, mul_comm (ca1 m1) (2 * cb0 n0),
        mul_div_assoc, div_self hA0.ne']
      linarith
    · intro z hz
      rw [ea1] at hz
      rcases hv1 z hz with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [eb1]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea1]; exact this
  · -- the first face's top is above the second's: `s = 1`, the middle vertex the second top
    have hA0 := U1.far_pos
    have hB0 := L2.far_pos
    refine vertex_core_tail2 O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) U1 (by simpa using L2)
      (α := 2 * ca0 m0 / cb1 n1) (β := 1) (by positivity) one_pos ?_ (zT := dz0 n0)
      (by rw [ea2]; exact U2.mem n0 le_rfl) ?_ (Or.inl (by linarith))
      (by rw [eb2]; linarith) hap1 hap2
      hpos1 hpos2 V hV1 hV2 ?_
    · rw [mul_div_assoc', mul_one, mul_comm (cb1 n1) (2 * ca0 m0), mul_div_assoc,
        div_self hB0.ne']
      linarith
    · intro z hz
      rw [ea2] at hz
      rcases hv2 z hz with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [eb2]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea2]; exact this
  · -- tops may tie, the second face's bottom is below the first's: `s = 1`, the middle vertex
    -- the first face's bottom
    have hA0 := U1.far_pos
    have hB0 := L2.far_pos
    refine vertex_core_tail1 O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) U1 (by simpa using L2)
      (α := 1) (β := 2 * cb1 n1 / ca0 m0) one_pos (by positivity) ?_ (zT := cz1 m1)
      (by rw [← ea1]; exact L1.mem m1 le_rfl) ?_ (by rw [eb1]; linarith)
      (Or.inl (by linarith)) hap1 hap2
      hpos1 hpos2 V hV1 hV2 ?_
    · rw [mul_div_assoc', mul_comm (cb1 n1) 1, one_mul, mul_comm (ca0 m0) (2 * cb1 n1),
        mul_div_assoc, div_self hA0.ne']
      linarith
    · intro z hz
      rcases hv1 z hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [eb1]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea2]; exact this
  · -- bottoms: the first face's bottom is below the second's: `s = -1`, the middle vertex the
    -- second face's bottom
    have hA0 := L1.far_pos
    have hB0 := U2.far_pos
    refine vertex_core_tail2 O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) L1 (by simpa using U2)
      (α := 2 * ca1 m1 / cb0 n0) (β := 1) (by positivity) one_pos ?_ (zT := dz1 n1)
      (by rw [← ea2]; exact L2.mem n1 le_rfl) ?_ (Or.inl (by linarith))
      (by rw [eb2]; linarith) hap1 hap2
      hpos1 hpos2 V hV1 hV2 ?_
    · rw [mul_div_assoc', mul_one, mul_comm (cb0 n0) (2 * ca1 m1), mul_div_assoc,
        div_self hB0.ne']
      linarith
    · intro z hz
      rcases hv2 z hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [eb2]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea1]; exact this

  · -- the rectangle (tops tied, bottoms tied): Proposition 24.12.  Four mixed sectors, each
    -- needing the last step of one chain to rise or fall suitably; if all four fail, the
    -- non-mixed arcs `(−, +, −)`, `(+, −, +)` (`vertex_core_nm`).
    have sec1 : cz0 (m0 - 1) < cz0 m0 → IsRupert V := fun hR => by
      -- `s = 1`, the middle vertex the second face's top, `P` above its chain predecessor
      have hA0 := U1.far_pos
      have hB0 := L2.far_pos
      refine vertex_core_tail2 O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) U1 (by simpa using L2)
        (α := 2 * ca0 m0 / cb1 n1) (β := 1) (by positivity) one_pos ?_ (zT := dz0 n0)
        (by rw [ea2]; exact U2.mem n0 le_rfl) ?_ (Or.inr ?_) (by rw [eb2]; linarith) hap1 hap2
        hpos1 hpos2 V hV1 hV2 ?_
      · rw [mul_div_assoc', mul_one, mul_comm (cb1 n1) (2 * ca0 m0), mul_div_assoc,
          div_self hB0.ne']
        linarith
      · intro z hz
        rw [ea2] at hz
        rcases hv2 z hz with h' | h'
        · exact Or.inr h'
        · exact Or.inl (by rw [eb2]; exact h')
      · linarith
      · intro y hy
        obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
        refine ⟨a, b, z, rfl, ?_⟩
        rcases hc with h' | h' | ⟨ha, hb, hin⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · right; right; refine ⟨ha, hb, ?_⟩
          have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
          rw [ea2]; exact this
    have sec4 : cz1 m1 < cz1 (m1 - 1) → IsRupert V := fun hR => by
      -- `s = -1`, the middle vertex the second face's bottom, `P` below its chain predecessor
      have hA0 := L1.far_pos
      have hB0 := U2.far_pos
      refine vertex_core_tail2 O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) L1 (by simpa using U2)
        (α := 2 * ca1 m1 / cb0 n0) (β := 1) (by positivity) one_pos ?_ (zT := dz1 n1)
        (by rw [← ea2]; exact L2.mem n1 le_rfl) ?_ (Or.inr ?_) (by rw [eb2]; linarith) hap1 hap2
        hpos1 hpos2 V hV1 hV2 ?_
      · rw [mul_div_assoc', mul_one, mul_comm (cb0 n0) (2 * ca1 m1), mul_div_assoc,
          div_self hB0.ne']
        linarith
      · intro z hz
        rcases hv2 z hz with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [eb2]; exact h')
      · linarith
      · intro y hy
        obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
        refine ⟨a, b, z, rfl, ?_⟩
        rcases hc with h' | h' | ⟨ha, hb, hin⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · right; right; refine ⟨ha, hb, ?_⟩
          have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
          rw [ea1]; exact this
    have sec2 : dz1 n1 < dz1 (n1 - 1) → IsRupert V := fun hR => by
      -- `s = 1`, the middle vertex the first face's bottom, `Q` below its chain predecessor
      have hA0 := U1.far_pos
      have hB0 := L2.far_pos
      refine vertex_core_tail1 O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) U1 (by simpa using L2)
        (α := 1) (β := 2 * cb1 n1 / ca0 m0) one_pos (by positivity) ?_ (zT := cz1 m1)
        (by rw [← ea1]; exact L1.mem m1 le_rfl) ?_ (by rw [eb1]; linarith) (Or.inr ?_) hap1 hap2
        hpos1 hpos2 V hV1 hV2 ?_
      · rw [mul_div_assoc', mul_comm (cb1 n1) 1, one_mul, mul_comm (ca0 m0) (2 * cb1 n1),
          mul_div_assoc, div_self hA0.ne']
        linarith
      · intro z hz
        rcases hv1 z hz with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [eb1]; exact h')
      · linarith
      · intro y hy
        obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
        refine ⟨a, b, z, rfl, ?_⟩
        rcases hc with h' | h' | ⟨ha, hb, hin⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · right; right; refine ⟨ha, hb, ?_⟩
          have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
          rw [ea2]; exact this
    have sec3 : dz0 (n0 - 1) < dz0 n0 → IsRupert V := fun hR => by
      -- `s = -1`, the middle vertex the first face's top, `Q` above its chain predecessor
      have hA0 := L1.far_pos
      have hB0 := U2.far_pos
      refine vertex_core_tail1 O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) L1 (by simpa using U2)
        (α := 1) (β := 2 * cb0 n0 / ca1 m1) one_pos (by positivity) ?_ (zT := cz0 m0)
        (by rw [ea1]; exact U1.mem m0 le_rfl) ?_ (by rw [eb1]; linarith) (Or.inr ?_) hap1 hap2
        hpos1 hpos2 V hV1 hV2 ?_
      · rw [mul_div_assoc', mul_comm (cb0 n0) 1, one_mul, mul_comm (ca1 m1) (2 * cb0 n0),
          mul_div_assoc, div_self hA0.ne']
        linarith
      · intro z hz
        rw [ea1] at hz
        rcases hv1 z hz with h' | h'
        · exact Or.inr h'
        · exact Or.inl (by rw [eb1]; exact h')
      · linarith
      · intro y hy
        obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
        refine ⟨a, b, z, rfl, ?_⟩
        rcases hc with h' | h' | ⟨ha, hb, hin⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · right; right; refine ⟨ha, hb, ?_⟩
          have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
          rw [ea1]; exact this
    rcases hTRI hT with h3 | h3 | ⟨h4a, h4b, hvT, hvB⟩
    · -- the first face is a triangle: its chains have no middle
      have hm0 : m0 = 1 := U1.m_eq_one h3 hc1 hne1
      have hm1 : m1 = 1 := L1.m_eq_one h3 (c := cz0 m0) (by rw [ea1]; exact U1.mem m0 le_rfl)
        (by rw [eb1]; exact hlt1.ne')
      have hp0 : cz0 (m0 - 1) = z0 := by rw [hm0]; exact U1.start.2
      have hp1 : cz1 (m1 - 1) = z0 := by rw [hm1]; exact L1.start.2
      by_cases hz : z0 < cz0 m0
      · exact sec1 (by rw [hp0]; exact hz)
      · exact sec4 (by rw [hp1]; linarith [not_lt.mp hz])
    · -- the second face is a triangle
      have hn0 : n0 = 1 := U2.m_eq_one h3 hc2 hne2
      have hn1 : n1 = 1 := L2.m_eq_one h3 (c := dz0 n0) (by rw [ea2]; exact U2.mem n0 le_rfl)
        (by rw [eb2]; exact hlt2.ne')
      have hq0 : dz0 (n0 - 1) = z0 := by rw [hn0]; exact U2.start.2
      have hq1 : dz1 (n1 - 1) = z0 := by rw [hn1]; exact L2.start.2
      by_cases hz : dz1 n1 < z0
      · exact sec2 (by rw [hq1]; exact hz)
      · exact sec3 (by rw [hq0]; linarith [not_lt.mp hz])
    · -- two faces with at most four points: when the four mixed sectors fail, one of the two
      -- non-mixed arcs works unless the apex ties with a far end (`hvT`, `hvB`)
      by_cases R1 : cz0 (m0 - 1) < cz0 m0
      · exact sec1 R1
      by_cases R4 : cz1 m1 < cz1 (m1 - 1)
      · exact sec4 R4
      by_cases R2 : dz1 n1 < dz1 (n1 - 1)
      · exact sec2 R2
      by_cases R3 : dz0 (n0 - 1) < dz0 n0
      · exact sec3 R3
      rw [not_lt] at R1 R2 R3 R4
      have hm01 := U1.one_of_atMost4 L1 h4a hc1 hlt1
      have hn01 := U2.one_of_atMost4 L2 h4b hc2 hlt2
      have hVc' : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
          ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
            a * cb0 n0 + b * ca0 m0 < ca0 m0 * cb0 n0)) := by
        intro y hy
        obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
        refine ⟨a, b, z, rfl, ?_⟩
        rcases hc with h' | h' | ⟨ha, hb, hin⟩
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr ⟨ha, hb, hin m0 ca0 cz0 n0 cb0 dz0 U1 U2⟩)
      rcases hm01 with hm0 | hm1 <;> rcases hn01 with hn0 | hn1
      · -- both upper chains single segments, `v` above the tops: the arc `(−, +, −)`
        have hp0 : cz0 (m0 - 1) = z0 := by rw [hm0]; exact U1.start.2
        have e1 : cz0 1 = cz0 m0 := by rw [hm0]
        have hzT : z0 ≠ cz0 m0 := fun e => by
          obtain ⟨a, z, hz, hlt⟩ := hvT m0 ca0 cz0 U1 e.symm
          rcases hz with hz | hz
          · have := U1.le_of_one hm0 e.symm a z hz; linarith
          · have := U2.le_of_one hn0 (by rw [← hr1]; exact e.symm) a z hz; linarith
        have hlt : cz0 m0 < z0 := lt_of_le_of_ne (by rw [← hp0]; exact R1) (Ne.symm hzT)
        refine vertex_core_nm O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) U1 U2 hc1 hne1 hv1 hc2 hne2 hv2
          (Or.inl (by linarith)) hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc'
      · -- `R1` and `R2` contradict the tie of the bottoms
        have hp0 : cz0 (m0 - 1) = z0 := by rw [hm0]; exact U1.start.2
        have hq1 : dz1 (n1 - 1) = z0 := by rw [hn1]; exact L2.start.2
        exfalso
        rw [hp0] at R1
        rw [hq1] at R2
        linarith
      · -- `R4` and `R3` contradict the tie of the tops
        have hp1 : cz1 (m1 - 1) = z0 := by rw [hm1]; exact L1.start.2
        have hq0 : dz0 (n0 - 1) = z0 := by rw [hn0]; exact U2.start.2
        exfalso
        rw [hp1] at R4
        rw [hq0] at R3
        linarith
      · -- both lower chains single segments, `v` below the bottoms: the arc `(+, −, +)`
        have hp1 : cz1 (m1 - 1) = z0 := by rw [hm1]; exact L1.start.2
        have e1 : cz1 1 = cz1 m1 := by rw [hm1]
        have hzB : z0 ≠ cz1 m1 := fun e => by
          obtain ⟨a, z, hz, hlt⟩ := hvB m1 ca1 cz1 L1 e.symm
          rcases hz with hz | hz
          · have := L1.le_of_one hm1 e.symm a z hz; linarith
          · have := L2.le_of_one hn1 (by rw [← hr2]; exact e.symm) a z hz; linarith
        have hlt : z0 < cz1 m1 := lt_of_le_of_ne (by rw [← hp1]; exact R4) hzB
        have hVc'' : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
            ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
              a * cb1 n1 + b * ca1 m1 < ca1 m1 * cb1 n1)) := by
          intro y hy
          obtain ⟨a, b, z, rfl, hc⟩ := hVc' y hy
          refine ⟨a, b, z, rfl, ?_⟩
          rcases hc with h' | h' | ⟨ha, hb, hin⟩
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr ⟨ha, hb, by rw [ea1, ea2]; exact hin⟩)
        refine vertex_core_nm O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) L1 L2
          (zM1 := cz0 m0) (zM2 := dz0 n0) (by rw [ea1]; exact U1.mem m0 le_rfl)
          (by rw [eb1]; exact hlt1.ne')
          (fun z hz => by
            rw [ea1] at hz
            rcases hv1 z hz with h' | h'
            · exact Or.inr h'
            · exact Or.inl (by rw [eb1]; exact h'))
          (by rw [ea2]; exact U2.mem n0 le_rfl) (by rw [eb2]; exact hlt2.ne')
          (fun z hz => by
            rw [ea2] at hz
            rcases hv2 z hz with h' | h'
            · exact Or.inr h'
            · exact Or.inl (by rw [eb2]; exact h'))
          (Or.inl (by linarith)) hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc''

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, far companions allowed, from chains, with no unique-far-end
condition** (as `isRupert_vertex_frame_par'`; upper chains start at the top apex vertex, lower
chains at the bottom one). -/
theorem isRupert_edge_frame_par' (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {zx zx' : ℝ} (hxx : zx < zx')
    (hU1 : ∃ m ca cz, ChainOKc Q1 zx' 1 m ca cz) (hL1 : ∃ m ca cz, ChainOKc Q1 zx (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOKc Q2 zx' 1 m ca cz) (hL2 : ∃ m ca cz, ChainOKc Q2 zx (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = zx ∨ z = zx') (hap2 : ∀ z, Q2 0 z → z = zx ∨ z = zx')
    (hQ1x : Q1 0 zx) (hQ1x' : Q1 0 zx') (hQ2x : Q2 0 zx) (hQ2x' : Q2 0 zx')
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (hcard1 : ∀ a z1 z2 z3, Q1 a z1 → Q1 a z2 → Q1 a z3 → z1 = z2 ∨ z1 = z3 ∨ z2 = z3)
    (hcard2 : ∀ a z1 z2 z3, Q2 a z1 → Q2 a z2 → Q2 a z3 → z1 = z2 ∨ z1 = z3 ∨ z2 = z3)
    (hsep : ∀ m ca cz m' ca' cz' n cb dz n' cb' dz', ChainOKc Q1 zx' 1 m ca cz →
      ChainOKc Q1 zx (-1) m' ca' cz' → ChainOKc Q2 zx' 1 n cb dz → ChainOKc Q2 zx (-1) n' cb' dz' →
      (cz m ≠ dz n ∧ cz m ≠ dz' n') ∨ (cz' m' < cz m ∧ dz' n' = dz n) ∨
        (cz' m' = cz m ∧ dz' n' < dz n) ∨
        (cz' m' < cz m ∧ dz' n' < dz n ∧ (cz m ≠ dz n ∨ cz' m' ≠ dz' n')))
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOKc Q1 zx' 1 m ca cz → ChainOKc Q2 zx' 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  by_cases hone : (∀ m ca cz, ChainOKc Q1 zx' 1 m ca cz → ∀ z, Q1 (ca m) z → z = cz m) ∨
      (∀ n cb dz, ChainOKc Q2 zx' 1 n cb dz → ∀ z, Q2 (cb n) z → z = dz n)
  · refine isRupert_edge_frame_par O r1 r2 hρ Q1 Q2 hxx hU1 hL1 hU2 hL2 hap1 hap2 hQ1x hQ1x'
      hQ2x hQ2x' hpos1 hpos2 hone ?_ V hV1 hV2 hVc
    intro m ca cz m' ca' cz' n cb dz n' cb' dz' U1 L1 U2 L2
    exact hfar_of_sep (U1.low_le_up L1) (U2.low_le_up L2)
      (hsep m ca cz m' ca' cz' n cb dz n' cb' dz' U1 L1 U2 L2)
  push Not at hone
  obtain ⟨⟨m0, ca0, cz0, U1, c1, hc1, hne1⟩, ⟨n0, cb0, dz0, U2, c2, hc2, hne2⟩⟩ := hone
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  obtain ⟨ea1, eb1, hlt1, hv1⟩ := U1.two_ends L1 hcard1 hc1 hne1
  obtain ⟨ea2, eb2, hlt2, hv2⟩ := U2.two_ends L2 hcard2 hc2 hne2
  have hc : cz0 m0 < dz0 n0 ∨ dz0 n0 < cz0 m0 ∨ dz1 n1 < cz1 m1 ∨ cz1 m1 < dz1 n1 := by
    rcases hsep m0 ca0 cz0 m1 ca1 cz1 n0 cb0 dz0 n1 cb1 dz1 U1 L1 U2 L2 with h | h | h | h
    · rcases lt_or_gt_of_ne h.1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exfalso; linarith [h.2, eb2, hlt2]
    · exfalso; linarith [h.1, eb1, hlt1]
    · rcases h.2.2 with h' | h'
      · rcases lt_or_gt_of_ne h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (Or.inl h'')
      · rcases lt_or_gt_of_ne h' with h'' | h''
        · exact Or.inr (Or.inr (Or.inr h''))
        · exact Or.inr (Or.inr (Or.inl h''))
  rcases hc with h | h | h | h
  · have hA0 := L1.far_pos
    have hB0 := U2.far_pos
    refine edge_core_tail1 O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) (by linarith) L1 (by simpa using U2)
      (α := 1) (β := 2 * cb0 n0 / ca1 m1) one_pos (by positivity) ?_ (zT := cz0 m0)
      (by rw [ea1]; exact U1.mem m0 le_rfl) ?_ (by rw [eb1]; linarith) (by linarith) hap1 hap2
      hQ1x' hQ2x hpos1 hpos2 V hV1 hV2 ?_
    · rw [mul_div_assoc', mul_comm (cb0 n0) 1, one_mul, mul_comm (ca1 m1) (2 * cb0 n0),
        mul_div_assoc, div_self hA0.ne']
      linarith
    · intro z hz
      rw [ea1] at hz
      rcases hv1 z hz with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [eb1]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea1]; exact this
  · have hA0 := U1.far_pos
    have hB0 := L2.far_pos
    refine edge_core_tail2 O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) (by linarith) U1 (by simpa using L2)
      (α := 2 * ca0 m0 / cb1 n1) (β := 1) (by positivity) one_pos ?_ (zT := dz0 n0)
      (by rw [ea2]; exact U2.mem n0 le_rfl) ?_ (by linarith) (by rw [eb2]; linarith)
      (fun z hz => (hap1 z hz).symm) (fun z hz => (hap2 z hz).symm) hQ1x hQ2x' hpos1 hpos2 V hV1
      hV2 ?_
    · rw [mul_div_assoc', mul_one, mul_comm (cb1 n1) (2 * ca0 m0), mul_div_assoc,
        div_self hB0.ne']
      linarith
    · intro z hz
      rw [ea2] at hz
      rcases hv2 z hz with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [eb2]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea2]; exact this
  · have hA0 := U1.far_pos
    have hB0 := L2.far_pos
    refine edge_core_tail1 O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) (by linarith) U1 (by simpa using L2)
      (α := 1) (β := 2 * cb1 n1 / ca0 m0) one_pos (by positivity) ?_ (zT := cz1 m1)
      (by rw [← ea1]; exact L1.mem m1 le_rfl) ?_ (by rw [eb1]; linarith) (by linarith)
      (fun z hz => (hap1 z hz).symm) (fun z hz => (hap2 z hz).symm) hQ1x hQ2x' hpos1 hpos2 V hV1
      hV2 ?_
    · rw [mul_div_assoc', mul_comm (cb1 n1) 1, one_mul, mul_comm (ca0 m0) (2 * cb1 n1),
        mul_div_assoc, div_self hA0.ne']
      linarith
    · intro z hz
      rcases hv1 z hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [eb1]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea2]; exact this
  · have hA0 := L1.far_pos
    have hB0 := U2.far_pos
    refine edge_core_tail2 O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) (by linarith) L1 (by simpa using U2)
      (α := 2 * ca1 m1 / cb0 n0) (β := 1) (by positivity) one_pos ?_ (zT := dz1 n1)
      (by rw [← ea2]; exact L2.mem n1 le_rfl) ?_ (by linarith) (by rw [eb2]; linarith) hap1 hap2
      hQ1x' hQ2x hpos1 hpos2 V hV1 hV2 ?_
    · rw [mul_div_assoc', mul_one, mul_comm (cb0 n0) (2 * ca1 m1), mul_div_assoc,
        div_self hB0.ne']
      linarith
    · intro z hz
      rcases hv2 z hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [eb2]; exact h')
    · intro y hy
      obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h' | h' | ⟨ha, hb, hin⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · right; right; refine ⟨ha, hb, ?_⟩
        have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
        rw [ea1]; exact this

end Minimality

end
