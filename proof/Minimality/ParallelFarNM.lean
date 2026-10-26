module

public import Minimality.ParallelFar
public import Minimality.TriShadowNM

@[expose] public section

/-!
# The non-mixed tilt arcs from chains (both faces with a vertical far edge)

FEWER-FACES-PROOFS.md Proposition 24.12, arcs `(−, +, −)` and `(+, −, +)`.  The frame theorem
`isRupert_triShadow_nm` for chains `ChainOKc` of both faces with the same sign `s`, the far
vertical of each face carrying exactly two points, the apex strictly above one of its two chain
neighbours (`s z_apex > s z_{C1 1}` or `> s z_{C2 1}`).  The tests of the three far-side edges
are independent of the tilt ratio.
-/

namespace Minimality

/-- Every point of the face lies at `a ≤ ca m`. -/
theorem ChainOKc.a_le {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOKc Q z0 s m ca cz) {a z : ℝ} (h : Q a z) : a ≤ ca m := by
  by_cases e : a = ca m ∧ z = cz m
  · exact e.1.le
  rcases C.far a z h e with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- The `a`-coordinates along a chain increase. -/
theorem ChainOKc.mono {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOKc Q z0 s m ca cz) : ∀ i j, i < j → j ≤ m → ca i < ca j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact lt_trans (ih h (by omega)) (C.inc j (by omega))
    · subst h; exact C.inc i (by omega)

/-- The vertical cycle edge `P → M1` over the first far end `A`: every point of the shadow
triangle off that vertical passes the test, whatever the tilt ratio. -/
theorem tiltOK_nm_vert1 {s α β A zP zM a b z : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hPM : s * zM < s * zP) (ha : a ≤ A) (hb : 0 ≤ b) (hne : a < A ∨ 0 < b) :
    TiltOK A 0 zP A 0 zM a b z (s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have hX : (a - A) * β - b * α < 0 := by
    rcases hne with h | h
    · nlinarith [mul_pos (sub_pos.mpr h) hβ, mul_nonneg hb hα.le]
    · nlinarith [mul_pos h hα, mul_nonneg (sub_nonneg.mpr ha) hβ.le]
  have h := mul_pos_of_neg_of_neg (show s * (zM - zP) < 0 by linarith) hX
  nlinarith [h]

/-- The vertical cycle edge `M2 → Q` over the second far end `B`. -/
theorem tiltOK_nm_vert2 {s α β B zM zQ a b z : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hMQ : s * zM < s * zQ) (ha : 0 ≤ a) (hb : b ≤ B) (hne : 0 < a ∨ b < B) :
    TiltOK 0 B zM 0 B zQ a b z (s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have hX : 0 < a * β + (B - b) * α := by
    rcases hne with h | h
    · nlinarith [mul_pos h hβ, mul_nonneg (sub_nonneg.mpr hb) hα.le]
    · nlinarith [mul_pos (sub_pos.mpr h) hα, mul_nonneg ha hβ.le]
  have h := mul_pos (show 0 < s * (zQ - zM) by linarith) hX
  nlinarith [h]

/-- The chord `M1 → M2` (the level edge) against the first far end `P` over `A`. -/
theorem tiltOK_nm_chordP {s α β A B zM1 zM2 zP : ℝ} (hα : 0 < α) (hβ : 0 < β) (hA : 0 < A)
    (hB : 0 < B) (hPM : s * zM1 < s * zP) :
    TiltOK A 0 zM1 0 B zM2 A 0 zP (s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have h := mul_pos (show 0 < s * (zP - zM1) by linarith)
    (show 0 < A * β + B * α by positivity)
  nlinarith [h]

/-- The chord `M1 → M2` against the second far end `Q` over `B`. -/
theorem tiltOK_nm_chordQ {s α β A B zM1 zM2 zQ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hA : 0 < A)
    (hB : 0 < B) (hQM : s * zM2 < s * zQ) :
    TiltOK A 0 zM1 0 B zM2 0 B zQ (s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have h := mul_pos (show 0 < s * (zQ - zM2) by linarith)
    (show 0 < A * β + B * α by positivity)
  nlinarith [h]


set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, the non-mixed arcs, from chains** (Proposition 24.12, the arcs
`(−, +, −)` for `s = 1` and `(+, −, +)` for `s = -1`): both faces with a vertical far edge carrying
exactly two points of the face (`hcard1`, `hcard2`), the tilt `s (r1 + r2)`, and the apex strictly
above one of its two chain neighbours (`hapex`, in the sense of `s z`). -/
theorem vertex_core_nm (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ} (s : ℝ) (hs : s = 1 ∨ s = -1) {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z0 s m ca cz) (C2 : ChainOKc Q2 z0 s n cb dz)
    {zM1 zM2 : ℝ} (hM1 : Q1 (ca m) zM1) (hM1ne : zM1 ≠ cz m)
    (hcard1 : ∀ z, Q1 (ca m) z → z = cz m ∨ z = zM1)
    (hM2 : Q2 (cb n) zM2) (hM2ne : zM2 ≠ dz n)
    (hcard2 : ∀ z, Q2 (cb n) z → z = dz n ∨ z = zM2)
    (hapex : s * cz 1 < s * z0 ∨ s * dz 1 < s * z0)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have hPM : s * zM1 < s * cz m := by
    rcases C1.far (ca m) zM1 hM1 (fun h => hM1ne h.2) with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · linarith
  have hQM : s * zM2 < s * dz n := by
    rcases C2.far (cb n) zM2 hM2 (fun h => hM2ne h.2) with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · linarith
  have q20 : Q2 0 z0 := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
  have q10 : Q1 0 z0 := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) < 0 := by
    intro b z hq l hl h1 h2
    exact C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
  have hα : (0 : ℝ) < 1 := one_pos
  -- the three far-side tests for points of the first face
  have t1 : ∀ a z, Q1 a z →
      (TiltOK (ca m) 0 (cz m) (ca m) 0 zM1 a 0 z (s * 1) (s * 1) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 (cz m) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 zM1) ∧
      (TiltOK (ca m) 0 zM1 0 (cb n) zM2 a 0 z (s * 1) (s * 1) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 zM1 ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 0 (cb n) zM2) ∧
      (TiltOK 0 (cb n) zM2 0 (cb n) (dz n) a 0 z (s * 1) (s * 1) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 0 (cb n) zM2 ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 0 (cb n) (dz n)) := by
    intro a z hq
    have hale := C1.a_le hq
    have h3 : TiltOK 0 (cb n) zM2 0 (cb n) (dz n) a 0 z (s * 1) (s * 1) :=
      tiltOK_nm_vert2 hα hα hQM (hpos1 a z hq) hB0.le (Or.inr hB0)
    rcases hale.lt_or_eq with hlt | rfl
    · exact ⟨Or.inl (tiltOK_nm_vert1 hα hα hPM hlt.le le_rfl (Or.inl hlt)),
        Or.inl (far_tiltOK (by nlinarith)), Or.inl h3⟩
    · rcases hcard1 z hq with rfl | rfl
      · exact ⟨Or.inr (Or.inl rfl), Or.inl (tiltOK_nm_chordP hα hα hA0 hB0 hPM), Or.inl h3⟩
      · exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), Or.inl h3⟩
  -- ... and for points of the second face
  have t2 : ∀ b z, Q2 b z →
      (TiltOK (ca m) 0 (cz m) (ca m) 0 zM1 0 b z (s * 1) (s * 1) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 (ca m) 0 (cz m) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 (ca m) 0 zM1) ∧
      (TiltOK (ca m) 0 zM1 0 (cb n) zM2 0 b z (s * 1) (s * 1) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 (ca m) 0 zM1 ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 0 (cb n) zM2) ∧
      (TiltOK 0 (cb n) zM2 0 (cb n) (dz n) 0 b z (s * 1) (s * 1) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 0 (cb n) zM2 ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 0 (cb n) (dz n)) := by
    intro b z hq
    have hble := C2.a_le hq
    have h1 : TiltOK (ca m) 0 (cz m) (ca m) 0 zM1 0 b z (s * 1) (s * 1) :=
      tiltOK_nm_vert1 hα hα hPM hA0.le (hpos2 b z hq) (Or.inl hA0)
    rcases hble.lt_or_eq with hlt | rfl
    · exact ⟨Or.inl h1, Or.inl (far_tiltOK (by nlinarith)),
        Or.inl (tiltOK_nm_vert2 hα hα hQM le_rfl hlt.le (Or.inr hlt))⟩
    · rcases hcard2 z hq with rfl | rfl
      · exact ⟨Or.inl h1, Or.inl (tiltOK_nm_chordQ hα hα hA0 hB0 hQM), Or.inr (Or.inr rfl)⟩
      · exact ⟨Or.inl h1, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
  refine isRupert_triShadow_nm O r1 r2 hρ C1.one_le C2.one_le s hs hα hα ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]) C1.inc C2.inc V zM1 zM2 (hV1 _ _ hM1) (hV2 _ _ hM2)
    (fun l hl => hV1 _ _ (C1.mem l hl)) (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hPM hQM
    (by rw [c10.2, c20.2]; exact hapex)
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · obtain ⟨u1, u2, u3⟩ := t1 a z hq
    refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, u1, u2, u3, fun _ => side1 a z hq, ?_⟩
    intro ha; subst ha; rw [hap1 z hq]; exact side2 0 z0 q20
  · obtain ⟨u1, u2, u3⟩ := t2 b z hq
    refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, u1, u2, u3, ?_, fun _ => side2 b z hq⟩
    intro hb; subst hb; rw [hap2 z hq]; exact side1 0 z0 q10
  · refine ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (tiltOK_nm_vert1 hα hα hPM ?_ hb.le (Or.inr hb)),
      Or.inl (far_tiltOK hin), Or.inl (tiltOK_nm_vert2 hα hα hQM ha.le ?_ (Or.inl ha)),
      fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩
    · nlinarith
    · nlinarith

end Minimality

end
