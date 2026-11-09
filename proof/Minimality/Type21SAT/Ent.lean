module

public import Minimality.Type21SAT.Def

@[expose] public section

/-!
# L3, part 4 (start): the generic lemmas behind every table entry, three valued

Every entry of the triple table is, by L/B21Ent3 to Ent7, one of: zero (ZC, ZQ); a positive multiple
of (constant or `kv` atom) times (facing atom or constant); an integer multiple of an atom (BR, L, M);
a bracket sign from the orientation table (B4).  Three valued, the same identities hold and the
entry is `mul3` of the two three valued factors, so the lemmas below are the whole new content:
no entry needs a nonzero hypothesis.  What remains is the routing of each key (constants from
`OriOK`), which is word for word the two valued code with `Sg3` for `Sg`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical

namespace Minimality.H21.SAT

/-- In-facet determinant against a facing: `det(u, v, w) |N|^2 = det(u, v, N) <N, w>` (copy of `det_perp`). -/
theorem det_perp (u v w N : ℝ³) (hu : ⟪N, u⟫ = 0) (hv : ⟪N, v⟫ = 0) :
    det3 u v w * ⟪N, N⟫ = det3 u v N * ⟪N, w⟫ := by
  simp only [inn3, det3_expand] at hu hv ⊢
  linear_combination ((u 0 * N 1 * w 2 - u 0 * N 2 * w 1 - u 1 * N 0 * w 2 + u 1 * N 2 * w 0 + u 2 * N 0 * w 1 - u 2 * N 1 * w 0)) * hv - ((v 0 * N 1 * w 2 - v 0 * N 2 * w 1 - v 1 * N 0 * w 2 + v 1 * N 2 * w 0 + v 2 * N 0 * w 1 - v 2 * N 1 * w 0)) * hu

/-- **The facet route, three valued** (replaces `fac_core`, `facTm_sound`): if `u, v` are orthogonal to a
nonzero `N`, the entry `mul3 SA SF` is the sign of `det(u, v, w)`, whenever `SA` is the sign of
`det(u, v, N)` and `SF` that of `<N, w>`.  Zero factors are allowed. -/
theorem fac_core3 {ρ : V → Bool} (hP : Proper ρ) (hG : GateOK ρ) {u v w N : ℝ³}
    (hu : ⟪N, u⟫ = 0) (hv : ⟪N, v⟫ = 0) (hN : 0 < ⟪N, N⟫) {SA SF : S3}
    (hA : Sg3 ρ SA (det3 u v N)) (hF : Sg3 ρ SF ⟪N, w⟫) :
    Sg3 ρ (mul3 SA SF) (det3 u v w) := by
  have hp := Sg3.mul3 hP hG hA hF
  have id := det_perp u v w N hu hv
  have e : det3 u v w = (1 / ⟪N, N⟫) * (det3 u v N * ⟪N, w⟫) := by
    field_simp; linarith [id]
  rw [e]
  exact Sg3.scale (by positivity) hp

/-- Multiplication by an integer constant on three valued signs. -/
def scaleS (c : Int) (t : S3) : S3 := if 0 < c then t else if c < 0 then negS t else zeroS

/-- An integer multiple of a real: the sign is that of the real, flipped or zeroed by the constant. -/
theorem Sg3_scaleS {ρ : V → Bool} (hP : Proper ρ) {t : S3} {r : ℝ} (c : Int) (h : Sg3 ρ t r) :
    Sg3 ρ (scaleS c t) ((c : ℝ) * r) := by
  unfold scaleS
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hc' : (c : ℝ) < 0 := by exact_mod_cast hc
    simp only [not_lt.mpr hc.le, ite_false, hc, ite_true]
    have := h.neg
    have e : (c : ℝ) * r = (-(c : ℝ)) * (-r) := by ring
    rw [e]
    exact Sg3.scale (by linarith) this
  · subst hc
    simp only [lt_irrefl, ite_false, Int.cast_zero, zero_mul]
    exact Sg3_zero hP
  · have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    simp only [hc, ite_true]
    exact Sg3.scale hc' h

/-- A determinant equal to an integer multiple of an atom (routes BR, L, M, B4): the entry is `scaleS c (atomS v)`. -/
theorem entry_atom {ρ : V → Bool} (hP : Proper ρ) {v : V} {a d : ℝ} (c : Int)
    (hv : Sg3 ρ (atomS v) a) (hd : d = (c : ℝ) * a) : Sg3 ρ (scaleS c (atomS v)) d := by
  rw [hd]; exact Sg3_scaleS hP c hv

/-- A vanishing determinant (routes ZC, ZQ) has the sign `zeroS`. -/
theorem entry_zero {ρ : V → Bool} (hP : Proper ρ) {d : ℝ} (hd : d = 0) : Sg3 ρ zeroS d := by
  rw [hd]; exact Sg3_zero hP

/-- **Permutation of a determinant**: a swap negates the entry, a cycle keeps it (the keys of the table are
sorted, the schemas ask for sorted arguments and flip signs). -/
theorem entry_swap {ρ : V → Bool} {t : S3} {a b c : ℝ³}
    (h : Sg3 ρ t (det3 a b c)) : Sg3 ρ (negS t) (det3 a c b) := by
  have : det3 a c b = -det3 a b c := by simp only [det3_expand]; ring
  rw [this]; exact h.neg

end Minimality.H21.SAT
