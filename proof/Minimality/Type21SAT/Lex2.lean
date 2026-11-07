module

public import Minimality.Type20Bridge

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Three-level lexicographic positivity: first entry positive, or zero and then the second
positive, or both zero and the third positive. -/
def LP3 (a b c : ℝ) : Prop := 0 < a ∨ (a = 0 ∧ (0 < b ∨ (b = 0 ∧ 0 < c)))

/-- Lex-weak order on depths with tie-break `y`: `z i < z j`, or equal and `y i ≤ y j`. -/
def LexLE (z y : ZMod k → ℝ) (i j : ZMod k) : Prop := z i < z j ∨ (z i = z j ∧ y i ≤ y j)

/-- `RobUni` with the weak order `≤` replaced by the lex-weak order of `(z, y)`. -/
def RobUniL {k : ℕ} (z y : ZMod k → ℝ) : Prop :=
  ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
    ¬ (LexLE z y (B + b) B ∧ LexLE z y (B + b) (B + c) ∧
       LexLE z y (B + d) B ∧ LexLE z y (B + d) (B + c))

/-- If `a, b, c` are three-level positive, then for small `ε > 0` the pair `(a + ε b, c)` is
two-level positive. -/
theorem lp3_ev {a b c : ℝ} (h : LP3 a b c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), h21b_LP (a + ε * b) c := by
  by_cases h1 : 0 < a ∨ (a = 0 ∧ 0 < b)
  · exact (eventually_pos_affine h1).mono fun ε hε => Or.inl hε
  · have ha : a = 0 := by
      rcases h with h | ⟨h, _⟩
      · exact absurd (Or.inl h) h1
      · exact h
    have hb : b = 0 ∧ 0 < c := by
      rcases h with h | ⟨_, h | h⟩
      · exact absurd (Or.inl h) h1
      · exact absurd (Or.inr ⟨ha, h⟩) h1
      · exact h
    exact Eventually.of_forall fun ε => Or.inr ⟨by rw [ha, hb.1]; ring, hb.2⟩

/-- For small `ε > 0`, the depths `z + ε y` weakly compare only when `(z, y)` lex-weakly compares. -/
theorem lexLE_ev {k : ℕ} [NeZero k] (z y : ZMod k → ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, z i + ε * y i ≤ z j + ε * y j → LexLE z y i j := by
  refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
  by_cases h : LexLE z y i j
  · exact Eventually.of_forall fun _ _ => h
  · have h' : z j < z i ∨ (z j = z i ∧ y j < y i) := by
      unfold LexLE at h
      push_neg at h
      rcases lt_or_eq_of_le h.1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h.2 h1.symm⟩
    have := eventually_pos_affine (A := z i - z j) (B := y i - y j) (by
      rcases h' with h' | ⟨h1, h2⟩
      · exact Or.inl (sub_pos.2 h')
      · exact Or.inr ⟨sub_eq_zero.2 h1.symm, sub_pos.2 h2⟩)
    exact this.mono fun ε hε hle => absurd hle (by nlinarith)

/-- **Lex tilt leaf, two levels of perturbation.**  A cycle `c` that is a silhouette of the pattern
`pat`, with the facings of every facet determined lexicographically by `(N·u, N·d, N·w)`, and depths
`x (c i) · u` robustly unimodal after the tie-break `x (c i) · d`, gives a Rupert point set.  Proof:
at `u + ε d` for small `ε > 0` this is the plain tilt leaf with tilt `w`. -/
theorem s0x_lex2_rupert {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod k → Fin n} {pat : Fin m → Bool} {u d w : ℝ³} (hc : Function.Injective c)
    (hk : 3 ≤ k) (hcyc : S0xCycOK S c pat) (hu : u ≠ 0)
    (hfac : ∀ t, (pat t = true → LP3 ⟪F.N t, u⟫ ⟪F.N t, d⟫ ⟪F.N t, w⟫) ∧
      (pat t = false → LP3 (-⟪F.N t, u⟫) (-⟪F.N t, d⟫) (-⟪F.N t, w⟫)))
    (hU : RobUniL (fun i => ⟪x (c i), u⟫) (fun i => ⟪x (c i), d⟫)) :
    IsRupert (univ.image x) := by
  have e1 : ∀ ε : ℝ, ∀ p : ℝ³, ⟪p, u + ε • d⟫ = ⟪p, u⟫ + ε * ⟪p, d⟫ := by
    intro ε p; rw [inner_add_right, inner_smul_right]
  have hfacev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S0xFacOK F pat (u + ε • d) w := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t : Fin m, (pat t = true → h21b_LP ⟪F.N t, u + ε • d⟫ ⟪F.N t, w⟫) ∧
        (pat t = false → h21b_LP (-⟪F.N t, u + ε • d⟫) (-⟪F.N t, w⟫)) := by
      refine eventually_all.2 fun t => ?_
      obtain ⟨h1, h2⟩ := hfac t
      by_cases hp : pat t = true
      · filter_upwards [lp3_ev (h1 hp)] with ε hε
        refine ⟨fun _ => by rw [e1]; exact hε, fun h => absurd hp (by simp [h])⟩
      · have hp' : pat t = false := by simpa using hp
        filter_upwards [lp3_ev (h2 hp')] with ε hε
        refine ⟨fun h => absurd h hp, fun _ => ?_⟩
        have : -⟪F.N t, u + ε • d⟫ = -⟪F.N t, u⟫ + ε * (-⟪F.N t, d⟫) := by rw [e1]; ring
        rw [this]; exact hε
    exact this
  have hune : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u + ε • d ≠ 0 := by
    have hcont : Continuous fun ε : ℝ => u + ε • d := by fun_prop
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), u + ε • d ≠ 0 :=
      hcont.continuousAt.eventually (isOpen_ne.mem_nhds (by simpa using hu))
    exact this.filter_mono nhdsWithin_le_nhds
  have hlex := lexLE_ev (fun i => ⟪x (c i), u⟫) (fun i => ⟪x (c i), d⟫)
  obtain ⟨ε, h1, h2, h3⟩ := (hfacev.and (hune.and hlex)).exists
  obtain ⟨D⟩ := s0x_silL (k := k) F hcyc h1
  refine s0x_sil_isRupert_lex hk hx hc h2 D ?_
  intro B b c' d' hb hbc hcd hdk ⟨q1, q2, q3, q4⟩
  have e2 : ∀ i, ⟪x (c i), u + ε • d⟫ = ⟪x (c i), u⟫ + ε * ⟪x (c i), d⟫ := fun i => e1 ε _
  simp only [e2] at q1 q2 q3 q4
  exact hU B b c' d' hb hbc hcd hdk ⟨h3 _ _ q1, h3 _ _ q2, h3 _ _ q3, h3 _ _ q4⟩

/-- **Any tope at `u` is a leaf** (type-free).  If the facings of all facets at `(u, v)` follow the
pattern in the lex sense (facets edge-on at `u` are decided by the tilt `v`; any number of them),
the cycle `c` is a silhouette of the pattern, and the depths `x (c i) · u` are robustly unimodal,
then the point set is Rupert.  This holds for every `u ≠ 0`. -/
theorem s0x_tope_rupert {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod k → Fin n} {pat : Fin m → Bool} {u : ℝ³} (v : ℝ³) (hc : Function.Injective c)
    (hk : 3 ≤ k) (hcyc : S0xCycOK S c pat) (hu : u ≠ 0) (hfac : S0xFacOK F pat u v)
    (hU : RobUni (fun a : ZMod k => ⟪x (c a), u⟫)) : IsRupert (univ.image x) := by
  obtain ⟨D⟩ := s0x_silL (k := k) F hcyc hfac
  exact s0x_sil_isRupert_lex hk hx hc hu D hU

/-- A tope at `u`: a pattern whose facings at `u` are strict, or edge-on and settled by one tilt `v`
(rank 2 tope: all the edge-on facets share the single tilt). -/
def S0xTope (F : S0xFac m S x) (pat : Fin m → Bool) (u : ℝ³) : Prop := ∃ v, S0xFacOK F pat u v

/-- **Tope leaf, packaged**: a tope at `u ≠ 0` with a silhouette cycle of robustly unimodal depths
makes the point set Rupert. -/
theorem s0x_tope_rupert' {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod k → Fin n} {pat : Fin m → Bool} {u : ℝ³} (hc : Function.Injective c)
    (hk : 3 ≤ k) (hcyc : S0xCycOK S c pat) (hu : u ≠ 0) (ht : S0xTope F pat u)
    (hU : RobUni (fun a : ZMod k => ⟪x (c a), u⟫)) : IsRupert (univ.image x) := by
  obtain ⟨v, hv⟩ := ht
  exact s0x_tope_rupert F hx v hc hk hcyc hu hv hU

end H21
end Minimality

