module

public import Minimality.Type29Disp
public import Minimality.Type29Sigma

@[expose] public section

/-!
# Type 29, classes K3 and K4, outside codimension 2 (`FEWER-FACES-PROOFS.md` §28)

The assembly of Theorem 28.10: a type-29 shape whose octahedron `K − 6` is in class K3a, K3b,
K4a or K4b is Rupert if it has at most one tie at its named views (`OneTieGlobal29`) and at each
closing `ℓ` of the cover's whitelists (`Lab29`) the codimension-2 condition `Cond29` holds:
no horizontal double normal at the view, or the exception of §22 for that closing (a failure of
(G1) at a view between two triangles or at a two-circle closing, `Sec29`, `TwoGen29`; the
conditions of Lemma E at the quadrilateral-triangle edges, `EdgeOK29`).

* `isRupert_type29_limit_hdn`: the limit theorem (Lemma 18.2 with §22).
* `HDN29K3`, `HDN29K4`: the hypothesis.
* `NF29.isRupert_K3a_codim2`, `_K3b_`, `_K4a_`, `_K4b_`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-- **Type 29 outside the HDN set and codimension 2, with the exceptions of §22** (Lemma 18.2,
Proposition 22.2, §22.3–22.8): a type-29 shape `x` of class K3a or K4a (`hcls`) with at most one
tie at its named views is Rupert if at each closing of the whitelists `Cond29` holds. -/
theorem isRupert_type29_limit_hdn (N : NF29 x)
    (hcls : (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) ∨
      (0 < N.a2 ∧ 0 < N.b0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0))
    (H : ∀ ℓ : Lab29, ℓ.Ok → Cond29 N ℓ) (htie : OneTieGlobal29 x) :
    IsRupert (univ.image x) := by
  obtain ⟨K, θs, hK, hθs, hc⟩ := exists_certSeq29_params N htie hcls
  exact isRupert_of_cert_seq29_hdn N K hK θs hθs H hc

/-- **The HDN exceptions of class K3** (§28.5, Theorem 28.10): at every closing `ℓ` of the K3a
cover, `Cond29`. -/
def HDN29K3 (N : NF29 x) : Prop := ∀ ℓ : Lab29, ℓ.Ok → Cond29 N ℓ

/-- **The HDN exceptions of class K4** (§28.5, Theorem 28.10): at every closing `ℓ` of the K4a
cover, `Cond29`. -/
def HDN29K4 (N : NF29 x) : Prop := ∀ ℓ : Lab29, ℓ.Ok → Cond29 N ℓ

/-- **Class K3a outside codimension 2** (Theorem 28.10): `a2 < 0 < b0`, `V > 0`, at most one tie
at the named views and the exceptions `HDN29K3`. -/
theorem NF29.isRupert_K3a_codim2 (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) (htie : OneTieGlobal29 x)
    (hH : HDN29K3 N) : IsRupert (univ.image x) :=
  isRupert_type29_limit_hdn N (Or.inl ⟨ha2, hb0, hV⟩) hH htie

/-- **Class K4a outside codimension 2** (Theorem 28.10): `a2, b0 > 0`, `V < 0`. -/
theorem NF29.isRupert_K4a_codim2 (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0) (htie : OneTieGlobal29 x)
    (hH : HDN29K4 N) : IsRupert (univ.image x) :=
  isRupert_type29_limit_hdn N (Or.inr ⟨ha2, hb0, hV⟩) hH htie

/-- **Class K3b outside codimension 2** (`σ` of K3a): `a2 > 0 > b0`, `V < 0`; the exceptions
are those of the `σ`-image `N.sigma`.  The tie condition is that of `x` (`OneTieGlobal29.sigma`). -/
theorem NF29.isRupert_K3b_codim2 (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : N.b0 < 0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0) (htie : OneTieGlobal29 x)
    (hH : HDN29K3 N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K3a_codim2 N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith)
    htie.sigma hH
  rwa [image_sigma29] at h

/-- **Class K4b outside codimension 2** (`σ` of K4a): `a2, b0 > 0`, `V > 0`. -/
theorem NF29.isRupert_K4b_codim2 (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) (htie : OneTieGlobal29 x)
    (hH : HDN29K4 N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K4a_codim2 N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith)
    htie.sigma hH
  rwa [image_sigma29] at h

end Minimality

end
