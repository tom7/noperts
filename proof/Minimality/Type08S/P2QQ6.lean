module

public import Minimality.Type08S.P2QQ6b

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp

/-- **Q6.** Every type-08 shape has a `Norm08w` structure in one of the six labellings (orders as in
`Resid08FinalH` and `type08_set_perm`). -/
theorem exists_norm08w {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (G : GaleData a a' b b' c c') :
    Nonempty (Norm08w a a' b b' c c' d) ∨ Nonempty (Norm08w b b' a a' c c' d) ∨
    Nonempty (Norm08w a a' c c' b b' d) ∨ Nonempty (Norm08w c c' a a' b b' d) ∨
    Nonempty (Norm08w b b' c c' a a' d) ∨ Nonempty (Norm08w c c' b b' a a' d) := by
  have hA : galeD G.l G.m a b * galeD G.l G.m a c < 0 := pole_first F G
  have hB : galeD G.l G.m b a * galeD G.l G.m b c < 0 := pole_first F.perm₁₂ G.perm₁₂
  have hC : galeD G.l G.m c a * galeD G.l G.m c b < 0 := pole_first F.perm₂₃.perm₁₂ G.perm₂₃.perm₁₂
  obtain ⟨σ, hσ, hpick⟩ := pick_sigma (galeD G.l G.m a a') (galeD G.l G.m b b') (galeD G.l G.m c c')
  obtain ⟨G', hG'⟩ := exists_gale_sigma G hσ
  have anti := galeD_anti G.l G.m
  have hκ : ∀ s t, 0 ≤ σ * galeD G.l G.m s t → 0 ≤ galeD G'.l G'.m s t := fun s t h => by rw [hG']; exact h
  have hle : ∀ s t, σ * galeD G.l G.m s t ≤ 0 → galeD G'.l G'.m s t ≤ 0 := fun s t h => by rw [hG']; exact h
  rcases hpick with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- z = c
    have h : galeD G.l G.m a c * galeD G.l G.m b c < 0 := by
      have := hC; rw [anti a c, anti b c] at this; nlinarith
    rcases sign_step σ _ _ h with s | s
    · exact Or.inl ⟨⟨F, hd, G', hκ _ _ h1, hκ _ _ h2, hle _ _ s⟩⟩
    · exact Or.inr (Or.inl ⟨⟨F.perm₁₂, hd.perm₁₂, G'.perm₁₂, hκ _ _ h2, hκ _ _ h1, hle _ _ s⟩⟩)
  · -- z = b
    have h : galeD G.l G.m a b * galeD G.l G.m c b < 0 := by
      have := hB; rw [anti a b, anti c b] at this; nlinarith
    rcases sign_step σ _ _ h with s | s
    · exact Or.inr (Or.inr (Or.inl ⟨⟨F.perm₂₃, hd.perm₂₃, G'.perm₂₃, hκ _ _ h1, hκ _ _ h2, hle _ _ s⟩⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨F.perm₂₃.perm₁₂, hd.perm₂₃.perm₁₂, G'.perm₂₃.perm₁₂,
        hκ _ _ h2, hκ _ _ h1, hle _ _ s⟩⟩)))
  · -- z = a
    have h : galeD G.l G.m b a * galeD G.l G.m c a < 0 := by
      rw [anti a b, anti a c]; nlinarith
    rcases sign_step σ _ _ h with s | s
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨F.perm₁₂.perm₂₃, hd.perm₁₂.perm₂₃,
        G'.perm₁₂.perm₂₃, hκ _ _ h1, hκ _ _ h2, hle _ _ s⟩⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨F.perm₁₂.perm₂₃.perm₁₂, hd.perm₁₂.perm₂₃.perm₁₂,
        G'.perm₁₂.perm₂₃.perm₁₂, hκ _ _ h2, hκ _ _ h1, hle _ _ s⟩⟩))))

end Type08Sp
end Minimality

