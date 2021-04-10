set_option autoBoundImplicitLocal false

universes u₁ u₂ v



class HasEquivalence (α : Sort u₁) (β : Sort u₂) where
{γ : Sort v}
(Equiv : α → β → γ)

infix:25 " ≃ "  => HasEquivalence.Equiv
