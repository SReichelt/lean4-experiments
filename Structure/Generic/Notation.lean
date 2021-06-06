-- Some type classes for special notation that we use.

import mathlib4_experiments.Data.Notation



set_option autoBoundImplicitLocal false

universes u v w



class HasProduct (α : Sort u) (β : Sort v) where
{γ       : Sort w}
(Product : α → β → γ)

infixr:35 " (⧆) " => HasProduct.γ
infixr:35 " ⧆ " => HasProduct.Product


class HasArrow (α : Sort u) (β : Sort v) where
{γ     : Sort w}
(Arrow : α → β → γ)

infixr:20 " (⇝) " => HasArrow.γ
infixr:20 " ⇝ " => HasArrow.Arrow


infixr:25 " (≃) " => HasEquivalence.γ
