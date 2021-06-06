import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true



def ExternalProduct {U V : Universe} (α : U) (β : V) := PProd ⌈α⌉ ⌈β⌉

namespace ExternalProduct

  infixr:35 " ⊓' " => ExternalProduct

end ExternalProduct

class HasInternalProducts (U : Universe) [h : HasExternalFunctors U U] where
(Prod                                                   : U → U → U)
(prodEquiv        (α β : U)                             : ⌈Prod α β⌉ ≃ (α ⊓' β))
(prodIntroIsFun   {α β ω : U} (F : ω ⟶' α) (G : ω ⟶' β) : h.IsFun (λ a : ω => (prodEquiv α β).invFun ⟨F a, G a⟩))
(prodElimFstIsFun (α β : U)                             : h.IsFun (λ P : Prod α β => ((prodEquiv α β).toFun P).fst))
(prodElimSndIsFun (α β : U)                             : h.IsFun (λ P : Prod α β => ((prodEquiv α β).toFun P).snd))

namespace HasInternalProducts

  infixr:35 " ⊓ " => HasInternalProducts.Prod

end HasInternalProducts

-- TODO: Add a type class that says that the combination of intro and elim are equivalences (when the other side is fixed).
-- Prove that this is an equivalence between U and U ⨯ U.

-- TODO: Derive some logic and especially the arrow/product laws.
