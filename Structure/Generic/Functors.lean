--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- This file contains definitions of category-theoretic functors using just the basic axioms.



import Structure.Generic.Axioms
import Structure.Generic.Mapped



section Functors

  variable {α : Sort u} {β : Sort v} (V W : Universe)
           [HasInternalFunctors V] [HasInternalFunctors W] [HasInstanceArrows W] [HasExternalFunctors V W]
           (F : α → β)

  class IsProductFunctor [hα : HasProducts     α V] [hβ : HasProducts     β W] where
  (mapProduct {a b : α} : a ⊓ b ⟶' F a ⊓ F b)
  [isFunctor            : IsSymmFunctor        hα.Product (mapOperation hβ.Product F) mapProduct]

  class IsArrowFunctor   [hα : HasArrows       α V] [hβ : HasArrows       β W] where
  (mapArrow   {a b : α} : (a ⇝ b) ⟶' (F a ⇝ F b))
  [isFunctor            : IsPreorderFunctor    hα.Arrow   (mapOperation hβ.Arrow   F) mapArrow]

  class IsEquivFunctor   [hα : HasEquivalences α V] [hβ : HasEquivalences β W] where
  (mapEquiv   {a b : α} : a ≃ b ⟶' F a ≃ F b)
  [isFunctor            : IsEquivalenceFunctor hα.Equiv   (mapOperation hβ.Equiv   F) mapEquiv]

end Functors

-- TODO: id, const, comp



section NaturalTransformations

  variable {α : Sort u} {β : Sort v} (V W : Universe)
           [HasInternalFunctors V] [HasInternalFunctors W] [HasInstanceEquivalences W] [HasExternalFunctors V W]
           (F G : α → β)

  instance : HasInstanceArrows W := HasInstanceEquivalences.toHasInstanceArrows W

  class IsNaturalTransformation [hα : HasArrows α V] [hβ : HasArrows β W]
                                [hF : IsArrowFunctor V W F] [hG : IsArrowFunctor V W G] where
  (arrow (a : α) : F a ⇝ G a)
  [isNatural     : IsNatural hα.Arrow hβ.Arrow hF.mapArrow hG.mapArrow arrow]

  class IsNaturalEquivalence [hα : HasEquivalences α V] [hβ : HasEquivalences β W]
                             [hF : IsEquivFunctor V W F] [hG : IsEquivFunctor V W G] where
  (equiv (a : α) : F a ≃ G a)
  [isNatural     : IsNatural hα.Equiv hβ.Equiv hF.mapEquiv hG.mapEquiv equiv]

end NaturalTransformations

-- TODO: is preorder, is equivalence
