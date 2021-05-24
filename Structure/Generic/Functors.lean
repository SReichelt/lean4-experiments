import Structure.Generic.Axioms
import Structure.Generic.Mapped
import Structure.Generic.Lemmas



section Functors

  variable {α : Sort u} {β : Sort v} (V W : Universe)
           [HasInternalFunctors V] [HasInternalFunctors W] [HasInstanceArrows W] [HasExternalFunctors V W]

  class IsProductFunctor [hα : HasProducts     α V] [hβ : HasProducts     β W] (F : α → β) where
  (mapProduct {a b : α} : a ⊓ b ⟶' F a ⊓ F b)
  [isFunctor            : IsSymmFunctor        hα.Product (mapOperation hβ.Product F) mapProduct]

  class IsArrowFunctor   [hα : HasArrows       α V] [hβ : HasArrows       β W] (F : α → β) where
  (mapArrow   {a b : α} : (a ⇝ b) ⟶' (F a ⇝ F b))
  [isFunctor            : IsPreorderFunctor    hα.Arrow   (mapOperation hβ.Arrow   F) mapArrow]

  class IsEquivFunctor   [hα : HasEquivalences α V] [hβ : HasEquivalences β W] (F : α → β) where
  (mapEquiv   {a b : α} : a ≃ b ⟶' F a ≃ F b)
  [isFunctor            : IsEquivalenceFunctor hα.Equiv   (mapOperation hβ.Equiv   F) mapEquiv]

end Functors

section FunctorOperations

  variable {α : Sort u}

  namespace idFun

    variable (V : Universe) [HasInternalFunctors V] [HasInstanceArrows V] [HasIdFun V]

    instance isProductFunctor [hα : HasProducts α V] : IsProductFunctor V V (@id α) :=
    { mapProduct := HasIdFun.idFun' _,
      isFunctor  := GeneralizedRelation.mapSymm.id hα.Product ▸ isSymmFunctor hα.Product }

    instance isArrowFunctor [hα : HasArrows α V] : IsArrowFunctor V V (@id α) :=
    { mapArrow  := HasIdFun.idFun' _,
      isFunctor := GeneralizedRelation.mapPreorder.id hα.Arrow ▸ isPreorderFunctor hα.Arrow }

    instance isEquivFunctor [hα : HasEquivalences α V] : IsEquivFunctor V V (@id α) :=
    { mapEquiv  := HasIdFun.idFun' _,
      isFunctor := GeneralizedRelation.mapEquivalence.id hα.Equiv ▸ isEquivalenceFunctor hα.Equiv }

  end idFun

  -- TODO: const, comp

end FunctorOperations



section NaturalTransformations

  variable {α : Sort u} {β : Sort v} (V W : Universe)
           [HasInternalFunctors V] [HasInternalFunctors W] [HasInstanceEquivalences W] [HasExternalFunctors V W]

  instance : HasInstanceArrows W := HasInstanceEquivalences.toHasInstanceArrows W

  def NaturalTransformation [hα : HasArrows α V] [hβ : HasArrows β W]
                            (F G : α → β) [hF : IsArrowFunctor V W F] [hG : IsArrowFunctor V W G] :=
  NaturalQuantification hα.Arrow hβ.Arrow hF.mapArrow hG.mapArrow

  def NaturalEquivalence [hα : HasEquivalences α V] [hβ : HasEquivalences β W]
                         (F G : α → β) [hF : IsEquivFunctor V W F] [hG : IsEquivFunctor V W G] :=
  NaturalQuantification hα.Equiv hβ.Equiv hF.mapEquiv hG.mapEquiv

end NaturalTransformations

-- TODO: is preorder, is equivalence