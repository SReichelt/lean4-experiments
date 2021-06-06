import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors
import Structure.Generic.Axioms.InstanceEquivalences
import Structure.Generic.Axioms.CategoryTheory



set_option autoBoundImplicitLocal false
--set_option pp.universes true



def FunctorEquiv {U : Universe} [HasInternalFunctors U] [h : HasInstanceEquivalences U] [HasEquivCongrArg U U] [HasInstanceEquivalences h.equivUniverse] {α β : U} (F G : α ⟶ β) :=
NaturalQuantification (h.Equiv α) (h.Equiv β) (HasEquivCongrArg.equivCongrArg (HasInternalFunctors.toBundled F)) (HasEquivCongrArg.equivCongrArg (HasInternalFunctors.toBundled G))

class HasFunctorExtensionality (U : Universe) [HasInternalFunctors U] [h : HasInstanceEquivalences U] [HasEquivCongrArg U U] [HasInstanceEquivalences h.equivUniverse] where
(funEquivEquiv {α β : U} {F G : α ⟶ β} : ⌈F ≃ G⌉ ≃ FunctorEquiv F G)

-- TODO: This should follow from functor extensionality. Maybe because of the special role of equality in functors?

--class HasLinearFunOpMorphisms (U : Universe) [HasInternalFunctors U] [HasLinearFunOp U] [HasInstanceEquivalences U] where
--(leftId  (α β : U) : HasLinearFunOp.revCompFunFun α (HasLinearFunOp.idFun β) ≃ HasLinearFunOp.idFun (α ⟶ β))
--(rightId (α β : U) : HasLinearFunOp.compFunFun (HasLinearFunOp.idFun α) β ≃ HasLinearFunOp.idFun (α ⟶ β))
