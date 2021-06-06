import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true



class HasEmptyType (U : Universe) [h : HasExternalFunctors U U] where
(Empty                  : U)
(emptyIsEmpty           : ⌈Empty⌉ → False)
(emptyElimIsFun (α : U) : h.IsFun (λ e : Empty => @False.elim ⌈α⌉ (emptyIsEmpty e)))

namespace HasEmptyType

  variable {U : Universe}
  
  def emptyElimFun' [HasExternalFunctors U U] [h : HasEmptyType U] (α : U) : h.Empty ⟶' α :=
  BundledFunctor.mkFun (h.emptyElimIsFun α)
  def emptyElimFun  [HasInternalFunctors U]   [h : HasEmptyType U] (α : U) : h.Empty ⟶  α :=
  HasInternalFunctors.fromBundled (emptyElimFun' α)

  def Not [HasInternalFunctors U] [h : HasEmptyType U] (α : U) := α ⟶ h.Empty

end HasEmptyType

-- TODO: Can we prove `α ⟶ Not α ⟶ β`?

class HasClassicalLogic (U : Universe) [HasInternalFunctors U] [h : HasEmptyType U] where
(byContradiction (α : U) : HasEmptyType.Not (HasEmptyType.Not α) ⟶ α)



class HasUnitType (U : Universe) [h : HasExternalFunctors U U] where
(Unit                   : U)
(unit                   : Unit)
(unitIntroIsFun (α : U) : h.IsFun (λ a : α => unit))

namespace HasUnitType

  variable {U : Universe}
  
  def unitIntroFun' [HasExternalFunctors U U] [h : HasUnitType U] (α : U) : α ⟶' h.Unit :=
  BundledFunctor.mkFun (h.unitIntroIsFun α)
  def unitIntroFun  [HasInternalFunctors U]   [h : HasUnitType U] (α : U) : α ⟶  h.Unit :=
  HasInternalFunctors.fromBundled (unitIntroFun' α)

  @[simp] theorem unitIntroFun.eff [HasInternalFunctors U] [h : HasUnitType U] (α : U) (a : α) :
    (unitIntroFun α) a = h.unit :=
  by apply HasInternalFunctors.fromBundled.eff

end HasUnitType
