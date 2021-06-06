import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors
import Structure.Generic.Axioms.InstanceEquivalences
import Structure.Generic.Axioms.CategoryTheory



set_option autoBoundImplicitLocal false
--set_option pp.universes true



class HasInstanceIsomorphisms (U : Universe) [HasInternalFunctors U] extends HasNaturalEquivalences U where
[equivIsIso (α : U) : IsIsomorphismRelation (Equiv α)]

namespace HasInstanceIsomorphisms

  variable (U : Universe) [HasInternalFunctors U] [h : HasInstanceIsomorphisms U]

  instance typeIsGroupoid (α : U) : IsGroupoid h.equivUniverse ⌈α⌉ :=
  { isIso := h.equivIsIso α }

end HasInstanceIsomorphisms
