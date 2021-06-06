import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic

import mathlib4_experiments.Data.Equiv.Basic

open GeneralizedRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u



def EquivRel : GeneralizedRelation Type type := Equiv

namespace EquivRel

  -- TODO: We want to use this to show that `typeUniverse` is a groupoid, along with `propUniverse` and `groupoid` itself.
  -- See bottom of `Categories.lean`.

  instance isEquivalence : IsEquivalence EquivRel :=
  { refl  := Equiv.refl,
    trans := Equiv.trans,
    symm  := ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩ }

  instance isCompositionRelation : IsCompositionRelation EquivRel :=
  { assoc := funext (λ ab => (funext (λ bc => funext (λ cd => Equiv.trans_assoc ab bc cd)))) }

  instance isMorphismRelation : IsMorphismRelation EquivRel :=
  { leftId  := funext Equiv.trans_refl,
    rightId := funext Equiv.refl_trans }

  instance isIsomorphismRelation : IsIsomorphismRelation EquivRel :=
  { leftInv  := funext Equiv.trans_symm,
    rightInv := funext Equiv.symm_trans }

end EquivRel
