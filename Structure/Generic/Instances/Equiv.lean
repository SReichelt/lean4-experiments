import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic

import mathlib4_experiments.Data.Equiv.Basic

open GeneralizedRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u



def EquivRel : GeneralizedRelation (Type u) typeUniverse.{u} := Equiv

namespace EquivRel

  -- TODO: We want to use this to show that `typeUniverse` is a groupoid, along with `propUniverse` and `groupoid` itself.
  -- See bottom of `Categories.lean`.

  instance isEquivalence : IsEquivalence EquivRel :=
  { refl  := Equiv.refl,
    symm  := Equiv.symm,
    trans := Equiv.trans }

  instance isCompositionRelation : IsCompositionRelation EquivRel :=
  { assocLR := λ f g h => Eq.symm (Equiv.trans_assoc f g h),
    assocRL := Equiv.trans_assoc }

  instance isMorphismRelation : IsMorphismRelation EquivRel :=
  { leftId  := Equiv.trans_refl,
    rightId := Equiv.refl_trans }

  instance isIsomorphismRelation : IsIsomorphismRelation EquivRel :=
  { leftInv  := Equiv.trans_symm,
    rightInv := Equiv.symm_trans,
    invInv   := Equiv.symm_symm,
    compInv  := Equiv.symm_trans_symm,
    idInv    := @Equiv.refl_symm }

end EquivRel

instance typeHasEquivalences : HasEquivalences (Type u) typeUniverse.{u} := ⟨EquivRel⟩
