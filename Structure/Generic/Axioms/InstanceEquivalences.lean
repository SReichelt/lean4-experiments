import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors
import Structure.Generic.Axioms.AbstractEquivalences
import Structure.Generic.Axioms.GeneralizedProperties

open GeneralizedRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v



-- When defining the groupoid axioms, we need to compare equivalences for equivalence. Although this will
-- frequently be an equality or at least a setoid equivalence, we need to prepare for the most generic
-- case where equivalences are arbitrary objects. Since we then need to define a relation into the type
-- of equivalences, we need to bundle equivalences with their equivalences.

class HasInstanceEquivalences (U : Universe.{u}) where
(equivUniverse              : Universe.{v})
[equivHasFunOp              : HasFunOp equivUniverse]
[equivHasEquiv              : HasInternalEquivalences equivUniverse]
(Equiv (α : U)              : GeneralizedRelation ⌈α⌉ equivUniverse)
[equivIsEquivalence (α : U) : IsEquivalence (Equiv α)]

namespace HasInstanceEquivalences

  variable (U : Universe) [h : HasInstanceEquivalences U]

  instance hasFunOp : HasFunOp                h.equivUniverse := h.equivHasFunOp
  instance hasEquiv : HasInternalEquivalences h.equivUniverse := h.equivHasEquiv

  instance equivEquivalence (α : U) : IsEquivalence (h.Equiv α) := h.equivIsEquivalence α

  instance hasEquivalences (α : U) : HasEquivalences ⌈α⌉ h.equivUniverse := ⟨h.Equiv α⟩
  @[reducible] def InstEquivType (α : U) := ⌈α⌉ (≃) ⌈α⌉
  instance (α : U) : HasInstances (InstEquivType U α) := Universe.instInst h.equivUniverse

end HasInstanceEquivalences

class HasEquivCongrArg (U V : Universe) [HasExternalFunctors U V]
                       [hU : HasInstanceEquivalences U] [hV : HasInstanceEquivalences V]
                       [HasExternalFunctors hU.equivUniverse hV.equivUniverse] where
(equivCongrArg {α : U} {β : V} (F : α ⟶' β) {a b : α} : a ≃ b ⟶' F a ≃ F b)

namespace HasEquivCongrArg

  variable (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] [h : HasEquivCongrArg U U]

  def equiv_congrArg' {α β : U} (F : α ⟶' β) {a b : α} : a ≃ b ⟶' F a ≃ F b := h.equivCongrArg F
  def equiv_congrArg  {α β : U} (F : α ⟶  β) {a b : α} : a ≃ b ⟶  F a ≃ F b := HasInternalFunctors.fromBundled (equiv_congrArg' U (HasInternalFunctors.toBundled F))

end HasEquivCongrArg

class HasEquivCongrFun (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] where
(equivCongrFun {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G ⟶' F a ≃ G a)

namespace HasEquivCongrFun

  variable (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] [h : HasEquivCongrFun U]

  def equiv_congrFun' {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G ⟶' F a ≃ G a := h.equivCongrFun a
  def equiv_congrFun  {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G ⟶  F a ≃ G a := HasInternalFunctors.fromBundled (equiv_congrFun' U a)

end HasEquivCongrFun

class HasEquivCongr (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] extends HasEquivCongrArg U U, HasEquivCongrFun U

namespace HasEquivCongr

  variable (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] [HasEquivCongr U]

  def equiv_congr  {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G ⟶ a ≃ b ⟶ F a ≃ G b :=
  HasLinearFunOp.swapFunFun (HasTrans.trans    ⊙ HasEquivCongrArg.equiv_congrArg U F) ⊙ HasEquivCongrFun.equiv_congrFun U b

  def equiv_congr' {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G ⟶ a ≃ b ⟶ F a ≃ G b :=
  HasLinearFunOp.swapFunFun (HasTrans.revTrans ⊙ HasEquivCongrArg.equiv_congrArg U G) ⊙ HasEquivCongrFun.equiv_congrFun U a

end HasEquivCongr

class HasNaturalEquivalences (U : Universe) [HasInternalFunctors U] extends HasInstanceEquivalences U, HasEquivCongr U where
[equivHasInstEquivs                      : HasInstanceEquivalences equivUniverse]
(isNat {α β : U} (F G : α ⟶ β) (a b : α) : HasEquivCongr.equiv_congr  U (F := F) (G := G) (a := a) (b := b) ≃
                                           HasEquivCongr.equiv_congr' U (F := F) (G := G) (a := a) (b := b))

namespace HasNaturalEquivalences

  variable (U : Universe) [HasInternalFunctors U] [h : HasNaturalEquivalences U]

  instance equivEquivs : HasInstanceEquivalences h.equivUniverse := h.equivHasInstEquivs

end HasNaturalEquivalences
