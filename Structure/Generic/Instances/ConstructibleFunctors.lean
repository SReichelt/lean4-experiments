#exit

import Structure.Generic.Axioms
import Structure.Generic.DerivedFunctors

open GeneralizedRelation



-- TODO: To make this work for groupoids, we need to add a configurable condition (I think).
class HasConstructibleFunctors (U V : Universe) [h : HasExternalFunctors U V]
                               [hU : HasInstanceEquivalences U] [hV : HasInstanceEquivalences V]
                               [HasExternalFunctors hU.equivUniverse hV.equivUniverse] where
(isFun {α : U} {β : V} (mF : α → β) (F : MappedBaseFunctor (hU.Equiv α) (hV.Equiv β) mF) : h.IsFun mF)

namespace HasConstructibleFunctors

  section idFun

    variable (U : Universe) [HasExternalFunctors U U] [hU : HasInstanceEquivalences U]
             [HasExternalFunctors hU.equivUniverse hU.equivUniverse]
             [h : HasConstructibleFunctors U U]
             [HasIdFun hU.equivUniverse]

    instance hasIdFun : HasIdFun U := ⟨λ α => h.isFun id (HasIdFun.idFun' _)⟩

  end idFun

  section constFun

    variable (U V : Universe) [HasExternalFunctors U V]
             [hU : HasInstanceEquivalences U] [hV : HasInstanceEquivalences V]
             [HasExternalFunctors hU.equivUniverse hV.equivUniverse]
             [h : HasConstructibleFunctors U V]
             [HasConstFun hU.equivUniverse hV.equivUniverse]

    instance hasConstFun : HasConstFun U V :=
    ⟨λ α {β} c => h.isFun (Function.const ⌈α⌉ c) (HasConstFun.constFun' _ (HasRefl.refl c))⟩

  end constFun

  section compFun

    variable (U V W : Universe) [HasExternalFunctors U V] [HasExternalFunctors V W] [HasExternalFunctors U W]
             [hU : HasInstanceEquivalences U] [hV : HasInstanceEquivalences V] [hW : HasInstanceEquivalences W]
             [HasExternalFunctors hU.equivUniverse hV.equivUniverse] [HasExternalFunctors hV.equivUniverse hW.equivUniverse]
             [HasExternalFunctors hU.equivUniverse hW.equivUniverse]
             [hF : HasEquivCongrArg U V] [hG : HasEquivCongrArg V W]
             [h : HasConstructibleFunctors U W]
             [HasCompFun hU.equivUniverse hV.equivUniverse hW.equivUniverse]

    instance hasCompFun : HasCompFun U V W :=
    ⟨λ {α β γ} F G => h.isFun (G.f ∘ F.f) (hG.equivCongrArg G ⊙' hF.equivCongrArg F)⟩

  end compFun

  variable (U : Universe) [HasInternalFunctors U] [hU : HasFunctorialEquivalences U]
           [h : HasConstructibleFunctors U U]

  instance hasLinearFunOp [HasLinearFunOp hU.equivUniverse] : HasLinearFunOp U :=
  { appIsFun        := λ {α} a β   => h.isFun (λ F : α ⟶ β => F a) (HasInternalFunctors.toBundled (HasFunctorialEquivalences.equiv_congrFun U a)),
    appFunIsFun     := λ α β       => sorry, --⟨λ ha F   => BundledFunctor.congrArg F ha⟩,
    compFunIsFun    := λ {α β} F γ => sorry, --⟨λ hG a   => BundledFunctor.congrFun hG (F a)⟩,
    compFunFunIsFun := λ α β γ     => sorry }-- ⟨λ hF G a => BundledFunctor.congrArg G (BundledFunctor.congrFun hF a)⟩ }

  instance hasAffineFunOp [HasAffineFunOp hU.equivUniverse] : HasAffineFunOp U :=
  { constFunIsFun   := λ α β       => h.isFun (λ c : β => HasInternalFunctors.mkFun (HasConstFun.constIsFun α c)) sorry } -- λ hc a => BundledFunctor.congrArg (HasIdFun.idFun' _) hc

  instance hasFullFunOp [HasFullFunOp hU.equivUniverse] : HasFullFunOp U :=
  { dupIsFun        := λ {α β} F   => sorry, --⟨λ ha     => BundledFunctor.congr (BundledFunctor.congrArg F ha) ha⟩,
    dupFunIsFun     := λ α β       => sorry } --⟨λ hF a   => BundledFunctor.congrFun (BundledFunctor.congrFun hF a) a⟩,

end HasConstructibleFunctors
