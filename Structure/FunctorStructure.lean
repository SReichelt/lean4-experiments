import Structure.Basic

open Structure
open StructureFunctor
open Forgetfulness



-- `universeStructure` enables us to define functors for the two maps from a structure `T` to the
-- functor structure with `T` on one side, with the restriction that we need to work with setoid
-- structures in most places.

namespace FunctorStructure

variable (S : Structure)

@[reducible] def UniverseStructureFunctor := StructureFunctor universeStructure universeStructure

def outgoingFunctorStructure (T : Structure) := functorStructure S (setoidStructure T)

def outgoingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  SetoidStructureFunctor (outgoingFunctorStructure S T₁) (outgoingFunctorStructure S T₂) :=
{ map     := λ f => compFun f e.toFun,
  functor := { FF        := λ h => compFun.congrArg' h (Setoid.refl _),
               isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ => proofIrrel _ _,
                              respectsId     := λ _   => proofIrrel _ _,
                              respectsInv    := λ _   => proofIrrel _ _ } } }

def outgoingFunctorEquiv {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  outgoingFunctorStructure S T₁ ≃ outgoingFunctorStructure S T₂ :=
{ toFun    := outgoingToFun S e,
  invFun   := outgoingToFun S e⁻¹,
  leftInv  := λ f => Setoid.trans (compFun.congrArg' (Setoid.refl _) e.leftInv')  (idFun.leftId' f),
  rightInv := λ f => Setoid.trans (compFun.congrArg' (Setoid.refl _) e.rightInv') (idFun.leftId' f) }

def outgoingFunctorFunctor : UniverseStructureFunctor :=
{ map     := outgoingFunctorStructure S,
  functor := { FF        := outgoingFunctorEquiv S,
               isFunctor := { respectsSetoid := λ ⟨l, r⟩ => ⟨⟨λ f => compFun.congrArg' (Setoid.refl _) l⟩,
                                                             ⟨λ f => compFun.congrArg' (Setoid.refl _) r⟩⟩,
                              respectsComp   := λ e₁ e₂ => ⟨⟨λ f => compFun.assoc' f e₁.toFun  e₂.toFun⟩,
                                                            ⟨λ f => compFun.assoc' f e₂.invFun e₁.invFun⟩⟩,
                              respectsId     := λ S     => ⟨⟨λ f => Setoid.trans (compFun.congrArg' (idFun.leftId' f) (Setoid.refl _)) (idFun.leftId' f)⟩,
                                                            ⟨λ f => Setoid.trans (compFun.congrArg' (idFun.leftId' f) (Setoid.refl _)) (idFun.leftId' f)⟩⟩,
                              respectsInv    := λ e     => ⟨⟨λ f => Setoid.refl (compFun f e.invFun)⟩,
                                                            ⟨λ f => Setoid.refl (compFun f e.toFun)⟩⟩ } } }

def incomingFunctorStructure (T : Structure) := functorStructure (setoidStructure T) S

def incomingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  SetoidStructureFunctor (incomingFunctorStructure S T₁) (incomingFunctorStructure S T₂) :=
{ map     := λ f => compFun e.invFun f,
  functor := { FF        := λ h => compFun.congrArg' (Setoid.refl _) h,
               isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ => proofIrrel _ _,
                              respectsId     := λ _   => proofIrrel _ _,
                              respectsInv    := λ _   => proofIrrel _ _ } } }

def incomingFunctorEquiv {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  incomingFunctorStructure S T₁ ≃ incomingFunctorStructure S T₂ :=
{ toFun    := incomingToFun S e,
  invFun   := incomingToFun S e⁻¹,
  leftInv  := λ f => Setoid.trans (compFun.congrArg' e.leftInv'  (Setoid.refl _)) (idFun.rightId' f),
  rightInv := λ f => Setoid.trans (compFun.congrArg' e.rightInv' (Setoid.refl _)) (idFun.rightId' f) }

def incomingFunctorFunctor : UniverseStructureFunctor :=
{ map     := incomingFunctorStructure S,
  functor := { FF        := incomingFunctorEquiv S,
               isFunctor := { respectsSetoid := λ ⟨l, r⟩ => ⟨⟨λ f => compFun.congrArg' r (Setoid.refl _)⟩,
                                                             ⟨λ f => compFun.congrArg' l (Setoid.refl _)⟩⟩,
                              respectsComp   := λ e₁ e₂ => ⟨⟨λ f => compFun.assoc' e₂.invFun e₁.invFun f⟩,
                                                            ⟨λ f => compFun.assoc' e₁.toFun  e₂.toFun  f⟩⟩,
                              respectsId     := λ S     => ⟨⟨λ f => Setoid.trans (compFun.congrArg' (Setoid.refl _) (idFun.rightId' f)) (idFun.rightId' f)⟩,
                                                            ⟨λ f => Setoid.trans (compFun.congrArg' (Setoid.refl _) (idFun.rightId' f)) (idFun.rightId' f)⟩⟩,
                              respectsInv    := λ e     => ⟨⟨λ f => Setoid.refl (compFun e.toFun  f)⟩,
                                                            ⟨λ f => Setoid.refl (compFun e.invFun f)⟩⟩ } } }

end FunctorStructure
