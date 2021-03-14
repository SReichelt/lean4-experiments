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
{ map     := λ F => compFun F e.toFun,
  functor := { FF        := λ h => compFun.congrArg' h (Setoid.refl _),
               isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ => proofIrrel _ _,
                              respectsId     := λ _   => proofIrrel _ _,
                              respectsInv    := λ _   => proofIrrel _ _ } } }

def outgoingFunctorEquiv {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  outgoingFunctorStructure S T₁ ≃ outgoingFunctorStructure S T₂ :=
{ toFun    := outgoingToFun S e,
  invFun   := outgoingToFun S (SetoidStructureEquiv.symm e),
  leftInv  := sorry,
  rightInv := sorry }

def outgoingFunctorFunctor : UniverseStructureFunctor :=
{ map     := outgoingFunctorStructure S,
  functor := { FF        := outgoingFunctorEquiv S,
               isFunctor := sorry } }

def incomingFunctorStructure (T : Structure) := functorStructure (setoidStructure T) S

def incomingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  SetoidStructureFunctor (incomingFunctorStructure S T₁) (incomingFunctorStructure S T₂) :=
{ map     := λ F => compFun e.invFun F,
  functor := { FF        := λ h => compFun.congrArg' (Setoid.refl _) h,
               isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ => proofIrrel _ _,
                              respectsId     := λ _   => proofIrrel _ _,
                              respectsInv    := λ _   => proofIrrel _ _ } } }

def incomingFunctorEquiv {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  incomingFunctorStructure S T₁ ≃ incomingFunctorStructure S T₂ :=
{ toFun    := incomingToFun S e,
  invFun   := incomingToFun S (SetoidStructureEquiv.symm e),
  leftInv  := sorry,
  rightInv := sorry }

def incomingFunctorFunctor : UniverseStructureFunctor :=
{ map     := incomingFunctorStructure S,
  functor := { FF        := incomingFunctorEquiv S,
               isFunctor := sorry } }

end FunctorStructure
