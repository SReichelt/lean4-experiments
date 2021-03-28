import Structure.Basic
import Structure.UniverseFunctor

open Structure
open StructureFunctor
open Forgetfulness



-- `universeStructure` enables us to define functors for the two maps from a structure `T` to the
-- functor structure with `T` on one side, with the restriction that we need to work with setoid
-- structures in most places.

namespace FunctorStructure

variable (S : Structure)

def outgoingFunctorStructure (T : Structure) := functorStructure S (setoidStructure T)

def outgoingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  SetoidStructureFunctor (outgoingFunctorStructure S T₁) (outgoingFunctorStructure S T₂) :=
makeSetoidStructureFunctor (λ f => e.toFun ⊙ f) (λ h => compFun.congrArg' h (Setoid.refl _))

def outgoingFunctorDesc : UniverseFunctorDesc universeStructure :=
{ map            := outgoingFunctorStructure S,
  toFun          := outgoingToFun S,
  respectsSetoid := λ h     f => ⟨compFun.congrArg' (functorIsSetoid.refl f) h.left⟩,
  respectsComp   := λ e₁ e₂ f => ⟨compFun.assoc' f e₁.toFun e₂.toFun⟩,
  respectsId     := λ T     f => ⟨idFun.leftId' f⟩ }

def outgoingFunctorFunctor : UniverseStructureFunctor := UniverseFunctorDesc.functor (outgoingFunctorDesc S)

def incomingFunctorStructure (T : Structure) := functorStructure (setoidStructure T) S

def incomingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  SetoidStructureFunctor (incomingFunctorStructure S T₁) (incomingFunctorStructure S T₂) :=
makeSetoidStructureFunctor (λ f => f ⊙ e.invFun) (λ h => compFun.congrArg' (Setoid.refl _) h)

def incomingFunctorDesc : UniverseFunctorDesc universeStructure :=
{ map            := incomingFunctorStructure S,
  toFun          := incomingToFun S,
  respectsSetoid := λ h     f => ⟨compFun.congrArg' h.right (functorIsSetoid.refl f)⟩,
  respectsComp   := λ e₁ e₂ f => ⟨compFun.assoc' e₂.invFun e₁.invFun f⟩,
  respectsId     := λ T     f => ⟨idFun.rightId' f⟩ }

def incomingFunctorFunctor : UniverseStructureFunctor := UniverseFunctorDesc.functor (incomingFunctorDesc S)

end FunctorStructure
