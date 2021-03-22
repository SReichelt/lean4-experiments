import Structure.Basic
import Structure.UniverseFunctor

open Structure
open StructureFunctor
open Forgetfulness



-- `universeStructure` enables us to define functors for the two maps from a structure `T` to the
-- functor structure with `T` on one side, with the restriction that we need to work with setoid
-- structures in most places.

namespace FunctorStructure

@[reducible] def UniverseStructureFunctor := StructureFunctor universeStructure universeStructure

variable (S : Structure)

def outgoingFunctorStructure (T : Structure) := functorStructure S (setoidStructure T)

def outgoingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  SetoidStructureFunctor (outgoingFunctorStructure S T₁) (outgoingFunctorStructure S T₂) :=
makeSetoidStructureFunctor (λ f => compFun f e.toFun) (λ h => compFun.congrArg' h (Setoid.refl _))

def outgoingFunctorDesc : UniverseFunctorDesc universeStructure :=
{ map            := outgoingFunctorStructure S,
  toFun          := outgoingToFun S,
  respectsSetoid := λ h     f => ⟨compFun.congrArg' (Setoid.refl f) h.left⟩,
  respectsComp   := λ e₁ e₂ f => ⟨compFun.assoc' f e₁.toFun e₂.toFun⟩,
  respectsId     := λ T     f => ⟨Setoid.trans (compFun.congrArg' (idFun.leftId' f) (Setoid.refl idFun)) (idFun.leftId' f)⟩,
  respectsInv    := λ e     f => ⟨Setoid.trans (compFun.congrArg' (Setoid.refl f) e.leftInv') (idFun.leftId' f)⟩ }

def outgoingFunctorFunctor : UniverseStructureFunctor := UniverseFunctorDesc.functor (outgoingFunctorDesc S)

def incomingFunctorStructure (T : Structure) := functorStructure (setoidStructure T) S

def incomingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  SetoidStructureFunctor (incomingFunctorStructure S T₁) (incomingFunctorStructure S T₂) :=
makeSetoidStructureFunctor (λ f => compFun e.invFun f) (λ h => compFun.congrArg' (Setoid.refl _) h)

def incomingFunctorDesc : UniverseFunctorDesc universeStructure :=
{ map            := incomingFunctorStructure S,
  toFun          := incomingToFun S,
  respectsSetoid := λ h     f => ⟨compFun.congrArg' h.right (Setoid.refl f)⟩,
  respectsComp   := λ e₁ e₂ f => ⟨compFun.assoc' e₂.invFun e₁.invFun f⟩,
  respectsId     := λ T     f => ⟨Setoid.trans (compFun.congrArg' (Setoid.refl idFun) (idFun.rightId' f)) (idFun.rightId' f)⟩,
  respectsInv    := λ e     f => ⟨Setoid.trans (compFun.congrArg' e.leftInv' (Setoid.refl f)) (idFun.rightId' f)⟩ }

def incomingFunctorFunctor : UniverseStructureFunctor := UniverseFunctorDesc.functor (incomingFunctorDesc S)

end FunctorStructure
