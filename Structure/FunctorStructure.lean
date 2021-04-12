import Structure.Basic
import Structure.Forgetfulness
import Structure.UniverseFunctor

open Morphisms
open Structure
open StructureFunctor
open Forgetfulness
open SetoidStructureFunctor



set_option autoBoundImplicitLocal false



-- `universeStructure` enables us to define functors for the two maps from a structure `T` to the
-- functor structure with `T` on one side.

namespace FunctorStructure

variable (S : Structure)

def outgoingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  StructureFunctor (functorStructure S T₁) (functorStructure S T₂) :=
compFun.congrArgRight.functor S e.toFun

namespace outgoingToFun

def respectsEquiv {T₁ T₂ : Structure} :
  GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure T₁ T₂)
                             (T := functorStructure (functorStructure S T₁) (functorStructure S T₂))
                             (outgoingToFun S) :=
(compFun.congrArgRight.functor.functorFunctor S ⊙ StructureEquiv.toFunProj T₁ T₂).functor

def respectsComp {T₁ T₂ T₃ : Structure} (e : T₁ ≃ T₂) (f : T₂ ≃ T₃) :
  outgoingToFun S (f • e) ≃ outgoingToFun S f ⊙ outgoingToFun S e :=
compFun.congrArgRight.functor.respectsCompFun S e.toFun f.toFun

theorem respectsComp.nat {T₁ T₂ T₃ : Structure} {e₁ e₂ : T₁ ≃ T₂} {f₁ f₂ : T₂ ≃ T₃} (η : e₁ ≃ e₂) (θ : f₁ ≃ f₂) :
  compFun.congrArg (respectsEquiv S η) (respectsEquiv S θ) • respectsComp S e₁ f₁ ≈ respectsComp S e₂ f₂ • respectsEquiv S (StructureEquiv.congrArgComp η θ) :=
compFun.congrArgRight.functor.respectsCompFun.nat S η.toFunEquiv θ.toFunEquiv

def respectsId (T : Structure) :
  outgoingToFun S (id_ T) ≃ @idFun (functorStructure S T) :=
compFun.congrArgRight.functor.respectsIdFun S T

end outgoingToFun

def outgoingFunctorDesc : UniverseStructureFunctorDesc :=
{ map             := λ T => functorStructure S T,
  toFun           := outgoingToFun                  S,
  respectsEquiv   := outgoingToFun.respectsEquiv    S,
  respectsComp    := outgoingToFun.respectsComp     S,
  respectsCompNat := outgoingToFun.respectsComp.nat S,
  respectsId      := outgoingToFun.respectsId       S }

def outgoingFunctorFunctor : UniverseStructureFunctor :=
UniverseStructureFunctorDesc.universeStructureFunctor (outgoingFunctorDesc S)

def incomingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  StructureFunctor (functorStructure T₁ S) (functorStructure T₂ S) :=
compFun.congrArgLeft.functor S e.invFun

namespace incomingToFun

def respectsEquiv {T₁ T₂ : Structure} :
  GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure T₁ T₂)
                             (T := functorStructure (functorStructure T₁ S) (functorStructure T₂ S))
                             (incomingToFun S) :=
(compFun.congrArgLeft.functor.functorFunctor S ⊙ StructureEquiv.invFunProj T₁ T₂).functor

def respectsComp {T₁ T₂ T₃ : Structure} (e : T₁ ≃ T₂) (f : T₂ ≃ T₃) :
  incomingToFun S (f • e) ≃ incomingToFun S f ⊙ incomingToFun S e :=
compFun.congrArgLeft.functor.respectsCompFun S f.invFun e.invFun

theorem respectsComp.nat {T₁ T₂ T₃ : Structure} {e₁ e₂ : T₁ ≃ T₂} {f₁ f₂ : T₂ ≃ T₃} (η : e₁ ≃ e₂) (θ : f₁ ≃ f₂) :
  compFun.congrArg (respectsEquiv S η) (respectsEquiv S θ) • respectsComp S e₁ f₁ ≈ respectsComp S e₂ f₂ • respectsEquiv S (StructureEquiv.congrArgComp η θ) :=
compFun.congrArgLeft.functor.respectsCompFun.nat S θ.invFunEquiv η.invFunEquiv

def respectsId (T : Structure) :
  incomingToFun S (id_ T) ≃ @idFun (functorStructure T S) :=
compFun.congrArgLeft.functor.respectsIdFun S T

end incomingToFun

def incomingFunctorDesc : UniverseStructureFunctorDesc :=
{ map             := λ T => functorStructure T S,
  toFun           := incomingToFun                  S,
  respectsEquiv   := incomingToFun.respectsEquiv    S,
  respectsComp    := incomingToFun.respectsComp     S,
  respectsCompNat := incomingToFun.respectsComp.nat S,
  respectsId      := incomingToFun.respectsId       S }

def incomingFunctorFunctor : UniverseStructureFunctor :=
UniverseStructureFunctorDesc.universeStructureFunctor (incomingFunctorDesc S)

end FunctorStructure
