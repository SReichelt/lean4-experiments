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
{ map     := λ F => e.toFun ⊙ F,
  functor := { FF        := compFun.congrArgRight,
               isFunctor := { respectsSetoid := λ h   α => respectsSetoid e.toFun (h α),
                              respectsComp   := λ φ ψ α => respectsComp   e.toFun (φ.ext α) (ψ.ext α),
                              respectsId     := λ F   α => respectsId     e.toFun (F α),
                              respectsInv    := λ φ   α => respectsInv    e.toFun (φ.ext α) } } }

namespace outgoingToFun

def respectsEquiv {T₁ T₂ : Structure} :
  GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure T₁ T₂)
                             (T := functorStructure (functorStructure S T₁) (functorStructure S T₂))
                             (outgoingToFun S) :=
{ FF        := λ φ => { ext := λ F => compFun.congrArgLeft (F := F) φ.toFunEquiv,
                        nat := sorry }
  isFunctor := sorry }

def respectsId (T : Structure) :
  outgoingToFun S (StructureEquiv.refl T) ≃ @idFun (functorStructure S T) :=
{ ext := λ F => idFun.leftId F,
  nat := sorry }

def respectsComp {T₁ T₂ T₃ : Structure} (e : T₁ ≃ T₂) (f : T₂ ≃ T₃) :
  outgoingToFun S (StructureEquiv.trans e f) ≃ outgoingToFun S f ⊙ outgoingToFun S e :=
{ ext := λ F => compFun.assoc F e.toFun f.toFun,
  nat := sorry }

end outgoingToFun

def outgoingFunctorDesc : UniverseStructureFunctorDesc :=
{ map           := λ T => functorStructure S T,
  toFun         := outgoingToFun               S,
  respectsEquiv := outgoingToFun.respectsEquiv S,
  respectsComp  := outgoingToFun.respectsComp  S,
  respectsId    := outgoingToFun.respectsId    S }

def outgoingFunctorFunctor : UniverseStructureFunctor :=
UniverseStructureFunctorDesc.universeStructureFunctor (outgoingFunctorDesc S)

def incomingToFun {T₁ T₂ : Structure} (e : T₁ ≃ T₂) :
  StructureFunctor (functorStructure T₁ S) (functorStructure T₂ S) :=
{ map     := λ f => f ⊙ e.invFun,
  functor := { FF        := compFun.congrArgLeft,
               isFunctor := { respectsSetoid := λ h   α => h (e.invFun α),
                              respectsComp   := λ φ ψ α => Setoid.refl (ψ.ext (e.invFun α) • φ.ext (e.invFun α)),
                              respectsId     := λ f   α => Setoid.refl (id_ (f (e.invFun α))),
                              respectsInv    := λ φ   α => Setoid.refl (φ.ext (e.invFun α))⁻¹ } } }

namespace incomingToFun

def respectsEquiv {T₁ T₂ : Structure} :
  GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure T₁ T₂)
                             (T := functorStructure (functorStructure T₁ S) (functorStructure T₂ S))
                             (incomingToFun S) :=
{ FF        := λ φ => { ext := λ F => compFun.congrArgRight (G := F) φ.invFunEquiv,
                        nat := sorry }
  isFunctor := sorry }

def respectsId (T : Structure) :
  incomingToFun S (StructureEquiv.refl T) ≃ @idFun (functorStructure T S) :=
{ ext := λ F => idFun.rightId F,
  nat := sorry }

def respectsComp {T₁ T₂ T₃ : Structure} (e : T₁ ≃ T₂) (f : T₂ ≃ T₃) :
  incomingToFun S (StructureEquiv.trans e f) ≃ incomingToFun S f ⊙ incomingToFun S e :=
{ ext := λ F => compFun.assoc f.invFun e.invFun F,
  nat := sorry }

end incomingToFun

def incomingFunctorDesc : UniverseStructureFunctorDesc :=
{ map           := λ T => functorStructure T S,
  toFun         := incomingToFun               S,
  respectsEquiv := incomingToFun.respectsEquiv S,
  respectsComp  := incomingToFun.respectsComp  S,
  respectsId    := incomingToFun.respectsId    S }

def incomingFunctorFunctor : UniverseStructureFunctor :=
UniverseStructureFunctorDesc.universeStructureFunctor (incomingFunctorDesc S)

end FunctorStructure
