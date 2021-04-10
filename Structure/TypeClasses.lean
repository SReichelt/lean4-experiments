-- TODO: This is partly outdated.



import Structure.Basic
import Structure.SortStructure
import Structure.AbstractPiSigma

open StructureFunctor
open PiSigma



set_option autoBoundImplicitLocal false

universes u v



namespace TypeClasses

-- If `C` is a type class, we need to show that it is a functor in order to use our abstract framework.
-- We can do that by providing equivalences between `C α` and `D α`, where `D` is already known to be a
-- functor from `sortStructure` to `sortStructure`.

def TypeClass := Sort u → Sort v

def TypeClassEquiv (C D : TypeClass) := ∀ α, C α ≃≃ D α

@[reducible] def TypeClassFunctor := StructureFunctor sortStructure sortStructure

class StructuralTypeClass (C : TypeClass) where
(F : TypeClassFunctor)
(φ : TypeClassEquiv C F.map)

def toTypeClassFunctor (C : TypeClass) [h : StructuralTypeClass C] : TypeClassFunctor :=
proxyFunctor C h.F h.φ



-- A bundled instance of a type class is just a dependent pair. If the type class is a functor, we can
-- build a `SigmaExpr`, which has a structure.

def toStructureDependency {S : Structure} (F : StructureFunctor S sortStructure) : StructureDependency :=
⟨S, sortToStructureFunctor ⊙ F⟩

def bundledStructure (C : TypeClass) [h : StructuralTypeClass C] := sigmaStructure (toStructureDependency (toTypeClassFunctor C))

def bundled (C : TypeClass) [h : StructuralTypeClass C] (α : Sort u) (x : C α) : bundledStructure C := ⟨α, x⟩

def bundledType     {C : TypeClass} [h : StructuralTypeClass C] (S : bundledStructure C) : Sort u := S.fst
def bundledInstance {C : TypeClass} [h : StructuralTypeClass C] (S : bundledStructure C) : C S.fst  := S.snd



-- This lets us define isomorphism of two instances of a type class as equivalence of the corresponding
-- bundled structures.

def Isomorphism {C : TypeClass} [h : StructuralTypeClass C] (α : Sort u) (x : C α) (β : Sort u) (y : C β) :=
bundled C α x ≃ bundled C β y

-- From an isomorphism, we can recover the `Equiv` of the types and the condition on the instances.

def isoTypeEquiv {C : TypeClass} [h : StructuralTypeClass C] {α : Sort u} {x : C α} {β : Sort u} {y : C β} (e : Isomorphism α x β y) :
  α ≃≃ β :=
e.fst

def isoInstanceEquiv {C : TypeClass} [h : StructuralTypeClass C] {α : Sort u} {x : C α} {β : Sort u} {y : C β} (e : Isomorphism α x β y) :
  C α ≃ C β :=
congrArgMap (toTypeClassFunctor C) e.fst

theorem isoCondition {C : TypeClass} [h : StructuralTypeClass C] {α : Sort u} {x : C α} {β : Sort u} {y : C β} (e : Isomorphism α x β y) :
-- TODO: Write in terms of `congrArgMap D e.fst`.
  (isoInstanceEquiv e).toFun x = y :=
-- TODO: Need to undo `sortToStructureFunctor`.
sorry --e.snd

end TypeClasses
