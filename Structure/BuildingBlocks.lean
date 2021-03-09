import Structure.Basic
import Structure.SortStructure

open Morphisms
open Structure
open DependentStructure
open StructureFunctor
open Forgetfulness



universes u v



-- In this file, we define some basic building blocks which are closely related to the cases mentioned in
-- the introduction in `Basic.lean`.

namespace BuildingBlocks

-- We start with abstractions of Π and Σ types where types and instances are replaced with structures.
-- Although Σ may be redundant in theory, it is very important for our use case because bundled instances
-- of type classes are Σ types.

structure EncodedLambda where
(S : Structure)
(C : StructureFunctor S universeStructure)

def toEncodedLambda {S : Structure} (C : StructureFunctor S sortStructure) : EncodedLambda :=
⟨S, compFun C sortToStructureFunctor⟩

structure EncodedPiExpr (L : EncodedLambda) where
(map (α : L.S) : (L.C α).U)

instance (L : EncodedLambda) : CoeFun (EncodedPiExpr L) (λ f => ∀ α : L.S, (L.C α).U) := ⟨EncodedPiExpr.map⟩

structure EncodedSigmaExpr (L : EncodedLambda) where
(α : L.S)
(x : (L.C α).U)

-- Every term of type `∀ x, C x` or `Σ' x, C x` where everything has structures and functors can be
-- converted to an instance of `EncodedPiExpr` or `EncodedSigmaExpr`, respectively.

def encodePiExpr    {α : Sort u} [h : HasStructure α] (C : StructureFunctor (defaultStructure α) sortStructure) (f : ∀  x : α, C x) :
  EncodedPiExpr    (toEncodedLambda C) := ⟨f⟩

def encodeSigmaExpr {α : Sort u} [h : HasStructure α] (C : StructureFunctor (defaultStructure α) sortStructure) (s : Σ' x : α, C x) :
  EncodedSigmaExpr (toEncodedLambda C) := ⟨s.fst, s.snd⟩



-- We can define equivalences between such Π and Σ expressions. These fulfill the isomorphism axioms
-- and thus turn the types `EncodedPiExpr L` and `EncodedSigmaExpr L` into structures.

def PiEquiv {L : EncodedLambda} (f g : EncodedPiExpr L) := DependentEquiv f.map g.map

namespace PiEquiv

variable {L : EncodedLambda}

def refl  (f     : EncodedPiExpr L)                                     : PiEquiv f f :=
DependentEquiv.refl  f.map
def symm  {f g   : EncodedPiExpr L} (φ : PiEquiv f g)                   : PiEquiv g f :=
DependentEquiv.symm  φ
def trans {f g h : EncodedPiExpr L} (φ : PiEquiv f g) (ψ : PiEquiv g h) : PiEquiv f h :=
DependentEquiv.trans φ ψ

def piEquiv (f g : EncodedPiExpr L) := DependentEquiv.dependentEquiv f.map g.map

-- Unfortunately, uncommenting this line (after uncommenting DependentEquiv.dependentEquivHasIso first)
-- causes Lean to hang indefinitely, so we have to copy and paste the code instead.
--instance piEquivHasIso : HasIsomorphisms (@piEquiv T) := @DependentEquiv.dependentEquivHasIso T.S T.C.map

instance piEquivHasIso : HasIsomorphisms (@piEquiv L) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ α => congrArgComp (hφ α) (hψ α),
  assoc        := λ φ ψ χ α => assoc        (φ α) (ψ α) (χ α),
  id           := refl,
  leftId       := λ φ     α => leftId       (φ α),
  rightId      := λ φ     α => rightId      (φ α),
  inv          := symm,
  congrArgInv  := λ hφ    α => congrArgInv  (hφ α),
  leftInv      := λ φ     α => leftInv      (φ α),
  rightInv     := λ φ     α => rightInv     (φ α),
  invInv       := λ φ     α => invInv       (φ α),
  compInv      := λ φ ψ   α => compInv      (φ α) (ψ α),
  idInv        := λ f     α => idInv        (f α) }

end PiEquiv

open PiEquiv

instance piHasStructure (L : EncodedLambda) : HasStructure (EncodedPiExpr L) := ⟨piEquiv⟩
def piStructure (L : EncodedLambda) : Structure := ⟨EncodedPiExpr L⟩



-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence between the types such that `congrArgMap` maps one instance of the type
-- class to the other.

def SigmaEquiv {L : EncodedLambda} (s t : EncodedSigmaExpr L) :=
Σ' e : s.α ≃ t.α, InstanceEquiv (congrArgMap L.C e) s.x t.x

namespace SigmaEquiv

variable {L : EncodedLambda}

def refl  (s     : EncodedSigmaExpr L)                                           : SigmaEquiv s s :=
let h₁ := InstanceEquiv.refl (setoidStructure (L.C s.α)) s.x;
let h₂ := Setoid.symm (respectsId   L.C s.α);
⟨IsEquivalence.refl  s.α,         InstanceEquiv.congrArg h₂ s.x s.x h₁⟩

def symm  {s t   : EncodedSigmaExpr L} (φ : SigmaEquiv s t)                      : SigmaEquiv t s :=
let h₁ := InstanceEquiv.symm (congrArgMap L.C φ.fst) s.x t.x φ.snd;
let h₂ := Setoid.symm (respectsInv  L.C φ.fst);
⟨IsEquivalence.symm  φ.fst,       InstanceEquiv.congrArg h₂ t.x s.x h₁⟩

def trans {r s t : EncodedSigmaExpr L} (φ : SigmaEquiv r s) (ψ : SigmaEquiv s t) : SigmaEquiv r t :=
let h₁ := InstanceEquiv.trans (congrArgMap L.C φ.fst) (congrArgMap L.C ψ.fst) r.x s.x t.x φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp L.C φ.fst ψ.fst);
⟨IsEquivalence.trans φ.fst ψ.fst, InstanceEquiv.congrArg h₂ r.x t.x h₁⟩

-- No need to compare `φ.snd` and `ψ.snd` because they are proofs.
def SigmaEquivEquiv {s t : EncodedSigmaExpr L} (φ ψ : SigmaEquiv s t) := φ.fst ≈ ψ.fst

namespace SigmaEquivEquiv

variable {s t : EncodedSigmaExpr L}

theorem refl  (φ     : SigmaEquiv s t)                                                     : SigmaEquivEquiv φ φ :=
Setoid.refl  φ.fst

theorem symm  {φ ψ   : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ)                           : SigmaEquivEquiv ψ φ :=
Setoid.symm  e

theorem trans {φ ψ χ : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ) (f : SigmaEquivEquiv ψ χ) : SigmaEquivEquiv φ χ :=
Setoid.trans e f

instance sigmaEquivSetoid : Setoid (SigmaEquiv s t) := ⟨SigmaEquivEquiv, ⟨refl, symm, trans⟩⟩

end SigmaEquivEquiv

def sigmaEquiv (s t : EncodedSigmaExpr L) : BundledSetoid := ⟨SigmaEquiv s t⟩

instance sigmaEquivHasIso : HasIsomorphisms (@sigmaEquiv L) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ => congrArgComp hφ hψ,
  assoc        := λ φ ψ χ => assoc        φ.fst ψ.fst χ.fst,
  id           := refl,
  leftId       := λ φ     => leftId       φ.fst,
  rightId      := λ φ     => rightId      φ.fst,
  inv          := symm,
  congrArgInv  := λ hφ    => congrArgInv  hφ,
  leftInv      := λ φ     => leftInv      φ.fst,
  rightInv     := λ φ     => rightInv     φ.fst,
  invInv       := λ φ     => invInv       φ.fst,
  compInv      := λ φ ψ   => compInv      φ.fst ψ.fst,
  idInv        := λ s     => idInv        s.α }

end SigmaEquiv

open SigmaEquiv

instance sigmaHasStructure (L : EncodedLambda) : HasStructure (EncodedSigmaExpr L) := ⟨sigmaEquiv⟩
def sigmaStructure (L : EncodedLambda) : Structure := ⟨EncodedSigmaExpr L⟩



-- If we think of `SigmaEquiv` as defining our concept of isomorphism, we can actually _prove_ that
-- isomorphisms between particular structures match their concrete definitions. This even works for
-- structures that lack an obvious concept of "morphism".
--
-- We will call `EncodedSigmaExpr.α` the "type" and `EncodedSigmaExpr.x` the "instance" (that depends
-- on the type). Correspondingly, `SigmaEquiv.fst` is the "type equivalence", and `SigmaEquiv.snd` is the
-- corresponding "instance equivalence".

namespace AbstractIsomorphism

-- We would like to state our theorems not about the entire `SigmaEquiv` but about how the instance
-- equivalence depends on the type equivalence.
-- Whenever we do want to reason about the entire `SigmaEquiv`, `isoEquiv` will provide the desired
-- result. Although `isoEquiv` is a _definition_ (of an equivalence), it can also be read as the theorem
-- that the two types are equivalent.

def HasIso {L : EncodedLambda} (s t : EncodedSigmaExpr L) (I : ∀ e : s.α ≃ t.α, Prop) :=
∀ e : s.α ≃ t.α, InstanceEquiv (congrArgMap L.C e) s.x t.x ↔ I e

def isoEquiv {L : EncodedLambda} {s t : EncodedSigmaExpr L} {I : ∀ e : s.α ≃ t.α, Prop} (h : HasIso s t I) :
  SigmaEquiv s t ≃≃ Σ' e : s.α ≃ t.α, I e :=
{ toFun    := λ ⟨h₁, h₂⟩ => ⟨h₁, (h h₁).mp  h₂⟩,
  invFun   := λ ⟨h₁, h₂⟩ => ⟨h₁, (h h₁).mpr h₂⟩,
  leftInv  := λ ⟨h₁, h₂⟩ => rfl,
  rightInv := λ ⟨h₁, h₂⟩ => rfl }

-- Degenerate case: If the instance does not actually depend on the type, an isomorphism is just an
-- equivalence between the types together with an equivalence between the instances.

def constantLambda (S T : Structure) : EncodedLambda := ⟨S, constFun T⟩

namespace constantLambda

variable (S T : Structure)

-- This degenerate case is actually equivalent to `PProd S T`.

def equivProd : EncodedSigmaExpr (constantLambda S T) ≃≃ PProd S.U T.U :=
{ toFun    := λ ⟨x, y⟩ => ⟨x, y⟩,
  invFun   := λ ⟨x, y⟩ => ⟨x, y⟩,
  leftInv  := λ ⟨x, y⟩ => rfl,
  rightInv := λ ⟨x, y⟩ => rfl }

-- The theorem about the instance equivalence.

theorem iso (s t : EncodedSigmaExpr (constantLambda S T)) :
  HasIso s t (λ e => s.x ≈ t.x) :=
λ e => Iff.refl (s.x ≈ t.x)

-- For this particular case, we can also specialize `isoEquiv` a bit.

def equiv (s t : EncodedSigmaExpr (constantLambda S T)) :
  SigmaEquiv s t ≃≃ PProd (s.α ≃ t.α) (s.x ≈ t.x) :=
{ toFun    := λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩,
  invFun   := λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩,
  leftInv  := λ ⟨h₁, h₂⟩ => rfl,
  rightInv := λ ⟨h₁, h₂⟩ => rfl }

end constantLambda

-- While in this degenerate case, the left and right side could actually be arbitrary structures, in the
-- following cases we will really consider the left side as a type, in particular we need to work with
-- instances of this type.
--
-- Since in our generalized framework, the instances should actually be arbitrary structure, we represent
-- the type not by an arbitrary structure but by an instance of `universeStructure`.

-- The first such case is that the instance on the right is just a particular instance of the type on the
-- left, i.e. we have a generalized "pointed type" structure. Obviously, in that case an isomorphism
-- should transport the instance along the type equivalence.

def instanceLambda : EncodedLambda := ⟨universeStructure, idFun⟩

namespace instanceLambda

def equivSigma : EncodedSigmaExpr instanceLambda ≃≃ Σ' S : Structure, S.U :=
{ toFun    := λ ⟨S, x⟩ => ⟨S, x⟩,
  invFun   := λ ⟨S, x⟩ => ⟨S, x⟩,
  leftInv  := λ ⟨S, x⟩ => rfl,
  rightInv := λ ⟨S, x⟩ => rfl }

theorem iso (s t : EncodedSigmaExpr instanceLambda) :
  HasIso s t (λ e => e.toFun s.x ≈ t.x) :=
λ e => setoidInstanceEquiv (congrArgMap instanceLambda.C e) s.x t.x

end instanceLambda

end AbstractIsomorphism





-- If we have an `Equiv` with a type that has a structure, we can transport the structure along
-- that `Equiv`.

-- TODO: Do we still need this, or is the use case completely covered by `toTypeClassFunctor`?

instance hasEquivalentStructure {α : Sort u} {β : Sort v} [h : HasStructure β] (e : α ≃≃ β) : HasStructure α :=
{ M := λ a b => h.M (e.toFun a) (e.toFun b),
  h := { comp         := h.h.comp,
         congrArgComp := h.h.congrArgComp,
         assoc        := λ _ _ => h.h.assoc    _ _,
         id           := λ _ => h.h.id _,
         leftId       := λ _   => h.h.leftId   _,
         rightId      := λ _   => h.h.rightId  _,
         inv          := h.h.inv,
         congrArgInv  := h.h.congrArgInv,
         leftInv      := λ _   => h.h.leftInv  _,
         rightInv     := λ _   => h.h.rightInv _,
         invInv       := λ _   => h.h.invInv   _,
         compInv      := λ _ _ => h.h.compInv  _ _,
         idInv        := λ _   => h.h.idInv    _ } }

-- Obviously, this turns the `Equiv` into a `StructureEquiv` between the two structures.

-- TODO



-- If `C` is a type class, we need to show that it is a functor in order to use our abstract framework.
-- We can do that by providing equivalences between `C α` and `D α`, where `D` is already known to be a
-- functor from `sortStructure` to `sortStructure`.

def TypeClass := Sort u → Sort v

def TypeClassEquiv (C D : TypeClass) := ∀ α, C α ≃≃ D α

def TypeClassFunctor := StructureFunctor sortStructure sortStructure

instance : CoeFun TypeClassFunctor (λ F => Sort u → Sort v) := ⟨λ F => F.map⟩

class StructuralTypeClass (C : TypeClass) where
(F : TypeClassFunctor)
(φ : TypeClassEquiv C F.map)

def toTypeClassFunctor (C : TypeClass) [h : StructuralTypeClass C] : TypeClassFunctor :=
proxyFunctor C h.F h.φ



-- A bundled instance of a type class is just a dependent pair. If the type class is a functor, we can
-- build an `EncodedSigmaExpr`, which has a structure.

def bundledStructure (C : TypeClass) [h : StructuralTypeClass C] := sigmaStructure (toEncodedLambda (toTypeClassFunctor C))

def bundled (C : TypeClass) [h : StructuralTypeClass C] (α : Sort u) (x : C α) : bundledStructure C := ⟨α, x⟩

def bundledType     {C : TypeClass} [h : StructuralTypeClass C] (S : bundledStructure C) : Sort u := S.α
def bundledInstance {C : TypeClass} [h : StructuralTypeClass C] (S : bundledStructure C) : C S.α  := S.x



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

end BuildingBlocks

open BuildingBlocks
