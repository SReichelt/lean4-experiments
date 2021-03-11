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

structure InstanceIsoCriterion {L : EncodedLambda} (s t : EncodedSigmaExpr L) where
{I : ∀ e : s.α ≃ t.α, Prop}
(h : HasIso s t I)

def IsoCriterion (L : EncodedLambda) := ∀ s t : EncodedSigmaExpr L, InstanceIsoCriterion s t

def isoEquiv {L : EncodedLambda} {s t : EncodedSigmaExpr L} (c : InstanceIsoCriterion s t) :
  SigmaEquiv s t ≃≃ Σ' e : s.α ≃ t.α, c.I e :=
{ toFun    := λ ⟨h₁, h₂⟩ => ⟨h₁, (c.h h₁).mp  h₂⟩,
  invFun   := λ ⟨h₁, h₂⟩ => ⟨h₁, (c.h h₁).mpr h₂⟩,
  leftInv  := λ ⟨h₁, h₂⟩ => rfl,
  rightInv := λ ⟨h₁, h₂⟩ => rfl }



-- Degenerate case: If the instance does not actually depend on the type, an isomorphism is just an
-- equivalence between the types together with an equivalence between the instances.

def independentPairLambda (S T : Structure) : EncodedLambda := ⟨S, constFun T⟩

def IndependentPair (S T : Structure) := EncodedSigmaExpr (independentPairLambda S T)

namespace IndependentPair

variable (S T : Structure)

-- This degenerate case is actually equivalent to `PProd S T`.

def equivProd : IndependentPair S T ≃≃ PProd S.U T.U :=
{ toFun    := λ ⟨x, y⟩ => ⟨x, y⟩,
  invFun   := λ ⟨x, y⟩ => ⟨x, y⟩,
  leftInv  := λ ⟨x, y⟩ => rfl,
  rightInv := λ ⟨x, y⟩ => rfl }

-- The theorem about the instance equivalence.

theorem iso (s t : IndependentPair S T) : HasIso s t (λ e => s.x ≈ t.x) :=
λ e => Iff.refl (s.x ≈ t.x)

def isoCriterion : IsoCriterion (independentPairLambda S T) :=
λ s t => ⟨iso S T s t⟩

-- For this particular case, we can also specialize `isoEquiv` a bit.

def equiv (s t : IndependentPair S T) : SigmaEquiv s t ≃≃ PProd (s.α ≃ t.α) (s.x ≈ t.x) :=
{ toFun    := λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩,
  invFun   := λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩,
  leftInv  := λ ⟨h₁, h₂⟩ => rfl,
  rightInv := λ ⟨h₁, h₂⟩ => rfl }

-- And in particular, if any of the two structures is the unit structure, we just have the equivalence
-- on the other side.

-- TODO

end IndependentPair



-- While in this degenerate case, the left and right side could actually be instances of arbitrary
-- structures, in the following cases we will really consider the left side as a type, so we need it to
-- be a structure, which is our abstraction of a type. In other word, we need it to be an instance of
-- `universeStructure`.
--
-- The target of a `DependentLambda` is always `universeStructure` as well, so now we will be dealing
-- with functors from `universeStructure` to `universeStructure`. This can be regarded as an abstraction
-- of a type class, which is a function between two types.

@[reducible] def UniverseFunctor := StructureFunctor universeStructure universeStructure

def universeLambda (F : UniverseFunctor) : EncodedLambda := ⟨universeStructure, F⟩

def BundledInstance (F : UniverseFunctor) := EncodedSigmaExpr (universeLambda F)

def UniverseIsoCriterion (F : UniverseFunctor) := IsoCriterion (universeLambda F)

namespace BundledInstance



-- First, we define a specialized version of `IndependentPair` under these constraints, i.e. a type
-- together with a constant.

def ConstantInstance (T : Structure) := BundledInstance (constFun T)

namespace ConstantInstance

variable (T : Structure)

theorem iso (s t : IndependentPair universeStructure T) : HasIso s t (λ e => s.x ≈ t.x) :=
IndependentPair.iso universeStructure T s t

def isoCriterion : UniverseIsoCriterion (constFun T) :=
λ s t => ⟨iso T s t⟩

end ConstantInstance



-- Another simple case is that the instance on the right is just a particular instance of the type on the
-- left, i.e. we have a generalized "pointed type" structure. Obviously, in that case an isomorphism
-- should transport the instance along the type equivalence.

def InstanceInstance := BundledInstance idFun

namespace InstanceInstance

def equivSigma : InstanceInstance ≃≃ Σ' S : Structure, S.U :=
{ toFun    := λ ⟨S, x⟩ => ⟨S, x⟩,
  invFun   := λ ⟨S, x⟩ => ⟨S, x⟩,
  leftInv  := λ ⟨S, x⟩ => rfl,
  rightInv := λ ⟨S, x⟩ => rfl }

theorem iso (s t : InstanceInstance) : HasIso s t (λ e => e.toFun s.x ≈ t.x) :=
λ e => setoidInstanceEquiv e s.x t.x

def isoCriterion : UniverseIsoCriterion idFun :=
λ s t => ⟨iso s t⟩

end InstanceInstance



-- The next building block is a bit opaque in its full generality. It covers the case where the instance
-- is a functor from the type into something that is itself represented by a `UniverseFunctor`, i.e. a
-- generalized type class. This is quite a powerful building block because functors are an abstraction of
-- functions, so n-ary operations and relations are just special cases of this and the previous two
-- building blocks composed in different ways.
--
-- This is best explained by considering the main use case where the type is really `α : Sort u` and `F`
-- is a function `Sort u → Sort v`. Then we can consider the function
-- `mapFun F : Sort u → Sort _ := λ α => α → F α`
-- to be a type class that assigns to each `α` a function from `α` to something specified rather freely by
-- `F`.
--
-- For example:
-- * `mapFun (const _ γ)` is a type class that maps `α` to `α → γ`. In particular, if `γ` is `Prop`, we
--   have a unary relation aka subset of `α`.
-- * `mapFun (mapFun (const _ γ))` maps `α` to `α → α → γ`. In particular, if `γ` is `Prop`, we have a
--   binary relation on `α`.
-- * `mapFun id` maps `α` to `α → α`.
-- * `mapFun (mapFun id)` maps `α` to `α → α → α`, i.e. a binary operation.
--
-- To give a general isomorphism criterion for `mapFun F`, we need to consider `F` as a functor again.
-- Then we can prove the following: An `e : α ≃ β` is an isomorphism between `⟨α, f⟩` and `⟨β, g⟩` (with
-- `f : α → _` and `g : β → _`) iff for all `x : α`, `congrArgMap F e` transports `f x` to `g (e x)`.
--
-- Applying this criterion to the examples above, we obtain all familiar special cases, e.g.:
-- * For a function returning a constant, the condition is simply `f x = g (e x)`.
-- * For a binary relation, the condition is `f x y ↔ g (e x) (e y)`.
-- * For a function returning an instance of the type, the condition is `e (f x) = g (e x)`.
-- * For a binary operation, the condition is `e (f x y) = g (e x) (e y)`.
--
-- TODO: We will also need to generalize the left side for e.g. outer operations.
-- Can we generalize to `piStructure`?

def mapFun (F : UniverseFunctor) (S : Structure) := functorStructure (setoidStructure S) (setoidStructure (F S))

def congrArgFunToFun (F : UniverseFunctor) {S T : Structure} (e : SetoidStructureEquiv S T)
  : SetoidStructureFunctor (mapFun F S) (mapFun F T) :=
{ map     := λ f => compFun (compFun e.invFun f) (congrArgMap F e).toFun,
  functor := sorry }  -- TODO: Since we are dealing with setoid functors here, we just need to combine `compFun.congrArg'` etc.

def congrArgFun (F : UniverseFunctor) {S T : Structure} (e : SetoidStructureEquiv S T) :
  SetoidStructureEquiv (mapFun F S) (mapFun F T) :=
{ toFun    := congrArgFunToFun F e,
  invFun   := congrArgFunToFun F (SetoidStructureEquiv.symm e),
  leftInv  := sorry,  -- TODO: This is a bit similar to `DependentEquiv.transport`; maybe we can reuse something.
  rightInv := sorry }

def functorFun (F : UniverseFunctor) : UniverseFunctor :=
{ map     := mapFun F,
  functor := { FF        := congrArgFun F,
               isFunctor := sorry } }

def FunctorInstance (F : UniverseFunctor) := BundledInstance (functorFun F)

namespace FunctorInstance

variable (F : UniverseFunctor)

-- The isomorphism criterion for the functors `s.x` and `t.x`, as described above.

theorem iso (s t : FunctorInstance F) :
  HasIso s t (λ e => ∀ x, InstanceEquiv (congrArgMap F e) (s.x.map x) (t.x.map (e.toFun x))) :=
sorry

-- If we have an isomorphism criterion for `F`, we can combine it with `iso`. This way, we can not only
-- compose the building blocks but also their isomorphism criteria.

theorem iso' (s t : FunctorInstance F) (c : UniverseIsoCriterion F) :
  HasIso s t (λ e => ∀ x, (c ⟨s.α, s.x.map x⟩ ⟨t.α, t.x.map (e.toFun x)⟩).I e) :=
λ e => let h₁ := iso F s t e;
       let h₂ := λ x => (c ⟨s.α, s.x.map x⟩ ⟨t.α, t.x.map (e.toFun x)⟩).h e;
       ⟨λ h x => (h₂ x).mp (h₁.mp h x), λ h => h₁.mpr (λ x => (h₂ x).mpr (h x))⟩

def isoCriterion (c : UniverseIsoCriterion F) : UniverseIsoCriterion (functorFun F) :=
λ s t => ⟨iso' F s t c⟩

end FunctorInstance



-- The previous building blocks give us criteria for the individual fields of a type class. To combine
-- these fields, we need to give an isomorphism criterion for an instance that is a dependent pair.

-- TODO



-- TODO: Prove that, with our generalized definition of a dependent pair, we have a structure equivalence
-- between nested pairs that maps `⟨⟨a, b⟩, c⟩` to `⟨a, ⟨b, c⟩⟩`. Could this become part of a general
-- definition of the word "canonical"?



-- TODO: Also define building blocks for everything we need in order to formalize categories and
-- groupoids, and then define isomorphism for the `HasStructure` type class. This gives us an interesting
-- and probably quite powerful reflection principle. Maybe it will lead to a proof of univalence in the
-- internal logic.

end BundledInstance

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

@[reducible] def TypeClassFunctor := StructureFunctor sortStructure sortStructure

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
