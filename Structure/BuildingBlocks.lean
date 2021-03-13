import Structure.Basic
import Structure.SortStructure
import Structure.PiSigma

open Morphisms
open Structure
open DependentStructure
open StructureFunctor
open Forgetfulness
open PiSigma



universes u v



-- In this file, we define some basic building blocks which are closely related to the cases mentioned in
-- the introduction in `Basic.lean`.

namespace BuildingBlocks

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

def HasIso {F : StructureDependency} (a b : EncodedSigmaExpr F) (I : ∀ e : a.α ≃ b.α, Prop) :=
∀ e : a.α ≃ b.α, InstanceEquiv (congrArgMap F.F e) a.x b.x ↔ I e

structure InstanceIsoCriterion {F : StructureDependency} (a b : EncodedSigmaExpr F) where
{I : ∀ e : a.α ≃ b.α, Prop}
(h : HasIso a b I)

def IsoCriterion (F : StructureDependency) := ∀ a b : EncodedSigmaExpr F, InstanceIsoCriterion a b

def isoEquiv {F : StructureDependency} {a b : EncodedSigmaExpr F} (c : InstanceIsoCriterion a b) :
  (a ≃ b) ≃≃ Σ' e : a.α ≃ b.α, c.I e :=
{ toFun    := λ ⟨h₁, h₂⟩ => ⟨h₁, (c.h h₁).mp  h₂⟩,
  invFun   := λ ⟨h₁, h₂⟩ => ⟨h₁, (c.h h₁).mpr h₂⟩,
  leftInv  := λ ⟨h₁, h₂⟩ => rfl,
  rightInv := λ ⟨h₁, h₂⟩ => rfl }



-- Degenerate case: If the instance does not actually depend on the type, an isomorphism is just an
-- equivalence between the types together with an equivalence between the instances.

def independentPairDependency (S T : Structure) : StructureDependency := ⟨S, constFun T⟩

def IndependentPair (S T : Structure) := EncodedSigmaExpr (independentPairDependency S T)

namespace IndependentPair

variable (S T : Structure)

-- This degenerate case is actually equivalent to `PProd S T`.

def equivProd : IndependentPair S T ≃≃ PProd S.U T.U :=
{ toFun    := λ ⟨x, y⟩ => ⟨x, y⟩,
  invFun   := λ ⟨x, y⟩ => ⟨x, y⟩,
  leftInv  := λ ⟨x, y⟩ => rfl,
  rightInv := λ ⟨x, y⟩ => rfl }

-- The theorem about the instance equivalence.

theorem iso (a b : IndependentPair S T) : HasIso a b (λ e => a.x ≈ b.x) :=
λ e => Iff.refl (a.x ≈ b.x)

def isoCriterion : IsoCriterion (independentPairDependency S T) := λ a b => ⟨iso S T a b⟩

-- For this particular case, we can also specialize `isoEquiv` a bit.

def equiv (a b : IndependentPair S T) : SigmaEquiv a b ≃≃ PProd (a.α ≃ b.α) (a.x ≈ b.x) :=
{ toFun    := λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩,
  invFun   := λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩,
  leftInv  := λ ⟨h₁, h₂⟩ => rfl,
  rightInv := λ ⟨h₁, h₂⟩ => rfl }

-- And in particular, if any of the two structures is the unit structure, we just have the equivalence
-- on the other side.

-- TODO

end IndependentPair



-- Another simple case is that the instance on the right is just a particular instance of the type on the
-- left, i.e. we have a generalized "pointed type" structure. Obviously, in that case an isomorphism
-- should transport the instance along the type equivalence.

def instanceDependency : StructureDependency := ⟨universeStructure, idFun⟩

def InstanceInstance := EncodedSigmaExpr instanceDependency

namespace InstanceInstance

def equivSigma : InstanceInstance ≃≃ Σ' S : Structure, S.U :=
{ toFun    := λ ⟨S, x⟩ => ⟨S, x⟩,
  invFun   := λ ⟨S, x⟩ => ⟨S, x⟩,
  leftInv  := λ ⟨S, x⟩ => rfl,
  rightInv := λ ⟨S, x⟩ => rfl }

theorem iso (a b : InstanceInstance) : HasIso a b (λ e => e.toFun a.x ≈ b.x) :=
λ e => setoidInstanceEquiv e a.x b.x

def isoCriterion : IsoCriterion instanceDependency := λ a b => ⟨iso a b⟩

end InstanceInstance



-- The next building block is a bit opaque in its full generality. It covers the case where the instance
-- is a functor between two structures that are both obtained from a `StructureDependency`. This is quite
-- a powerful building block because functors are an abstraction of functions, so n-ary operations and
-- relations are just special cases of this and the previous two building blocks composed in different
-- ways.
--
-- This is best explained by considering the main use case where the type is really `α : Sort u` and `F`
-- and `G` are functions `Sort u → Sort _`. Then we can consider the analogue of
-- `functorMap F G : Sort u → Sort _ := λ α => F α → G α` (defined below)
-- to be a type class that assigns to each `α` a function between two types that depend on `α` in a very
-- flexible way.
--
-- For example:
-- * `functorMap id (const _ γ)` is a type class that maps `α` to `α → γ`. In particular, if `γ` is
--   `Prop`, we have a unary relation aka subset of `α`.
-- * `functorMap id (functorMap id (const _ γ))` maps `α` to `α → α → γ`. In particular, if `γ` is `Prop`,
--   we have a binary relation on `α`.
-- * `functorMap id id` maps `α` to `α → α`.
-- * `functorMap id (functorMap id id)` maps `α` to `α → α → α`, i.e. a binary operation.
-- * `functorMap (const _ γ) id` maps `α` to `γ → α`, i.e. we have an instance of `α` that depends on some
--   external constant.
-- * `functorMap (const _ γ) (functorMap id id)` maps `α` to `γ → α → α`, which is an outer operation.
--
-- To give a general isomorphism criterion for `functorMap F G`, we need to consider `F` and `G` as
-- functors again. Then we can prove the following: An `e : α ≃ β` is an isomorphism between `⟨α, f⟩` and
-- `⟨β, g⟩` (with functions `f` and `g`) iff for all `x y : α` such that `congrArgMap F e` transports `x`
-- to `y`, `congrArgMap G e` transports `f x` to `g y`.
--
-- Applying this criterion to the examples above, we obtain all familiar special cases, e.g.:
-- * For a function returning a constant, the condition is simply `f x = g (e x)`.
-- * For a binary relation, the condition is `f x y ↔ g (e x) (e y)`.
-- * For a function returning an instance of the type, the condition is `e (f x) = g (e x)`.
-- * For a binary operation, the condition is `e (f x y) = g (e x) (e y)`.
-- * For an instance depending on a constant `c`, the condition is `e (f c) = g c`.
-- * For an outer operation, the condition is `e (f c x) = g c (e x)`.

section FunctorInstanceDef

variable {S : Structure} (F G : StructureFunctor S universeStructure)

def functorMap (α : S) := setoidFunctorStructure (F α) (G α)

def functorCongrArgToFun {α β : S} (e : α ≃ β) : SetoidStructureFunctor (functorMap F G α) (functorMap F G β) :=
{ map     := λ f => compFun (congrArgMap F e).invFun (compFun f (congrArgMap G e).toFun),
  functor := sorry }  -- TODO: Since we are dealing with setoid functors here, we just need to combine `compFun.congrArg'` etc.

def functorCongrArg {α β : S} (e : α ≃ β) : functorMap F G α ≃ functorMap F G β :=
{ toFun    := functorCongrArgToFun F G e,
  invFun   := functorCongrArgToFun F G e⁻¹,
  leftInv  := sorry,  -- TODO: This is a bit similar to `DependentEquiv.transport`; maybe we can reuse something.
  rightInv := sorry }

def functorFun : StructureFunctor S universeStructure :=
{ map     := functorMap F G,
  functor := { FF        := functorCongrArg F G,
               isFunctor := sorry } }

def functorDependency : StructureDependency := ⟨S, functorFun F G⟩

def FunctorInstance := EncodedSigmaExpr (functorDependency F G)

namespace FunctorInstance

-- The isomorphism criterion for the functors `a.x` and `b.x`, as described above.

theorem iso (a b : FunctorInstance F G) :
  HasIso a b (λ e => ∀ x y, InstanceEquiv (congrArgMap F e) x y → InstanceEquiv (congrArgMap G e) (a.x.map x) (b.x.map y)) :=
λ e => ⟨λ h₁ x y h₂ => let h₃ : compFun (congrArgMap F e).invFun (compFun a.x (congrArgMap G e).toFun) ≈ b.x := h₁;
                       let h₄ : compFun a.x (congrArgMap G e).toFun ≈ compFun (congrArgMap F e).toFun b.x := sorry;
                       let h₅ : (congrArgMap G e).toFun (a.x.map x) ≈ b.x.map ((congrArgMap F e).toFun x) := sorry;
                       let h₆ : (congrArgMap G e).toFun (a.x.map x) ≈ b.x.map y := sorry;
                       (setoidInstanceEquiv (congrArgMap G e) (a.x.map x) (b.x.map y)).mpr h₆,
        sorry⟩

-- If we have isomorphism criteria for `F` and `G`, we can combine them with `iso`. This way, we can not
-- only compose the building blocks but also their isomorphism criteria.

theorem iso' (a b : FunctorInstance F G) (cF : IsoCriterion ⟨S, F⟩) (cG : IsoCriterion ⟨S, G⟩) :
  HasIso a b (λ e => ∀ x y, (cF ⟨a.α, x⟩ ⟨b.α, y⟩).I e → (cG ⟨a.α, a.x.map x⟩ ⟨b.α, b.x.map y⟩).I e) :=
λ e => let h₁ := iso F G a b e;
       let h₂ := λ x y => (cF ⟨a.α, x⟩ ⟨b.α, y⟩).h e;
       let h₃ := λ x y => (cG ⟨a.α, a.x.map x⟩ ⟨b.α, b.x.map y⟩).h e;
       ⟨λ h₄ x y h₅ => (h₃ x y).mp (h₁.mp h₄ x y ((h₂ x y).mpr h₅)),
        λ h₄ => h₁.mpr (λ x y h₅ => (h₃ x y).mpr (h₄ x y ((h₂ x y).mp h₅)))⟩

def isoCriterion (cF : IsoCriterion ⟨S, F⟩) (cG : IsoCriterion ⟨S, G⟩) : IsoCriterion ⟨S, functorFun F G⟩ :=
λ a b => ⟨iso' F G a b cF cG⟩

end FunctorInstance

end FunctorInstanceDef



-- The previous building blocks give us criteria for the individual fields of a type class. To combine
-- these fields, we need to give an isomorphism criterion for an instance that is a dependent pair.
--
-- To specify the isomorphism criterion for `⟨x, y⟩`, we can consider a bundled instance `⟨α, ⟨x, y⟩⟩`
-- canonically as `⟨⟨α, x⟩, y⟩`, as mentioned in the introduction. In this term, we can consider both the
-- inner and the outer pair as a type with an instance, and if we have isomorphism criteria for these, we
-- can combine them into an isomorphism criterion for the original term.

namespace SigmaInstance

-- TODO: Prove that, with our generalized definition of a dependent pair, we have a structure equivalence
-- between nested pairs that maps `⟨⟨a, b⟩, c⟩` to `⟨a, ⟨b, c⟩⟩`. Could this become part of a general
-- definition of the word "canonical"?

end SigmaInstance



-- TODO: Also define building blocks for everything we need in order to formalize categories and
-- groupoids, and then define isomorphism for the `HasStructure` type class. This gives us an interesting
-- and probably quite powerful reflection principle. Maybe it will lead to a proof of univalence in the
-- internal logic.

end AbstractIsomorphism








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

def bundledStructure (C : TypeClass) [h : StructuralTypeClass C] := sigmaStructure (toStructureDependency (toTypeClassFunctor C))

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
