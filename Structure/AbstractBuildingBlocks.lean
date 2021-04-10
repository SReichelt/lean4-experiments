-- In this file, we define some basic building blocks which are closely related to the cases mentioned in
-- the introduction in `Structure.lean`.



import Structure.Basic
import Structure.Forgetfulness
import Structure.UniverseFunctor
import Structure.AbstractPiSigma

-- A quick&dirty port of the parts of `data.equiv.basic` we need; should be replaced once it becomes
-- available in Lean 4 mathlib.
import Structure.Data.Equiv

open Morphisms
open Structure
open DependentStructure
open StructureFunctor
open Forgetfulness
open PiSigma
open PiSigmaEquivalences



set_option autoBoundImplicitLocal false

universes u v



namespace BuildingBlocks

-- If we think of `SigmaEquiv` as defining our concept of isomorphism, we can actually _prove_ that
-- isomorphisms between particular structures match their concrete definitions. This even works for
-- structures that lack an obvious concept of "morphism".
--
-- We will call `SigmaExpr.fst` the "type" and `SigmaExpr.snd` the "instance" (that depends on the type).
-- Correspondingly, `SigmaEquiv.fst` is the "type equivalence", and `SigmaEquiv.snd` is the "instance
-- equivalence".

-- We would like to state our theorems not about the entire `SigmaEquiv` but about how the instance
-- equivalence depends on the type equivalence.
-- Whenever we do want to reason about the entire `SigmaEquiv`, `isoEquiv` will provide the desired
-- result. Although `isoEquiv` is a _definition_ (of an equivalence), it can also be read as the theorem
-- that the two types are equivalent.

def HasIso {F : StructureDependency} (a b : SigmaExpr F) (I : ∀ e : a.fst ≃ b.fst, Prop) :=
∀ e : a.fst ≃ b.fst, a.snd ≈[congrArgMap F.F e] b.snd ↔ I e

structure InstanceIsoCriterion {F : StructureDependency} (a b : SigmaExpr F) where
{I : ∀ e : a.fst ≃ b.fst, Prop}
(h : HasIso a b I)

def IsoCriterion (F : StructureDependency) := ∀ a b : SigmaExpr F, InstanceIsoCriterion a b

def isoEquiv {F : StructureDependency} {a b : SigmaExpr F} (c : InstanceIsoCriterion a b) :
  (a ≃ b) ≃≃ Σ' e : a.fst ≃ b.fst, c.I e :=
{ toFun    := λ ⟨h₁, h₂⟩ => ⟨h₁, (c.h h₁).mp  h₂⟩,
  invFun   := λ ⟨h₁, h₂⟩ => ⟨h₁, (c.h h₁).mpr h₂⟩,
  leftInv  := λ ⟨h₁, h₂⟩ => rfl,
  rightInv := λ ⟨h₁, h₂⟩ => rfl }



-- Degenerate case: If the instance does not actually depend on the type, an isomorphism is just an
-- equivalence between the types together with an equivalence between the instances.

def independentPairDependency (S T : Structure) := StructureDependency.constDep S T

def IndependentPair (S T : Structure) := SigmaExpr (independentPairDependency S T)

namespace IndependentPair

variable (S T : Structure)

-- This degenerate case is actually equivalent to `PProd S T`.

def equivProd : IndependentPair S T ≃≃ PProd S.U T.U :=
{ toFun    := λ ⟨x, y⟩ => ⟨x, y⟩,
  invFun   := λ ⟨x, y⟩ => ⟨x, y⟩,
  leftInv  := λ ⟨x, y⟩ => rfl,
  rightInv := λ ⟨x, y⟩ => rfl }

-- The instance equivalence does not depend on the type equivalence.

theorem iso (a b : IndependentPair S T) : HasIso a b (λ e => SetoidEquiv T a.snd b.snd) :=
λ e => Iff.refl (SetoidEquiv T a.snd b.snd)

def isoCriterion : IsoCriterion (independentPairDependency S T) := λ a b => ⟨iso S T a b⟩

-- For this particular case, we can also specialize `isoEquiv` a bit.

def equiv (a b : IndependentPair S T) : SigmaEquiv a b ≃≃ PProd (a.fst ≃ b.fst) (SetoidEquiv T a.snd b.snd) :=
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

def InstanceInstance := SigmaExpr instanceDependency

namespace InstanceInstance

def equivSigma : InstanceInstance ≃≃ Σ' S : Structure, S.U :=
{ toFun    := λ ⟨S, x⟩ => ⟨S, x⟩,
  invFun   := λ ⟨S, x⟩ => ⟨S, x⟩,
  leftInv  := λ ⟨S, x⟩ => rfl,
  rightInv := λ ⟨S, x⟩ => rfl }

theorem iso (a b : InstanceInstance) : HasIso a b (λ e => e.toFun a.snd ≈ b.snd) :=
λ e => SetoidInstanceEquiv.setoidInstanceEquiv e a.snd b.snd

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
-- * `functorMap id id` maps `α` to `α → α`, i.e. a unary operation.
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
-- Applying this criterion to the examples above, we obtain all familiar special cases:
--
--  Example                              | Isomorphism criterion
-- --------------------------------------+-----------------------------
--  Function returning a constant        | `f x = g (e x)`
--  Unary relation                       | `f x ↔ g (e x)`
--  Binary relation                      | `f x y ↔ g (e x) (e y)`
--  Unary operation                      | `e (f x) = g (e x)`
--  Binary operation                     | `e (f x y) = g (e x) (e y)`
--  Instance depending on a constant `c` | `e (f c) = g c`
--  Outer operation                      | `e (f c x) = g c (e x)`

section FunctorInstanceDef

variable {S : Structure} (F G : UniverseFunctor S)

def functorMap (α : S) := functorStructure (F α) (G α)

def functorToFun {α β : S} (e : α ≃ β) : SetoidStructureFunctor (functorMap F G α) (functorMap F G β) :=
{ map     := λ f => ((congrArgMap G e).toFun ⊙ f) ⊙ (congrArgMap F e).invFun,
  functor := sorry }  -- TODO: Since we are dealing with setoid functors here, we just need to combine `compFun.congrArg'` etc.

def functorFunDesc : SetoidUniverseFunctorDesc S :=
{ map            := functorMap   F G,
  toFun          := functorToFun F G,
  respectsSetoid := sorry,
  respectsComp   := sorry,
  respectsId     := sorry }

def functorFun : UniverseFunctor S := SetoidUniverseFunctorDesc.universeFunctor (functorFunDesc F G)

def functorDependency : StructureDependency := ⟨S, functorFun F G⟩

def FunctorInstance := SigmaExpr (functorDependency F G)

namespace FunctorInstance

-- The isomorphism criterion for the functors `a.snd` and `b.snd`, as described above.

theorem iso (a b : FunctorInstance F G) :
  HasIso a b (λ e => ∀ x y, x ≈[congrArgMap F e] y → a.snd.map x ≈[congrArgMap G e] b.snd.map y) :=
--λ e => let f := congrArgMap F e;
--       let g := congrArgMap G e;
--       ⟨λ h₁ x y h₂ => let ⟨h₃⟩ := h₁;
--                       let h₄ : g.toFun ⊙ a.snd ≃ b.snd ⊙ f.toFun := sorry;
--                       let h₅ : g.toFun (a.snd.map x) ≃ b.snd.map (f.toFun x) := h₄.ext x;
--                       let h₆ : g.toFun (a.snd.map x) ≃ b.snd.map y := sorry;
--                       h₆,
--        sorry⟩
sorry

-- If we have isomorphism criteria for `F` and `G`, we can combine them with `iso`. This way, we can not
-- only compose the building blocks but also their isomorphism criteria.

theorem iso' (a b : FunctorInstance F G) (cF : IsoCriterion ⟨S, F⟩) (cG : IsoCriterion ⟨S, G⟩) :
  HasIso a b (λ e => ∀ x y, (cF ⟨a.fst, x⟩ ⟨b.fst, y⟩).I e → (cG ⟨a.fst, a.snd.map x⟩ ⟨b.fst, b.snd.map y⟩).I e) :=
λ e => let h₁ := iso F G a b e;
       let h₂ := λ x y => (cF ⟨a.fst, x⟩ ⟨b.fst, y⟩).h e;
       let h₃ := λ x y => (cG ⟨a.fst, a.snd.map x⟩ ⟨b.fst, b.snd.map y⟩).h e;
       ⟨λ h₄ x y h₅ => (h₃ x y).mp (h₁.mp h₄ x y ((h₂ x y).mpr h₅)),
        λ h₄ => h₁.mpr (λ x y h₅ => (h₃ x y).mpr (h₄ x y ((h₂ x y).mp h₅)))⟩

def isoCriterion (cF : IsoCriterion ⟨S, F⟩) (cG : IsoCriterion ⟨S, G⟩) : IsoCriterion (functorDependency F G) :=
λ a b => ⟨iso' F G a b cF cG⟩

end FunctorInstance

end FunctorInstanceDef



-- TODO: Generalize `FunctorInstance` to `PiExpr`, somewhat similarly to how we treat `SigmaExpr`. This
-- would be useful because ultimately everything is built on Π types.

-- TODO: At least we need to define some simple cases for dependent propositions.



-- The previous building blocks give us criteria for the individual fields of a type class. To combine
-- these fields, we need to give an isomorphism criterion for an instance that is a dependent pair.
--
-- To specify the isomorphism criterion for a dependent pair `⟨x, y⟩`, we can consider a bundled instance
-- `⟨α, ⟨x, y⟩⟩` canonically as `⟨⟨α, x⟩, y⟩`, as mentioned in the introduction. In this term, we can
-- consider both the inner and the outer pair as a type with an instance, and if we have isomorphism
-- criteria for these, we can combine them into an isomorphism criterion for the original term.
--
-- It turns out that our setoid-based formalization prevents us from generically supporting all possible
-- sigma instances on the right by defining a `StructureDependency` for generic sigma types.
-- Therefore, the variables `F` and `G` are based on the variant where the dependent types are nested on
-- the left, and then we convert that to a `StructureDependency` where the structure contained in `F` is
-- moved to the outside.

section SigmaInstanceDef

variable (F : NestedDependency)

def UncurriedSigmaInstance := SigmaExpr (innerPairDependency   F)
def SigmaInstance          := SigmaExpr (nestedSigmaDependency F)

namespace SigmaInstance

def innerPair (a : SigmaInstance F) : SigmaExpr F.fst :=
⟨a.fst, a.snd.fst⟩

def outerPair (a : SigmaInstance F) : UncurriedSigmaInstance F :=
⟨innerPair F a, a.snd.snd⟩

-- TODO: Make use of `PiSigmaEquivalences` here (and finish those first).

def applyInnerEquiv (a b : SigmaInstance F) (e : a.fst ≃ b.fst)
                    (h : InstanceEquiv (congrArgMap F.fst.F e) a.snd.fst b.snd.fst) :
  innerPair F a ≃ innerPair F b :=
sorry

theorem iso (a b : SigmaInstance F) :
  HasIso a b (λ e => ∃ h : InstanceEquiv (congrArgMap F.fst.F e) a.snd.fst b.snd.fst,
                     InstanceEquiv (congrArgMap F.snd (applyInnerEquiv F a b e h)) a.snd.snd b.snd.snd) :=
sorry

def applyInnerEquiv' (a b : SigmaInstance F) (cF : IsoCriterion F.fst) (e : a.fst ≃ b.fst)
                     (h : (cF (innerPair F a) (innerPair F b)).I e) :
  innerPair F a ≃ innerPair F b :=
sorry

theorem iso' (a b : SigmaInstance F) (cF : IsoCriterion F.fst) (cG : IsoCriterion (innerPairDependency F)) :
  HasIso a b (λ e => ∃ h : (cF (innerPair F a) (innerPair F b)).I e,
                     (cG (outerPair F a) (outerPair F b)).I (applyInnerEquiv' F a b cF e h)) :=
sorry

def isoCriterion (cF : IsoCriterion F.fst) (cG : IsoCriterion (innerPairDependency F)) :
  IsoCriterion (nestedSigmaDependency F) :=
λ a b => ⟨iso' F a b cF cG⟩

end SigmaInstance

end SigmaInstanceDef



-- TODO: Also define building blocks for everything we need in order to formalize categories and
-- groupoids, and then define isomorphism for the `HasStructure` type class. This gives us an interesting
-- and probably quite powerful reflection principle. Maybe it will lead to a proof of something like
-- univalence in the internal logic.

end BuildingBlocks

open BuildingBlocks
