--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- This file contains collections of category-theoretic axioms that are parameterized in such a way that
-- they are suitable for all kinds of categories, groupoids, and higher groupoids.
--
-- Several instances of these axioms can be constructed from basic structures provided by Lean (i.e. Core
-- and a tiny bit of mathlib). These can be found in `Instances.lean`.



import Structure.Generic.Notation

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



-- A type class that says that a given type can be used like `Sort u`, i.e. its instances can be regarded
-- as types. We can also regard this as `V` defining a universe (corresponding to the Lean universe `u`).
-- * The canonical instance is `Sort u` itself (with `Prop` as a special case).
-- * Another common case is `Bundled C` for a type class `C : Sort u → Sort v`.
-- Both examples are defined in `Instances.lean`.

class HasInstances (U : Sort v) : Sort (max (u + 1) v) where
(Inst : U → Sort u)

namespace HasInstances

  instance coeSort (U : Sort v) [s : HasInstances.{u, v} U] : CoeSort U (Sort u) := ⟨s.Inst⟩

  notation "⌈" U:0 "⌉" => HasInstances.Inst U

  instance sortHasInstances : HasInstances.{u, u + 1} (Sort u) := ⟨id⟩

end HasInstances



def GeneralizedTypeClass (U : Type u) [HasInstances.{u, u + 1} U] : Type (max u v) := U → Sort v

structure Bundled {U : Type u} [HasInstances.{u, u + 1} U] (C : GeneralizedTypeClass.{u, v} U) : Type (max u v) where
(α    : U)
[inst : C α]

namespace Bundled

  instance hasInstances {U : Type u} [HasInstances.{u, u + 1} U] (C : GeneralizedTypeClass.{u, v} U) : HasInstances (Bundled C) :=
  ⟨λ S => ⌈S.α⌉⟩

end Bundled



def Universe : Type (u + 1) := Bundled HasInstances.{u, u + 1}

namespace Universe

  instance hasInstances : HasInstances Universe.{u} := Bundled.hasInstances HasInstances

  variable (U : Universe)

  instance instInst : HasInstances U.α := U.inst
  instance : HasInstances ⌈U⌉ := instInst U

end Universe



-- We additionally want "sort-like" types to have some concept of "functors" that map instances. Here, we
-- need to reconcile two conflicting requirements:
--
-- * We want a functor `F : α ⟶ β` with `α β : V` to be an instance of `V`, so that we can chain functors
--   as in `α ⟶ β ⟶ γ`.
--
-- * We axiomatically assert the existence of certain functors such as identity and composition, which we
--   assume to map instances in a specific way. We want this mapping to be a definitional equality so that
--   e.g. applying the identity functor is a trivial operation.
--   This implies that "functoriality" should be extra structure on functions, so that we can say that a
--   given function "is functorial".
--
-- In order to meet both requirements, we define both kinds of functors, and write `α ⟶ β` for the first
-- kind and `α ⟶' β` for a bundled version of the second kind, i.e. a function that is functorial. We
-- assert the equivalence of these two kinds of functors as an axiom.
--
-- In the case of `Bundled C`, we can make sure that `α ⟶' β` is actually an instance of the type class
-- `C`, so we can define `α ⟶ β` to be the same as `α ⟶' β`. However, in the case of `Sort u`, `α ⟶' β`
-- is not an instance of `Sort u` if `u = 0` (i.e. `Sort u` is actually `Prop`).
--
-- Moreover, `α ⟶' β` is defined so that `α` and `β` can live in different universes.

class HasExternalFunctors (U : Universe.{u}) (V : Universe.{v}) : Type (max u v) where
(IsFun {α : U} {β : V} : (α → β) → Sort (max u v))

structure BundledFunctor {U : Universe.{u}} {V : Universe.{v}} [h : HasExternalFunctors U V]
                         (α : U) (β : V) : Sort (max 1 u v) where
(f     : α → β)
(isFun : h.IsFun f)

namespace BundledFunctor

  infixr:20 " ⟶' " => BundledFunctor

  variable {U V : Universe} [h : HasExternalFunctors U V]

  instance coeFun (α : U) (β : V) : CoeFun (α ⟶' β) (λ _ => α → β) := ⟨BundledFunctor.f⟩

  def mkFun {α : U} {β : V} {f : α → β} (hf : h.IsFun f) : α ⟶' β := ⟨f, hf⟩

end BundledFunctor

class HasInternalFunctors (U : Universe.{u}) extends HasExternalFunctors U U : Type u where
(Fun                : U → U → U)
(funEquiv (α β : U) : ⌈Fun α β⌉ ≃ (α ⟶' β))

namespace HasInternalFunctors

  infixr:20 " ⟶ " => HasInternalFunctors.Fun

  variable {U : Universe} [h : HasInternalFunctors U]

  def toBundled   {α β : U} (F : α ⟶  β) : α ⟶' β := (h.funEquiv α β).toFun  F
  def fromBundled {α β : U} (F : α ⟶' β) : α ⟶  β := (h.funEquiv α β).invFun F

  @[simp] theorem fromToBundled {α β : U} (F : α ⟶  β) : fromBundled (toBundled F) = F := (h.funEquiv α β).leftInv  F
  @[simp] theorem toFromBundled {α β : U} (F : α ⟶' β) : toBundled (fromBundled F) = F := (h.funEquiv α β).rightInv F

  def funCoe {α β : U} (F : α ⟶ β) : α → β := (toBundled F).f
  instance (α β : U) : CoeFun ⌈α ⟶ β⌉ (λ _ => α → β) := ⟨funCoe⟩

  -- Workaround for cases where `coeFun` doesn't work.
  notation:max F:max "⟮" x:0 "⟯" => HasInternalFunctors.funCoe F x

  def isFun {α β : U} (F : α ⟶ β) : h.IsFun (funCoe F) := (toBundled F).isFun

  theorem toBundled.eff {α β : U} (F : α ⟶ β) (a : α) : (toBundled F) a = F a := rfl

  @[simp] theorem fromBundled.coe {α β : U} (F : α ⟶' β) : funCoe (fromBundled F) = F.f :=
  congrArg BundledFunctor.f (toFromBundled F)
  @[simp] theorem fromBundled.eff {α β : U} (F : α ⟶' β) (a : α) : (fromBundled F) a = F a :=
  congrFun (fromBundled.coe F) a

  def mkFun {α β : U} {f : α → β} (hf : h.IsFun f) : α ⟶ β := fromBundled (BundledFunctor.mkFun hf)

  @[simp] theorem mkFun.eff {α β : U} {f : α → β} (hf : h.IsFun f) (a : α) :
    (mkFun hf) a = f a :=
  fromBundled.eff (BundledFunctor.mkFun hf) a

end HasInternalFunctors



@[simp] theorem elimRec {α : Sort u} {a a' : α} {ha : a = a'}
                        {T : α → Sort v} {x : T a}
                        {β : Sort w} {f : {a : α} → T a → β} :
  @f a' (ha ▸ x) = f x :=
by subst ha; rfl



-- The following axioms are equivalent to asserting the existence of five functors with specified behavior:
-- id    : `α ⟶ α,                           a ↦ a`
-- const : `β ⟶ (α ⟶ β),                     c ↦ (a ↦ c)`
-- app   : `α ⟶ (α ⟶ β) ⟶ β,                 a ↦ (F ↦ F a)`
-- dup   : `(α ⟶ α ⟶ β) ⟶ (α ⟶ β),           F ↦ (a ↦ F a a)`
-- comp  : `(α ⟶ β) ⟶ (β ⟶ γ) ⟶ (α ⟶ γ),     F ↦ (G ↦ (a ↦ G (F a)))`
--
-- From these, we can construct several other functors such as
-- swap  : `(α ⟶ β ⟶ γ) ⟶ (β ⟶ α ⟶ γ),       F ↦ (b ↦ (a ↦ F a b))`
-- subst : `(α ⟶ β ⟶ γ) ⟶ (α ⟶ β) ⟶ (α ⟶ γ), F ↦ (G ↦ (a ↦ F a (G a)))`
-- Using these, we can give a general algorithm for proving that a function is functorial.

class HasIdFun (U : Universe) [h : HasExternalFunctors U U] where
(idIsFun (α : U) : h.IsFun (λ a : α => a))

namespace HasIdFun

  variable {U : Universe} [HasExternalFunctors U U] [h : HasIdFun U]

  def idFun' (α : U) : α ⟶' α := BundledFunctor.mkFun (h.idIsFun α)

end HasIdFun

class HasConstFun (U V : Universe) [h : HasExternalFunctors U V] where
(constIsFun (α : U) {β : V} (c : β) : h.IsFun (λ a : α => c))

namespace HasConstFun

  variable {U V : Universe} [HasExternalFunctors U V] [h : HasConstFun U V]

  def constFun' (α : U) {β : V} (c : β) : α ⟶' β := BundledFunctor.mkFun (h.constIsFun α c)

end HasConstFun

class HasCompFun (U V W : Universe) [HasExternalFunctors U V] [HasExternalFunctors V W] [h : HasExternalFunctors U W] where
(compIsFun {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) : h.IsFun (λ a : α => G (F a)))

namespace HasCompFun

  variable {U V W : Universe} [HasExternalFunctors U V] [HasExternalFunctors V W] [HasExternalFunctors U W] [h : HasCompFun U V W]

  def compFun' {α : U} {β : V} {γ : W} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶' γ := BundledFunctor.mkFun (h.compIsFun F G)

  def revCompFun' {α : U} {β : V} {γ : W} (G : β ⟶' γ) (F : α ⟶' β) : α ⟶' γ := compFun' F G
  infixr:90 " ⊙' " => HasCompFun.revCompFun'

end HasCompFun



class HasLinearFunOp (U : Universe.{u}) [h : HasInternalFunctors U] extends HasIdFun U, HasCompFun U U U where
(appIsFun        {α : U} (a : α) (β : U)        : h.IsFun (λ F : α ⟶ β     => F a))
(appFunIsFun     (α β : U)                      : h.IsFun (λ a : α         => HasInternalFunctors.mkFun (appIsFun a β)))
(compFunIsFun    {α β : U} (F : α ⟶' β) (γ : U) : h.IsFun (λ G : β ⟶ γ     => HasInternalFunctors.mkFun (compIsFun F (HasInternalFunctors.toBundled G))))
(compFunFunIsFun (α β γ : U)                    : h.IsFun (λ F : α ⟶ β     => HasInternalFunctors.mkFun (compFunIsFun (HasInternalFunctors.toBundled F) γ)))

namespace HasLinearFunOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [h : HasLinearFunOp U]

  def idFun' (α : U) : α ⟶' α := HasIdFun.idFun' α
  def idFun  (α : U) : α ⟶  α := HasInternalFunctors.fromBundled (idFun' α)

  @[simp] theorem idFun.eff (α : U) (a : α) : (idFun α) a = a :=
  by apply HasInternalFunctors.fromBundled.eff

  def appFun' {α : U} (a : α) (β : U) : (α ⟶ β) ⟶' β := BundledFunctor.mkFun (h.appIsFun a β)
  def appFun  {α : U} (a : α) (β : U) : (α ⟶ β) ⟶  β := HasInternalFunctors.fromBundled (appFun' a β)

  @[simp] theorem appFun.eff {α : U} (a : α) (β : U) (F : α ⟶ β) : (appFun a β) F = F a :=
  by apply HasInternalFunctors.fromBundled.eff

  def appFunFun' (α β : U) : α ⟶' (α ⟶ β) ⟶ β := BundledFunctor.mkFun (h.appFunIsFun α β)
  def appFunFun  (α β : U) : α ⟶  (α ⟶ β) ⟶ β := HasInternalFunctors.fromBundled (appFunFun' α β)

  @[simp] theorem appFunFun.eff (α β : U) (a : α) : (appFunFun α β) a = appFun a β :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem appFunFun.effEff (α β : U) (a : α) (F : α ⟶ β) : ((appFunFun α β) a) F = F a :=
  by simp

  def compFun' {α β γ : U} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶' γ := HasCompFun.compFun' F G
  def compFun  {α β γ : U} (F : α ⟶  β) (G : β ⟶  γ) : α ⟶  γ :=
  HasInternalFunctors.fromBundled (compFun' (HasInternalFunctors.toBundled F) (HasInternalFunctors.toBundled G))

  @[simp] theorem compFun.eff {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) (a : α) : (compFun F G) a = G (F a) :=
  by apply HasInternalFunctors.fromBundled.eff

  def compFunFun' {α β : U} (F : α ⟶' β) (γ : U) : (β ⟶ γ) ⟶' (α ⟶ γ) := BundledFunctor.mkFun (h.compFunIsFun F γ)
  def compFunFun  {α β : U} (F : α ⟶  β) (γ : U) : (β ⟶ γ) ⟶  (α ⟶ γ) :=
  HasInternalFunctors.fromBundled (compFunFun' (HasInternalFunctors.toBundled F) γ)

  @[simp] theorem compFunFun.eff {α β : U} (F : α ⟶ β) (γ : U) (G : β ⟶ γ) : (compFunFun F γ) G = compFun F G :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem compFunFun.effEff {α β : U} (F : α ⟶ β) (γ : U) (G : β ⟶ γ) (a : α) : ((compFunFun F γ) G) a = G (F a) :=
  by simp

  def compFunFunFun' (α β γ : U) : (α ⟶ β) ⟶' (β ⟶ γ) ⟶ (α ⟶ γ) := BundledFunctor.mkFun (h.compFunFunIsFun α β γ)
  def compFunFunFun  (α β γ : U) : (α ⟶ β) ⟶  (β ⟶ γ) ⟶ (α ⟶ γ) := HasInternalFunctors.fromBundled (compFunFunFun' α β γ)
  
  @[simp] theorem compFunFunFun.eff (α β γ : U) (F : α ⟶ β) : (compFunFunFun α β γ) F = compFunFun F γ :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem compFunFunFun.effEff (α β γ : U) (F : α ⟶ β) (G : β ⟶ γ) : ((compFunFunFun α β γ) F) G = compFun F G :=
  by simp
  @[simp] theorem compFunFunFun.effEffEff (α β γ : U) (F : α ⟶ β) (G : β ⟶ γ) (a : α) : (((compFunFunFun α β γ) F) G) a = G (F a) :=
  by simp

  -- The "swap" functor swaps the arguments of a nested functor. Its plain version `swapFun` actually
  -- just fixes the second argument.

  def swapIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) : HasExternalFunctors.IsFun (λ a : α => F a b) :=
  h.compIsFun F (appFun' b γ)

  def swapFun' {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) : α ⟶' γ := BundledFunctor.mkFun (swapIsFun F b)
  def swapFun  {α β γ : U} (F : α ⟶  β ⟶ γ) (b : β) : α ⟶  γ := HasInternalFunctors.fromBundled (swapFun' (HasInternalFunctors.toBundled F) b)

  @[simp] theorem swapFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) (a : α) : (swapFun F b) a = F a b :=
  by apply HasInternalFunctors.fromBundled.eff

  theorem swapFunFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) :
    HasInternalFunctors.fromBundled (swapFun' F b) = HasInternalFunctors.fromBundled (HasInternalFunctors.toBundled (appFun b γ) ⊙' F) :=
  HasInternalFunctors.toFromBundled (appFun' b γ) ▸ rfl

  def swapFunIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) : HasExternalFunctors.IsFun (λ b : β => HasInternalFunctors.fromBundled (swapFun' F b)) :=
  funext (swapFunFun.def F) ▸ h.compIsFun (appFunFun' β γ) (compFunFun' F γ)

  def swapFunFun' {α β γ : U} (F : α ⟶' β ⟶ γ) : β ⟶' α ⟶ γ := BundledFunctor.mkFun (swapFunIsFun F)
  def swapFunFun  {α β γ : U} (F : α ⟶  β ⟶ γ) : β ⟶  α ⟶ γ := HasInternalFunctors.fromBundled (swapFunFun' (HasInternalFunctors.toBundled F))

  @[simp] theorem swapFunFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) : (swapFunFun F) b = swapFun F b :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem swapFunFun.effEff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) (a : α) : ((swapFunFun F) b) a = F a b :=
  by simp

  theorem swapFunFunFun.def (α β γ : U) (F : α ⟶ β ⟶ γ) :
    HasInternalFunctors.mkFun (swapFunIsFun (HasInternalFunctors.toBundled F)) = HasInternalFunctors.fromBundled (HasInternalFunctors.toBundled (compFunFun F γ) ⊙' appFunFun' β γ) :=
  HasInternalFunctors.toFromBundled (compFunFun' (HasInternalFunctors.toBundled F) γ) ▸ elimRec

  def swapFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ F : α ⟶ β ⟶ γ => swapFunFun F) :=
  funext (swapFunFunFun.def α β γ) ▸ h.compIsFun (compFunFunFun' α (β ⟶ γ) γ) (compFunFun' (appFunFun' β γ) (α ⟶ γ))

  def swapFunFunFun' (α β γ : U) : (α ⟶ β ⟶ γ) ⟶' (β ⟶ α ⟶ γ) := BundledFunctor.mkFun (swapFunFunIsFun α β γ)
  def swapFunFunFun  (α β γ : U) : (α ⟶ β ⟶ γ) ⟶  (β ⟶ α ⟶ γ) := HasInternalFunctors.fromBundled (swapFunFunFun' α β γ)

  @[simp] theorem swapFunFunFun.eff (α β γ : U) (F : α ⟶ β ⟶ γ) : (swapFunFunFun α β γ) F = swapFunFun F :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem swapFunFunFun.effEff (α β γ : U) (F : α ⟶ β ⟶ γ) (b : β) : ((swapFunFunFun α β γ) F) b = swapFun F b :=
  by simp

  @[simp] theorem swapFunFunFun.effEffEff (α β γ : U) (F : α ⟶ β ⟶ γ) (b : β) (a : α) : (((swapFunFunFun α β γ) F) b) a = F a b :=
  by simp

  -- In particular, reverse composition is also functorial.

  def revCompFun {α β γ : U} (G : β ⟶  γ) (F : α ⟶  β) : α ⟶ γ := compFun F G
  infixr:90 " ⊙ "  => HasLinearFunOp.revCompFun

  @[simp] theorem revCompFun.eff {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) (a : α) : (G ⊙ F) a = G (F a) :=
  compFun.eff F G a

  theorem revCompFunFun.def (α : U) {β γ : U} (G : β ⟶' γ) (F : α ⟶ β) :
    HasInternalFunctors.fromBundled (G ⊙' HasInternalFunctors.toBundled F) = (compFunFun F γ) (HasInternalFunctors.fromBundled G) :=
  Eq.subst (motive := λ H => HasInternalFunctors.fromBundled (H ⊙' HasInternalFunctors.toBundled F) = (compFunFun F γ) (HasInternalFunctors.fromBundled G))
           (HasInternalFunctors.toFromBundled G)
           (Eq.symm (compFunFun.eff F γ (HasInternalFunctors.fromBundled G)))

  def revCompFunIsFun (α : U) {β γ : U} (G : β ⟶' γ) :
    HasExternalFunctors.IsFun (λ F : α ⟶ β => HasInternalFunctors.fromBundled (G ⊙' HasInternalFunctors.toBundled F)) :=
  funext (revCompFunFun.def α G) ▸ swapIsFun (compFunFunFun' α β γ) (HasInternalFunctors.fromBundled G)

  def revCompFunFun' (α : U) {β γ : U} (G : β ⟶' γ) : (α ⟶ β) ⟶' (α ⟶ γ) := BundledFunctor.mkFun (revCompFunIsFun α G)
  def revCompFunFun  (α : U) {β γ : U} (G : β ⟶  γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasInternalFunctors.fromBundled (revCompFunFun' α (HasInternalFunctors.toBundled G))

  @[simp] theorem revCompFunFun.eff (α : U) {β γ : U} (G : β ⟶ γ) (F : α ⟶ β) : (revCompFunFun α G) F = G ⊙ F :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem revCompFunFun.effEff (α : U) {β γ : U} (G : β ⟶ γ) (F : α ⟶ β) (a : α) : ((revCompFunFun α G) F) a = G (F a) :=
  by simp

  theorem revCompFunFunFun.def (α β γ : U) (G : β ⟶ γ) :
    HasInternalFunctors.mkFun (revCompFunIsFun α (HasInternalFunctors.toBundled G)) = HasInternalFunctors.fromBundled (swapFun' (compFunFunFun' α β γ) G) :=
  congrArg (λ H => HasInternalFunctors.fromBundled (swapFun' (compFunFunFun' α β γ) H)) (HasInternalFunctors.fromToBundled G) ▸ elimRec

  def revCompFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ G : β ⟶ γ => revCompFunFun α G) :=
  funext (revCompFunFunFun.def α β γ) ▸ swapFunIsFun (compFunFunFun' α β γ)

  def revCompFunFunFun' (α β γ : U) : (β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := BundledFunctor.mkFun (revCompFunFunIsFun α β γ)
  def revCompFunFunFun  (α β γ : U) : (β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.fromBundled (revCompFunFunFun' α β γ)

  @[simp] theorem revCompFunFunFun.eff (α β γ : U) (G : β ⟶ γ) : (revCompFunFunFun α β γ) G = revCompFunFun α G :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem revCompFunFunFun.effEff (α β γ : U) (G : β ⟶ γ) (F : α ⟶ β) : ((revCompFunFunFun α β γ) G) F = G ⊙ F :=
  by simp

  @[simp] theorem revCompFunFunFun.effEffEff (α β γ : U) (G : β ⟶ γ) (F : α ⟶ β) (a : α) : (((revCompFunFunFun α β γ) G) F) a = G (F a) :=
  by simp

  -- Composition of a function with two arguments.

  def compFun₂ {α β γ δ : U} (F : α ⟶ β ⟶ γ) (G : γ ⟶ δ) : α ⟶ β ⟶ δ := swapFunFun (revCompFunFun α G ⊙ swapFunFun F)

end HasLinearFunOp



class HasSubLinearFunOp (U : Universe.{u}) [h : HasInternalFunctors U] extends HasConstFun U U where
(constFunIsFun (α β : U) : h.IsFun (λ c : β => HasInternalFunctors.mkFun (constIsFun α c)))

namespace HasSubLinearFunOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [h : HasSubLinearFunOp U]

  def constFun' (α : U) {β : U} (c : β) : α ⟶' β := HasConstFun.constFun' α c
  def constFun  (α : U) {β : U} (c : β) : α ⟶  β := HasInternalFunctors.fromBundled (constFun' α c)

  @[simp] theorem constFun.eff (α : U) {β : U} (c : β) (a : α) : (constFun α c) a = c :=
  by apply HasInternalFunctors.fromBundled.eff

  def constFunFun' (α β : U) : β ⟶' (α ⟶ β) := BundledFunctor.mkFun (h.constFunIsFun α β)
  def constFunFun  (α β : U) : β ⟶  (α ⟶ β) := HasInternalFunctors.fromBundled (constFunFun' α β)

  @[simp] theorem constFunFun.eff (α β : U) (c : β) : (constFunFun α β) c = constFun α c :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem constFunFun.effEff (α β : U) (c : β) (a : α) : ((constFunFun α β) c) a = c :=
  by simp

end HasSubLinearFunOp

class HasAffineFunOp (U : Universe.{u}) [h : HasInternalFunctors U] extends HasLinearFunOp U, HasSubLinearFunOp U



class HasNonLinearFunOp (U : Universe.{u}) [h : HasInternalFunctors U] where
(dupIsFun    {α β : U} (F : α ⟶' α ⟶ β) : h.IsFun (λ a : α         => F a a))
(dupFunIsFun (α β : U)                  : h.IsFun (λ F : α ⟶ α ⟶ β => HasInternalFunctors.mkFun (dupIsFun (HasInternalFunctors.toBundled F))))

namespace HasNonLinearFunOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [h : HasNonLinearFunOp U]

  def dupFun' {α β : U} (F : α ⟶' α ⟶ β) : α ⟶' β := BundledFunctor.mkFun (h.dupIsFun F)
  def dupFun  {α β : U} (F : α ⟶  α ⟶ β) : α ⟶  β :=
  HasInternalFunctors.fromBundled (dupFun' (HasInternalFunctors.toBundled F))

  @[simp] theorem dupFun.eff {α β : U} (F : α ⟶ α ⟶ β) (a : α) : (dupFun F) a = F a a :=
  by apply HasInternalFunctors.fromBundled.eff

  def dupFunFun' (α β : U) : (α ⟶ α ⟶ β) ⟶' (α ⟶ β) := BundledFunctor.mkFun (h.dupFunIsFun α β)
  def dupFunFun  (α β : U) : (α ⟶ α ⟶ β) ⟶  (α ⟶ β) := HasInternalFunctors.fromBundled (dupFunFun' α β)

  @[simp] theorem dupFunFun.eff (α β : U) (F : α ⟶ α ⟶ β) : (dupFunFun α β) F = dupFun F :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem dupFunFun.effEff (α β : U) (F : α ⟶ α ⟶ β) (a : α) : ((dupFunFun α β) F) a = F a a :=
  by simp

end HasNonLinearFunOp

class HasFullFunOp (U : Universe.{u}) [h : HasInternalFunctors U] extends HasAffineFunOp U, HasNonLinearFunOp U

namespace HasFullFunOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [h : HasFullFunOp U]

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `H : β ⟶ γ` and an argument `b : β`, then the
  -- construction of `H b` is also functorial.

  theorem substFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) (a : α) :
    F a (G a) = HasInternalFunctors.fromBundled (HasLinearFunOp.swapFun' F (G a)) a :=
  Eq.symm (HasInternalFunctors.fromBundled.eff (HasLinearFunOp.swapFun' F (G a)) a)

  def substIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : HasExternalFunctors.IsFun (λ a : α => F a (G a)) :=
  funext (substFun.def F G) ▸ h.dupIsFun (HasLinearFunOp.swapFunFun' F ⊙' G)

  def substFun' {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : α ⟶' γ := BundledFunctor.mkFun (substIsFun F G)
  def substFun  {α β γ : U} (F : α ⟶  β ⟶ γ) (G : α ⟶  β) : α ⟶  γ := HasInternalFunctors.fromBundled (substFun' (HasInternalFunctors.toBundled F) (HasInternalFunctors.toBundled G))

  @[simp] theorem substFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) : (substFun F G) a = F a (G a) :=
  by apply HasInternalFunctors.fromBundled.eff

  theorem substFunFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶ β) :
    HasInternalFunctors.mkFun (substIsFun F (HasInternalFunctors.toBundled G)) =
    HasInternalFunctors.fromBundled (HasNonLinearFunOp.dupFun' (HasInternalFunctors.toBundled (HasInternalFunctors.fromBundled (HasLinearFunOp.swapFunFun' F ⊙' HasInternalFunctors.toBundled G)))) :=
  HasInternalFunctors.toFromBundled _ ▸ elimRec

  def substFunIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) :
    HasExternalFunctors.IsFun (λ G : α ⟶ β => HasInternalFunctors.fromBundled (substFun' F (HasInternalFunctors.toBundled G))) :=
  funext (substFunFun.def F) ▸ h.compIsFun (HasLinearFunOp.revCompFunFun' α (HasLinearFunOp.swapFunFun' F)) (HasNonLinearFunOp.dupFunFun' α γ)

  def substFunFun' {α β γ : U} (F : α ⟶' β ⟶ γ) : (α ⟶ β) ⟶' (α ⟶ γ) := BundledFunctor.mkFun (substFunIsFun F)
  def substFunFun  {α β γ : U} (F : α ⟶  β ⟶ γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasInternalFunctors.fromBundled (substFunFun' (HasInternalFunctors.toBundled F))

  @[simp] theorem substFunFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) : (substFunFun F) G = substFun F G :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem substFunFun.effEff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) : ((substFunFun F) G) a = F a (G a) :=
  by simp

  theorem substFunFunFun.def (α β γ : U) (F : α ⟶ β ⟶ γ) :
    HasInternalFunctors.mkFun (substFunIsFun (HasInternalFunctors.toBundled F)) = HasInternalFunctors.fromBundled (HasNonLinearFunOp.dupFunFun' α γ ⊙' HasInternalFunctors.toBundled (HasLinearFunOp.revCompFunFun α (HasLinearFunOp.swapFunFun F))) :=
  HasInternalFunctors.toFromBundled _ ▸ HasInternalFunctors.toFromBundled _ ▸ elimRec

  def substFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ F : α ⟶ β ⟶ γ => substFunFun F) :=
  funext (substFunFunFun.def α β γ) ▸ h.compIsFun (HasLinearFunOp.revCompFunFunFun' α β (α ⟶ γ) ⊙' HasLinearFunOp.swapFunFunFun' α β γ)
                                                  (HasLinearFunOp.revCompFunFun' (α ⟶ β) (HasNonLinearFunOp.dupFunFun' α γ))

  def substFunFunFun' (α β γ : U) : (α ⟶ β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := BundledFunctor.mkFun (substFunFunIsFun α β γ)
  def substFunFunFun  (α β γ : U) : (α ⟶ β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.fromBundled (substFunFunFun' α β γ)

  @[simp] theorem substFunFunFun.eff (α β γ : U) (F : α ⟶ β ⟶ γ) : (substFunFunFun α β γ) F = substFunFun F :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem substFunFunFun.effEff (α β γ : U) (F : α ⟶ β ⟶ γ) (G : α ⟶ β) : ((substFunFunFun α β γ) F) G = substFun F G :=
  by simp

  @[simp] theorem substFunFunFun.effEffEff (α β γ : U) (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) : (((substFunFunFun α β γ) F) G) a = F a (G a) :=
  by simp

end HasFullFunOp



-- Using the functoriality axioms and the constructions above, we can algorithmically prove
-- functoriality of lambda terms. The algorithm to prove `HasExternalFunctors.IsFun (λ a : α => t)`
-- is as follows:
--
--  Case                           | Proof
-- --------------------------------+--------------------------------------------------------------
--  `t` does not contain `a`       | `constIsFun α t`
--  `t` is `a`                     | `idIsFun α`
--  `t` is `G b` with `G : β ⟶ γ`: |
--    `a` appears only in `b`      | Prove that `λ a => b` is functorial, yielding a functor
--                                 | `F : α ⟶ β`. Then the proof is `compIsFun F G`.
--      `b` is `a`                 | Optimization: `HasInternalFunctors.isFun G`
--    `a` appears only in `G`      | Prove that `λ a => G` is functorial, yielding a functor
--                                 | `F : α ⟶ β ⟶ γ`. Then the proof is `swapIsFun F b`.
--      `G` is `a`                 | Optimization: `appIsFun b γ`
--    `a` appears in both          | Prove that `λ a => G` is functorial, yielding a functor
--                                 | `F₁ : α ⟶ β ⟶ γ`. Prove that `λ a => b` is functorial,
--                                 | yielding a functor `F₂ : α ⟶ β`. Then the proof is
--                                 | `substIsFun F₁ F₂`.
--  `t` is `mkFun (λ b : β => c)`  | Prove that `λ a => c` is functorial when regarding `b` as
--                                 | a constant, yielding a functor `F : α ⟶ γ` for every `b`.
--                                 | Prove that  `λ b => F` is functorial, yielding a functor
--                                 | `G : β ⟶ α ⟶ γ`. Then the proof is `swapFunIsFun G`.
--
-- (This list does not contain all possible optimizations.)



class HasFunOp (U : Universe.{u}) extends HasInternalFunctors U, HasFullFunOp U : Type u



class HasExternalEquivalences (U : Universe.{u}) (V : Universe.{v})
                              [hUV : HasExternalFunctors U V] [hVU : HasExternalFunctors V U] : Type (max u v) where
(IsEquiv {α : U} {β : V} : (α ⟶' β) → (β ⟶' α) → Sort (max u v))

structure BundledEquivalence {U : Universe.{u}} {V : Universe.{v}}
                             [hUV : HasExternalFunctors U V] [hVU : HasExternalFunctors V U]
                             [h : HasExternalEquivalences U V]
                             (α : U) (β : V) : Sort (max 1 u v) where
(toFun   : α ⟶' β)
(invFun  : β ⟶' α)
(isEquiv : h.IsEquiv toFun invFun)

namespace BundledEquivalence

  infix:20 " ⟷' " => BundledEquivalence

  variable {U V : Universe} [hUV : HasExternalFunctors U V] [hVU : HasExternalFunctors V U]
           [h : HasExternalEquivalences U V]

  def mkEquiv {α : U} {β : V} {to : α ⟶' β} {inv : β ⟶' α} (he : h.IsEquiv to inv) : α ⟷' β :=
  ⟨to, inv, he⟩

end BundledEquivalence

class HasInternalEquivalences (U : Universe.{u}) [h : HasInternalFunctors U] extends HasExternalEquivalences U U : Type u where
(Equiv                          : U → U → U)
(equivEquiv           (α β : U) : ⌈Equiv α β⌉ ≃ (α ⟷' β))
(equivElimToFunIsFun  (α β : U) : h.IsFun (λ E : Equiv α β => HasInternalFunctors.fromBundled ((equivEquiv α β).toFun E).toFun))
(equivElimInvFunIsFun (α β : U) : h.IsFun (λ E : Equiv α β => HasInternalFunctors.fromBundled ((equivEquiv α β).toFun E).invFun))

namespace HasInternalEquivalences

  infix:20 " ⟷ " => HasInternalEquivalences.Equiv

  variable {U : Universe} [HasInternalFunctors U] [h : HasInternalEquivalences U]

  def toBundled   {α β : U} (E : α ⟷  β) : α ⟷' β := (h.equivEquiv α β).toFun  E
  def fromBundled {α β : U} (E : α ⟷' β) : α ⟷  β := (h.equivEquiv α β).invFun E

  @[simp] theorem fromToBundled {α β : U} (E : α ⟷  β) : fromBundled (toBundled E) = E :=
  (h.equivEquiv α β).leftInv  E
  @[simp] theorem toFromBundled {α β : U} (E : α ⟷' β) : toBundled (fromBundled E) = E :=
  (h.equivEquiv α β).rightInv E

  def to  {α β : U} (E : α ⟷ β) (a : α) : β := (toBundled E).toFun  a
  def inv {α β : U} (E : α ⟷ β) (b : β) : α := (toBundled E).invFun b

  def toFun  {α β : U} (E : α ⟷ β) : α ⟶ β := HasInternalFunctors.fromBundled (toBundled E).toFun
  def invFun {α β : U} (E : α ⟷ β) : β ⟶ α := HasInternalFunctors.fromBundled (toBundled E).invFun

  @[simp] theorem toFun.eff  {α β : U} (E : α ⟷ β) (a : α) : (toFun  E) a = to  E a :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem invFun.eff {α β : U} (E : α ⟷ β) (b : β) : (invFun E) b = inv E b :=
  by apply HasInternalFunctors.fromBundled.eff

  def toFunFun'  (α β : U) : (α ⟷ β) ⟶' (α ⟶ β) := BundledFunctor.mkFun (h.equivElimToFunIsFun  α β)
  def invFunFun' (α β : U) : (α ⟷ β) ⟶' (β ⟶ α) := BundledFunctor.mkFun (h.equivElimInvFunIsFun α β)
  def toFunFun   (α β : U) : (α ⟷ β) ⟶  (α ⟶ β) := HasInternalFunctors.fromBundled (toFunFun'  α β)
  def invFunFun  (α β : U) : (α ⟷ β) ⟶  (β ⟶ α) := HasInternalFunctors.fromBundled (invFunFun' α β)

  @[simp] theorem toFunFun.eff  {α β : U} (E : α ⟷ β) : (toFunFun  α β) E = toFun  E :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem invFunFun.eff {α β : U} (E : α ⟷ β) : (invFunFun α β) E = invFun E :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem toFunFun.effEff  {α β : U} (E : α ⟷ β) (a : α) : ((toFunFun  α β) E) a = to  E a :=
  by simp
  @[simp] theorem invFunFun.effEff {α β : U} (E : α ⟷ β) (b : β) : ((invFunFun α β) E) b = inv E b :=
  by simp

  @[simp] theorem toFun.bundledEq  {α β : U} (E : α ⟷ β) : HasInternalFunctors.toBundled (toFun E)  = (toBundled E).toFun :=
  HasInternalFunctors.toFromBundled (toBundled E).toFun
  @[simp] theorem invFun.bundledEq {α β : U} (E : α ⟷ β) : HasInternalFunctors.toBundled (invFun E) = (toBundled E).invFun :=
  HasInternalFunctors.toFromBundled (toBundled E).invFun

  def isEquiv {α β : U} (E : α ⟷ β) : h.IsEquiv (toBundled E).toFun (toBundled E).invFun :=
  (toBundled E).isEquiv

  def isEquiv' {α β : U} (E : α ⟷ β) :
    h.IsEquiv (HasInternalFunctors.toBundled (toFun E)) (HasInternalFunctors.toBundled (invFun E)) :=
  by simp; apply isEquiv

  @[simp] theorem fromBundled.to.coe'  {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).toFun  = E.toFun  :=
  congrArg BundledEquivalence.toFun  (toFromBundled E)
  @[simp] theorem fromBundled.inv.coe' {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).invFun = E.invFun :=
  congrArg BundledEquivalence.invFun (toFromBundled E)
  @[simp] theorem fromBundled.to.coe  {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).toFun.f  = E.toFun.f  :=
  congrArg BundledFunctor.f (fromBundled.to.coe'  E)
  @[simp] theorem fromBundled.inv.coe {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).invFun.f = E.invFun.f :=
  congrArg BundledFunctor.f (fromBundled.inv.coe' E)
  @[simp] theorem fromBundled.to.eff  {α β : U} (E : α ⟷' β) (a : α) : to  (fromBundled E) a = E.toFun  a :=
  congrFun (fromBundled.to.coe  E) a
  @[simp] theorem fromBundled.inv.eff {α β : U} (E : α ⟷' β) (b : β) : inv (fromBundled E) b = E.invFun b :=
  congrFun (fromBundled.inv.coe E) b

  def mkEquiv {α β : U} {to : α ⟶' β} {inv : β ⟶' α} (he : h.IsEquiv to inv) : α ⟷ β :=
  fromBundled (BundledEquivalence.mkEquiv he)

end HasInternalEquivalences

class HasIdEquiv (U : Universe) [HasExternalFunctors U U] [HasIdFun U] [h : HasExternalEquivalences U U] where
(idIsEquiv (α : U) : h.IsEquiv (HasIdFun.idFun' α) (HasIdFun.idFun' α))

namespace HasIdEquiv

  variable {U : Universe} [HasExternalFunctors U U] [HasIdFun U] [HasExternalEquivalences U U] [h : HasIdEquiv U]

  def idEquiv' (α : U) : α ⟷' α := BundledEquivalence.mkEquiv (h.idIsEquiv α)

end HasIdEquiv

class HasCompEquiv (U V W : Universe)
                   [HasExternalFunctors U V] [HasExternalFunctors V W] [HasExternalFunctors U W]
                   [HasExternalFunctors V U] [HasExternalFunctors W V] [HasExternalFunctors W U]
                   [HasCompFun U V W] [HasCompFun W V U]
                   [HasExternalEquivalences U V] [HasExternalEquivalences V W] [h : HasExternalEquivalences U W] where
(compIsEquiv {α : U} {β : V} {γ : W} (E : α ⟷' β) (F : β ⟷' γ) : h.IsEquiv (F.toFun ⊙' E.toFun) (E.invFun ⊙' F.invFun))

namespace HasCompEquiv

  variable {U V W : Universe} [HasExternalFunctors U V] [HasExternalFunctors V W] [HasExternalFunctors U W]
           [HasExternalFunctors V U] [HasExternalFunctors W V] [HasExternalFunctors W U]
           [HasCompFun U V W] [HasCompFun W V U]
           [HasExternalEquivalences U V] [HasExternalEquivalences V W] [HasExternalEquivalences U W]
           [h : HasCompEquiv U V W]

  def compEquiv' {α : U} {β : V} {γ : W} (E : α ⟷' β) (F : β ⟷' γ) : α ⟷' γ := BundledEquivalence.mkEquiv (h.compIsEquiv E F)

end HasCompEquiv

class HasInvEquiv (U V : Universe) [HasExternalFunctors U V] [HasExternalFunctors V U]
                  [HasExternalEquivalences U V] [h : HasExternalEquivalences V U] where
(invIsEquiv {α : U} {β : V} (E : α ⟷' β) : h.IsEquiv E.invFun E.toFun)

namespace HasInvEquiv

  variable {U V : Universe} [HasExternalFunctors U V] [HasExternalFunctors V U]
           [HasExternalEquivalences U V] [HasExternalEquivalences V U] [h : HasInvEquiv U V]

  def invEquiv' {α : U} {β : V} (E : α ⟷' β) : β ⟷' α := BundledEquivalence.mkEquiv (h.invIsEquiv E)

end HasInvEquiv

class HasEquivOp (U : Universe.{u}) [h : HasInternalFunctors U] [HasLinearFunOp U] extends
  HasInternalEquivalences U, HasIdEquiv U, HasCompEquiv U U U, HasInvEquiv U U : Type u where
(compEquivIsFun    {α β : U} (E : α ⟷' β) (γ : U) : h.IsFun (λ F : β ⟷ γ => HasInternalEquivalences.mkEquiv (compIsEquiv E (HasInternalEquivalences.toBundled F))))
(compEquivFunIsFun (α β γ : U)                    : h.IsFun (λ E : α ⟷ β => HasInternalFunctors.mkFun (compEquivIsFun (HasInternalEquivalences.toBundled E) γ)))
(invEquivIsFun     (α β : U)                      : h.IsFun (λ E : α ⟷ β => HasInternalEquivalences.mkEquiv (invIsEquiv (HasInternalEquivalences.toBundled E))))
(invEquivIsEquiv   (α β : U)                      : IsEquiv (BundledFunctor.mkFun (invEquivIsFun α β)) (BundledFunctor.mkFun (invEquivIsFun β α)))

namespace HasEquivOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [HasLinearFunOp U] [h : HasEquivOp U]

  def idEquiv' (α : U) : α ⟷' α := HasIdEquiv.idEquiv' α
  def idEquiv  (α : U) : α ⟷  α := HasInternalEquivalences.fromBundled (idEquiv' α)

  @[simp] theorem idEquiv.to.eff  (α : U) (a : α) : HasInternalEquivalences.to  (idEquiv α) a = a :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem idEquiv.inv.eff (α : U) (a : α) : HasInternalEquivalences.inv (idEquiv α) a = a :=
  by apply HasInternalEquivalences.fromBundled.inv.eff

  def compEquiv' {α β γ : U} (E : α ⟷' β) (F : β ⟷' γ) : α ⟷' γ := HasCompEquiv.compEquiv' E F
  def compEquiv  {α β γ : U} (E : α ⟷  β) (F : β ⟷  γ) : α ⟷  γ :=
  HasInternalEquivalences.fromBundled (compEquiv' (HasInternalEquivalences.toBundled E) (HasInternalEquivalences.toBundled F))

  @[simp] theorem compEquiv.to.eff  {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) (a : α) :
    HasInternalEquivalences.to  (compEquiv E F) a = HasInternalEquivalences.to  F (HasInternalEquivalences.to  E a) :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem compEquiv.inv.eff {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) (c : γ) :
    HasInternalEquivalences.inv (compEquiv E F) c = HasInternalEquivalences.inv E (HasInternalEquivalences.inv F c) :=
  by apply HasInternalEquivalences.fromBundled.inv.eff

  def compEquivFun' {α β : U} (E : α ⟷' β) (γ : U) : (β ⟷ γ) ⟶' (α ⟷ γ) := BundledFunctor.mkFun (h.compEquivIsFun E γ)
  def compEquivFun  {α β : U} (E : α ⟷  β) (γ : U) : (β ⟷ γ) ⟶  (α ⟷ γ) :=
  HasInternalFunctors.fromBundled (compEquivFun' (HasInternalEquivalences.toBundled E) γ)

  @[simp] theorem compEquivFun.eff {α β : U} (E : α ⟷ β) (γ : U) (F : β ⟷ γ) : (compEquivFun E γ) F = compEquiv E F :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem compEquivFun.to.effEff  {α β : U} (E : α ⟷ β) (γ : U) (F : β ⟷ γ) (a : α) :
    HasInternalEquivalences.to  ((compEquivFun E γ) F) a = HasInternalEquivalences.to  F (HasInternalEquivalences.to  E a) :=
  by simp
  @[simp] theorem compEquivFun.inv.effEff {α β : U} (E : α ⟷ β) (γ : U) (F : β ⟷ γ) (c : γ) :
    HasInternalEquivalences.inv ((compEquivFun E γ) F) c = HasInternalEquivalences.inv E (HasInternalEquivalences.inv F c) :=
  by simp

  def compEquivFunFun' (α β γ : U) : (α ⟷ β) ⟶' (β ⟷ γ) ⟶ (α ⟷ γ) := BundledFunctor.mkFun (h.compEquivFunIsFun α β γ)
  def compEquivFunFun  (α β γ : U) : (α ⟷ β) ⟶  (β ⟷ γ) ⟶ (α ⟷ γ) := HasInternalFunctors.fromBundled (compEquivFunFun' α β γ)
  
  @[simp] theorem compEquivFunFun.eff (α β γ : U) (E : α ⟷ β) : (compEquivFunFun α β γ) E = compEquivFun E γ :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem compEquivFunFun.effEff (α β γ : U) (E : α ⟷ β) (F : β ⟷ γ) : ((compEquivFunFun α β γ) E) F = compEquiv E F :=
  by simp
  @[simp] theorem compEquivFunFun.to.effEffEff  (α β γ : U) (E : α ⟷ β) (F : β ⟷ γ) (a : α) :
    HasInternalEquivalences.to  (((compEquivFunFun α β γ) E) F) a = HasInternalEquivalences.to  F (HasInternalEquivalences.to  E a) := by simp
  @[simp] theorem compEquivFunFun.inv.effEffEff (α β γ : U) (E : α ⟷ β) (F : β ⟷ γ) (c : γ) :
    HasInternalEquivalences.inv (((compEquivFunFun α β γ) E) F) c = HasInternalEquivalences.inv E (HasInternalEquivalences.inv F c) := by simp

  def invEquiv' {α β : U} (E : α ⟷' β) : β ⟷' α := HasInvEquiv.invEquiv' E
  def invEquiv  {α β : U} (E : α ⟷  β) : β ⟷  α :=
  HasInternalEquivalences.fromBundled (invEquiv' (HasInternalEquivalences.toBundled E))

  @[simp] theorem invEquiv.to.eff  {α β : U} (E : α ⟷ β) (b : β) : HasInternalEquivalences.to  (invEquiv E) b = HasInternalEquivalences.inv E b :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem invEquiv.inv.eff {α β : U} (E : α ⟷ β) (a : α) : HasInternalEquivalences.inv (invEquiv E) a = HasInternalEquivalences.to  E a :=
  by apply HasInternalEquivalences.fromBundled.inv.eff

  def invEquivFun' (α β : U) : (α ⟷ β) ⟶' (β ⟷ α) := BundledFunctor.mkFun (h.invEquivIsFun α β)
  def invEquivFun  (α β : U) : (α ⟷ β) ⟶  (β ⟷ α) := HasInternalFunctors.fromBundled (invEquivFun' α β)

  @[simp] theorem invEquivFun.eff (α β : U) (E : α ⟷ β) : (invEquivFun α β) E = invEquiv E :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem invEquivFun.to.effEff  (α β : U) (E : α ⟷ β) (b : β) :
    HasInternalEquivalences.to  ((invEquivFun α β) E) b = HasInternalEquivalences.inv E b := by simp
  @[simp] theorem invEquivFun.inv.effEff (α β : U) (E : α ⟷ β) (a : α) :
    HasInternalEquivalences.inv ((invEquivFun α β) E) a = HasInternalEquivalences.to  E a := by simp

  def invEquivEquiv' (α β : U) : (α ⟷ β) ⟷' (β ⟷ α) := BundledEquivalence.mkEquiv (h.invEquivIsEquiv α β)
  def invEquivEquiv  (α β : U) : (α ⟷ β) ⟷  (β ⟷ α) := HasInternalEquivalences.fromBundled (invEquivEquiv' α β)

  @[simp] theorem invEquivEquiv.to.eff  (α β : U) (E : α ⟷ β) : HasInternalEquivalences.to  (invEquivEquiv α β) E = invEquiv E :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem invEquivEquiv.inv.eff (α β : U) (E : β ⟷ α) : HasInternalEquivalences.inv (invEquivEquiv α β) E = invEquiv E :=
  by apply HasInternalEquivalences.fromBundled.inv.eff
  @[simp] theorem invEquivEquiv.to.to.effEff   (α β : U) (E : α ⟷ β) (b : β) :
    HasInternalEquivalences.to  (HasInternalEquivalences.to  (invEquivEquiv α β) E) b = HasInternalEquivalences.inv E b := by simp
  @[simp] theorem invEquivEquiv.to.inv.effEff  (α β : U) (E : α ⟷ β) (a : α) :
    HasInternalEquivalences.inv (HasInternalEquivalences.to  (invEquivEquiv α β) E) a = HasInternalEquivalences.to  E a := by simp
  @[simp] theorem invEquivEquiv.inv.to.effEff  (α β : U) (E : β ⟷ α) (a : α) :
    HasInternalEquivalences.to  (HasInternalEquivalences.inv (invEquivEquiv α β) E) a = HasInternalEquivalences.inv E a := by simp
  @[simp] theorem invEquivEquiv.inv.inv.effEff (α β : U) (E : β ⟷ α) (b : β) :
    HasInternalEquivalences.inv (HasInternalEquivalences.inv (invEquivEquiv α β) E) b = HasInternalEquivalences.to  E b := by simp

end HasEquivOp



def ExternalProduct {U : Universe.{u}} {V : Universe.{v}} (α : U) (β : V) := PProd ⌈α⌉ ⌈β⌉

namespace ExternalProduct

  infixr:35 " ⊓' " => ExternalProduct

end ExternalProduct

class HasInternalProducts (U : Universe.{u}) [h : HasExternalFunctors U U] where
(Prod                                                   : U → U → U)
(prodEquiv        (α β : U)                             : ⌈Prod α β⌉ ≃ (α ⊓' β))
(prodIntroIsFun   {α β ω : U} (F : ω ⟶' α) (G : ω ⟶' β) : h.IsFun (λ a : ω => (prodEquiv α β).invFun ⟨F a, G a⟩))
(prodElimFstIsFun (α β : U)                             : h.IsFun (λ P : Prod α β => ((prodEquiv α β).toFun P).fst))
(prodElimSndIsFun (α β : U)                             : h.IsFun (λ P : Prod α β => ((prodEquiv α β).toFun P).snd))

namespace HasInternalProducts

  infixr:35 " ⊓ " => HasInternalProducts.Prod

end HasInternalProducts

-- TODO: Add a type class that says that the combination of intro and elim are equivalences (when the other side is fixed).
-- Prove that this is an equivalence between U and U ⨯ U.



class HasEmptyType (U : Universe.{u}) [h : HasExternalFunctors U U] where
(Empty                  : U)
(emptyIsEmpty           : ⌈Empty⌉ → False)
(emptyElimIsFun (α : U) : h.IsFun (λ e : Empty => @False.elim ⌈α⌉ (emptyIsEmpty e)))

namespace HasEmptyType

  variable {U : Universe}
  
  def emptyElimFun' [HasExternalFunctors U U] [h : HasEmptyType U] (α : U) : h.Empty ⟶' α :=
  BundledFunctor.mkFun (h.emptyElimIsFun α)
  def emptyElimFun  [HasInternalFunctors U]   [h : HasEmptyType U] (α : U) : h.Empty ⟶  α :=
  HasInternalFunctors.fromBundled (emptyElimFun' α)

  def Not [HasInternalFunctors U] [h : HasEmptyType U] (α : U) := α ⟶ h.Empty

end HasEmptyType

-- TODO: Can we prove `α ⟶ Not α ⟶ β`?

class HasClassicalLogic (U : Universe.{u}) [HasInternalFunctors U] [h : HasEmptyType U] where
(byContradiction (α : U) : HasEmptyType.Not (HasEmptyType.Not α) ⟶ α)



class HasUnitType (U : Universe.{u}) [h : HasExternalFunctors U U] where
(Unit                   : U)
(unit                   : Unit)
(unitIntroIsFun (α : U) : h.IsFun (λ a : α => unit))

namespace HasUnitType

  variable {U : Universe}
  
  def unitIntroFun' [HasExternalFunctors U U] [h : HasUnitType U] (α : U) : α ⟶' h.Unit :=
  BundledFunctor.mkFun (h.unitIntroIsFun α)
  def unitIntroFun  [HasInternalFunctors U]   [h : HasUnitType U] (α : U) : α ⟶  h.Unit :=
  HasInternalFunctors.fromBundled (unitIntroFun' α)

  @[simp] theorem unitIntroFun.eff [HasInternalFunctors U] [h : HasUnitType U] (α : U) (a : α) :
    (unitIntroFun α) a = h.unit :=
  by apply HasInternalFunctors.fromBundled.eff

end HasUnitType



-- TODO: Derive some logic and especially the arrow/product laws.



def GeneralizedProperty (α : Sort u) (V : Universe.{v}) := α → V

namespace GeneralizedProperty

  variable {α : Sort u} {V : Universe.{v}}

  instance hasInstances : HasInstances (GeneralizedProperty α V) := ⟨λ P => ∀ a, P a⟩

  section Properties

    variable (P : GeneralizedProperty α V)

    class HasInst where
    (inst (a : α) : P a)

  end Properties

end GeneralizedProperty

open GeneralizedProperty



-- TODO: Update comments

-- We want to formalize a very general "structure with equivalences", so we start with a very basic
-- abstraction for something that looks like an equivalence relation except that the codomain is
-- generalized to `Sort u` instead of `Prop`. Therefore, `⟨Equiv.refl, Equiv.symm, Equiv.trans⟩`, where
-- `Equiv` is the Lean 4 version of the `equiv` type in Lean 3 mathlib, is also an instance of this type
-- (with the restriction that both arguments must live in the same universe).
--
-- We actually need to generalize slightly further to a codomain that is not necessarily a sort but can be
-- coerced to a sort. This way, the codomain can be any Lean structure that bundles a sort, in particular
-- it can be our `Structure` type.

def GeneralizedRelation (α : Sort u) (V : Universe.{v}) := α → α → V

namespace GeneralizedRelation

  variable {α : Sort u} {V : Universe.{v}}

  instance hasInstances : HasInstances (GeneralizedRelation α V) := ⟨λ R => ∀ a b, R a b⟩

  section Properties

    variable (R : GeneralizedRelation α V)

    class HasRefl where
    (refl (a : α) : R a a)

    variable [HasInternalFunctors V]

    class HasTrans where
    (trans {a b c : α} : R a b ⟶ R b c ⟶ R a c)

    class IsPreorder extends HasRefl R, HasTrans R

    variable [HasInternalEquivalences V]

    class HasSymm where
    (symm {a b : α} : R a b ⟷ R b a)

    class IsEquivalence extends IsPreorder R, HasSymm R
  
  end Properties

  def HasTrans.revTrans {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasLinearFunOp V] [h : HasTrans R]
                        {a b c : α} : R b c ⟶ R a b ⟶ R a c :=
  HasLinearFunOp.swapFunFun h.trans

  @[simp] theorem HasTrans.revTrans.eff {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasLinearFunOp V] [h : HasTrans R]
                                        {a b c : α} (g : R b c) (f : R a b) :
    h.revTrans g f = h.trans f g :=
  by apply HasLinearFunOp.swapFunFun.effEff

  def HasTrans.trans' {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasTrans R]
                      {a b c : α} (f : R a b) (g : R b c) : R a c := h.trans f g

  def HasSymm.symm' {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasInternalEquivalences V] [h : HasSymm R]
                    {a b : α} (f : R a b) : R b a := HasInternalEquivalences.to h.symm f

  -- When reasoning about instances of `R a b`, we would like to write `trans` as composition, `refl` as
  -- identity, and `symm` as inverse.
  -- Note that `R` can be inferred from `f : R a b` by elaboration.

  section Notation

    @[reducible] def revComp {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasTrans R] {a b c : α} (g : R b c) (f : R a b) : R a c := h.trans' f g
    infixr:90 " • " => revComp

    @[reducible] def ident (R : GeneralizedRelation α V) [h : HasRefl R] (a : α) : R a a := h.refl a

    @[reducible] def inv {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasInternalEquivalences V] [h : HasSymm R] {a b : α} (f : R a b) : R b a := h.symm' f
    postfix:max "⁻¹" => inv

  end Notation

end GeneralizedRelation

open GeneralizedRelation



-- TODO: Do we want to more dependent properties and relations to a separate file?

def GeneralizedDependentProperty {U V : Universe} (P : GeneralizedProperty ⌈U⌉ V) (W : Universe) :=
∀ {α}, P α → (α → W)

namespace GeneralizedDependentProperty

  variable {U V : Universe} {P : GeneralizedProperty ⌈U⌉ V} {W : Universe}

  section Properties

    variable (D : GeneralizedDependentProperty P W)

    class HasDependentInst [h : HasInst P] where
    (inst {α : U} (a : α) : D (h.inst α) a)

    def instProp [h : HasInst P] (α : U) : GeneralizedProperty ⌈α⌉ W := D (h.inst α)
    instance [HasInst P] [h : HasDependentInst D] (α : U) : HasInst (instProp D α) := ⟨h.inst⟩

  end Properties

end GeneralizedDependentProperty

open GeneralizedDependentProperty



def GeneralizedDependentRelation {U V : Universe} (R : GeneralizedRelation ⌈U⌉ V) (W : Universe) :=
∀ {α β}, R α β → (α → β → W)

namespace GeneralizedDependentRelation

  variable {U V : Universe} {R : GeneralizedRelation ⌈U⌉ V} {W : Universe}

  section Properties

    variable (D : GeneralizedDependentRelation R W)

    class HasDependentRefl [h : HasRefl R] where
    (refl {α : U} (a : α) : D (h.refl α) a a)

    def reflRel [h : HasRefl R] (α : U) : GeneralizedRelation ⌈α⌉ W := D (h.refl α)
    instance [HasRefl R] [h : HasDependentRefl D] (α : U) : HasRefl (reflRel D α) := ⟨h.refl⟩

    variable [HasInternalFunctors V] [HasInternalFunctors W]

    class HasDependentTrans [h : HasTrans R] where
    (trans {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} : D F a b ⟶ D G b c ⟶ D (h.trans' F G) a c)

    class IsDependentPreorder [h : IsPreorder R] extends HasDependentRefl D, HasDependentTrans D

    variable [HasInternalEquivalences V] [HasInternalEquivalences W]

    class HasDependentSymm [h : HasSymm R] where
    (symm {α β : U} {F : R α β} {a : α} {b : β} : D F a b ⟷ D (h.symm' F) b a)

    class IsDependentEquivalence [h : IsEquivalence R] extends IsDependentPreorder D, HasDependentSymm D

  end Properties

  def HasDependentTrans.trans' {D : GeneralizedDependentRelation R W}
                               [HasInternalFunctors V] [HasInternalFunctors W] [HasTrans R] [h : HasDependentTrans D]
                               {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (f : D F a b) (g : D G b c) :
    D (HasTrans.trans' F G) a c :=
  h.trans f g

  def HasDependentSymm.symm' {D : GeneralizedDependentRelation R W}
                             [HasInternalFunctors V] [HasInternalFunctors W] [HasInternalEquivalences V] [HasInternalEquivalences W]
                             [HasSymm  R] [h : HasDependentSymm  D]
                             {α β : U} {F : R α β} {a : α} {b : β} (f : D F a b) :
   D (HasSymm.symm' F) b a :=
  HasInternalEquivalences.to h.symm f

  section Notation

    @[reducible] def depRevComp {D : GeneralizedDependentRelation R W} [HasInternalFunctors V] [HasInternalFunctors W]
                                [HasTrans R] [h : HasDependentTrans D]
                                {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (g : D G b c) (f : D F a b) :
      D (G • F) a c :=
    h.trans' f g
    -- TODO: What is the correct way to overload this?
    --infixr:90 " • " => depRevComp

    @[reducible] def depIdent (D : GeneralizedDependentRelation R W) [HasRefl R] [h : HasDependentRefl D] {α : U} (a : α) :
      D (ident R α) a a :=
    h.refl a

    @[reducible] def depInv {D : GeneralizedDependentRelation R W}
                            [HasInternalFunctors V] [HasInternalFunctors W] [HasInternalEquivalences V] [HasInternalEquivalences W]
                            [HasSymm R] [h : HasDependentSymm D]
                            {α β : U} {F : R α β} {a : α} {b : β} (f : D F a b) :
      D F⁻¹ b a :=
    h.symm' f
    --postfix:max "⁻¹" => depInv

  end Notation

end GeneralizedDependentRelation

open GeneralizedDependentRelation



-- We can attach products, arrows, and/or equivalences to a given sort, in the form of generalized
-- relations satisfying appropriate properties.

section AttachedRelations

  variable (α : Sort u) (V : Universe.{v}) [HasInternalFunctors V]

  class HasArrows where
  (Arrow      : GeneralizedRelation α V)
  [isPreorder : IsPreorder Arrow]

  namespace HasArrows
    variable [h : HasArrows α V]
    instance arrowPreorder : IsPreorder h.Arrow := h.isPreorder
    instance hasArrow : HasArrow α α := ⟨h.Arrow⟩
    instance : HasInstances (HasArrow.γ α α) := Universe.instInst V
    instance : IsPreorder (@HasArrow.Arrow α α (hasArrow α V)) := h.isPreorder
  end HasArrows

  variable [HasInternalEquivalences V]

  class HasEquivalences where
  (Equiv   : GeneralizedRelation α V)
  [isEquiv : IsEquivalence Equiv]

  namespace HasEquivalences
    variable [h : HasEquivalences α V]
    instance equivEquivalence : IsEquivalence h.Equiv := h.isEquiv
    instance hasEquivalence : HasEquivalence α α := ⟨h.Equiv⟩
    instance : HasInstances (HasEquivalence.γ α α) := Universe.instInst V
    instance : IsEquivalence (@HasEquivalence.Equiv α α (hasEquivalence α V)) := h.isEquiv
  end HasEquivalences

  class HasProducts where
  (Product : GeneralizedRelation α V)
  [hasSymm : HasSymm Product]

  namespace HasProducts
    variable [h : HasProducts α V]
    instance productSymm : HasSymm h.Product := h.hasSymm
    instance hasProduct : HasProduct α α := ⟨h.Product⟩
    instance : HasInstances (HasProduct.γ α α) := Universe.instInst V
    instance : HasSymm (@HasProduct.Product α α (hasProduct α V)) := h.hasSymm
  end HasProducts

end AttachedRelations



section AttachedDependentRelations

  variable (U V W : Universe) [HasInternalFunctors V] [HasInternalFunctors W]

  class HasDependentArrows [h : HasArrows ⌈U⌉ V] where
  (Arrow      : GeneralizedDependentRelation h.Arrow W)
  [isPreorder : IsDependentPreorder Arrow]

  namespace HasDependentArrows
    variable [HasArrows ⌈U⌉ V] [h : HasDependentArrows U V W]
    instance arrowPreorder : IsDependentPreorder h.Arrow := h.isPreorder
    notation:20 a:21 " ⇝[" F:0 "] " b:21 => HasDependentArrows.Arrow F a b
    notation:20 a:21 " ⇝[" F:0 "," V':0 "," W':0 "] " b:21 => HasDependentArrows.Arrow (V := V') (W := W') F a b
  end HasDependentArrows

  variable [HasInternalEquivalences V] [HasInternalEquivalences W]

  class HasDependentEquivalences [h : HasEquivalences ⌈U⌉ V] where
  (Equiv   : GeneralizedDependentRelation h.Equiv W)
  [isEquiv : IsDependentEquivalence Equiv]

  namespace HasDependentEquivalences
    variable [HasEquivalences ⌈U⌉ V] [h : HasDependentEquivalences U V W]
    instance equivEquivalence : IsDependentEquivalence h.Equiv := h.isEquiv
    notation:25 a:26 " ≃[" F:0 "] " b:26 => HasDependentEquivalences.Equiv F a b
    notation:25 a:26 " ≃[" F:0 "," V':0 "," W':0 "] " b:26 => HasDependentEquivalences.Equiv (V := V') (W := W') F a b
  end HasDependentEquivalences

  class HasDependentProducts [h : HasProducts ⌈U⌉ V] where
  (Product : GeneralizedDependentRelation h.Product W)
  [hasSymm : HasDependentSymm Product]

  namespace HasDependentProducts
    variable [HasProducts ⌈U⌉ V] [h : HasDependentProducts U V W]
    instance productSymm : HasDependentSymm h.Product := h.hasSymm
    notation:35 a:36 " ⧆[" P:0 "] " b:36 => HasDependentProducts.Product P a b
    notation:35 a:36 " ⧆[" P:0 "," V':0 "," W':0 "] " b:36 => HasDependentProducts.Product (V := V') (W := W') P a b
  end HasDependentProducts

end AttachedDependentRelations



-- When defining the groupoid axioms, we need to compare equivalences for equivalence. Although this will
-- frequently be an equality or at least a setoid equivalence, we need to prepare for the most generic
-- case where equivalences are arbitrary objects. Since we then need to define a relation into the type
-- of equivalences, we need to bundle equivalences with their equivalences.

class HasInstanceEquivalences (U : Universe.{u}) where
(equivUniverse              : Universe.{v})
[equivHasFunOp              : HasFunOp equivUniverse]
[equivHasEquiv              : HasInternalEquivalences equivUniverse]
(Equiv (α : U)              : GeneralizedRelation ⌈α⌉ equivUniverse)
[equivIsEquivalence (α : U) : IsEquivalence (Equiv α)]

namespace HasInstanceEquivalences

  variable (U : Universe) [h : HasInstanceEquivalences U]

  instance hasFunOp : HasFunOp                h.equivUniverse := h.equivHasFunOp
  instance hasEquiv : HasInternalEquivalences h.equivUniverse := h.equivHasEquiv

  instance equivEquivalence (α : U) : IsEquivalence (h.Equiv α) := h.equivIsEquivalence α

  instance hasEquivalences (α : U) : HasEquivalences ⌈α⌉ h.equivUniverse := ⟨h.Equiv α⟩
  @[reducible] def InstEquivType (α : U) := ⌈α⌉ (≃) ⌈α⌉
  instance (α : U) : HasInstances (InstEquivType U α) := Universe.instInst h.equivUniverse

end HasInstanceEquivalences

class HasEquivCongrArg (U V : Universe) [HasExternalFunctors U V]
                       [hU : HasInstanceEquivalences U] [hV : HasInstanceEquivalences V]
                       [HasExternalFunctors hU.equivUniverse hV.equivUniverse] where
(equivCongrArg {α : U} {β : V} (F : α ⟶' β) {a b : α} : a ≃ b ⟶' F a ≃ F b)

namespace HasEquivCongrArg

  variable (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] [h : HasEquivCongrArg U U]

  def equiv_congrArg' {α β : U} (F : α ⟶' β) {a b : α} : a ≃ b ⟶' F a ≃ F b := h.equivCongrArg F
  def equiv_congrArg  {α β : U} (F : α ⟶  β) {a b : α} : a ≃ b ⟶  F a ≃ F b := HasInternalFunctors.fromBundled (equiv_congrArg' U (HasInternalFunctors.toBundled F))

end HasEquivCongrArg

class HasEquivCongrFun (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] where
(equivCongrFun {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G ⟶' F a ≃ G a)

namespace HasEquivCongrFun

  variable (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] [h : HasEquivCongrFun U]

  def equiv_congrFun' {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G ⟶' F a ≃ G a := h.equivCongrFun a
  def equiv_congrFun  {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G ⟶  F a ≃ G a := HasInternalFunctors.fromBundled (equiv_congrFun' U a)

end HasEquivCongrFun

class HasEquivCongr (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] extends HasEquivCongrArg U U, HasEquivCongrFun U

namespace HasEquivCongr

  variable (U : Universe) [HasInternalFunctors U] [HasInstanceEquivalences U] [HasEquivCongr U]

  def equiv_congr  {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G ⟶ a ≃ b ⟶ F a ≃ G b :=
  HasLinearFunOp.swapFunFun (HasTrans.trans    ⊙ HasEquivCongrArg.equiv_congrArg U F) ⊙ HasEquivCongrFun.equiv_congrFun U b

  def equiv_congr' {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G ⟶ a ≃ b ⟶ F a ≃ G b :=
  HasLinearFunOp.swapFunFun (HasTrans.revTrans ⊙ HasEquivCongrArg.equiv_congrArg U G) ⊙ HasEquivCongrFun.equiv_congrFun U a

end HasEquivCongr

class HasNaturalEquivalences (U : Universe) [HasInternalFunctors U] extends HasInstanceEquivalences U, HasEquivCongr U where
[equivHasInstEquivs                      : HasInstanceEquivalences equivUniverse]
(isNat {α β : U} (F G : α ⟶ β) (a b : α) : HasEquivCongr.equiv_congr  U (F := F) (G := G) (a := a) (b := b) ≃
                                           HasEquivCongr.equiv_congr' U (F := F) (G := G) (a := a) (b := b))

namespace HasNaturalEquivalences

  variable (U : Universe) [HasInternalFunctors U] [h : HasNaturalEquivalences U]

  instance equivEquivs : HasInstanceEquivalences h.equivUniverse := h.equivHasInstEquivs

end HasNaturalEquivalences



-- We would also like to be able to manipulate such equivalences, and we need them to behave like
-- isomorphisms when doing so, with `refl` as the identity, `symm` as inverse, and `trans` as composition.
-- In other words, a structure with its equivalences is a category where every morphism has an inverse (as
-- guaranteed by `symm`), i.e. it is a groupoid. Since equivalences have equivalences, it is actually a
-- higher groupoid.
--
-- (Of course, the same type may also have a category structure with more morphisms, but since we are
-- defining a generalization of an equivalence relation, not a category, we wish to ignore such extra
-- structure at this point.)
--
-- We add three redundant axioms to avoid unnecessary computations. (Actually, this list of axioms was
-- originally inspired by the seven corresponding lemmas in `data.equiv.basic` of mathlib in Lean 3:
-- `symm_symm`, `trans_refl`, etc.)
--
-- Remark: Interestingly, all axioms can be regarded as simplification rules (with the simplification for
-- associativity being the omission of parentheses). With the addition of the three redundant axioms, they
-- enable equational reasoning by transforming all possible terms into a "flat" canonical form. Besides
-- making proofs trivial, this observation also suggests an alternative formalization of the axioms in
-- terms of a simplification function.
--
-- Note that for actual equivalence relations, the axioms are trivially satisfied in a proof-irrelevant
-- system such as Lean.

-- TODO: Introduce a specification that describes all of the redundancies in axioms, so that higher
-- structures can force redundant data to be equal.

section Morphisms

  variable {α : Sort u} {V : Universe.{v}} [HasInternalFunctors V] [HasInstanceEquivalences.{v, w} V]
           (R : GeneralizedRelation α V)

  variable [HasLinearFunOp V] [HasTrans R]

  @[reducible] def compCompRight (a b c d : α) : R a b ⟶ R b c ⟶ R c d ⟶ R a d :=
  HasLinearFunOp.revCompFunFun (R b c) HasTrans.trans ⊙ HasTrans.trans
  @[reducible] def compCompLeft  (a b c d : α) : R a b ⟶ R b c ⟶ R c d ⟶ R a d :=
  HasLinearFunOp.swapFunFun (HasLinearFunOp.compFunFunFun (R c d) (R b d) (R a d) ⊙ HasTrans.trans) ⊙ HasTrans.trans

  theorem compCompRight.eff [HasEquivCongrFun V] {a b c d : α} (f : R a b) (g : R b c) (h : R c d) :
    (compCompRight R a b c d) f g h = h • (g • f) :=
  by simp; rfl
  theorem compCompLeft.eff  [HasEquivCongrFun V] {a b c d : α} (f : R a b) (g : R b c) (h : R c d) :
    (compCompLeft  R a b c d) f g h = (h • g) • f :=
  by simp; rfl

  class IsCompositionRelation                                 : Sort (max 1 u v w) where
  (assoc {a b c d : α} : compCompRight R a b c d ≃ compCompLeft R a b c d)

  variable [HasRefl R]

  @[reducible] def leftMulId  (a b : α) : R a b ⟶ R a b := HasTrans.revTrans ⟮ident R b⟯
  @[reducible] def rightMulId (a b : α) : R a b ⟶ R a b := HasTrans.trans    ⟮ident R a⟯

  theorem leftMulId.eff  [HasEquivCongrFun V] {a b : α} (f : R a b) : (leftMulId  R a b) f = ident R b • f :=
  by simp; rfl
  theorem rightMulId.eff [HasEquivCongrFun V] {a b : α} (f : R a b) : (rightMulId R a b) f = f • ident R a :=
  rfl

  class IsMorphismRelation    extends IsCompositionRelation R : Sort (max 1 u v w) where
  (leftId  {a b : α} : leftMulId  R a b ≃ HasLinearFunOp.idFun (R a b))
  (rightId {a b : α} : rightMulId R a b ≃ HasLinearFunOp.idFun (R a b))

  variable [HasSubLinearFunOp V] [HasNonLinearFunOp V] [HasInternalEquivalences V] [HasSymm R]

  @[reducible] def leftMulInv  (a b : α) : R a b ⟶ R a a :=
  HasNonLinearFunOp.dupFun (HasTrans.revTrans ⊙ HasInternalEquivalences.toFun HasSymm.symm)
  @[reducible] def rightMulInv (a b : α) : R a b ⟶ R b b :=
  HasNonLinearFunOp.dupFun (HasTrans.trans    ⊙ HasInternalEquivalences.toFun HasSymm.symm)

  theorem leftMulInv.eff  [HasEquivCongrFun V] {a b : α} (f : R a b) : (leftMulInv  R a b) f = f⁻¹ • f :=
  by simp; rfl
  theorem rightMulInv.eff [HasEquivCongrFun V] {a b : α} (f : R a b) : (rightMulInv R a b) f = f • f⁻¹ :=
  by simp; rfl

  class IsIsomorphismRelation extends IsMorphismRelation    R : Sort (max 1 u v w) where
  (leftInv  {a b : α} : leftMulInv  R a b ≃ HasSubLinearFunOp.constFun (R a b) (ident R a))
  (rightInv {a b : α} : rightMulInv R a b ≃ HasSubLinearFunOp.constFun (R a b) (ident R b))

  -- TODO: convert to lemmas?
  --(invInv   {a b   : α} (f : R a b)             : (f⁻¹)⁻¹       ≃ f)
  --(compInv  {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹     ≃ f⁻¹ • g⁻¹)
  --(idInv    (a     : α)                         : (ident R a)⁻¹ ≃ ident R a)

end Morphisms



-- TODO: Rephrase trans and symm as functor composition.

section Functors

  variable {α : Sort u} {V W : Universe} [HasInstanceEquivalences W] [HasExternalFunctors V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation α W)

  def BaseFunctor := ∀ {a b}, R a b ⟶' S a b

  variable (F : BaseFunctor R S)

  class IsReflFunctor  [hR : HasRefl  R] [hS : HasRefl  S] where
  (respectsRefl  (a     : α)                         : F (hR.refl   a)   ≃ hS.refl   a)

  variable [HasInternalFunctors V] [HasInternalFunctors W]

  class IsTransFunctor [hR : HasTrans R] [hS : HasTrans S] where
  (respectsTrans {a b c : α} (f : R a b) (g : R b c) : F (hR.trans' f g) ≃ hS.trans' (F f) (F g))

  class IsPreorderFunctor [IsPreorder R] [IsPreorder S] extends IsReflFunctor R S F, IsTransFunctor R S F

  variable [HasInternalEquivalences V] [HasInternalEquivalences W]

  class IsSymmFunctor  [hR : HasSymm  R] [hS : HasSymm  S] where
  (respectsSymm  {a b   : α} (f : R a b)             : F (hR.symm'  f)   ≃ hS.symm'  (F f))

  class IsEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] extends IsPreorderFunctor R S F, IsSymmFunctor R S F

end Functors



-- TODO: If arrows have equivalences, we can specify redundancies in axioms as such equivalences.



section NaturalTransformations

  variable {α : Sort u} {β : Sort v} {V W : Universe} [HasExternalFunctors V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation β W)

  def MappedBaseFunctor (m : α → β) := ∀ {a b}, R a b ⟶' S (m a) (m b)

  variable [HasInternalFunctors W] [HasInstanceEquivalences W] [h : HasTrans S]
           {mF mG : α → β} (F : MappedBaseFunctor R S mF) (G : MappedBaseFunctor R S mG)

  class IsNatural (n : ∀ a, S (mF a) (mG a)) where
  (nat {a b : α} (f : R a b) : h.trans' (n a) (G f) ≃ h.trans' (F f) (n b))

  -- The following definitions specify how we can treat a natural quantification as an element of `W`.
  -- TODO: Maybe we can replace this with a more general quantification mechanism.

  structure NaturalQuantification where
  (n         : ∀ a, S (mF a) (mG a))
  [isNatural : IsNatural R S F G n]

  class HasInternalNaturalQuantification where
  (Nat      : W)
  (natEquiv : ⌈Nat⌉ ≃ NaturalQuantification R S F G)

end NaturalTransformations

class HasNaturalQuantification (U₁ U₂ V W : Universe) [HasExternalFunctors U₁ U₂] [HasExternalFunctors V W]
                                                      [HasInternalFunctors W] [HasInstanceEquivalences W] where
[hasNat {α : U₁} {β : U₂} (R : GeneralizedRelation ⌈α⌉ V) (S : GeneralizedRelation ⌈β⌉ W) [h : HasTrans S]
        {mF mG : α ⟶' β} (F : MappedBaseFunctor R S mF) (G : MappedBaseFunctor R S mG) :
   HasInternalNaturalQuantification R S F G]



section Categories

  variable (M : Universe.{v}) [HasInternalFunctors M] [HasLinearFunOp M] [HasInstanceEquivalences.{v, w} M] (α : Sort u)

  class IsCategory extends HasArrows α M : Sort (max 1 u (v + 1) w) where
  [isMor : IsMorphismRelation Arrow]

  namespace IsCategory

    variable [h : IsCategory M α]

    instance hasMor : IsMorphismRelation h.Arrow := h.isMor

  end IsCategory

  variable [HasSubLinearFunOp M] [HasNonLinearFunOp M] [HasInternalEquivalences M]

  class IsGroupoid extends HasEquivalences α M : Sort (max 1 u (v + 1) w) where
  [isIso : IsIsomorphismRelation Equiv]

  namespace IsGroupoid

    variable [h : IsGroupoid M α]

    instance hasIso : IsIsomorphismRelation h.Equiv := h.isIso

  end IsGroupoid

end Categories



class HasInstanceIsomorphisms (U : Universe) [HasInternalFunctors U] extends HasNaturalEquivalences U where
[equivIsIso (α : U) : IsIsomorphismRelation (Equiv α)]

namespace HasInstanceIsomorphisms

  variable (U : Universe) [HasInternalFunctors U] [h : HasInstanceIsomorphisms U]

  instance typeIsGroupoid (α : U) : IsGroupoid h.equivUniverse ⌈α⌉ :=
  { isIso := h.equivIsIso α }

end HasInstanceIsomorphisms



def FunctorEquiv {U : Universe} [HasInternalFunctors U] [h : HasInstanceEquivalences U] [HasEquivCongrArg U U] [HasInstanceEquivalences h.equivUniverse] {α β : U} (F G : α ⟶ β) :=
NaturalQuantification (h.Equiv α) (h.Equiv β) (HasEquivCongrArg.equivCongrArg (HasInternalFunctors.toBundled F)) (HasEquivCongrArg.equivCongrArg (HasInternalFunctors.toBundled G))

class HasFunctorExtensionality (U : Universe) [HasInternalFunctors U] [h : HasInstanceEquivalences U] [HasEquivCongrArg U U] [HasInstanceEquivalences h.equivUniverse] where
(funEquivEquiv {α β : U} {F G : α ⟶ β} : ⌈F ≃ G⌉ ≃ FunctorEquiv F G)

-- TODO: This should follow from functor extensionality. Maybe because of the special role of equality in functors?

--class HasLinearFunOpMorphisms (U : Universe) [HasInternalFunctors U] [HasLinearFunOp U] [HasInstanceEquivalences U] where
--(leftId  (α β : U) : HasLinearFunOp.revCompFunFun α (HasLinearFunOp.idFun β) ≃ HasLinearFunOp.idFun (α ⟶ β))
--(rightId (α β : U) : HasLinearFunOp.compFunFun (HasLinearFunOp.idFun α) β ≃ HasLinearFunOp.idFun (α ⟶ β))



-- TODO: Move back to `Lemmas.lean`.
-- TODO: Add equivalences.
-- TODO: Add (iso)morphisms as an additional type class.

namespace HasLinearFunOp

  variable (U : Universe) [h : HasInternalFunctors U] [HasLinearFunOp U]

  instance : HasRefl    h.Fun := ⟨idFun⟩
  instance : HasTrans   h.Fun := ⟨compFunFunFun _ _ _⟩
  instance : IsPreorder h.Fun := ⟨⟩

  instance hasArrows : HasArrows ⌈U⌉ U := ⟨h.Fun⟩

  @[simp] theorem transDef {α β γ : U} {F : α ⟶ β} {G : β ⟶ γ} : G • F = G ⊙ F :=
  compFunFunFun.effEff α β γ F G

  variable [hInst : HasNaturalEquivalences U] [HasLinearFunOp hInst.equivUniverse]

  def DependentArrow {α β : U} (F : α ⟶ β) (a : α) (b : β) := F a ≃ b

  namespace DependentArrow

    def refl {α : U} (a : α) : (idFun α) a ≃ a :=
    Eq.ndrec (motive := λ x : α => ⌈x ≃ a⌉) (ident (hInst.Equiv α) a) (Eq.symm (idFun.eff α a))

    def trans {α β γ : U} {F : α ⟶ β} {G : β ⟶ γ} {a : α} {b : β} {c : γ} : F a ≃ b ⟶ G b ≃ c ⟶ (G • F) a ≃ c :=
    let f₁ : F a ≃ b ⟶ (G • F) a ≃ G b := compFunFunFun.effEffEff α β γ F G a ▸ HasEquivCongrArg.equiv_congrArg U G;
    HasTrans.trans ⊙ f₁ 

    instance : GeneralizedDependentRelation.HasDependentRefl    (DependentArrow U) := ⟨refl  U⟩
    instance : GeneralizedDependentRelation.HasDependentTrans   (DependentArrow U) := ⟨trans U⟩
    instance : GeneralizedDependentRelation.IsDependentPreorder (DependentArrow U) := ⟨⟩
  
  end DependentArrow

  instance hasDependentArrows : HasDependentArrows U U hInst.equivUniverse := ⟨DependentArrow U⟩

end HasLinearFunOp
