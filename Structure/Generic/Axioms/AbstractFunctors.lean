import Structure.Generic.Axioms.Universes

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



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
-- In `DerivedFunctors.lean`, we construct several other functors such as
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



class HasLinearFunOp (U : Universe) [h : HasInternalFunctors U] extends HasIdFun U, HasCompFun U U U where
(appIsFun        {α : U} (a : α) (β : U)        : h.IsFun (λ F : α ⟶ β     => F a))
(appFunIsFun     (α β : U)                      : h.IsFun (λ a : α         => HasInternalFunctors.mkFun (appIsFun a β)))
(compFunIsFun    {α β : U} (F : α ⟶' β) (γ : U) : h.IsFun (λ G : β ⟶ γ     => HasInternalFunctors.mkFun (compIsFun F (HasInternalFunctors.toBundled G))))
(compFunFunIsFun (α β γ : U)                    : h.IsFun (λ F : α ⟶ β     => HasInternalFunctors.mkFun (compFunIsFun (HasInternalFunctors.toBundled F) γ)))

namespace HasLinearFunOp

  variable {U : Universe} [HasInternalFunctors U] [h : HasLinearFunOp U]

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

end HasLinearFunOp



class HasSubLinearFunOp (U : Universe) [h : HasInternalFunctors U] extends HasConstFun U U where
(constFunIsFun (α β : U) : h.IsFun (λ c : β => HasInternalFunctors.mkFun (constIsFun α c)))

namespace HasSubLinearFunOp

  variable {U : Universe} [HasInternalFunctors U] [h : HasSubLinearFunOp U]

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

class HasAffineFunOp (U : Universe) [h : HasInternalFunctors U] extends HasLinearFunOp U, HasSubLinearFunOp U



class HasNonLinearFunOp (U : Universe) [h : HasInternalFunctors U] where
(dupIsFun    {α β : U} (F : α ⟶' α ⟶ β) : h.IsFun (λ a : α         => F a a))
(dupFunIsFun (α β : U)                  : h.IsFun (λ F : α ⟶ α ⟶ β => HasInternalFunctors.mkFun (dupIsFun (HasInternalFunctors.toBundled F))))

namespace HasNonLinearFunOp

  variable {U : Universe} [HasInternalFunctors U] [h : HasNonLinearFunOp U]

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

class HasFullFunOp (U : Universe) [h : HasInternalFunctors U] extends HasAffineFunOp U, HasNonLinearFunOp U



class HasFunOp (U : Universe.{u}) extends HasInternalFunctors U, HasFullFunOp U : Type u
