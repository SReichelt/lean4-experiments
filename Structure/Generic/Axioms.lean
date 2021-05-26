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

import mathlib4_experiments.Data.Notation
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
set_option pp.universes true

universes u v v' w w'



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

class HasExternalFunctors (U : Universe.{u}) (V : Universe.{v}) : Type (max u v w) where
(IsFun {α : U} {β : V} : (α → β) → Sort w)

structure BundledFunctor {U : Universe.{u}} {V : Universe.{v}}
          [h : HasExternalFunctors.{u, v, w} U V] (α : U) (β : V) : Sort (max 1 u v w) where
(f     : α → β)
(isFun : h.IsFun f)

namespace BundledFunctor

  infixr:20 " ⟶' " => BundledFunctor

  variable {U V : Universe} [h : HasExternalFunctors U V]

  instance coeFun (α : U) (β : V) : CoeFun (α ⟶' β) (λ _ => α → β) := ⟨BundledFunctor.f⟩

  def mkFun {α : U} {β : V} {f : α → β} (hf : h.IsFun f) : α ⟶' β := ⟨f, hf⟩

end BundledFunctor

class HasInternalFunctors (U : Universe.{u}) extends HasExternalFunctors.{u, u, w} U U : Type (max u w) where
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

  def mkFun {α β : U} {f : α → β} (hf : h.IsFun f) : α ⟶  β := fromBundled (BundledFunctor.mkFun hf)

  @[simp] theorem mkFun.eff {α β : U} {f : α → β} (hf : h.IsFun f) (a : α) :
    (mkFun hf) a = f a :=
  fromBundled.eff (BundledFunctor.mkFun hf) a

end HasInternalFunctors

-- The following axioms are equivalent to asserting the existence of five functors with specified behavior:
-- id    : `α ⟶ α,                           a ↦ a`
-- const : `β ⟶ (α ⟶ β),                     c ↦ (a ↦ c)`
-- app   : `α ⟶ (α ⟶ β) ⟶ β,                 a ↦ (F ↦ F a)`
-- dup   : `(α ⟶ α ⟶ β) ⟶ (α ⟶ β),           F ↦ (a ↦ F a a)`
-- comp  : `(α ⟶ β) ⟶ (β ⟶ γ) ⟶ (α ⟶ γ),     F ↦ (G ↦ (a ↦ G (F a)))`
--
-- We construct these functors below. In `Lemmas.lean`, we additionally construct e.g.
-- swap  : `(α ⟶ β ⟶ γ) ⟶ (β ⟶ α ⟶ γ),       F ↦ (b ↦ (a ↦ F a b))`
-- subst : `(α ⟶ β ⟶ γ) ⟶ (α ⟶ β) ⟶ (α ⟶ γ), F ↦ (G ↦ (a ↦ F a (G a)))`
-- from these axioms, and give a general algorithm for proving that a function is functorial.

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

  def idFun  (α : U) : α ⟶  α := HasInternalFunctors.mkFun (h.idIsFun α)
  def idFun' (α : U) : α ⟶' α := HasIdFun.idFun' α

  @[simp] theorem idFun.eff (α : U) (a : α) : (idFun α) a = a :=
  by apply HasInternalFunctors.mkFun.eff

  def appFun' {α : U} (a : α) (β : U) : (α ⟶ β) ⟶' β := BundledFunctor.mkFun      (h.appIsFun a β)
  def appFun  {α : U} (a : α) (β : U) : (α ⟶ β) ⟶  β := HasInternalFunctors.mkFun (h.appIsFun a β)

  @[simp] theorem appFun.eff {α : U} (a : α) (β : U) (F : α ⟶ β) : (appFun a β) F = F a :=
  by apply HasInternalFunctors.mkFun.eff

  def appFunFun' (α β : U) : α ⟶' (α ⟶ β) ⟶ β := BundledFunctor.mkFun      (h.appFunIsFun α β)
  def appFunFun  (α β : U) : α ⟶  (α ⟶ β) ⟶ β := HasInternalFunctors.mkFun (h.appFunIsFun α β)

  @[simp] theorem appFunFun.eff (α β : U) (a : α) : (appFunFun α β) a = appFun a β :=
  by apply HasInternalFunctors.mkFun.eff

  def compFun' {α β γ : U} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶' γ := HasCompFun.compFun' F G
  def compFun  {α β γ : U} (F : α ⟶  β) (G : β ⟶  γ) : α ⟶  γ := HasInternalFunctors.mkFun (h.compIsFun (HasInternalFunctors.toBundled F) (HasInternalFunctors.toBundled G))

  @[simp] theorem compFun.eff {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) (a : α) : (compFun F G) a = G (F a) :=
  by apply HasInternalFunctors.mkFun.eff

  def compFunFun' {α β : U} (F : α ⟶' β) (γ : U) : (β ⟶ γ) ⟶' (α ⟶ γ) := BundledFunctor.mkFun      (h.compFunIsFun F                                 γ)
  def compFunFun  {α β : U} (F : α ⟶  β) (γ : U) : (β ⟶ γ) ⟶  (α ⟶ γ) := HasInternalFunctors.mkFun (h.compFunIsFun (HasInternalFunctors.toBundled F) γ)

  @[simp] theorem compFunFun.eff {α β : U} (F : α ⟶ β) (γ : U) (G : β ⟶ γ) : (compFunFun F γ) G = compFun F G :=
  by apply HasInternalFunctors.mkFun.eff

  def compFunFunFun' (α β γ : U) : (α ⟶ β) ⟶' (β ⟶ γ) ⟶ (α ⟶ γ) := BundledFunctor.mkFun      (h.compFunFunIsFun α β γ)
  def compFunFunFun  (α β γ : U) : (α ⟶ β) ⟶  (β ⟶ γ) ⟶ (α ⟶ γ) := HasInternalFunctors.mkFun (h.compFunFunIsFun α β γ)
  
  @[simp] theorem compFunFunFun.eff (α β γ : U) (F : α ⟶ β) : (compFunFunFun α β γ) F = compFunFun F γ :=
  by apply HasInternalFunctors.mkFun.eff

  def revCompFun {α β γ : U} (G : β ⟶  γ) (F : α ⟶  β) : α ⟶ γ := compFun F G
  infixr:90 " ⊙ "  => HasLinearFunOp.revCompFun

end HasLinearFunOp

class HasAffineFunOp (U : Universe.{u}) [h : HasInternalFunctors U] extends HasLinearFunOp U, HasConstFun U U where
(constFunIsFun (α β : U) : h.IsFun (λ c : β => HasInternalFunctors.mkFun (constIsFun α c)))

namespace HasAffineFunOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [h : HasAffineFunOp U]

  def constFun' (α : U) {β : U} (c : β) : α ⟶' β := HasConstFun.constFun' α c
  def constFun  (α : U) {β : U} (c : β) : α ⟶  β := HasInternalFunctors.mkFun (h.constIsFun α c)

  @[simp] theorem constFun.eff (α : U) {β : U} (c : β) (a : α) : (constFun α c) a = c :=
  by apply HasInternalFunctors.mkFun.eff

  def constFunFun' (α β : U) : β ⟶' (α ⟶ β) := BundledFunctor.mkFun      (h.constFunIsFun α β)
  def constFunFun  (α β : U) : β ⟶  (α ⟶ β) := HasInternalFunctors.mkFun (h.constFunIsFun α β)

  @[simp] theorem constFunFun.eff (α β : U) (c : β) : (constFunFun α β) c = constFun α c :=
  by apply HasInternalFunctors.mkFun.eff

end HasAffineFunOp

class HasFullFunOp (U : Universe.{u}) [h : HasInternalFunctors U] extends HasAffineFunOp U where
(dupIsFun    {α β : U} (F : α ⟶' α ⟶ β) : h.IsFun (λ a : α         => F a a))
(dupFunIsFun (α β : U)                  : h.IsFun (λ F : α ⟶ α ⟶ β => HasInternalFunctors.mkFun (dupIsFun (HasInternalFunctors.toBundled F))))

namespace HasFullFunOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [h : HasFullFunOp U]

  def dupFun' {α β : U} (F : α ⟶' α ⟶ β) : α ⟶' β := BundledFunctor.mkFun      (h.dupIsFun F)
  def dupFun  {α β : U} (F : α ⟶  α ⟶ β) : α ⟶  β := HasInternalFunctors.mkFun (h.dupIsFun (HasInternalFunctors.toBundled F))

  @[simp] theorem dupFun.eff {α β : U} (F : α ⟶ α ⟶ β) (a : α) : (dupFun F) a = F a a :=
  by apply HasInternalFunctors.mkFun.eff

  def dupFunFun' (α β : U) : (α ⟶ α ⟶ β) ⟶' (α ⟶ β) := BundledFunctor.mkFun      (h.dupFunIsFun α β)
  def dupFunFun  (α β : U) : (α ⟶ α ⟶ β) ⟶  (α ⟶ β) := HasInternalFunctors.mkFun (h.dupFunIsFun α β)

  @[simp] theorem dupFunFun.eff (α β : U) (F : α ⟶ α ⟶ β) : (dupFunFun α β) F = dupFun F :=
  by apply HasInternalFunctors.mkFun.eff

end HasFullFunOp

class HasFunOp (U : Universe.{u}) extends HasInternalFunctors.{u, w} U, HasFullFunOp U : Type (max u w)



-- TODO: Introduce products (with functorial construction and projection)
--       and equivalences (with functorial projection to product of to/inv functors)
-- We should be able to prove the arrow/product laws.



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

    class HasRefl  where
    (refl  (a     : α) : R a a)

    variable [HasInternalFunctors V]

    class HasSymm  where
    (symm  {a b   : α} : R a b ⟶ R b a)

    class HasTrans where
    (trans {a b c : α} : R a b ⟶ R b c ⟶ R a c)

    class IsPreorder    extends HasRefl R, HasTrans R
    class IsEquivalence extends IsPreorder R, HasSymm R
  
  end Properties

  def HasSymm.symm'   {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasSymm  R] {a b   : α} (f : R a b) : R b a := h.symm f
  def HasTrans.trans' {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasTrans R] {a b c : α} (f : R a b) (g : R b c) : R a c := h.trans f g

  -- When reasoning about instances of `R a b`, we would like to write `trans` as composition, `refl` as
  -- identity, and `symm` as inverse.
  -- Note that `R` can be inferred from `f : R a b` by elaboration.

  section Notation

    @[reducible] def revComp {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasTrans R] {a b c : α} (g : R b c) (f : R a b) : R a c := h.trans' f g
    infixr:90 " • " => revComp

    @[reducible] def ident (R : GeneralizedRelation α V) [h : HasRefl R] (a : α) : R a a := h.refl a

    @[reducible] def inv {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasSymm R] {a b : α} (f : R a b) : R b a := h.symm' f
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

    class HasDependentRefl  [h : HasRefl  R] where
    (refl  {α     : U}                         (a : α)                 : D (h.refl α) a a)

    def reflRel [h : HasRefl R] (α : U) : GeneralizedRelation ⌈α⌉ W := D (h.refl α)
    instance [HasRefl R] [h : HasDependentRefl D] (α : U) : HasRefl (reflRel D α) := ⟨h.refl⟩

    variable [HasInternalFunctors V] [HasInternalFunctors W]

    class HasDependentSymm  [h : HasSymm  R] where
    (symm  {α β   : U} {F : R α β}             {a : α} {b : β}         : D F a b ⟶ D (h.symm' F) b a)

    class HasDependentTrans [h : HasTrans R] where
    (trans {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} : D F a b ⟶ D G b c ⟶ D (h.trans' F G) a c)

    class IsDependentPreorder    [h : IsPreorder    R] extends HasDependentRefl D, HasDependentTrans D
    class IsDependentEquivalence [h : IsEquivalence R] extends IsDependentPreorder D, HasDependentSymm D

  end Properties

  def HasDependentSymm.symm'    {D : GeneralizedDependentRelation R W}
                                [HasInternalFunctors V] [HasInternalFunctors W] [HasSymm  R] [h : HasDependentSymm  D]
                                {α β : U} {F : R α β} {a : α} {b : β} (f : D F a b) :
   D (HasSymm.symm' F) b a :=
  h.symm f

  def HasDependentTrans.trans'  {D : GeneralizedDependentRelation R W}
                                [HasInternalFunctors V] [HasInternalFunctors W] [HasTrans R] [h : HasDependentTrans D]
                                {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (f : D F a b) (g : D G b c) :
    D (HasTrans.trans' F G) a c :=
  h.trans f g

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

    @[reducible] def depInv {D : GeneralizedDependentRelation R W} [HasInternalFunctors V] [HasInternalFunctors W]
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

  variable (α : Sort u) (V : Universe.{v}) [HasInternalFunctors.{v, w} V]

  -- TODO: Remove this?
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

end AttachedRelations



section AttachedDependentRelations

  variable (U V W : Universe) [HasInternalFunctors V] [HasInternalFunctors W]

  class HasDependentProducts [h : HasProducts ⌈U⌉ V] where
  (Product : GeneralizedDependentRelation h.Product W)
  [hasSymm : HasDependentSymm Product]

  namespace HasDependentProducts
    variable [HasProducts ⌈U⌉ V] [h : HasDependentProducts U V W]
    instance productSymm : HasDependentSymm h.Product := h.hasSymm
    notation:35 a:36 " ⊓[" P:0 "] " b:36 => HasDependentProducts.Product P a b
    notation:35 a:36 " ⊓[" P:0 "," V':0 "," W':0 "] " b:36 => HasDependentProducts.Product (V := V') (W := W') P a b
  end HasDependentProducts

  class HasDependentArrows [h : HasArrows ⌈U⌉ V] where
  (Arrow      : GeneralizedDependentRelation h.Arrow W)
  [isPreorder : IsDependentPreorder Arrow]

  namespace HasDependentArrows
    variable [HasArrows ⌈U⌉ V] [h : HasDependentArrows U V W]
    instance arrowPreorder : IsDependentPreorder h.Arrow := h.isPreorder
    notation:20 a:21 " ⇝[" F:0 "] " b:21 => HasDependentArrows.Arrow F a b
    notation:20 a:21 " ⇝[" F:0 "," V':0 "," W':0 "] " b:21 => HasDependentArrows.Arrow (V := V') (W := W') F a b
  end HasDependentArrows

  class HasDependentEquivalences [h : HasEquivalences ⌈U⌉ V] where
  (Equiv   : GeneralizedDependentRelation h.Equiv W)
  [isEquiv : IsDependentEquivalence Equiv]

  namespace HasDependentEquivalences
    variable [HasEquivalences ⌈U⌉ V] [h : HasDependentEquivalences U V W]
    instance equivEquivalence : IsDependentEquivalence h.Equiv := h.isEquiv
    notation:25 a:26 " ≃[" F:0 "] " b:26 => HasDependentEquivalences.Equiv F a b
    notation:25 a:26 " ≃[" F:0 "," V':0 "," W':0 "] " b:26 => HasDependentEquivalences.Equiv (V := V') (W := W') F a b
  end HasDependentEquivalences

end AttachedDependentRelations



-- When defining the groupoid axioms, we need to compare equivalences for equivalence. Although this will
-- frequently be an equality or at least a setoid equivalence, we need to prepare for the most generic
-- case where equivalences are arbitrary objects. Since we then need to define a relation into the type
-- of equivalences, we need to bundle equivalences with their equivalences.
--
-- TODO: describe arrows

class HasInstanceArrows (U : Universe.{u}) where
(arrowUniverse           : Universe.{v})
[arrowHasFun             : HasInternalFunctors.{v, w} arrowUniverse]
(Arrow (α : U)           : GeneralizedRelation ⌈α⌉ arrowUniverse)
[arrowIsPreorder (α : U) : IsPreorder (Arrow α)]

namespace HasInstanceArrows

  variable (U : Universe) [h : HasInstanceArrows U]

  instance hasFun : HasInternalFunctors h.arrowUniverse := h.arrowHasFun

  instance arrowPreorder (α : U) : IsPreorder (h.Arrow α) := h.arrowIsPreorder α

  instance hasArrows (α : U) : HasArrows ⌈α⌉ h.arrowUniverse := ⟨h.Arrow α⟩
  @[reducible] def InstArrowType (α : U) := ⌈α⌉ (⇝) ⌈α⌉
  instance (α : U) : HasInstances (InstArrowType U α) := Universe.instInst h.arrowUniverse

end HasInstanceArrows

class HasArrowCongrArg (U V : Universe) [HasExternalFunctors U V]
                       [hU : HasInstanceArrows U] [hV : HasInstanceArrows V]
                       [HasExternalFunctors hU.arrowUniverse hV.arrowUniverse] where
(arrowCongrArg {α : U} {β : V} (F : α ⟶' β) {a b : α} : (a ⇝ b) ⟶' (F a ⇝ F b))

class HasFunctorialArrows (U : Universe) [HasInternalFunctors U] extends HasInstanceArrows U where
(arrowCongr {α β : U} {F G : α ⟶ β} {a b : α} : (F ⇝ G) ⟶ (a ⇝ b) ⟶ (F a ⇝ G b))

namespace HasFunctorialArrows

  variable (U : Universe) [HasInternalFunctors U] [h : HasFunctorialArrows U]

  def arrow_congr   {α β : U} {F G : α ⟶ β} {a b : α} : (F ⇝ G) ⟶ (a ⇝ b) ⟶ (F a ⇝ G b) := h.arrowCongr
  def arrow_congr'  {α β : U} {F G : α ⟶ β} {a b : α} : (F ⇝ G) → ((a ⇝ b) ⟶ (F a ⇝ G b)) := HasInternalFunctors.funCoe (arrow_congr U)
  def arrow_congr'' {α β : U} {F G : α ⟶ β} {a b : α} : (F ⇝ G) → (a ⇝ b) → (F a ⇝ G b) := λ f => HasInternalFunctors.funCoe (arrow_congr' U f)

  def arrow_congrArg    {α β : U} (F : α ⟶  β) {a b : α} : (a ⇝ b) ⟶ (F a ⇝ F b) := (arrow_congr' U) (HasRefl.refl F)
  def arrow_congrArg'   {α β : U} (F : α ⟶  β) {a b : α} : (a ⇝ b) → (F a ⇝ F b) := HasInternalFunctors.funCoe (arrow_congrArg U F)
  def arrow_congrArg''  {α β : U} (F : α ⟶' β) {a b : α} : (a ⇝ b) ⟶ (F a ⇝ F b) := HasInternalFunctors.fromBundled.coe F ▸ arrow_congrArg U (HasInternalFunctors.fromBundled F)
  def arrow_congrArg''' {α β : U} (F : α ⟶' β) {a b : α} : (a ⇝ b) → (F a ⇝ F b) := HasInternalFunctors.funCoe (arrow_congrArg'' U F)

  def arrow_congrFun [HasLinearFunOp h.arrowUniverse] {α β : U} {F G : α ⟶ β} (a : α) : (F ⇝ G) ⟶ (F a ⇝ G a) :=
  HasLinearFunOp.appFun (HasRefl.refl a) (F a ⇝ G a) ⊙ arrow_congr U
  def arrow_congrFun' {α β : U} {F G : α ⟶ β} (a : α) : (F ⇝ G) → (F a ⇝ G a) :=
  λ f => arrow_congr'' U f (HasRefl.refl a)

  instance toHasArrowCongrArg : HasArrowCongrArg U U := ⟨λ F => HasInternalFunctors.toBundled (arrow_congrArg'' U F)⟩

end HasFunctorialArrows

class HasInstanceEquivalences (U : Universe.{u}) where
(equivUniverse              : Universe.{v})
[equivHasFun                : HasInternalFunctors.{v, w} equivUniverse]
(Equiv (α : U)              : GeneralizedRelation ⌈α⌉ equivUniverse)
[equivIsEquivalence (α : U) : IsEquivalence (Equiv α)]

namespace HasInstanceEquivalences

  variable (U : Universe) [h : HasInstanceEquivalences U]

  instance hasFun : HasInternalFunctors h.equivUniverse := h.equivHasFun

  instance equivEquivalence (α : U) : IsEquivalence (h.Equiv α) := h.equivIsEquivalence α

  instance hasEquivalences (α : U) : HasEquivalences ⌈α⌉ h.equivUniverse := ⟨h.Equiv α⟩
  @[reducible] def InstEquivType (α : U) := ⌈α⌉ (≃) ⌈α⌉
  instance (α : U) : HasInstances (InstEquivType U α) := Universe.instInst h.equivUniverse

  def toHasInstanceArrows : HasInstanceArrows U :=
  { arrowUniverse   := h.equivUniverse,
    arrowHasFun     := h.equivHasFun,
    Arrow           := h.Equiv,
    arrowIsPreorder := λ α => (h.equivIsEquivalence α).toIsPreorder }

end HasInstanceEquivalences

class HasEquivCongrArg (U V : Universe) [HasExternalFunctors U V]
                       [hU : HasInstanceEquivalences U] [hV : HasInstanceEquivalences V]
                       [HasExternalFunctors hU.equivUniverse hV.equivUniverse] where
(equivCongrArg {α : U} {β : V} (F : α ⟶' β) {a b : α} : a ≃ b ⟶' F a ≃ F b)

class HasFunctorialEquivalences (U : Universe) [HasInternalFunctors U] extends HasInstanceEquivalences U where
(equivCongr {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G ⟶ a ≃ b ⟶ F a ≃ G b)

namespace HasFunctorialEquivalences

  variable (U : Universe) [HasInternalFunctors U] [h : HasFunctorialEquivalences U]

  def toHasFunctorialArrows : HasFunctorialArrows U :=
  { toHasInstanceArrows := HasInstanceEquivalences.toHasInstanceArrows U,
    arrowCongr          := h.equivCongr }

  def equiv_congr   {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G ⟶ a ≃ b ⟶ F a ≃ G b := h.equivCongr
  def equiv_congr'  {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G → (a ≃ b ⟶ F a ≃ G b) := HasInternalFunctors.funCoe (equiv_congr U)
  def equiv_congr'' {α β : U} {F G : α ⟶ β} {a b : α} : F ≃ G → a ≃ b → F a ≃ G b := λ e => HasInternalFunctors.funCoe (equiv_congr' U e)

  def equiv_congrArg    {α β : U} (F : α ⟶  β) {a b : α} : a ≃ b ⟶ F a ≃ F b := (equiv_congr' U) (HasRefl.refl F)
  def equiv_congrArg'   {α β : U} (F : α ⟶  β) {a b : α} : a ≃ b → F a ≃ F b := HasInternalFunctors.funCoe (equiv_congrArg U F)
  def equiv_congrArg''  {α β : U} (F : α ⟶' β) {a b : α} : a ≃ b ⟶ F a ≃ F b := HasInternalFunctors.fromBundled.coe F ▸ equiv_congrArg U (HasInternalFunctors.fromBundled F)
  def equiv_congrArg''' {α β : U} (F : α ⟶' β) {a b : α} : a ≃ b → F a ≃ F b := HasInternalFunctors.funCoe (equiv_congrArg'' U F)

  def equiv_congrFun [HasLinearFunOp h.equivUniverse] {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G ⟶ F a ≃ G a :=
  HasLinearFunOp.appFun (HasRefl.refl a) (F a ≃ G a) ⊙ equiv_congr U
  def equiv_congrFun' {α β : U} {F G : α ⟶ β} (a : α) : F ≃ G → F a ≃ G a :=
  λ e => equiv_congr'' U e (HasRefl.refl a)

  instance toHasEquivCongrArg : HasEquivCongrArg U U := ⟨λ F => HasInternalFunctors.toBundled (equiv_congrArg'' U F)⟩

end HasFunctorialEquivalences



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

  variable {α : Sort u} {V : Universe.{v}} [HasInternalFunctors.{v, v'} V] [HasInstanceArrows.{v, w, w'} V]
           (R : GeneralizedRelation α V)

  class IsCompositionRelation [HasTrans      R]                                 : Sort (max 1 u v w) where
  (assocLR {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ⇝ h • (g • f))
  (assocRL {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : h • (g • f) ⇝ (h • g) • f)

  class IsMorphismRelation    [IsPreorder    R] extends IsCompositionRelation R : Sort (max 1 u v w) where
  (leftId  {a b : α} (f : R a b) : ident R b • f ⇝ f)
  (rightId {a b : α} (f : R a b) : f • ident R a ⇝ f)

  class IsIsomorphismRelation [IsEquivalence R] extends IsMorphismRelation    R : Sort (max 1 u v w) where
  (leftInv  {a b   : α} (f : R a b)             : f⁻¹ • f       ⇝ ident R a)
  (rightInv {a b   : α} (f : R a b)             : f • f⁻¹       ⇝ ident R b)
  (invInv   {a b   : α} (f : R a b)             : (f⁻¹)⁻¹       ⇝ f)
  (compInv  {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹     ⇝ f⁻¹ • g⁻¹)
  (idInv    (a     : α)                         : (ident R a)⁻¹ ⇝ ident R a)

end Morphisms



section Functors

  variable {α : Sort u} {V W : Universe} [HasInstanceArrows W] [HasExternalFunctors V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation α W)

  def BaseFunctor := ∀ {a b}, R a b ⟶' S a b

  variable (F : BaseFunctor R S)

  class IsReflFunctor  [hR : HasRefl  R] [hS : HasRefl  S] where
  (respectsRefl  (a     : α)                         : F (hR.refl   a)   ⇝ hS.refl   a)

  variable [HasInternalFunctors V] [HasInternalFunctors W]

  class IsSymmFunctor  [hR : HasSymm  R] [hS : HasSymm  S] where
  (respectsSymm  {a b   : α} (f : R a b)             : F (hR.symm'  f)   ⇝ hS.symm'  (F f))

  class IsTransFunctor [hR : HasTrans R] [hS : HasTrans S] where
  (respectsTrans {a b c : α} (f : R a b) (g : R b c) : F (hR.trans' f g) ⇝ hS.trans' (F f) (F g))

  class IsPreorderFunctor    [IsPreorder    R] [IsPreorder    S] extends IsReflFunctor R S F, IsTransFunctor R S F
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

  variable (M : Universe.{v}) [HasInternalFunctors.{v, v'} M] [HasInstanceArrows.{v, w, w'} M] (α : Sort u)

  class IsCategory extends HasArrows α M : Sort (max 1 u (v + 1) w) where
  [isMor : IsMorphismRelation Arrow]

  namespace IsCategory

    variable [h : IsCategory M α]

    instance hasMor : IsMorphismRelation h.Arrow := h.isMor

  end IsCategory

  class IsGroupoid extends HasEquivalences α M : Sort (max 1 u (v + 1) w) where
  [isIso : IsIsomorphismRelation Equiv]

  namespace IsGroupoid

    variable [h : IsGroupoid M α]

    instance hasIso : IsIsomorphismRelation h.Equiv := h.isIso

  end IsGroupoid

end Categories



class HasInstanceMorphisms (U : Universe) [HasInternalFunctors U] extends HasFunctorialArrows U where
[arrowHasArrows     : HasInstanceArrows arrowUniverse]
[arrowIsMor (α : U) : IsMorphismRelation (Arrow α)]

namespace HasInstanceMorphisms

  variable (U : Universe) [HasInternalFunctors U] [h : HasInstanceMorphisms U]

  instance arrowArrows : HasInstanceArrows h.arrowUniverse := h.arrowHasArrows

  instance instIsCategory (α : U) : IsCategory h.arrowUniverse ⌈α⌉ :=
  { isMor := h.arrowIsMor α }

end HasInstanceMorphisms

class HasInstanceIsomorphisms (U : Universe) [HasInternalFunctors U] extends HasFunctorialEquivalences U where
[equivHasArrows     : HasInstanceArrows equivUniverse]
[equivIsIso (α : U) : IsIsomorphismRelation (Equiv α)]

namespace HasInstanceIsomorphisms

  variable (U : Universe) [HasInternalFunctors U] [h : HasInstanceIsomorphisms U]

  instance equivArrows : HasInstanceArrows h.equivUniverse := h.equivHasArrows

  instance instIsCategory (α : U) : IsGroupoid h.equivUniverse ⌈α⌉ :=
  { isIso := h.equivIsIso α }

end HasInstanceIsomorphisms
