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



import mathlib4_experiments.Data.Notation
import mathlib4_experiments.Data.Equiv.Basic
import Structure.Generic.Notation



set_option autoBoundImplicitLocal false

universes u v w w'



-- A type class that says that a given type can be used like `Sort u`, i.e. its instances can be regarded
-- as types. We can also regard this as `V` defining a universe (corresponding to the Lean universe `u`).
-- * The canonical instance is `Sort u` itself (with `Prop` as a special case).
-- * Another common case is `Bundled C` for a type class `C : Sort u → Sort v`.
-- Both examples are defined in `Instances.lean`.

class HasInstances (V : Sort v) where
(Inst : V → Sort u)

namespace HasInstances

  instance coeSort (V : Sort v) [s : HasInstances V] : CoeSort V (Sort u) := ⟨s.Inst⟩

end HasInstances



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

class HasIsFun (V : Sort v) (W : Sort w) [HasInstances V] [HasInstances W] where
(IsFun {α : V} {β : W} : (α → β) → Sort u)

structure BundledFunctor {V : Sort v} {W : Sort w} [HasInstances V] [HasInstances W] [h : HasIsFun V W]
                         (α : V) (β : W) where
(f     : α → β)
(isFun : h.IsFun f)

namespace BundledFunctor

  variable {V : Sort v} {W : Sort w} [HasInstances V] [HasInstances W] [h : HasIsFun V W]

  infixr:20 " ⟶' " => BundledFunctor

  instance coeFun (α : V) (β : W) : CoeFun (α ⟶' β) (λ _ => α → β) := ⟨BundledFunctor.f⟩

end BundledFunctor

class HasFun (V : Sort v) extends HasInstances V, HasIsFun V V where
(Fun                : V → V → V)
(funEquiv (α β : V) : Inst (Fun α β) ≃ (α ⟶' β))

namespace HasFun

  variable {V : Sort v} [h : HasFun V]

  -- This is potentially endless. Is there a better way?
  instance hasArrow : HasArrow     V                             V              := ⟨h.Fun⟩
  instance : HasFun   (            V             (⟶)             V            ) := h
  instance : HasArrow              V                 (    V     (⟶)     V    )  := hasArrow
  instance : HasFun   (            V             (⟶) (    V     (⟶)     V    )) := h
  instance : HasArrow  (    V     (⟶)     V    )                 V              := hasArrow
  instance : HasFun   ((    V     (⟶)     V    ) (⟶)             V            ) := h
  instance : HasArrow  (    V     (⟶)     V    )     (    V     (⟶)     V    )  := hasArrow
  instance : HasFun   ((    V     (⟶)     V    ) (⟶) (    V     (⟶)     V    )) := h
  instance : HasArrow              V                 (    V     (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   (            V             (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasArrow  (    V     (⟶)     V    )     (    V     (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   ((    V     (⟶)     V    ) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasArrow              V                 ((V (⟶) V) (⟶)     V    )  := hasArrow
  instance : HasFun   (            V             (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasArrow              V                 ((V (⟶) V) (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   (            V             (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasArrow  (    V     (⟶)     V    )     ((V (⟶) V) (⟶)     V    )  := hasArrow
  instance : HasFun   ((    V     (⟶)     V    ) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasArrow  (    V     (⟶)     V    )     ((V (⟶) V) (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   ((    V     (⟶)     V    ) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasArrow  (    V     (⟶) (V (⟶) V))                 V              := hasArrow
  instance : HasFun   ((    V     (⟶) (V (⟶) V)) (⟶)             V            ) := h
  instance : HasArrow  (    V     (⟶) (V (⟶) V))     (    V     (⟶)     V    )  := hasArrow
  instance : HasFun   ((    V     (⟶) (V (⟶) V)) (⟶) (    V     (⟶)     V    )) := h
  instance : HasArrow  (    V     (⟶) (V (⟶) V))     (    V     (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   ((    V     (⟶) (V (⟶) V)) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasArrow  (    V     (⟶) (V (⟶) V))     ((V (⟶) V) (⟶)     V    )  := hasArrow
  instance : HasFun   ((    V     (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasArrow  (    V     (⟶) (V (⟶) V))     ((V (⟶) V) (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   ((    V     (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasArrow  ((V (⟶) V) (⟶)     V    )                 V              := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶)     V    ) (⟶)             V            ) := h
  instance : HasArrow  ((V (⟶) V) (⟶)     V    )     (    V     (⟶)     V    )  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶)     V    ) (⟶) (    V     (⟶)     V    )) := h
  instance : HasArrow  ((V (⟶) V) (⟶)     V    )     (    V     (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶)     V    ) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasArrow  ((V (⟶) V) (⟶)     V    )     ((V (⟶) V) (⟶)     V    )  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶)     V    ) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasArrow  ((V (⟶) V) (⟶)     V    )     ((V (⟶) V) (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶)     V    ) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasArrow  ((V (⟶) V) (⟶) (V (⟶) V))                 V              := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶) (V (⟶) V)) (⟶)             V            ) := h
  instance : HasArrow  ((V (⟶) V) (⟶) (V (⟶) V))     (    V     (⟶)     V    )  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) (    V     (⟶)     V    )) := h
  instance : HasArrow  ((V (⟶) V) (⟶) (V (⟶) V))     (    V     (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasArrow  ((V (⟶) V) (⟶) (V (⟶) V))     ((V (⟶) V) (⟶)     V    )  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasArrow  ((V (⟶) V) (⟶) (V (⟶) V))     ((V (⟶) V) (⟶) (V (⟶) V))  := hasArrow
  instance : HasFun   (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h

  instance : HasIsFun              V                 (    V     (⟶)     V    )  := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶)     V    )                 V              := h.toHasIsFun
  instance : HasIsFun              V                 (    V     (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶)     V    )     (    V     (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun              V                 ((V (⟶) V) (⟶)     V    )  := h.toHasIsFun
  instance : HasIsFun              V                 ((V (⟶) V) (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶)     V    )     ((V (⟶) V) (⟶)     V    )  := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶)     V    )     ((V (⟶) V) (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶) (V (⟶) V))                 V              := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶) (V (⟶) V))     (    V     (⟶)     V    )  := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶) (V (⟶) V))     ((V (⟶) V) (⟶)     V    )  := h.toHasIsFun
  instance : HasIsFun  (    V     (⟶) (V (⟶) V))     ((V (⟶) V) (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶)     V    )                 V              := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶)     V    )     (    V     (⟶)     V    )  := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶)     V    )     (    V     (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶)     V    )     ((V (⟶) V) (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶) (V (⟶) V))                 V              := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶) (V (⟶) V))     (    V     (⟶)     V    )  := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶) (V (⟶) V))     (    V     (⟶) (V (⟶) V))  := h.toHasIsFun
  instance : HasIsFun  ((V (⟶) V) (⟶) (V (⟶) V))     ((V (⟶) V) (⟶)     V    )  := h.toHasIsFun

  def toBundled   {α β : V} (F : α ⟶  β) : α ⟶' β := (h.funEquiv α β).toFun  F
  def fromBundled {α β : V} (F : α ⟶' β) : α ⟶  β := (h.funEquiv α β).invFun F

  @[simp] theorem fromToBundled {α β : V} (F : α ⟶  β) : fromBundled (toBundled F) = F := (h.funEquiv α β).leftInv  F
  @[simp] theorem toFromBundled {α β : V} (F : α ⟶' β) : toBundled (fromBundled F) = F := (h.funEquiv α β).rightInv F

  def funCoe {α β : V} (F : α ⟶ β) : α → β := (toBundled F).f
  instance coeFun (α β : V) : CoeFun (h.Inst (α ⟶ β)) (λ _ => α → β) := ⟨funCoe⟩

  def isFun {α β : V} (F : α ⟶ β) : h.IsFun (funCoe F) := (toBundled F).isFun

  theorem toBundled.eff {α β : V} (F : α ⟶ β) (a : α) : (toBundled F) a = F a := rfl

  @[simp] theorem fromBundled.coe {α β : V} (F : α ⟶' β) : funCoe (fromBundled F) = F.f :=
  congrArg BundledFunctor.f (toFromBundled F)

  @[simp] theorem fromBundled.eff {α β : V} (F : α ⟶' β) (a : α) : (fromBundled F) a = F a :=
  congrFun (fromBundled.coe F) a

  -- We need this to make type class resolution work in some places.
  @[reducible] def Fun' (α β : V) : V := α ⟶ β
  notation:20 α:21 " ⟶{" W:0 "} " β:21 => HasFun.Fun' (V := W) α β

  def mkFun' {α β : V} {f : α → β} (hf : h.IsFun f) : α ⟶' β := ⟨f, hf⟩
  def mkFun  {α β : V} {f : α → β} (hf : h.IsFun f) : α ⟶  β := fromBundled (mkFun' hf)

  @[simp] theorem mkFun.eff {α β : V} {f : α → β} (hf : h.IsFun f) (a : α) :
    (mkFun hf) a = f a :=
  fromBundled.eff (mkFun' hf) a

end HasFun

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

class HasFunOp (V : Sort v) [h : HasFun V] where
(idIsFun         (α : V)                               : h.IsFun (λ a : α         => a))
(constIsFun      (α : V) {β : V} (c : β)               : h.IsFun (λ a : α         => c))
(constFunIsFun   (α β : V)                             : h.IsFun (λ c : β         => HasFun.mkFun (constIsFun α c)))
(appIsFun        {α : V} (a : α) (β : V)               : h.IsFun (λ F : α ⟶ β     => F a))
(appFunIsFun     (α β : V)                             : h.IsFun (λ a : α         => HasFun.mkFun (appIsFun a β)))
(dupIsFun        {α β : V} (F : α ⟶' α ⟶ β)            : h.IsFun (λ a : α         => F a a))
(dupFunIsFun     (α β : V)                             : h.IsFun (λ F : α ⟶ α ⟶ β => HasFun.mkFun (dupIsFun (HasFun.toBundled F))))
(compIsFun       {α β γ : V} (F : α ⟶' β) (G : β ⟶' γ) : h.IsFun (λ a : α         => G (F a)))
(compFunIsFun    {α β : V} (F : α ⟶' β) (γ : V)        : h.IsFun (λ G : β ⟶ γ     => HasFun.mkFun (compIsFun F (HasFun.toBundled G))))
(compFunFunIsFun (α β γ : V)                           : h.IsFun (λ F : α ⟶ β     => HasFun.mkFun (compFunIsFun (HasFun.toBundled F) γ)))

namespace HasFunOp

  variable {V : Sort v} [HasFun V] [h : HasFunOp V]

  instance : HasFunOp (            V             (⟶)             V            ) := h
  instance : HasFunOp (            V             (⟶) (    V     (⟶)     V    )) := h
  instance : HasFunOp ((    V     (⟶)     V    ) (⟶)             V            ) := h
  instance : HasFunOp ((    V     (⟶)     V    ) (⟶) (    V     (⟶)     V    )) := h
  instance : HasFunOp (            V             (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasFunOp ((    V     (⟶)     V    ) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasFunOp (            V             (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasFunOp (            V             (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasFunOp ((    V     (⟶)     V    ) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasFunOp ((    V     (⟶)     V    ) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasFunOp ((    V     (⟶) (V (⟶) V)) (⟶)             V            ) := h
  instance : HasFunOp ((    V     (⟶) (V (⟶) V)) (⟶) (    V     (⟶)     V    )) := h
  instance : HasFunOp ((    V     (⟶) (V (⟶) V)) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasFunOp ((    V     (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasFunOp ((    V     (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasFunOp (((V (⟶) V) (⟶)     V    ) (⟶)             V            ) := h
  instance : HasFunOp (((V (⟶) V) (⟶)     V    ) (⟶) (    V     (⟶)     V    )) := h
  instance : HasFunOp (((V (⟶) V) (⟶)     V    ) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasFunOp (((V (⟶) V) (⟶)     V    ) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasFunOp (((V (⟶) V) (⟶)     V    ) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h
  instance : HasFunOp (((V (⟶) V) (⟶) (V (⟶) V)) (⟶)             V            ) := h
  instance : HasFunOp (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) (    V     (⟶)     V    )) := h
  instance : HasFunOp (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) (    V     (⟶) (V (⟶) V))) := h
  instance : HasFunOp (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶)     V    )) := h
  instance : HasFunOp (((V (⟶) V) (⟶) (V (⟶) V)) (⟶) ((V (⟶) V) (⟶) (V (⟶) V))) := h

  def idFun' (α : V) : α ⟶' α := HasFun.mkFun' (h.idIsFun α)
  def idFun  (α : V) : α ⟶  α := HasFun.mkFun  (h.idIsFun α)

  @[simp] theorem idFun.eff (α : V) (a : α) : (idFun α) a = a :=
  by apply HasFun.mkFun.eff

  def constFun' (α : V) {β : V} (c : β) : α ⟶' β := HasFun.mkFun' (h.constIsFun α c)
  def constFun  (α : V) {β : V} (c : β) : α ⟶  β := HasFun.mkFun  (h.constIsFun α c)

  @[simp] theorem constFun.eff (α : V) {β : V} (c : β) (a : α) : (constFun α c) a = c :=
  by apply HasFun.mkFun.eff

  def constFunFun' (α β : V) : β ⟶' (α ⟶ β) := HasFun.mkFun' (h.constFunIsFun α β)
  def constFunFun  (α β : V) : β ⟶  (α ⟶ β) := HasFun.mkFun  (h.constFunIsFun α β)

  @[simp] theorem constFunFun.eff (α β : V) (c : β) : (constFunFun α β) c = constFun α c :=
  by apply HasFun.mkFun.eff

  def appFun' {α : V} (a : α) (β : V) : (α ⟶ β) ⟶' β := HasFun.mkFun' (h.appIsFun a β)
  def appFun  {α : V} (a : α) (β : V) : (α ⟶ β) ⟶  β := HasFun.mkFun  (h.appIsFun a β)

  @[simp] theorem appFun.eff {α : V} (a : α) (β : V) (F : α ⟶ β) : (appFun a β) F = F a :=
  by apply HasFun.mkFun.eff

  def appFunFun' (α β : V) : α ⟶' (α ⟶ β) ⟶ β := HasFun.mkFun' (h.appFunIsFun α β)
  def appFunFun  (α β : V) : α ⟶  (α ⟶ β) ⟶ β := HasFun.mkFun  (h.appFunIsFun α β)

  @[simp] theorem appFunFun.eff (α β : V) (a : α) : (appFunFun α β) a = appFun a β :=
  by apply HasFun.mkFun.eff

  def dupFun' {α β : V} (F : α ⟶' α ⟶ β) : α ⟶' β := HasFun.mkFun' (h.dupIsFun F)
  def dupFun  {α β : V} (F : α ⟶  α ⟶ β) : α ⟶  β := HasFun.mkFun  (h.dupIsFun (HasFun.toBundled F))

  @[simp] theorem dupFun.eff {α β : V} (F : α ⟶ α ⟶ β) (a : α) : (dupFun F) a = F a a :=
  by apply HasFun.mkFun.eff

  def dupFunFun' (α β : V) : (α ⟶ α ⟶ β) ⟶' (α ⟶ β) := HasFun.mkFun' (h.dupFunIsFun α β)
  def dupFunFun  (α β : V) : (α ⟶ α ⟶ β) ⟶  (α ⟶ β) := HasFun.mkFun  (h.dupFunIsFun α β)

  @[simp] theorem dupFunFun.eff (α β : V) (F : α ⟶ α ⟶ β) : (dupFunFun α β) F = dupFun F :=
  by apply HasFun.mkFun.eff

  def compFun' {α β γ : V} (F : α ⟶' β) (G : β ⟶' γ) : α ⟶' γ := HasFun.mkFun' (h.compIsFun F                    G)
  def compFun  {α β γ : V} (F : α ⟶  β) (G : β ⟶  γ) : α ⟶  γ := HasFun.mkFun  (h.compIsFun (HasFun.toBundled F) (HasFun.toBundled G))

  @[simp] theorem compFun.eff {α β γ : V} (F : α ⟶ β) (G : β ⟶ γ) (a : α) : (compFun F G) a = G (F a) :=
  by apply HasFun.mkFun.eff

  def compFunFun' {α β : V} (F : α ⟶' β) (γ : V) : (β ⟶ γ) ⟶' (α ⟶ γ) := HasFun.mkFun' (h.compFunIsFun F                    γ)
  def compFunFun  {α β : V} (F : α ⟶  β) (γ : V) : (β ⟶ γ) ⟶  (α ⟶ γ) := HasFun.mkFun  (h.compFunIsFun (HasFun.toBundled F) γ)

  @[simp] theorem compFunFun.eff {α β : V} (F : α ⟶ β) (γ : V) (G : β ⟶ γ) : (compFunFun F γ) G = compFun F G :=
  by apply HasFun.mkFun.eff

  def compFunFunFun' (α β γ : V) : (α ⟶ β) ⟶' (β ⟶ γ) ⟶ (α ⟶ γ) := HasFun.mkFun' (h.compFunFunIsFun α β γ)
  def compFunFunFun  (α β γ : V) : (α ⟶ β) ⟶  (β ⟶ γ) ⟶ (α ⟶ γ) := HasFun.mkFun  (h.compFunFunIsFun α β γ)
  
  @[simp] theorem compFunFunFun.eff (α β γ : V) (F : α ⟶ β) : (compFunFunFun α β γ) F = compFunFun F γ :=
  by apply HasFun.mkFun.eff

  def revCompFun' {α β γ : V} (G : β ⟶' γ) (F : α ⟶' β) : α ⟶' γ := compFun' F G
  def revCompFun  {α β γ : V} (G : β ⟶  γ) (F : α ⟶  β) : α ⟶  γ := compFun  F G

  infixr:90 " ⊙' " => revCompFun'
  infixr:90 " ⊙ "  => revCompFun

end HasFunOp



-- TODO: Introduce products (with functorial construction and projection)
--       and equivalences (with functorial projection to product of to/inv functors)
-- We should be able to prove the arrow/product laws.



class IsKind (V : Sort v) extends HasFun V, HasFunOp V



def GeneralizedProperty (α : Sort u) (V : Sort v) [HasInstances V] := α → V

namespace GeneralizedProperty

  variable {α : Sort u} {V : Sort v} [s : HasInstances V]

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

def GeneralizedRelation (α : Sort u) (V : Sort v) [IsKind V] := α → α → V

namespace GeneralizedRelation

  variable {α : Sort u} {V : Sort v} [s : IsKind V]

  instance hasInstances : HasInstances (GeneralizedRelation α V) := ⟨λ R => ∀ a b, R a b⟩

  section Properties

    variable (R : GeneralizedRelation α V)

    class HasRefl  where
    (refl  (a     : α) : R a a)

    class HasSymm  where
    (symm  {a b   : α} : R a b ⟶ R b a)

    class HasTrans where
    (trans {a b c : α} : R a b ⟶ R b c ⟶ R a c)

    class IsPreorder    extends HasRefl R, HasTrans R
    class IsEquivalence extends IsPreorder R, HasSymm R
  
  end Properties

  def HasSymm.symm' {R : GeneralizedRelation α V} [h : HasSymm R] {a b : α} (f : R a b) : R b a := h.symm f
  def HasTrans.trans''  {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} (f : R a b) : R b c ⟶ R a c := h.trans f
  def HasTrans.trans' {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} (f : R a b) (g : R b c) : R a c := trans'' f g

  -- When reasoning about instances of `R a b`, we would like to write `trans` as composition, `refl` as
  -- identity, and `symm` as inverse.
  -- Note that `R` can be inferred from `f : R a b` by elaboration.

  section Notation

    def revComp {R : GeneralizedRelation α V} [HasTrans R] {a b c : α} (g : R b c) (f : R a b) := HasTrans.trans' f g
    infixr:90 " • " => revComp

    def ident (R : GeneralizedRelation α V) [HasRefl R] (a : α) : R a a := HasRefl.refl a

    def inv {R : GeneralizedRelation α V} [HasSymm R] {a b : α} (f : R a b) := HasSymm.symm' f
    postfix:max "⁻¹" => inv

  end Notation

end GeneralizedRelation

open GeneralizedRelation



-- We can attach products, arrows, and/or equivalences to a given sort, in the form of generalized
-- relations satisfying appropriate properties.

section AttachedRelations

  variable (α : Sort u) (V : Sort v) [s : IsKind V]

  class HasProducts where
  (Product : GeneralizedRelation α V)
  [hasSymm : HasSymm Product]

  namespace HasProducts
    variable [h : HasProducts α V]
    instance productSymm : HasSymm h.Product := h.hasSymm
    instance hasProduct : HasProduct α α := ⟨h.Product⟩
    instance : IsKind (HasProduct.γ α α) := s
    instance : HasSymm (@HasProduct.Product α α (hasProduct α V)) := h.hasSymm
  end HasProducts

  class HasArrows where
  (Arrow      : GeneralizedRelation α V)
  [isPreorder : IsPreorder Arrow]

  namespace HasArrows
    variable [h : HasArrows α V]
    instance arrowPreorder : IsPreorder h.Arrow := h.isPreorder
    instance hasArrow : HasArrow' α α := ⟨h.Arrow⟩
    instance : IsKind (HasArrow'.γ α α) := s
    instance : IsPreorder (@HasArrow'.Arrow α α (hasArrow α V)) := h.isPreorder
  end HasArrows

  class HasEquivalences where
  (Equiv   : GeneralizedRelation α V)
  [isEquiv : IsEquivalence Equiv]

  namespace HasEquivalences
    variable [h : HasEquivalences α V]
    instance equivEquivalence : IsEquivalence h.Equiv := h.isEquiv
    instance hasEquivalence : HasEquivalence α α := ⟨h.Equiv⟩
    instance : IsKind (HasEquivalence.γ α α) := s
    instance : IsEquivalence (@HasEquivalence.Equiv α α (hasEquivalence α V)) := h.isEquiv
  end HasEquivalences

end AttachedRelations

namespace HasEquivalences
  variable {α : Sort u} {V : Sort v} [IsKind V] (h : HasEquivalences α V)
  def toHasProducts : HasProducts α V := ⟨h.Equiv⟩
  def toHasArrows   : HasArrows   α V := ⟨h.Equiv⟩
end HasEquivalences



def GeneralizedDependentProperty {U : Sort u} [IsKind U] {V : Sort v} [IsKind V] (P : GeneralizedProperty U V)
                                 (W : Sort w) [IsKind W] :=
∀ {α}, P α → (α → W)

namespace GeneralizedDependentProperty

  variable {U : Sort u} [IsKind U] {V : Sort v} [IsKind V] {P : GeneralizedProperty U V} {W : Sort w} [IsKind W]

  section Properties

    variable (D : GeneralizedDependentProperty P W)

    class HasDependentInst [h : HasInst P] where
    (inst {α : U} (a : α) : D (h.inst α) a)

    def instProp [h : HasInst P] (α : U) : GeneralizedProperty (HasInstances.Inst α) W := D (h.inst α)
    instance [HasInst P] [h : HasDependentInst D] (α : U) : HasInst (instProp D α) := ⟨h.inst⟩

  end Properties

end GeneralizedDependentProperty

open GeneralizedDependentProperty



def GeneralizedDependentRelation {U : Sort u} [IsKind U] {V : Sort v} [IsKind V] (R : GeneralizedRelation U V)
                                 (W : Sort w) [IsKind W] :=
∀ {α β}, R α β → (α → β → W)

namespace GeneralizedDependentRelation

  variable {U : Sort u} [IsKind U] {V : Sort v} [IsKind V] {R : GeneralizedRelation U V} {W : Sort w} [IsKind W]

  section Properties

    variable (D : GeneralizedDependentRelation R W)

    class HasDependentRefl  [h : HasRefl  R] where
    (refl  {α     : U}                         (a : α)                 : D (h.refl α) a a)

    def reflRel [h : HasRefl R] (α : U) : GeneralizedRelation (HasInstances.Inst α) W := D (h.refl α)
    instance [HasRefl R] [h : HasDependentRefl D] (α : U) : HasRefl (reflRel D α) := ⟨h.refl⟩

    class HasDependentSymm  [h : HasSymm  R] where
    (symm  {α β   : U} {F : R α β}             {a : α} {b : β}         : D F a b ⟶ D (h.symm F) b a)

    class HasDependentTrans [h : HasTrans R] where
    (trans {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} : D F a b ⟶ D G b c ⟶ D (h.trans F G) a c)

    class IsDependentPreorder    [h : IsPreorder    R] extends HasDependentRefl D, HasDependentTrans D
    class IsDependentEquivalence [h : IsEquivalence R] extends IsDependentPreorder D, HasDependentSymm D

  end Properties

  def HasDependentSymm.symm' {D : GeneralizedDependentRelation R W} [HasSymm R] [h : HasDependentSymm D] {α β : U}
                             {F : R α β} {a : α} {b : β} (f : D F a b) : D (HasSymm.symm' F) b a :=
  h.symm f

  def HasDependentTrans.trans'' {D : GeneralizedDependentRelation R W} [HasTrans R] [h : HasDependentTrans D] {α β γ : U}
                                {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (f : D F a b) :
    D G b c ⟶ D (HasTrans.trans' F G) a c :=
  h.trans f

  def HasDependentTrans.trans'  {D : GeneralizedDependentRelation R W} [HasTrans R] [h : HasDependentTrans D] {α β γ : U}
                                {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (f : D F a b) (g : D G b c) :
    D (HasTrans.trans' F G) a c
  := h.trans f g

  section Notation

    def depRevComp {D : GeneralizedDependentRelation R W} [HasTrans R] [HasDependentTrans D] {α β γ : U}
                   {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (g : D G b c) (f : D F a b) :
      D (G • F) a c :=
    HasDependentTrans.trans' f g
    -- TODO: What is the correct way to overload this?
    --infixr:90 " • " => depRevComp

    def depIdent (D : GeneralizedDependentRelation R W) [HasRefl R] [HasDependentRefl D] {α : U} (a : α) :
      D (ident R α) a a :=
    HasDependentRefl.refl a

    def depInv {D : GeneralizedDependentRelation R W} [HasSymm R] [HasDependentSymm D] {α β : U}
               {F : R α β} {a : α} {b : β} (f : D F a b) :
      D F⁻¹ b a :=
    HasDependentSymm.symm' f
    --postfix:max "⁻¹" => depInv

  end Notation

end GeneralizedDependentRelation

open GeneralizedDependentRelation



section AttachedDependentRelations

  variable (U : Sort u) [IsKind U] (V : Sort v) [IsKind V] (W : Sort w) [IsKind W]

  class HasDependentProducts [h : HasProducts U V] where
  (Product : GeneralizedDependentRelation h.Product W)
  [hasSymm : HasDependentSymm Product]

  namespace HasDependentProducts
    variable [HasProducts U V] [h : HasDependentProducts U V W]
    instance productSymm : HasDependentSymm h.Product := h.hasSymm
    notation:35 a:36 " ⊓[" P:0 "] " b:36 => HasDependentProducts.Product P a b
    notation:35 a:36 " ⊓[" P:0 "," V:0 "," W:0 "] " b:36 => HasDependentProducts.Product (V := V) (W := W) P a b
  end HasDependentProducts

  class HasDependentArrows [h : HasArrows U V] where
  (Arrow      : GeneralizedDependentRelation h.Arrow W)
  [isPreorder : IsDependentPreorder Arrow]

  namespace HasDependentArrows
    variable [HasArrows U V] [h : HasDependentArrows U V W]
    instance arrowPreorder : IsDependentPreorder h.Arrow := h.isPreorder
    notation:20 a:21 " ⇝[" F:0 "] " b:21 => HasDependentArrows.Arrow F a b
    notation:20 a:21 " ⇝[" F:0 "," V:0 "," W:0 "] " b:21 => HasDependentArrows.Arrow (V := V) (W := W) F a b
  end HasDependentArrows

  class HasDependentEquivalences [h : HasEquivalences U V] where
  (Equiv   : GeneralizedDependentRelation h.Equiv W)
  [isEquiv : IsDependentEquivalence Equiv]

  namespace HasDependentEquivalences
    variable [HasEquivalences U V] [h : HasDependentEquivalences U V W]
    instance equivEquivalence : IsDependentEquivalence h.Equiv := h.isEquiv
    notation:25 a:26 " ≃[" F:0 "] " b:26 => HasDependentEquivalences.Equiv F a b
    notation:25 a:26 " ≃[" F:0 "," V:0 "," W:0 "] " b:26 => HasDependentEquivalences.Equiv (V := V) (W := W) F a b
  end HasDependentEquivalences

end AttachedDependentRelations



-- When defining the groupoid axioms, we need to compare equivalences for equivalence. Although this will
-- frequently be an equality or at least a setoid equivalence, we need to prepare for the most generic
-- case where equivalences are arbitrary objects. Since we then need to define a relation into the type
-- of equivalences, we need to bundle equivalences with their equivalences.
--
-- TODO: describe arrows

class HasInstanceArrows (V : Sort v) [s : IsKind V] where
(ArrowKind                                    : Sort w)
[arrowIsKind                                  : IsKind ArrowKind]
[hasArrows (α : V)                            : HasArrows (s.Inst α) ArrowKind]
(arrowCongr {α β : V} {F G : α ⟶ β} {a b : α} : (hasArrows (α ⟶ β)).Arrow F G ⟶
                                                (hasArrows α).Arrow a b ⟶
                                                (hasArrows β).Arrow (F a) (G b))

namespace HasInstanceArrows

  variable (V : Sort v) [s : IsKind V] [h : HasInstanceArrows V]

  instance arrowKind : IsKind h.ArrowKind := h.arrowIsKind
  instance instArrows (α : V) : HasArrows (s.Inst α) h.ArrowKind := h.hasArrows α
  def InstArrow (α : V) : GeneralizedRelation (s.Inst α) h.ArrowKind := (instArrows V α).Arrow

  @[reducible] def InstArrowType (α : V) := s.Inst α (⇝) s.Inst α

  -- Again, this is potentially endless...
  instance (α β     : V) : HasArrow (InstArrowType V α)                (InstArrowType V β)                                    := HasFun.hasArrow
  instance (α β     : V) : IsKind   (InstArrowType V α (⟶)              InstArrowType V β)                                    := h.arrowIsKind
  instance (α β γ   : V) : HasArrow (InstArrowType V α)    (InstArrowType V β (⟶)              InstArrowType V γ)             := HasFun.hasArrow
  instance (α β γ   : V) : IsKind   (InstArrowType V α (⟶) (InstArrowType V β (⟶)              InstArrowType V γ))            := h.arrowIsKind
  instance (α β γ δ : V) : HasArrow (InstArrowType V α)    (InstArrowType V β (⟶) (InstArrowType V γ (⟶) InstArrowType V δ))  := HasFun.hasArrow
  instance (α β γ δ : V) : IsKind   (InstArrowType V α (⟶) (InstArrowType V β (⟶) (InstArrowType V γ (⟶) InstArrowType V δ))) := h.arrowIsKind

  def arrCongr {α β : V} {F G : α ⟶{V} β} {a b : α} : (F ⇝ G) ⟶ (a ⇝ b) ⟶ (F a ⇝ G b) := h.arrowCongr

end HasInstanceArrows

class HasInstanceEquivalences (V : Sort v) [s : IsKind V] extends HasInstanceArrows V where
[arrowSymm (α : V) : HasSymm (hasArrows α).Arrow]

namespace HasInstanceEquivalences

  variable (V : Sort v) [s : IsKind V] [h : HasInstanceEquivalences V]

  instance (α : V) : HasSymm (h.hasArrows α).Arrow := h.arrowSymm α
  instance arrowIsEquiv (α : V) : IsEquivalence (h.hasArrows α).Arrow := ⟨⟩
  instance instEquivs (α : V) : HasEquivalences (s.Inst α) h.ArrowKind := ⟨(h.hasArrows α).Arrow⟩

  @[reducible] def InstEquivType (α : V) := s.Inst α (≃) s.Inst α

  -- Again, this is potentially endless...
  instance (α β     : V) : HasArrow (InstEquivType V α)                (InstEquivType V β)                                    := HasFun.hasArrow
  instance (α β     : V) : IsKind   (InstEquivType V α (⟶)              InstEquivType V β)                                    := h.arrowIsKind
  instance (α β γ   : V) : HasArrow (InstEquivType V α)    (InstEquivType V β (⟶)              InstEquivType V γ)             := HasFun.hasArrow
  instance (α β γ   : V) : IsKind   (InstEquivType V α (⟶) (InstEquivType V β (⟶)              InstEquivType V γ))            := h.arrowIsKind
  instance (α β γ δ : V) : HasArrow (InstEquivType V α)    (InstEquivType V β (⟶) (InstEquivType V γ (⟶) InstEquivType V δ))  := HasFun.hasArrow
  instance (α β γ δ : V) : IsKind   (InstEquivType V α (⟶) (InstEquivType V β (⟶) (InstEquivType V γ (⟶) InstEquivType V δ))) := h.arrowIsKind

  instance : HasFun V := s.toHasFun

  def funCongr {α β : V} {F G : α ⟶{V} β} {a b : α} : F ≃ G ⟶ a ≃ b ⟶ F a ≃ G b := h.arrowCongr

end HasInstanceEquivalences

class HasInstanceEquivalences' (V : Sort v) [s : IsKind V] where
(EquivKind                                    : Sort w)
[equivIsKind                                  : IsKind EquivKind]
[hasEquivalences (α : V)                      : HasEquivalences (s.Inst α) EquivKind]
(equivCongr {α β : V} {F G : α ⟶ β} {a b : α} : (hasEquivalences (α ⟶ β)).Equiv F G ⟶
                                                (hasEquivalences α).Equiv a b ⟶
                                                (hasEquivalences β).Equiv (F a) (G b))

namespace HasInstanceEquivalences'

  variable {V : Sort v} [s : IsKind V] [h : HasInstanceEquivalences' V]

  instance equivKind : IsKind h.EquivKind := h.equivIsKind

  instance toHasInstancesEquivalences : HasInstanceEquivalences V :=
  { ArrowKind   := h.EquivKind,
    arrowIsKind := h.equivIsKind,
    hasArrows   := λ α => HasEquivalences.toHasArrows (h.hasEquivalences α),
    arrowCongr  := h.equivCongr,
    arrowSymm   := λ α => (h.hasEquivalences α).isEquiv.toHasSymm }

end HasInstanceEquivalences'


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

  variable {α : Sort u} {V : Sort v} [IsKind V] [HasInstanceArrows V] (R : GeneralizedRelation α V)

  class IsCompositionRelation extends HasTrans R where
  (assocLR {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : (h • g) • f ⇝ h • (g • f))
  (assocRL {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : h • (g • f) ⇝ (h • g) • f)

  class IsMorphismRelation extends IsCompositionRelation R, HasRefl R where
  (leftId  {a b : α} (f : R a b) : ident R b • f ⇝ f)
  (rightId {a b : α} (f : R a b) : f • ident R a ⇝ f)

  instance morPreorder [IsMorphismRelation R] : IsPreorder R := ⟨⟩

  class IsIsomorphismRelation extends IsMorphismRelation R, HasSymm R where
  (leftInv  {a b   : α} (f : R a b)             : f⁻¹ • f       ⇝ ident R a)
  (rightInv {a b   : α} (f : R a b)             : f • f⁻¹       ⇝ ident R b)
  (invInv   {a b   : α} (f : R a b)             : (f⁻¹)⁻¹       ⇝ f)
  (compInv  {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹     ⇝ f⁻¹ • g⁻¹)
  (idInv    (a     : α)                         : (ident R a)⁻¹ ⇝ ident R a)

  instance isoEquiv [IsIsomorphismRelation R] : IsEquivalence R := ⟨⟩

end Morphisms



section Functors

  variable {α : Sort u} {V : Sort v} {W : Sort w} [IsKind V] [IsKind W] [HasInstanceArrows W] [HasIsFun V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation α W)

  def BaseFunctor := ∀ {a b}, R a b ⟶' S a b

  variable (F : BaseFunctor R S)

  class IsReflFunctor  [HasRefl  R] [HasRefl  S] where
  (respectsRefl  (a     : α)                         : F (ident R a) ⇝ ident S a)

  class IsSymmFunctor  [HasSymm  R] [HasSymm  S] where
  (respectsSymm  {a b   : α} (f : R a b)             : F f⁻¹         ⇝ (F f)⁻¹)

  class IsTransFunctor [HasTrans R] [HasTrans S] where
  (respectsTrans {a b c : α} (f : R a b) (g : R b c) : F (g • f)     ⇝ F g • F f)

  class IsPreorderFunctor    [IsPreorder    R] [IsPreorder    S] extends IsReflFunctor R S F, IsTransFunctor R S F
  class IsEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] extends IsPreorderFunctor R S F, IsSymmFunctor R S F

end Functors



section NaturalTransformations

  variable {α : Sort u} {β : Sort w} {V : Sort v} {W : Sort w} [IsKind V] [IsKind W] [HasInstanceEquivalences W] [HasIsFun V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation β W) [h : HasTrans S]
           {mF mG : α → β} (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) (G : ∀ {a b}, R a b ⟶' S (mG a) (mG b))

  class IsNaturalTransformation (n : ∀ a, S (mF a) (mG a)) where
  (nat {a b : α} (f : R a b) : G f • n a ≃ n b • F f)

end NaturalTransformations



-- TODO: If arrows have equivalences, we can specify redundancies.



class IsCategory (α : Sort u) {MorphismKind : Sort v} [IsKind MorphismKind] [HasInstanceEquivalences MorphismKind] where
(M     : GeneralizedRelation α MorphismKind)
[isMor : IsMorphismRelation M]
