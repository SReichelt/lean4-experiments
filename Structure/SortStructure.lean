--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- This file extends `Basic.lean` with definitions that are related to `Equiv` from mathlib.
--
-- For more information, see the comment at the top of `Structure.lean`.



import Structure.Basic

-- A quick&dirty port of the parts of `data.equiv.basic` we need; should be replaced once it becomes
-- available in Lean 4 mathlib.
import Structure.Data.Equiv

open Morphisms
open StructureFunctor
open SetoidStructureEquiv



universe u



-- Define instances for `Equiv` to fit it into our more abstract framework.

namespace Equiv

def equivRel := genRel Equiv

instance genEquiv : IsEquivalence   equivRel := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

instance hasComp  : HasComp         equivRel := ⟨Equiv.trans⟩

theorem congrArgComp {α β γ : Sort u} {f₁ f₂ : equivRel α β} {g₁ g₂ : equivRel β γ} (h₁ : f₁ ≈ f₂) (h₂ : g₁ ≈ g₂) :
  g₁ • f₁ ≈ g₂ • f₂ :=
let h := congr (congrArg Equiv.trans h₁) h₂;
h

instance hasCmp   : HasComposition  equivRel := ⟨congrArgComp, Equiv.transAssoc⟩

instance hasId    : HasId           equivRel := ⟨Equiv.refl⟩

theorem leftId  {α β : Sort u} (f : equivRel α β) : id__ β • f ≈ f := Equiv.transRefl f
theorem rightId {α β : Sort u} (f : equivRel α β) : f • id__ α ≈ f := Equiv.reflTrans f

instance hasMor   : HasMorphisms    equivRel := ⟨leftId, rightId⟩

instance hasInv   : HasInv          equivRel := ⟨Equiv.symm⟩

theorem congrArgInv {α β : Sort u} {f₁ f₂ : equivRel α β} (h₁ : f₁ ≈ f₂) :
  f₁⁻¹ ≈ f₂⁻¹ :=
congrArg Equiv.symm h₁

instance hasIso   : HasIsomorphisms equivRel := ⟨congrArgInv, Equiv.transSymm, Equiv.symmTrans,
                                                 Equiv.symmSymm, Equiv.symmTransSymm, λ _ => Equiv.reflSymm⟩

end Equiv



-- Now, `Equiv` gives us a structure for `Sort u`.

instance sortHasStructure  : HasStructure (Sort u) := ⟨Equiv.equivRel⟩
def sortStructure : Structure := ⟨Sort u⟩



-- When using `sortStructure` to encode `Sort u` as a `Structure` with equivalences given by `Equiv`,
-- we also want to transport individual instances `x : α` of a type `α : Sort u` along an encoded
-- `Equiv`. Since the introductory description in `Basic.lean` contains precisely this operation, we
-- need to provide an abstraction for it.
--
-- `universeStructure` enables us to do exactly that: The function `instanceStructure`, which encodes
-- a given Lean type as a `Structure` with equivalence given by equality, is actually a functor from
-- `sortStructure` to `universeStructure`. This functor transports an `Equiv` between two types to a
-- `StructureEquiv` between the corresponding instance structures. And `StructureEquiv` provides the
-- necessary operation of transporting an instance of one structure to the other.
--
-- The benefit of this encoding is that `StructureEquiv` is much more general than the original
-- `Equiv` because many different objects can be encoded as instances of `Structure`.



-- An equivalence between instance structures is actually the same as `Equiv`.

def InstanceStructureEquiv (α β : Sort u) := StructureEquiv (instanceStructure α) (instanceStructure β)

def instanceStructureEquiv {α β : Sort u} (e : Equiv α β) : InstanceStructureEquiv α β :=
{ toFun    := instanceStructureFunctor e.toFun,
  invFun   := instanceStructureFunctor e.invFun,
  leftInv  := e.leftInv,
  rightInv := e.rightInv }

instance {α β : Sort u} : Coe (Equiv α β) (InstanceStructureEquiv α β) := ⟨instanceStructureEquiv⟩

@[simp] theorem instanceEquiv {α β : Sort u} (e : Equiv α β) (a : α) (b : β) :
  InstanceEquiv (instanceStructureEquiv e) a b = (e.toFun a = b) :=
rfl



-- To use `instanceStructure` as a functor into `universeStructure`, we need to coerce equivalences to
-- setoids after applying `instanceStructureEquiv`.

theorem Setoid.fromEq {α : Sort u} [Setoid α] {a b : α} (h : a = b) : a ≈ b :=
h ▸ Setoid.refl a

def instanceStructureEquiv' {α β : Sort u} (e : Equiv α β) := toSetoidStructureEquiv (instanceStructureEquiv e)

namespace instanceStructureEquiv'

theorem respectsSetoid {α β   : Sort u} {e₁ e₂ : Equiv α β} (h : e₁ = e₂) :
  instanceStructureEquiv' e₁ ≈ instanceStructureEquiv' e₂ :=
Setoid.fromEq (congrArg instanceStructureEquiv' h)

theorem respectsComp   {α β γ : Sort u} (e : Equiv α β) (f : Equiv β γ) :
  instanceStructureEquiv' (Equiv.trans e f) ≈ SetoidStructureEquiv.trans (instanceStructureEquiv' e) (instanceStructureEquiv' f) :=
Setoid.refl (instanceStructureEquiv' (Equiv.trans e f))

theorem respectsId     (α     : Sort u) :
  instanceStructureEquiv' (Equiv.refl α) ≈ SetoidStructureEquiv.refl (instanceStructure α) :=
Setoid.refl (instanceStructureEquiv' (Equiv.refl α))

theorem respectsInv    {α β   : Sort u} (e : Equiv α β) :
  instanceStructureEquiv' (Equiv.symm e) ≈ SetoidStructureEquiv.symm (instanceStructureEquiv' e) :=
Setoid.refl (instanceStructureEquiv' (Equiv.symm e))

end instanceStructureEquiv'

def sortToStructureFunctor : StructureFunctor sortStructure universeStructure :=
{ map     := instanceStructure,
  functor := { FF        := instanceStructureEquiv',
               isFunctor := { respectsSetoid := instanceStructureEquiv'.respectsSetoid,
                              respectsComp   := instanceStructureEquiv'.respectsComp,
                              respectsId     := instanceStructureEquiv'.respectsId,
                              respectsInv    := instanceStructureEquiv'.respectsInv } } }



-- If we have an `Equiv` with a type that has a structure, we can transport the structure along
-- that `Equiv`.

instance hasEquivalentStructure {α : Sort u} {β : Sort v} [h : HasStructure β] (e : Equiv α β) : HasStructure α :=
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
