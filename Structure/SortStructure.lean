--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- This file extends `Basic.lean` with definitions that are related to `Equiv` from mathlib.



import Structure.Basic
import Structure.Forgetfulness

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic

open Morphisms
open Structure
open StructureFunctor
open Forgetfulness
open SetoidStructureEquiv



set_option autoBoundImplicitLocal false

universes u v



-- Define instances for `Equiv` to fit it into our more abstract framework.

namespace Equiv

def equivRel := genRel Equiv

instance genEquiv : IsEquivalence   equivRel := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

instance hasComp  : HasComp         equivRel := ⟨Equiv.trans⟩

theorem comp_congrArg {α β γ : Sort u} {f₁ f₂ : equivRel α β} {g₁ g₂ : equivRel β γ} (h₁ : f₁ ≈ f₂) (h₂ : g₁ ≈ g₂) :
  g₁ • f₁ ≈ g₂ • f₂ :=
let h := congr (congrArg Equiv.trans h₁) h₂;
h

instance hasCmp   : HasComposition  equivRel := ⟨comp_congrArg, Equiv.trans_assoc⟩

instance hasId    : HasId           equivRel := ⟨Equiv.refl⟩

theorem leftId  {α β : Sort u} (f : equivRel α β) : id_ β • f ≈ f := Equiv.trans_refl f
theorem rightId {α β : Sort u} (f : equivRel α β) : f • id_ α ≈ f := Equiv.refl_trans f

instance hasMor   : HasMorphisms    equivRel := ⟨leftId, rightId⟩

instance hasInv   : HasInv          equivRel := ⟨Equiv.symm⟩

theorem inv_congrArg {α β : Sort u} {f₁ f₂ : equivRel α β} (h₁ : f₁ ≈ f₂) :
  f₁⁻¹ ≈ f₂⁻¹ :=
congrArg Equiv.symm h₁

instance hasIso   : HasIsomorphisms equivRel := ⟨inv_congrArg, Equiv.trans_symm, Equiv.symm_trans,
                                                 Equiv.symm_symm, Equiv.symm_trans_symm, λ _ => Equiv.refl_symm⟩

end Equiv



-- Now, `Equiv` gives us a structure for `Sort u`.

instance sortHasStructure : HasStructure (Sort u) := ⟨Equiv.equivRel⟩
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

@[reducible] def InstanceStructureEquiv (α β : Sort u) := StructureEquiv (instanceStructure α) (instanceStructure β)

def instanceStructureEquiv {α β : Sort u} (e : α ≃ β) : InstanceStructureEquiv α β :=
{ toFun    := instanceStructureFunctor e.toFun,
  invFun   := instanceStructureFunctor e.invFun,
  isInv  := { leftInv  := { ext := e.leftInv,
                            nat := λ _ => proofIrrel _ _ },
              rightInv := { ext := e.rightInv,
                            nat := λ _ => proofIrrel _ _ },
              lrCompat := λ _ => proofIrrel _ _,
              rlCompat := λ _ => proofIrrel _ _ } }

namespace instanceStructureEquiv

instance {α β : Sort u} : Coe (α ≃ β) (InstanceStructureEquiv α β) := ⟨instanceStructureEquiv⟩

@[simp] theorem instanceEquiv {α β : Sort u} (e : α ≃ β) (a : α) (b : β) :
  (a ≃[instanceStructureEquiv e] b) = (e.toFun a = b) :=
rfl

theorem respectsSetoid {α β   : Sort u} {e₁ e₂ : α ≃ β} (h : e₁ = e₂) :
  instanceStructureEquiv e₁ ≈ instanceStructureEquiv e₂ :=
Setoid.of_Eq (congrArg instanceStructureEquiv h)

theorem respectsComp   {α β γ : Sort u} (e : α ≃ β) (f : β ≃ γ) :
  instanceStructureEquiv (Equiv.trans e f) ≈ StructureEquiv.trans (instanceStructureEquiv e) (instanceStructureEquiv f) :=
--⟨⟨makeToSetoidStructureFunctorEquiv (λ a => let c : setoidStructure (instanceStructure γ) := f.toFun  (e.toFun  a);
--                                            Setoid.refl c)⟩,
-- ⟨makeToSetoidStructureFunctorEquiv (λ c => let a : setoidStructure (instanceStructure α) := e.invFun (f.invFun c);
--                                            Setoid.refl a)⟩⟩
sorry

theorem respectsId     (α     : Sort u) :
  instanceStructureEquiv (Equiv.refl α) ≈ StructureEquiv.refl (instanceStructure α) :=
--⟨⟨makeToSetoidStructureFunctorEquiv (λ a => Setoid.refl a)⟩,
-- ⟨makeToSetoidStructureFunctorEquiv (λ a => Setoid.refl a)⟩⟩
sorry

theorem respectsInv    {α β   : Sort u} (e : α ≃ β) :
  instanceStructureEquiv (Equiv.symm e) ≈ StructureEquiv.symm (instanceStructureEquiv e) :=
--⟨⟨makeToSetoidStructureFunctorEquiv (λ b => let a : setoidStructure (instanceStructure α) := e.invFun b;
--                                            Setoid.refl a)⟩,
-- ⟨makeToSetoidStructureFunctorEquiv (λ a => let b : setoidStructure (instanceStructure β) := e.toFun  a;
--                                            Setoid.refl b)⟩⟩
sorry

end instanceStructureEquiv

def sortToStructureFunctor : StructureFunctor sortStructure universeStructure :=
{ map     := instanceStructure,
  functor := { mapEquiv  := instanceStructureEquiv,
               isFunctor := { respectsSetoid := instanceStructureEquiv.respectsSetoid,
                              respectsComp   := instanceStructureEquiv.respectsComp,
                              respectsId     := instanceStructureEquiv.respectsId,
                              respectsInv    := instanceStructureEquiv.respectsInv } } }



-- If we have an `Equiv` between two types where one has a structure, we can transport the structure
-- along that `Equiv`.

namespace EquivalentStructure

variable {α : Sort u} {β : Sort v} [h : HasStructure β] (e : α ≃ β)

def hasEquivalentStructure : HasStructure α :=
{ M       := λ x y => h.M (e.toFun x) (e.toFun y),
  hasIsos := { comp         := h.hasIsos.comp,
               comp_congrArg := h.hasIsos.comp_congrArg,
               assoc        := λ f g => h.hasIsos.assoc    f g,
               id           := λ x => h.hasIsos.id (e.toFun x),
               leftId       := λ f   => h.hasIsos.leftId   f,
               rightId      := λ f   => h.hasIsos.rightId  f,
               inv          := h.hasIsos.inv,
               inv_congrArg  := h.hasIsos.inv_congrArg,
               leftInv      := λ f   => h.hasIsos.leftInv  f,
               rightInv     := λ f   => h.hasIsos.rightInv f,
               invInv       := λ f   => h.hasIsos.invInv   f,
               compInv      := λ f g => h.hasIsos.compInv  f g,
               idInv        := λ x   => h.hasIsos.idInv    (e.toFun x) } }

def equivalentStructure := @defaultStructure α (hasEquivalentStructure e)

-- In particular, we can map equivalences in both directions.

def equivalentEquiv {x y : α} (f : iso (equivalentStructure e) x y) : e.toFun x ≃ e.toFun y := f

def equivalentEquivInv {x y : β} (f : x ≃ y) : iso (equivalentStructure e) (e.invFun x) (e.invFun y) :=
let h₁ := congr (congrArg h.M (e.rightInv x)) (e.rightInv y);
cast (congrArg BundledSetoid.α (Eq.symm h₁)) f

-- That gives us a `StructureEquiv` between the two structures.

def equivalentStructureDefEquivToFun : StructureFunctor (equivalentStructure e) (defaultStructure β) :=
{ map     := e.toFun,
  functor := { mapEquiv  := equivalentEquiv e,
               isFunctor := sorry } }

def equivalentStructureDefEquivInvFun : StructureFunctor (defaultStructure β) (equivalentStructure e) :=
{ map     := e.invFun,
  functor := { mapEquiv  := equivalentEquivInv e,
               isFunctor := sorry } }

def equivalentStructureDefEquiv : StructureEquiv (equivalentStructure e) (defaultStructure β) :=
{ toFun  := equivalentStructureDefEquivToFun  e,
  invFun := equivalentStructureDefEquivInvFun e,
  isInv  := sorry }

end EquivalentStructure
