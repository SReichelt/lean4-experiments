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

def equivRel := RelationWithSetoid.relWithEq Equiv

instance genEquiv : IsEquivalence equivRel :=
{ refl  := Equiv.refl,
  symm  := Equiv.symm,
  trans := Equiv.trans }

theorem comp_congrArg {α β γ : Sort u} {f₁ f₂ : equivRel α β} {g₁ g₂ : equivRel β γ} (h₁ : f₁ ≈ f₂) (h₂ : g₁ ≈ g₂) :
  g₁ • f₁ ≈ g₂ • f₂ :=
let h := congr (congrArg Equiv.trans h₁) h₂;
h

theorem inv_congrArg {α β : Sort u} {f₁ f₂ : equivRel α β} (h₁ : f₁ ≈ f₂) :
  f₁⁻¹ ≈ f₂⁻¹ :=
congrArg Equiv.symm h₁

instance hasIso : HasIsomorphisms equivRel :=
{ comp_congrArg := comp_congrArg,
  inv_congrArg  := inv_congrArg,
  assoc         := Equiv.trans_assoc,
  leftId        := Equiv.trans_refl,
  rightId       := Equiv.refl_trans,
  leftInv       := Equiv.trans_symm,
  rightInv      := Equiv.symm_trans,
  invInv        := Equiv.symm_symm,
  compInv       := Equiv.symm_trans_symm,
  idInv         := @Equiv.refl_symm }

end Equiv



-- Now, `Equiv` gives us a structure for `Sort u`.

instance sortHasStructure : HasStructure (Sort u) := ⟨Equiv.equivRel⟩
def sortStructure : Structure := ⟨Sort u⟩



-- When using `sortStructure` to encode `Sort u` as a `Structure` with equivalences given by `Equiv`,
-- we also want to transport individual instances `a : α` of a type `α : Sort u` along an encoded
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

def instanceStructureEquiv {α β : Sort u} (e : α ≃ β) : instanceStructure α ≃ instanceStructure β :=
{ toFun    := instanceStructureFunctor e.toFun,
  invFun   := instanceStructureFunctor e.invFun,
  isInv  := { leftInv  := { ext := e.leftInv,
                            nat := λ _ => proofIrrel _ _ },
              rightInv := { ext := e.rightInv,
                            nat := λ _ => proofIrrel _ _ },
              lrCompat := λ _ => proofIrrel _ _,
              rlCompat := λ _ => proofIrrel _ _ } }

namespace instanceStructureEquiv

@[simp] theorem instanceEquiv {α β : Sort u} (e : α ≃ β) (a : α) (b : β) :
  a ≃[instanceStructureEquiv e] b ↔ e.toFun a = b :=
Iff.rfl

theorem respectsEquiv {α β   : Sort u} {e₁ e₂ : α ≃ β} (h : e₁ = e₂) :
  instanceStructureEquiv e₁ ≈ instanceStructureEquiv e₂ :=
Setoid.of_Eq (congrArg instanceStructureEquiv h)

theorem respectsComp  {α β γ : Sort u} (e : α ≃ β) (f : β ≃ γ) :
  instanceStructureEquiv (Equiv.trans e f) ≈ StructureEquiv.trans (instanceStructureEquiv e) (instanceStructureEquiv f) :=
⟨{ toFunEquiv    := { ext := λ a => let c : instanceStructure γ := f.toFun  (e.toFun  a);
                                    let ⟨h⟩ := Setoid.refl c; h,
                      nat := λ _ => proofIrrel _ _ },
   invFunEquiv   := { ext := λ c => let a : instanceStructure α := e.invFun (f.invFun c);
                                    let ⟨h⟩ := Setoid.refl a; h,
                      nat := λ _ => proofIrrel _ _ },
   leftInvEquiv  := λ _ => proofIrrel _ _,
   rightInvEquiv := λ _ => proofIrrel _ _ }⟩

theorem respectsId    (α     : Sort u) :
  instanceStructureEquiv (Equiv.refl α) ≈ StructureEquiv.refl (instanceStructure α) :=
⟨{ toFunEquiv    := { ext := λ a => let ⟨h⟩ := Setoid.refl a; h,
                      nat := λ _ => proofIrrel _ _ },
   invFunEquiv   := { ext := λ a => let ⟨h⟩ := Setoid.refl a; h,
                      nat := λ _ => proofIrrel _ _ },
   leftInvEquiv  := λ _ => proofIrrel _ _,
   rightInvEquiv := λ _ => proofIrrel _ _ }⟩

theorem respectsInv   {α β   : Sort u} (e : α ≃ β) :
  instanceStructureEquiv (Equiv.symm e) ≈ StructureEquiv.symm (instanceStructureEquiv e) :=
⟨{ toFunEquiv    := { ext := λ b => let a : instanceStructure α := e.invFun b;
                                    let ⟨h⟩ := Setoid.refl a; h,
                      nat := λ _ => proofIrrel _ _ },
   invFunEquiv   := { ext := λ a => let b : instanceStructure β := e.toFun  a;
                                    let ⟨h⟩ := Setoid.refl b; h,
                      nat := λ _ => proofIrrel _ _ },
   leftInvEquiv  := λ _ => proofIrrel _ _,
   rightInvEquiv := λ _ => proofIrrel _ _ }⟩

end instanceStructureEquiv

def sortToStructureFunctor : StructureFunctor sortStructure universeStructure :=
{ map     := instanceStructure,
  functor := { mapEquiv  := instanceStructureEquiv,
               isFunctor := { respectsEquiv := instanceStructureEquiv.respectsEquiv,
                              respectsComp  := instanceStructureEquiv.respectsComp,
                              respectsId    := instanceStructureEquiv.respectsId,
                              respectsInv   := instanceStructureEquiv.respectsInv } } }



-- If we have an `Equiv` between two types where one has a structure, we can transport the structure
-- along that `Equiv`.

namespace EquivalentStructure

variable {α : Sort u} {β : Sort v} [h : HasStructure β] (e : α ≃ β)

def hasEquivalentStructure : HasStructure α :=
{ M       := λ x y => h.M (e.toFun x) (e.toFun y),
  hasIsos := { refl          := λ x => h.hasIsos.refl (e.toFun x),
               symm          := h.hasIsos.symm,
               trans         := h.hasIsos.trans,
               comp_congrArg := h.hasIsos.comp_congrArg,
               inv_congrArg  := h.hasIsos.inv_congrArg,
               assoc         := λ f g => h.hasIsos.assoc    f g,
               leftId        := λ f   => h.hasIsos.leftId   f,
               rightId       := λ f   => h.hasIsos.rightId  f,
               leftInv       := λ f   => h.hasIsos.leftInv  f,
               rightInv      := λ f   => h.hasIsos.rightInv f,
               invInv        := λ f   => h.hasIsos.invInv   f,
               compInv       := λ f g => h.hasIsos.compInv  f g,
               idInv         := λ x   => h.hasIsos.idInv    (e.toFun x) } }

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

def equivalentStructureDefEquiv : equivalentStructure e ≃ defaultStructure β :=
{ toFun  := equivalentStructureDefEquivToFun  e,
  invFun := equivalentStructureDefEquivInvFun e,
  isInv  := sorry }

end EquivalentStructure
