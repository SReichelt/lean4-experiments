--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- A variant of `Structure` where equivalences are `Structure`s instead of setoids.



import Structure.Basic



open Morphisms
open Functors
open HasStructure
open Structure



-- A 2-structure is simply a structure where equivalences are (1-)structures.
-- We can reuse `HasIsomorphisms` because it accepts generic equivalences; however we additionally need
-- the combinations of `trans`/`comp_congrArg` and `symm`/`inv_congrArg` to be functorial.

class HasTwoStructure (α : Sort u) where
(M       : GeneralizedRelation α Structure)
[hasIsos : HasIsomorphisms M]
[comp_congrArg_left_functor  {a b c : α} (f : M a b) :
   IsIsomorphismFunctor (iso (M b c)) (mapRelation (λ g => hasIsos.trans f g) (iso (M a c)))
                        (λ eg => hasIsos.comp_congrArg (id_ f) eg)]
[comp_congrArg_right_functor {a b c : α} (g : M b c) :
   IsIsomorphismFunctor (iso (M a b)) (mapRelation (λ f => hasIsos.trans f g) (iso (M a c)))
                        (λ ef => hasIsos.comp_congrArg ef (id_ g))]
[inv_congrArg_functor        {a b   : α}             :
   IsIsomorphismFunctor (iso (M a b)) (mapRelation hasIsos.symm (iso (M b a))) hasIsos.inv_congrArg]

namespace HasTwoStructure

variable {α : Sort u} [h : HasTwoStructure α]

instance hasGeneralStructure : HasGeneralStructure α :=
{ equivType := Structure,
  M         := h.M,
  hasIsos   := h.hasIsos }

instance hasIso : HasIsomorphisms h.M := h.hasIsos

end HasTwoStructure



instance structureHasTwoStructure : HasTwoStructure Structure :=
{ M                           := StructureEquiv.equivStructure,
  hasIsos                     := StructureEquiv.equivHasIso,
  comp_congrArg_left_functor  := sorry,
  comp_congrArg_right_functor := sorry,
  inv_congrArg_functor        := sorry }



structure TwoStructure where
(α         : Sort u)
[hasStruct : HasTwoStructure α]

namespace TwoStructure

instance structureIsType : IsType TwoStructure := ⟨TwoStructure.α⟩

def iso (S : TwoStructure) : GeneralizedRelation (IsType.type S) Structure := S.hasStruct.M

variable {S : TwoStructure}

instance hasTwoStructure : HasTwoStructure (IsType.type S) := S.hasStruct
instance hasGeneralStructure : HasGeneralStructure (IsType.type S) := HasTwoStructure.hasGeneralStructure (h := hasTwoStructure)
instance hasIso : HasIsomorphisms (iso S) := hasGeneralStructure.hasIso

instance twoStructureIsTypeWithEquiv : IsTypeWithEquivalence TwoStructure :=
{ type  := TwoStructure.α,
  equiv := λ S => HasGeneralStructure.hasInstEquiv (h := hasGeneralStructure) }

end TwoStructure



instance universeTwoStructure : TwoStructure := ⟨Structure⟩
