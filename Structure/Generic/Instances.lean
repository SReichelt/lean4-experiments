--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- Very basic instances of the axioms in `Axioms.lean`.



import Structure.Generic.Axioms

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false

universes u v u' v' w



namespace AnySort

  instance hasInstances : HasInstances (Sort u) := ⟨id⟩

  instance hasIsFun : HasIsFun (Sort u) (Sort v) := ⟨λ _ => True⟩

  instance hasFun : HasFun (Sort u) :=
  { Fun      := λ α β => α → β,
    funEquiv := λ α β => { toFun    := λ f      => ⟨f, trivial⟩,
                           invFun   := λ F      => F.f,
                           leftInv  := λ f      => rfl,
                           rightInv := λ ⟨f, _⟩ => rfl } }

  instance hasFunOp : HasFunOp (Sort u) :=
  { idIsFun         := λ _     => trivial,
    constIsFun      := λ _ _ _ => trivial,
    constFunIsFun   := λ _ _   => trivial,
    appIsFun        := λ _ _   => trivial,
    appFunIsFun     := λ _ _   => trivial,
    dupIsFun        := λ _     => trivial,
    dupFunIsFun     := λ _ _   => trivial,
    compIsFun       := λ _ _   => trivial,
    compFunIsFun    := λ _ _   => trivial,
    compFunFunIsFun := λ _ _ _ => trivial }

  instance isKind : IsKind (Sort u) := ⟨⟩

end AnySort



def UnivRel (α : Sort u) : α → α → Prop := λ _ _ => True

def UnivRel.isEquivalence {α : Sort u} : Equivalence (UnivRel α) :=
⟨λ _ => trivial, λ _ => trivial, λ _ _ => trivial⟩

def EquivRel : GeneralizedRelation (Type u) (Type u) := Equiv

namespace GeneralizedRelation.IsEquivalence

  -- Every equivalence relation can trivially be converted to an instance of `IsEquivalence`.
  instance relEquiv {α : Sort u} {r : α → α → Prop} (e : Equivalence r) : IsEquivalence r :=
  { refl  := e.refl,
    symm  := e.symm,
    trans := e.trans }

  -- So these are the instances that we obtain directly from Lean.
  instance univ   (α : Sort u)                : IsEquivalence (UnivRel α) := relEquiv UnivRel.isEquivalence
  instance iff                                : IsEquivalence Iff         := relEquiv Iff.isEquivalence
  instance eq     (α : Sort u)                : IsEquivalence (@Eq α)     := relEquiv Eq.isEquivalence
  instance setoid (α : Sort u) [s : Setoid α] : IsEquivalence s.r         := relEquiv s.iseqv

  instance equiv : IsEquivalence EquivRel :=
  { refl  := Equiv.refl,
    symm  := Equiv.symm,
    trans := Equiv.trans }

end GeneralizedRelation.IsEquivalence



namespace HasProducts

  instance : GeneralizedRelation.HasSymm And := ⟨λ h => ⟨h.right, h.left⟩⟩
  instance : HasProducts Prop Prop := ⟨And⟩

  instance : GeneralizedRelation.HasSymm Prod := ⟨λ p => ⟨p.snd, p.fst⟩⟩
  instance : HasProducts (Type u) (Type u) := ⟨Prod⟩

end HasProducts

namespace HasEquivalences

  def univ   (α : Sort u)                : HasEquivalences α        Prop     := ⟨UnivRel α⟩
  instance iff                           : HasEquivalences Prop     Prop     := ⟨Iff⟩
  def eq     (α : Sort u)                : HasEquivalences α        Prop     := ⟨Eq⟩
  def setoid (α : Sort u) [s : Setoid α] : HasEquivalences α        Prop     := ⟨s.r⟩
  instance equiv                         : HasEquivalences (Type u) (Type u) := ⟨EquivRel⟩

end HasEquivalences



namespace HasInstanceEquivalences

  -- By specializing here, we avoid invoking proof irrelevance explicitly.
  -- Instead, we just declare all proofs to be equivalent according to our own notion of equivalence.
  instance prop : HasInstanceEquivalences' Prop :=
  { EquivType       := Prop,
    equivIsKind     := AnySort.isKind,
    hasEquivalences := HasEquivalences.univ,
    equivCongr      := λ _ _ => trivial }

  instance typeWithEq : HasInstanceEquivalences' (Type u) :=
  { EquivType       := Prop,
    equivIsKind     := AnySort.isKind,
    hasEquivalences := HasEquivalences.eq,
    equivCongr      := congr }

end HasInstanceEquivalences



namespace PropRel

  variable {α : Sort u} (r : α → α → Prop) [GeneralizedRelation.IsEquivalence r]

  instance hasComposition : HasComposition r :=
  { assocLR := λ _ _ _ => trivial,
    assocRL := λ _ _ _ => trivial }

  instance hasMorphisms : HasMorphisms r :=
  { leftId  := λ _ => trivial,
    rightId := λ _ => trivial }

  instance hasIsomorphisms : HasIsomorphisms r :=
  { leftInv  := λ _   => trivial,
    rightInv := λ _   => trivial,
    invInv   := λ _   => trivial,
    compInv  := λ _ _ => trivial,
    idInv    := λ _   => trivial }

  variable (s : α → α → Prop) [GeneralizedRelation.IsEquivalence s] (F : BaseFunctor r s)

  instance isReflFunctor  : IsReflFunctor  r s F := ⟨λ _   => trivial⟩
  instance isSymmFunctor  : IsSymmFunctor  r s F := ⟨λ _   => trivial⟩
  instance isTransFunctor : IsTransFunctor r s F := ⟨λ _ _ => trivial⟩

end PropRel

namespace EquivRel

  instance hasComposition : HasComposition EquivRel :=
  { assocLR := λ f g h => Eq.symm (Equiv.trans_assoc f g h),
    assocRL := Equiv.trans_assoc }

  instance hasMorphisms : HasMorphisms EquivRel :=
  { leftId  := Equiv.trans_refl,
    rightId := Equiv.refl_trans }

  instance hasIsomorphisms : HasIsomorphisms EquivRel :=
  { leftInv  := Equiv.trans_symm,
    rightInv := Equiv.symm_trans,
    invInv   := Equiv.symm_symm,
    compInv  := Equiv.symm_trans_symm,
    idInv    := @Equiv.refl_symm }

end EquivRel



def TypeClass := Sort u → Sort v

structure Bundled (C : TypeClass.{u, v}) where
(α    : Sort u)
(inst : C α)

namespace Bundled

  instance hasInstances (C : TypeClass) : HasInstances (Bundled C) := ⟨Bundled.α⟩

  class HasFunctoriality (C D : TypeClass) where
  (IsFunctorial {S : Bundled.{u, v} C} {T : Bundled.{u', v'} D} : (S → T) → Sort w)

  instance hasIsFun (C D : TypeClass) [h : HasFunctoriality C D] : HasIsFun (Bundled.{u, v} C) (Bundled.{u', v'} D) := ⟨h.IsFunctorial⟩

  class HasFunctorInstances (C : TypeClass) [hf : HasFunctoriality.{max 1 u w, v, max 1 u w, v, w} C C] where
  (funInst (S T : Bundled.{max 1 u w, v} C) : C (S ⟶' T))

  instance hasFun (C : TypeClass) [hf : HasFunctoriality.{max 1 u w, v, max 1 u w, v, w} C C] [h : HasFunctorInstances.{u, v, w} C] :
    HasFun (Bundled.{max 1 u w, v} C) :=
  { Fun      := λ S T => ⟨S ⟶' T, h.funInst S T⟩,
    funEquiv := λ S T => Equiv.refl (S ⟶' T) }

end Bundled



@[reducible] def BundledSetoid : Type (u + 1) := Bundled.{u + 1, u + 1} Setoid

namespace BundledSetoid

  instance isSetoid (S : BundledSetoid) : Setoid (HasInstances.Inst S) := S.inst

  class IsFunctorial {S T : BundledSetoid} (f : S → T) where
  (mapEquiv {a b : S} : a ≈ b → f a ≈ f b)

  instance hasFunctoriality : Bundled.HasFunctoriality.{u + 1, u + 1, u' + 1, u' + 1, 1} Setoid Setoid := ⟨IsFunctorial⟩

  namespace BundledFunctor

    def Equiv {S T : BundledSetoid} (F G : S ⟶' T) := ∀ a, F a ≈ G a

    namespace Equiv

      variable {S T : BundledSetoid}

      theorem refl  (F     : S ⟶' T)                                 : Equiv F F := λ a => Setoid.refl  (F a)
      theorem symm  {F G   : S ⟶' T} (h : Equiv F G)                 : Equiv G F := λ a => Setoid.symm  (h a)
      theorem trans {F G H : S ⟶' T} (h : Equiv F G) (i : Equiv G H) : Equiv F H := λ a => Setoid.trans (h a) (i a)

      def isEquivalence : Equivalence (@Equiv S T) := ⟨refl, symm, trans⟩

    end Equiv

    instance isSetoid (S T : BundledSetoid) : Setoid (S ⟶' T) := ⟨Equiv, Equiv.isEquivalence⟩
    instance hasFunctorInstances : Bundled.HasFunctorInstances.{u + 1, u + 1, 1} Setoid := ⟨isSetoid⟩

  end BundledFunctor

  instance hasFun : HasFun BundledSetoid := Bundled.hasFun Setoid

  instance hasFunOp : HasFunOp BundledSetoid :=
  { idIsFun         := λ S           => ⟨λ ha         => ha⟩,
    constIsFun      := λ S {T} c     => ⟨λ ha         => Setoid.refl c⟩,
    constFunIsFun   := λ S T         => ⟨λ hc a       => hc⟩,
    appIsFun        := λ {S} a T     => ⟨λ hF         => hF a⟩,
    appFunIsFun     := λ S T         => ⟨λ ha F       => F.isFun.mapEquiv ha⟩,
    dupIsFun        := λ {S T} F     => ⟨λ {a₁ a₂} ha => Setoid.trans (F.isFun.mapEquiv ha a₁) ((F a₂).isFun.mapEquiv ha)⟩,
    dupFunIsFun     := λ S T         => ⟨λ hF a       => hF a a⟩,
    compIsFun       := λ {S T U} F G => ⟨λ ha         => G.isFun.mapEquiv (F.isFun.mapEquiv ha)⟩,
    compFunIsFun    := λ {S T} F U   => ⟨λ hG a       => hG (F a)⟩,
    compFunFunIsFun := λ S T U       => ⟨λ hF G a     => G.isFun.mapEquiv (hF a)⟩ }

  instance isKind : IsKind BundledSetoid := ⟨⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences' BundledSetoid :=
  { EquivType       := Prop,
    equivIsKind     := AnySort.isKind,
    hasEquivalences := λ S => HasEquivalences.setoid (HasInstances.Inst S),
    equivCongr      := λ {S T F G a b} h₁ h₂ => Setoid.trans (h₁ a) (G.isFun.mapEquiv h₂) }

  def eq (α : Sort u) : Bundled Setoid :=
  { α    := α,
    inst := ⟨Eq, Eq.isEquivalence⟩ }

end BundledSetoid



-- TODO: Where exactly does this fit into the axioms?
-- It is an equivalence between instances of IsKind, with a dependent equivalence given by `e a = b`...

class IsFunctorialTypeClass (C : TypeClass) where
(mapEquiv      {α β   : Sort u}                         : α ≃ β → C α ≃ C β)
(respectsRefl  (α     : Sort u)                         : mapEquiv (Equiv.refl  α)   = Equiv.refl  (C α))
(respectsSymm  {α β   : Sort u} (e : α ≃ β)             : mapEquiv (Equiv.symm  e)   = Equiv.symm  (mapEquiv e))
(respectsTrans {α β γ : Sort u} (e : α ≃ β) (f : β ≃ γ) : mapEquiv (Equiv.trans e f) = Equiv.trans (mapEquiv e) (mapEquiv f))

structure TypeFunctor where
(C     : TypeClass)
[isFun : IsFunctorialTypeClass C]

namespace TypeFunctor

  -- TODO: This duplicates generic proofs.

  instance (F : TypeFunctor) : IsFunctorialTypeClass F.C := F.isFun

  instance : IsFunctorialTypeClass id :=
  { mapEquiv      := id,
    respectsRefl  := λ _   => rfl,
    respectsSymm  := λ _   => rfl,
    respectsTrans := λ _ _ => rfl }

  def funId : TypeFunctor := ⟨id⟩

  instance (C D : TypeClass) [hC : IsFunctorialTypeClass C] [hD : IsFunctorialTypeClass D] :
    IsFunctorialTypeClass (D ∘ C) :=
  { mapEquiv      := hD.mapEquiv ∘ hC.mapEquiv,
    respectsRefl  := λ α   => Eq.trans (congrArg hD.mapEquiv (hC.respectsRefl  α))
                                       (hD.respectsRefl (C α)),
    respectsSymm  := λ e   => Eq.trans (congrArg hD.mapEquiv (hC.respectsSymm  e))
                                       (hD.respectsSymm (hC.mapEquiv e)),
    respectsTrans := λ e f => Eq.trans (congrArg hD.mapEquiv (hC.respectsTrans e f))
                                       (hD.respectsTrans (hC.mapEquiv e) (hC.mapEquiv f)) }

  def funComp (F G : TypeFunctor) : TypeFunctor := ⟨G.C ∘ F.C⟩

end TypeFunctor
