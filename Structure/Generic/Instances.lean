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
set_option pp.universes true

universes u uu v vv w



namespace SortUniverse

  instance hasExternalFunctors : HasExternalFunctors sortUniverse.{u} sortUniverse.{v} := ⟨λ _ => True⟩

  instance hasInternalFunctors : HasInternalFunctors sortUniverse.{u} :=
  { Fun      := λ α β => α → β,
    funEquiv := λ α β => { toFun    := λ f      => ⟨f, trivial⟩,
                           invFun   := λ F      => F.f,
                           leftInv  := λ f      => rfl,
                           rightInv := λ ⟨f, _⟩ => rfl } }

  instance hasIdFun    : HasIdFun    sortUniverse.{u}                                   := ⟨λ _     => trivial⟩
  instance hasConstFun : HasConstFun sortUniverse.{u} sortUniverse.{v}                  := ⟨λ _ _ _ => trivial⟩
  instance hasCompFun  : HasCompFun  sortUniverse.{u} sortUniverse.{v} sortUniverse.{w} := ⟨λ _ _   => trivial⟩

  instance hasFunOp : HasFunOp sortUniverse.{u} :=
  { constFunIsFun   := λ _ _   => trivial,
    appIsFun        := λ _ _   => trivial,
    appFunIsFun     := λ _ _   => trivial,
    dupIsFun        := λ _     => trivial,
    dupFunIsFun     := λ _ _   => trivial,
    compFunIsFun    := λ _ _   => trivial,
    compFunFunIsFun := λ _ _ _ => trivial }

end SortUniverse



def UnivRel (α : Sort u) : GeneralizedRelation α propUniverse := λ _ _ => True

def UnivRel.isEquivalence {α : Sort u} : Equivalence (UnivRel α) :=
⟨λ _ => trivial, λ _ => trivial, λ _ _ => trivial⟩

def EquivRel : GeneralizedRelation (Type u) typeUniverse.{u} := Equiv

namespace GeneralizedRelation.IsEquivalence

  -- Every equivalence relation can trivially be converted to an instance of `IsEquivalence`.
  instance relEquiv {α : Sort u} {R : GeneralizedRelation α propUniverse} (e : Equivalence R) : IsEquivalence R :=
  { refl  := e.refl,
    symm  := e.symm,
    trans := e.trans }

  -- So these are the instances that we obtain directly from Lean.
  instance univ   (α : Sort u)                : IsEquivalence (V := propUniverse) (UnivRel α) := relEquiv UnivRel.isEquivalence
  instance iff                                : IsEquivalence (V := propUniverse) Iff         := relEquiv Iff.isEquivalence
  instance eq     (α : Sort u)                : IsEquivalence (V := propUniverse) (@Eq α)     := relEquiv Eq.isEquivalence
  instance setoid (α : Sort u) [s : Setoid α] : IsEquivalence (V := propUniverse) s.r         := relEquiv s.iseqv

  instance equiv : IsEquivalence EquivRel :=
  { refl  := Equiv.refl,
    symm  := Equiv.symm,
    trans := Equiv.trans }

end GeneralizedRelation.IsEquivalence



-- TODO: Convert products, `Iff`, and `Equiv` to general axioms and an instance similar to `Fun` -> `Arrow`.

namespace HasProducts

  instance : GeneralizedRelation.HasSymm (V := propUniverse) And := ⟨λ h => ⟨h.right, h.left⟩⟩
  instance : HasProducts Prop propUniverse := ⟨And⟩

  instance : GeneralizedRelation.HasSymm (V := typeUniverse.{u}) Prod := ⟨λ p => ⟨p.snd, p.fst⟩⟩
  instance : HasProducts (Type u) typeUniverse.{u} := ⟨Prod⟩

end HasProducts

namespace HasEquivalences

  def univ   (α : Sort u)                : HasEquivalences α        propUniverse     := ⟨UnivRel α⟩
  instance iff                           : HasEquivalences Prop     propUniverse     := ⟨Iff⟩
  def eq     (α : Sort u)                : HasEquivalences α        propUniverse     := ⟨Eq⟩
  def setoid (α : Sort u) [s : Setoid α] : HasEquivalences α        propUniverse     := ⟨s.r⟩
  instance equiv                         : HasEquivalences (Type u) typeUniverse.{u} := ⟨EquivRel⟩

end HasEquivalences



namespace HasInstanceEquivalences

  -- By specializing here, we avoid invoking proof irrelevance explicitly.
  -- Instead, we just declare all proofs to be equivalent according to our own notion of equivalence.
  instance prop       : HasInstanceEquivalences propUniverse     := ⟨propUniverse, UnivRel⟩
  instance typeWithEq : HasInstanceEquivalences typeUniverse.{u} := ⟨propUniverse, @Eq⟩

  instance : HasInstanceArrows propUniverse     := HasInstanceEquivalences.toHasInstanceArrows propUniverse
  instance : HasInstanceArrows typeUniverse.{u} := HasInstanceEquivalences.toHasInstanceArrows typeUniverse.{u}

end HasInstanceEquivalences

namespace HasFunctorialEquivalences
  
  instance prop       : HasFunctorialEquivalences propUniverse :=
  { equivCongr := λ _ _ => trivial }

  instance typeWithEq : HasFunctorialEquivalences typeUniverse.{u} :=
  { equivCongr := congr }

end HasFunctorialEquivalences



namespace PropRel

  variable {α : Sort u} (R : GeneralizedRelation α propUniverse) [GeneralizedRelation.IsEquivalence R]

  instance isCompositionRelation : IsCompositionRelation R :=
  { assocLR := λ _ _ _ => trivial,
    assocRL := λ _ _ _ => trivial }

  instance isMorphismRelation : IsMorphismRelation R :=
  { leftId  := λ _ => trivial,
    rightId := λ _ => trivial }

  instance isIsomorphismRelation : IsIsomorphismRelation R :=
  { leftInv  := λ _   => trivial,
    rightInv := λ _   => trivial,
    invInv   := λ _   => trivial,
    compInv  := λ _ _ => trivial,
    idInv    := λ _   => trivial }

  variable (S : GeneralizedRelation α propUniverse) [GeneralizedRelation.IsEquivalence S] (F : BaseFunctor R S)

  instance isReflFunctor  : IsReflFunctor  R S F := ⟨λ _   => trivial⟩
  instance isSymmFunctor  : IsSymmFunctor  R S F := ⟨λ _   => trivial⟩
  instance isTransFunctor : IsTransFunctor R S F := ⟨λ _ _ => trivial⟩

end PropRel

namespace EquivRel

  instance isCompositionRelation : IsCompositionRelation EquivRel :=
  { assocLR := λ f g h => Eq.symm (Equiv.trans_assoc f g h),
    assocRL := Equiv.trans_assoc }

  instance isMorphismRelation : IsMorphismRelation EquivRel :=
  { leftId  := Equiv.trans_refl,
    rightId := Equiv.refl_trans }

  instance isIsomorphismRelation : IsIsomorphismRelation EquivRel :=
  { leftInv  := Equiv.trans_symm,
    rightInv := Equiv.symm_trans,
    invInv   := Equiv.symm_symm,
    compInv  := Equiv.symm_trans_symm,
    idInv    := @Equiv.refl_symm }

end EquivRel



namespace Bundled

  class HasFunctoriality (C : TypeClass.{u, u + 1, uu} (Sort u)) (D : TypeClass.{v, v + 1, vv} (Sort v)) where
  (IsFunctorial {S : Bundled C} {T : Bundled D} : (S → T) → Sort w)

  def bundledUniverse (C : TypeClass.{u, u + 1, uu} (Sort u)) : Universe.{u, max (u + 1) uu} := ⟨Bundled C⟩

  instance hasExternalFunctors (C : TypeClass.{u, u + 1, uu} (Sort u)) (D : TypeClass.{v, v + 1, vv} (Sort v))
                               [h : HasFunctoriality C D] :
    HasExternalFunctors (bundledUniverse.{u, uu} C) (bundledUniverse.{v, vv} D) :=
  ⟨h.IsFunctorial⟩

  class HasFunctorInstances (C : TypeClass (Sort (max 1 u v)))
                            [hf : HasFunctoriality.{max 1 u v, uu, max 1 u v, uu, v} C C] where
  (funInst (S T : bundledUniverse.{max 1 u v, uu} C) : C (S ⟶' T))

  instance hasInternalFunctors (C : TypeClass (Sort (max 1 u v)))
                               [hf : HasFunctoriality.{max 1 u v, uu, max 1 u v, uu, v} C C]
                               [h : HasFunctorInstances.{u, uu, v} C] :
    HasInternalFunctors (bundledUniverse.{max 1 u v, uu} C) :=
  { Fun      := λ S T => { α    := S ⟶' T,
                           inst := h.funInst S T },
    funEquiv := λ S T => Equiv.refl (S ⟶' T) }

end Bundled



@[reducible] def bundledSetoid : Universe.{u + 1} := Bundled.bundledUniverse.{u + 1, u + 1} Setoid

namespace BundledSetoid

  instance isSetoid (S : bundledSetoid) : Setoid ⌈S⌉ := S.inst
  instance (S : bundledSetoid) : Setoid ⌈S⌉ := isSetoid S

  class IsFunctorial {S T : bundledSetoid} (f : S → T) where
  (mapEquiv {a b : S} : a ≈ b → f a ≈ f b)

  instance hasFunctoriality : Bundled.HasFunctoriality.{u + 1, u + 1, v + 1, v + 1, 1} Setoid Setoid := ⟨IsFunctorial⟩

  namespace BundledFunctor

    def Equiv {S T : bundledSetoid} (F G : S ⟶' T) := ∀ a, F a ≈ G a

    namespace Equiv

      variable {S T : bundledSetoid}

      theorem refl  (F     : S ⟶' T)                                 : Equiv F F := λ a => Setoid.refl  (F a)
      theorem symm  {F G   : S ⟶' T} (h : Equiv F G)                 : Equiv G F := λ a => Setoid.symm  (h a)
      theorem trans {F G H : S ⟶' T} (h : Equiv F G) (i : Equiv G H) : Equiv F H := λ a => Setoid.trans (h a) (i a)

      def isEquivalence : Equivalence (@Equiv S T) := ⟨refl, symm, trans⟩

    end Equiv

    instance isSetoid (S T : bundledSetoid) : Setoid (S ⟶' T) := ⟨Equiv, Equiv.isEquivalence⟩
    instance hasFunctorInstances : Bundled.HasFunctorInstances.{u + 1, u + 1, 1} Setoid := ⟨isSetoid⟩

  end BundledFunctor

  instance hasInternalFunctors : HasInternalFunctors bundledSetoid := Bundled.hasInternalFunctors Setoid

  instance hasIdFun    : HasIdFun    bundledSetoid.{u}                                     :=
  ⟨λ S           => ⟨id⟩⟩
  instance hasConstFun : HasConstFun bundledSetoid.{u} bundledSetoid.{v}                   :=
  ⟨λ S {T}   c   => ⟨Function.const _ (Setoid.refl c)⟩⟩
  instance hasCompFun  : HasCompFun  bundledSetoid.{u} bundledSetoid.{v} bundledSetoid.{w} :=
  ⟨λ {S T U} F G => ⟨G.isFun.mapEquiv ∘ F.isFun.mapEquiv⟩⟩

  instance hasFunOp : HasFunOp bundledSetoid :=
  { constFunIsFun   := λ S T         => ⟨λ hc a       => hc⟩,
    appIsFun        := λ {S} a T     => ⟨λ hF         => hF a⟩,
    appFunIsFun     := λ S T         => ⟨λ ha F       => F.isFun.mapEquiv ha⟩,
    dupIsFun        := λ {S T} F     => ⟨λ {a₁ a₂} ha => Setoid.trans (F.isFun.mapEquiv ha a₁) ((F a₂).isFun.mapEquiv ha)⟩,
    dupFunIsFun     := λ S T         => ⟨λ hF a       => hF a a⟩,
    compFunIsFun    := λ {S T} F U   => ⟨λ hG a       => hG (F a)⟩,
    compFunFunIsFun := λ S T U       => ⟨λ hF G a     => G.isFun.mapEquiv (hF a)⟩ }

  instance hasInstanceEquivalences : HasInstanceEquivalences bundledSetoid :=
  ⟨propUniverse, λ S => (isSetoid S).r⟩

  instance hasFunctorialEquivalences : HasFunctorialEquivalences bundledSetoid :=
  { equivCongr := λ {S T F G a b} h₁ h₂ => Setoid.trans (h₁ a) (G.isFun.mapEquiv h₂) }

  def eq (α : Type u) : bundledSetoid :=
  { α    := α,
    inst := ⟨Eq, Eq.isEquivalence⟩ }

end BundledSetoid
