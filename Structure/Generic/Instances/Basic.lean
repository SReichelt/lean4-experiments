import Structure.Generic.Axioms

import mathlib4_experiments.CoreExt

open GeneralizedRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



def sortUniverse : Universe.{u} := ⟨Sort u⟩
@[reducible] def propUniverse := sortUniverse.{0}
@[reducible] def typeUniverse := sortUniverse.{u + 1}

namespace SortUniverse

  instance hasExternalFunctors : HasExternalFunctors sortUniverse.{u} sortUniverse.{v} := ⟨λ _ => PUnit⟩

  def funEquiv (α β : sortUniverse.{u}) : (α → β) ≃ (α ⟶' β) :=
  { toFun    := λ f      => ⟨f, PUnit.unit⟩,
    invFun   := λ F      => F.f,
    leftInv  := λ _      => rfl,
    rightInv := λ ⟨_, _⟩ => by simp }

  instance hasInternalFunctors : HasInternalFunctors sortUniverse.{u} :=
  { Fun      := λ α β => α → β,
    funEquiv := funEquiv }

  instance hasIdFun    : HasIdFun    sortUniverse.{u}                                   := ⟨λ _     => PUnit.unit⟩
  instance hasConstFun : HasConstFun sortUniverse.{u} sortUniverse.{v}                  := ⟨λ _ _ _ => PUnit.unit⟩
  instance hasCompFun  : HasCompFun  sortUniverse.{u} sortUniverse.{v} sortUniverse.{w} := ⟨λ _ _   => PUnit.unit⟩

  instance hasFunOp : HasFunOp sortUniverse.{u} :=
  { constFunIsFun   := λ _ _   => PUnit.unit,
    appIsFun        := λ _ _   => PUnit.unit,
    appFunIsFun     := λ _ _   => PUnit.unit,
    dupIsFun        := λ _     => PUnit.unit,
    dupFunIsFun     := λ _ _   => PUnit.unit,
    compFunIsFun    := λ _ _   => PUnit.unit,
    compFunFunIsFun := λ _ _ _ => PUnit.unit }

end SortUniverse



def UnivRel (α : Sort u) : GeneralizedRelation α propUniverse := λ _ _ => True

def UnivRel.isEquivalence {α : Sort u} : Equivalence (UnivRel α) :=
⟨λ _ => trivial, λ _ => trivial, λ _ _ => trivial⟩

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

end GeneralizedRelation.IsEquivalence



-- TODO: Convert products, `Iff`, and `Equiv` to general axioms and an instance similar to `Fun` -> `Arrow`.

namespace HasProducts

  instance : HasSymm (V := propUniverse) And := ⟨λ h => ⟨h.right, h.left⟩⟩
  instance : HasProducts Prop propUniverse := ⟨And⟩

  instance : HasSymm (V := typeUniverse.{u}) Prod := ⟨λ p => ⟨p.snd, p.fst⟩⟩
  instance : HasProducts (Type u) typeUniverse.{u} := ⟨Prod⟩

end HasProducts

namespace HasEquivalences

  def univ   (α : Sort u)                : HasEquivalences α    propUniverse := ⟨UnivRel α⟩
  instance iff                           : HasEquivalences Prop propUniverse := ⟨Iff⟩
  def eq     (α : Sort u)                : HasEquivalences α    propUniverse := ⟨Eq⟩
  def setoid (α : Sort u) [s : Setoid α] : HasEquivalences α    propUniverse := ⟨s.r⟩

end HasEquivalences



namespace HasInstanceEquivalences

  -- By specializing here, we avoid invoking proof irrelevance explicitly.
  -- Instead, we just declare all proofs to be equivalent according to our own notion of equivalence.
  instance prop : HasInstanceEquivalences propUniverse     := ⟨propUniverse, UnivRel⟩
  instance type : HasInstanceEquivalences typeUniverse.{u} := ⟨propUniverse, @Eq⟩

  instance : HasInstanceArrows propUniverse     := HasInstanceEquivalences.toHasInstanceArrows propUniverse
  instance : HasInstanceArrows typeUniverse.{u} := HasInstanceEquivalences.toHasInstanceArrows typeUniverse.{u}

end HasInstanceEquivalences

namespace HasFunctorialEquivalences

  instance prop : HasFunctorialEquivalences propUniverse :=
  { equivCongr    := λ _ _ => trivial }

  instance type : HasFunctorialEquivalences typeUniverse.{u} :=
  { equivCongr    := congr }

end HasFunctorialEquivalences



namespace PropRel

  section Morphisms

    variable {α : Sort u} (R : GeneralizedRelation α propUniverse) [IsEquivalence R]

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

  end Morphisms

  section Functors

    variable {α : Sort u} {V : Universe} [HasInternalFunctors V] [HasExternalFunctors V propUniverse]
             (R : GeneralizedRelation α V) (S : GeneralizedRelation α propUniverse)
             [IsEquivalence R] [IsEquivalence S]
             (F : BaseFunctor R S)

    instance isReflFunctor  : IsReflFunctor  R S F := ⟨λ _   => trivial⟩
    instance isSymmFunctor  : IsSymmFunctor  R S F := ⟨λ _   => trivial⟩
    instance isTransFunctor : IsTransFunctor R S F := ⟨λ _ _ => trivial⟩

    instance isPreorderFunctor    : IsPreorderFunctor    R S F := ⟨⟩
    instance isEquivalenceFunctor : IsEquivalenceFunctor R S F := ⟨⟩

  end Functors

  section NaturalTransformations

    variable {α : Sort u} {β : Sort v} {V : Universe} [HasInternalFunctors V] [HasExternalFunctors V propUniverse]
             (R : GeneralizedRelation α V) (S : GeneralizedRelation β propUniverse) [HasTrans S]
             {mF mG : α → β} (F : MappedBaseFunctor R S mF) (G : MappedBaseFunctor R S mG)

    instance isNatural (n : ∀ a, S (mF a) (mG a)) : IsNatural R S F G n := ⟨λ _ => trivial⟩

    def natEquiv : (∀ a, S (mF a) (mG a)) ≃ NaturalQuantification R S F G :=
    { toFun    := λ n => ⟨n⟩,
      invFun   := λ N => N.n,
      leftInv  := λ _ => rfl,
      rightInv := λ { n := _, isNatural := ⟨_⟩ } => rfl }

    instance hasIntNat : HasInternalNaturalQuantification R S F G :=
    { Nat      := ∀ a, S (mF a) (mG a),
      natEquiv := natEquiv R S F G }

  end NaturalTransformations

  instance hasNat {U₁ U₂ V : Universe} [HasExternalFunctors U₁ U₂] [HasExternalFunctors V propUniverse] :
    HasNaturalQuantification U₁ U₂ V propUniverse :=
  { hasNat := λ {α β} R S {h mF mG} F G => hasIntNat R S F G }

end PropRel
