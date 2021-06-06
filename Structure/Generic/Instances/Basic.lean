import Structure.Generic.Axioms

import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Equiv.Basic

open GeneralizedRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



instance unitHasInstances : HasInstances Unit := ⟨λ _ => True⟩

def unit : Universe.{0} := ⟨Unit⟩

namespace unit

  instance hasExternalFunctors (U : Universe.{u}) : HasExternalFunctors U unit := ⟨λ _ => PUnit.{u}⟩

  @[reducible] def unitFunctor {U : Universe.{u}} (α : U) (β : unit) : α ⟶' β :=
  ⟨Function.const ⌈α⌉ trivial, ⟨⟩⟩

  @[simp] theorem unitFunctorIsUnique {U : Universe.{u}} {α : U} {β : unit} (F : α ⟶' β) :
    F = unitFunctor α β := match F with
  | ⟨_, _⟩ => by simp

  def funEquiv (α β : unit) : True ≃ (α ⟶' β) :=
  { toFun    := λ _ => unitFunctor α β,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => by simp,
    rightInv := λ _ => by simp }

  instance hasInternalFunctors : HasInternalFunctors unit :=
  { Fun      := λ _ _ => ⟨⟩,
    funEquiv := funEquiv }

  instance hasIdFun : HasIdFun unit := ⟨λ _ => ⟨⟩⟩
  instance hasConstFun (U : Universe.{u}) : HasConstFun U unit := ⟨λ _ _ _ => ⟨⟩⟩
  instance hasCompFun (U : Universe.{u}) (V : Universe.{v}) [HasExternalFunctors U V] : HasCompFun U V unit :=
  ⟨λ _ _ => ⟨⟩⟩

  instance hasLinearFunOp : HasLinearFunOp unit :=
  { appIsFun        := λ _ _   => ⟨⟩,
    appFunIsFun     := λ _ _   => ⟨⟩,
    compFunIsFun    := λ _ _   => ⟨⟩,
    compFunFunIsFun := λ _ _ _ => ⟨⟩ }

  instance hasAffineFunOp : HasAffineFunOp unit :=
  { constFunIsFun := λ _ _ => ⟨⟩ }

  instance hasFullFunOp : HasFullFunOp unit :=
  { dupIsFun    := λ _   => ⟨⟩,
    dupFunIsFun := λ _ _ => ⟨⟩ }

  instance hasFunOp : HasFunOp unit := ⟨⟩

  instance hasExternalEquivalences : HasExternalEquivalences unit unit := ⟨λ _ _ => True⟩

  @[reducible] def unitEquivalence (α : unit) (β : unit) : α ⟷' β :=
  ⟨unitFunctor α β, unitFunctor β α, trivial⟩

  @[simp] theorem unitEquivalenceIsUnique {α : unit} {β : unit} (E : α ⟷' β) :
    E = unitEquivalence α β := match E with
  | ⟨_, _, _⟩ => by simp; exact HEq.rfl

  def equivEquiv (α β : unit) : True ≃ (α ⟷' β) :=
  { toFun    := λ _ => unitEquivalence α β,
    invFun   := λ _ => trivial,
    leftInv  := λ _ => by simp,
    rightInv := λ _ => by simp }

  instance hasInternalEquivalences : HasInternalEquivalences unit :=
  { Equiv                := λ _ _ => ⟨⟩,
    equivEquiv           := equivEquiv,
    equivElimToFunIsFun  := λ _ _ => ⟨⟩,
    equivElimInvFunIsFun := λ _ _ => ⟨⟩ }

  instance hasIdEquiv   : HasIdEquiv   unit           := ⟨λ _   => trivial⟩
  instance hasCompEquiv : HasCompEquiv unit unit unit := ⟨λ _ _ => trivial⟩
  instance hasInvEquiv  : HasInvEquiv  unit unit      := ⟨λ _   => trivial⟩

  instance hasEquivOp : HasEquivOp unit :=
  { compEquivIsFun    := λ _ _   => ⟨⟩,
    compEquivFunIsFun := λ _ _ _ => ⟨⟩,
    invEquivIsFun     := λ _ _   => ⟨⟩,
    invEquivIsEquiv   := λ _ _   => trivial }

  @[reducible] def unitProduct (α : unit) (β : unit) : α ⊓' β :=
  ⟨⟨⟩, ⟨⟩⟩

  @[simp] theorem unitProductIsUnique {α : unit} {β : unit} (P : α ⊓' β) :
    P = unitProduct α β := match P with
  | ⟨_, _⟩ => rfl

  def prodEquiv (α β : unit) : True ≃ (α ⊓' β) :=
  { toFun    := λ _ => unitProduct α β,
    invFun   := λ _ => ⟨⟩,
    leftInv  := λ _ => by simp,
    rightInv := λ _ => by simp }

  instance hasInternalProducts : HasInternalProducts unit :=
  { Prod             := λ _ _ => ⟨⟩,
    prodEquiv        := prodEquiv,
    prodIntroIsFun   := λ _ _ => ⟨⟩,
    prodElimFstIsFun := λ _ _ => ⟨⟩,
    prodElimSndIsFun := λ _ _ => ⟨⟩ }

  instance hasUnitType : HasUnitType unit :=
  { Unit           := ⟨⟩,
    unit           := trivial,
    unitIntroIsFun := λ _ => ⟨⟩ }

  def Rel (α : Sort u) : GeneralizedRelation α unit := λ _ _ => ⟨⟩

  instance Rel.isEquivalence (α : Sort u) : IsEquivalence (Rel α) :=
  { refl  := λ _ => trivial,
    trans := trivial,
    symm  := trivial }

  class HasUnitEquivalences (U : Universe.{u}) where
  (Equiv (α : U)              : GeneralizedRelation ⌈α⌉ unit)
  [equivIsEquivalence (α : U) : IsEquivalence (Equiv α)]

  instance hasUnitInstanceEquivalences (U : Universe.{u}) [HasUnitEquivalences U] :
    HasInstanceEquivalences U :=
  ⟨unit, λ α => unit.Rel ⌈α⌉⟩

  instance hasUnitEquivalence : HasUnitEquivalences unit := ⟨λ _ => unit.Rel True⟩

  instance hasEquivCongr : HasEquivCongr unit :=
  { equivCongrArg := λ _ => unitFunctor (U := unit) ⟨⟩ ⟨⟩,
    equivCongrFun := λ _ => unitFunctor (U := unit) ⟨⟩ ⟨⟩ }

  instance hasNaturalEquivalences : HasNaturalEquivalences unit :=
  { equivHasInstEquivs := hasUnitInstanceEquivalences unit,
    isNat              := λ _ _ _ _ => trivial }

  section Morphisms

    variable {α : Sort u} {V : Universe.{v}} [HasInternalFunctors V] [HasUnitEquivalences V] (R : GeneralizedRelation α V)

    variable [HasLinearFunOp V] [HasTrans R]

    instance isCompositionRelation : IsCompositionRelation R :=
    { assoc := trivial }

    variable [HasRefl R]

    instance isMorphismRelation [IsPreorder R] : IsMorphismRelation R :=
    { leftId  := trivial,
      rightId := trivial }

    variable [HasSubLinearFunOp V] [HasNonLinearFunOp V] [HasInternalEquivalences V] [HasSymm R]

    instance isIsomorphismRelation [IsEquivalence R] : IsIsomorphismRelation R :=
    { leftInv  := trivial,
      rightInv := trivial }

  end Morphisms

  section Functors

    variable {α : Sort u} {V : Universe.{v}} {W : Universe.{w}}
             [HasInternalFunctors V] [HasInternalEquivalences V] [HasInternalFunctors W] [HasInternalEquivalences W]
             [HasUnitEquivalences W] [HasExternalFunctors V W]
             (R : GeneralizedRelation α V) (S : GeneralizedRelation α W)
             [IsEquivalence R] [IsEquivalence S]
             (F : BaseFunctor R S)

    instance isReflFunctor  : IsReflFunctor  R S F := ⟨λ _   => trivial⟩
    instance isSymmFunctor  : IsSymmFunctor  R S F := ⟨λ _   => trivial⟩
    instance isTransFunctor : IsTransFunctor R S F := ⟨λ _ _ => trivial⟩

    instance isPreorderFunctor    : IsPreorderFunctor    R S F := ⟨⟩
    instance isEquivalenceFunctor : IsEquivalenceFunctor R S F := ⟨⟩

  end Functors

end unit



def sort : Universe.{u} := ⟨Sort u⟩
@[reducible] def prop := sort.{0}
@[reducible] def type := sort.{1}

namespace sort

  instance hasExternalFunctors (U : Universe.{u}) : HasExternalFunctors U sort.{v} := ⟨λ _ => PUnit.{max u v}⟩

  @[reducible] def toBundledFunctor {U : Universe.{u}} {α : U} {β : sort.{v}} (f : α → β) : α ⟶' β := ⟨f, ⟨⟩⟩

  theorem toFromBundledFunctor {U : Universe.{u}} {α : U} {β : sort.{v}} (F : α ⟶' β) :
    toBundledFunctor F.f = F := match F with
  | ⟨_, _⟩ => by simp

  def funEquiv (α β : sort.{u}) : (α → β) ≃ (α ⟶' β) :=
  { toFun    := λ f => toBundledFunctor f,
    invFun   := λ F => F.f,
    leftInv  := λ f => rfl,
    rightInv := λ F => toFromBundledFunctor F }

  instance hasInternalFunctors : HasInternalFunctors sort.{u} :=
  { Fun      := λ α β => α → β,
    funEquiv := funEquiv }

  instance hasIdFun : HasIdFun sort.{u} := ⟨λ _ => ⟨⟩⟩
  instance hasConstFun (U : Universe.{u}) : HasConstFun U sort.{v} := ⟨λ _ _ _ => ⟨⟩⟩
  instance hasCompFun (U : Universe.{u}) (V : Universe.{v}) [HasExternalFunctors U V] : HasCompFun U V sort.{w} :=
  ⟨λ _ _ => ⟨⟩⟩

  instance hasLinearFunOp : HasLinearFunOp sort.{u} :=
  { appIsFun        := λ _ _   => ⟨⟩,
    appFunIsFun     := λ _ _   => ⟨⟩,
    compFunIsFun    := λ _ _   => ⟨⟩,
    compFunFunIsFun := λ _ _ _ => ⟨⟩ }

  instance hasAffineFunOp : HasAffineFunOp sort.{u} :=
  { constFunIsFun := λ _ _ => ⟨⟩ }

  instance hasFullFunOp : HasFullFunOp sort.{u} :=
  { dupIsFun    := λ _   => ⟨⟩,
    dupFunIsFun := λ _ _ => ⟨⟩ }

  instance hasFunOp : HasFunOp sort.{u} := ⟨⟩

end sort

namespace prop

  instance hasExternalEquivalences : HasExternalEquivalences prop prop := ⟨λ _ _ => PUnit.{0}⟩

  @[reducible] def toBundledEquivalence {p q : prop} (h : p ↔ q) : p ⟷' q :=
  ⟨sort.toBundledFunctor h.mp, sort.toBundledFunctor h.mpr, ⟨⟩⟩

  @[reducible] def fromBundledEquivalence {p q : prop} (E : p ⟷' q) : p ↔ q :=
  ⟨E.toFun.f, E.invFun.f⟩

  theorem fromToBundledEquivalence {p q : prop} (h : p ↔ q) :
    fromBundledEquivalence (toBundledEquivalence h) = h :=
  rfl

  theorem toFromBundledEquivalence {p q : prop} (E : p ⟷' q) :
    toBundledEquivalence (fromBundledEquivalence E) = E := match E with
  | ⟨toFun, invFun, _⟩ => by simp; exact ⟨sort.toFromBundledFunctor toFun, sort.toFromBundledFunctor invFun, HEq.rfl⟩

  def equivEquiv (p q : prop) : (p ↔ q) ≃ (p ⟷' q) :=
  { toFun    := toBundledEquivalence,
    invFun   := fromBundledEquivalence,
    leftInv  := fromToBundledEquivalence,
    rightInv := toFromBundledEquivalence }

  instance hasInternalEquivalences : HasInternalEquivalences prop :=
  { Equiv                := Iff,
    equivEquiv           := equivEquiv,
    equivElimToFunIsFun  := λ _ _ => ⟨⟩,
    equivElimInvFunIsFun := λ _ _ => ⟨⟩ }

  instance hasIdEquiv   : HasIdEquiv   prop           := ⟨λ _   => ⟨⟩⟩
  instance hasCompEquiv : HasCompEquiv prop prop prop := ⟨λ _ _ => ⟨⟩⟩
  instance hasInvEquiv  : HasInvEquiv  prop prop      := ⟨λ _   => ⟨⟩⟩

  instance hasEquivOp : HasEquivOp prop :=
  { compEquivIsFun    := λ _ _   => ⟨⟩,
    compEquivFunIsFun := λ _ _ _ => ⟨⟩,
    invEquivIsFun     := λ _ _   => ⟨⟩,
    invEquivIsEquiv   := λ _ _   => ⟨⟩ }

  def prodEquiv (p q : prop) : (p ∧ q) ≃ (p ⊓' q) :=
  { toFun    := λ h => ⟨h.left, h.right⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ _ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasInternalProducts : HasInternalProducts prop :=
  { Prod             := And,
    prodEquiv        := prodEquiv,
    prodIntroIsFun   := λ _ _ => ⟨⟩,
    prodElimFstIsFun := λ _ _ => ⟨⟩,
    prodElimSndIsFun := λ _ _ => ⟨⟩ }

  instance hasEmptyType : HasEmptyType prop :=
  { Empty          := False,
    emptyIsEmpty   := id,
    emptyElimIsFun := λ _ => ⟨⟩ }

  instance hasClassicalLogic : HasClassicalLogic prop :=
  { byContradiction := @Classical.byContradiction }

  instance hasUnitType : HasUnitType prop :=
  { Unit           := True,
    unit           := trivial,
    unitIntroIsFun := λ _ => ⟨⟩ }

  -- Every equivalence relation can trivially be converted to an instance of `IsEquivalence`.
  instance relEquiv {α : Sort u} {R : GeneralizedRelation α prop} (e : Equivalence R) : IsEquivalence R :=
  { refl  := e.refl,
    trans := e.trans,
    symm  := ⟨e.symm, e.symm⟩ }

  namespace relEquiv

    instance eq     (α : Sort u)                : IsEquivalence (V := prop) (@Eq α) := relEquiv Eq.isEquivalence
    instance setoid (α : Sort u) [s : Setoid α] : IsEquivalence (V := prop) s.r     := relEquiv s.iseqv

  end relEquiv

  instance hasUnitEquivalences : unit.HasUnitEquivalences prop := ⟨unit.Rel⟩

  instance hasEquivCongr : HasEquivCongr prop :=
  { equivCongrArg := λ _ => unit.unitFunctor (U := unit) ⟨⟩ ⟨⟩,
    equivCongrFun := λ _ => unit.unitFunctor (U := unit) ⟨⟩ ⟨⟩ }

  instance hasNaturalEquivalences : HasNaturalEquivalences prop :=
  { equivHasInstEquivs := unit.hasUnitInstanceEquivalences unit,
    isNat              := λ _ _ _ _ => trivial }

  section NaturalTransformations

    variable {α : Sort u} {β : Sort v} {V : Universe.{v}}
             [HasInternalFunctors V] [HasExternalFunctors V prop]
             (R : GeneralizedRelation α V) (S : GeneralizedRelation β prop) [HasTrans S]
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

  instance hasNat {U₁ U₂ V : Universe} [HasExternalFunctors U₁ U₂] [HasExternalFunctors V prop] :
    HasNaturalQuantification U₁ U₂ V prop :=
  { hasNat := λ {α β} R S {h mF mG} F G => hasIntNat R S F G }

  instance hasInstanceIsomorphisms : HasInstanceIsomorphisms prop :=
  { equivIsIso := λ p => unit.isIsomorphismRelation (unit.Rel p) }

end prop

namespace type

  class IsEquiv {α β : type} (toFun : α ⟶' β) (invFun : β ⟶' α) where
  (leftInv  : ∀ a, invFun (toFun a) = a)
  (rightInv : ∀ b, toFun (invFun b) = b)

  instance hasExternalEquivalences : HasExternalEquivalences type type := ⟨IsEquiv⟩

  @[reducible] def isEquivalence {α β : type} (e : Equiv α β) :
    IsEquiv (sort.toBundledFunctor e.toFun) (sort.toBundledFunctor e.invFun) :=
  ⟨e.leftInv, e.rightInv⟩

  theorem isEquivalenceIsUnique {α β : type} {e : Equiv α β} (h : IsEquiv (sort.toBundledFunctor e.toFun) (sort.toBundledFunctor e.invFun)) :
    h = isEquivalence e := match h with
  | ⟨_, _⟩ => sorry -- by proof irrelevance

  @[reducible] def invIsEquivalence {α β : type} {toFun : α ⟶' β} {invFun : β ⟶' α} (h : IsEquiv toFun invFun) :
    IsEquiv invFun toFun :=
  ⟨h.rightInv, h.leftInv⟩

  @[reducible] def toBundledEquivalence {α β : type} (e : Equiv α β) : α ⟷' β :=
  ⟨sort.toBundledFunctor e.toFun, sort.toBundledFunctor e.invFun, isEquivalence e⟩

  @[reducible] def fromBundledEquivalence {α β : type} (E : α ⟷' β) : Equiv α β :=
  ⟨E.toFun.f, E.invFun.f, E.isEquiv.leftInv, E.isEquiv.rightInv⟩

  theorem fromToBundledEquivalence {α β : type} (e : Equiv α β) :
    fromBundledEquivalence (toBundledEquivalence e) = e := match e with
  | ⟨_, _, _, _⟩ => rfl

  theorem toFromBundledEquivalence {α β : type} (E : α ⟷' β) :
    toBundledEquivalence (fromBundledEquivalence E) = E := match E with
  | ⟨toFun, invFun, _⟩ => by simp; exact ⟨sort.toFromBundledFunctor toFun, sort.toFromBundledFunctor invFun,
                                          sorry⟩ -- by `isEquivalenceIsUnique`

  def equivEquiv (α β : type) : Equiv α β ≃ (α ⟷' β) :=
  { toFun    := toBundledEquivalence,
    invFun   := fromBundledEquivalence,
    leftInv  := fromToBundledEquivalence,
    rightInv := toFromBundledEquivalence }

  instance hasInternalEquivalences : HasInternalEquivalences type :=
  { Equiv                := Equiv,
    equivEquiv           := equivEquiv,
    equivElimToFunIsFun  := λ _ _ => ⟨⟩,
    equivElimInvFunIsFun := λ _ _ => ⟨⟩ }

  instance hasIdEquiv   : HasIdEquiv   type           := ⟨λ α   => isEquivalence (Equiv.refl α)⟩
  instance hasCompEquiv : HasCompEquiv type type type := ⟨λ E F => isEquivalence (Equiv.trans (fromBundledEquivalence E) (fromBundledEquivalence F))⟩
  instance hasInvEquiv  : HasInvEquiv  type type      := ⟨λ E   => invIsEquivalence E.isEquiv⟩

  instance hasEquivOp : HasEquivOp type :=
  { compEquivIsFun    := λ _ _   => ⟨⟩,
    compEquivFunIsFun := λ _ _ _ => ⟨⟩,
    invEquivIsFun     := λ _ _   => ⟨⟩,
    invEquivIsEquiv   := λ α β   => ⟨@Equiv.symm_symm α β, @Equiv.symm_symm β α⟩ }

  def prodEquiv (α β : type) : Prod α β ≃ (α ⊓' β) :=
  { toFun    := λ p => ⟨p.fst, p.snd⟩,
    invFun   := λ P => ⟨P.fst, P.snd⟩,
    leftInv  := λ ⟨_, _⟩ => rfl,
    rightInv := λ ⟨_, _⟩ => rfl }

  instance hasInternalProducts : HasInternalProducts type :=
  { Prod             := Prod,
    prodEquiv        := prodEquiv,
    prodIntroIsFun   := λ _ _ => ⟨⟩,
    prodElimFstIsFun := λ _ _ => ⟨⟩,
    prodElimSndIsFun := λ _ _ => ⟨⟩ }

  instance hasEmptyType : HasEmptyType type :=
  { Empty          := Empty,
    emptyIsEmpty   := λ a => (by induction a),
    emptyElimIsFun := λ _ => ⟨⟩ }

  instance hasUnitType : HasUnitType type :=
  { Unit           := Unit,
    unit           := ⟨⟩,
    unitIntroIsFun := λ _ => ⟨⟩ }

  instance hasInstanceEquivalences : HasInstanceEquivalences type := ⟨prop, @Eq⟩

  instance hasEquivCongr : HasEquivCongr type :=
  { equivCongrArg := λ F => sort.toBundledFunctor (congrArg F.f),
    equivCongrFun := λ a => sort.toBundledFunctor (λ h => congrFun h a) }

  instance hasNaturalEquivalences : HasNaturalEquivalences type :=
  { equivHasInstEquivs := unit.hasUnitInstanceEquivalences prop,
    isNat              := λ _ _ _ _ => trivial }

  instance hasInstanceIsomorphisms : HasInstanceIsomorphisms type :=
  { equivIsIso := λ α => unit.isIsomorphismRelation (V := prop) (@Eq α) }

end type
