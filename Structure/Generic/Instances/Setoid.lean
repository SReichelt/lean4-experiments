import Structure.Generic.Axioms
import Structure.Generic.Instances.Bundled



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u



def BundledSetoid := Bundled Setoid
@[reducible] def setoid : Universe := simpleBundledUniverse Setoid

namespace BundledSetoid

  instance isSetoid (S : setoid) : Setoid ⌈S⌉ := S.inst
  instance (S : setoid) : Setoid ⌈S⌉ := isSetoid S

  class IsFunctorial {S T : setoid} (f : S → T) : Type u where
  (mapEquiv {a b : S} : a ≈ b → f a ≈ f b)

  instance hasFunctoriality : Bundled.HasFunctoriality Setoid Setoid := ⟨IsFunctorial⟩

  namespace BundledFunctor

    theorem congrArg {S T : setoid} (F : S ⟶' T) {a b : S} : a ≈ b → F a ≈ F b := F.isFun.mapEquiv

    def Equiv {S T : setoid} (F G : S ⟶' T) := ∀ a, F a ≈ G a

    namespace Equiv

      variable {S T : setoid}

      theorem refl  (F     : S ⟶' T)                                 : Equiv F F := λ a => Setoid.refl  (F a)
      theorem symm  {F G   : S ⟶' T} (h : Equiv F G)                 : Equiv G F := λ a => Setoid.symm  (h a)
      theorem trans {F G H : S ⟶' T} (h : Equiv F G) (i : Equiv G H) : Equiv F H := λ a => Setoid.trans (h a) (i a)

      def isEquivalence : Equivalence (@Equiv S T) := ⟨refl, symm, trans⟩

    end Equiv

    instance isSetoid (S T : setoid) : Setoid (S ⟶' T) := ⟨Equiv, Equiv.isEquivalence⟩

    theorem congrFun {S T : setoid} {F G : S ⟶' T} (h : F ≈ G) (a : S) : F a ≈ G a := h a

    theorem congr {S T : setoid} {F G : S ⟶' T} {a b : S} : F ≈ G → a ≈ b → F a ≈ G b :=
    λ h₁ h₂ => Setoid.trans (congrFun h₁ a) (congrArg G h₂)

    instance hasFunctorInstances : Bundled.HasFunctorInstances Setoid := ⟨isSetoid⟩

  end BundledFunctor

  -- Although this duplicates generic proofs in `ConstructibleFunctors.lean`, we keep this version because
  -- it is much more readable and we can avoid the import.
  instance hasIdFun    : HasIdFun    setoid                             :=
  ⟨λ S           => ⟨id⟩⟩
  instance hasConstFun : HasConstFun setoid setoid               :=
  ⟨λ S {T}   c   => ⟨λ _ => Setoid.refl c⟩⟩
  instance hasCompFun  : HasCompFun  setoid setoid setoid :=
  ⟨λ {S T U} F G => ⟨BundledFunctor.congrArg G ∘ BundledFunctor.congrArg F⟩⟩

  -- Same.
  instance hasFunOp : HasFunOp setoid :=
  { constFunIsFun   := λ S T       => ⟨λ hc a   => hc⟩,
    appIsFun        := λ {S} a T   => ⟨λ hF     => BundledFunctor.congrFun hF a⟩,
    appFunIsFun     := λ S T       => ⟨λ ha F   => BundledFunctor.congrArg F ha⟩,
    dupIsFun        := λ {S T} F   => ⟨λ ha     => BundledFunctor.congr (BundledFunctor.congrArg F ha) ha⟩,
    dupFunIsFun     := λ S T       => ⟨λ hF a   => BundledFunctor.congrFun (BundledFunctor.congrFun hF a) a⟩,
    compFunIsFun    := λ {S T} F U => ⟨λ hG a   => BundledFunctor.congrFun hG (F a)⟩,
    compFunFunIsFun := λ S T U     => ⟨λ hF G a => BundledFunctor.congrArg G (BundledFunctor.congrFun hF a)⟩ }

  instance hasInstanceEquivalences : HasInstanceEquivalences setoid :=
  ⟨prop, λ S => (isSetoid S).r⟩

  instance hasEquivCongr : HasEquivCongr setoid :=
  { equivCongrArg := λ F => sort.toBundledFunctor (BundledFunctor.congrArg F),
    equivCongrFun := λ a => sort.toBundledFunctor (λ h => BundledFunctor.congrFun h a) }

  instance hasNaturalEquivalences : HasNaturalEquivalences setoid :=
  { equivHasInstEquivs := unit.hasUnitInstanceEquivalences prop,
    isNat              := λ _ _ _ _ => trivial }

  def eq (α : Sort u) : BundledSetoid :=
  { α    := α,
    inst := ⟨Eq, Eq.isEquivalence⟩ }

end BundledSetoid
