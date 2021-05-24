import Structure.Generic.Axioms
import Structure.Generic.Instances.Bundled



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



def BundledSetoid := Bundled Setoid
@[reducible] def bundledSetoid : Universe := bundledUniverse (U := typeUniverse.{u}) Setoid

namespace BundledSetoid

  instance isSetoid (S : bundledSetoid) : Setoid ⌈S⌉ := S.inst
  instance (S : bundledSetoid) : Setoid ⌈S⌉ := isSetoid S

  class IsFunctorial {S T : bundledSetoid} (f : S → T) where
  (mapEquiv {a b : S} : a ≈ b → f a ≈ f b)

  instance hasFunctoriality : Bundled.HasFunctoriality.{u + 1, u + 1, v + 1, v + 1, 1} Setoid Setoid := ⟨IsFunctorial⟩

  namespace BundledFunctor

    theorem congrArg {S T : bundledSetoid} (F : S ⟶' T) {a b : S} : a ≈ b → F a ≈ F b := F.isFun.mapEquiv

    def Equiv {S T : bundledSetoid} (F G : S ⟶' T) := ∀ a, F a ≈ G a

    namespace Equiv

      variable {S T : bundledSetoid}

      theorem refl  (F     : S ⟶' T)                                 : Equiv F F := λ a => Setoid.refl  (F a)
      theorem symm  {F G   : S ⟶' T} (h : Equiv F G)                 : Equiv G F := λ a => Setoid.symm  (h a)
      theorem trans {F G H : S ⟶' T} (h : Equiv F G) (i : Equiv G H) : Equiv F H := λ a => Setoid.trans (h a) (i a)

      def isEquivalence : Equivalence (@Equiv S T) := ⟨refl, symm, trans⟩

    end Equiv

    instance isSetoid (S T : bundledSetoid) : Setoid (S ⟶' T) := ⟨Equiv, Equiv.isEquivalence⟩

    theorem congrFun {S T : bundledSetoid} {F G : S ⟶' T} (h : F ≈ G) (a : S) : F a ≈ G a := h a

    theorem congr {S T : bundledSetoid} {F G : S ⟶' T} {a b : S} : F ≈ G → a ≈ b → F a ≈ G b :=
    λ h₁ h₂ => Setoid.trans (congrFun h₁ a) (congrArg G h₂)

    instance hasFunctorInstances : Bundled.HasFunctorInstances.{u + 1, u + 1, 1} Setoid := ⟨isSetoid⟩

  end BundledFunctor

  instance hasInternalFunctors : HasInternalFunctors bundledSetoid := Bundled.hasInternalFunctors Setoid

  instance hasIdFun    : HasIdFun    bundledSetoid.{u}                                     :=
  ⟨λ S           => ⟨id⟩⟩
  instance hasConstFun : HasConstFun bundledSetoid.{u} bundledSetoid.{v}                   :=
  ⟨λ S {T}   c   => ⟨Function.const _ (Setoid.refl c)⟩⟩
  instance hasCompFun  : HasCompFun  bundledSetoid.{u} bundledSetoid.{v} bundledSetoid.{w} :=
  ⟨λ {S T U} F G => ⟨G.isFun.mapEquiv ∘ F.isFun.mapEquiv⟩⟩

  instance hasInstanceEquivalences : HasInstanceEquivalences bundledSetoid :=
  ⟨propUniverse, λ S => (isSetoid S).r⟩

  instance hasFunctorialEquivalences : HasFunctorialEquivalences bundledSetoid :=
  { equivCongr := BundledFunctor.congr }

  -- TODO: Move to `Bundled.lean`
  instance hasFunOp : HasFunOp bundledSetoid :=
  { constFunIsFun   := λ S T       => ⟨λ hc a   => hc⟩,
    appIsFun        := λ {S} a T   => ⟨λ hF     => BundledFunctor.congrFun hF a⟩,
    appFunIsFun     := λ S T       => ⟨λ ha F   => BundledFunctor.congrArg F ha⟩,
    dupIsFun        := λ {S T} F   => ⟨λ ha     => BundledFunctor.congr (BundledFunctor.congrArg F ha) ha⟩,
    dupFunIsFun     := λ S T       => ⟨λ hF a   => BundledFunctor.congrFun (BundledFunctor.congrFun hF a) a⟩,
    compFunIsFun    := λ {S T} F U => ⟨λ hG a   => BundledFunctor.congrFun hG (F a)⟩,
    compFunFunIsFun := λ S T U     => ⟨λ hF G a => BundledFunctor.congrArg G (BundledFunctor.congrFun hF a)⟩ }

  def eq (α : Sort u) : BundledSetoid :=
  { α    := α,
    inst := ⟨Eq, Eq.isEquivalence⟩ }

end BundledSetoid
