import Structure.Basic
import Structure.SortStructure

open Morphisms
open Structure
open DependentStructure
open StructureFunctor
open Forgetfulness



universes u v



-- In this file, we define some basic building blocks which are closely related to the cases mentioned in
-- the introduction in `Basic.lean`.

namespace PiSigma

-- We start with abstractions of Π and Σ types where types and instances are replaced with structures.
-- Although Σ may be redundant in theory, it is very important for our use case because bundled instances
-- of type classes are Σ types.

def StructureDependency := Σ' S : Structure, StructureFunctor S universeStructure

@[reducible] def DependentStructureType (F : StructureDependency) := DependentStructure F.snd.map

def toStructureDependency {S : Structure} (F : StructureFunctor S sortStructure) : StructureDependency :=
⟨S, compFun F sortToStructureFunctor⟩

-- A structure that represents the type `∀ α, F α`. We need to wrap it this way because otherwise Lean's
-- type inference will get confused in places.
structure PiExpr (F : StructureDependency) where (map : ∀ α : F.fst, (F.snd α).U)

instance (F : StructureDependency) : CoeFun (PiExpr F) (λ f => ∀ α : F.fst, (F.snd α).U) := ⟨PiExpr.map⟩

def SigmaExpr (F : StructureDependency) := Σ' α : F.fst, (F.snd α).U

-- Every term of type `∀ x, F x` or `Σ' x, F x` where everything has structures and functors can be
-- converted to an instance of `PiExpr` or `SigmaExpr`, respectively.

def encodePiExpr    {α : Sort u} [h : HasStructure α] (F : StructureFunctor (defaultStructure α) sortStructure) (f : ∀  x : α, F x) :
  PiExpr    (toStructureDependency F) := ⟨f⟩

def encodeSigmaExpr {α : Sort u} [h : HasStructure α] (F : StructureFunctor (defaultStructure α) sortStructure) (s : Σ' x : α, F x) :
  SigmaExpr (toStructureDependency F) := ⟨s.fst, s.snd⟩



-- We can define equivalences between such Π and Σ expressions. These fulfill the isomorphism axioms
-- and thus turn the types `PiExpr F` and `SigmaExpr F` into structures.

def PiEquiv {F : StructureDependency} (f g : PiExpr F) := DependentEquiv f.map g.map

namespace PiEquiv

variable {F : StructureDependency}

def refl  (f     : PiExpr F)                                     : PiEquiv f f :=
DependentEquiv.refl  f.map
def symm  {f g   : PiExpr F} (φ : PiEquiv f g)                   : PiEquiv g f :=
DependentEquiv.symm  φ
def trans {f g h : PiExpr F} (φ : PiEquiv f g) (ψ : PiEquiv g h) : PiEquiv f h :=
DependentEquiv.trans φ ψ

def piEquiv (f g : PiExpr F) := DependentEquiv.dependentEquiv f.map g.map

-- Unfortunately, uncommenting this line causes Lean to hang indefinitely, so we have to copy and paste the code instead.
--instance piEquivHasIso : HasIsomorphisms (@piEquiv F) := @DependentEquiv.dependentEquivHasIso F.fst F.snd.map

instance piEquivHasIso : HasIsomorphisms (@piEquiv F) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ α => congrArgComp (hφ α) (hψ α),
  assoc        := λ φ ψ χ α => assoc        (φ α) (ψ α) (χ α),
  id           := refl,
  leftId       := λ φ     α => leftId       (φ α),
  rightId      := λ φ     α => rightId      (φ α),
  inv          := symm,
  congrArgInv  := λ hφ    α => congrArgInv  (hφ α),
  leftInv      := λ φ     α => leftInv      (φ α),
  rightInv     := λ φ     α => rightInv     (φ α),
  invInv       := λ φ     α => invInv       (φ α),
  compInv      := λ φ ψ   α => compInv      (φ α) (ψ α),
  idInv        := λ f     α => idInv        (f α) }

end PiEquiv

instance piHasStructure (F : StructureDependency) : HasStructure (PiExpr F) := ⟨PiEquiv.piEquiv⟩
def piStructure (F : StructureDependency) : Structure := ⟨PiExpr F⟩



-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence `e` between the types such that `congrArgMap F.snd e` maps one instance of
-- the type class to the other.

def SigmaEquiv {F : StructureDependency} (s t : SigmaExpr F) :=
Σ' e : s.fst ≃ t.fst, InstanceEquiv (congrArgMap F.snd e) s.snd t.snd

namespace SigmaEquiv

variable {F : StructureDependency}

def refl  (s     : SigmaExpr F)                                           : SigmaEquiv s s :=
let h₁ := InstanceEquiv.refl (setoidStructure (F.snd s.fst)) s.snd;
let h₂ := Setoid.symm (respectsId   F.snd s.fst);
⟨IsEquivalence.refl  s.fst,         InstanceEquiv.congrArg h₂ s.snd s.snd h₁⟩

def symm  {s t   : SigmaExpr F} (φ : SigmaEquiv s t)                      : SigmaEquiv t s :=
let h₁ := InstanceEquiv.symm (congrArgMap F.snd φ.fst) s.snd t.snd φ.snd;
let h₂ := Setoid.symm (respectsInv  F.snd φ.fst);
⟨IsEquivalence.symm  φ.fst,       InstanceEquiv.congrArg h₂ t.snd s.snd h₁⟩

def trans {r s t : SigmaExpr F} (φ : SigmaEquiv r s) (ψ : SigmaEquiv s t) : SigmaEquiv r t :=
let h₁ := InstanceEquiv.trans (congrArgMap F.snd φ.fst) (congrArgMap F.snd ψ.fst) r.snd s.snd t.snd φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp F.snd φ.fst ψ.fst);
⟨IsEquivalence.trans φ.fst ψ.fst, InstanceEquiv.congrArg h₂ r.snd t.snd h₁⟩

-- No need to compare `φ.snd` and `ψ.snd` because they are proofs.
def SigmaEquivEquiv {s t : SigmaExpr F} (φ ψ : SigmaEquiv s t) := φ.fst ≈ ψ.fst

namespace SigmaEquivEquiv

variable {s t : SigmaExpr F}

theorem refl  (φ     : SigmaEquiv s t)                                                     : SigmaEquivEquiv φ φ :=
Setoid.refl  φ.fst

theorem symm  {φ ψ   : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ)                           : SigmaEquivEquiv ψ φ :=
Setoid.symm  e

theorem trans {φ ψ χ : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ) (f : SigmaEquivEquiv ψ χ) : SigmaEquivEquiv φ χ :=
Setoid.trans e f

instance sigmaEquivSetoid : Setoid (SigmaEquiv s t) := ⟨SigmaEquivEquiv, ⟨refl, symm, trans⟩⟩

end SigmaEquivEquiv

def sigmaEquiv (s t : SigmaExpr F) : BundledSetoid := ⟨SigmaEquiv s t⟩

instance sigmaEquivHasIso : HasIsomorphisms (@sigmaEquiv F) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ => congrArgComp hφ hψ,
  assoc        := λ φ ψ χ => assoc        φ.fst ψ.fst χ.fst,
  id           := refl,
  leftId       := λ φ     => leftId       φ.fst,
  rightId      := λ φ     => rightId      φ.fst,
  inv          := symm,
  congrArgInv  := λ hφ    => congrArgInv  hφ,
  leftInv      := λ φ     => leftInv      φ.fst,
  rightInv     := λ φ     => rightInv     φ.fst,
  invInv       := λ φ     => invInv       φ.fst,
  compInv      := λ φ ψ   => compInv      φ.fst ψ.fst,
  idInv        := λ s     => idInv        s.fst }

end SigmaEquiv

instance sigmaHasStructure (F : StructureDependency) : HasStructure (SigmaExpr F) := ⟨SigmaEquiv.sigmaEquiv⟩
def sigmaStructure (F : StructureDependency) : Structure := ⟨SigmaExpr F⟩



-- Since `StructureDependency` is just a sigma type, we can retroactively define it as a structure.
-- However, in our formalization with coercion to setoids, this requires classical logic.

-- TODO: This would be nice, but it doesn't quite work in the setoid variant: `dependencyFunctor` is the
-- same as `incomingFunctorFunctor universeStructure` except for the setoid coercion. That means we
-- cannot declare `dependencyFunctor` the way we want, and if we use `incomingFunctorFunctor`, it no
-- longer matches `StructureDependency`.

-- def dependencyFunctor : StructureFunctor universeStructure universeStructure :=
-- { map     := λ S => functorStructure S universeStructure,
--   functor := sorry }
-- 
-- def dependencyDependency : StructureDependency := ⟨universeStructure, dependencyFunctor⟩
-- 
-- instance dependencyHasStructure : HasStructure StructureDependency := sigmaHasStructure dependencyDependency
-- def dependencyStructure : Structure := ⟨StructureDependency⟩
-- 
-- -- Now `piStructure` and `sigmaStructure` can be viewed as dependent structures.
-- 
-- def piFunctor    : StructureFunctor dependencyStructure universeStructure :=
-- { map     := piStructure,
--   functor := sorry }
-- 
-- def sigmaFunctor : StructureFunctor dependencyStructure universeStructure :=
-- { map     := sigmaStructure,
--   functor := sorry }
-- 
-- def piDependency    : StructureDependency := ⟨dependencyStructure, piFunctor⟩
-- def sigmaDependency : StructureDependency := ⟨dependencyStructure, sigmaFunctor⟩
-- 
-- def PiStructureType    := DependentStructureType piDependency
-- def SigmaStructureType := DependentStructureType sigmaDependency



-- We have the familiar equivalences between dependent structures.
-- TODO: Could these become part of a general definition of the word "canonical"?

namespace PiSigmaEquivalences

@[reducible] def PairToUniverseFunctor (F : StructureDependency) :=
StructureFunctor (sigmaStructure F) universeStructure

def makePairFunctor {F : StructureDependency} (G : PairToUniverseFunctor F) (α : F.fst) :
  StructureFunctor (F.snd α) universeStructure :=
{ map     := λ β => G ⟨α, β⟩,
  functor := sorry }

def dependentPiFunctor    (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureFunctor F.fst universeStructure :=
{ map     := λ α => piStructure    ⟨F.snd α, makePairFunctor G α⟩,
  functor := sorry }

def dependentSigmaFunctor (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureFunctor F.fst universeStructure :=
{ map     := λ α => sigmaStructure ⟨F.snd α, makePairFunctor G α⟩,
  functor := sorry }

-- `(∀ x : α, ∀ y : F x, G x y) ≃ (∀ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`(λ x y => g x y) ↦ (λ ⟨x, y⟩ => g x y)`)

def applyPair {F : StructureDependency} {G : PairToUniverseFunctor F}
  (g : PiExpr ⟨F.fst, dependentPiFunctor F G⟩) (s : SigmaExpr F) : (G ⟨s.fst, s.snd⟩).U :=
(g s.fst).map s.snd

def applyPair' {F : StructureDependency} {G : PairToUniverseFunctor F}
  (g : PiExpr ⟨F.fst, dependentPiFunctor F G⟩) (s : SigmaExpr F) : (G s).U :=
sorry -- TODO: Should be `applyPair g s`, but there seems to be some definitional equality problem.

def piPiEquivToFun (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureFunctor (piStructure ⟨F.fst, dependentPiFunctor F G⟩) (piStructure ⟨sigmaStructure F, G⟩) :=
{ map     := λ g => ⟨applyPair' g⟩,
  functor := sorry }

def applyFields {F : StructureDependency} {G : PairToUniverseFunctor F}
  (g : PiExpr ⟨sigmaStructure F, G⟩) (α : F.fst) (β : (F.snd α).U) : (G ⟨α, β⟩).U :=
g ⟨α, β⟩

def piPiEquivInvFun (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureFunctor (piStructure ⟨sigmaStructure F, G⟩) (piStructure ⟨F.fst, dependentPiFunctor F G⟩) :=
{ map     := λ g => sorry, -- TODO: Should be `applyFields g`.
  functor := sorry }

def piPiEquiv (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureEquiv (piStructure ⟨F.fst, dependentPiFunctor F G⟩) (piStructure ⟨sigmaStructure F, G⟩) :=
sorry

-- `(Σ x : α, Σ y : F x, G x y) ≃ (Σ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`⟨x, ⟨y, z⟩⟩ ↦ ⟨⟨x, y⟩, z⟩`)

def sigmaSigmaEquivToFun  (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureFunctor (sigmaStructure ⟨F.fst, dependentSigmaFunctor F G⟩) (sigmaStructure ⟨sigmaStructure F, G⟩) :=
{ map     := λ ⟨α, ⟨β, γ⟩⟩ => ⟨⟨α, β⟩, γ⟩,
  functor := sorry }

def sigmaSigmaEquivInvFun (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureFunctor (sigmaStructure ⟨sigmaStructure F, G⟩) (sigmaStructure ⟨F.fst, dependentSigmaFunctor F G⟩) :=
{ map     := λ ⟨⟨α, β⟩, γ⟩ => ⟨α, ⟨β, γ⟩⟩,
  functor := sorry }

def sigmaSigmaEquiv (F : StructureDependency) (G : PairToUniverseFunctor F) :
  StructureEquiv (sigmaStructure ⟨F.fst, dependentSigmaFunctor F G⟩) (sigmaStructure ⟨sigmaStructure F, G⟩) :=
{ toFun    := sigmaSigmaEquivToFun  F G,
  invFun   := sigmaSigmaEquivInvFun F G,
  leftInv  := sorry,
  rightInv := sorry }

-- `(∀ x : α, Σ y : F x, G x y) ≃ (Σ f : (∀ x : α, F x), ∀ x : α, G x (f x))`
-- (`(λ x => ⟨y, f x⟩ ↦ ⟨λ x => y, λ x => f x⟩`)

-- TODO

end PiSigmaEquivalences

end PiSigma
