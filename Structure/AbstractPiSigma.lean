-- As a prerequisite for `AbstractBuildingBlocks.lean`, here we define generalized versions of Π and Σ
-- expressions, where all involved types are replaced by structures and all dependencies are functors.



import Structure.Basic
import Structure.FunctorStructure

open Morphisms
open Structure
open DependentStructure
open StructureFunctor
open Forgetfulness
open FunctorStructure



universes u v



namespace PiSigma

-- First, we define a "structure dependency" that holds the information contained in a Π or Σ type:
-- A structure (representing the type on the left-hand side) and a functor that returns a structure
-- (representing the dependent type on the right-hand side).

def StructureDependency := Σ' S : Structure, StructureFunctor S universeStructure



-- A Π expression of structures.

-- We already have a somewhat more general `DependentStructure` that holds the same data.
-- TODO: The naming isn't optimal here.
@[reducible] def RawPiExpr (F : StructureDependency) := DependentStructure F.snd.map

-- A structure that represents the type `∀ α, F α`. We need to wrap it this way because otherwise Lean's
-- type inference will get confused in places.
structure PiExpr (F : StructureDependency) where (map : RawPiExpr F)

instance (F : StructureDependency) : CoeFun (PiExpr F) (λ f => ∀ α : F.fst, (F.snd α).U) := ⟨PiExpr.map⟩

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

-- Every individual projection of `piStructure` is a functor.

namespace piStructure

def projFunctor (F : StructureDependency) (α : F.fst) : StructureFunctor (piStructure F) (F.snd α) :=
{ map     := λ g => g.map α,
  functor := { FF        := λ e => e α,
               isFunctor := { respectsSetoid := λ h   => h α,
                              respectsComp   := λ e f => Setoid.refl (f α • e α),
                              respectsId     := λ g   => Setoid.refl (id_ (g.map α)),
                              respectsInv    := λ e   => Setoid.refl (e α)⁻¹ } } }

end piStructure



-- A Σ expression of structures.

def SigmaExpr (F : StructureDependency) := Σ' α : F.fst, (F.snd α).U

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
⟨IsEquivalence.refl  s.fst,       InstanceEquiv.congrArg h₂ s.snd s.snd h₁⟩

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

-- Introduction and projections of `sigmaStructure` are functorial.

namespace sigmaStructure

variable (F : StructureDependency)

def mkSndEquiv {α β : F.fst} (e : α ≃ β) :
  incomingFunctorStructure (sigmaStructure F) (F.snd α) ≃ incomingFunctorStructure (sigmaStructure F) (F.snd β) :=
incomingFunctorEquiv (sigmaStructure F) (congrArgMap F.snd e)

def mkSndFunctor : StructureFunctor F.fst universeStructure :=
{ map     := λ α => incomingFunctorStructure (sigmaStructure F) (F.snd α),
  functor := { FF        := mkSndEquiv F,
               isFunctor := sorry } }

def mkDependency : StructureDependency := ⟨F.fst, mkSndFunctor F⟩

def mkExprFunctor (α : F.fst) : StructureFunctor (setoidStructure (F.snd α)) (sigmaStructure F) :=
{ map     := λ β => ⟨α, β⟩,
  functor := { FF        := λ {a b} h => ⟨id_ α, InstanceEquiv.congrArg (Setoid.symm (respectsId F.snd α)) a b h⟩,
               isFunctor := sorry } }

def mkExpr : PiExpr (mkDependency F) := ⟨mkExprFunctor F⟩

def projFstFunctor : StructureFunctor (sigmaStructure F) F.fst :=
{ map     := PSigma.fst,
  functor := { FF        := PSigma.fst,
               isFunctor := sorry } }

def projSndFunctor : StructureFunctor (sigmaStructure F) universeStructure :=
{ map     := λ s => F.snd s.fst,
  functor := { FF        := λ e => congrArgMap F.snd e.fst,
               isFunctor := sorry } }

def projSndDependency : StructureDependency := ⟨sigmaStructure F, projSndFunctor F⟩

def projSndExpr : PiExpr (projSndDependency F) := ⟨PSigma.snd⟩

end sigmaStructure



-- Since `StructureDependency` is just a sigma type, we can retroactively define it as a structure.

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



-- We have the familiar equivalences between dependent structures.
-- TODO: Could these become part of a general definition of the word "canonical"?

namespace PiSigmaEquivalences

variable (F : StructureDependency)

def innerPairStructure := setoidStructure (sigmaStructure F)

@[reducible] def PairToUniverseFunctor := StructureFunctor (innerPairStructure F) universeStructure

def sndStructure (α : F.fst) := setoidStructure (F.snd α)

variable (G : PairToUniverseFunctor F)

def innerPairDependency : StructureDependency := ⟨innerPairStructure F, G⟩

def makePairFunctor (α : F.fst) : StructureFunctor (sndStructure F α) universeStructure :=
compFun (sigmaStructure.mkExprFunctor F α) (compFun (toSetoidFunctor (sigmaStructure F)) G)

-- TODO: Much of this looks like we could just compose introduction and projection in just the right way.

def dependentPiStructure (α : F.fst) := piStructure ⟨sndStructure F α, makePairFunctor F G α⟩

def dependentPiFunctorCongrArgToFun {α β : F.fst} (e : α ≃ β) :
  SetoidStructureFunctor (dependentPiStructure F G α) (dependentPiStructure F G β) :=
{ map     := sorry,
  functor := { FF        := sorry,
               isFunctor := sorry } }

def dependentPiFunctorCongrArg {α β : F.fst} (e : α ≃ β) :
  dependentPiStructure F G α ≃ dependentPiStructure F G β :=
{ toFun    := dependentPiFunctorCongrArgToFun F G e,
  invFun   := dependentPiFunctorCongrArgToFun F G e⁻¹,
  leftInv  := sorry,
  rightInv := sorry }

def dependentPiFunctor    : StructureFunctor F.fst universeStructure :=
{ map     := dependentPiStructure F G,
  functor := { FF        := dependentPiFunctorCongrArg F G,
               isFunctor := sorry } }

def dependentSigmaFunctor : StructureFunctor F.fst universeStructure :=
{ map     := λ α => sigmaStructure ⟨sndStructure F α, makePairFunctor F G α⟩,
  functor := sorry }

-- `(∀ x : α, ∀ y : F x, G x y) ≃ (∀ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`(λ x y => g x y) ↦ (λ ⟨x, y⟩ => g x y)`)

def nestedPiDependency : StructureDependency := ⟨F.fst, dependentPiFunctor F G⟩

def piPiCurried   := piStructure (nestedPiDependency  F G)
def piPiUncurried := piStructure (innerPairDependency F G)

def piPiEquivToFun  : StructureFunctor (piPiCurried   F G) (piPiUncurried F G) :=
{ map     := λ g => ⟨λ ⟨α, β⟩ => (g.map α).map β⟩,
  functor := sorry }

def piPiEquivInvFun : StructureFunctor (piPiUncurried F G) (piPiCurried   F G) :=
{ map     := λ g => ⟨λ α => ⟨λ β => g.map ⟨α, β⟩⟩⟩,
  functor := sorry }

def piPiEquiv : StructureEquiv (piPiCurried F G) (piPiUncurried F G) :=
{ toFun    := piPiEquivToFun  F G,
  invFun   := piPiEquivInvFun F G,
  leftInv  := sorry,
  rightInv := sorry }

-- `(Σ x : α, Σ y : F x, G x y) ≃ (Σ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`⟨x, ⟨y, z⟩⟩ ↦ ⟨⟨x, y⟩, z⟩`)

def nestedSigmaDependency : StructureDependency := ⟨F.fst, dependentSigmaFunctor F G⟩

def sigmaSigmaCurried   := sigmaStructure (nestedSigmaDependency F G)
def sigmaSigmaUncurried := sigmaStructure (innerPairDependency   F G)

def sigmaSigmaEquivToFun  : StructureFunctor (sigmaSigmaCurried   F G) (sigmaSigmaUncurried F G) :=
{ map     := λ ⟨α, ⟨β, γ⟩⟩ => ⟨⟨α, β⟩, γ⟩,
  functor := sorry }

def sigmaSigmaEquivInvFun : StructureFunctor (sigmaSigmaUncurried F G) (sigmaSigmaCurried   F G) :=
{ map     := λ ⟨⟨α, β⟩, γ⟩ => ⟨α, ⟨β, γ⟩⟩,
  functor := sorry }

def sigmaSigmaEquiv : StructureEquiv (sigmaSigmaCurried F G) (sigmaSigmaUncurried F G) :=
{ toFun    := sigmaSigmaEquivToFun  F G,
  invFun   := sigmaSigmaEquivInvFun F G,
  leftInv  := sorry,
  rightInv := sorry }

-- `(∀ x : α, Σ y : F x, G x y) ≃ (Σ f : (∀ x : α, F x), ∀ x : α, G x (f x))`
-- (`(λ x => ⟨y, f x⟩ ↦ ⟨λ x => y, λ x => f x⟩`)

-- TODO

end PiSigmaEquivalences

end PiSigma
