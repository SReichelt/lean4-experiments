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

structure StructureDependency where
(S : Structure)
(F : StructureFunctor S universeStructure)

def DependentStructureType (F : StructureDependency) := DependentStructure F.F.map

def toStructureDependency {S : Structure} (F : StructureFunctor S sortStructure) : StructureDependency :=
⟨S, compFun F sortToStructureFunctor⟩

structure EncodedPiExpr (F : StructureDependency) where
(map (α : F.S) : (F.F α).U)

instance (F : StructureDependency) : CoeFun (EncodedPiExpr F) (λ f => ∀ α : F.S, (F.F α).U) := ⟨EncodedPiExpr.map⟩

structure EncodedSigmaExpr (F : StructureDependency) where
(α : F.S)
(x : (F.F α).U)

-- Every term of type `∀ x, F x` or `Σ' x, F x` where everything has structures and functors can be
-- converted to an instance of `EncodedPiExpr` or `EncodedSigmaExpr`, respectively.

def encodePiExpr    {α : Sort u} [h : HasStructure α] (F : StructureFunctor (defaultStructure α) sortStructure) (f : ∀  x : α, F x) :
  EncodedPiExpr    (toStructureDependency F) := ⟨f⟩

def encodeSigmaExpr {α : Sort u} [h : HasStructure α] (F : StructureFunctor (defaultStructure α) sortStructure) (s : Σ' x : α, F x) :
  EncodedSigmaExpr (toStructureDependency F) := ⟨s.fst, s.snd⟩



-- We can define equivalences between such Π and Σ expressions. These fulfill the isomorphism axioms
-- and thus turn the types `EncodedPiExpr F` and `EncodedSigmaExpr F` into structures.

def PiEquiv {F : StructureDependency} (f g : EncodedPiExpr F) := DependentEquiv f.map g.map

namespace PiEquiv

variable {F : StructureDependency}

def refl  (f     : EncodedPiExpr F)                                     : PiEquiv f f :=
DependentEquiv.refl  f.map
def symm  {f g   : EncodedPiExpr F} (φ : PiEquiv f g)                   : PiEquiv g f :=
DependentEquiv.symm  φ
def trans {f g h : EncodedPiExpr F} (φ : PiEquiv f g) (ψ : PiEquiv g h) : PiEquiv f h :=
DependentEquiv.trans φ ψ

def piEquiv (f g : EncodedPiExpr F) := DependentEquiv.dependentEquiv f.map g.map

-- Unfortunately, uncommenting this line (after uncommenting DependentEquiv.dependentEquivHasIso first)
-- causes Lean to hang indefinitely, so we have to copy and paste the code instead.
--instance piEquivHasIso : HasIsomorphisms (@piEquiv T) := @DependentEquiv.dependentEquivHasIso T.S T.C.map

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

instance piHasStructure (F : StructureDependency) : HasStructure (EncodedPiExpr F) := ⟨PiEquiv.piEquiv⟩
def piStructure (F : StructureDependency) : Structure := ⟨EncodedPiExpr F⟩



-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence between the types such that `congrArgMap` maps one instance of the type
-- class to the other.

def SigmaEquiv {F : StructureDependency} (s t : EncodedSigmaExpr F) :=
Σ' e : s.α ≃ t.α, InstanceEquiv (congrArgMap F.F e) s.x t.x

namespace SigmaEquiv

variable {F : StructureDependency}

def refl  (s     : EncodedSigmaExpr F)                                           : SigmaEquiv s s :=
let h₁ := InstanceEquiv.refl (setoidStructure (F.F s.α)) s.x;
let h₂ := Setoid.symm (respectsId   F.F s.α);
⟨IsEquivalence.refl  s.α,         InstanceEquiv.congrArg h₂ s.x s.x h₁⟩

def symm  {s t   : EncodedSigmaExpr F} (φ : SigmaEquiv s t)                      : SigmaEquiv t s :=
let h₁ := InstanceEquiv.symm (congrArgMap F.F φ.fst) s.x t.x φ.snd;
let h₂ := Setoid.symm (respectsInv  F.F φ.fst);
⟨IsEquivalence.symm  φ.fst,       InstanceEquiv.congrArg h₂ t.x s.x h₁⟩

def trans {r s t : EncodedSigmaExpr F} (φ : SigmaEquiv r s) (ψ : SigmaEquiv s t) : SigmaEquiv r t :=
let h₁ := InstanceEquiv.trans (congrArgMap F.F φ.fst) (congrArgMap F.F ψ.fst) r.x s.x t.x φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp F.F φ.fst ψ.fst);
⟨IsEquivalence.trans φ.fst ψ.fst, InstanceEquiv.congrArg h₂ r.x t.x h₁⟩

-- No need to compare `φ.snd` and `ψ.snd` because they are proofs.
def SigmaEquivEquiv {s t : EncodedSigmaExpr F} (φ ψ : SigmaEquiv s t) := φ.fst ≈ ψ.fst

namespace SigmaEquivEquiv

variable {s t : EncodedSigmaExpr F}

theorem refl  (φ     : SigmaEquiv s t)                                                     : SigmaEquivEquiv φ φ :=
Setoid.refl  φ.fst

theorem symm  {φ ψ   : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ)                           : SigmaEquivEquiv ψ φ :=
Setoid.symm  e

theorem trans {φ ψ χ : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ) (f : SigmaEquivEquiv ψ χ) : SigmaEquivEquiv φ χ :=
Setoid.trans e f

instance sigmaEquivSetoid : Setoid (SigmaEquiv s t) := ⟨SigmaEquivEquiv, ⟨refl, symm, trans⟩⟩

end SigmaEquivEquiv

def sigmaEquiv (s t : EncodedSigmaExpr F) : BundledSetoid := ⟨SigmaEquiv s t⟩

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
  idInv        := λ s     => idInv        s.α }

end SigmaEquiv

instance sigmaHasStructure (F : StructureDependency) : HasStructure (EncodedSigmaExpr F) := ⟨SigmaEquiv.sigmaEquiv⟩
def sigmaStructure (F : StructureDependency) : Structure := ⟨EncodedSigmaExpr F⟩



-- Since `StructureDependency` is actually just a sigma type as well, we can retroactively define it as a
-- structure.

def dependencyFunctor : StructureFunctor universeStructure universeStructure :=
{ map     := λ S => functorStructure S universeStructure,
  functor := sorry }  -- TODO: This can be stated more generally about maps into `functorStructure`.

def dependencyDependency : StructureDependency := ⟨universeStructure, dependencyFunctor⟩

def dependencyEquivSigma : Equiv StructureDependency (EncodedSigmaExpr dependencyDependency) :=
{ toFun    := λ ⟨S, F⟩ => ⟨S, F⟩,
  invFun   := λ ⟨S, F⟩ => ⟨S, F⟩,
  leftInv  := λ ⟨S, F⟩ => rfl,
  rightInv := λ ⟨S, F⟩ => rfl }

instance dependencyHasStructure : HasStructure StructureDependency := hasEquivalentStructure dependencyEquivSigma

-- This gives a "deterministic timeout" if we don't specify `dependencyHasStructure` explicitly, which is strange.
def dependencyStructure : Structure := { U := StructureDependency, h := dependencyHasStructure }

-- Now `piStructure` and `sigmaStructure` can be viewed as dependent structures.

def piFunctor    : StructureFunctor dependencyStructure universeStructure :=
{ map     := piStructure,
  functor := sorry }

def sigmaFunctor : StructureFunctor dependencyStructure universeStructure :=
{ map     := sigmaStructure,
  functor := sorry }

def piDependency    : StructureDependency := ⟨dependencyStructure, piFunctor⟩
def sigmaDependency : StructureDependency := ⟨dependencyStructure, sigmaFunctor⟩

def PiStructureType    := DependentStructureType piDependency
def SigmaStructureType := DependentStructureType sigmaDependency

end PiSigma
