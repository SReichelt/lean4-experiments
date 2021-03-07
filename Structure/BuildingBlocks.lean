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

namespace BuildingBlocks

structure DependentFunctor where
(S : Structure)
(C : StructureFunctor S universeStructure)

def makeDependentFunctor {S : Structure} (C : StructureFunctor S sortStructure) : DependentFunctor :=
⟨S, compFun C sortToStructureFunctor⟩

structure EncodedPiExpr (T : DependentFunctor) where
(map (α : T.S) : (T.C α).U)

instance (T : DependentFunctor) : CoeFun (EncodedPiExpr T) (λ F => ∀ α : T.S, (T.C α).U) := ⟨EncodedPiExpr.map⟩

-- TODO: Σ may be redundant because everything is built on Π/∀ in Lean.

structure EncodedSigmaExpr (T : DependentFunctor) where
(α : T.S)
(x : (T.C α).U)

-- Every term of type `∀ x, C x` or `Σ' x, C x` where everything has structures and functors can be
-- converted to an instance of `EncodedPiExpr` or `EncodedSigmaExpr`, respectively.

-- TODO: Figure out in which cases we can determine the functor properties of `C` automatically.
-- Easiest case: `C` does not actually depend on `x`, i.e. we have a function...

def encodePiExpr    {α : Sort u} [h : HasStructure α] {C : StructureFunctor (defaultStructure α) sortStructure} (f : ∀  x : α, C x) :
  EncodedPiExpr    (makeDependentFunctor C) := ⟨f⟩

def encodeSigmaExpr {α : Sort u} [h : HasStructure α] {C : StructureFunctor (defaultStructure α) sortStructure} (f : Σ' x : α, C x) :
  EncodedSigmaExpr (makeDependentFunctor C) := ⟨f.fst, f.snd⟩



-- We can define equivalences between such Π and Σ expressions. These fulfill the isomorphism axioms
-- and thus turn the types `EncodedPiExpr T` and `EncodedSigmaExpr T` into structures.

def PiEquiv {T : DependentFunctor} (F G : EncodedPiExpr T) := DependentEquiv F.map G.map

namespace PiEquiv

variable {T : DependentFunctor}

def refl  (F     : EncodedPiExpr T)                                     : PiEquiv F F :=
DependentEquiv.refl  F.map
def symm  {F G   : EncodedPiExpr T} (φ : PiEquiv F G)                   : PiEquiv G F :=
DependentEquiv.symm  φ
def trans {F G H : EncodedPiExpr T} (φ : PiEquiv F G) (ψ : PiEquiv G H) : PiEquiv F H :=
DependentEquiv.trans φ ψ

def piEquiv (F G : EncodedPiExpr T) := DependentEquiv.dependentEquiv F.map G.map

-- Unfortunately, uncommenting this line (after uncommenting DependentEquiv.dependentEquivHasIso first)
-- causes Lean to hang indefinitely, so we have to copy and paste the code instead.
--instance piEquivHasIso : HasIsomorphisms (@piEquiv T) := @DependentEquiv.dependentEquivHasIso T.S T.C.map

instance piEquivHasIso : HasIsomorphisms (@piEquiv T) :=
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
  idInv        := λ F     α => idInv        (F α) }

end PiEquiv

open PiEquiv

instance piHasStructure (T : DependentFunctor) : HasStructure (EncodedPiExpr T) := ⟨piEquiv⟩
def piStructure (T : DependentFunctor) : Structure := ⟨EncodedPiExpr T⟩



-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence between the types such that `congrArgMap` maps one instance of the type
-- class to the other.

def SigmaEquiv {T : DependentFunctor} (F G : EncodedSigmaExpr T) :=
Σ' e : F.α ≃ G.α, InstanceEquiv (T.C.congrArgMap e) F.x G.x

namespace SigmaEquiv

variable {T : DependentFunctor}

def refl  (F     : EncodedSigmaExpr T)                                           : SigmaEquiv F F :=
let h₁ := InstanceEquiv.refl (setoidStructure (T.C F.α)) F.x;
let h₂ := Setoid.symm (respectsId   T.C F.α);
⟨IsEquivalence.refl  F.α,         InstanceEquiv.congrArg h₂ F.x F.x h₁⟩

def symm  {F G   : EncodedSigmaExpr T} (φ : SigmaEquiv F G)                      : SigmaEquiv G F :=
let h₁ := InstanceEquiv.symm (congrArgMap T.C φ.fst) F.x G.x φ.snd;
let h₂ := Setoid.symm (respectsInv  T.C φ.fst);
⟨IsEquivalence.symm  φ.fst,       InstanceEquiv.congrArg h₂ G.x F.x h₁⟩

def trans {F G H : EncodedSigmaExpr T} (φ : SigmaEquiv F G) (ψ : SigmaEquiv G H) : SigmaEquiv F H :=
let h₁ := InstanceEquiv.trans (congrArgMap T.C φ.fst) (congrArgMap T.C ψ.fst) F.x G.x H.x φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp T.C φ.fst ψ.fst);
⟨IsEquivalence.trans φ.fst ψ.fst, InstanceEquiv.congrArg h₂ F.x H.x h₁⟩

-- No need to compare `φ.snd` and `ψ.snd` because they are proofs.
def SigmaEquivEquiv {F G : EncodedSigmaExpr T} (φ ψ : SigmaEquiv F G) := φ.fst ≈ ψ.fst

namespace SigmaEquivEquiv

variable {F G : EncodedSigmaExpr T}

theorem refl  (φ     : SigmaEquiv F G)                                                     : SigmaEquivEquiv φ φ :=
Setoid.refl  φ.fst

theorem symm  {φ ψ   : SigmaEquiv F G} (e : SigmaEquivEquiv φ ψ)                           : SigmaEquivEquiv ψ φ :=
Setoid.symm  e

theorem trans {φ ψ χ : SigmaEquiv F G} (e : SigmaEquivEquiv φ ψ) (f : SigmaEquivEquiv ψ χ) : SigmaEquivEquiv φ χ :=
Setoid.trans e f

instance sigmaEquivSetoid : Setoid (SigmaEquiv F G) := ⟨SigmaEquivEquiv, ⟨refl, symm, trans⟩⟩

end SigmaEquivEquiv

def sigmaEquiv (F G : EncodedSigmaExpr T) : BundledSetoid := ⟨SigmaEquiv F G⟩

instance sigmaEquivHasIso : HasIsomorphisms (@sigmaEquiv T) :=
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
  idInv        := λ F     => idInv        F.α }

end SigmaEquiv

open SigmaEquiv

instance sigmaHasStructure (T : DependentFunctor) : HasStructure (EncodedSigmaExpr T) := ⟨@sigmaEquiv T⟩
def sigmaStructure (T : DependentFunctor) : Structure := ⟨EncodedSigmaExpr T⟩



-- If we have an `Equiv` with a type that has a structure, we can transport the structure along
-- that `Equiv`.

-- TODO: Do we still need this?

instance hasEquivalentStructure {α : Sort u} {β : Sort v} [h : HasStructure β] (e : Equiv α β) : HasStructure α :=
{ M := λ a b => h.M (e.toFun a) (e.toFun b),
  h := { comp         := h.h.comp,
         congrArgComp := h.h.congrArgComp,
         assoc        := λ _ _ => h.h.assoc    _ _,
         id           := λ _ => h.h.id _,
         leftId       := λ _   => h.h.leftId   _,
         rightId      := λ _   => h.h.rightId  _,
         inv          := h.h.inv,
         congrArgInv  := h.h.congrArgInv,
         leftInv      := λ _   => h.h.leftInv  _,
         rightInv     := λ _   => h.h.rightInv _,
         invInv       := λ _   => h.h.invInv   _,
         compInv      := λ _ _ => h.h.compInv  _ _,
         idInv        := λ _   => h.h.idInv    _ } }

-- Obviously, this turns the `Equiv` into a `StructureEquiv` between the two structures.

-- TODO



-- If `C` is a type class, we need to show that it is a functor in order to use our abstract framework.
-- We can do that by providing equivalences between `C α` and `D α`, where `D` is already known to be a
-- functor from `sortStructure` to `sortStructure`.

def TypeClass := Type u → Type v

def TypeClassEquiv (C D : TypeClass) := ∀ α, Equiv (C α) (D α)

def TypeClassFunctor := StructureFunctor sortStructure sortStructure

def toTypeClassFunctor (C : TypeClass) (D : TypeClassFunctor) (φ : TypeClassEquiv C D.map) : TypeClassFunctor :=
proxyFunctor C D φ

end BuildingBlocks

open BuildingBlocks
