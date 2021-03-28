-- As a prerequisite for `AbstractBuildingBlocks.lean`, here we define generalized versions of Π and Σ
-- expressions, where all involved types are replaced by structures and all dependencies are functors.



import Structure.Basic
import Structure.UniverseFunctor
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

structure StructureDependency where
(S : Structure)
(F : UniverseFunctor S)

namespace StructureDependency

def constDep (S T : Structure) : StructureDependency := ⟨S, constFun T⟩

structure StructureDependencyEquiv (F G : StructureDependency) where
(φ : StructureEquiv F.S G.S)
(ψ : F.F ≃ G.F ⊙ φ.toFun)

end StructureDependency



-- A Π expression of structures.

@[reducible] def RawPiExpr (F : StructureDependency) := DependentStructure (strictUniverseFunctor F.F).map

-- A structure that represents a functorial version of the type `∀ α : F.S, F.F α`.
-- Since `F` is a functor, `e : α ≃ β` induces an `e' : F.F α ≃ F.F β`. We then require an
-- `f : PiExpr F` to produce an instance equivalence between `f α : F.F α` and `f β : F.F β`.
-- As a special case, if `F.F` is constant, this ensures that `f` is a functor.

structure PiExpr (F : StructureDependency) where
(map                              : RawPiExpr F)
(congrArg {α β : F.S} (e : α ≃ β) : InstanceEquiv (congrArgMap F.F e) (map α) (map β))

instance (F : StructureDependency) : CoeFun (PiExpr F) (λ _ => ∀ α : F.S, F.F α) := ⟨PiExpr.map⟩

def idPi {S : Structure} : PiExpr (StructureDependency.constDep S S) :=
{ map      := id,
  congrArg := toSetoidEquiv S }

def compFunPi {S : Structure} {F : StructureDependency} (f : StructureFunctor S F.S) (g : PiExpr F) :
  PiExpr ⟨S, F.F ⊙ f⟩ :=
{ map      := λ α => g (f α),
  congrArg := λ e => g.congrArg (congrArgMap f e) }

def constPiToFun {S T : Structure} (f : PiExpr (StructureDependency.constDep S T)) :
  StructureFunctor S (setoidStructure T) :=
makeToSetoidStructureFunctor f.map f.congrArg

def funToConstPi {S T : Structure} (F : StructureFunctor S (setoidStructure T)) :
  PiExpr (StructureDependency.constDep S T) :=
{ map      := F.map,
  congrArg := congrArgMap F }

def transportPi {S : Structure} {F₁ F₂ : UniverseFunctor S} (φ : F₁ ≃ F₂) :
  PiExpr ⟨S, F₁⟩ → PiExpr ⟨S, F₂⟩ :=
λ f => { map      := λ α => (φ.ext α).toFun (f α),
         congrArg := λ {α β} e => let ⟨⟨l⟩, ⟨r⟩⟩ := φ.nat e;
                                  IsEquivalence.trans (l.ext (f α)) (congrArgMap (φ.ext β).toFun (f.congrArg e)) }

def dependentApplicationFunctor {S T : Structure} {F : UniverseFunctor S}
                                (f : PiExpr ⟨S, incomingFunctorFunctor T ⊙ F⟩) (a : PiExpr ⟨S, F⟩) :
  SetoidStructureFunctor S T :=
makeSetoidStructureFunctor (λ α => (f α).map (a α))
                           (λ {α β} ⟨e⟩ => let ⟨h₁⟩ := f.congrArg e;
                                           let h₂ := a.congrArg e;
                                           let h₃ := StructureFunctor.congrMap h₁ h₂;
                                           let h₄ := congrArgMap (f α) ((congrArgMap F e).leftInv.ext (a α));
                                           ⟨IsEquivalence.trans (IsEquivalence.symm h₄) h₃⟩)

def PiEquiv {F : StructureDependency} (f g : PiExpr F) := DependentEquiv.DependentDependentEquiv PiExpr.map f g

namespace PiEquiv

variable {F : StructureDependency}

def refl  (f     : PiExpr F)                                     : PiEquiv f f :=
DependentEquiv.DependentDependentEquiv.refl  f
def symm  {f g   : PiExpr F} (φ : PiEquiv f g)                   : PiEquiv g f :=
DependentEquiv.DependentDependentEquiv.symm  φ
def trans {f g h : PiExpr F} (φ : PiEquiv f g) (ψ : PiEquiv g h) : PiEquiv f h :=
DependentEquiv.DependentDependentEquiv.trans φ ψ

def piEquiv : GeneralizedRelation (PiExpr F) := DependentEquiv.DependentDependentEquiv.dependentDependentEquiv (H := PiExpr.map)

instance piEquivHasIso : HasIsomorphisms (@piEquiv F) := DependentEquiv.DependentDependentEquiv.dependentDependentEquivHasIso

end PiEquiv

instance piHasStructure (F : StructureDependency) : HasStructure (PiExpr F) := ⟨PiEquiv.piEquiv⟩
def piStructure (F : StructureDependency) : Structure := ⟨PiExpr F⟩

namespace piStructure

instance (F : StructureDependency) : CoeFun (IsType.type (piStructure F)) (λ _ => ∀ α : F.S, F.F α) := ⟨PiExpr.map⟩

-- An independent `PiExpr` is the same as a functor (to a setoid structure).

section constDep

variable (S T : Structure)

def constDepToFun :
  StructureFunctor (piStructure (StructureDependency.constDep S T)) (functorStructure S (setoidStructure T)) :=
{ map     := constPiToFun,
  functor := { FF        := λ e => makeToSetoidStructureFunctorEquiv' e,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ • φ),
                              respectsId     := λ f   => Setoid.refl (id_ f),
                              respectsInv    := λ φ   => Setoid.refl φ⁻¹ } } }

def constDepInvFun :
  StructureFunctor (functorStructure S (setoidStructure T)) (piStructure (StructureDependency.constDep S T)) :=
{ map     := funToConstPi,
  functor := { FF        := λ e => e.ext,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ • φ),
                              respectsId     := λ F   => Setoid.refl (id_ F),
                              respectsInv    := λ φ   => Setoid.refl φ⁻¹ } } }

def constDepEquiv :
  StructureEquiv (piStructure (StructureDependency.constDep S T)) (functorStructure S (setoidStructure T)) :=
{ toFun    := constDepToFun  S T,
  invFun   := constDepInvFun S T,
  leftInv  := ⟨λ f α => IsEquivalence.refl (f α), sorry⟩,
  rightInv := ⟨λ F => sorry, sorry⟩ }

end constDep

-- If we fix the argument, we obtain a functor from `piStructure` to the result type.

variable (F : StructureDependency)

def projFunctor (α : F.S) : StructureFunctor (piStructure F) (strictUniverseFunctor F.F α) :=
{ map     := λ f => f α,
  functor := { FF        := λ φ => φ α,
               isFunctor := { respectsSetoid := λ h   => h α,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ α • φ α),
                              respectsId     := λ f   => Setoid.refl (id_ (f α)),
                              respectsInv    := λ φ   => Setoid.refl (φ α)⁻¹ } } }

end piStructure



-- A Σ expression of structures.

def SigmaExpr (F : StructureDependency) := Σ' α : F.S, IsType.type ((strictUniverseFunctor F.F) α)

instance (F : StructureDependency) (α : F.S) : Setoid (IsType.type ((strictUniverseFunctor F.F) α)) :=
structureToSetoid (F.F α)

-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence `e` between the types such that `congrArgMap F.F e` maps one instance of
-- the type class to the other.

def SigmaEquiv {F : StructureDependency} (s t : SigmaExpr F) :=
Σ' e : s.fst ≃ t.fst, InstanceEquiv (congrArgMap F.F e) s.snd t.snd

namespace SigmaEquiv

variable {F : StructureDependency}

def refl  (s     : SigmaExpr F)                                           : SigmaEquiv s s :=
let h₁ := InstanceEquiv.refl (setoidStructure (F.F s.fst)) s.snd;
let h₂ := Setoid.symm (respectsId   F.F s.fst);
⟨IsEquivalence.refl  s.fst,       InstanceEquiv.congrArg h₂ s.snd s.snd h₁⟩

def symm  {s t   : SigmaExpr F} (φ : SigmaEquiv s t)                      : SigmaEquiv t s :=
let h₁ := InstanceEquiv.symm (congrArgMap F.F φ.fst) s.snd t.snd φ.snd;
let h₂ := Setoid.symm (respectsInv  F.F φ.fst);
⟨IsEquivalence.symm  φ.fst,       InstanceEquiv.congrArg h₂ t.snd s.snd h₁⟩

def trans {r s t : SigmaExpr F} (φ : SigmaEquiv r s) (ψ : SigmaEquiv s t) : SigmaEquiv r t :=
let h₁ := InstanceEquiv.trans (congrArgMap F.F φ.fst) (congrArgMap F.F ψ.fst) r.snd s.snd t.snd φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp F.F φ.fst ψ.fst);
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

def mkSndFunctor : UniverseFunctor F.S :=
incomingFunctorFunctor (sigmaStructure F) ⊙ F.F

def mkDependency : StructureDependency := ⟨F.S, mkSndFunctor F⟩

def mkExprFunctor (α : F.S) : StructureFunctor (setoidStructure (F.F α)) (sigmaStructure F) :=
{ map     := λ β => ⟨α, β⟩,
  functor := { FF        := λ {β γ} e => ⟨id_ α, InstanceEquiv.congrArg (Setoid.symm (respectsId F.F α)) β γ e⟩,
               isFunctor := { respectsSetoid := λ _   => Setoid.refl _,
                              respectsComp   := λ _ _ => Setoid.symm (leftId _),
                              respectsId     := λ _   => Setoid.refl id',
                              respectsInv    := λ _   => Setoid.symm (idInv _) } } }

theorem mkExprCongrArg {α₁ α₂ : F.S} (e : α₁ ≃ α₂) :
  InstanceEquiv (congrArgMap (mkSndFunctor F) e) (mkExprFunctor F α₁) (mkExprFunctor F α₂) :=
⟨λ β => ⟨e, (congrArgMap F.F e).rightInv.ext β⟩, sorry⟩

def mkExpr : PiExpr (mkDependency F) := ⟨mkExprFunctor F, mkExprCongrArg F⟩

def mkFunctor {S : Structure} (mkFst : StructureFunctor S F.S) (mkSnd : PiExpr ⟨S, F.F ⊙ mkFst⟩) :
  SetoidStructureFunctor S (sigmaStructure F) :=
let f : PiExpr ⟨S, mkSndFunctor F ⊙ mkFst⟩ := compFunPi (F := mkDependency F) mkFst (mkExpr F);
dependentApplicationFunctor f mkSnd

def projFstFunctor : StructureFunctor (sigmaStructure F) F.S :=
{ map     := PSigma.fst,
  functor := { FF        := PSigma.fst,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ e f => Setoid.refl (f • e),
                              respectsId     := λ α   => Setoid.refl (id_ α),
                              respectsInv    := λ e   => Setoid.refl e⁻¹ } } }

def projSndDependencyFunctor : UniverseFunctor (sigmaStructure F) :=
F.F ⊙ projFstFunctor F

def projSndDependency : StructureDependency := ⟨sigmaStructure F, projSndDependencyFunctor F⟩

def projSndExpr : PiExpr (projSndDependency F) := ⟨PSigma.snd, PSigma.snd⟩

-- TODO: Define product structures, and show that a sigma structure with `constDep` is the same as a binary product.

end sigmaStructure



-- Since `StructureDependency` is just a sigma type, we can retroactively define it as a structure.

-- TODO: This would be nice, but it doesn't quite work in the setoid variant: `dependencyFunctor` is the
-- same as `incomingFunctorFunctor universeStructure` except for the setoid coercion. That means we
-- cannot declare `dependencyFunctor` the way we want, and if we use `incomingFunctorFunctor`, it no
-- longer matches `StructureDependency`.

-- def dependencyFunctor : UniverseFunctor universeStructure :=
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
-- def piFunctor    : UniverseFunctor dependencyStructure :=
-- { map     := piStructure,
--   functor := sorry }
-- 
-- def sigmaFunctor : UniverseFunctor dependencyStructure :=
-- { map     := sigmaStructure,
--   functor := sorry }
-- 
-- def piDependency    : StructureDependency := ⟨dependencyStructure, piFunctor⟩
-- def sigmaDependency : StructureDependency := ⟨dependencyStructure, sigmaFunctor⟩



-- We have the familiar equivalences between dependent structures.
-- TODO: Could these become part of a general definition of the word "canonical"?

namespace PiSigmaEquivalences

section InnerPair

variable (F : StructureDependency)

def sndStructure (α : F.S) := setoidStructure (F.F α)

-- `x ↦ ⟨α, x⟩`
def innerPairFunctor (α : F.S) : StructureFunctor (sndStructure F α) (sigmaStructure F) :=
sigmaStructure.mkExprFunctor F α

end InnerPair

def NestedDependency := Σ' F : StructureDependency, UniverseFunctor (sigmaStructure F)

variable (F : NestedDependency)

def innerPairDependency : StructureDependency := ⟨sigmaStructure F.fst, F.snd⟩

-- `x ↦ F.snd ⟨α, x⟩`
def resultFunctor (α : F.fst.S) : UniverseFunctor (sndStructure F.fst α) :=
F.snd ⊙ innerPairFunctor F.fst α

-- `∀ x : F.fst.F α, F.snd ⟨α, x⟩`
-- TODO: Directly construct this as a functor from `F.fst.S` into the dependency.
-- (Requires solving the setoid problem above.)
-- Then prove that a functor into the dependency turns `piStructure` into a functor as well.
@[reducible] def dependentPiStructure (α : F.fst.S) := piStructure ⟨sndStructure F.fst α, resultFunctor F α⟩

def dependentPiFunctorToFunResultFun {α β : F.fst.S} (e : α ≃ β) (y : sndStructure F.fst β) :=
let x := (congrArgMap F.fst.F e).invFun y;
let se : SigmaEquiv ⟨α, x⟩ ⟨β, y⟩ := ⟨e, (congrArgMap F.fst.F e).rightInv.ext y⟩;
let re := congrArgMap F.snd se;
re.toFun

def dependentPiFunctorToFunMap' {α β : F.fst.S} (e : α ≃ β) (f : dependentPiStructure F α) (y : sndStructure F.fst β) :
  resultFunctor F β y :=
let x := (congrArgMap F.fst.F e).invFun y;
dependentPiFunctorToFunResultFun F e y (f x)

def dependentPiFunctorToFunMap {α β : F.fst.S} (e : α ≃ β) (f : dependentPiStructure F α) :
  dependentPiStructure F β :=
⟨dependentPiFunctorToFunMap' F e f, sorry⟩

theorem dependentPiFunctorToFunCongrArg {α β : F.fst.S} (e : α ≃ β) {f₁ f₂ : dependentPiStructure F α} (h : f₁ ≈ f₂) :
  dependentPiFunctorToFunMap F e f₁ ≈ dependentPiFunctorToFunMap F e f₂ :=
let ⟨eh⟩ := h;
⟨λ y => congrArgMap (dependentPiFunctorToFunResultFun F e y) (eh ((congrArgMap F.fst.F e).invFun y))⟩

def dependentPiFunctorToFun {α β : F.fst.S} (e : α ≃ β) :
  SetoidStructureFunctor (dependentPiStructure F α) (dependentPiStructure F β) :=
makeSetoidStructureFunctor (dependentPiFunctorToFunMap F e) (dependentPiFunctorToFunCongrArg F e)

-- TODO: Instead of proving this by hand here, we should expand and use general infrastructure such as
-- `dependentApplicationFunctor`.

theorem dependentPiFunctorRespectsComp {α β γ : F.fst.S} (e₁ : α ≃ β) (e₂ : β ≃ γ) (f : dependentPiStructure F α) :
  dependentPiFunctorToFun F (e₂ • e₁) f ≈ dependentPiFunctorToFun F e₂ (dependentPiFunctorToFun F e₁ f) :=
⟨⟨λ z => let lx := (congrArgMap F.fst.F (e₂ • e₁)).invFun z;
         let lse : SigmaEquiv ⟨α, lx⟩ ⟨γ, z⟩ := ⟨e₂ • e₁, (congrArgMap F.fst.F (e₂ • e₁)).rightInv.ext z⟩;
         let lre := congrArgMap F.snd lse;
         let ry := (congrArgMap F.fst.F e₂).invFun z;
         let rse₂ : SigmaEquiv ⟨β, ry⟩ ⟨γ, z⟩ := ⟨e₂, (congrArgMap F.fst.F e₂).rightInv.ext z⟩;
         let rre₂ := congrArgMap F.snd rse₂;
         let rx := (congrArgMap F.fst.F e₁).invFun ry;
         let rse₁ : SigmaEquiv ⟨α, rx⟩ ⟨β, ry⟩ := ⟨e₁, (congrArgMap F.fst.F e₁).rightInv.ext ry⟩;
         let rre₁ := congrArgMap F.snd rse₁;
         let h₁ : lx ≃ rx := sorry;
         let h₂ := f.congrArg h₁;
         let h : lre.toFun (f lx) ≃ rre₂.toFun (rre₁.toFun (f rx)) := sorry;
         h⟩⟩

def dependentPiFunctorDesc : UniverseFunctorDesc F.fst.S :=
{ map            := dependentPiStructure F,
  toFun          := dependentPiFunctorToFun F,
  respectsSetoid := λ h     f => ⟨sorry⟩,
  respectsComp   := dependentPiFunctorRespectsComp F,
  respectsId     := λ α     f => ⟨sorry⟩ }

-- `α ↦ ∀ x : F.fst.F α, F.snd ⟨α, x⟩`
def dependentPiFunctor : UniverseFunctor F.fst.S := UniverseFunctorDesc.functor (dependentPiFunctorDesc F)

-- `Σ x : F.fst.F α, F.snd ⟨α, x⟩`
def dependentSigmaStructure (α : F.fst.S) := sigmaStructure ⟨sndStructure F.fst α, resultFunctor F α⟩

def dependentSigmaFunctorDesc : UniverseFunctorDesc F.fst.S :=
{ map            := dependentSigmaStructure F,
  toFun          := sorry,
  respectsSetoid := sorry,
  respectsComp   := sorry,
  respectsId     := sorry }

-- `α ↦ Σ x : F.fst.F α, F.snd ⟨α, x⟩`
def dependentSigmaFunctor : UniverseFunctor F.fst.S := UniverseFunctorDesc.functor (dependentSigmaFunctorDesc F)

-- `(∀ x : α, ∀ y : F x, G x y) ≃ (∀ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`(λ x y => g x y) ↦ (λ ⟨x, y⟩ => g x y)`)

def nestedPiDependency : StructureDependency := ⟨F.fst.S, dependentPiFunctor F⟩

@[reducible] def piPiCurried   := piStructure (nestedPiDependency  F)
@[reducible] def piPiUncurried := piStructure (innerPairDependency F)

def piPiEquivToFun  : StructureFunctor (piPiCurried   F) (piPiUncurried F) :=
{ map     := λ g => ⟨λ ⟨α, x⟩ => (g α).map x, sorry⟩,
  functor := sorry }

def piPiEquivInvFun : StructureFunctor (piPiUncurried F) (piPiCurried   F) :=
{ map     := λ g => ⟨λ α => ⟨λ x => g ⟨α, x⟩, sorry⟩, sorry⟩,
  functor := sorry }

def piPiEquiv : StructureEquiv (piPiCurried F) (piPiUncurried F) :=
{ toFun    := piPiEquivToFun  F,
  invFun   := piPiEquivInvFun F,
  leftInv  := sorry,
  rightInv := sorry }

-- `(Σ x : α, Σ y : F x, G x y) ≃ (Σ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`⟨x, ⟨y, z⟩⟩ ↦ ⟨⟨x, y⟩, z⟩`)

def nestedSigmaDependency : StructureDependency := ⟨F.fst.S, dependentSigmaFunctor F⟩

def sigmaSigmaCurried   := sigmaStructure (nestedSigmaDependency F)
def sigmaSigmaUncurried := sigmaStructure (innerPairDependency   F)

def sigmaSigmaEquivToFun  : StructureFunctor (sigmaSigmaCurried   F) (sigmaSigmaUncurried F) :=
{ map     := λ ⟨α, ⟨x, y⟩⟩ => ⟨⟨α, x⟩, y⟩,
  functor := { FF        := λ ⟨e, h⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquivInvFun : StructureFunctor (sigmaSigmaUncurried F) (sigmaSigmaCurried   F) :=
{ map     := λ ⟨⟨α, x⟩, y⟩ => ⟨α, ⟨x, y⟩⟩,
  functor := { FF        := λ ⟨⟨e, f⟩, g⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquiv : StructureEquiv (sigmaSigmaCurried F) (sigmaSigmaUncurried F) :=
{ toFun    := sigmaSigmaEquivToFun  F,
  invFun   := sigmaSigmaEquivInvFun F,
  leftInv  := sorry,
  rightInv := sorry }

-- `(∀ x : α, Σ y : F x, G x y) ≃ (Σ f : (∀ x : α, F x), ∀ x : α, G x (f x))`
-- (`(λ x => ⟨y, f x⟩ ↦ ⟨λ x => y, λ x => f x⟩`)

-- TODO

end PiSigmaEquivalences

end PiSigma
