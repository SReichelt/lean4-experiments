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

def StructureDependency := Σ' S : Structure, UniverseFunctor S

namespace StructureDependency

def constDep (S T : Structure) : StructureDependency := ⟨S, constFun T⟩

end StructureDependency



-- A Π expression of structures.

@[reducible] def RawPiExpr (F : StructureDependency) := DependentStructure F.snd.map

-- A structure that represents a functorial version of the type `∀ α : F.fst, F.snd α`.
-- Since `F` is a functor, `e : α ≃ β` induces an `e' : F.snd α ≃ F.snd β`. We then require an
-- `f : PiExpr F` to produce an instance equivalence between `f.map α : F.snd α` and
-- `f.map β : F.snd β`.
-- As a special case, if `F.snd` is constant, this ensures that `f` is a functor.

structure PiExpr (F : StructureDependency) where
(map                                   : RawPiExpr F)
(congrArgMap {α β : F.fst} (e : α ≃ β) : InstanceEquiv (congrArgMap F.snd e) (map α) (map β))

instance (F : StructureDependency) : CoeFun (PiExpr F) (λ f => ∀ α : F.fst, F.snd α) := ⟨PiExpr.map⟩

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

namespace piStructure

-- A `PiExpr` with no actual dependency is just a functor.

def constDepEquiv (S T : Structure) :
  StructureEquiv (piStructure (StructureDependency.constDep S T)) (functorStructure S (setoidStructure T)) :=
sorry

variable (F : StructureDependency)

-- Every individual projection of `piStructure` is a functor.

def projFunctor (α : F.fst) : StructureFunctor (piStructure F) (F.snd α) :=
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

def mkSndFunctor : UniverseFunctor F.fst :=
compFun F.snd (incomingFunctorFunctor (sigmaStructure F))

def mkDependency : StructureDependency := ⟨F.fst, mkSndFunctor F⟩

def mkExprFunctor (α : F.fst) : StructureFunctor (setoidStructure (F.snd α)) (sigmaStructure F) :=
{ map     := λ β => ⟨α, β⟩,
  functor := { FF        := λ {β γ} e => ⟨id_ α, InstanceEquiv.congrArg (Setoid.symm (respectsId F.snd α)) β γ e⟩,
               isFunctor := { respectsSetoid := λ _   => Setoid.refl _,
                              respectsComp   := λ _ _ => Setoid.symm (leftId _),
                              respectsId     := λ _   => Setoid.refl id',
                              respectsInv    := λ _   => Setoid.symm (idInv _) } } }

def mkExpr : PiExpr (mkDependency F) := ⟨mkExprFunctor F, sorry⟩

def projFstFunctor : StructureFunctor (sigmaStructure F) F.fst :=
{ map     := PSigma.fst,
  functor := { FF        := PSigma.fst,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ e f => Setoid.refl (f • e),
                              respectsId     := λ α   => Setoid.refl (id_ α),
                              respectsInv    := λ e   => Setoid.refl e⁻¹ } } }

def projSndDependencyFunctor : UniverseFunctor (sigmaStructure F) :=
compFun (projFstFunctor F) F.snd

def projSndDependency : StructureDependency := ⟨sigmaStructure F, projSndDependencyFunctor F⟩

def projSndExpr : PiExpr (projSndDependency F) := ⟨PSigma.snd, sorry⟩

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

variable (F : StructureDependency)

def innerPairStructure := setoidStructure (sigmaStructure F)

@[reducible] def PairToUniverseFunctor := UniverseFunctor (innerPairStructure F)

def sndStructure (α : F.fst) := setoidStructure (F.snd α)

-- x ↦ ⟨α, x⟩
def innerPairFunctor (α : F.fst) : StructureFunctor (sndStructure F α) (innerPairStructure F) :=
compFun (sigmaStructure.mkExprFunctor F α) (toSetoidFunctor (sigmaStructure F))

-- TODO: Use currying instead.
-- Maybe first prove that currying works, which should also be useful in proofs below.
variable (G : PairToUniverseFunctor F)

def innerPairDependency : StructureDependency := ⟨innerPairStructure F, G⟩

-- x ↦ G ⟨α, x⟩
def resultFunctor (α : F.fst) : UniverseFunctor (sndStructure F α) :=
compFun (innerPairFunctor F α) G

-- ∀ x : F.snd α, G ⟨α, x⟩
def dependentPiStructure (α : F.fst) := piStructure ⟨sndStructure F α, resultFunctor F G α⟩

def dependentPiFunctorToFunResultFun {α β : F.fst} (e : α ≃ β) (y : sndStructure F β) :=
let x := (congrArgMap F.snd e).invFun y;
let se : SigmaEquiv ⟨α, x⟩ ⟨β, y⟩ := ⟨e, (congrArgMap F.snd e).rightInv y⟩;
let re := congrArgMap G (toSetoidEquiv (sigmaStructure F) se);
re.toFun

def dependentPiFunctorToFunMap' {α β : F.fst} (e : α ≃ β) (f : dependentPiStructure F G α) (y : sndStructure F β) :
  resultFunctor F G β y :=
let x := (congrArgMap F.snd e).invFun y;
dependentPiFunctorToFunResultFun F G e y (f.map x)

def dependentPiFunctorToFunMap {α β : F.fst} (e : α ≃ β) (f : dependentPiStructure F G α) :
  dependentPiStructure F G β :=
⟨dependentPiFunctorToFunMap' F G e f, sorry⟩

theorem dependentPiFunctorToFunCongrArg {α β : F.fst} (e : α ≃ β) {f₁ f₂ : dependentPiStructure F G α} (h : f₁ ≈ f₂) :
  dependentPiFunctorToFunMap F G e f₁ ≈ dependentPiFunctorToFunMap F G e f₂ :=
let ⟨eh⟩ := h;
-- We need choice here to work around the limitation that `congrArgMap G` returns setoid functors.
-- With an inductive definition of `Structure`, it would disappear.
⟨λ y => Classical.choice (congrArgMap (dependentPiFunctorToFunResultFun F G e y) (toSetoidEquiv _ (eh ((congrArgMap F.snd e).invFun y))))⟩

def dependentPiFunctorToFun {α β : F.fst} (e : α ≃ β) :
  SetoidStructureFunctor (dependentPiStructure F G α) (dependentPiStructure F G β) :=
makeSetoidStructureFunctor (dependentPiFunctorToFunMap F G e) (dependentPiFunctorToFunCongrArg F G e)

theorem dependentPiFunctorRespectsComp {α β γ : F.fst} (e₁ : α ≃ β) (e₂ : β ≃ γ) (f : dependentPiStructure F G α) :
  dependentPiFunctorToFun F G (e₂ • e₁) f ≈ dependentPiFunctorToFun F G e₂ (dependentPiFunctorToFun F G e₁ f) :=
⟨⟨λ z => let lx := (congrArgMap F.snd (e₂ • e₁)).invFun z;
         let lse : SigmaEquiv ⟨α, lx⟩ ⟨γ, z⟩ := ⟨e₂ • e₁, (congrArgMap F.snd (e₂ • e₁)).rightInv z⟩;
         let lre := congrArgMap G (toSetoidEquiv (sigmaStructure F) lse);
         let ry := (congrArgMap F.snd e₂).invFun z;
         let rse₂ : SigmaEquiv ⟨β, ry⟩ ⟨γ, z⟩ := ⟨e₂, (congrArgMap F.snd e₂).rightInv z⟩;
         let rre₂ := congrArgMap G (toSetoidEquiv (sigmaStructure F) rse₂);
         let rx := (congrArgMap F.snd e₁).invFun ry;
         let rse₁ : SigmaEquiv ⟨α, rx⟩ ⟨β, ry⟩ := ⟨e₁, (congrArgMap F.snd e₁).rightInv ry⟩;
         let rre₁ := congrArgMap G (toSetoidEquiv (sigmaStructure F) rse₁);
         let h₁ : lx ≃ rx := sorry;
         let h₂ := f.congrArgMap h₁;
         let h : lre.toFun (f.map lx) ≃ rre₂.toFun (rre₁.toFun (f.map rx)) := sorry;
         Classical.choice h⟩⟩

def dependentPiFunctorDesc : UniverseFunctorDesc F.fst :=
{ map            := dependentPiStructure F G,
  toFun          := dependentPiFunctorToFun F G,
  respectsSetoid := λ h     f => ⟨sorry⟩,
  respectsComp   := dependentPiFunctorRespectsComp F G,
  respectsId     := λ α     f => ⟨sorry⟩ }

-- α ↦ ∀ x : F.snd α, G ⟨α, x⟩
def dependentPiFunctor : UniverseFunctor F.fst := UniverseFunctorDesc.functor (dependentPiFunctorDesc F G)

-- Σ x : F.snd α, G ⟨α, x⟩
def dependentSigmaStructure (α : F.fst) := sigmaStructure ⟨sndStructure F α, resultFunctor F G α⟩

def dependentSigmaFunctorDesc : UniverseFunctorDesc F.fst :=
{ map            := dependentSigmaStructure F G,
  toFun          := sorry,
  respectsSetoid := sorry,
  respectsComp   := sorry,
  respectsId     := sorry }

-- α ↦ Σ x : F.snd α, G ⟨α, x⟩
def dependentSigmaFunctor : UniverseFunctor F.fst := UniverseFunctorDesc.functor (dependentSigmaFunctorDesc F G)

-- `(∀ x : α, ∀ y : F x, G x y) ≃ (∀ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`(λ x y => g x y) ↦ (λ ⟨x, y⟩ => g x y)`)

def nestedPiDependency : StructureDependency := ⟨F.fst, dependentPiFunctor F G⟩

def piPiCurried   := piStructure (nestedPiDependency  F G)
def piPiUncurried := piStructure (innerPairDependency F G)

def piPiEquivToFun  : StructureFunctor (piPiCurried   F G) (piPiUncurried F G) :=
{ map     := λ g => ⟨λ ⟨α, x⟩ => (g.map α).map x, sorry⟩,
  functor := sorry }

def piPiEquivInvFun : StructureFunctor (piPiUncurried F G) (piPiCurried   F G) :=
{ map     := λ g => ⟨λ α => ⟨λ x => g.map ⟨α, x⟩, sorry⟩, sorry⟩,
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
{ map     := λ ⟨α, ⟨x, y⟩⟩ => ⟨⟨α, x⟩, y⟩,
  functor := { FF        := λ ⟨e, f⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquivInvFun : StructureFunctor (sigmaSigmaUncurried F G) (sigmaSigmaCurried   F G) :=
{ map     := λ ⟨⟨α, x⟩, y⟩ => ⟨α, ⟨x, y⟩⟩,
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
