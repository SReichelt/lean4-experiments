-- As a prerequisite for `AbstractBuildingBlocks.lean`, here we define generalized versions of Π and Σ
-- expressions, where all involved types are replaced by structures and all dependencies are functors.



import Structure.Basic
import Structure.Forgetfulness
import Structure.UniverseFunctor
import Structure.FunctorStructure

open Morphisms
open HasStructure
open Structure
open DependentStructure
open StructureFunctor
open Forgetfulness
open SetoidStructureFunctor
open FunctorStructure



set_option autoBoundImplicitLocal false

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
(φ : F.S ≃ G.S)
-- TODO: Why does `≃` not work here? There is some strange type class resolution issue with the `universeFunctor` argument at play.
(ψ : FunctorEquiv F.F (G.F ⊙ φ.toFun))

namespace StructureDependencyEquiv

def refl  (F     : StructureDependency)                                                                       : StructureDependencyEquiv F F :=
⟨StructureEquiv.refl  F.S,     FunctorEquiv.symm (idFun.rightId F.F)⟩

def symm  {F G   : StructureDependency} (e : StructureDependencyEquiv F G)                                    : StructureDependencyEquiv G F :=
let e₁ := FunctorEquiv.trans (compFun.congrArgLeft (F := e.φ.invFun) e.ψ) (compFun.congrArgRight (G := G.F) e.φ.isInv.rightInv);
let e₂ := FunctorEquiv.trans e₁ (idFun.rightId G.F);
⟨StructureEquiv.symm  e.φ,     FunctorEquiv.symm e₂⟩

def trans {F G H : StructureDependency} (e : StructureDependencyEquiv F G) (f : StructureDependencyEquiv G H) : StructureDependencyEquiv F H :=
⟨StructureEquiv.trans e.φ f.φ, FunctorEquiv.trans e.ψ (compFun.congrArgLeft (F := e.φ.toFun) f.ψ)⟩

def StructureDependencyEquivEquiv {F G : StructureDependency} (e f : StructureDependencyEquiv F G) :=
∃ χ : e.φ ≃ f.φ, compFun.congrArgRight (G := G.F) χ.toFunEquiv • e.ψ ≈ f.ψ

namespace StructureDependencyEquivEquiv

variable {F G : StructureDependency}

theorem refl  (e     : StructureDependencyEquiv F G)                                                                                 : StructureDependencyEquivEquiv e e :=
⟨StructureEquiv.EquivEquiv.refl  e.φ,
 leftCancelId (compFun.congrArgRight.respectsId e.φ.toFun)⟩

theorem symm  {e f   : StructureDependencyEquiv F G} (φ : StructureDependencyEquivEquiv e f)                                         : StructureDependencyEquivEquiv f e :=
let ⟨χ, hχ⟩ := φ;
let h₁ := (leftMulInv (h := functorHasStructure) e.ψ f.ψ (compFun.congrArgRight χ.toFunEquiv)).mp hχ;
let h₂ := compFun.congrArgRight.respectsInv χ.toFunEquiv;
⟨StructureEquiv.EquivEquiv.symm  χ,
 substCompLeft h₂ (Setoid.symm h₁)⟩

theorem trans {e f g : StructureDependencyEquiv F G} (φ : StructureDependencyEquivEquiv e f) (ψ : StructureDependencyEquivEquiv f g) : StructureDependencyEquivEquiv e g :=
let ⟨χ, hχ⟩ := φ;
let ⟨ξ, hξ⟩ := ψ;
let h₁ := applyAssocLeft (substCompRight hχ hξ);
let h₂ := compFun.congrArgRight.respectsComp χ.toFunEquiv ξ.toFunEquiv;
⟨StructureEquiv.EquivEquiv.trans χ ξ,
 substCompLeft h₂ h₁⟩

instance structureDependencyEquivSetoid : Setoid (StructureDependencyEquiv F G) := ⟨StructureDependencyEquivEquiv, ⟨refl, symm, trans⟩⟩

end StructureDependencyEquivEquiv

def structureDependencyEquiv (F G : StructureDependency) : BundledSetoid := ⟨StructureDependencyEquiv F G⟩

instance structureDependencyEquivHasIso : HasIsomorphisms structureDependencyEquiv :=
{ comp         := trans,
  congrArgComp := λ hφ hψ => sorry,
  assoc        := λ φ ψ χ => sorry,
  id           := refl,
  leftId       := λ φ     => sorry,
  rightId      := λ φ     => sorry,
  inv          := symm,
  congrArgInv  := λ hφ    => sorry,
  leftInv      := λ φ     => sorry,
  rightInv     := λ φ     => sorry,
  invInv       := λ φ     => sorry,
  compInv      := λ φ ψ   => sorry,
  idInv        := λ s     => sorry }

end StructureDependencyEquiv

instance structureDependencyHasStructure : HasStructure StructureDependency := ⟨StructureDependencyEquiv.structureDependencyEquiv⟩
def structureDependencyStructure : Structure := ⟨StructureDependency⟩

end StructureDependency

open StructureDependency



-- A structure that represents a functorial version of the type `∀ a : F.S, F.F a`.
--
-- Since `F` is a functor, `e : a ≃ b` induces an `e' : F.F a ≃ F.F b`. We then require an
-- `f : PiExpr F` to produce an instance equivalence between `f a : F.F a` and `f b : F.F b`.
-- As a special case, if `F.F` is constant, this ensures that `f` is a functor.
--
-- Since equivalence of equivalences in `F.S` is just a proposition, we cannot meaningfully compare
-- two results of `mapEquiv` even if the inputs are equivalent. Therefore, we truncate the resulting
-- equivalences to setoids so that no such comparison is necessary.

structure PiExpr (F : StructureDependency) where
(map                              : DependentStructure (setoidStructure ∘ F.F.map))
(mapEquiv {a b : F.S} (e : a ≃ b) : map a ≈[congrArgMap F.F e] map b)

instance (F : StructureDependency) : CoeFun (PiExpr F) (λ _ => ∀ a : F.S, F.F a) := ⟨PiExpr.map⟩

def idPi {S : Structure} : PiExpr (StructureDependency.constDep S S) :=
{ map      := id,
  mapEquiv := toSetoidEquiv S }

def compFunPi {S : Structure} {F : StructureDependency} (f : StructureFunctor S F.S) (g : PiExpr F) :
  PiExpr ⟨S, F.F ⊙ f⟩ :=
{ map      := λ a => g (f a),
  mapEquiv := λ e => g.mapEquiv (congrArgMap f e) }

def constPiToFun {S T : Structure} (f : PiExpr (StructureDependency.constDep S T)) :
  StructureFunctor S (setoidStructure T) :=
makeToSetoidStructureFunctor f.map f.mapEquiv

def funToConstPi {S T : Structure} (F : StructureFunctor S (setoidStructure T)) :
  PiExpr (StructureDependency.constDep S T) :=
{ map      := F.map,
  mapEquiv := congrArgMap F }

def transportPi {S : Structure} {F₁ F₂ : UniverseFunctor S} (φ : FunctorEquiv F₁ F₂) :
  PiExpr ⟨S, F₁⟩ → PiExpr ⟨S, F₂⟩ :=
λ f => { map      := λ a => (φ.ext a).toFun (f a),
         mapEquiv := λ {a b} e => let ⟨n⟩ := φ.nat e;
                                  let ⟨m⟩ := f.mapEquiv e;
                                  ⟨IsEquivalence.trans (n.toFunEquiv.ext (f a)) (congrArgMap (φ.ext b).toFun m)⟩ }

def dependentApplicationFunctor {S T : Structure} {F : UniverseFunctor S}
                                (f : PiExpr ⟨S, incomingFunctorFunctor T ⊙ F⟩)
                                (x : PiExpr ⟨S, F⟩) :
  SetoidStructureFunctor S T :=
makeSetoidStructureFunctor (λ a => (f a).map (x a))
                           (λ {a b} ⟨e⟩ => let ⟨h₁⟩ := f.mapEquiv e;
                                           let ⟨h₂⟩ := x.mapEquiv e;
                                           let h₃ := StructureFunctor.congrMap h₁ h₂;
                                           let h₄ := congrArgMap (f a) ((congrArgMap F e).isInv.leftInv.ext (x a));
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

instance (F : StructureDependency) : CoeFun (IsType.type (piStructure F)) (λ _ => ∀ a : F.S, F.F a) := ⟨PiExpr.map⟩

-- An independent `PiExpr` is the same as a functor (to a setoid structure).

section constDep

variable (S T : Structure)

def constDepToFun :
  StructureFunctor (piStructure (StructureDependency.constDep S T)) (functorStructure S (setoidStructure T)) :=
{ map     := constPiToFun,
  functor := { mapEquiv  := λ e => makeToSetoidStructureFunctorEquiv' (λ a => e a),
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ • φ),
                              respectsId     := λ f   => Setoid.refl (id__ f),
                              respectsInv    := λ φ   => Setoid.refl φ⁻¹ } } }

def constDepInvFun :
  StructureFunctor (functorStructure S (setoidStructure T)) (piStructure (StructureDependency.constDep S T)) :=
{ map     := funToConstPi,
  functor := { mapEquiv  := λ e => e.ext,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ • φ),
                              respectsId     := λ F   => Setoid.refl (id__ F),
                              respectsInv    := λ φ   => Setoid.refl φ⁻¹ } } }

def constDepEquiv :
  StructureEquiv (piStructure (StructureDependency.constDep S T)) (functorStructure S (setoidStructure T)) :=
{ toFun    := constDepToFun  S T,
  invFun   := constDepInvFun S T,
  isInv  := { leftInv  := { ext := λ f a => IsEquivalence.refl (f a),
                            nat := λ _ _ => proofIrrel _ _ },
              rightInv := { ext := λ F => makeToSetoidStructureFunctorEquiv' (λ a => IsEquivalence.refl (F a)),
                            nat := λ _ _ => proofIrrel _ _ },
              lrCompat := λ _ _ => proofIrrel _ _,
              rlCompat := λ _ _ => proofIrrel _ _ } }

end constDep

-- If we fix the argument, we obtain a functor from `piStructure` to the result type.

variable (F : StructureDependency)

def projFunctor (a : F.S) : StructureFunctor (piStructure F) (setoidStructure (F.F a)) :=
{ map     := λ f => f a,
  functor := { mapEquiv  := λ φ => φ a,
               isFunctor := { respectsSetoid := λ h   => h a,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ a • φ a),
                              respectsId     := λ f   => Setoid.refl (id_ (f a)),
                              respectsInv    := λ φ   => Setoid.refl (φ a)⁻¹ } } }

end piStructure



-- A Σ expression of structures.

def SigmaExpr (F : StructureDependency) := Σ' a : F.S, IsType.type (F.F a)

-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence `e` between the types such that `congrArgMap F.F e` maps one
-- instance of the type class to the other.

def SigmaEquiv {F : StructureDependency} (s t : SigmaExpr F) :=
Σ' e : s.fst ≃ t.fst, s.snd ≈[congrArgMap F.F e] t.snd

namespace SigmaEquiv

variable {F : StructureDependency}

def refl  (s     : SigmaExpr F)                                           : SigmaEquiv s s :=
let h₁ := SetoidInstanceEquiv.refl (F.F s.fst) s.snd;
let h₂ := Setoid.symm (respectsId   F.F s.fst);
⟨IsEquivalence.refl  s.fst,       SetoidInstanceEquiv.congrArgEquiv h₂ s.snd s.snd h₁⟩

def symm  {s t   : SigmaExpr F} (φ : SigmaEquiv s t)                      : SigmaEquiv t s :=
let h₁ := SetoidInstanceEquiv.symm (congrArgMap F.F φ.fst) s.snd t.snd φ.snd;
let h₂ := Setoid.symm (respectsInv  F.F φ.fst);
⟨IsEquivalence.symm  φ.fst,       SetoidInstanceEquiv.congrArgEquiv h₂ t.snd s.snd h₁⟩

def trans {r s t : SigmaExpr F} (φ : SigmaEquiv r s) (ψ : SigmaEquiv s t) : SigmaEquiv r t :=
let h₁ := SetoidInstanceEquiv.trans (congrArgMap F.F φ.fst) (congrArgMap F.F ψ.fst) r.snd s.snd t.snd φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp F.F φ.fst ψ.fst);
⟨IsEquivalence.trans φ.fst ψ.fst, SetoidInstanceEquiv.congrArgEquiv h₂ r.snd t.snd h₁⟩

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

def mkExprFunctor (a : F.S) : StructureFunctor (F.F a) (sigmaStructure F) :=
{ map     := λ b => ⟨a, b⟩,
  functor := { mapEquiv  := λ {b c} e => ⟨id_ a, SetoidInstanceEquiv.congrArgEquiv (Setoid.symm (respectsId F.F a)) b c ⟨e⟩⟩,
               isFunctor := { respectsSetoid := λ _   => Setoid.refl _,
                              respectsComp   := λ _ _ => Setoid.symm (leftId _),
                              respectsId     := λ _   => Setoid.refl (id'' (S := sigmaStructure F)),
                              respectsInv    := λ _   => Setoid.symm (idInv _) } } }

theorem mkExprCongrArg {a₁ a₂ : F.S} (e : a₁ ≃ a₂) :
  mkExprFunctor F a₁ ≈[congrArgMap (mkSndFunctor F) e] mkExprFunctor F a₂ :=
⟨{ ext := λ b       => ⟨e, ⟨(congrArgMap F.F e).isInv.rightInv.ext b⟩⟩,
   nat := λ {b c} φ => sorry }⟩

def mkExpr : PiExpr (mkDependency F) := ⟨mkExprFunctor F, mkExprCongrArg F⟩

def mkFunctor {S : Structure} (mkFst : StructureFunctor S F.S) (mkSnd : PiExpr ⟨S, F.F ⊙ mkFst⟩) :
  SetoidStructureFunctor S (sigmaStructure F) :=
let f : PiExpr ⟨S, mkSndFunctor F ⊙ mkFst⟩ := compFunPi (F := mkDependency F) mkFst (mkExpr F);
dependentApplicationFunctor f mkSnd

def projFstFunctor : StructureFunctor (sigmaStructure F) F.S :=
{ map     := PSigma.fst,
  functor := { mapEquiv  := PSigma.fst,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ e f => Setoid.refl (f • e),
                              respectsId     := λ a   => Setoid.refl (id__ a),
                              respectsInv    := λ e   => Setoid.refl e⁻¹ } } }

def projSndDependencyFunctor : UniverseFunctor (sigmaStructure F) :=
F.F ⊙ projFstFunctor F

def projSndDependency : StructureDependency := ⟨sigmaStructure F, projSndDependencyFunctor F⟩

def projSndExpr : PiExpr (projSndDependency F) := ⟨PSigma.snd, PSigma.snd⟩

-- TODO: Show that a sigma structure with `constDep` is the same as a binary product.

end sigmaStructure



-- `piStructure` and `sigmaStructure` themselves can be viewed as dependent structures, depending on an
-- instance of `StructureDependency`.

def piStructureFunctor    : UniverseFunctor structureDependencyStructure :=
{ map     := piStructure,
  functor := sorry }

def sigmaStructureFunctor : UniverseFunctor structureDependencyStructure :=
{ map     := sigmaStructure,
  functor := sorry }

def piStructureDependency    : StructureDependency := ⟨structureDependencyStructure, piStructureFunctor⟩
def sigmaStructureDependency : StructureDependency := ⟨structureDependencyStructure, sigmaStructureFunctor⟩



-- We have the familiar equivalences between dependent structures.
-- TODO: Could these become part of a general definition of the word "canonical"?

namespace PiSigmaEquivalences

section InnerPair

variable (F : StructureDependency)

-- `x ↦ ⟨a, x⟩`
def innerPairFunctor (a : F.S) : StructureFunctor (F.F a) (sigmaStructure F) :=
sigmaStructure.mkExprFunctor F a

end InnerPair

def NestedDependency := Σ' F : StructureDependency, UniverseFunctor (sigmaStructure F)

variable (F : NestedDependency)

def innerPairDependency : StructureDependency := ⟨sigmaStructure F.fst, F.snd⟩

-- `x ↦ F.snd ⟨a, x⟩`
def resultFunctor (a : F.fst.S) : UniverseFunctor (F.fst.F a) :=
F.snd ⊙ innerPairFunctor F.fst a

-- `∀ x : F.fst.F a, F.snd ⟨a, x⟩`
-- TODO: Directly construct this as a functor from `F.fst.S` into the dependency, now that the setoid problem should be solved.
-- Then prove that a functor into the dependency turns `piStructure` into a functor as well.
@[reducible] def dependentPiStructure (a : F.fst.S) := piStructure ⟨F.fst.F a, resultFunctor F a⟩

def dependentPiFunctorToFunResultFun {a b : F.fst.S} (e : a ≃ b) (y : F.fst.F b) :=
let x := (congrArgMap F.fst.F e).invFun y;
let se : SigmaEquiv ⟨a, x⟩ ⟨b, y⟩ := ⟨e, ⟨(congrArgMap F.fst.F e).isInv.rightInv.ext y⟩⟩;
let re := congrArgMap F.snd se;
re.toFun

def dependentPiFunctorToFunMap' {a b : F.fst.S} (e : a ≃ b) (f : dependentPiStructure F a) (y : F.fst.F b) :
  resultFunctor F b y :=
let x := (congrArgMap F.fst.F e).invFun y;
dependentPiFunctorToFunResultFun F e y (f x)

def dependentPiFunctorToFunMap {a b : F.fst.S} (e : a ≃ b) (f : dependentPiStructure F a) :
  dependentPiStructure F b :=
⟨dependentPiFunctorToFunMap' F e f, sorry⟩

theorem dependentPiFunctorToFunCongrArg {a b : F.fst.S} (e : a ≃ b) {f₁ f₂ : dependentPiStructure F a} (h : f₁ ≈ f₂) :
  dependentPiFunctorToFunMap F e f₁ ≈ dependentPiFunctorToFunMap F e f₂ :=
let ⟨eh⟩ := h;
⟨λ y => congrArgMap (setoidFunctor (dependentPiFunctorToFunResultFun F e y)) (eh ((congrArgMap F.fst.F e).invFun y))⟩

def dependentPiFunctorToFun {a b : F.fst.S} (e : a ≃ b) :
  SetoidStructureFunctor (dependentPiStructure F a) (dependentPiStructure F b) :=
makeSetoidStructureFunctor (dependentPiFunctorToFunMap F e) (dependentPiFunctorToFunCongrArg F e)

-- TODO: Instead of proving this by hand here, we should expand and use general infrastructure such as
-- `dependentApplicationFunctor`.

theorem dependentPiFunctorRespectsComp {a b c : F.fst.S} (e₁ : a ≃ b) (e₂ : b ≃ c) (f : dependentPiStructure F a) :
  dependentPiFunctorToFun F (e₂ • e₁) f ≈ dependentPiFunctorToFun F e₂ (dependentPiFunctorToFun F e₁ f) :=
⟨⟨λ z => let lx := (congrArgMap F.fst.F (e₂ • e₁)).invFun z;
         let lse : SigmaEquiv ⟨a, lx⟩ ⟨c, z⟩ := ⟨e₂ • e₁, ⟨(congrArgMap F.fst.F (e₂ • e₁)).isInv.rightInv.ext z⟩⟩;
         let lre := congrArgMap F.snd lse;
         let ry := (congrArgMap F.fst.F e₂).invFun z;
         let rse₂ : SigmaEquiv ⟨b, ry⟩ ⟨c, z⟩ := ⟨e₂, ⟨(congrArgMap F.fst.F e₂).isInv.rightInv.ext z⟩⟩;
         let rre₂ := congrArgMap F.snd rse₂;
         let rx := (congrArgMap F.fst.F e₁).invFun ry;
         let rse₁ : SigmaEquiv ⟨a, rx⟩ ⟨b, ry⟩ := ⟨e₁, ⟨(congrArgMap F.fst.F e₁).isInv.rightInv.ext ry⟩⟩;
         let rre₁ := congrArgMap F.snd rse₁;
         let h₁ : lx ≃ rx := sorry;
         let h₂ := f.mapEquiv h₁;
         let h : lre.toFun (f lx) ≈ rre₂.toFun (rre₁.toFun (f rx)) := sorry;
         h⟩⟩

def dependentPiFunctorDesc : SetoidUniverseFunctorDesc F.fst.S :=
{ map            := dependentPiStructure F,
  toFun          := dependentPiFunctorToFun F,
  respectsSetoid := λ h     f => ⟨sorry⟩,
  respectsComp   := dependentPiFunctorRespectsComp F,
  respectsId     := λ a     f => ⟨sorry⟩ }

-- `a ↦ ∀ x : F.fst.F a, F.snd ⟨a, x⟩`
def dependentPiFunctor : UniverseFunctor F.fst.S := SetoidUniverseFunctorDesc.universeFunctor (dependentPiFunctorDesc F)

-- `Σ x : F.fst.F a, F.snd ⟨a, x⟩`
def dependentSigmaStructure (a : F.fst.S) := sigmaStructure ⟨F.fst.F a, resultFunctor F a⟩

def dependentSigmaFunctorDesc : SetoidUniverseFunctorDesc F.fst.S :=
{ map            := dependentSigmaStructure F,
  toFun          := sorry,
  respectsSetoid := sorry,
  respectsComp   := sorry,
  respectsId     := sorry }

-- `a ↦ Σ x : F.fst.F a, F.snd ⟨a, x⟩`
def dependentSigmaFunctor : UniverseFunctor F.fst.S := SetoidUniverseFunctorDesc.universeFunctor (dependentSigmaFunctorDesc F)

-- `(∀ x : α, ∀ y : F x, G x y) ≃ (∀ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`(λ x y => g x y) ↦ (λ ⟨x, y⟩ => g x y)`)

def nestedPiDependency : StructureDependency := ⟨F.fst.S, dependentPiFunctor F⟩

@[reducible] def piPiCurried   := piStructure (nestedPiDependency  F)
@[reducible] def piPiUncurried := piStructure (innerPairDependency F)

def piPiEquivToFun  : StructureFunctor (piPiCurried   F) (piPiUncurried F) :=
{ map     := λ g => ⟨λ ⟨a, x⟩ => (g a).map x, sorry⟩,
  functor := sorry }

def piPiEquivInvFun : StructureFunctor (piPiUncurried F) (piPiCurried   F) :=
{ map     := λ g => ⟨λ a => ⟨λ x => g ⟨a, x⟩, sorry⟩, sorry⟩,
  functor := sorry }

def piPiEquiv : StructureEquiv (piPiCurried F) (piPiUncurried F) :=
{ toFun  := piPiEquivToFun  F,
  invFun := piPiEquivInvFun F,
  isInv  := sorry }

-- `(Σ x : α, Σ y : F x, G x y) ≃ (Σ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`⟨x, ⟨y, z⟩⟩ ↦ ⟨⟨x, y⟩, z⟩`)

def nestedSigmaDependency : StructureDependency := ⟨F.fst.S, dependentSigmaFunctor F⟩

def sigmaSigmaCurried   := sigmaStructure (nestedSigmaDependency F)
def sigmaSigmaUncurried := sigmaStructure (innerPairDependency   F)

def sigmaSigmaEquivToFun  : StructureFunctor (sigmaSigmaCurried   F) (sigmaSigmaUncurried F) :=
{ map     := λ ⟨a, ⟨x, y⟩⟩ => ⟨⟨a, x⟩, y⟩,
  functor := { mapEquiv  := λ ⟨e, he⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquivInvFun : StructureFunctor (sigmaSigmaUncurried F) (sigmaSigmaCurried   F) :=
{ map     := λ ⟨⟨a, x⟩, y⟩ => ⟨a, ⟨x, y⟩⟩,
  functor := { mapEquiv  := λ ⟨⟨e, f⟩, g⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquiv : StructureEquiv (sigmaSigmaCurried F) (sigmaSigmaUncurried F) :=
{ toFun  := sigmaSigmaEquivToFun  F,
  invFun := sigmaSigmaEquivInvFun F,
  isInv  := sorry }

-- `(∀ x : α, Σ y : F x, G x y) ≃ (Σ f : (∀ x : α, F x), ∀ x : α, G x (f x))`
-- (`(λ x => ⟨y, f x⟩ ↦ ⟨λ x => y, λ x => f x⟩`)

-- TODO

end PiSigmaEquivalences

end PiSigma
