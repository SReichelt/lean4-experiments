-- As a prerequisite for `AbstractBuildingBlocks.lean`, here we define generalized versions of Π and Σ
-- expressions, where all involved types are replaced by structures and all dependencies are functors.



import Structure.Basic
import Structure.Forgetfulness
import Structure.UniverseFunctor
import Structure.FunctorStructure

open Morphisms
open HasStructure
open Structure
open Pi
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

structure StructureDependencyEquiv (C D : StructureDependency) where
(φ : C.S ≃ D.S)
-- TODO: Why does `≃` not work here? There is some strange type class resolution issue with the `universeFunctor` argument at play.
(ψ : FunctorEquiv C.F (D.F ⊙ φ.toFun))

namespace StructureDependencyEquiv

def refl  (C     : StructureDependency)                                                                       : StructureDependencyEquiv C C :=
⟨StructureEquiv.refl  C.S,     FunctorEquiv.symm (idFun.rightId C.F)⟩

def symm  {C D   : StructureDependency} (e : StructureDependencyEquiv C D)                                    : StructureDependencyEquiv D C :=
let e₁ := FunctorEquiv.trans (compFun.congrArgLeft (F := e.φ.invFun) e.ψ) (compFun.congrArgRight (G := D.F) e.φ.isInv.rightInv);
let e₂ := FunctorEquiv.trans e₁ (idFun.rightId D.F);
⟨StructureEquiv.symm  e.φ,     FunctorEquiv.symm e₂⟩

def trans {C D E : StructureDependency} (e : StructureDependencyEquiv C D) (f : StructureDependencyEquiv D E) : StructureDependencyEquiv C E :=
⟨StructureEquiv.trans e.φ f.φ, FunctorEquiv.trans e.ψ (compFun.congrArgLeft (F := e.φ.toFun) f.ψ)⟩

def StructureDependencyEquivEquiv {C D : StructureDependency} (e f : StructureDependencyEquiv C D) :=
∃ χ : e.φ ≃ f.φ, compFun.congrArgRight (G := D.F) χ.toFunEquiv • e.ψ ≈ f.ψ

namespace StructureDependencyEquivEquiv

variable {C D : StructureDependency}

theorem refl  (e     : StructureDependencyEquiv C D)                                                                                 : StructureDependencyEquivEquiv e e :=
⟨StructureEquiv.EquivEquiv.refl  e.φ,
 leftCancelId (compFun.congrArgRight.respectsId e.φ.toFun)⟩

theorem symm  {e f   : StructureDependencyEquiv C D} (φ : StructureDependencyEquivEquiv e f)                                         : StructureDependencyEquivEquiv f e :=
let ⟨χ, hχ⟩ := φ;
let h₁ := (leftMulInv (h := functorHasStructure) e.ψ f.ψ (compFun.congrArgRight χ.toFunEquiv)).mp hχ;
let h₂ := compFun.congrArgRight.respectsInv χ.toFunEquiv;
⟨StructureEquiv.EquivEquiv.symm  χ,
 substCompLeft h₂ (Setoid.symm h₁)⟩

theorem trans {e f g : StructureDependencyEquiv C D} (φ : StructureDependencyEquivEquiv e f) (ψ : StructureDependencyEquivEquiv f g) : StructureDependencyEquivEquiv e g :=
let ⟨χ, hχ⟩ := φ;
let ⟨ξ, hξ⟩ := ψ;
let h₁ := applyAssocLeft (substCompRight hχ hξ);
let h₂ := compFun.congrArgRight.respectsComp χ.toFunEquiv ξ.toFunEquiv;
⟨StructureEquiv.EquivEquiv.trans χ ξ,
 substCompLeft h₂ h₁⟩

instance structureDependencyEquivSetoid : Setoid (StructureDependencyEquiv C D) := ⟨StructureDependencyEquivEquiv, ⟨refl, symm, trans⟩⟩

end StructureDependencyEquivEquiv

def structureDependencyEquiv (C D : StructureDependency) : BundledSetoid := ⟨StructureDependencyEquiv C D⟩

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



-- A structure that represents a functorial version of the type `∀ a : C.S, C.F a`.
--
-- Since `C.F` is a functor, `e : a ≃ b` induces an `e' : C.F a ≃ C.F b`. We then require an
-- `F : PiExpr C` to produce an instance equivalence between `F a : C.F a` and `F b : C.F b`.
-- As a special case, if `C.F` is constant, this ensures that `F` is a functor.
--
-- Since equivalence of equivalences in `C.S` is just a proposition, we cannot meaningfully compare
-- two results of `mapEquiv` even if the inputs are equivalent. Therefore, we truncate the resulting
-- equivalences to setoids so that no such comparison is necessary.

structure PiExpr (C : StructureDependency) where
(map                              : Pi (setoidStructure ∘ C.F.map))
(mapEquiv {a b : C.S} (e : a ≃ b) : map a ≈[congrArgMap C.F e] map b)

instance (C : StructureDependency) : CoeFun (PiExpr C) (λ _ => ∀ a : C.S, C.F a) := ⟨PiExpr.map⟩

def idPi {S : Structure} : PiExpr (StructureDependency.constDep S S) :=
{ map      := id,
  mapEquiv := toSetoidEquiv S }

def compFunPi {S : Structure} {C : StructureDependency} (F : StructureFunctor S C.S) (G : PiExpr C) :
  PiExpr ⟨S, C.F ⊙ F⟩ :=
{ map      := λ a => G (F a),
  mapEquiv := λ e => G.mapEquiv (congrArgMap F e) }

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

def PiEquiv {C : StructureDependency} (F G : PiExpr C) := Pi.PiEquiv.DependentPiEquiv PiExpr.map F G

namespace PiEquiv

variable {C : StructureDependency}

def refl  (F     : PiExpr C)                                     : PiEquiv F F :=
Pi.PiEquiv.DependentPiEquiv.refl  F
def symm  {F G   : PiExpr C} (φ : PiEquiv F G)                   : PiEquiv G F :=
Pi.PiEquiv.DependentPiEquiv.symm  φ
def trans {F G H : PiExpr C} (φ : PiEquiv F G) (ψ : PiEquiv G H) : PiEquiv F H :=
Pi.PiEquiv.DependentPiEquiv.trans φ ψ

def piEquiv : GeneralizedRelation (PiExpr C) := Pi.PiEquiv.DependentPiEquiv.dependentPiEquiv (z := PiExpr.map)

instance piEquivHasIso : HasIsomorphisms (@piEquiv C) := Pi.PiEquiv.DependentPiEquiv.dependentPiEquivHasIso

end PiEquiv

instance piHasStructure (C : StructureDependency) : HasStructure (PiExpr C) := ⟨PiEquiv.piEquiv⟩
def piStructure (C : StructureDependency) : Structure := ⟨PiExpr C⟩

namespace piStructure

instance (C : StructureDependency) : CoeFun (IsType.type (piStructure C)) (λ _ => ∀ a : C.S, C.F a) := ⟨PiExpr.map⟩

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

variable (C : StructureDependency)

def projFunctor (a : C.S) : StructureFunctor (piStructure C) (setoidStructure (C.F a)) :=
{ map     := λ f => f a,
  functor := { mapEquiv  := λ φ => φ a,
               isFunctor := { respectsSetoid := λ h   => h a,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ a • φ a),
                              respectsId     := λ f   => Setoid.refl (id_ (f a)),
                              respectsInv    := λ φ   => Setoid.refl (φ a)⁻¹ } } }

end piStructure



-- A Σ expression of structures.

def SigmaExpr (C : StructureDependency) := Σ' a : C.S, IsType.type (C.F a)

-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence `e` between the types such that `congrArgMap C.F e` maps one
-- instance of the type class to the other.

def SigmaEquiv {C : StructureDependency} (s t : SigmaExpr C) :=
Σ' e : s.fst ≃ t.fst, s.snd ≈[congrArgMap C.F e] t.snd

namespace SigmaEquiv

variable {C : StructureDependency}

def refl  (s     : SigmaExpr C)                                           : SigmaEquiv s s :=
let h₁ := SetoidInstanceEquiv.refl (C.F s.fst) s.snd;
let h₂ := Setoid.symm (respectsId   C.F s.fst);
⟨IsEquivalence.refl  s.fst,       SetoidInstanceEquiv.congrArgEquiv h₂ s.snd s.snd h₁⟩

def symm  {s t   : SigmaExpr C} (φ : SigmaEquiv s t)                      : SigmaEquiv t s :=
let h₁ := SetoidInstanceEquiv.symm (congrArgMap C.F φ.fst) s.snd t.snd φ.snd;
let h₂ := Setoid.symm (respectsInv  C.F φ.fst);
⟨IsEquivalence.symm  φ.fst,       SetoidInstanceEquiv.congrArgEquiv h₂ t.snd s.snd h₁⟩

def trans {r s t : SigmaExpr C} (φ : SigmaEquiv r s) (ψ : SigmaEquiv s t) : SigmaEquiv r t :=
let h₁ := SetoidInstanceEquiv.trans (congrArgMap C.F φ.fst) (congrArgMap C.F ψ.fst) r.snd s.snd t.snd φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp C.F φ.fst ψ.fst);
⟨IsEquivalence.trans φ.fst ψ.fst, SetoidInstanceEquiv.congrArgEquiv h₂ r.snd t.snd h₁⟩

-- No need to compare `φ.snd` and `ψ.snd` because they are proofs.
def SigmaEquivEquiv {s t : SigmaExpr C} (φ ψ : SigmaEquiv s t) := φ.fst ≈ ψ.fst

namespace SigmaEquivEquiv

variable {s t : SigmaExpr C}

theorem refl  (φ     : SigmaEquiv s t)                                                     : SigmaEquivEquiv φ φ :=
Setoid.refl  φ.fst

theorem symm  {φ ψ   : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ)                           : SigmaEquivEquiv ψ φ :=
Setoid.symm  e

theorem trans {φ ψ χ : SigmaEquiv s t} (e : SigmaEquivEquiv φ ψ) (f : SigmaEquivEquiv ψ χ) : SigmaEquivEquiv φ χ :=
Setoid.trans e f

instance sigmaEquivSetoid : Setoid (SigmaEquiv s t) := ⟨SigmaEquivEquiv, ⟨refl, symm, trans⟩⟩

end SigmaEquivEquiv

def sigmaEquiv (s t : SigmaExpr C) : BundledSetoid := ⟨SigmaEquiv s t⟩

instance sigmaEquivHasIso : HasIsomorphisms (@sigmaEquiv C) :=
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

instance sigmaHasStructure (C : StructureDependency) : HasStructure (SigmaExpr C) := ⟨SigmaEquiv.sigmaEquiv⟩
def sigmaStructure (C : StructureDependency) : Structure := ⟨SigmaExpr C⟩

-- Introduction and projections of `sigmaStructure` are functorial.

namespace sigmaStructure

variable (C : StructureDependency)

def mkSndFunctor : UniverseFunctor C.S :=
incomingFunctorFunctor (sigmaStructure C) ⊙ C.F

def mkDependency : StructureDependency := ⟨C.S, mkSndFunctor C⟩

def mkExprFunctor (a : C.S) : StructureFunctor (C.F a) (sigmaStructure C) :=
{ map     := λ b => ⟨a, b⟩,
  functor := { mapEquiv  := λ {b c} e => ⟨id_ a, SetoidInstanceEquiv.congrArgEquiv (Setoid.symm (respectsId C.F a)) b c ⟨e⟩⟩,
               isFunctor := { respectsSetoid := λ _   => Setoid.refl _,
                              respectsComp   := λ _ _ => Setoid.symm (leftId _),
                              respectsId     := λ _   => Setoid.refl (id'' (S := sigmaStructure C)),
                              respectsInv    := λ _   => Setoid.symm (idInv _) } } }

theorem mkExprCongrArg {a₁ a₂ : C.S} (e : a₁ ≃ a₂) :
  mkExprFunctor C a₁ ≈[congrArgMap (mkSndFunctor C) e] mkExprFunctor C a₂ :=
⟨{ ext := λ b       => ⟨e, ⟨(congrArgMap C.F e).isInv.rightInv.ext b⟩⟩,
   nat := λ {b c} φ => sorry }⟩

def mkExpr : PiExpr (mkDependency C) := ⟨mkExprFunctor C, mkExprCongrArg C⟩

def mkFunctor {S : Structure} (mkFst : StructureFunctor S C.S) (mkSnd : PiExpr ⟨S, C.F ⊙ mkFst⟩) :
  SetoidStructureFunctor S (sigmaStructure C) :=
let F : PiExpr ⟨S, mkSndFunctor C ⊙ mkFst⟩ := compFunPi (C := mkDependency C) mkFst (mkExpr C);
dependentApplicationFunctor F mkSnd

def projFstFunctor : StructureFunctor (sigmaStructure C) C.S :=
{ map     := PSigma.fst,
  functor := { mapEquiv  := PSigma.fst,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ e f => Setoid.refl (f • e),
                              respectsId     := λ a   => Setoid.refl (id__ a),
                              respectsInv    := λ e   => Setoid.refl e⁻¹ } } }

def projSndDependencyFunctor : UniverseFunctor (sigmaStructure C) :=
C.F ⊙ projFstFunctor C

def projSndDependency : StructureDependency := ⟨sigmaStructure C, projSndDependencyFunctor C⟩

def projSndExpr : PiExpr (projSndDependency C) := ⟨PSigma.snd, PSigma.snd⟩

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

variable (C : StructureDependency)

-- `x ↦ ⟨a, x⟩`
def innerPairFunctor (a : C.S) : StructureFunctor (C.F a) (sigmaStructure C) :=
sigmaStructure.mkExprFunctor C a

end InnerPair

def NestedDependency := Σ' C : StructureDependency, UniverseFunctor (sigmaStructure C)

variable (D : NestedDependency)

def innerPairDependency : StructureDependency := ⟨sigmaStructure D.fst, D.snd⟩

-- `x ↦ D.snd ⟨a, x⟩`
def resultFunctor (a : D.fst.S) : UniverseFunctor (D.fst.F a) :=
D.snd ⊙ innerPairFunctor D.fst a

-- `∀ x : D.fst.F a, D.snd ⟨a, x⟩`
-- TODO: Directly construct this as a functor from `D.fst.S` into the dependency, now that the setoid problem should be solved.
-- Then prove that a functor into the dependency turns `piStructure` into a functor as well.
@[reducible] def dependentPiStructure (a : D.fst.S) := piStructure ⟨D.fst.F a, resultFunctor D a⟩

def dependentPiFunctorToFunResultFun {a b : D.fst.S} (e : a ≃ b) (y : D.fst.F b) :=
let x := (congrArgMap D.fst.F e).invFun y;
let se : SigmaEquiv ⟨a, x⟩ ⟨b, y⟩ := ⟨e, ⟨(congrArgMap D.fst.F e).isInv.rightInv.ext y⟩⟩;
let re := congrArgMap D.snd se;
re.toFun

def dependentPiFunctorToFunMap' {a b : D.fst.S} (e : a ≃ b) (f : dependentPiStructure D a) (y : D.fst.F b) :
  resultFunctor D b y :=
let x := (congrArgMap D.fst.F e).invFun y;
dependentPiFunctorToFunResultFun D e y (f x)

def dependentPiFunctorToFunMap {a b : D.fst.S} (e : a ≃ b) (f : dependentPiStructure D a) :
  dependentPiStructure D b :=
⟨dependentPiFunctorToFunMap' D e f, sorry⟩

theorem dependentPiFunctorToFunCongrArg {a b : D.fst.S} (e : a ≃ b) {f₁ f₂ : dependentPiStructure D a} (h : f₁ ≈ f₂) :
  dependentPiFunctorToFunMap D e f₁ ≈ dependentPiFunctorToFunMap D e f₂ :=
let ⟨eh⟩ := h;
⟨λ y => congrArgMap (setoidFunctor (dependentPiFunctorToFunResultFun D e y)) (eh ((congrArgMap D.fst.F e).invFun y))⟩

def dependentPiFunctorToFun {a b : D.fst.S} (e : a ≃ b) :
  SetoidStructureFunctor (dependentPiStructure D a) (dependentPiStructure D b) :=
makeSetoidStructureFunctor (dependentPiFunctorToFunMap D e) (dependentPiFunctorToFunCongrArg D e)

-- TODO: Instead of proving this by hand here, we should expand and use general infrastructure such as
-- `dependentApplicationFunctor`.

theorem dependentPiFunctorRespectsComp {a b c : D.fst.S} (e₁ : a ≃ b) (e₂ : b ≃ c) (f : dependentPiStructure D a) :
  dependentPiFunctorToFun D (e₂ • e₁) f ≈ dependentPiFunctorToFun D e₂ (dependentPiFunctorToFun D e₁ f) :=
⟨⟨λ z => let lx := (congrArgMap D.fst.F (e₂ • e₁)).invFun z;
         let lse : SigmaEquiv ⟨a, lx⟩ ⟨c, z⟩ := ⟨e₂ • e₁, ⟨(congrArgMap D.fst.F (e₂ • e₁)).isInv.rightInv.ext z⟩⟩;
         let lre := congrArgMap D.snd lse;
         let ry := (congrArgMap D.fst.F e₂).invFun z;
         let rse₂ : SigmaEquiv ⟨b, ry⟩ ⟨c, z⟩ := ⟨e₂, ⟨(congrArgMap D.fst.F e₂).isInv.rightInv.ext z⟩⟩;
         let rre₂ := congrArgMap D.snd rse₂;
         let rx := (congrArgMap D.fst.F e₁).invFun ry;
         let rse₁ : SigmaEquiv ⟨a, rx⟩ ⟨b, ry⟩ := ⟨e₁, ⟨(congrArgMap D.fst.F e₁).isInv.rightInv.ext ry⟩⟩;
         let rre₁ := congrArgMap D.snd rse₁;
         let h₁ : lx ≃ rx := sorry;
         let h₂ := f.mapEquiv h₁;
         let h : lre.toFun (f lx) ≈ rre₂.toFun (rre₁.toFun (f rx)) := sorry;
         h⟩⟩

def dependentPiFunctorDesc : SetoidUniverseFunctorDesc D.fst.S :=
{ map            := dependentPiStructure D,
  toFun          := dependentPiFunctorToFun D,
  respectsSetoid := λ h     f => ⟨sorry⟩,
  respectsComp   := dependentPiFunctorRespectsComp D,
  respectsId     := λ a     f => ⟨sorry⟩ }

-- `a ↦ ∀ x : D.fst.F a, D.snd ⟨a, x⟩`
def dependentPiFunctor : UniverseFunctor D.fst.S := SetoidUniverseFunctorDesc.universeFunctor (dependentPiFunctorDesc D)

-- `Σ x : D.fst.F a, D.snd ⟨a, x⟩`
def dependentSigmaStructure (a : D.fst.S) := sigmaStructure ⟨D.fst.F a, resultFunctor D a⟩

def dependentSigmaFunctorDesc : SetoidUniverseFunctorDesc D.fst.S :=
{ map            := dependentSigmaStructure D,
  toFun          := sorry,
  respectsSetoid := sorry,
  respectsComp   := sorry,
  respectsId     := sorry }

-- `a ↦ Σ x : D.fst.F a, D.snd ⟨a, x⟩`
def dependentSigmaFunctor : UniverseFunctor D.fst.S := SetoidUniverseFunctorDesc.universeFunctor (dependentSigmaFunctorDesc D)

-- `(∀ x : α, ∀ y : F x, G x y) ≃ (∀ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`(λ x y => g x y) ↦ (λ ⟨x, y⟩ => g x y)`)

def nestedPiDependency : StructureDependency := ⟨D.fst.S, dependentPiFunctor D⟩

@[reducible] def piPiCurried   := piStructure (nestedPiDependency  D)
@[reducible] def piPiUncurried := piStructure (innerPairDependency D)

def piPiEquivToFun  : StructureFunctor (piPiCurried   D) (piPiUncurried D) :=
{ map     := λ g => ⟨λ ⟨a, x⟩ => (g a).map x, sorry⟩,
  functor := sorry }

def piPiEquivInvFun : StructureFunctor (piPiUncurried D) (piPiCurried   D) :=
{ map     := λ g => ⟨λ a => ⟨λ x => g ⟨a, x⟩, sorry⟩, sorry⟩,
  functor := sorry }

def piPiEquiv : StructureEquiv (piPiCurried D) (piPiUncurried D) :=
{ toFun  := piPiEquivToFun  D,
  invFun := piPiEquivInvFun D,
  isInv  := sorry }

-- `(Σ x : α, Σ y : F x, G x y) ≃ (Σ ⟨x, y⟩ : (Σ x : α, F x), G x y)`
-- (`⟨x, ⟨y, z⟩⟩ ↦ ⟨⟨x, y⟩, z⟩`)

def nestedSigmaDependency : StructureDependency := ⟨D.fst.S, dependentSigmaFunctor D⟩

def sigmaSigmaCurried   := sigmaStructure (nestedSigmaDependency D)
def sigmaSigmaUncurried := sigmaStructure (innerPairDependency   D)

def sigmaSigmaEquivToFun  : StructureFunctor (sigmaSigmaCurried   D) (sigmaSigmaUncurried D) :=
{ map     := λ ⟨a, ⟨x, y⟩⟩ => ⟨⟨a, x⟩, y⟩,
  functor := { mapEquiv  := λ ⟨e, he⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquivInvFun : StructureFunctor (sigmaSigmaUncurried D) (sigmaSigmaCurried   D) :=
{ map     := λ ⟨⟨a, x⟩, y⟩ => ⟨a, ⟨x, y⟩⟩,
  functor := { mapEquiv  := λ ⟨⟨e, f⟩, g⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquiv : StructureEquiv (sigmaSigmaCurried D) (sigmaSigmaUncurried D) :=
{ toFun  := sigmaSigmaEquivToFun  D,
  invFun := sigmaSigmaEquivInvFun D,
  isInv  := sorry }

-- `(∀ x : α, Σ y : F x, G x y) ≃ (Σ f : (∀ x : α, F x), ∀ x : α, G x (f x))`
-- (`(λ x => ⟨y, f x⟩ ↦ ⟨λ x => y, λ x => f x⟩`)

-- TODO

end PiSigmaEquivalences

end PiSigma
