--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
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

-- TODO: It is really annoying that `C` is not definitionally equivalent to `⟨C.S, C.F⟩`. Is there a way around this?
theorem dependencyDef (C : StructureDependency) : C = ⟨C.S, C.F⟩ := match C with
| ⟨_, _⟩ => rfl

def constDep (S T : Structure) : StructureDependency := ⟨S, constFun T⟩

structure StructureDependencyEquiv (C D : StructureDependency) where
(e : C.S ≃ D.S)
-- TODO: Why does `≃` not work here? There is some strange type class resolution issue with the `universeFunctor` argument at play.
(η : FunctorEquiv C.F (D.F ⊙ e.toFun))

namespace StructureDependencyEquiv

def invFunEquiv {C D : StructureDependency} (e : StructureDependencyEquiv C D) : FunctorEquiv (C.F ⊙ e.e.invFun) D.F :=
let e₁ := FunctorEquiv.trans (compFun.congrArg_left (F := e.e.invFun) e.η) (compFun.congrArg_right (G := D.F) e.e.isInv.rightInv);
FunctorEquiv.trans e₁ (idFun.rightId D.F)

def refl  (C     : StructureDependency)                                                                       : StructureDependencyEquiv C C :=
⟨StructureEquiv.refl  C.S,     FunctorEquiv.symm (idFun.rightId C.F)⟩

def symm  {C D   : StructureDependency} (e : StructureDependencyEquiv C D)                                    : StructureDependencyEquiv D C :=
⟨StructureEquiv.symm  e.e,     FunctorEquiv.symm (invFunEquiv e)⟩

def trans {C D E : StructureDependency} (e : StructureDependencyEquiv C D) (f : StructureDependencyEquiv D E) : StructureDependencyEquiv C E :=
⟨StructureEquiv.trans e.e f.e, FunctorEquiv.trans e.η (compFun.congrArg_left (F := e.e.toFun) f.η)⟩

def StructureDependencyEquivEquiv {C D : StructureDependency} (e f : StructureDependencyEquiv C D) :=
∃ ζ : e.e ≃ f.e, compFun.congrArg_right (G := D.F) ζ.toFunEquiv • e.η ≈ f.η

namespace StructureDependencyEquivEquiv

variable {C D : StructureDependency}

theorem refl  (e     : StructureDependencyEquiv C D)                                                                                 : StructureDependencyEquivEquiv e e :=
⟨StructureEquiv.EquivEquiv.refl  e.e,
 leftCancelId (compFun.congrArg_right.respectsId e.e.toFun)⟩

theorem symm  {e f   : StructureDependencyEquiv C D} (h : StructureDependencyEquivEquiv e f)                                         : StructureDependencyEquivEquiv f e :=
let ⟨ζ, hζ⟩ := h;
let h₁ := (leftMulInv (h := functorHasStructure) e.η f.η (compFun.congrArg_right ζ.toFunEquiv)).mp hζ;
let h₂ := compFun.congrArg_right.respectsInv ζ.toFunEquiv;
⟨StructureEquiv.EquivEquiv.symm  ζ,
 comp_subst_left h₂ (Setoid.symm h₁)⟩

theorem trans {e f g : StructureDependencyEquiv C D} (h : StructureDependencyEquivEquiv e f) (i : StructureDependencyEquivEquiv f g) : StructureDependencyEquivEquiv e g :=
let ⟨ζ, hζ⟩ := h;
let ⟨ξ, hξ⟩ := i;
let h₁ := applyAssoc_left (comp_subst_right hζ hξ);
let h₂ := compFun.congrArg_right.respectsComp ζ.toFunEquiv ξ.toFunEquiv;
⟨StructureEquiv.EquivEquiv.trans ζ ξ,
 comp_subst_left h₂ h₁⟩

instance structureDependencyEquivSetoid : Setoid (StructureDependencyEquiv C D) := ⟨StructureDependencyEquivEquiv, ⟨refl, symm, trans⟩⟩

end StructureDependencyEquivEquiv

def structureDependencyEquiv (C D : StructureDependency) : BundledSetoid := ⟨StructureDependencyEquiv C D⟩

instance structureDependencyEquivHasIso : HasIsomorphisms structureDependencyEquiv :=
{ comp          := trans,
  comp_congrArg := λ he hf => sorry,
  assoc         := λ e f g => sorry,
  id            := refl,
  leftId        := λ e     => sorry,
  rightId       := λ e     => sorry,
  inv           := symm,
  inv_congrArg  := λ he    => sorry,
  leftInv       := λ e     => sorry,
  rightInv      := λ e     => sorry,
  invInv        := λ e     => sorry,
  compInv       := λ e f   => sorry,
  idInv         := λ C     => sorry }

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
(mapEquiv {a b : C.S} (e : a ≃ b) : map a ≈[congrArg C.F e] map b)

namespace PiExpr

instance (C : StructureDependency) : CoeFun (PiExpr C) (λ _ => ∀ a : C.S, C.F a) := ⟨PiExpr.map⟩

def PiEquiv {C : StructureDependency} (F G : PiExpr C) := Pi.PiEquiv.DependentPiEquiv PiExpr.map F G

namespace PiEquiv

variable {C : StructureDependency}

def refl  (F     : PiExpr C)                                     : PiEquiv F F :=
Pi.PiEquiv.DependentPiEquiv.refl  F
def symm  {F G   : PiExpr C} (η : PiEquiv F G)                   : PiEquiv G F :=
Pi.PiEquiv.DependentPiEquiv.symm  η
def trans {F G H : PiExpr C} (η : PiEquiv F G) (θ : PiEquiv G H) : PiEquiv F H :=
Pi.PiEquiv.DependentPiEquiv.trans η θ

def piEquiv : GeneralizedRelation (PiExpr C) := Pi.PiEquiv.DependentPiEquiv.dependentPiEquiv (z := PiExpr.map)

instance piEquivHasIso : HasIsomorphisms (@piEquiv C) := Pi.PiEquiv.DependentPiEquiv.dependentPiEquivHasIso

end PiEquiv

instance piHasStructure (C : StructureDependency) : HasStructure (PiExpr C) := ⟨PiEquiv.piEquiv⟩
def piStructure (C : StructureDependency) : Structure := ⟨PiExpr C⟩



def idPi {S : Structure} : PiExpr (StructureDependency.constDep S S) :=
{ map      := id,
  mapEquiv := toSetoidEquiv S }

def compFunPi {S : Structure} {C : StructureDependency} (F : StructureFunctor S C.S) (G : PiExpr C) :
  PiExpr ⟨S, C.F ⊙ F⟩ :=
{ map      := λ a => G (F a),
  mapEquiv := λ e => G.mapEquiv (congrArg F e) }

def constPiToFun {S T : Structure} (F : PiExpr (StructureDependency.constDep S T)) :
  StructureFunctor S (setoidStructure T) :=
makeToSetoidStructureFunctor F.map F.mapEquiv

def funToConstPi {S T : Structure} (F : StructureFunctor S (setoidStructure T)) :
  PiExpr (StructureDependency.constDep S T) :=
{ map      := F.map,
  mapEquiv := F.functor.mapEquiv }

def transportPiS {S₁ S₂ : Structure} (ε : S₁ ≃ S₂) (F : UniverseFunctor S₁) :
  PiExpr ⟨S₁, F⟩ → PiExpr ⟨S₂, F ⊙ ε.invFun⟩ :=
λ G => { map      := λ a => G (ε.invFun a),
         mapEquiv := λ e => G.mapEquiv (congrArg ε.invFun e) }

def transportPiF {S : Structure} {F₁ F₂ : UniverseFunctor S} (η : FunctorEquiv F₁ F₂) :
  PiExpr ⟨S, F₁⟩ → PiExpr ⟨S, F₂⟩ :=
λ G => { map      := λ a => (η.ext a).toFun (G a),
         mapEquiv := λ {a b} e => let ⟨n⟩ := η.nat e;
                                  let ⟨m⟩ := G.mapEquiv e;
                                  ⟨IsEquivalence.trans (n.toFunEquiv.ext (G a)) (congrArg (η.ext b).toFun m)⟩ }

def transportPi' {S₁ S₂ : Structure} {F₁ : UniverseFunctor S₁} {F₂ : UniverseFunctor S₂}
                 (ε : S₁ ≃ S₂) (η : FunctorEquiv (F₁ ⊙ ε.invFun) F₂) :
  PiExpr ⟨S₁, F₁⟩ → PiExpr ⟨S₂, F₂⟩ :=
λ G => transportPiF η (transportPiS ε F₁ G)

def transportPi {C D : StructureDependency} (e : StructureDependencyEquiv C D) :
  PiExpr C → PiExpr D :=
dependencyDef C ▸ dependencyDef D ▸ transportPi' e.e (StructureDependencyEquiv.invFunEquiv e)

def dependentApplicationFunctor {S T : Structure} {F : UniverseFunctor S}
                                (G : PiExpr ⟨S, incomingFunctorFunctor T ⊙ F⟩)
                                (x : PiExpr ⟨S, F⟩) :
  SetoidStructureFunctor S T :=
makeSetoidStructureFunctor (λ a => (G a).map (x a))
                           (λ {a b} ⟨e⟩ => let ⟨h₁⟩ := G.mapEquiv e;
                                           let ⟨h₂⟩ := x.mapEquiv e;
                                           let h₃ := StructureFunctor.congr h₁ h₂;
                                           let h₄ := congrArg (G a) ((congrArg F e).isInv.leftInv.ext (x a));
                                           ⟨IsEquivalence.trans (IsEquivalence.symm h₄) h₃⟩)



namespace piStructure

instance (C : StructureDependency) : CoeFun (IsType.type (piStructure C)) (λ _ => ∀ a : C.S, C.F a) := ⟨PiExpr.map⟩

-- An independent `PiExpr` is the same as a functor (to a setoid structure).

section constDep

variable (S T : Structure)

def constDepToFun :
  StructureFunctor (piStructure (StructureDependency.constDep S T)) (functorStructure S (setoidStructure T)) :=
{ map     := constPiToFun,
  functor := { mapEquiv  := λ η => makeToSetoidStructureFunctorEquiv' η,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ η θ => Setoid.refl (θ • η),
                              respectsId     := λ F   => Setoid.refl (id__ F),
                              respectsInv    := λ η   => Setoid.refl η⁻¹ } } }

def constDepInvFun :
  StructureFunctor (functorStructure S (setoidStructure T)) (piStructure (StructureDependency.constDep S T)) :=
{ map     := funToConstPi,
  functor := { mapEquiv  := λ η => η.ext,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ η θ => Setoid.refl (θ • η),
                              respectsId     := λ F   => Setoid.refl (id__ F),
                              respectsInv    := λ η   => Setoid.refl η⁻¹ } } }

def constDepEquiv :
  StructureEquiv (piStructure (StructureDependency.constDep S T)) (functorStructure S (setoidStructure T)) :=
{ toFun    := constDepToFun  S T,
  invFun   := constDepInvFun S T,
  isInv  := { leftInv  := { ext := λ F a => IsEquivalence.refl (F a),
                            nat := λ _ _ => proofIrrel _ _ },
              rightInv := { ext := λ F => makeToSetoidStructureFunctorEquiv' (λ a => IsEquivalence.refl (F a)),
                            nat := λ _ _ => proofIrrel _ _ },
              lrCompat := λ _ _ => proofIrrel _ _,
              rlCompat := λ _ _ => proofIrrel _ _ } }

end constDep

-- If we fix the argument, we obtain a functor from `piStructure` to the result type.

def projFunctor (C : StructureDependency) (a : C.S) : StructureFunctor (piStructure C) (setoidStructure (C.F a)) :=
{ map     := λ F => F a,
  functor := { mapEquiv  := λ η => η a,
               isFunctor := { respectsSetoid := λ h   => h a,
                              respectsComp   := λ η θ => Setoid.refl (θ a • η a),
                              respectsId     := λ F   => Setoid.refl (id_ (F a)),
                              respectsInv    := λ η   => Setoid.refl (η a)⁻¹ } } }

-- `piStructure` itself can be viewed as a dependent structure, depending on an instance of
-- `StructureDependency`.

-- TODO: Why does `C ≃ D` not work?
def piStructureFunctor_toFun {C D : StructureDependency} (e : StructureDependencyEquiv C D) :
  StructureFunctor (piStructure C) (piStructure D) :=
{ map     := transportPi e,
  functor := { mapEquiv  := λ {F G} η a => let F' : PiExpr ⟨C.S, C.F⟩ := dependencyDef C ▸ F;
                                           let G' : PiExpr ⟨C.S, C.F⟩ := dependencyDef C ▸ G;
                                           let η' : PiEquiv F' G' := sorry; --dependencyDef C ▸ η;
                                           let θ := StructureDependencyEquiv.invFunEquiv e;
                                           let h₁ : transportPi' e.e θ F' a ≃ transportPi' e.e θ G' a := congrArg (setoidFunctor (θ.ext a).toFun) (η' (e.e.invFun a));
                                           let h₂ : transportPi e F a ≃ transportPi e G a := sorry; --dependencyDef C ▸ dependencyDef D ▸ h₁;
                                           h₂,
               isFunctor := { respectsSetoid := λ _ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ _ => proofIrrel _ _,
                              respectsId     := λ _   _ => proofIrrel _ _,
                              respectsInv    := λ _   _ => proofIrrel _ _ } } }

def piStructureFunctor_equiv {C D : StructureDependency} (e : StructureDependencyEquiv C D) :
  piStructure C ≃ piStructure D :=
{ toFun  := piStructureFunctor_toFun e,
  invFun := piStructureFunctor_toFun (StructureDependencyEquiv.symm e),
  isInv  := sorry }

def piStructureFunctor : UniverseFunctor structureDependencyStructure :=
{ map     := piStructure,
  functor := { mapEquiv  := piStructureFunctor_equiv,
               isFunctor := sorry } }

def piStructureDependency : StructureDependency := ⟨structureDependencyStructure, piStructureFunctor⟩

end piStructure

end PiExpr

open PiExpr



-- A Σ expression of structures.

def SigmaExpr (C : StructureDependency) := Σ' a : C.S, IsType.type (C.F a)

namespace SigmaExpr

-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence `e` between the types such that `congrArg C.F e` maps one
-- instance of the type class to the other.

def SigmaEquiv {C : StructureDependency} (P Q : SigmaExpr C) :=
Σ' e : P.fst ≃ Q.fst, P.snd ≈[congrArg C.F e] Q.snd

namespace SigmaEquiv

variable {C : StructureDependency}

def refl  (P     : SigmaExpr C)                                           : SigmaEquiv P P :=
let h₁ := SetoidInstanceEquiv.refl (C.F P.fst) P.snd;
let h₂ := Setoid.symm (respectsId   C.F P.fst);
⟨IsEquivalence.refl  P.fst,       SetoidInstanceEquiv.mapEquiv h₂ P.snd P.snd h₁⟩

def symm  {P Q   : SigmaExpr C} (e : SigmaEquiv P Q)                      : SigmaEquiv Q P :=
let h₁ := SetoidInstanceEquiv.symm (congrArg C.F e.fst) P.snd Q.snd e.snd;
let h₂ := Setoid.symm (respectsInv  C.F e.fst);
⟨IsEquivalence.symm  e.fst,       SetoidInstanceEquiv.mapEquiv h₂ Q.snd P.snd h₁⟩

def trans {P Q R : SigmaExpr C} (e : SigmaEquiv P Q) (f : SigmaEquiv Q R) : SigmaEquiv P R :=
let h₁ := SetoidInstanceEquiv.trans (congrArg C.F e.fst) (congrArg C.F f.fst) P.snd Q.snd R.snd e.snd f.snd;
let h₂ := Setoid.symm (respectsComp C.F e.fst f.fst);
⟨IsEquivalence.trans e.fst f.fst, SetoidInstanceEquiv.mapEquiv h₂ P.snd R.snd h₁⟩

-- No need to compare `e.snd` and `f.snd` because they are proofs.
def SigmaEquivEquiv {P Q : SigmaExpr C} (e f : SigmaEquiv P Q) := e.fst ≈ f.fst

namespace SigmaEquivEquiv

variable {P Q : SigmaExpr C}

theorem refl  (e     : SigmaEquiv P Q)                                                     : SigmaEquivEquiv e e :=
Setoid.refl  e.fst

theorem symm  {e f   : SigmaEquiv P Q} (h : SigmaEquivEquiv e f)                           : SigmaEquivEquiv f e :=
Setoid.symm  h

theorem trans {e f g : SigmaEquiv P Q} (h : SigmaEquivEquiv e f) (i : SigmaEquivEquiv f g) : SigmaEquivEquiv e g :=
Setoid.trans h i

instance sigmaEquivSetoid : Setoid (SigmaEquiv P Q) := ⟨SigmaEquivEquiv, ⟨refl, symm, trans⟩⟩

end SigmaEquivEquiv

def sigmaEquiv (P Q : SigmaExpr C) : BundledSetoid := ⟨SigmaEquiv P Q⟩

instance sigmaEquivHasIso : HasIsomorphisms (@sigmaEquiv C) :=
{ comp          := trans,
  comp_congrArg := λ he hf => comp_congrArg he hf,
  assoc         := λ e f g => assoc         e.fst f.fst g.fst,
  id            := refl,
  leftId        := λ e     => leftId        e.fst,
  rightId       := λ e     => rightId       e.fst,
  inv           := symm,
  inv_congrArg  := λ he    => inv_congrArg  he,
  leftInv       := λ e     => leftInv       e.fst,
  rightInv      := λ e     => rightInv      e.fst,
  invInv        := λ e     => invInv        e.fst,
  compInv       := λ e f   => compInv       e.fst f.fst,
  idInv         := λ s     => idInv         s.fst }

end SigmaEquiv

instance sigmaHasStructure (C : StructureDependency) : HasStructure (SigmaExpr C) := ⟨SigmaEquiv.sigmaEquiv⟩
def sigmaStructure (C : StructureDependency) : Structure := ⟨SigmaExpr C⟩



def transportSigmaS {S₁ S₂ : Structure} (ε : S₁ ≃ S₂) (F : UniverseFunctor S₁) :
  SigmaExpr ⟨S₁, F⟩ → SigmaExpr ⟨S₂, F ⊙ ε.invFun⟩ :=
λ s => ⟨ε.toFun s.fst, (congrArg F (ε.isInv.leftInv.ext s.fst)).invFun s.snd⟩

def transportSigmaF {S : Structure} {F₁ F₂ : UniverseFunctor S} (η : FunctorEquiv F₁ F₂) :
  SigmaExpr ⟨S, F₁⟩ → SigmaExpr ⟨S, F₂⟩ :=
λ s => ⟨s.fst, (η.ext s.fst).toFun s.snd⟩

def transportSigma' {S₁ S₂ : Structure} {F₁ : UniverseFunctor S₁} {F₂ : UniverseFunctor S₂}
                 (ε : S₁ ≃ S₂) (η : FunctorEquiv (F₁ ⊙ ε.invFun) F₂) :
  SigmaExpr ⟨S₁, F₁⟩ → SigmaExpr ⟨S₂, F₂⟩ :=
λ G => transportSigmaF η (transportSigmaS ε F₁ G)

def transportSigma {C D : StructureDependency} (e : StructureDependencyEquiv C D) :
  SigmaExpr C → SigmaExpr D :=
dependencyDef C ▸ dependencyDef D ▸ transportSigma' e.e (StructureDependencyEquiv.invFunEquiv e)



namespace sigmaStructure

-- Introduction and projections of `sigmaStructure` are functorial.

section MkProj

variable (C : StructureDependency)

def mkSndFunctor : UniverseFunctor C.S :=
incomingFunctorFunctor (sigmaStructure C) ⊙ C.F

def mkDependency : StructureDependency := ⟨C.S, mkSndFunctor C⟩

def mkExprFunctor (a : C.S) : StructureFunctor (C.F a) (sigmaStructure C) :=
{ map     := λ b => ⟨a, b⟩,
  functor := { mapEquiv  := λ {b c} e => ⟨id_ a, SetoidInstanceEquiv.mapEquiv (Setoid.symm (respectsId C.F a)) b c ⟨e⟩⟩,
               isFunctor := { respectsSetoid := λ _   => Setoid.refl _,
                              respectsComp   := λ _ _ => Setoid.symm (leftId _),
                              respectsId     := λ _   => Setoid.refl (id'' (S := sigmaStructure C)),
                              respectsInv    := λ _   => Setoid.symm (idInv _) } } }

theorem mkExprCongrArg {a₁ a₂ : C.S} (e : a₁ ≃ a₂) :
  mkExprFunctor C a₁ ≈[congrArg (mkSndFunctor C) e] mkExprFunctor C a₂ :=
⟨{ ext := λ b       => ⟨e, ⟨(congrArg C.F e).isInv.rightInv.ext b⟩⟩,
   nat := λ {b c} ε => sorry }⟩

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

end MkProj



-- `sigmaStructure` itself can be viewed as dependent structures, depending on an instance of
-- `StructureDependency`.

-- TODO: Why does `C ≃ D` not work?
def sigmaStructureFunctor_toFun {C D : StructureDependency} (e : StructureDependencyEquiv C D) :
  StructureFunctor (sigmaStructure C) (sigmaStructure D) :=
{ map     := transportSigma e,
  functor := { mapEquiv  := λ {s t} ε => let s' : SigmaExpr ⟨C.S, C.F⟩ := dependencyDef C ▸ s;
                                         let t' : SigmaExpr ⟨C.S, C.F⟩ := dependencyDef C ▸ t;
                                         let ε' : SigmaEquiv s' t' := sorry; --dependencyDef C ▸ ε;
                                         let θ := StructureDependencyEquiv.invFunEquiv e;
                                         let h₁ : transportSigma' e.e θ s' ≃ transportSigma' e.e θ t' := ⟨congrArg e.e.toFun ε'.fst, sorry⟩;
                                         let h₂ : transportSigma e s ≃ transportSigma e t := sorry; --dependencyDef C ▸ dependencyDef D ▸ h₁;
                                         h₂,
               isFunctor := sorry } }

def sigmaStructureFunctor_equiv {C D : StructureDependency} (e : StructureDependencyEquiv C D) :
  sigmaStructure C ≃ sigmaStructure D :=
{ toFun  := sigmaStructureFunctor_toFun e,
  invFun := sigmaStructureFunctor_toFun (StructureDependencyEquiv.symm e),
  isInv  := sorry }

def sigmaStructureFunctor : UniverseFunctor structureDependencyStructure :=
{ map     := sigmaStructure,
  functor := { mapEquiv  := sigmaStructureFunctor_equiv,
               isFunctor := sorry } }

def sigmaStructureDependency : StructureDependency := ⟨structureDependencyStructure, sigmaStructureFunctor⟩

end sigmaStructure

end SigmaExpr

open SigmaExpr



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
let x := (congrArg D.fst.F e).invFun y;
let se : SigmaEquiv ⟨a, x⟩ ⟨b, y⟩ := ⟨e, ⟨(congrArg D.fst.F e).isInv.rightInv.ext y⟩⟩;
let re := congrArg D.snd se;
re.toFun

def dependentPiFunctorToFunMap' {a b : D.fst.S} (e : a ≃ b) (f : dependentPiStructure D a) (y : D.fst.F b) :
  resultFunctor D b y :=
let x := (congrArg D.fst.F e).invFun y;
dependentPiFunctorToFunResultFun D e y (f x)

def dependentPiFunctorToFunMap {a b : D.fst.S} (e : a ≃ b) (f : dependentPiStructure D a) :
  dependentPiStructure D b :=
⟨dependentPiFunctorToFunMap' D e f, sorry⟩

theorem dependentPiFunctorToFunCongrArg {a b : D.fst.S} (e : a ≃ b) {f₁ f₂ : dependentPiStructure D a} (h : f₁ ≈ f₂) :
  dependentPiFunctorToFunMap D e f₁ ≈ dependentPiFunctorToFunMap D e f₂ :=
let ⟨eh⟩ := h;
⟨λ y => congrArg (setoidFunctor (dependentPiFunctorToFunResultFun D e y)) (eh ((congrArg D.fst.F e).invFun y))⟩

def dependentPiFunctorToFun {a b : D.fst.S} (e : a ≃ b) :
  SetoidStructureFunctor (dependentPiStructure D a) (dependentPiStructure D b) :=
makeSetoidStructureFunctor (dependentPiFunctorToFunMap D e) (dependentPiFunctorToFunCongrArg D e)

-- TODO: Instead of proving this by hand here, we should expand and use general infrastructure such as
-- `dependentApplicationFunctor`.

theorem dependentPiFunctorRespectsComp {a b c : D.fst.S} (e₁ : a ≃ b) (e₂ : b ≃ c) (F : dependentPiStructure D a) :
  dependentPiFunctorToFun D (e₂ • e₁) F ≈ dependentPiFunctorToFun D e₂ (dependentPiFunctorToFun D e₁ F) :=
⟨⟨λ z => let lx := (congrArg D.fst.F (e₂ • e₁)).invFun z;
         let lse : SigmaEquiv ⟨a, lx⟩ ⟨c, z⟩ := ⟨e₂ • e₁, ⟨(congrArg D.fst.F (e₂ • e₁)).isInv.rightInv.ext z⟩⟩;
         let lre := congrArg D.snd lse;
         let ry := (congrArg D.fst.F e₂).invFun z;
         let rse₂ : SigmaEquiv ⟨b, ry⟩ ⟨c, z⟩ := ⟨e₂, ⟨(congrArg D.fst.F e₂).isInv.rightInv.ext z⟩⟩;
         let rre₂ := congrArg D.snd rse₂;
         let rx := (congrArg D.fst.F e₁).invFun ry;
         let rse₁ : SigmaEquiv ⟨a, rx⟩ ⟨b, ry⟩ := ⟨e₁, ⟨(congrArg D.fst.F e₁).isInv.rightInv.ext ry⟩⟩;
         let rre₁ := congrArg D.snd rse₁;
         let h₁ : lx ≃ rx := sorry;
         let h₂ := F.mapEquiv h₁;
         let h : lre.toFun (F lx) ≈ rre₂.toFun (rre₁.toFun (F rx)) := sorry;
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
