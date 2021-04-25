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
(e : C.S ≃ D.S)
-- TODO: Why does `≃` not work here? There is some strange type class resolution issue with the `universeFunctor` argument at play.
(η : FunctorEquiv C.F (D.F ⊙ e.toFun))

namespace StructureDependencyEquiv

def invFunEquiv {C D : StructureDependency} (φ : StructureDependencyEquiv C D) : FunctorEquiv (C.F ⊙ φ.e.invFun) D.F :=
let e₁ := FunctorEquiv.trans (compFun.congrArg_left (F := φ.e.invFun) φ.η) (compFun.congrArg_right (G := D.F) φ.e.isInv.rightInv);
FunctorEquiv.trans e₁ (idFun.rightId D.F)

def refl  (C     : StructureDependency)                                                                       : StructureDependencyEquiv C C :=
⟨StructureEquiv.refl  C.S,     FunctorEquiv.symm (idFun.rightId C.F)⟩

def symm  {C D   : StructureDependency} (φ : StructureDependencyEquiv C D)                                    : StructureDependencyEquiv D C :=
⟨StructureEquiv.symm  φ.e,     FunctorEquiv.symm (invFunEquiv φ)⟩

def trans {C D E : StructureDependency} (φ : StructureDependencyEquiv C D) (ψ : StructureDependencyEquiv D E) : StructureDependencyEquiv C E :=
⟨StructureEquiv.trans φ.e ψ.e, FunctorEquiv.trans φ.η (compFun.congrArg_left (F := φ.e.toFun) ψ.η)⟩

def StructureDependencyEquivEquiv {C D : StructureDependency} (φ ψ : StructureDependencyEquiv C D) :=
Σ' ζ : φ.e ≃ ψ.e, compFun.congrArg_right (G := D.F) ζ.toFunEquiv • φ.η ≈ ψ.η

namespace StructureDependencyEquivEquiv

variable {C D : StructureDependency}

def refl  (φ     : StructureDependencyEquiv C D)                                                                                 : StructureDependencyEquivEquiv φ φ :=
⟨StructureEquiv.EquivEquiv.refl  φ.e,
 leftCancelId (compFun.congrArg_right.respectsId φ.e.toFun)⟩

def symm  {φ ψ   : StructureDependencyEquiv C D} (ζ : StructureDependencyEquivEquiv φ ψ)                                         : StructureDependencyEquivEquiv ψ φ :=
⟨StructureEquiv.EquivEquiv.symm  ζ.fst,
 let h₁ := (leftMulInv (h := functorHasStructure) φ.η ψ.η (compFun.congrArg_right ζ.fst.toFunEquiv)).mp ζ.snd;
 let h₂ := compFun.congrArg_right.respectsInv ζ.fst.toFunEquiv;
 comp_subst_left h₂ (Setoid.symm h₁)⟩

def trans {φ ψ χ : StructureDependencyEquiv C D} (ζ : StructureDependencyEquivEquiv φ ψ) (ξ : StructureDependencyEquivEquiv ψ χ) : StructureDependencyEquivEquiv φ χ :=
⟨StructureEquiv.EquivEquiv.trans ζ.fst ξ.fst,
 let h₁ := applyAssoc_left (comp_subst_right ζ.snd ξ.snd);
 let h₂ := compFun.congrArg_right.respectsComp ζ.fst.toFunEquiv ξ.fst.toFunEquiv;
 comp_subst_left h₂ h₁⟩

def StructureDependencyEquivEquivEquiv {φ ψ : StructureDependencyEquiv C D} (ζ ξ : StructureDependencyEquivEquiv φ ψ) :=
ζ.fst ≈ ξ.fst

namespace StructureDependencyEquivEquivEquiv

variable {φ ψ : StructureDependencyEquiv C D}

theorem refl  (ζ     : StructureDependencyEquivEquiv φ ψ)                                                                                           : StructureDependencyEquivEquivEquiv ζ ζ :=
Setoid.refl  ζ.fst

theorem symm  {ζ ξ   : StructureDependencyEquivEquiv φ ψ} (h : StructureDependencyEquivEquivEquiv ζ ξ)                                              : StructureDependencyEquivEquivEquiv ξ ζ :=
Setoid.symm  h

theorem trans {ζ ξ σ : StructureDependencyEquivEquiv φ ψ} (h : StructureDependencyEquivEquivEquiv ζ ξ) (i : StructureDependencyEquivEquivEquiv ξ σ) : StructureDependencyEquivEquivEquiv ζ σ :=
Setoid.trans h i

instance structureDependencyEquivEquivSetoid : Setoid (StructureDependencyEquivEquiv φ ψ) := ⟨StructureDependencyEquivEquivEquiv, ⟨refl, symm, trans⟩⟩

end StructureDependencyEquivEquivEquiv

def structureDependencyEquivEquiv (φ ψ : StructureDependencyEquiv C D) : BundledSetoid := ⟨StructureDependencyEquivEquiv φ ψ⟩

-- TODO: Is there a less annoying way to do this?
def comp_congrArg {φ ψ χ : StructureDependencyEquiv C D}
                  {ζ₁ ζ₂ : StructureDependencyEquivEquiv φ ψ}     {ξ₁ ξ₂ : StructureDependencyEquivEquiv ψ χ}
                  (hζ : StructureDependencyEquivEquivEquiv ζ₁ ζ₂) (hξ : StructureDependencyEquivEquivEquiv ξ₁ ξ₂) :
  StructureDependencyEquivEquivEquiv (trans ζ₁ ξ₁) (trans ζ₂ ξ₂) :=
HasStructure.comp_congrArg hζ hξ

instance structureDependencyEquivEquivHasIso : HasIsomorphisms (@structureDependencyEquivEquiv C D) :=
{ comp          := trans,
  comp_congrArg := comp_congrArg,
  assoc         := λ ζ ξ σ => sorry,
  id            := refl,
  leftId        := λ ζ     => sorry,
  rightId       := λ ζ     => sorry,
  inv           := symm,
  inv_congrArg  := λ hζ    => sorry,
  leftInv       := λ ζ     => sorry,
  rightInv      := λ ζ     => sorry,
  invInv        := λ ζ     => sorry,
  compInv       := λ ζ ξ   => sorry,
  idInv         := λ φ     => sorry }

end StructureDependencyEquivEquiv

instance structureDependencyEquivHasStructure (C D : StructureDependency) : HasStructure (StructureDependencyEquiv C D) :=
⟨StructureDependencyEquivEquiv.structureDependencyEquivEquiv⟩

def structureDependencyEquivStructure (C D : StructureDependency) : Structure := ⟨StructureDependencyEquiv C D⟩

instance structureDependencyEquivSetoid (C D : StructureDependency) : Setoid (StructureDependencyEquiv C D) := structureToSetoid (structureDependencyEquivStructure C D)

def structureDependencyEquiv (C D : StructureDependency) : BundledSetoid := ⟨StructureDependencyEquiv C D⟩

instance structureDependencyEquivHasIso : HasIsomorphisms structureDependencyEquiv :=
{ comp          := trans,
  comp_congrArg := λ hφ hψ => sorry,
  assoc         := λ φ ψ χ => sorry,
  id            := refl,
  leftId        := λ φ     => sorry,
  rightId       := λ φ     => sorry,
  inv           := symm,
  inv_congrArg  := λ hφ    => sorry,
  leftInv       := λ φ     => sorry,
  rightInv      := λ φ     => sorry,
  invInv        := λ φ     => sorry,
  compInv       := λ φ ψ   => sorry,
  idInv         := λ C     => sorry }

end StructureDependencyEquiv

instance structureDependencyHasStructure : HasStructure StructureDependency := ⟨StructureDependencyEquiv.structureDependencyEquiv⟩
def structureDependencyStructure : Structure := ⟨StructureDependency⟩

namespace structureDependencyStructure

-- We can construct a functor into `StructureDependency` by giving essentially a functor yielding `S` and
-- a Π expression yielding `F`.

structure StructureDependencyFunctorDesc where
(FS                                                                 : UniverseStructureFunctor)
(FF                 (S   : Structure)                               : UniverseFunctor (FS.map S))
(mapEquiv           {S T : Structure} (e : S ≃ T)                   : FunctorEquiv (FF S) (FF T ⊙ (FS.mapEquiv e).toFun))
(respectsEquivEquiv {S T : Structure} {e₁ e₂ : S ≃ T} (η : e₁ ≃ e₂) : compFun.congrArg_right (G := FF T) (FS.respectsEquiv η).toFunEquiv • mapEquiv e₁ ≈ mapEquiv e₂)

variable (D : StructureDependencyFunctorDesc)

def structureDependency (S : Structure) : StructureDependency := ⟨D.FS S, D.FF S⟩

def mkFunctor_equiv {S T : Structure} (e : S ≃ T) :
  structureDependency D S ≃ structureDependency D T :=
⟨D.FS.mapEquiv e, D.mapEquiv e⟩

def mkFunctor_respectsEquiv {S T : Structure} {e₁ e₂ : S ≃ T} (η : e₁ ≃ e₂) :
  StructureDependencyEquiv.StructureDependencyEquivEquiv (mkFunctor_equiv D e₁) (mkFunctor_equiv D e₂) :=
⟨D.FS.respectsEquiv η, D.respectsEquivEquiv η⟩

def mkFunctor_respectsComp {S T U : Structure} (e : S ≃ T) (f : T ≃ U) :
  StructureDependencyEquiv.StructureDependencyEquivEquiv (mkFunctor_equiv D (f • e)) (mkFunctor_equiv D f • mkFunctor_equiv D e) :=
⟨D.FS.respectsComp e f, sorry⟩

def mkFunctor : StructureFunctor universeStructure structureDependencyStructure :=
{ map     := structureDependency D,
  functor := { mapEquiv  := mkFunctor_equiv D,
               isFunctor := { respectsSetoid := λ ⟨η⟩ => ⟨mkFunctor_respectsEquiv D η⟩,
                              respectsComp   := λ e f => ⟨mkFunctor_respectsComp D e f⟩,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

end structureDependencyStructure

def setoidMap (C : StructureDependency) := setoidStructure ∘ C.F.map

end StructureDependency

open StructureDependency



-- A structure that represents a functorial version of the type `∀ a : C.S, C.F a`.
--
-- Since `C.F` is a functor, `e : a ≃ b` induces an `e' : C.F a ≃ C.F b`. We then require an
-- `F : PiExpr C` to produce an instance equivalence between `F a : C.F a` and `F b : C.F b`.
-- As a special case, if `C.F` is constant, this ensures that `F` is a functor.
--
-- Since equivalence of equivalences in `C.S` is just a proposition, we cannot meaningfully compare two
-- results of `mapEquiv` even if the inputs are equivalent: For `h : e₁ ≈ e₂`, we would need something
-- along the lines of `mapEquiv e₁ ≈[respectsSetoid C.F h] mapEquiv e₂`, but such an expression only makes
-- sense with an object inside the brackets, not with a proof.
-- Therefore, we include a setoid truncation in `mapEquiv` so that its result is just a proof.

structure PiExpr (C : StructureDependency) where
(map                              : Pi (setoidMap C))
(mapEquiv {a b : C.S} (e : a ≃ b) : map a ≈[congrArg C.F e] map b)

namespace PiExpr

instance (C : StructureDependency) : CoeFun (PiExpr C) (λ _ => ∀ a : C.S, C.F a) := ⟨PiExpr.map⟩

def congrArg {C : StructureDependency} (F : PiExpr C) {a b : C.S} (e : a ≃ b) : F a ≈[congrArg C.F e] F b :=
F.mapEquiv e

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
  mapEquiv := λ e => congrArg G (StructureFunctor.congrArg F e) }

def constPiToFun {S T : Structure} (F : PiExpr (StructureDependency.constDep S T)) :
  StructureFunctor S (setoidStructure T) :=
makeToSetoidStructureFunctor F.map F.mapEquiv

def funToConstPi {S T : Structure} (F : StructureFunctor S (setoidStructure T)) :
  PiExpr (StructureDependency.constDep S T) :=
{ map      := F.map,
  mapEquiv := F.functor.mapEquiv }

def transportPi {C D : StructureDependency} (φ : StructureDependencyEquiv C D) :
  PiExpr C → PiExpr D :=
let θ := StructureDependencyEquiv.invFunEquiv φ;
λ G => { map      := λ a => (θ.ext a).toFun (G (φ.e.invFun a)),
         mapEquiv := λ {a b} e => let ⟨n⟩ := θ.nat e;
                                  let ⟨m⟩ := congrArg G (StructureFunctor.congrArg φ.e.invFun e);
                                  ⟨IsEquivalence.trans (n.toFunEquiv.ext (G (φ.e.invFun a))) (StructureFunctor.congrArg (θ.ext b).toFun m)⟩ }

def dependentApplicationFunctor {S T : Structure} {F : UniverseFunctor S}
                                (G : PiExpr ⟨S, functorStructure.incomingFunctorFunctor T ⊙ F⟩)
                                (x : PiExpr ⟨S, F⟩) :
  SetoidStructureFunctor S T :=
makeSetoidStructureFunctor (λ a => (G a).map (x a))
                           (λ {a b} ⟨e⟩ => let ⟨h₁⟩ := congrArg G e;
                                           let ⟨h₂⟩ := congrArg x e;
                                           let h₃ := StructureFunctor.congr h₁ h₂;
                                           let h₄ := StructureFunctor.congrArg (G a) ((StructureFunctor.congrArg F e).isInv.leftInv.ext (x a));
                                           ⟨IsEquivalence.trans (IsEquivalence.symm h₄) h₃⟩)



namespace piStructure

instance (C : StructureDependency) : CoeFun (IsType.type (piStructure C)) (λ _ => ∀ a : C.S, C.F a) := ⟨PiExpr.map⟩

-- An independent `PiExpr` is the same as a functor (to a setoid structure).

section constDep

variable (S T : Structure)

@[reducible] def constDepPi  := piStructure (StructureDependency.constDep S T)
@[reducible] def constDepFun := functorStructure S (setoidStructure T)

def constDepToFun : StructureFunctor (constDepPi S T) (constDepFun S T) :=
{ map     := constPiToFun,
  functor := { mapEquiv  := λ η => makeToSetoidStructureFunctorEquiv' η,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ η θ => Setoid.refl (θ • η),
                              respectsId     := λ F   => Setoid.refl (id__ F),
                              respectsInv    := λ η   => Setoid.refl η⁻¹ } } }

def constDepInvFun : StructureFunctor (constDepFun S T) (constDepPi S T) :=
{ map     := funToConstPi,
  functor := { mapEquiv  := λ η => η.ext,
               isFunctor := { respectsSetoid := id,
                              respectsComp   := λ η θ => Setoid.refl (θ • η),
                              respectsId     := λ F   => Setoid.refl (id__ F),
                              respectsInv    := λ η   => Setoid.refl η⁻¹ } } }

def constDepEquiv : StructureEquiv (constDepPi S T) (constDepFun S T) :=
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
def piStructureFunctor_toFun {C D : StructureDependency} (φ : StructureDependencyEquiv C D) :
  StructureFunctor (piStructure C) (piStructure D) :=
let θ := StructureDependencyEquiv.invFunEquiv φ;
{ map     := transportPi φ,
  functor := { mapEquiv  := λ η a => StructureFunctor.congrArg (setoidFunctor (θ.ext a).toFun) (η (φ.e.invFun a)),
               isFunctor := { respectsSetoid := λ _ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ _ => proofIrrel _ _,
                              respectsId     := λ _   _ => proofIrrel _ _,
                              respectsInv    := λ _   _ => proofIrrel _ _ } } }

def piStructureFunctor_equiv {C D : StructureDependency} (φ : StructureDependencyEquiv C D) :
  piStructure C ≃ piStructure D :=
{ toFun  := piStructureFunctor_toFun φ,
  invFun := piStructureFunctor_toFun (StructureDependencyEquiv.symm φ),
  isInv  := sorry }

def piStructureFunctor : UniverseFunctor structureDependencyStructure :=
{ map     := piStructure,
  functor := { mapEquiv  := piStructureFunctor_equiv,
               isFunctor := sorry } }

def piStructureDependency : StructureDependency := ⟨structureDependencyStructure, piStructureFunctor⟩

def piStructureMkFunctor (D : structureDependencyStructure.StructureDependencyFunctorDesc) :
  UniverseStructureFunctor :=
{ map           := λ S => piStructure (structureDependencyStructure.structureDependency D S),
  mapEquiv      := λ e => piStructureFunctor_equiv (structureDependencyStructure.mkFunctor_equiv D e),
  respectsEquiv := sorry,
  respectsComp  := sorry,
  respectsId    := sorry,
  respectsInv   := sorry }

end piStructure

end PiExpr

open PiExpr



-- A Σ expression of structures.

def SigmaExpr (C : StructureDependency) := Σ' a : C.S, IsType.type (setoidMap C a)

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



def transportSigma {C D : StructureDependency} (φ : StructureDependencyEquiv C D) :
  SigmaExpr C → SigmaExpr D :=
λ s => ⟨φ.e.toFun s.fst, (φ.η.ext s.fst).toFun s.snd⟩



namespace sigmaStructure

-- Introduction and projections of `sigmaStructure` are functorial.

section MkProj

variable (C : StructureDependency)

def mkSndFunctor : UniverseFunctor C.S :=
functorStructure.incomingFunctorFunctor (sigmaStructure C) ⊙ C.F

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
⟨{ ext := λ b       => ⟨e, ⟨(StructureFunctor.congrArg C.F e).isInv.rightInv.ext b⟩⟩,
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

theorem transportSnd {C D : StructureDependency} (φ : StructureDependencyEquiv C D)
                     {s t : SigmaExpr C} (e : SigmaEquiv s t) :
  (φ.η.ext s.fst).toFun s.snd ≈[congrArg (D.F ⊙ φ.e.toFun) e.fst] (φ.η.ext t.fst).toFun t.snd :=
let ⟨f⟩ := φ.η.nat e.fst;
let h₁ := ⟨f.toFunEquiv.ext s.snd⟩;
let h₂ := StructureFunctor.congrArg (setoidFunctor (φ.η.ext t.fst).toFun) e.snd;
Setoid.trans h₁ h₂

-- TODO: Why does `C ≃ D` not work?
def sigmaStructureFunctor_toFun {C D : StructureDependency} (φ : StructureDependencyEquiv C D) :
  StructureFunctor (sigmaStructure C) (sigmaStructure D) :=
{ map     := transportSigma φ,
  functor := { mapEquiv  := λ {s t} e => ⟨congrArg φ.e.toFun e.fst, transportSnd φ e⟩,
               isFunctor := { respectsSetoid := λ h   => respectsSetoid φ.e.toFun h,
                              respectsComp   := λ e f => respectsComp   φ.e.toFun e.fst f.fst,
                              respectsId     := λ s   => respectsId     φ.e.toFun s.fst,
                              respectsInv    := λ e   => respectsInv    φ.e.toFun e.fst } } }

def sigmaStructureFunctor_equiv {C D : StructureDependency} (φ : StructureDependencyEquiv C D) :
  sigmaStructure C ≃ sigmaStructure D :=
{ toFun  := sigmaStructureFunctor_toFun φ,
  invFun := sigmaStructureFunctor_toFun (StructureDependencyEquiv.symm φ),
  isInv  := sorry }

def sigmaStructureFunctor : UniverseFunctor structureDependencyStructure :=
{ map     := sigmaStructure,
  functor := { mapEquiv  := sigmaStructureFunctor_equiv,
               isFunctor := sorry } }

def sigmaStructureDependency : StructureDependency := ⟨structureDependencyStructure, sigmaStructureFunctor⟩

end sigmaStructure

end SigmaExpr

open SigmaExpr



-- TODO: Define richer Π and Σ structures where the left side is a structure.
-- Looks like we need `nestedPiFunctor` to be a `UniverseStructureFunctor` then. Is it possible?



-- Analogously to the equivalences in `ProductStructure.lean`, we have equivalences between dependent
-- structures. However, since the left side of a dependent structure always requires more data than
-- the right side, we need to restrict ourselves to the case that the first variable is a structure,
-- the second variable is any instance of any structure, and the third argument is an instance of a
-- setoid structure.
--
-- TODO: We may be able to give a somewhat general definition of the word "canonical" based on these
-- equivalences.

namespace PiSigmaEquivalences

section InnerPair

variable (F : UniverseStructureFunctor)

def innerPairStructure := sigmaStructure ⟨universeStructure, UniverseStructureFunctor.universeFunctor F⟩

-- `b ↦ ⟨A, b⟩`
def innerPairFunctor (A : Structure) : StructureFunctor (F A) (innerPairStructure F) :=
sigmaStructure.mkExprFunctor ⟨universeStructure, UniverseStructureFunctor.universeFunctor F⟩ A

end InnerPair

def NestedDependency := Σ' F : UniverseStructureFunctor, UniverseFunctor (innerPairStructure F)

variable (D : NestedDependency)

def innerPairDependency : StructureDependency := ⟨innerPairStructure D.fst, D.snd⟩

-- `b ↦ D.snd ⟨A, b⟩`
def resultFunctor (A : Structure) : UniverseFunctor (D.fst A) :=
D.snd ⊙ innerPairFunctor D.fst A

-- `A ↦ (b ↦ D.snd ⟨A, b⟩)`
def innerDependencyFunctorDesc : structureDependencyStructure.StructureDependencyFunctorDesc :=
{ FS                 := D.fst,
  FF                 := resultFunctor D,
  mapEquiv           := sorry,
  respectsEquivEquiv := sorry }

def innerDependencyFunctor : StructureFunctor universeStructure structureDependencyStructure :=
StructureDependency.structureDependencyStructure.mkFunctor (innerDependencyFunctorDesc D)



-- `(∀ A : Structure, ∀ b : F A, G A b) ≃ (∀ ⟨A, b⟩ : (Σ A : Structure, F A), G A b)`
-- (`(λ A b => g A b) ↦ (λ ⟨A, b⟩ => g A b)`)

-- `A ↦ ∀ b : D.fst A, D.snd ⟨A, b⟩`
def nestedPiFunctor : UniverseFunctor universeStructure := piStructure.piStructureFunctor ⊙ innerDependencyFunctor D
def nestedPiDependency : StructureDependency := ⟨universeStructure, nestedPiFunctor D⟩

@[reducible] def piPiCurried   := piStructure (nestedPiDependency  D)
@[reducible] def piPiUncurried := piStructure (innerPairDependency D)

def piPiEquivToFun  : StructureFunctor (piPiCurried   D) (piPiUncurried D) :=
{ map     := λ g => ⟨λ ⟨a, b⟩ => (g a).map b, sorry⟩,
  functor := sorry }

def piPiEquivInvFun : StructureFunctor (piPiUncurried D) (piPiCurried   D) :=
{ map     := λ g => ⟨λ a => ⟨λ b => g ⟨a, b⟩, sorry⟩, sorry⟩,
  functor := sorry }

def piPiEquiv : StructureEquiv (piPiCurried D) (piPiUncurried D) :=
{ toFun  := piPiEquivToFun  D,
  invFun := piPiEquivInvFun D,
  isInv  := sorry }

-- `(Σ A : Structure, Σ b : F A, G A b) ≃ (Σ ⟨A, b⟩ : (Σ A : Structure, F A), G A b)`
-- (`⟨A, ⟨b, c⟩⟩ ↦ ⟨⟨A, b⟩, c⟩`)

-- `A ↦ Σ b : D.fst A, D.snd ⟨A, b⟩`
def nestedSigmaFunctor : UniverseFunctor universeStructure := sigmaStructure.sigmaStructureFunctor ⊙ innerDependencyFunctor D
def nestedSigmaDependency : StructureDependency := ⟨universeStructure, nestedSigmaFunctor D⟩

def sigmaSigmaCurried   := sigmaStructure (nestedSigmaDependency D)
def sigmaSigmaUncurried := sigmaStructure (innerPairDependency   D)

def sigmaSigmaEquivToFun  : StructureFunctor (sigmaSigmaCurried   D) (sigmaSigmaUncurried D) :=
{ map     := λ ⟨A, ⟨b, c⟩⟩ => ⟨⟨A, b⟩, c⟩,
  functor := { mapEquiv  := λ ⟨e, he⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquivInvFun : StructureFunctor (sigmaSigmaUncurried D) (sigmaSigmaCurried   D) :=
{ map     := λ ⟨⟨A, b⟩, c⟩ => ⟨A, ⟨b, c⟩⟩,
  functor := { mapEquiv  := λ ⟨⟨e, f⟩, g⟩ => sorry,
               isFunctor := { respectsSetoid := sorry,
                              respectsComp   := sorry,
                              respectsId     := sorry,
                              respectsInv    := sorry } } }

def sigmaSigmaEquiv : StructureEquiv (sigmaSigmaCurried D) (sigmaSigmaUncurried D) :=
{ toFun  := sigmaSigmaEquivToFun  D,
  invFun := sigmaSigmaEquivInvFun D,
  isInv  := sorry }

-- `(∀ A : Structure, Σ b : F A, G A b) ≃ (Σ f : (∀ A : Structure, F A), ∀ A : Structure, G A (f A))`
-- (`(λ A => ⟨f A, g A (f A)⟩ ↦ ⟨λ A => f A, λ A => g A (f A)⟩`)

-- TODO

end PiSigmaEquivalences

end PiSigma
