import Structure.Basic
import Structure.Forgetfulness

open Morphisms
open Structure
open GeneralizedFunctor
open StructureFunctor
open Forgetfulness
open SetoidStructureFunctor
open SetoidStructureEquiv



set_option autoBoundImplicitLocal false



-- Aliases for functors into `universeStructure`.

@[reducible] def UniverseFunctor (S : Structure) := StructureFunctor S universeStructure
@[reducible] def UniverseStructureFunctor := UniverseFunctor universeStructure



-- A special limitation of `UniverseFunctor S` for a generic `S` is that since equivalences of
-- equivalences in `S` are propositions, we can only map instances of `S` to setoid structures. The
-- definition of `UniverseFunctor` itself does not encode this knowledge, but sometimes we want to
-- restrict ourselves to this very frequent case. We can do this by replacing `UniverseFunctor` with
-- `SetoidUniverseFunctor` and then coercing it into a `UniverseFunctor`.

structure SetoidUniverseFunctor (S : Structure) :=
(map     : S → universeStructure)
(functor : Functor (T := universeStructure) (setoidStructure ∘ map))

namespace SetoidUniverseFunctor

def universeFunctor {S : Structure} (F : SetoidUniverseFunctor S) : UniverseFunctor S :=
{ map     := setoidStructure ∘ F.map,
  functor := F.functor }

instance {S : Structure} : Coe (SetoidUniverseFunctor S) (UniverseFunctor S) := ⟨universeFunctor⟩

def toSetoidUniverseFunctor {S : Structure} (F : UniverseFunctor S) : SetoidUniverseFunctor S :=
{ map     := F.map,
  functor := comp.genFun' F.map F.functor toSetoidStructureEquiv.genFun }

def compFun {S T : Structure} (F : StructureFunctor S T) (G : SetoidUniverseFunctor T) : SetoidUniverseFunctor S :=
{ map     := G.map ∘ F.map,
  functor := comp.genFun' F.map F.functor G.functor }

def constFun {S : Structure} (T : Structure) : SetoidUniverseFunctor S :=
{ map     := Function.const (IsType.type S) T,
  functor := const.genFun (setoidStructure T) }

end SetoidUniverseFunctor

@[reducible] def SetoidUniverseStructureFunctor := SetoidUniverseFunctor universeStructure



-- The function `setoidStructure`, which truncates the equivalences of a structure to setoids, is a
-- `UniverseStructureFunctor`.

def structureToSetoidStructureFunctor' : SetoidUniverseFunctor universeStructure :=
{ map     := id,
  functor := toSetoidStructureEquiv.genFun }

def setoidUniverseFunctor {S : Structure} (F : UniverseFunctor S) : SetoidUniverseFunctor S :=
SetoidUniverseFunctor.compFun F structureToSetoidStructureFunctor'

def structureToSetoidStructureFunctor : UniverseStructureFunctor :=
SetoidUniverseFunctor.universeFunctor structureToSetoidStructureFunctor'



-- A helper structure for constructing a `SetoidUniverseFunctor`, and thus indirectly also a
-- `UniverseFunctor`.
--
-- Instead of directly specifying the resulting structure equivalence, we only give its `toFun` because
-- the `invFun` can be obtained by inverting the input equivalence. By stating the functor axioms in terms
-- of `toFun`, we can ensure that the result is indeed a functor.
--
-- The limitation that we can only define functors to setoid structures is reflected in
-- `SetoidUniverseFunctorDesc` in two ways:
-- * `toFun` yields a `SetoidStructureFunctor` because for a given equivalence `e`, it would be
--   unrealistic to obtain a regular `StructureFunctor`.
-- * The `respects...` functions return proofs. Especially, `respectsSetoid` can only return a proof since
--   it takes a proof as an input.

structure SetoidUniverseFunctorDesc (S : Structure) where
(map                                                : S → Structure)
(toFun          {a b   : S}                         : a ≃ b → SetoidStructureFunctor (map a) (map b))
(respectsSetoid {a b   : S} {e₁ e₂ : a ≃ b}         : e₁ ≈ e₂ → ∀ T, toFun e₁ T ≈ toFun e₂ T)
(respectsComp   {a b c : S} (e : a ≃ b) (f : b ≃ c) : ∀ T, toFun (f • e) T ≈ toFun f (toFun e T))
(respectsId     (a     : S)                         : ∀ T, toFun (id_ a) T ≈ T)

namespace SetoidUniverseFunctorDesc

variable {S : Structure} (D : SetoidUniverseFunctorDesc S)

def targetLeftInv {a b : S} (e : a ≃ b) : D.toFun e⁻¹ ⊙ D.toFun e ≃ @idFun (setoidStructure (D.map a)) :=
makeToSetoidStructureFunctorEquiv (λ T => let h₁ := D.respectsComp e e⁻¹ T;
                                          let h₂ := D.respectsSetoid (leftInv e) T;
                                          let h₃ := Setoid.trans (Setoid.symm h₁) h₂;
                                          let h₄ := D.respectsId a T;
                                          Setoid.trans h₃ h₄)

def targetRightInv {a b : S} (e : a ≃ b) : D.toFun e ⊙ D.toFun e⁻¹ ≃ @idFun (setoidStructure (D.map b)) :=
makeToSetoidStructureFunctorEquiv (λ T => let h₁ := D.respectsComp e⁻¹ e T;
                                          let h₂ := D.respectsSetoid (rightInv e) T;
                                          let h₃ := Setoid.trans (Setoid.symm h₁) h₂
                                          let h₄ := D.respectsId b T;
                                          Setoid.trans h₃ h₄)

def targetEquiv {a b : S} (e : a ≃ b) : SetoidStructureEquiv (D.map a) (D.map b) :=
{ toFun  := D.toFun e,
  invFun := D.toFun e⁻¹,
  isInv  := makeSetoidStructureFunctorInverse (targetLeftInv D e) (targetRightInv D e) }

theorem targetRespectsSetoid {a b : S} {e₁ e₂ : a ≃ b} :
  e₁ ≈ e₂ → targetEquiv D e₁ ≈ targetEquiv D e₂ :=
λ h => ⟨makeSetoidStructureEquivEquiv (D.respectsSetoid h)
                                      (D.respectsSetoid (congrArgInv h))⟩

theorem targetRespectsComp {a b c : S} (e : a ≃ b) (f : b ≃ c) :
  targetEquiv D (f • e) ≈ StructureEquiv.trans (targetEquiv D e) (targetEquiv D f) :=
⟨makeSetoidStructureEquivEquiv (D.respectsComp e f)
                               (λ T => let h₁ := D.respectsComp f⁻¹ e⁻¹ T;
                                       let h₂ := D.respectsSetoid (compInv e f) T;
                                       Setoid.trans h₂ h₁)⟩

theorem targetRespectsId (a : S) :
  targetEquiv D (id_ a) ≈ StructureEquiv.refl (setoidStructure (D.map a)) :=
⟨makeSetoidStructureEquivEquiv (D.respectsId a)
                               (λ T => let h₁ := D.respectsId a T;
                                       let h₂ := D.respectsSetoid (idInv a) T;
                                       Setoid.trans h₂ h₁)⟩

theorem targetRespectsInv {a b : S} (e : a ≃ b) :
  targetEquiv D e⁻¹ ≈ StructureEquiv.symm (targetEquiv D e) :=
⟨makeSetoidStructureEquivEquiv (λ T => Setoid.refl (D.toFun e⁻¹ T))
                               (D.respectsSetoid (invInv e))⟩

def setoidUniverseFunctor : SetoidUniverseFunctor S :=
{ map     := D.map,
  functor := { FF        := targetEquiv D,
               isFunctor := { respectsSetoid := targetRespectsSetoid D,
                              respectsComp   := targetRespectsComp   D,
                              respectsId     := targetRespectsId     D,
                              respectsInv    := targetRespectsInv    D } } }

def universeFunctor : UniverseFunctor S := SetoidUniverseFunctor.universeFunctor (setoidUniverseFunctor D)

instance {S : Structure} : Coe (SetoidUniverseFunctorDesc S) (SetoidUniverseFunctor S) := ⟨setoidUniverseFunctor⟩
instance {S : Structure} : Coe (SetoidUniverseFunctorDesc S) (UniverseFunctor S)       := ⟨universeFunctor⟩

end SetoidUniverseFunctorDesc



-- Similar to `SetoidUniverseFunctorDesc`, but constructs a `UniverseStructureFunctor` producing regular
-- structures without any truncation to setoids. This is possible because equivalences of structure
-- equivalences also come in a non-setoid form.

structure UniverseStructureFunctorDesc where
(map                                                       : Structure → Structure)
(toFun         {S T   : Structure}                         : S ≃ T → StructureFunctor (map S) (map T))
(respectsEquiv {S T   : Structure}                         : GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure S T) (T := functorStructure (map S) (map T)) toFun)
(respectsComp  {S T U : Structure} (e : S ≃ T) (f : T ≃ U) : toFun (f • e) ≃ toFun f ⊙ toFun e)
(respectsId    (S     : Structure)                         : toFun (id_ S) ≃ @idFun (map S))

namespace UniverseStructureFunctorDesc

variable (D : UniverseStructureFunctorDesc)

def targetLeftInv {S T : Structure} (e : S ≃ T) : D.toFun e⁻¹ ⊙ D.toFun e ≃ @idFun (D.map S) :=
let φ₁ := FunctorEquiv.symm (D.respectsComp e e⁻¹);
let φ₂ := D.respectsEquiv (StructureEquiv.leftInv' e);
FunctorEquiv.trans (FunctorEquiv.trans φ₁ φ₂) (D.respectsId S)

def targetRightInv {S T : Structure} (e : S ≃ T) : D.toFun e ⊙ D.toFun e⁻¹ ≃ @idFun (D.map T) :=
let φ₁ := FunctorEquiv.symm (D.respectsComp e⁻¹ e);
let φ₂ := D.respectsEquiv (StructureEquiv.rightInv' e);
FunctorEquiv.trans (FunctorEquiv.trans φ₁ φ₂) (D.respectsId T)

def targetEquiv {S T : Structure} (e : S ≃ T) : StructureEquiv (D.map S) (D.map T) :=
{ toFun  := D.toFun e,
  invFun := D.toFun e⁻¹,
  isInv  := { leftInv  := targetLeftInv  D e,
              rightInv := targetRightInv D e,
              lrCompat := sorry,
              rlCompat := sorry } }

theorem targetRespectsSetoid {S T : Structure} {e₁ e₂ : S ≃ T} :
  e₁ ≈ e₂ → targetEquiv D e₁ ≈ targetEquiv D e₂ :=
λ ⟨φ⟩ => ⟨{ toFunEquiv    := D.respectsEquiv φ,
            invFunEquiv   := D.respectsEquiv (StructureEquiv.congrArgInv φ),
            leftInvEquiv  := sorry,
            rightInvEquiv := sorry }⟩

theorem targetRespectsComp {S T U : Structure} (e : S ≃ T) (f : T ≃ U) :
  targetEquiv D (StructureEquiv.trans e f) ≈ StructureEquiv.trans (targetEquiv D e) (targetEquiv D f) :=
⟨{ toFunEquiv    := D.respectsComp e   f,
   invFunEquiv   := D.respectsComp f⁻¹ e⁻¹,
   leftInvEquiv  := sorry,
   rightInvEquiv := sorry }⟩

theorem targetRespectsId (S : Structure) :
  targetEquiv D (StructureEquiv.refl S) ≈ StructureEquiv.refl (D.map S) :=
⟨{ toFunEquiv    := D.respectsId S,
   invFunEquiv   := D.respectsId S,
   leftInvEquiv  := sorry,
   rightInvEquiv := sorry }⟩

theorem targetRespectsInv {S T : Structure} (e : S ≃ T) :
  targetEquiv D (StructureEquiv.symm e) ≈ StructureEquiv.symm (targetEquiv D e) :=
⟨{ toFunEquiv    := FunctorEquiv.refl (D.toFun e⁻¹),
   invFunEquiv   := D.respectsEquiv (StructureEquiv.invInv e),
   leftInvEquiv  := sorry,
   rightInvEquiv := sorry }⟩

def universeStructureFunctor : UniverseStructureFunctor :=
{ map     := D.map,
  functor := { FF        := targetEquiv D,
               isFunctor := { respectsSetoid := targetRespectsSetoid D,
                              respectsComp   := targetRespectsComp   D,
                              respectsId     := targetRespectsId     D,
                              respectsInv    := targetRespectsInv    D } } }

instance {S : Structure} : Coe UniverseStructureFunctorDesc UniverseStructureFunctor := ⟨universeStructureFunctor⟩

end UniverseStructureFunctorDesc
