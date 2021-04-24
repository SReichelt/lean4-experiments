--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- Helpers for the construction of functors into `universeStructure`.



import Structure.Basic
import Structure.Forgetfulness

open Morphisms
open HasStructure
open Structure
open GeneralizedFunctor
open StructureFunctor
open Forgetfulness
open SetoidStructureFunctor
open SetoidStructureEquiv



set_option autoBoundImplicitLocal false



-- Aliases for functors into `universeStructure`.

@[reducible] def UniverseFunctor (S : Structure) := StructureFunctor S universeStructure



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



-- The function `setoidStructure`, which truncates the equivalences of a structure to setoids, is a
-- `UniverseFunctor`.

def structureToSetoidStructureFunctor' : SetoidUniverseFunctor universeStructure :=
{ map     := id,
  functor := toSetoidStructureEquiv.genFun }

def setoidUniverseFunctor {S : Structure} (F : UniverseFunctor S) : SetoidUniverseFunctor S :=
SetoidUniverseFunctor.compFun F structureToSetoidStructureFunctor'

def structureToSetoidStructureFunctor : UniverseFunctor universeStructure :=
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
                                      (D.respectsSetoid (inv_congrArg h))⟩

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
  functor := { mapEquiv  := targetEquiv D,
               isFunctor := { respectsSetoid := targetRespectsSetoid D,
                              respectsComp   := targetRespectsComp   D,
                              respectsId     := targetRespectsId     D,
                              respectsInv    := targetRespectsInv    D } } }

def universeFunctor : UniverseFunctor S := SetoidUniverseFunctor.universeFunctor (setoidUniverseFunctor D)

end SetoidUniverseFunctorDesc

instance {S : Structure} : Coe (SetoidUniverseFunctorDesc S) (SetoidUniverseFunctor S) := ⟨SetoidUniverseFunctorDesc.setoidUniverseFunctor⟩
instance {S : Structure} : Coe (SetoidUniverseFunctorDesc S) (UniverseFunctor S)       := ⟨SetoidUniverseFunctorDesc.universeFunctor⟩



-- A 2-functor specifically between universe structures. I.e. we have a functor between structures and a
-- functor between equivalences.

structure UniverseStructureFunctor where
(map                                                       : Structure → Structure)
(mapEquiv      {S T   : Structure}                         : S ≃ T → map S ≃ map T)
(respectsEquiv {S T   : Structure}                         : GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure S T) (T := StructureEquiv.equivStructure (map S) (map T)) mapEquiv)
(respectsComp  {S T U : Structure} (e : S ≃ T) (f : T ≃ U) : mapEquiv (f • e) ≃ mapEquiv f • mapEquiv e)
-- TODO: Why don't `≃` and `id_` work as they should here?
(respectsId    (S     : Structure)                         : StructureEquiv.EquivEquiv (mapEquiv (id_ S)) (StructureEquiv.refl (map S)))
(respectsInv   {S T   : Structure} (e : S ≃ T)             : mapEquiv e⁻¹ ≃ (mapEquiv e)⁻¹)

namespace UniverseStructureFunctor

instance universeStructureFunctorCoeFun : CoeFun UniverseStructureFunctor (λ _ => Structure → Structure) := ⟨UniverseStructureFunctor.map⟩

variable (F : UniverseStructureFunctor)

def congrArg {S T : Structure} (e : S ≃ T) : F S ≃ F T := F.mapEquiv e

def universeFunctor : UniverseFunctor universeStructure :=
{ map     := F.map,
  functor := { mapEquiv  := F.mapEquiv,
               isFunctor := { respectsSetoid := λ ⟨η⟩ => ⟨F.respectsEquiv η⟩,
                              respectsComp   := λ e f => ⟨F.respectsComp  e f⟩,
                              respectsId     := λ S   => ⟨F.respectsId    S⟩,
                              respectsInv    := λ e   => ⟨F.respectsInv   e⟩ } } }

end UniverseStructureFunctor

instance : Coe UniverseStructureFunctor (UniverseFunctor universeStructure) := ⟨UniverseStructureFunctor.universeFunctor⟩



-- Similar to `SetoidUniverseFunctorDesc`, but constructs a `UniverseStructureFunctor` producing regular
-- structures without any truncation to setoids. This is possible because equivalences of structure
-- equivalences also come in a non-setoid form.

structure UniverseStructureFunctorDesc where
(map                                                       : Structure → Structure)
(toFun         {S T   : Structure}                         : S ≃ T → StructureFunctor (map S) (map T))
(respectsEquiv {S T   : Structure}                         : GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure S T) (T := functorStructure (map S) (map T)) toFun)
(respectsComp  {S T U : Structure} (e : S ≃ T) (f : T ≃ U) : toFun (f • e) ≃ toFun f ⊙ toFun e)
(respectsCompNat {S T U : Structure} {e₁ e₂ : S ≃ T} {f₁ f₂ : T ≃ U} (η : e₁ ≃ e₂) (θ : f₁ ≃ f₂) :
   compFun.congrArg (respectsEquiv η) (respectsEquiv θ) • respectsComp e₁ f₁ ≈ respectsComp e₂ f₂ • respectsEquiv (StructureEquiv.comp_congrArg η θ))
(respectsId    (S     : Structure)                         : toFun (id_ S) ≃ @idFun (map S))

namespace UniverseStructureFunctorDesc

variable (D : UniverseStructureFunctorDesc)

-- TODO: We can probably make use of `toFunFunctor` somehow in order to make the missing proofs easier.

def toFunFunctor (S T : Structure) : StructureFunctor (StructureEquiv.equivStructure S T) (functorStructure (D.map S) (D.map T)) :=
{ map     := D.toFun,
  functor := D.respectsEquiv }

def targetLeftInv {S T : Structure} (e : S ≃ T) : D.toFun e⁻¹ ⊙ D.toFun e ≃ @idFun (D.map S) :=
let η₁ := FunctorEquiv.symm (D.respectsComp e e⁻¹);
let η₂ := D.respectsEquiv (StructureEquiv.leftInv' e);
FunctorEquiv.trans (FunctorEquiv.trans η₁ η₂) (D.respectsId S)

def targetRightInv {S T : Structure} (e : S ≃ T) : D.toFun e ⊙ D.toFun e⁻¹ ≃ @idFun (D.map T) :=
let η₁ := FunctorEquiv.symm (D.respectsComp e⁻¹ e);
let η₂ := D.respectsEquiv (StructureEquiv.rightInv' e);
FunctorEquiv.trans (FunctorEquiv.trans η₁ η₂) (D.respectsId T)

-- This might simplify some proofs.
theorem targetInv {S T : Structure} (e : S ≃ T) :
  targetRightInv D e ≈ StructureEquiv.symm_symm e ▸ targetLeftInv D e⁻¹ :=
sorry

def targetEquiv {S T : Structure} (e : S ≃ T) : StructureEquiv (D.map S) (D.map T) :=
{ toFun  := D.toFun e,
  invFun := D.toFun e⁻¹,
  isInv  := { leftInv  := targetLeftInv  D e,
              rightInv := targetRightInv D e,
              lrCompat := sorry,
              rlCompat := sorry } }

def targetRespectsEquiv {S T : Structure} {e₁ e₂ : S ≃ T} (η : e₁ ≃ e₂) :
  targetEquiv D e₁ ≃ targetEquiv D e₂ :=
{ toFunEquiv    := D.respectsEquiv η,
  invFunEquiv   := D.respectsEquiv (StructureEquiv.inv_congrArg η),
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def targetEquiv.functor {S T : Structure} :
  GeneralizedFunctor.Functor (S := StructureEquiv.equivStructure S T) (T := StructureEquiv.equivStructure (D.map S) (D.map T)) (targetEquiv D) :=
{ mapEquiv  := targetRespectsEquiv D,
  isFunctor := sorry }

def targetRespectsComp {S T U : Structure} (e : S ≃ T) (f : T ≃ U) :
  targetEquiv D (StructureEquiv.trans e f) ≃ StructureEquiv.trans (targetEquiv D e) (targetEquiv D f) :=
{ toFunEquiv    := D.respectsComp e   f,
  invFunEquiv   := D.respectsComp f⁻¹ e⁻¹,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def targetRespectsId (S : Structure) :
  targetEquiv D (StructureEquiv.refl S) ≃ StructureEquiv.refl (D.map S) :=
{ toFunEquiv    := D.respectsId S,
  invFunEquiv   := D.respectsId S,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def targetRespectsInv {S T : Structure} (e : S ≃ T) :
  targetEquiv D (StructureEquiv.symm e) ≃ StructureEquiv.symm (targetEquiv D e) :=
{ toFunEquiv    := FunctorEquiv.refl (D.toFun e⁻¹),
  invFunEquiv   := D.respectsEquiv (StructureEquiv.invInv e),
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def universeStructureFunctor : UniverseStructureFunctor :=
{ map            := D.map,
  mapEquiv       := targetEquiv         D,
  respectsEquiv  := targetEquiv.functor D,
  respectsComp   := targetRespectsComp  D,
  respectsId     := targetRespectsId    D,
  respectsInv    := targetRespectsInv   D }

def universeFunctor : UniverseFunctor universeStructure := UniverseStructureFunctor.universeFunctor (universeStructureFunctor D)

end UniverseStructureFunctorDesc

instance : Coe UniverseStructureFunctorDesc UniverseStructureFunctor := ⟨UniverseStructureFunctorDesc.universeStructureFunctor⟩
instance : Coe UniverseStructureFunctorDesc (UniverseFunctor universeStructure) := ⟨UniverseStructureFunctorDesc.universeFunctor⟩
