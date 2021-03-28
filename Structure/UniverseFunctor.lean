import Structure.Basic

open Structure
open StructureFunctor
open Forgetfulness



@[reducible] def UniverseFunctor (S : Structure) := StructureFunctor S universeStructure
@[reducible] def UniverseStructureFunctor := UniverseFunctor universeStructure



-- A helper structure for constructing a `UniverseFunctor`.
-- Instead of directly specifying the resulting structure equivalence, we only give its `toFun` because
-- the `invFun` can be obtained by inverting the input equivalence. By stating the functor axioms in terms
-- of `toFun`, we can ensure that the result is indeed a functor.

structure UniverseFunctorDesc (S : Structure) where
(map                                                                  : S → universeStructure)
(toFun          {α β   : S} (e : α ≃ β)                               : SetoidStructureFunctor (map α) (map β))
(respectsSetoid {α β   : S} {e₁ e₂ : α ≃ β} (h : e₁ ≈ e₂) (T : map α) : toFun e₁ T ≈ toFun e₂ T)
(respectsComp   {α β γ : S} (e : α ≃ β) (f : β ≃ γ)       (T : map α) : toFun (f • e) T ≈ toFun f (toFun e T))
(respectsId     (α     : S)                               (T : map α) : toFun (id_ α) T ≈ T)

namespace UniverseFunctorDesc

variable {S : Structure} (D : UniverseFunctorDesc S)

def targetLeftInv {α β : S} (e : α ≃ β) : compFun (D.toFun e) (D.toFun e⁻¹) ≃ idFun :=
makeToSetoidStructureFunctorEquiv (λ T => let h₁ := D.respectsComp e e⁻¹ T;
                                          let h₂ := D.respectsSetoid (leftInv e) T;
                                          let h₃ := Setoid.trans (Setoid.symm h₁) h₂
                                          let h₄ := D.respectsId α T;
                                          Setoid.trans h₃ h₄)

def targetRightInv {α β : S} (e : α ≃ β) : compFun (D.toFun e⁻¹) (D.toFun e) ≃ idFun :=
makeToSetoidStructureFunctorEquiv (λ T => let h₁ := D.respectsComp e⁻¹ e T;
                                          let h₂ := D.respectsSetoid (rightInv e) T;
                                          let h₃ := Setoid.trans (Setoid.symm h₁) h₂
                                          let h₄ := D.respectsId β T;
                                          Setoid.trans h₃ h₄)

def targetEquiv {α β : S} (e : α ≃ β) : D.map α ≃ D.map β :=
{ toFun    := D.toFun e,
  invFun   := D.toFun e⁻¹,
  leftInv  := targetLeftInv  D e,
  rightInv := targetRightInv D e }

theorem targetRespectsSetoid {α β : S} {e₁ e₂ : α ≃ β} (h : e₁ ≈ e₂) :
  D.toFun e₁ ≈ D.toFun e₂ :=
⟨makeToSetoidStructureFunctorEquiv (D.respectsSetoid h)⟩

theorem targetRespectsComp {α β γ : S} (e : α ≃ β) (f : β ≃ γ) :
  D.toFun (f • e) ≈ compFun (D.toFun e) (D.toFun f) :=
⟨makeToSetoidStructureFunctorEquiv (D.respectsComp e f)⟩

theorem targetRespectsCompInv {α β γ : S} (e : α ≃ β) (f : β ≃ γ) :
  D.toFun (f • e)⁻¹ ≈ compFun (D.toFun f⁻¹) (D.toFun e⁻¹) :=
⟨makeToSetoidStructureFunctorEquiv (λ T => let h₁ := D.respectsComp f⁻¹ e⁻¹ T;
                                           let h₂ := D.respectsSetoid (compInv e f) T;
                                           Setoid.trans h₂ h₁)⟩

theorem targetRespectsId (α : S) :
  D.toFun (id_ α) ≈ idFun :=
⟨makeToSetoidStructureFunctorEquiv (D.respectsId α)⟩

theorem targetRespectsIdInv (α : S) :
  D.toFun (id_ α)⁻¹ ≈ idFun :=
⟨makeToSetoidStructureFunctorEquiv (λ T => let h₁ := D.respectsId α T;
                                           let h₂ := D.respectsSetoid (idInv α) T;
                                           Setoid.trans h₂ h₁)⟩

theorem targetRespectsInvInv {α β : S} (e : α ≃ β) :
  D.toFun (e⁻¹)⁻¹ ≈ D.toFun e :=
⟨makeToSetoidStructureFunctorEquiv (D.respectsSetoid (invInv e))⟩

def functor : UniverseFunctor S :=
{ map     := D.map,
  functor := { FF        := targetEquiv D,
               isFunctor := { respectsSetoid := λ h   => ⟨targetRespectsSetoid D h,
                                                          targetRespectsSetoid D (congrArgInv h)⟩,
                              respectsComp   := λ e f => ⟨targetRespectsComp    D e f,
                                                          targetRespectsCompInv D e f⟩,
                              respectsId     := λ α   => ⟨targetRespectsId    D α,
                                                          targetRespectsIdInv D α⟩,
                              respectsInv    := λ e   => ⟨Setoid.refl (D.toFun e⁻¹),
                                                          targetRespectsInvInv D e⟩ } } }

end UniverseFunctorDesc

instance {S : Structure} : Coe (UniverseFunctorDesc S) (UniverseFunctor S) := ⟨UniverseFunctorDesc.functor⟩



-- The function `setoidStructure`, which coerces the equivalences of a structure to setoids, is a functor.
-- Note that the equivalences that this functor receives are already setoids, so in a way the functor does
-- not actually have any effect. However, it can be used to mitigate the mismatch between structures and
-- their equivalences within `universeStructure`.

theorem toSetoidStructureFunctorRespectsSetoid {S T : Structure} {f₁ f₂ : SetoidStructureFunctor S T} :
  f₁ ≈ f₂ → setoidFunctor f₁ ≈ setoidFunctor f₂ :=
λ ⟨e⟩ => ⟨makeToSetoidStructureFunctorEquiv' (λ α : setoidStructure S => ⟨e.ext α⟩)⟩

theorem toSetoidStructureEquivRespectsSetoid {S T : Structure} {e₁ e₂ : SetoidStructureEquiv S T} :
  e₁ ≈ e₂ → toSetoidStructureEquiv e₁ ≈ toSetoidStructureEquiv e₂ :=
λ ⟨l, r⟩ => ⟨toSetoidStructureFunctorRespectsSetoid l, toSetoidStructureFunctorRespectsSetoid r⟩

theorem toSetoidStructureFunctorRespectsComp {S T U : Structure} (f : SetoidStructureFunctor S T) (g : SetoidStructureFunctor T U) :
  setoidFunctor (compFun f g) ≈ compFun (setoidFunctor f) (setoidFunctor g) :=
⟨makeToSetoidStructureFunctorEquiv' (λ α : setoidStructure S => ⟨IsEquivalence.refl (g (f α))⟩)⟩

theorem toSetoidStructureEquivRespectsComp {S T U : Structure} (e : SetoidStructureEquiv S T) (f : SetoidStructureEquiv T U) :
  toSetoidStructureEquiv (SetoidStructureEquiv.trans e f) ≈ SetoidStructureEquiv.trans (toSetoidStructureEquiv e) (toSetoidStructureEquiv f) :=
⟨toSetoidStructureFunctorRespectsComp e.toFun f.toFun, toSetoidStructureFunctorRespectsComp f.invFun e.invFun⟩

theorem toSetoidStructureFunctorRespectsId (S : Structure) :
  setoidFunctor (@idFun (setoidStructure S)) ≈ @idFun (setoidStructure (setoidStructure S)) :=
⟨makeToSetoidStructureFunctorEquiv' (λ α : setoidStructure S => ⟨IsEquivalence.refl α⟩)⟩

theorem toSetoidStructureEquivRespectsId (S : Structure) :
  toSetoidStructureEquiv (SetoidStructureEquiv.refl S) ≈ SetoidStructureEquiv.refl (setoidStructure S) :=
⟨toSetoidStructureFunctorRespectsId S, toSetoidStructureFunctorRespectsId S⟩

theorem toSetoidStructureEquivRespectsInv {S T : Structure} (e : SetoidStructureEquiv S T) :
  toSetoidStructureEquiv (SetoidStructureEquiv.symm e) ≈ SetoidStructureEquiv.symm (toSetoidStructureEquiv e) :=
⟨Setoid.refl (setoidFunctor e.invFun), Setoid.refl (setoidFunctor e.toFun)⟩

def toSetoidStructureFunctor : UniverseStructureFunctor :=
{ map     := setoidStructure,
  functor := { FF        := toSetoidStructureEquiv,
               isFunctor := { respectsSetoid := toSetoidStructureEquivRespectsSetoid,
                              respectsComp   := toSetoidStructureEquivRespectsComp,
                              respectsId     := toSetoidStructureEquivRespectsId,
                              respectsInv    := toSetoidStructureEquivRespectsInv } } }

def strictUniverseFunctor {S : Structure} (F : UniverseFunctor S) : UniverseFunctor S :=
compFun F toSetoidStructureFunctor
