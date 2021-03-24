import Structure.Basic

open Structure
open StructureFunctor
open Forgetfulness



@[reducible] def UniverseFunctor (S : Structure) := StructureFunctor S universeStructure



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
λ T => let ⟨h₁⟩ := D.respectsComp e e⁻¹ T;
       let ⟨h₂⟩ := D.respectsSetoid (leftInv e) T;
       let h₃ := IsEquivalence.trans (IsEquivalence.symm h₁) h₂
       let ⟨h₄⟩ := D.respectsId α T;
       IsEquivalence.trans h₃ h₄

def targetRightInv {α β : S} (e : α ≃ β) : compFun (D.toFun e⁻¹) (D.toFun e) ≃ idFun :=
λ T => let ⟨h₁⟩ := D.respectsComp e⁻¹ e T;
       let ⟨h₂⟩ := D.respectsSetoid (rightInv e) T;
       let h₃ := IsEquivalence.trans (IsEquivalence.symm h₁) h₂
       let ⟨h₄⟩ := D.respectsId β T;
       IsEquivalence.trans h₃ h₄

def targetEquiv {α β : S} (e : α ≃ β) : D.map α ≃ D.map β :=
{ toFun    := D.toFun e,
  invFun   := D.toFun e⁻¹,
  leftInv  := targetLeftInv  D e,
  rightInv := targetRightInv D e }

theorem targetRespectsSetoid {α β : S} {e₁ e₂ : α ≃ β} (h : e₁ ≈ e₂) :
  D.toFun e₁ ≈ D.toFun e₂ :=
⟨λ T => let ⟨h₁⟩ := D.respectsSetoid h T;
        h₁⟩

theorem targetRespectsComp {α β γ : S} (e : α ≃ β) (f : β ≃ γ) :
  D.toFun (f • e) ≈ compFun (D.toFun e) (D.toFun f) :=
⟨λ T => let ⟨h₁⟩ := D.respectsComp e f T;
        h₁⟩

theorem targetRespectsCompInv {α β γ : S} (e : α ≃ β) (f : β ≃ γ) :
  D.toFun (f • e)⁻¹ ≈ compFun (D.toFun f⁻¹) (D.toFun e⁻¹) :=
⟨λ T => let ⟨h₁⟩ := D.respectsComp f⁻¹ e⁻¹ T;
        let ⟨h₂⟩ := D.respectsSetoid (compInv e f) T;
        IsEquivalence.trans h₂ h₁⟩

theorem targetRespectsId (α : S) :
  D.toFun (id_ α) ≈ idFun :=
⟨λ T => let ⟨h₁⟩ := D.respectsId α T;
        h₁⟩

theorem targetRespectsIdInv (α : S) :
  D.toFun (id_ α)⁻¹ ≈ idFun :=
⟨λ T => let ⟨h₁⟩ := D.respectsId α T;
        let ⟨h₂⟩ := D.respectsSetoid (idInv α) T;
        IsEquivalence.trans h₂ h₁⟩

theorem targetRespectsInvInv {α β : S} (e : α ≃ β) :
  D.toFun (e⁻¹)⁻¹ ≈ D.toFun e :=
⟨λ T => let ⟨h₁⟩ := D.respectsSetoid (invInv e) T;
        h₁⟩

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
