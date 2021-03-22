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
(respectsInv    {α β   : S} (e : α ≃ β)                   (T : map α) : toFun e⁻¹ (toFun e T) ≈ T)

namespace UniverseFunctorDesc

variable {S : Structure} (D : UniverseFunctorDesc S)

def targetEquiv {α β : S} (e : α ≃ β) : D.map α ≃ D.map β :=
{ toFun    := D.toFun e,
  invFun   := D.toFun e⁻¹,
  leftInv  := λ T => let ⟨h₁⟩ := D.respectsInv e T;
                     h₁,
  rightInv := λ T => let ⟨h₁⟩ := D.respectsInv e⁻¹ T;
                     let ⟨h₂⟩ := D.respectsSetoid (invInv e) (D.toFun e⁻¹ T);
                     IsEquivalence.trans (IsEquivalence.symm h₂) h₁ }

def targetRespectsSetoid {α β : S} {e₁ e₂ : α ≃ β} (h : e₁ ≈ e₂) : D.toFun e₁ ≃ D.toFun e₂ :=
λ T => let ⟨h₁⟩ := D.respectsSetoid h T;
       h₁

def targetRespectsComp {α β γ : S} (e : α ≃ β) (f : β ≃ γ) :
  D.toFun (f • e) ≃ compFun (D.toFun e) (D.toFun f) :=
λ T => let ⟨h₁⟩ := D.respectsComp e f T;
       h₁

def targetRespectsCompInv {α β γ : S} (e : α ≃ β) (f : β ≃ γ) :
  D.toFun (f • e)⁻¹ ≃ compFun (D.toFun f⁻¹) (D.toFun e⁻¹) :=
λ T => let ⟨h₁⟩ := D.respectsComp f⁻¹ e⁻¹ T;
       let ⟨h₂⟩ := D.respectsSetoid (compInv e f) T;
       IsEquivalence.trans h₂ h₁

def targetRespectsId (α : S) : D.toFun (id_ α) ≃ idFun :=
λ T => let ⟨h₁⟩ := D.respectsId α T;
       h₁

def targetRespectsIdInv (α : S) : D.toFun (id_ α)⁻¹ ≃ idFun :=
λ T => let ⟨h₁⟩ := D.respectsId α T;
       let ⟨h₂⟩ := D.respectsSetoid (idInv α) T;
       IsEquivalence.trans h₂ h₁

def targetRespectsInvInv {α β : S} (e : α ≃ β) : D.toFun (e⁻¹)⁻¹ ≃ D.toFun e :=
λ T => let ⟨h₁⟩ := D.respectsInv e T;
       let ⟨h₂⟩ := D.respectsInv e⁻¹ (D.toFun e T);
       let h₃ := congrArgMap (D.toFun (e⁻¹)⁻¹) h₁;
       IsEquivalence.trans (IsEquivalence.symm h₃) h₂

def functor : UniverseFunctor S :=
{ map     := D.map,
  functor := { FF        := targetEquiv D,
               isFunctor := { respectsSetoid := λ h   => ⟨⟨targetRespectsSetoid D h⟩,
                                                          ⟨targetRespectsSetoid D (congrArgInv h)⟩⟩,
                              respectsComp   := λ e f => ⟨⟨targetRespectsComp    D e f⟩,
                                                          ⟨targetRespectsCompInv D e f⟩⟩,
                              respectsId     := λ α   => ⟨⟨targetRespectsId    D α⟩,
                                                          ⟨targetRespectsIdInv D α⟩⟩,
                              respectsInv    := λ e   => ⟨Setoid.refl (D.toFun e⁻¹),
                                                          ⟨targetRespectsInvInv D e⟩⟩ } } }

end UniverseFunctorDesc

instance {S : Structure} : Coe (UniverseFunctorDesc S) (UniverseFunctor S) := ⟨UniverseFunctorDesc.functor⟩
