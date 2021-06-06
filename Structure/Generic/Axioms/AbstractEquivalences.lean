import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors

import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v



class HasExternalEquivalences (U : Universe.{u}) (V : Universe.{v})
                              [hUV : HasExternalFunctors U V] [hVU : HasExternalFunctors V U] : Type (max u v) where
(IsEquiv {α : U} {β : V} : (α ⟶' β) → (β ⟶' α) → Sort (max u v))

structure BundledEquivalence {U : Universe.{u}} {V : Universe.{v}}
                             [hUV : HasExternalFunctors U V] [hVU : HasExternalFunctors V U]
                             [h : HasExternalEquivalences U V]
                             (α : U) (β : V) : Sort (max 1 u v) where
(toFun   : α ⟶' β)
(invFun  : β ⟶' α)
(isEquiv : h.IsEquiv toFun invFun)

namespace BundledEquivalence

  infix:20 " ⟷' " => BundledEquivalence

  variable {U V : Universe} [hUV : HasExternalFunctors U V] [hVU : HasExternalFunctors V U]
           [h : HasExternalEquivalences U V]

  def mkEquiv {α : U} {β : V} {to : α ⟶' β} {inv : β ⟶' α} (he : h.IsEquiv to inv) : α ⟷' β :=
  ⟨to, inv, he⟩

end BundledEquivalence

class HasInternalEquivalences (U : Universe.{u}) [h : HasInternalFunctors U] extends HasExternalEquivalences U U : Type u where
(Equiv                          : U → U → U)
(equivEquiv           (α β : U) : ⌈Equiv α β⌉ ≃ (α ⟷' β))
(equivElimToFunIsFun  (α β : U) : h.IsFun (λ E : Equiv α β => HasInternalFunctors.fromBundled ((equivEquiv α β).toFun E).toFun))
(equivElimInvFunIsFun (α β : U) : h.IsFun (λ E : Equiv α β => HasInternalFunctors.fromBundled ((equivEquiv α β).toFun E).invFun))

namespace HasInternalEquivalences

  infix:20 " ⟷ " => HasInternalEquivalences.Equiv

  variable {U : Universe} [HasInternalFunctors U] [h : HasInternalEquivalences U]

  def toBundled   {α β : U} (E : α ⟷  β) : α ⟷' β := (h.equivEquiv α β).toFun  E
  def fromBundled {α β : U} (E : α ⟷' β) : α ⟷  β := (h.equivEquiv α β).invFun E

  @[simp] theorem fromToBundled {α β : U} (E : α ⟷  β) : fromBundled (toBundled E) = E :=
  (h.equivEquiv α β).leftInv  E
  @[simp] theorem toFromBundled {α β : U} (E : α ⟷' β) : toBundled (fromBundled E) = E :=
  (h.equivEquiv α β).rightInv E

  def to  {α β : U} (E : α ⟷ β) (a : α) : β := (toBundled E).toFun  a
  def inv {α β : U} (E : α ⟷ β) (b : β) : α := (toBundled E).invFun b

  def toFun  {α β : U} (E : α ⟷ β) : α ⟶ β := HasInternalFunctors.fromBundled (toBundled E).toFun
  def invFun {α β : U} (E : α ⟷ β) : β ⟶ α := HasInternalFunctors.fromBundled (toBundled E).invFun

  @[simp] theorem toFun.eff  {α β : U} (E : α ⟷ β) (a : α) : (toFun  E) a = to  E a :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem invFun.eff {α β : U} (E : α ⟷ β) (b : β) : (invFun E) b = inv E b :=
  by apply HasInternalFunctors.fromBundled.eff

  def toFunFun'  (α β : U) : (α ⟷ β) ⟶' (α ⟶ β) := BundledFunctor.mkFun (h.equivElimToFunIsFun  α β)
  def invFunFun' (α β : U) : (α ⟷ β) ⟶' (β ⟶ α) := BundledFunctor.mkFun (h.equivElimInvFunIsFun α β)
  def toFunFun   (α β : U) : (α ⟷ β) ⟶  (α ⟶ β) := HasInternalFunctors.fromBundled (toFunFun'  α β)
  def invFunFun  (α β : U) : (α ⟷ β) ⟶  (β ⟶ α) := HasInternalFunctors.fromBundled (invFunFun' α β)

  @[simp] theorem toFunFun.eff  {α β : U} (E : α ⟷ β) : (toFunFun  α β) E = toFun  E :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem invFunFun.eff {α β : U} (E : α ⟷ β) : (invFunFun α β) E = invFun E :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem toFunFun.effEff  {α β : U} (E : α ⟷ β) (a : α) : ((toFunFun  α β) E) a = to  E a :=
  by simp
  @[simp] theorem invFunFun.effEff {α β : U} (E : α ⟷ β) (b : β) : ((invFunFun α β) E) b = inv E b :=
  by simp

  @[simp] theorem toFun.bundledEq  {α β : U} (E : α ⟷ β) : HasInternalFunctors.toBundled (toFun E)  = (toBundled E).toFun :=
  HasInternalFunctors.toFromBundled (toBundled E).toFun
  @[simp] theorem invFun.bundledEq {α β : U} (E : α ⟷ β) : HasInternalFunctors.toBundled (invFun E) = (toBundled E).invFun :=
  HasInternalFunctors.toFromBundled (toBundled E).invFun

  def isEquiv {α β : U} (E : α ⟷ β) : h.IsEquiv (toBundled E).toFun (toBundled E).invFun :=
  (toBundled E).isEquiv

  def isEquiv' {α β : U} (E : α ⟷ β) :
    h.IsEquiv (HasInternalFunctors.toBundled (toFun E)) (HasInternalFunctors.toBundled (invFun E)) :=
  by simp; apply isEquiv

  @[simp] theorem fromBundled.to.coe'  {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).toFun  = E.toFun  :=
  congrArg BundledEquivalence.toFun  (toFromBundled E)
  @[simp] theorem fromBundled.inv.coe' {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).invFun = E.invFun :=
  congrArg BundledEquivalence.invFun (toFromBundled E)
  @[simp] theorem fromBundled.to.coe  {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).toFun.f  = E.toFun.f  :=
  congrArg BundledFunctor.f (fromBundled.to.coe'  E)
  @[simp] theorem fromBundled.inv.coe {α β : U} (E : α ⟷' β) : (toBundled (fromBundled E)).invFun.f = E.invFun.f :=
  congrArg BundledFunctor.f (fromBundled.inv.coe' E)
  @[simp] theorem fromBundled.to.eff  {α β : U} (E : α ⟷' β) (a : α) : to  (fromBundled E) a = E.toFun  a :=
  congrFun (fromBundled.to.coe  E) a
  @[simp] theorem fromBundled.inv.eff {α β : U} (E : α ⟷' β) (b : β) : inv (fromBundled E) b = E.invFun b :=
  congrFun (fromBundled.inv.coe E) b

  def mkEquiv {α β : U} {to : α ⟶' β} {inv : β ⟶' α} (he : h.IsEquiv to inv) : α ⟷ β :=
  fromBundled (BundledEquivalence.mkEquiv he)

end HasInternalEquivalences

class HasIdEquiv (U : Universe) [HasExternalFunctors U U] [HasIdFun U] [h : HasExternalEquivalences U U] where
(idIsEquiv (α : U) : h.IsEquiv (HasIdFun.idFun' α) (HasIdFun.idFun' α))

namespace HasIdEquiv

  variable {U : Universe} [HasExternalFunctors U U] [HasIdFun U] [HasExternalEquivalences U U] [h : HasIdEquiv U]

  def idEquiv' (α : U) : α ⟷' α := BundledEquivalence.mkEquiv (h.idIsEquiv α)

end HasIdEquiv

class HasCompEquiv (U V W : Universe)
                   [HasExternalFunctors U V] [HasExternalFunctors V W] [HasExternalFunctors U W]
                   [HasExternalFunctors V U] [HasExternalFunctors W V] [HasExternalFunctors W U]
                   [HasCompFun U V W] [HasCompFun W V U]
                   [HasExternalEquivalences U V] [HasExternalEquivalences V W] [h : HasExternalEquivalences U W] where
(compIsEquiv {α : U} {β : V} {γ : W} (E : α ⟷' β) (F : β ⟷' γ) : h.IsEquiv (F.toFun ⊙' E.toFun) (E.invFun ⊙' F.invFun))

namespace HasCompEquiv

  variable {U V W : Universe} [HasExternalFunctors U V] [HasExternalFunctors V W] [HasExternalFunctors U W]
           [HasExternalFunctors V U] [HasExternalFunctors W V] [HasExternalFunctors W U]
           [HasCompFun U V W] [HasCompFun W V U]
           [HasExternalEquivalences U V] [HasExternalEquivalences V W] [HasExternalEquivalences U W]
           [h : HasCompEquiv U V W]

  def compEquiv' {α : U} {β : V} {γ : W} (E : α ⟷' β) (F : β ⟷' γ) : α ⟷' γ := BundledEquivalence.mkEquiv (h.compIsEquiv E F)

end HasCompEquiv

class HasInvEquiv (U V : Universe) [HasExternalFunctors U V] [HasExternalFunctors V U]
                  [HasExternalEquivalences U V] [h : HasExternalEquivalences V U] where
(invIsEquiv {α : U} {β : V} (E : α ⟷' β) : h.IsEquiv E.invFun E.toFun)

namespace HasInvEquiv

  variable {U V : Universe} [HasExternalFunctors U V] [HasExternalFunctors V U]
           [HasExternalEquivalences U V] [HasExternalEquivalences V U] [h : HasInvEquiv U V]

  def invEquiv' {α : U} {β : V} (E : α ⟷' β) : β ⟷' α := BundledEquivalence.mkEquiv (h.invIsEquiv E)

end HasInvEquiv

class HasEquivOp (U : Universe.{u}) [h : HasInternalFunctors U] [HasLinearFunOp U] extends
  HasInternalEquivalences U, HasIdEquiv U, HasCompEquiv U U U, HasInvEquiv U U : Type u where
(compEquivIsFun    {α β : U} (E : α ⟷' β) (γ : U) : h.IsFun (λ F : β ⟷ γ => HasInternalEquivalences.mkEquiv (compIsEquiv E (HasInternalEquivalences.toBundled F))))
(compEquivFunIsFun (α β γ : U)                    : h.IsFun (λ E : α ⟷ β => HasInternalFunctors.mkFun (compEquivIsFun (HasInternalEquivalences.toBundled E) γ)))
(invEquivIsFun     (α β : U)                      : h.IsFun (λ E : α ⟷ β => HasInternalEquivalences.mkEquiv (invIsEquiv (HasInternalEquivalences.toBundled E))))
(invEquivIsEquiv   (α β : U)                      : IsEquiv (BundledFunctor.mkFun (invEquivIsFun α β)) (BundledFunctor.mkFun (invEquivIsFun β α)))

namespace HasEquivOp

  variable {U : Universe.{u}} [HasInternalFunctors U] [HasLinearFunOp U] [h : HasEquivOp U]

  def idEquiv' (α : U) : α ⟷' α := HasIdEquiv.idEquiv' α
  def idEquiv  (α : U) : α ⟷  α := HasInternalEquivalences.fromBundled (idEquiv' α)

  @[simp] theorem idEquiv.to.eff  (α : U) (a : α) : HasInternalEquivalences.to  (idEquiv α) a = a :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem idEquiv.inv.eff (α : U) (a : α) : HasInternalEquivalences.inv (idEquiv α) a = a :=
  by apply HasInternalEquivalences.fromBundled.inv.eff

  def compEquiv' {α β γ : U} (E : α ⟷' β) (F : β ⟷' γ) : α ⟷' γ := HasCompEquiv.compEquiv' E F
  def compEquiv  {α β γ : U} (E : α ⟷  β) (F : β ⟷  γ) : α ⟷  γ :=
  HasInternalEquivalences.fromBundled (compEquiv' (HasInternalEquivalences.toBundled E) (HasInternalEquivalences.toBundled F))

  @[simp] theorem compEquiv.to.eff  {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) (a : α) :
    HasInternalEquivalences.to  (compEquiv E F) a = HasInternalEquivalences.to  F (HasInternalEquivalences.to  E a) :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem compEquiv.inv.eff {α β γ : U} (E : α ⟷ β) (F : β ⟷ γ) (c : γ) :
    HasInternalEquivalences.inv (compEquiv E F) c = HasInternalEquivalences.inv E (HasInternalEquivalences.inv F c) :=
  by apply HasInternalEquivalences.fromBundled.inv.eff

  def compEquivFun' {α β : U} (E : α ⟷' β) (γ : U) : (β ⟷ γ) ⟶' (α ⟷ γ) := BundledFunctor.mkFun (h.compEquivIsFun E γ)
  def compEquivFun  {α β : U} (E : α ⟷  β) (γ : U) : (β ⟷ γ) ⟶  (α ⟷ γ) :=
  HasInternalFunctors.fromBundled (compEquivFun' (HasInternalEquivalences.toBundled E) γ)

  @[simp] theorem compEquivFun.eff {α β : U} (E : α ⟷ β) (γ : U) (F : β ⟷ γ) : (compEquivFun E γ) F = compEquiv E F :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem compEquivFun.to.effEff  {α β : U} (E : α ⟷ β) (γ : U) (F : β ⟷ γ) (a : α) :
    HasInternalEquivalences.to  ((compEquivFun E γ) F) a = HasInternalEquivalences.to  F (HasInternalEquivalences.to  E a) :=
  by simp
  @[simp] theorem compEquivFun.inv.effEff {α β : U} (E : α ⟷ β) (γ : U) (F : β ⟷ γ) (c : γ) :
    HasInternalEquivalences.inv ((compEquivFun E γ) F) c = HasInternalEquivalences.inv E (HasInternalEquivalences.inv F c) :=
  by simp

  def compEquivFunFun' (α β γ : U) : (α ⟷ β) ⟶' (β ⟷ γ) ⟶ (α ⟷ γ) := BundledFunctor.mkFun (h.compEquivFunIsFun α β γ)
  def compEquivFunFun  (α β γ : U) : (α ⟷ β) ⟶  (β ⟷ γ) ⟶ (α ⟷ γ) := HasInternalFunctors.fromBundled (compEquivFunFun' α β γ)
  
  @[simp] theorem compEquivFunFun.eff (α β γ : U) (E : α ⟷ β) : (compEquivFunFun α β γ) E = compEquivFun E γ :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem compEquivFunFun.effEff (α β γ : U) (E : α ⟷ β) (F : β ⟷ γ) : ((compEquivFunFun α β γ) E) F = compEquiv E F :=
  by simp
  @[simp] theorem compEquivFunFun.to.effEffEff  (α β γ : U) (E : α ⟷ β) (F : β ⟷ γ) (a : α) :
    HasInternalEquivalences.to  (((compEquivFunFun α β γ) E) F) a = HasInternalEquivalences.to  F (HasInternalEquivalences.to  E a) := by simp
  @[simp] theorem compEquivFunFun.inv.effEffEff (α β γ : U) (E : α ⟷ β) (F : β ⟷ γ) (c : γ) :
    HasInternalEquivalences.inv (((compEquivFunFun α β γ) E) F) c = HasInternalEquivalences.inv E (HasInternalEquivalences.inv F c) := by simp

  def invEquiv' {α β : U} (E : α ⟷' β) : β ⟷' α := HasInvEquiv.invEquiv' E
  def invEquiv  {α β : U} (E : α ⟷  β) : β ⟷  α :=
  HasInternalEquivalences.fromBundled (invEquiv' (HasInternalEquivalences.toBundled E))

  @[simp] theorem invEquiv.to.eff  {α β : U} (E : α ⟷ β) (b : β) : HasInternalEquivalences.to  (invEquiv E) b = HasInternalEquivalences.inv E b :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem invEquiv.inv.eff {α β : U} (E : α ⟷ β) (a : α) : HasInternalEquivalences.inv (invEquiv E) a = HasInternalEquivalences.to  E a :=
  by apply HasInternalEquivalences.fromBundled.inv.eff

  def invEquivFun' (α β : U) : (α ⟷ β) ⟶' (β ⟷ α) := BundledFunctor.mkFun (h.invEquivIsFun α β)
  def invEquivFun  (α β : U) : (α ⟷ β) ⟶  (β ⟷ α) := HasInternalFunctors.fromBundled (invEquivFun' α β)

  @[simp] theorem invEquivFun.eff (α β : U) (E : α ⟷ β) : (invEquivFun α β) E = invEquiv E :=
  by apply HasInternalFunctors.fromBundled.eff
  @[simp] theorem invEquivFun.to.effEff  (α β : U) (E : α ⟷ β) (b : β) :
    HasInternalEquivalences.to  ((invEquivFun α β) E) b = HasInternalEquivalences.inv E b := by simp
  @[simp] theorem invEquivFun.inv.effEff (α β : U) (E : α ⟷ β) (a : α) :
    HasInternalEquivalences.inv ((invEquivFun α β) E) a = HasInternalEquivalences.to  E a := by simp

  def invEquivEquiv' (α β : U) : (α ⟷ β) ⟷' (β ⟷ α) := BundledEquivalence.mkEquiv (h.invEquivIsEquiv α β)
  def invEquivEquiv  (α β : U) : (α ⟷ β) ⟷  (β ⟷ α) := HasInternalEquivalences.fromBundled (invEquivEquiv' α β)

  @[simp] theorem invEquivEquiv.to.eff  (α β : U) (E : α ⟷ β) : HasInternalEquivalences.to  (invEquivEquiv α β) E = invEquiv E :=
  by apply HasInternalEquivalences.fromBundled.to.eff
  @[simp] theorem invEquivEquiv.inv.eff (α β : U) (E : β ⟷ α) : HasInternalEquivalences.inv (invEquivEquiv α β) E = invEquiv E :=
  by apply HasInternalEquivalences.fromBundled.inv.eff
  @[simp] theorem invEquivEquiv.to.to.effEff   (α β : U) (E : α ⟷ β) (b : β) :
    HasInternalEquivalences.to  (HasInternalEquivalences.to  (invEquivEquiv α β) E) b = HasInternalEquivalences.inv E b := by simp
  @[simp] theorem invEquivEquiv.to.inv.effEff  (α β : U) (E : α ⟷ β) (a : α) :
    HasInternalEquivalences.inv (HasInternalEquivalences.to  (invEquivEquiv α β) E) a = HasInternalEquivalences.to  E a := by simp
  @[simp] theorem invEquivEquiv.inv.to.effEff  (α β : U) (E : β ⟷ α) (a : α) :
    HasInternalEquivalences.to  (HasInternalEquivalences.inv (invEquivEquiv α β) E) a = HasInternalEquivalences.inv E a := by simp
  @[simp] theorem invEquivEquiv.inv.inv.effEff (α β : U) (E : β ⟷ α) (b : β) :
    HasInternalEquivalences.inv (HasInternalEquivalences.inv (invEquivEquiv α β) E) b = HasInternalEquivalences.to  E b := by simp

end HasEquivOp
