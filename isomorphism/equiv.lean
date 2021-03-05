/-
Quick&dirty port of relevant parts of `data.equiv.basic` from Lean 3.

Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/


structure Equiv (α β : Sort u) where
(toFun    : α → β)
(invFun   : β → α)
(leftInv  : ∀ x, invFun (toFun x) = x)
(rightInv : ∀ y, toFun (invFun y) = y)

namespace Equiv

infix:25 " ≃≃ " => Equiv

def refl (α : Sort u) : α ≃≃ α := ⟨id, id, λ x => rfl, λ y => rfl⟩

def symm {α β : Sort u} (e : α ≃≃ β) : β ≃≃ α := ⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩

theorem transLeftInv {α β γ : Sort u} (e₁ : α ≃≃ β) (e₂ : β ≃≃ γ) (x : α) :
  e₁.invFun (e₂.invFun (e₂.toFun (e₁.toFun x))) = x :=
Eq.trans (congrArg e₁.invFun (e₂.leftInv (e₁.toFun x))) (e₁.leftInv x)

def trans {α β γ : Sort u} (e₁ : α ≃≃ β) (e₂ : β ≃≃ γ) : α ≃≃ γ :=
⟨e₂.toFun ∘ e₁.toFun, e₁.invFun ∘ e₂.invFun, transLeftInv e₁ e₂, transLeftInv (symm e₂) (symm e₁)⟩

protected def cast {α β : Sort u} (h : α = β) : α ≃≃ β :=
⟨cast h, cast h.symm, sorry, sorry⟩

variable {α β γ δ : Sort u}

@[simp] theorem symmSymm (e : α ≃≃ β) : e.symm.symm = e := sorry

@[simp] theorem transRefl (e : α ≃≃ β) : e.trans (refl β) = e := sorry

@[simp] theorem reflSymm : (refl α).symm = refl α := rfl

@[simp] theorem reflTrans (e : α ≃≃ β) : (refl α).trans e = e := sorry

@[simp] theorem symmTrans (e : α ≃≃ β) : e.symm.trans e = refl β := sorry

@[simp] theorem transSymm (e : α ≃≃ β) : e.trans e.symm = refl α := sorry

@[simp] theorem symmTransSymm (ab : α ≃≃ β) (bc : β ≃≃ γ) :
  (ab.trans bc).symm = bc.symm.trans ab.symm :=
sorry

theorem transAssoc (ab : α ≃≃ β) (bc : β ≃≃ γ) (cd : γ ≃≃ δ) :
  (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
sorry

end Equiv
