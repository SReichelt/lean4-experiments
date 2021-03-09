/-
Quick&dirty port of relevant parts of `data.equiv.basic` from Lean 3.

Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/


universes u₁ u₂ u₃ u₄

structure Equiv (α : Sort u₁) (β : Sort u₂) where
(toFun    : α → β)
(invFun   : β → α)
(leftInv  : ∀ x, invFun (toFun x) = x)
(rightInv : ∀ y, toFun (invFun y) = y)

namespace Equiv

-- We would really like to keep using `≃` in `Structure.Basic`. Not sure how to avoid clashes.
infix:25 " ≃≃ " => Equiv

def refl (α : Sort u₁) : α ≃≃ α := ⟨id, id, λ x => rfl, λ y => rfl⟩

def symm {α : Sort u₁} {β : Sort u₂} (e : α ≃≃ β) : β ≃≃ α := ⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩

theorem transLeftInv {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃} (e₁ : α ≃≃ β) (e₂ : β ≃≃ γ) (x : α) :
  e₁.invFun (e₂.invFun (e₂.toFun (e₁.toFun x))) = x :=
Eq.trans (congrArg e₁.invFun (e₂.leftInv (e₁.toFun x))) (e₁.leftInv x)

def trans {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃} (e₁ : α ≃≃ β) (e₂ : β ≃≃ γ) : α ≃≃ γ :=
⟨e₂.toFun ∘ e₁.toFun, e₁.invFun ∘ e₂.invFun, transLeftInv e₁ e₂, transLeftInv (symm e₂) (symm e₁)⟩

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃} {δ : Sort u₄}

@[simp] theorem symmSymm (e : α ≃≃ β) : e.symm.symm = e := match e with
| ⟨toFun, invFun, leftInv, rightInv⟩ => rfl

@[simp] theorem transRefl (e : α ≃≃ β) : e.trans (refl β) = e := match e with
| ⟨toFun, invFun, leftInv, rightInv⟩ => rfl

@[simp] theorem reflSymm : (refl α).symm = refl α := rfl

@[simp] theorem reflTrans (e : α ≃≃ β) : (refl α).trans e = e := match e with
| ⟨toFun, invFun, leftInv, rightInv⟩ => rfl

@[simp] theorem symmTrans (e : α ≃≃ β) : e.symm.trans e = refl β :=
let h₁ : e.toFun ∘ e.invFun = id := funext e.rightInv;
-- No idea how this works in Lean 4.
sorry

@[simp] theorem transSymm (e : α ≃≃ β) : e.trans e.symm = refl α := symmTrans (symm e)

@[simp] theorem symmTransSymm (ab : α ≃≃ β) (bc : β ≃≃ γ) :
  (ab.trans bc).symm = bc.symm.trans ab.symm := rfl

theorem transAssoc (ab : α ≃≃ β) (bc : β ≃≃ γ) (cd : γ ≃≃ δ) :
  (ab.trans bc).trans cd = ab.trans (bc.trans cd) := rfl

end Equiv