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


def refl (α : Sort u) : Equiv α α := ⟨id, id, λ x => rfl, λ y => rfl⟩

def symm {α β : Sort u} (e : Equiv α β) : Equiv β α := ⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩

theorem transLeftInv {α β γ : Sort u} (e₁ : Equiv α β) (e₂ : Equiv β γ) (x : α) :
  e₁.invFun (e₂.invFun (e₂.toFun (e₁.toFun x))) = x :=
Eq.trans (congrArg e₁.invFun (e₂.leftInv (e₁.toFun x))) (e₁.leftInv x)

def trans {α β γ : Sort u} (e₁ : Equiv α β) (e₂ : Equiv β γ) : Equiv α γ :=
⟨e₂.toFun ∘ e₁.toFun, e₁.invFun ∘ e₂.invFun, transLeftInv e₁ e₂, transLeftInv (symm e₂) (symm e₁)⟩
