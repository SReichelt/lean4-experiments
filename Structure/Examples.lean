--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- This file contains some examples that show how operations and properties can be deduced purely from
-- structure in a generic way.
--
-- See the comment at the top of `Structure.lean` for more information.



import Structure.Basic
import Structure.BuildingBlocks

-- A quick&dirty port of the parts of data.equiv.basic we need; should be replaced once it becomes
-- available in Lean 4 mathlib.
import Structure.Data.Equiv

open StructureFunctor
open BuildingBlocks



universe u



namespace Examples

-- As the simplest example of a type class, let us consider `Inhabited` from `Prelude`, which gives a
-- type a "pointed type" structure.
--
-- In order to let our framework determine automatically what an isomorphism between two instances of
-- `Inhabited` should be, we need to show that the function `Inhabited : Sort _ → Sort _` is a
-- `StructureFunctor`.
-- The easiest way to do this is to observe that the content of `Inhabited α` is actually a single
-- instance of `α`, so we have an `Equiv` between `Inhabited α` and `α`. Using this `Equiv`, the type
-- class `Inhabited` becomes an instance (!) of the type class `StructuralTypeClass`.

namespace Inhabited

def inhabitedEquiv (α : Type u) : Equiv (Inhabited α) α :=
{ toFun    := λ ⟨x⟩ =>  x,
  invFun   := λ  x  => ⟨x⟩,
  leftInv  := λ ⟨x⟩ => rfl,
  rightInv := λ  x  => rfl }

instance : StructuralTypeClass Inhabited := ⟨idFun, inhabitedEquiv⟩

-- This gives us a definition of when two inhabited types are isomorphic.

def Iso (α β : Type u) [h₁ : Inhabited α] [h₂ : Inhabited β] := Isomorphism α h₁ β h₂

-- Let's check whether that definition is actually the correct one.

theorem isoMapsBasePoint {α β : Type u} [h₁ : Inhabited α] [h₂ : Inhabited β] (e : Iso α β) :
  (isoTypeEquiv e).toFun h₁.default = h₂.default :=
let h := isoCondition e;
sorry

end Inhabited

end Examples
