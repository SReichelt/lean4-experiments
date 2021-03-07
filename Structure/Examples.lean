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



namespace Examples

-- As the simplest example of a type class, let us consider `Inhabited` from `Prelude`, which gives a
-- type a "pointed type" structure.
--
-- In order to let our framework determine automatically what an isomorphism between two instances of
-- `Inhabited` should be, we need to show that the function `Inhabited : Sort _ → Sort _` is a
-- `StructureFunctor`.
-- The easiest way to do this is to observe that the content of `Inhabited α` is actually a single
-- instance of `α`, so we have an `Equiv` between `Inhabited α` and `α`. That gives us a `TypeClassEquiv`
-- between `Inhabited` and `id`, and then `toTypeClassFunctor` will return the required functor.

def inhabitedEquivInstance (α : Sort u) : Equiv (Inhabited α) α :=
{ toFun    := λ ⟨x⟩ =>  x,
  invFun   := λ  x  => ⟨x⟩,
  leftInv  := λ ⟨x⟩ => rfl,
  rightInv := λ  x  => rfl }

def inhabitedFunctor := toTypeClassFunctor Inhabited idFun inhabitedEquivInstance

end Examples
