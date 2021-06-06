set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



-- A type class that says that a given type can be used like `Sort u`, i.e. its instances can be regarded
-- as types. We can also regard this as `V` defining a universe (corresponding to the Lean universe `u`).
-- * The canonical instance is `Sort u` itself (with `Prop` as a special case).
-- * Another common case is `Bundled C` for a type class `C : Sort u → Sort v`.
-- Both examples are defined in `Instances.lean`.

class HasInstances (U : Sort v) : Sort (max (u + 1) v) where
(Inst : U → Sort u)

namespace HasInstances

  instance coeSort (U : Sort v) [s : HasInstances.{u, v} U] : CoeSort U (Sort u) := ⟨s.Inst⟩

  notation "⌈" U:0 "⌉" => HasInstances.Inst U

  instance sortHasInstances : HasInstances.{u, u + 1} (Sort u) := ⟨id⟩

end HasInstances



def GeneralizedTypeClass (U : Type u) [HasInstances.{u, u + 1} U] : Type (max u v) := U → Sort v

structure Bundled {U : Type u} [HasInstances.{u, u + 1} U] (C : GeneralizedTypeClass.{u, v} U) : Type (max u v) where
(α    : U)
[inst : C α]

namespace Bundled

  instance hasInstances {U : Type u} [HasInstances.{u, u + 1} U] (C : GeneralizedTypeClass.{u, v} U) : HasInstances (Bundled C) :=
  ⟨λ S => ⌈S.α⌉⟩

end Bundled



def Universe : Type (u + 1) := Bundled HasInstances.{u, u + 1}

namespace Universe

  instance hasInstances : HasInstances Universe.{u} := Bundled.hasInstances HasInstances

  variable (U : Universe)

  instance instInst : HasInstances U.α := U.inst
  instance : HasInstances ⌈U⌉ := instInst U

end Universe
