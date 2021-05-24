import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u uu u' v v' w



def bundledUniverse {U : Universe.{u, uu}} (C : TypeClass.{u, uu, v} U) : Universe.{u, max 1 uu v} := ⟨Bundled C⟩
instance bundledInstance {U : Universe.{u, uu}} (C : TypeClass.{u, uu, v} U) (S : bundledUniverse C) : C S.α := S.inst

-- TODO: Make `universeUniverse` more specific so that it makes sense to speak of functors between
-- universes, i.e. generalized type classes.
def universeUniverse : Universe.{uu, (max u uu) + 1} := bundledUniverse (U := sortUniverse.{uu}) HasInstances.{u, uu}



namespace Bundled

  class HasFunctoriality (C : TypeClass.{u, u + 1, u'} sortUniverse.{u}) (D : TypeClass.{v, v + 1, v'} sortUniverse.{v}) where
  (IsFunctorial {S : bundledUniverse C} {T : bundledUniverse D} : (S → T) → Sort w)

  instance hasExternalFunctors (C : TypeClass.{u, u + 1, u'} sortUniverse.{u}) (D : TypeClass.{v, v + 1, v'} sortUniverse.{v})
                               [h : HasFunctoriality C D] :
    HasExternalFunctors (bundledUniverse C) (bundledUniverse D) :=
  ⟨h.IsFunctorial⟩

  class HasFunctorInstances (C : TypeClass.{max 1 u v, (max 1 u v) + 1, u'} sortUniverse.{max 1 u v})
                            [HasFunctoriality.{max 1 u v, u', max 1 u v, u', v} C C] where
  (funInst (S T : bundledUniverse C) : C (S ⟶' T))

  instance hasInternalFunctors (C : TypeClass.{max 1 u v, (max 1 u v) + 1, u'} sortUniverse.{max 1 u v})
                               [HasFunctoriality.{max 1 u v, u', max 1 u v, u', v} C C]
                               [h : HasFunctorInstances.{u, u', v} C] :
    HasInternalFunctors (bundledUniverse C) :=
  { Fun      := λ S T => { α    := S ⟶' T,
                           inst := h.funInst S T },
    funEquiv := λ S T => Equiv.refl (S ⟶' T) }

end Bundled
