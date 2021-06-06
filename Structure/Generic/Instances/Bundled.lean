import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



def bundledUniverse {U : Universe.{u}} (C : GeneralizedTypeClass.{u, u} U) : Universe.{u} := ⟨Bundled C⟩
instance bundledInstance {U : Universe.{u}} (C : GeneralizedTypeClass.{u, u} U) (S : bundledUniverse C) : C S.α := S.inst

def SimpleTypeClass := GeneralizedTypeClass.{u + 1, u + 1} sort.{u + 1}
def simpleBundledUniverse (C : SimpleTypeClass.{u}) : Universe.{u + 1} := bundledUniverse C
instance simpleBundledInstance (C : SimpleTypeClass.{u}) (S : simpleBundledUniverse C) : C S.α := bundledInstance C S

-- TODO: Make `universeUniverse` more specific so that it makes sense to speak of functors between
-- universes, i.e. generalized type classes.
def universeUniverse : Universe.{u + 1} := simpleBundledUniverse HasInstances.{u, u + 1}



namespace Bundled

  class HasFunctoriality (C : SimpleTypeClass.{u}) (D : SimpleTypeClass.{v}) : Type ((max u v) + 1) where
  (IsFunctorial {S : simpleBundledUniverse C} {T : simpleBundledUniverse D} : (S → T) → Type (max u v))

  instance hasExternalFunctors (C : SimpleTypeClass.{u}) (D : SimpleTypeClass.{v})
                               [h : HasFunctoriality.{u, v} C D] :
    HasExternalFunctors.{u + 1, v + 1} (simpleBundledUniverse C) (simpleBundledUniverse D) :=
  ⟨h.IsFunctorial⟩

  class HasFunctorInstances (C : SimpleTypeClass.{u}) [h : HasFunctoriality.{u, u} C C] : Type (u + 1) where
  (funInst (S T : simpleBundledUniverse C) : C (S ⟶' T))

  -- Work around type class resolution problems.
  class HasFunctorInstances' (C : SimpleTypeClass.{u}) (h : HasFunctoriality.{u, u} C C) : Type (u + 1) where
  (funInst (S T : simpleBundledUniverse C) : C (S ⟶' T))

  instance (C : SimpleTypeClass.{u}) (h : HasFunctoriality.{u, u} C C) [h' : HasFunctorInstances' C h] :
    HasFunctorInstances C := ⟨h'.funInst⟩

  instance hasInternalFunctors (C : SimpleTypeClass.{u})
                               [HasFunctoriality.{u, u} C C]
                               [h : HasFunctorInstances.{u} C] :
    HasInternalFunctors.{u + 1} (simpleBundledUniverse C) :=
  { Fun      := λ S T => { α    := S ⟶' T,
                           inst := h.funInst S T },
    funEquiv := λ S T => Equiv.refl (S ⟶' T) }

  instance hasInternalFunctors' (C : SimpleTypeClass.{u})
                                (h : HasFunctoriality.{u, u} C C)
                                [h' : HasFunctorInstances'.{u} C h] :
    HasInternalFunctors.{u + 1} (simpleBundledUniverse C) :=
  hasInternalFunctors C

end Bundled
