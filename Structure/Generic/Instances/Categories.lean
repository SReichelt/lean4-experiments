import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic
import Structure.Generic.Instances.Bundled
import Structure.Generic.Functors

open GeneralizedRelation



section BundledCategories

  variable (M : Universe) [HasInternalFunctors M] [HasInstanceArrows M]

  namespace IsCategory

    @[reducible] def Category := Bundled (IsCategory M)

    @[reducible] def category : Universe := bundledUniverse (U := sortUniverse) (IsCategory M)

    instance (S : category M) : IsCategory M ⌈S⌉ := bundledInstance (U := sortUniverse) (IsCategory M) S

  end IsCategory

  namespace IsGroupoid

    @[reducible] def Groupoid := Bundled (IsGroupoid M)

    @[reducible] def groupoid : Universe := bundledUniverse (U := sortUniverse) (IsGroupoid M)

    instance (S : groupoid M) : IsGroupoid M ⌈S⌉ := bundledInstance (U := sortUniverse) (IsGroupoid M) S

  end IsGroupoid

end BundledCategories



section ExternalFunctors

  variable (M : Universe) [HasInternalFunctors M] [HasInstanceArrows M]
           (N : Universe) [HasInternalFunctors N] [HasInstanceArrows N]
           [HasExternalFunctors M N]

  namespace IsCategory

    instance hasFunctoriality : Bundled.HasFunctoriality (IsCategory M) (IsCategory N) := ⟨IsArrowFunctor M N⟩

    instance {S : category M} {T : category N} (F : S ⟶' T) : IsArrowFunctor M N F.f := F.isFun

  end IsCategory

  namespace IsGroupoid

    instance hasFunctoriality : Bundled.HasFunctoriality (IsGroupoid M) (IsGroupoid N) := ⟨IsEquivFunctor M N⟩

    instance {S : groupoid M} {T : groupoid N} (F : S ⟶' T) : IsEquivFunctor M N F.f := F.isFun

  end IsGroupoid

end ExternalFunctors



section InternalFunctors

  variable (M : Universe) [HasInternalFunctors M] [HasInstanceEquivalences M] [hNat : HasNaturalQuantification sortUniverse sortUniverse M M]

  namespace IsCategory

    -- TODO

  end IsCategory

  namespace IsGroupoid

    def Equiv {S T : groupoid M} (F G : S ⟶' T) := NaturalEquivalence M M F.f G.f

    -- TODO: Can we write this more cleanly?
    def EquivRel (S T : groupoid M) : GeneralizedRelation (S ⟶' T) M :=
    λ F G => (hNat.hasNat S.inst.Equiv T.inst.Equiv
                          (h := T.inst.isEquiv.toHasTrans)
                          (mF := HasInternalFunctors.toBundled F.f) (mG := HasInternalFunctors.toBundled G.f)
                          F.isFun.mapEquiv G.isFun.mapEquiv).Nat (h := T.inst.isEquiv.toHasTrans)

    instance functorGroupoid (S T : groupoid M) : IsGroupoid M (S ⟶' T) :=
    { Equiv   := EquivRel M (hNat := hNat) S T,
      isEquiv := sorry,
      isIso   := sorry }

    instance hasFunctorInstances : Bundled.HasFunctorInstances (IsGroupoid M) := ⟨functorGroupoid M (hNat := hNat)⟩

    --instance hasInternalFunctors : HasInternalFunctors (groupoid M) := Bundled.hasInternalFunctors (IsGroupoid M)
  
  end IsGroupoid

end InternalFunctors



section ExternalFunctorOperations

  section idFun

    variable (M : Universe) [HasInternalFunctors M] [HasInstanceArrows M] [HasIdFun M]

    instance IsCategory.hasIdFun : HasIdFun (category M) := ⟨λ _ => idFun.isArrowFunctor M⟩
    instance IsGroupoid.hasIdFun : HasIdFun (groupoid M) := ⟨λ _ => idFun.isEquivFunctor M⟩

  end idFun

  -- TODO: constFun, compFun

end ExternalFunctorOperations



-- TODO: Show that:
-- * the universes of categories and groupoids have nice properties
--   (-> bundled functors -> natural transformation as equivalence -> internal functors, also instance arrows/equivalences), and
-- * universes with certain properties are actually categories/groupoids
--   (-> category of categories, groupoid of groupoids).
-- TODO: At some point, we will add the assumption that the `Equiv` relation of a universe has isomorphisms.
-- So all instances are groupoids. How does that fit into this scheme?
