import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic
import Structure.Generic.Instances.Bundled
import Structure.Generic.Functors

open GeneralizedRelation



set_option autoBoundImplicitLocal false
set_option pp.universes true

universes u u' v v' w w'



section BundledCategories

  variable (M : Universe.{max v w}) [HasInternalFunctors M] [HasInstanceArrows.{max v w, w} M]

  namespace IsCategory

    @[reducible] def Category := Bundled (IsCategory.{(max u v w) + 1} M)

    @[reducible] def category : Universe.{(max u v w) + 1} := simpleBundledUniverse.{max u v w} (IsCategory.{(max u v w) + 1} M)

    instance (S : category.{u, v, w} M) : IsCategory M ⌈S⌉ := simpleBundledInstance.{max u v w} (IsCategory.{(max u v w) + 1} M) S

  end IsCategory

  namespace IsGroupoid

    @[reducible] def Groupoid := Bundled (IsGroupoid.{(max u v w) + 1} M)

    @[reducible] def groupoid : Universe.{(max u v w) + 1} := simpleBundledUniverse.{max u v w} (IsGroupoid.{(max u v w) + 1} M)

    instance (S : groupoid.{u, v, w} M) : IsGroupoid M ⌈S⌉ := simpleBundledInstance.{max u v w} (IsGroupoid.{(max u v w) + 1} M) S

  end IsGroupoid

end BundledCategories



section ExternalFunctors

  variable (M : Universe.{max v  w})  [HasInternalFunctors M] [HasInstanceArrows.{max v  w,  w}  M]
           (N : Universe.{max v' w'}) [HasInternalFunctors N] [HasInstanceArrows.{max v' w', w'} N]
           [HasExternalFunctors M N]

  namespace IsCategory

    instance hasFunctoriality : Bundled.HasFunctoriality.{max u v w, max u' v' w'} (IsCategory M) (IsCategory N) :=
    ⟨λ {S T} => IsArrowFunctor.{(max u' v' w') + 1} M N (hα := S.inst.toHasArrows) (hβ := T.inst.toHasArrows)⟩

    instance hasExternalFunctors : HasExternalFunctors (category.{u, v, w} M) (category.{u', v', w'} N) :=
    Bundled.hasExternalFunctors.{max u v w, max u' v' w'} (IsCategory M) (IsCategory N)
                                                          (h := hasFunctoriality.{u, u', v, v', w, w'} M N)

    instance {S : category.{u, v, w} M} {T : category.{u', v', w'} N} (F : S ⟶' T) : IsArrowFunctor M N F.f := F.isFun

  end IsCategory

  namespace IsGroupoid

    instance hasFunctoriality : Bundled.HasFunctoriality.{max u v w, max u' v' w'} (IsGroupoid M) (IsGroupoid N) :=
    ⟨λ {S T} => IsEquivFunctor.{(max u' v' w') + 1} M N (hα := S.inst.toHasEquivalences) (hβ := T.inst.toHasEquivalences)⟩

    instance hasExternalFunctors : HasExternalFunctors (groupoid.{u, v, w} M) (groupoid.{u', v', w'} N) :=
    Bundled.hasExternalFunctors.{max u v w, max u' v' w'} (IsGroupoid M) (IsGroupoid N)
                                                          (h := hasFunctoriality.{u, u', v, v', w, w'} M N)

    instance {S : groupoid.{u, v, w} M} {T : groupoid.{u', v', w'} N} (F : S ⟶' T) : IsEquivFunctor M N F.f := F.isFun

  end IsGroupoid

end ExternalFunctors



section InternalFunctors

  variable (M : Universe.{max v w}) [HasInternalFunctors M] [HasInstanceEquivalences.{max v w, w} M]
           [hNat : HasNaturalQuantification typeUniverse.{max u v w} typeUniverse.{max u v w} M M]

  namespace IsCategory

    -- TODO

  end IsCategory

  namespace IsGroupoid

    def Equiv {S T : groupoid.{u, v, w} M} (F G : S ⟶' T) := NaturalEquivalence M M F.f G.f

    def EquivRel (S T : groupoid.{u, v, w} M) : GeneralizedRelation (S ⟶' T) M :=
    λ F G => (hNat.hasNat S.inst.Equiv T.inst.Equiv
                          (h := T.inst.isEquiv.toHasTrans)
                          (mF := HasInternalFunctors.toBundled F.f) (mG := HasInternalFunctors.toBundled G.f)
                          F.isFun.mapEquiv G.isFun.mapEquiv).Nat (h := T.inst.isEquiv.toHasTrans)

    instance functorGroupoid (S T : groupoid.{u, v, w} M) : IsGroupoid.{(max u v w) + 1} M (S ⟶' T) :=
    { Equiv   := EquivRel M (hNat := hNat) S T,
      isEquiv := sorry,
      isIso   := sorry }

    instance hasFunctorInstances : Bundled.HasFunctorInstances.{max u v w} (IsGroupoid M) (h := hasFunctoriality.{u, u, v, v, w, w} M M) :=
    sorry --⟨functorGroupoid.{u, v, w} M (hNat := hNat)⟩

    instance hasInternalFunctors : HasInternalFunctors (groupoid.{u, v, w} M) :=
    sorry --Bundled.hasInternalFunctors.{max u v w} (IsGroupoid M) (h := hasFunctorInstances.{u, v, w} M)

  end IsGroupoid

end InternalFunctors



section ExternalFunctorOperations

  section idFun

    variable (M : Universe.{max v w}) [HasInternalFunctors M] [HasInstanceArrows.{max v w, w} M] [HasIdFun M]

    instance IsCategory.hasIdFun : HasIdFun (category.{u, v, w} M) := ⟨λ _ => idFun.isArrowFunctor M⟩
    instance IsGroupoid.hasIdFun : HasIdFun (groupoid.{u, v, w} M) := ⟨λ _ => idFun.isEquivFunctor M⟩

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
