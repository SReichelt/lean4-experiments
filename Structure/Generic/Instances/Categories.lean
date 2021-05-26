import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic
import Structure.Generic.Instances.Bundled
import Structure.Generic.Functors

open GeneralizedRelation



set_option autoBoundImplicitLocal false
set_option pp.universes true

universes u u' v vv v' vv' w ww w' ww' w''



section BundledCategories

  variable (M : Universe.{v}) [HasInternalFunctors.{v, vv} M] [HasInstanceArrows.{v, w, ww} M]

  namespace IsCategory

    @[reducible] def Category := Bundled (IsCategory.{(max u v w) + 1} M)

    @[reducible] def category : Universe.{(max u v w) + 1} := simpleBundledUniverse.{max u v w} (IsCategory.{(max u v w) + 1} M)

    instance (S : category.{u} M) : IsCategory M ⌈S⌉ := simpleBundledInstance.{max u v w} (IsCategory.{(max u v w) + 1} M) S

  end IsCategory

  namespace IsGroupoid

    @[reducible] def Groupoid := Bundled (IsGroupoid.{(max u v w) + 1} M)

    @[reducible] def groupoid : Universe.{(max u v w) + 1} := simpleBundledUniverse.{max u v w} (IsGroupoid.{(max u v w) + 1} M)

    instance (S : groupoid.{u} M) : IsGroupoid M ⌈S⌉ := simpleBundledInstance.{max u v w} (IsGroupoid.{(max u v w) + 1} M) S

  end IsGroupoid

end BundledCategories



section ExternalFunctors

  variable (M : Universe.{v})  [HasInternalFunctors.{v,  vv}  M] [HasInstanceArrows.{v,  w,  ww}  M]
           (N : Universe.{v'}) [HasInternalFunctors.{v', vv'} N] [HasInstanceArrows.{v', w', ww'} N]
           [HasExternalFunctors.{v, v', w''} M N]

  namespace IsCategory

    instance hasFunctoriality : Bundled.HasFunctoriality.{max u v w, max u' v' w'} (IsCategory M) (IsCategory N) :=
    ⟨λ {S T} => IsArrowFunctor M N (hα := S.inst.toHasArrows) (hβ := T.inst.toHasArrows)⟩

    instance hasExternalFunctors : HasExternalFunctors (category.{u} M) (category.{u'} N) :=
    Bundled.hasExternalFunctors.{max u v w, max u' v' w'} (IsCategory M) (IsCategory N)
                                                          (h := hasFunctoriality.{u, u'} M N)

  end IsCategory

  namespace IsGroupoid

    instance hasFunctoriality : Bundled.HasFunctoriality.{max u v w, max u' v' w'} (IsGroupoid M) (IsGroupoid N) :=
    ⟨λ {S T} => IsEquivFunctor M N (hα := S.inst.toHasEquivalences) (hβ := T.inst.toHasEquivalences)⟩

    instance hasExternalFunctors : HasExternalFunctors (groupoid.{u} M) (groupoid.{u'} N) :=
    Bundled.hasExternalFunctors.{max u v w, max u' v' w'} (IsGroupoid M) (IsGroupoid N)
                                                          (h := hasFunctoriality.{u, u'} M N)

  end IsGroupoid

end ExternalFunctors

-- We have to reopen this section because the explicit universe annotations above somehow break things.
-- TODO: It seems to work because of the universe metavariables. Does that mean the problems are only postponed?
section ExternalFunctors

  variable (M : Universe.{v})  [HasInternalFunctors M] [HasInstanceArrows M]
           (N : Universe.{v'}) [HasInternalFunctors N] [HasInstanceArrows N]
           [HasExternalFunctors M N]

  namespace IsCategory

    instance {S : category.{u} M} {T : category.{u'} N} (F : S ⟶' T) : IsArrowFunctor M N F.f := F.isFun

  end IsCategory

  namespace IsGroupoid

    instance {S : groupoid.{u} M} {T : groupoid.{u'} N} (F : S ⟶' T) : IsEquivFunctor M N F.f := F.isFun

  end IsGroupoid

end ExternalFunctors




section InternalFunctors

  variable (M : Universe.{v}) [HasInternalFunctors M] [HasInstanceEquivalences M] [hNat : HasNaturalQuantification typeUniverse.{u} typeUniverse.{u} M M]

  namespace IsCategory

    -- TODO

  end IsCategory

  namespace IsGroupoid

    def Equiv {S T : groupoid.{u} M} (F G : S ⟶' T) := NaturalEquivalence M M F.f G.f

--    -- TODO: Can we write this more cleanly?
--    def EquivRel (S T : groupoid.{u} M) : GeneralizedRelation (S ⟶' T) M :=
--    λ F G => (hNat.hasNat S.inst.Equiv T.inst.Equiv
--                          (h := T.inst.isEquiv.toHasTrans)
--                          (mF := HasInternalFunctors.toBundled F.f) (mG := HasInternalFunctors.toBundled G.f)
--                          F.isFun.mapEquiv G.isFun.mapEquiv).Nat (h := T.inst.isEquiv.toHasTrans)
--
--    instance functorGroupoid (S T : groupoid.{u} M) : IsGroupoid M (S ⟶' T) :=
--    { Equiv   := EquivRel M (hNat := hNat) S T,
--      isEquiv := sorry,
--      isIso   := sorry }
--
--    instance hasFunctorInstances : Bundled.HasFunctorInstances (IsGroupoid M) := ⟨functorGroupoid M (hNat := hNat)⟩
--
--    instance hasInternalFunctors : HasInternalFunctors (groupoid.{u} M) := Bundled.hasInternalFunctors (IsGroupoid M) (h := hasFunctorInstances M)

  end IsGroupoid

end InternalFunctors



section ExternalFunctorOperations

  section idFun

    variable (M : Universe.{v}) [HasInternalFunctors M] [HasInstanceArrows M] [HasIdFun M]

    instance IsCategory.hasIdFun : HasIdFun (category.{u} M) := ⟨λ _ => idFun.isArrowFunctor M⟩
    instance IsGroupoid.hasIdFun : HasIdFun (groupoid.{u} M) := ⟨λ _ => idFun.isEquivFunctor M⟩

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
