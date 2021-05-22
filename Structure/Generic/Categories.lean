--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- This file contains definitions of (potentially higher) categories and groupoids.



import Structure.Generic.Axioms
import Structure.Generic.Functors



section Categories

  variable (M : Universe) [HasInternalFunctors M] [HasInstanceArrows M] (α : Sort u)

  class IsCategory extends HasArrows α M where
  [isMor : IsMorphismRelation Arrow]

  namespace IsCategory

    variable [h : IsCategory M α]

    instance hasMor : IsMorphismRelation h.Arrow := h.isMor

  end IsCategory

  class IsGroupoid extends HasEquivalences α M where
  [isIso : IsIsomorphismRelation Equiv]

  namespace IsGroupoid

    variable [h : IsGroupoid M α]

    instance hasIso : IsIsomorphismRelation h.Equiv := h.isIso

  end IsGroupoid

end Categories



section BundledCategories

  variable (M : Universe) [HasInternalFunctors M] [HasInstanceArrows M]

  @[reducible] def Category := Bundled (IsCategory M)
  @[reducible] def Groupoid := Bundled (IsGroupoid M)

end BundledCategories



-- TODO: Show that:
-- * the universes of categories and groupoids have nice properties
--   (-> bundled functors -> natural transformation as equivalence -> internal functors), and
-- * universes with certain properties are actually categories/groupoids
--   (-> category of categories, groupoid of groupoids).
