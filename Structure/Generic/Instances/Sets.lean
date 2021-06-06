import Structure.Generic.Axioms
import Structure.Generic.Instances.Basic
import Structure.Generic.Instances.Bundled



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v



section Sets

  variable (M : Universe.{v})

  -- TODO: We want sets to have an instance equivalence (i.e. equality).
  -- For this, we probably need to start with a universe with instance equivalences.
  -- I think we need to introduce a `UniverseWithEquivalences` type. Or is it just `Groupoid`?

  def Subset (U : Universe.{u}) : Type (max u v) := GeneralizedProperty ⌈U⌉ M

  @[reducible] def GeneralizedSet := Bundled (Subset.{u, v} M)

end Sets
