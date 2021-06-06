--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- This file contains collections of category-theoretic axioms that are parameterized in such a way that
-- they are suitable for all kinds of categories, groupoids, and higher groupoids.
--
-- Several instances of these axioms can be constructed from basic structures provided by Lean (i.e. Core
-- and a tiny bit of mathlib). These can be found in `Instances.lean`.



import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors
import Structure.Generic.Axioms.AbstractEquivalences
import Structure.Generic.Axioms.AbstractProducts
import Structure.Generic.Axioms.AbstractTrivialTypes
import Structure.Generic.Axioms.GeneralizedProperties
import Structure.Generic.Axioms.DependentGeneralizedProperties
import Structure.Generic.Axioms.InstanceEquivalences
import Structure.Generic.Axioms.CategoryTheory
import Structure.Generic.Axioms.InstanceIsomorphisms
import Structure.Generic.Axioms.FunctorExtensionality
