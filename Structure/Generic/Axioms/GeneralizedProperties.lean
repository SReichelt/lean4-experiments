import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors
import Structure.Generic.Axioms.AbstractEquivalences
import Structure.Generic.Lemmas.DerivedFunctors
import Structure.Generic.Notation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v



def GeneralizedProperty (α : Sort u) (V : Universe.{v}) := α → V

namespace GeneralizedProperty

  variable {α : Sort u} {V : Universe.{v}}

  instance hasInstances : HasInstances (GeneralizedProperty α V) := ⟨λ P => ∀ a, P a⟩

  section Properties

    variable (P : GeneralizedProperty α V)

    class HasInst where
    (inst (a : α) : P a)

  end Properties

end GeneralizedProperty

open GeneralizedProperty



-- TODO: Update comments

-- We want to formalize a very general "structure with equivalences", so we start with a very basic
-- abstraction for something that looks like an equivalence relation except that the codomain is
-- generalized to `Sort u` instead of `Prop`. Therefore, `⟨Equiv.refl, Equiv.symm, Equiv.trans⟩`, where
-- `Equiv` is the Lean 4 version of the `equiv` type in Lean 3 mathlib, is also an instance of this type
-- (with the restriction that both arguments must live in the same universe).
--
-- We actually need to generalize slightly further to a codomain that is not necessarily a sort but can be
-- coerced to a sort. This way, the codomain can be any Lean structure that bundles a sort, in particular
-- it can be our `Structure` type.

def GeneralizedRelation (α : Sort u) (V : Universe.{v}) := α → α → V

namespace GeneralizedRelation

  variable {α : Sort u} {V : Universe.{v}}

  instance hasInstances : HasInstances (GeneralizedRelation α V) := ⟨λ R => ∀ a b, R a b⟩

  section Properties

    variable (R : GeneralizedRelation α V)

    class HasRefl where
    (refl (a : α) : R a a)

    variable [HasInternalFunctors V]

    class HasTrans where
    (trans {a b c : α} : R a b ⟶ R b c ⟶ R a c)

    class IsPreorder extends HasRefl R, HasTrans R

    variable [HasInternalEquivalences V]

    class HasSymm where
    (symm {a b : α} : R a b ⟷ R b a)

    class IsEquivalence extends IsPreorder R, HasSymm R
  
  end Properties

  def HasTrans.revTrans {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasLinearFunOp V] [h : HasTrans R]
                        {a b c : α} : R b c ⟶ R a b ⟶ R a c :=
  HasLinearFunOp.swapFunFun h.trans

  @[simp] theorem HasTrans.revTrans.eff {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasLinearFunOp V] [h : HasTrans R]
                                        {a b c : α} (g : R b c) (f : R a b) :
    h.revTrans g f = h.trans f g :=
  by apply HasLinearFunOp.swapFunFun.effEff

  def HasTrans.trans' {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasTrans R]
                      {a b c : α} (f : R a b) (g : R b c) : R a c := h.trans f g

  def HasSymm.symm' {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasInternalEquivalences V] [h : HasSymm R]
                    {a b : α} (f : R a b) : R b a := HasInternalEquivalences.to h.symm f

  -- When reasoning about instances of `R a b`, we would like to write `trans` as composition, `refl` as
  -- identity, and `symm` as inverse.
  -- Note that `R` can be inferred from `f : R a b` by elaboration.

  section Notation

    @[reducible] def revComp {R : GeneralizedRelation α V} [HasInternalFunctors V] [h : HasTrans R] {a b c : α} (g : R b c) (f : R a b) : R a c := h.trans' f g
    infixr:90 " • " => revComp

    @[reducible] def ident (R : GeneralizedRelation α V) [h : HasRefl R] (a : α) : R a a := h.refl a

    @[reducible] def inv {R : GeneralizedRelation α V} [HasInternalFunctors V] [HasInternalEquivalences V] [h : HasSymm R] {a b : α} (f : R a b) : R b a := h.symm' f
    postfix:max "⁻¹" => inv

  end Notation

end GeneralizedRelation

open GeneralizedRelation



-- We can attach products, arrows, and/or equivalences to a given sort, in the form of generalized
-- relations satisfying appropriate properties.

section AttachedRelations

  variable (α : Sort u) (V : Universe.{v}) [HasInternalFunctors V]

  class HasArrows where
  (Arrow      : GeneralizedRelation α V)
  [isPreorder : IsPreorder Arrow]

  namespace HasArrows
    variable [h : HasArrows α V]
    instance arrowPreorder : IsPreorder h.Arrow := h.isPreorder
    instance hasArrow : HasArrow α α := ⟨h.Arrow⟩
    instance : HasInstances (HasArrow.γ α α) := Universe.instInst V
    instance : IsPreorder (@HasArrow.Arrow α α (hasArrow α V)) := h.isPreorder
  end HasArrows

  variable [HasInternalEquivalences V]

  class HasEquivalences where
  (Equiv   : GeneralizedRelation α V)
  [isEquiv : IsEquivalence Equiv]

  namespace HasEquivalences
    variable [h : HasEquivalences α V]
    instance equivEquivalence : IsEquivalence h.Equiv := h.isEquiv
    instance hasEquivalence : HasEquivalence α α := ⟨h.Equiv⟩
    instance : HasInstances (HasEquivalence.γ α α) := Universe.instInst V
    instance : IsEquivalence (@HasEquivalence.Equiv α α (hasEquivalence α V)) := h.isEquiv
  end HasEquivalences

  class HasProducts where
  (Product : GeneralizedRelation α V)
  [hasSymm : HasSymm Product]

  namespace HasProducts
    variable [h : HasProducts α V]
    instance productSymm : HasSymm h.Product := h.hasSymm
    instance hasProduct : HasProduct α α := ⟨h.Product⟩
    instance : HasInstances (HasProduct.γ α α) := Universe.instInst V
    instance : HasSymm (@HasProduct.Product α α (hasProduct α V)) := h.hasSymm
  end HasProducts

end AttachedRelations
