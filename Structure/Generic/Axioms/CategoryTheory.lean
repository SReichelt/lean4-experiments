import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors
import Structure.Generic.Axioms.AbstractEquivalences
import Structure.Generic.Axioms.GeneralizedProperties
import Structure.Generic.Axioms.InstanceEquivalences

open GeneralizedRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v w



-- We would also like to be able to manipulate such equivalences, and we need them to behave like
-- isomorphisms when doing so, with `refl` as the identity, `symm` as inverse, and `trans` as composition.
-- In other words, a structure with its equivalences is a category where every morphism has an inverse (as
-- guaranteed by `symm`), i.e. it is a groupoid. Since equivalences have equivalences, it is actually a
-- higher groupoid.
--
-- (Of course, the same type may also have a category structure with more morphisms, but since we are
-- defining a generalization of an equivalence relation, not a category, we wish to ignore such extra
-- structure at this point.)
--
-- We add three redundant axioms to avoid unnecessary computations. (Actually, this list of axioms was
-- originally inspired by the seven corresponding lemmas in `data.equiv.basic` of mathlib in Lean 3:
-- `symm_symm`, `trans_refl`, etc.)
--
-- Remark: Interestingly, all axioms can be regarded as simplification rules (with the simplification for
-- associativity being the omission of parentheses). With the addition of the three redundant axioms, they
-- enable equational reasoning by transforming all possible terms into a "flat" canonical form. Besides
-- making proofs trivial, this observation also suggests an alternative formalization of the axioms in
-- terms of a simplification function.
--
-- Note that for actual equivalence relations, the axioms are trivially satisfied in a proof-irrelevant
-- system such as Lean.

-- TODO: Introduce a specification that describes all of the redundancies in axioms, so that higher
-- structures can force redundant data to be equal.

section Morphisms

  variable {α : Sort u} {V : Universe.{v}} [HasInternalFunctors V] [HasInstanceEquivalences.{v, w} V]
           (R : GeneralizedRelation α V)

  variable [HasLinearFunOp V] [HasTrans R]

  @[reducible] def compCompRight (a b c d : α) : R a b ⟶ R b c ⟶ R c d ⟶ R a d :=
  HasLinearFunOp.revCompFunFun (R b c) HasTrans.trans ⊙ HasTrans.trans
  @[reducible] def compCompLeft  (a b c d : α) : R a b ⟶ R b c ⟶ R c d ⟶ R a d :=
  HasLinearFunOp.swapFunFun (HasLinearFunOp.compFunFunFun (R c d) (R b d) (R a d) ⊙ HasTrans.trans) ⊙ HasTrans.trans

  theorem compCompRight.eff [HasEquivCongrFun V] {a b c d : α} (f : R a b) (g : R b c) (h : R c d) :
    (compCompRight R a b c d) f g h = h • (g • f) :=
  by simp; rfl
  theorem compCompLeft.eff  [HasEquivCongrFun V] {a b c d : α} (f : R a b) (g : R b c) (h : R c d) :
    (compCompLeft  R a b c d) f g h = (h • g) • f :=
  by simp; rfl

  class IsCompositionRelation                                 : Sort (max 1 u v w) where
  (assoc {a b c d : α} : compCompRight R a b c d ≃ compCompLeft R a b c d)

  variable [HasRefl R]

  @[reducible] def leftMulId  (a b : α) : R a b ⟶ R a b := HasTrans.revTrans ⟮ident R b⟯
  @[reducible] def rightMulId (a b : α) : R a b ⟶ R a b := HasTrans.trans    ⟮ident R a⟯

  theorem leftMulId.eff  [HasEquivCongrFun V] {a b : α} (f : R a b) : (leftMulId  R a b) f = ident R b • f :=
  by simp; rfl
  theorem rightMulId.eff [HasEquivCongrFun V] {a b : α} (f : R a b) : (rightMulId R a b) f = f • ident R a :=
  rfl

  class IsMorphismRelation    extends IsCompositionRelation R : Sort (max 1 u v w) where
  (leftId  {a b : α} : leftMulId  R a b ≃ HasLinearFunOp.idFun (R a b))
  (rightId {a b : α} : rightMulId R a b ≃ HasLinearFunOp.idFun (R a b))

  variable [HasSubLinearFunOp V] [HasNonLinearFunOp V] [HasInternalEquivalences V] [HasSymm R]

  @[reducible] def leftMulInv  (a b : α) : R a b ⟶ R a a :=
  HasNonLinearFunOp.dupFun (HasTrans.revTrans ⊙ HasInternalEquivalences.toFun HasSymm.symm)
  @[reducible] def rightMulInv (a b : α) : R a b ⟶ R b b :=
  HasNonLinearFunOp.dupFun (HasTrans.trans    ⊙ HasInternalEquivalences.toFun HasSymm.symm)

  theorem leftMulInv.eff  [HasEquivCongrFun V] {a b : α} (f : R a b) : (leftMulInv  R a b) f = f⁻¹ • f :=
  by simp; rfl
  theorem rightMulInv.eff [HasEquivCongrFun V] {a b : α} (f : R a b) : (rightMulInv R a b) f = f • f⁻¹ :=
  by simp; rfl

  class IsIsomorphismRelation extends IsMorphismRelation    R : Sort (max 1 u v w) where
  (leftInv  {a b : α} : leftMulInv  R a b ≃ HasSubLinearFunOp.constFun (R a b) (ident R a))
  (rightInv {a b : α} : rightMulInv R a b ≃ HasSubLinearFunOp.constFun (R a b) (ident R b))

  -- TODO: convert to lemmas?
  --(invInv   {a b   : α} (f : R a b)             : (f⁻¹)⁻¹       ≃ f)
  --(compInv  {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹     ≃ f⁻¹ • g⁻¹)
  --(idInv    (a     : α)                         : (ident R a)⁻¹ ≃ ident R a)

end Morphisms



-- TODO: Rephrase trans and symm as functor composition.

section Functors

  variable {α : Sort u} {V W : Universe} [HasInstanceEquivalences W] [HasExternalFunctors V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation α W)

  def BaseFunctor := ∀ {a b}, R a b ⟶' S a b

  variable (F : BaseFunctor R S)

  class IsReflFunctor  [hR : HasRefl  R] [hS : HasRefl  S] where
  (respectsRefl  (a     : α)                         : F (hR.refl   a)   ≃ hS.refl   a)

  variable [HasInternalFunctors V] [HasInternalFunctors W]

  class IsTransFunctor [hR : HasTrans R] [hS : HasTrans S] where
  (respectsTrans {a b c : α} (f : R a b) (g : R b c) : F (hR.trans' f g) ≃ hS.trans' (F f) (F g))

  class IsPreorderFunctor [IsPreorder R] [IsPreorder S] extends IsReflFunctor R S F, IsTransFunctor R S F

  variable [HasInternalEquivalences V] [HasInternalEquivalences W]

  class IsSymmFunctor  [hR : HasSymm  R] [hS : HasSymm  S] where
  (respectsSymm  {a b   : α} (f : R a b)             : F (hR.symm'  f)   ≃ hS.symm'  (F f))

  class IsEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] extends IsPreorderFunctor R S F, IsSymmFunctor R S F

end Functors



-- TODO: If arrows have equivalences, we can specify redundancies in axioms as such equivalences.



section NaturalTransformations

  variable {α : Sort u} {β : Sort v} {V W : Universe} [HasExternalFunctors V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation β W)

  def MappedBaseFunctor (m : α → β) := ∀ {a b}, R a b ⟶' S (m a) (m b)

  variable [HasInternalFunctors W] [HasInstanceEquivalences W] [h : HasTrans S]
           {mF mG : α → β} (F : MappedBaseFunctor R S mF) (G : MappedBaseFunctor R S mG)

  class IsNatural (n : ∀ a, S (mF a) (mG a)) where
  (nat {a b : α} (f : R a b) : h.trans' (n a) (G f) ≃ h.trans' (F f) (n b))

  -- The following definitions specify how we can treat a natural quantification as an element of `W`.
  -- TODO: Maybe we can replace this with a more general quantification mechanism.

  structure NaturalQuantification where
  (n         : ∀ a, S (mF a) (mG a))
  [isNatural : IsNatural R S F G n]

  class HasInternalNaturalQuantification where
  (Nat      : W)
  (natEquiv : ⌈Nat⌉ ≃ NaturalQuantification R S F G)

end NaturalTransformations

class HasNaturalQuantification (U₁ U₂ V W : Universe) [HasExternalFunctors U₁ U₂] [HasExternalFunctors V W]
                                                      [HasInternalFunctors W] [HasInstanceEquivalences W] where
[hasNat {α : U₁} {β : U₂} (R : GeneralizedRelation ⌈α⌉ V) (S : GeneralizedRelation ⌈β⌉ W) [h : HasTrans S]
        {mF mG : α ⟶' β} (F : MappedBaseFunctor R S mF) (G : MappedBaseFunctor R S mG) :
   HasInternalNaturalQuantification R S F G]



section Categories

  variable (M : Universe.{v}) [HasInternalFunctors M] [HasLinearFunOp M] [HasInstanceEquivalences.{v, w} M] (α : Sort u)

  class IsCategory extends HasArrows α M : Sort (max 1 u (v + 1) w) where
  [isMor : IsMorphismRelation Arrow]

  namespace IsCategory

    variable [h : IsCategory M α]

    instance hasMor : IsMorphismRelation h.Arrow := h.isMor

  end IsCategory

  variable [HasSubLinearFunOp M] [HasNonLinearFunOp M] [HasInternalEquivalences M]

  class IsGroupoid extends HasEquivalences α M : Sort (max 1 u (v + 1) w) where
  [isIso : IsIsomorphismRelation Equiv]

  namespace IsGroupoid

    variable [h : IsGroupoid M α]

    instance hasIso : IsIsomorphismRelation h.Equiv := h.isIso

  end IsGroupoid

end Categories
