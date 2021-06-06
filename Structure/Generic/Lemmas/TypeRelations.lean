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
import Structure.Generic.Axioms.GeneralizedProperties
import Structure.Generic.Axioms.DependentGeneralizedProperties
import Structure.Generic.Axioms.InstanceEquivalences

open GeneralizedRelation
open GeneralizedDependentRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true



-- TODO: Add equivalences.
-- TODO: Add (iso)morphisms as an additional type class.

namespace HasLinearFunOp

  variable (U : Universe) [h : HasInternalFunctors U] [HasLinearFunOp U]

  instance : HasRefl    h.Fun := ⟨idFun⟩
  instance : HasTrans   h.Fun := ⟨compFunFunFun _ _ _⟩
  instance : IsPreorder h.Fun := ⟨⟩

  instance hasArrows : HasArrows ⌈U⌉ U := ⟨h.Fun⟩

  @[simp] theorem transDef {α β γ : U} {F : α ⟶ β} {G : β ⟶ γ} : G • F = G ⊙ F :=
  compFunFunFun.effEff α β γ F G

  variable [hInst : HasNaturalEquivalences U] [HasLinearFunOp hInst.equivUniverse]

  def DependentArrow {α β : U} (F : α ⟶ β) (a : α) (b : β) := F a ≃ b

  namespace DependentArrow

    def refl {α : U} (a : α) : (idFun α) a ≃ a :=
    Eq.ndrec (motive := λ x : α => ⌈x ≃ a⌉) (ident (hInst.Equiv α) a) (Eq.symm (idFun.eff α a))

    def trans {α β γ : U} {F : α ⟶ β} {G : β ⟶ γ} {a : α} {b : β} {c : γ} : F a ≃ b ⟶ G b ≃ c ⟶ (G • F) a ≃ c :=
    let f₁ : F a ≃ b ⟶ (G • F) a ≃ G b := compFunFunFun.effEffEff α β γ F G a ▸ HasEquivCongrArg.equiv_congrArg U G;
    HasTrans.trans ⊙ f₁ 

    instance : HasDependentRefl    (DependentArrow U) := ⟨refl  U⟩
    instance : HasDependentTrans   (DependentArrow U) := ⟨trans U⟩
    instance : IsDependentPreorder (DependentArrow U) := ⟨⟩
  
  end DependentArrow

  instance hasDependentArrows : HasDependentArrows U U hInst.equivUniverse := ⟨DependentArrow U⟩

end HasLinearFunOp
