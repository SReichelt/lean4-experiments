import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors
import Structure.Generic.Axioms.AbstractEquivalences
import Structure.Generic.Axioms.GeneralizedProperties
import Structure.Generic.Notation

open GeneralizedProperty
open GeneralizedRelation



set_option autoBoundImplicitLocal false
--set_option pp.universes true



def GeneralizedDependentProperty {U V : Universe} (P : GeneralizedProperty ⌈U⌉ V) (W : Universe) :=
∀ {α}, P α → (α → W)

namespace GeneralizedDependentProperty

  variable {U V : Universe} {P : GeneralizedProperty ⌈U⌉ V} {W : Universe}

  section Properties

    variable (D : GeneralizedDependentProperty P W)

    class HasDependentInst [h : HasInst P] where
    (inst {α : U} (a : α) : D (h.inst α) a)

    def instProp [h : HasInst P] (α : U) : GeneralizedProperty ⌈α⌉ W := D (h.inst α)
    instance [HasInst P] [h : HasDependentInst D] (α : U) : HasInst (instProp D α) := ⟨h.inst⟩

  end Properties

end GeneralizedDependentProperty

open GeneralizedDependentProperty



def GeneralizedDependentRelation {U V : Universe} (R : GeneralizedRelation ⌈U⌉ V) (W : Universe) :=
∀ {α β}, R α β → (α → β → W)

namespace GeneralizedDependentRelation

  variable {U V : Universe} {R : GeneralizedRelation ⌈U⌉ V} {W : Universe}

  section Properties

    variable (D : GeneralizedDependentRelation R W)

    class HasDependentRefl [h : HasRefl R] where
    (refl {α : U} (a : α) : D (h.refl α) a a)

    def reflRel [h : HasRefl R] (α : U) : GeneralizedRelation ⌈α⌉ W := D (h.refl α)
    instance [HasRefl R] [h : HasDependentRefl D] (α : U) : HasRefl (reflRel D α) := ⟨h.refl⟩

    variable [HasInternalFunctors V] [HasInternalFunctors W]

    class HasDependentTrans [h : HasTrans R] where
    (trans {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} : D F a b ⟶ D G b c ⟶ D (h.trans' F G) a c)

    class IsDependentPreorder [h : IsPreorder R] extends HasDependentRefl D, HasDependentTrans D

    variable [HasInternalEquivalences V] [HasInternalEquivalences W]

    class HasDependentSymm [h : HasSymm R] where
    (symm {α β : U} {F : R α β} {a : α} {b : β} : D F a b ⟷ D (h.symm' F) b a)

    class IsDependentEquivalence [h : IsEquivalence R] extends IsDependentPreorder D, HasDependentSymm D

  end Properties

  def HasDependentTrans.trans' {D : GeneralizedDependentRelation R W}
                               [HasInternalFunctors V] [HasInternalFunctors W] [HasTrans R] [h : HasDependentTrans D]
                               {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (f : D F a b) (g : D G b c) :
    D (HasTrans.trans' F G) a c :=
  h.trans f g

  def HasDependentSymm.symm' {D : GeneralizedDependentRelation R W}
                             [HasInternalFunctors V] [HasInternalFunctors W] [HasInternalEquivalences V] [HasInternalEquivalences W]
                             [HasSymm  R] [h : HasDependentSymm  D]
                             {α β : U} {F : R α β} {a : α} {b : β} (f : D F a b) :
   D (HasSymm.symm' F) b a :=
  HasInternalEquivalences.to h.symm f

  section Notation

    @[reducible] def depRevComp {D : GeneralizedDependentRelation R W} [HasInternalFunctors V] [HasInternalFunctors W]
                                [HasTrans R] [h : HasDependentTrans D]
                                {α β γ : U} {F : R α β} {G : R β γ} {a : α} {b : β} {c : γ} (g : D G b c) (f : D F a b) :
      D (G • F) a c :=
    h.trans' f g
    -- TODO: What is the correct way to overload this?
    --infixr:90 " • " => depRevComp

    @[reducible] def depIdent (D : GeneralizedDependentRelation R W) [HasRefl R] [h : HasDependentRefl D] {α : U} (a : α) :
      D (ident R α) a a :=
    h.refl a

    @[reducible] def depInv {D : GeneralizedDependentRelation R W}
                            [HasInternalFunctors V] [HasInternalFunctors W] [HasInternalEquivalences V] [HasInternalEquivalences W]
                            [HasSymm R] [h : HasDependentSymm D]
                            {α β : U} {F : R α β} {a : α} {b : β} (f : D F a b) :
      D F⁻¹ b a :=
    h.symm' f
    --postfix:max "⁻¹" => depInv

  end Notation

end GeneralizedDependentRelation

open GeneralizedDependentRelation



section AttachedDependentRelations

  variable (U V W : Universe) [HasInternalFunctors V] [HasInternalFunctors W]

  class HasDependentArrows [h : HasArrows ⌈U⌉ V] where
  (Arrow      : GeneralizedDependentRelation h.Arrow W)
  [isPreorder : IsDependentPreorder Arrow]

  namespace HasDependentArrows
    variable [HasArrows ⌈U⌉ V] [h : HasDependentArrows U V W]
    instance arrowPreorder : IsDependentPreorder h.Arrow := h.isPreorder
    notation:20 a:21 " ⇝[" F:0 "] " b:21 => HasDependentArrows.Arrow F a b
    notation:20 a:21 " ⇝[" F:0 "," V':0 "," W':0 "] " b:21 => HasDependentArrows.Arrow (V := V') (W := W') F a b
  end HasDependentArrows

  variable [HasInternalEquivalences V] [HasInternalEquivalences W]

  class HasDependentEquivalences [h : HasEquivalences ⌈U⌉ V] where
  (Equiv   : GeneralizedDependentRelation h.Equiv W)
  [isEquiv : IsDependentEquivalence Equiv]

  namespace HasDependentEquivalences
    variable [HasEquivalences ⌈U⌉ V] [h : HasDependentEquivalences U V W]
    instance equivEquivalence : IsDependentEquivalence h.Equiv := h.isEquiv
    notation:25 a:26 " ≃[" F:0 "] " b:26 => HasDependentEquivalences.Equiv F a b
    notation:25 a:26 " ≃[" F:0 "," V':0 "," W':0 "] " b:26 => HasDependentEquivalences.Equiv (V := V') (W := W') F a b
  end HasDependentEquivalences

  class HasDependentProducts [h : HasProducts ⌈U⌉ V] where
  (Product : GeneralizedDependentRelation h.Product W)
  [hasSymm : HasDependentSymm Product]

  namespace HasDependentProducts
    variable [HasProducts ⌈U⌉ V] [h : HasDependentProducts U V W]
    instance productSymm : HasDependentSymm h.Product := h.hasSymm
    notation:35 a:36 " ⧆[" P:0 "] " b:36 => HasDependentProducts.Product P a b
    notation:35 a:36 " ⧆[" P:0 "," V':0 "," W':0 "] " b:36 => HasDependentProducts.Product (V := V') (W := W') P a b
  end HasDependentProducts

end AttachedDependentRelations
