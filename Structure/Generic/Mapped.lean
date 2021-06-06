#exit

import Structure.Generic.Axioms

open GeneralizedRelation



set_option autoBoundImplicitLocal false

universes u v w



@[reducible] def mapOperation {α : Sort u} {β : Sort v} (op : α → α → β) {ω : Sort w} (m : ω → α) :
  ω → ω → β :=
λ a b => op (m a) (m b)



namespace GeneralizedProperty

  variable {α : Sort u} {V : Universe} (P : GeneralizedProperty α V)
           {ω : Sort w} (m : ω → α)

  instance mapInst [h : HasInst P] : HasInst (P ∘ m) := ⟨λ a => h.inst (m a)⟩

end GeneralizedProperty



namespace GeneralizedRelation

  variable {α : Sort u} {V : Universe} (R : GeneralizedRelation α V)

  section Mapping

    variable {ω : Sort w} (m : ω → α)

    instance mapRefl  [h : HasRefl  R] : HasRefl  (mapOperation R m) := ⟨λ a => h.refl (m a)⟩

    variable [HasInternalFunctors V]

    instance mapSymm  [h : HasSymm  R] : HasSymm  (mapOperation R m) := ⟨h.symm⟩
    instance mapTrans [h : HasTrans R] : HasTrans (mapOperation R m) := ⟨h.trans⟩

    instance mapPreorder    [IsPreorder    R] : IsPreorder    (mapOperation R m) := ⟨⟩
    instance mapEquivalence [IsEquivalence R] : IsEquivalence (mapOperation R m) := ⟨⟩

  end Mapping

  section Identity

    @[simp] theorem mapRefl.id  [h : HasRefl  R] : mapRefl  R id = h := match h with | ⟨_⟩ => rfl

    variable [HasInternalFunctors V]

    @[simp] theorem mapSymm.id  [h : HasSymm  R] : mapSymm  R id = h := match h with | ⟨_⟩ => rfl
    @[simp] theorem mapTrans.id [h : HasTrans R] : mapTrans R id = h := match h with | ⟨_⟩ => rfl

    @[simp] theorem mapPreorder.id    [h : IsPreorder    R] : mapPreorder    R id = h := match h with | { refl := _, trans := _ } => rfl
    @[simp] theorem mapEquivalence.id [h : IsEquivalence R] : mapEquivalence R id = h := match h with | { refl := _, symm := _, trans := _ } => rfl

  end Identity

end GeneralizedRelation



section Morphisms

  variable {α : Sort u} {V : Universe} [HasInternalFunctors V] [HasInstanceArrows V]
           (R : GeneralizedRelation α V)
           {ω : Sort w} (m : ω → α)

  instance mapComposition  [HasTrans      R] [h : IsCompositionRelation R] :
    IsCompositionRelation (mapOperation R m) :=
  { assocLR  := h.assocLR,
    assocRL  := h.assocRL }

  instance mapMorphisms    [IsPreorder    R] [h : IsMorphismRelation    R] :
    IsMorphismRelation    (mapOperation R m) :=
  { leftId   := h.leftId,
    rightId  := h.rightId }

  instance mapIsomorphisms [IsEquivalence R] [h : IsIsomorphismRelation R] :
    IsIsomorphismRelation (mapOperation R m) :=
  { leftInv  := h.leftInv,
    rightInv := h.rightInv,
    invInv   := h.invInv,
    compInv  := h.compInv,
    idInv    := λ a => h.idInv (m a) }

end Morphisms



section Functors

  variable {α : Sort u} {V W : Universe} [HasInstanceArrows W] [HasExternalFunctors V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation α W)
           (F : BaseFunctor R S)
           {ω : Sort w} (m : ω → α)

  instance mapReflFunctor  [HasRefl  R] [HasRefl  S] [h : IsReflFunctor  R S F] :
    IsReflFunctor  (mapOperation R m) (mapOperation S m) F :=
  ⟨λ a => h.respectsRefl (m a)⟩

  variable [HasInternalFunctors V] [HasInternalFunctors W]

  instance mapSymmFunctor  [HasSymm  R] [HasSymm  S] [h : IsSymmFunctor  R S F] :
    IsSymmFunctor  (mapOperation R m) (mapOperation S m) F :=
  ⟨h.respectsSymm⟩

  instance mapTransFunctor [HasTrans R] [HasTrans S] [h : IsTransFunctor R S F] :
    IsTransFunctor (mapOperation R m) (mapOperation S m) F :=
  ⟨h.respectsTrans⟩

  instance mapPreorderFunctor    [IsPreorder    R] [IsPreorder    S] [IsPreorderFunctor    R S F] :
    IsPreorderFunctor    (mapOperation R m) (mapOperation S m) F := ⟨⟩
  instance mapEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalenceFunctor R S F] :
    IsEquivalenceFunctor (mapOperation R m) (mapOperation S m) F := ⟨⟩

end Functors



section NaturalTransformations

  variable {α : Sort u} {β : Sort v} {V W : Universe} [HasInternalFunctors W] [HasInstanceEquivalences W] [HasExternalFunctors V W]
           (R : GeneralizedRelation α V) (S : GeneralizedRelation β W) [h : HasTrans S]
           {mF mG : α → β} (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) (G : ∀ {a b}, R a b ⟶' S (mG a) (mG b))
           (n : ∀ a, S (mF a) (mG a))
           {ω : Sort w} (m : ω → α)
  
  instance mapNaturality [h : IsNatural R S F G n] :
    IsNatural (mapOperation R m) S F G (λ a => n (m a)) :=
  ⟨h.nat⟩

end NaturalTransformations
