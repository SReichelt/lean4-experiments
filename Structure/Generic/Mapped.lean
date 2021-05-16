--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- Mapped views on structures from `Axioms.lean`.



import Structure.Generic.Axioms

open GeneralizedRelation



set_option autoBoundImplicitLocal false

universes u v w



def mapOperation {α : Sort u} {β : Sort v} {ω : Sort w} (m : ω → α) (op : α → α → β) :
  ω → ω → β :=
λ a b => op (m a) (m b)



namespace GeneralizedProperty

  variable {α : Sort u} {V : Sort v} [HasInstances V]
           {ω : Sort w} (m : ω → α)
           (P : GeneralizedProperty α V)

  instance mapInst [h : HasInst P] : HasInst (P ∘ m) := ⟨λ a => h.inst (m a)⟩

end GeneralizedProperty



namespace GeneralizedRelation

  variable {α : Sort u} {V : Sort v} [IsKind V]
           {ω : Sort w} (m : ω → α) (R : GeneralizedRelation α V)

  instance mapRefl  [h : HasRefl  R] : HasRefl  (mapOperation m R) := ⟨λ a => h.refl (m a)⟩
  instance mapSymm  [h : HasSymm  R] : HasSymm  (mapOperation m R) := ⟨h.symm⟩
  instance mapTrans [h : HasTrans R] : HasTrans (mapOperation m R) := ⟨h.trans⟩

  instance mapPreorder    [IsPreorder    R] : IsPreorder    (mapOperation m R) := ⟨⟩
  instance mapEquivalence [IsEquivalence R] : IsEquivalence (mapOperation m R) := ⟨⟩

end GeneralizedRelation



section Morphisms

  variable {α : Sort u} {V : Sort v} [IsKind V] [HasInstanceArrows V]
           {ω : Sort w} (m : ω → α)
           (R : GeneralizedRelation α V)

  instance mapComposition  [h : HasComposition  R] :
    HasComposition  (mapOperation m R) :=
  { assocLR  := h.assocLR,
    assocRL  := h.assocRL }

  instance mapMorphisms    [h : HasMorphisms    R] :
    HasMorphisms    (mapOperation m R) :=
  { leftId   := h.leftId,
    rightId  := h.rightId }

  instance mapIsomorphisms [h : HasIsomorphisms R] :
    HasIsomorphisms (mapOperation m R) :=
  { leftInv  := h.leftInv,
    rightInv := h.rightInv,
    invInv   := h.invInv,
    compInv  := h.compInv,
    idInv    := λ a => h.idInv (m a) }

end Morphisms



section Functors

  variable {α : Sort u} {V : Sort v} [IsKind V] [HasInstanceArrows V]
           {ω : Sort w} (m : ω → α)
           (R S : GeneralizedRelation α V) (F : BaseFunctor R S)

  instance mapReflFunctor  [HasRefl  R] [HasRefl  S] [h : IsReflFunctor  R S F] :
    IsReflFunctor  (mapOperation m R) (mapOperation m S) F :=
  ⟨λ a => h.respectsRefl (m a)⟩

  instance mapSymmFunctor  [HasSymm  R] [HasSymm S ] [h : IsSymmFunctor  R S F] :
    IsSymmFunctor  (mapOperation m R) (mapOperation m S) F :=
  ⟨h.respectsSymm⟩

  instance mapTransFunctor [HasTrans R] [HasTrans S] [h : IsTransFunctor R S F] :
    IsTransFunctor (mapOperation m R) (mapOperation m S) F :=
  ⟨h.respectsTrans⟩

  instance mapPreorderFunctor    [IsPreorder    R] [IsPreorder    S] [IsPreorderFunctor    R S F] :
    IsPreorderFunctor    (mapOperation m R) (mapOperation m S) F := ⟨⟩
  instance mapEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalenceFunctor R S F] :
    IsEquivalenceFunctor (mapOperation m R) (mapOperation m S) F := ⟨⟩

end Functors



section NaturalTransformations

  variable {α : Sort u} {β : Sort w} {V : Sort v} [IsKind V] [HasInstanceEquivalences V]
           {ω : Sort w} (m : ω → α)
           (R : GeneralizedRelation α V) (S : GeneralizedRelation β V) [HasMorphisms S]
           {mF mG : α → β} (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) (G : ∀ {a b}, R a b ⟶' S (mG a) (mG b))
           (n : ∀ a, S (mF a) (mG a))
  
  instance mapNaturalTransformation [h : IsNaturalTransformation R S F G n] :
    IsNaturalTransformation (mapOperation m R) S F G (λ a => n (m a)) :=
  ⟨h.nat⟩

end NaturalTransformations
