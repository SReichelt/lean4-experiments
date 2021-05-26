import Structure.Generic.Axioms
import Structure.Generic.DerivedFunctors

import mathlib4_experiments.Data.Equiv.Basic

open GeneralizedRelation



set_option autoBoundImplicitLocal false

universes u v w



namespace HasLinearFunOp

  variable {U : Universe} [h : HasInternalFunctors U] [HasLinearFunOp U]

  -- TODO: Add equivalences.
  -- TODO: Add morphisms.

  instance : HasRefl    h.Fun := ⟨idFun⟩
  instance : HasTrans   h.Fun := ⟨compFunFunFun _ _ _⟩
  instance : IsPreorder h.Fun := ⟨⟩

  instance hasArrows : HasArrows ⌈U⌉ U := ⟨h.Fun⟩

end HasLinearFunOp



namespace GeneralizedProperty

  def ConstProp (α : Sort u) {V : Universe} {β : V} (c : β) : GeneralizedProperty α V := λ _ => β

  namespace ConstProp

    variable (α : Sort u) {V : Universe} {β : V} (c : β)

    instance hasInst : HasInst (ConstProp α c) := ⟨λ _ => c⟩

  end ConstProp

end GeneralizedProperty



namespace GeneralizedRelation

  def ConstRel (α : Sort u) {V : Universe} {β : V} (c : β) : GeneralizedRelation α V := λ _ _ => β

  namespace ConstRel
  
    variable (α : Sort u) {V : Universe} {β : V} (c : β)

    instance hasRefl  : HasRefl  (ConstRel α c) := ⟨λ _ => c⟩

    variable [HasInternalFunctors V] [HasAffineFunOp V]

    instance hasSymm  : HasSymm  (ConstRel α c) := ⟨HasLinearFunOp.idFun β⟩
    instance hasTrans : HasTrans (ConstRel α c) := ⟨HasAffineFunOp.constFun β (HasLinearFunOp.idFun β)⟩

    instance isPreorder    : IsPreorder    (ConstRel α c) := ⟨⟩
    instance isEquivalence : IsEquivalence (ConstRel α c) := ⟨⟩

    @[simp] theorem symmEq  {a₁ a₂    : α} : (hasSymm  α c).symm'  (a := a₁) (b := a₂)           c   = c :=
    HasLinearFunOp.idFun.eff β c
    @[simp] theorem transEq {a₁ a₂ a₃ : α} : (hasTrans α c).trans' (a := a₁) (b := a₂) (c := a₃) c c = c :=
    let h₁ := congrArg HasInternalFunctors.funCoe (HasAffineFunOp.constFun.eff β (HasLinearFunOp.idFun β) c);
    Eq.trans (congrFun h₁ c) (HasLinearFunOp.idFun.eff β c)

  end ConstRel

  variable {α : Sort u} {V : Universe} [HasInternalFunctors V] [HasLinearFunOp V]

  def HasTrans.revTrans   {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} : R b c ⟶ R a b ⟶ R a c := HasLinearFunOp.swapFunFun h.trans
  def HasTrans.revTrans'' {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} (g : R b c) : R a b ⟶ R a c := HasLinearFunOp.swapFun h.trans g

end GeneralizedRelation

open GeneralizedRelation



-- TODO: Should we use actual abstract equivalence here?

structure Iff' {U : Universe} [HasInternalFunctors U] (α β : U) where
(mp  : α ⟶ β)
(mpr : β ⟶ α)

infix:20 " ⟷' " => Iff'



section Morphisms

  variable {α : Sort u} {U : Universe} [HasInternalFunctors U] [he : HasFunctorialEquivalences U]
           [HasLinearFunOp he.equivUniverse] {R : GeneralizedRelation α U}

  instance : HasFunctorialArrows U := HasFunctorialEquivalences.toHasFunctorialArrows U

  open IsCompositionRelation

  namespace IsCompositionRelation

    variable [HasTrans R] [IsCompositionRelation R]

    def comp_congrArg {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} : f₁ ≃ f₂ ⟶ g₁ ≃ g₂ ⟶ g₁ • f₁ ≃ g₂ • f₂ :=
    he.equivCongr ⊙ HasFunctorialEquivalences.equiv_congrArg U HasTrans.trans

    def comp_congrArg_left  {a b c : α} {f : R a b} {g₁ g₂ : R b c} : g₁ ≃ g₂ ⟶ g₁ • f ≃ g₂ • f :=
    HasFunctorialEquivalences.equiv_congrArg U (HasTrans.trans ⟮f⟯)

    def comp_congrArg_right {a b c : α} {f₁ f₂ : R a b} {g : R b c} : f₁ ≃ f₂ ⟶ g • f₁ ≃ g • f₂ :=
    HasLinearFunOp.swapFun comp_congrArg (HasRefl.refl g)

    def comp_subst  {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} {e : R a c} : f₁ ≃ f₂ ⟶ g₁ ≃ g₂ ⟶ g₂ • f₂ ≃ e ⟶ g₁ • f₁ ≃ e :=
    HasLinearFunOp.compFun₂ comp_congrArg HasTrans.trans
    def comp_subst' {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} {e : R a c} : f₁ ≃ f₂ ⟶ g₁ ≃ g₂ ⟶ e ≃ g₁ • f₁ ⟶ e ≃ g₂ • f₂ :=
    HasLinearFunOp.compFun₂ comp_congrArg HasTrans.revTrans

    def comp_subst_left   {a b c : α} (f : R a b) {g₁ g₂ : R b c} {e : R a c} : g₁ ≃ g₂ ⟶ g₂ • f ≃ e ⟶ g₁ • f ≃ e :=
    HasTrans.trans    ⊙ comp_congrArg_left
    def comp_subst_left'  {a b c : α} (f : R a b) {g₁ g₂ : R b c} {e : R a c} : g₁ ≃ g₂ ⟶ e ≃ g₁ • f ⟶ e ≃ g₂ • f :=
    HasTrans.revTrans ⊙ comp_congrArg_left

    def comp_subst_right  {a b c : α} {f₁ f₂ : R a b} (g : R b c) {e : R a c} : f₁ ≃ f₂ ⟶ g • f₂ ≃ e ⟶ g • f₁ ≃ e :=
    HasTrans.trans    ⊙ comp_congrArg_right
    def comp_subst_right' {a b c : α} {f₁ f₂ : R a b} (g : R b c) {e : R a c} : f₁ ≃ f₂ ⟶ e ≃ g • f₁ ⟶ e ≃ g • f₂ :=
    HasTrans.revTrans ⊙ comp_congrArg_right

    def applyAssocLR_left  {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : (h • g) • f ≃ e ⟶ h • (g • f) ≃ e :=
    HasTrans.trans ⟮assocRL f g h⟯
    def applyAssocRL_left  {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : h • (g • f) ≃ e ⟶ (h • g) • f ≃ e :=
    HasTrans.trans ⟮assocLR f g h⟯
    def applyAssocLR_right {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : e ≃ (h • g) • f ⟶ e ≃ h • (g • f) :=
    HasTrans.revTrans'' (assocLR f g h)
    def applyAssocRL_right {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : e ≃ h • (g • f) ⟶ e ≃ (h • g) • f :=
    HasTrans.revTrans'' (assocRL f g h)

    def applyAssocLR {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : R a β₁} {f₂ : R a β₂} {g₁ : R β₁ γ₁} {g₂ : R β₂ γ₂} {h₁ : R γ₁ d} {h₂ : R γ₂ d} :
      (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ ⟶ h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) :=
    applyAssocLR_right ⊙ applyAssocLR_left
    def applyAssocRL {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : R a β₁} {f₂ : R a β₂} {g₁ : R β₁ γ₁} {g₂ : R β₂ γ₂} {h₁ : R γ₁ d} {h₂ : R γ₂ d} :
      h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) ⟶ (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ :=
    applyAssocRL_right ⊙ applyAssocRL_left

  end IsCompositionRelation

  namespace IsMorphismRelation

    variable [IsPreorder R] [IsMorphismRelation R]

    def leftCancelId  {a b : α} (f : R a b) {e : R b b} : e ≃ ident R b ⟶ e • f ≃ f :=
    HasLinearFunOp.swapFun (comp_subst_left  f) (leftId  f)
    def rightCancelId {a b : α} (f : R a b) {e : R a a} : e ≃ ident R a ⟶ f • e ≃ f :=
    HasLinearFunOp.swapFun (comp_subst_right f) (rightId f)

  end IsMorphismRelation

  open IsMorphismRelation

  namespace IsIsomorphismRelation

    variable [IsEquivalence R] [IsIsomorphismRelation R]

    def inv_congrArg {a b : α} {f₁ f₂ : R a b} : f₁ ≃ f₂ ⟶ f₁⁻¹ ≃ f₂⁻¹ :=
    HasFunctorialEquivalences.equiv_congrArg U HasSymm.symm

    def inv_subst  {a b : α} {f₁ f₂ : R a b} {e : R b a} : f₁ ≃ f₂ ⟶ f₂⁻¹ ≃ e ⟶ f₁⁻¹ ≃ e :=
    HasTrans.trans    ⊙ inv_congrArg
    def inv_subst' {a b : α} {f₁ f₂ : R a b} {e : R b a} : f₁ ≃ f₂ ⟶ e ≃ f₁⁻¹ ⟶ e ≃ f₂⁻¹ :=
    HasTrans.revTrans ⊙ inv_congrArg

    def leftCancel'     {a b c : α} (f : R a b) (g : R b c) : (g⁻¹ • g) • f ≃ f := (leftCancelId  f) (leftInv  g)
    def leftCancel      {a b c : α} (f : R a b) (g : R b c) : g⁻¹ • (g • f) ≃ f := applyAssocLR_left ⟮leftCancel'     f g⟯
    def leftCancelInv'  {a b c : α} (f : R a b) (g : R c b) : (g • g⁻¹) • f ≃ f := (leftCancelId  f) (rightInv g)
    def leftCancelInv   {a b c : α} (f : R a b) (g : R c b) : g • (g⁻¹ • f) ≃ f := applyAssocLR_left ⟮leftCancelInv'  f g⟯
    def rightCancel'    {a b c : α} (f : R a b) (g : R c a) : f • (g • g⁻¹) ≃ f := (rightCancelId f) (rightInv g)
    def rightCancel     {a b c : α} (f : R a b) (g : R c a) : (f • g) • g⁻¹ ≃ f := applyAssocRL_left ⟮rightCancel'    f g⟯
    def rightCancelInv' {a b c : α} (f : R a b) (g : R a c) : f • (g⁻¹ • g) ≃ f := (rightCancelId f) (leftInv  g)
    def rightCancelInv  {a b c : α} (f : R a b) (g : R a c) : (f • g⁻¹) • g ≃ f := applyAssocRL_left ⟮rightCancelInv' f g⟯

    def leftMulInv  {a b c : α} (f₁ : R a b) (f₂ : R a c) (g : R b c) : g • f₁ ≃ f₂ ⟷' f₁ ≃ g⁻¹ • f₂ :=
    ⟨HasLinearFunOp.swapFun (comp_subst_right' g⁻¹) (HasSymm.symm' (leftCancel f₁ g)),
     HasLinearFunOp.swapFun (comp_subst_right  g)   (leftCancelInv f₂ g)⟩
    def leftMulInv' {a b c : α} (f₁ : R a b) (f₂ : R a c) (g : R c b) : g⁻¹ • f₁ ≃ f₂ ⟷' f₁ ≃ g • f₂ :=
    ⟨HasLinearFunOp.swapFun (comp_subst_right' g)   (HasSymm.symm' (leftCancelInv f₁ g)),
     HasLinearFunOp.swapFun (comp_subst_right  g⁻¹) (leftCancel f₂ g)⟩

    def leftMul {a b c : α} (f₁ f₂ : R a b) (g : R b c) : g • f₁ ≃ g • f₂ ⟷' f₁ ≃ f₂ :=
    ⟨HasTrans.revTrans'' (leftCancel f₂ g) ⊙ (leftMulInv f₁ (g • f₂) g).mp, comp_congrArg_right⟩

    def rightMulInv  {a b c : α} (f₁ : R a c) (f₂ : R b c) (g : R b a) : f₁ • g ≃ f₂ ⟷' f₁ ≃ f₂ • g⁻¹ :=
    ⟨HasLinearFunOp.swapFun (comp_subst_left' g⁻¹) (HasSymm.symm' (rightCancel f₁ g)),
     HasLinearFunOp.swapFun (comp_subst_left  g)   (rightCancelInv f₂ g)⟩
    def rightMulInv' {a b c : α} (f₁ : R a c) (f₂ : R b c) (g : R a b) : f₁ • g⁻¹ ≃ f₂ ⟷' f₁ ≃ f₂ • g :=
    ⟨HasLinearFunOp.swapFun (comp_subst_left' g)   (HasSymm.symm' (rightCancelInv f₁ g)),
     HasLinearFunOp.swapFun (comp_subst_left  g⁻¹) (rightCancel f₂ g)⟩

    def rightMul {a b c : α} (f₁ f₂ : R a b) (g : R c a) : f₁ • g ≃ f₂ • g ⟷' f₁ ≃ f₂ :=
    ⟨HasTrans.revTrans'' (rightCancel f₂ g) ⊙ (rightMulInv f₁ (f₂ • g) g).mp, comp_congrArg_left⟩

    def eqInvIffInvEq {a b : α} (f : R a b) (g : R b a) : f ≃ g⁻¹ ⟷' f⁻¹ ≃ g :=
    ⟨HasLinearFunOp.swapFun inv_subst  (invInv g),
     HasLinearFunOp.swapFun inv_subst' (HasSymm.symm' (invInv f))⟩

    def eqIffEqInv {a b : α} (f₁ f₂ : R a b) : f₁⁻¹ ≃ f₂⁻¹ ⟷' f₁ ≃ f₂ :=
    ⟨HasTrans.revTrans'' (invInv f₂) ⊙ (eqInvIffInvEq f₁ f₂⁻¹).mpr, inv_congrArg⟩

    def leftRightMul {a b c d : α} (f₁ : R a b) (f₂ : R a c) (g₁ : R b d) (g₂ : R c d) :
      g₂⁻¹ • g₁ ≃ f₂ • f₁⁻¹ ⟷' g₁ • f₁ ≃ g₂ • f₂ :=
    ⟨(leftMulInv' (g₁ • f₁) f₂ g₂).mp ⊙ applyAssocLR_left ⊙ (rightMulInv (g₂⁻¹ • g₁) f₂ f₁).mpr,
     (leftMulInv' g₁ (f₂ • f₁⁻¹) g₂).mpr ⊙ applyAssocLR_right ⊙ (rightMulInv g₁ (g₂ • f₂) f₁).mp⟩

    def swapInv  {a b c d : α} (f₁ : R a b) (f₂ : R c d) (g₁ : R d b) (g₂ : R c a) :
      g₁⁻¹ • f₁ ≃ f₂ • g₂⁻¹ ⟶ f₁⁻¹ • g₁ ≃ g₂ • f₂⁻¹ :=
    (leftRightMul f₂ g₂ g₁ f₁).mpr ⊙ HasSymm.symm ⊙ (leftRightMul g₂ f₂ f₁ g₁).mp

    def swapInv' {a b c d : α} (f₁ : R a b) (f₂ : R c d) (g₁ : R d b) (g₂ : R c a) :
      f₂ • g₂⁻¹ ≃ g₁⁻¹ • f₁ ⟶ g₂ • f₂⁻¹ ≃ f₁⁻¹ • g₁ :=
    HasSymm.symm ⊙ swapInv f₁ f₂ g₁ g₂ ⊙ HasSymm.symm

  end IsIsomorphismRelation

  open IsIsomorphismRelation

end Morphisms



section Functors

  variable {α : Sort u}

  namespace idFun

    variable {U : Universe} [HasInstanceArrows U] [HasExternalFunctors U U]
             [HasIdFun U] (R : GeneralizedRelation α U)

    instance isReflFunctor  [HasRefl  R] : IsReflFunctor  R R (HasIdFun.idFun' _) :=
    ⟨λ a   => HasRefl.refl (ident R a)⟩

    variable [HasInternalFunctors U]

    instance isSymmFunctor  [HasSymm  R] : IsSymmFunctor  R R (HasIdFun.idFun' _) :=
    ⟨λ f   => HasRefl.refl f⁻¹⟩

    instance isTransFunctor [HasTrans R] : IsTransFunctor R R (HasIdFun.idFun' _) :=
    ⟨λ f g => HasRefl.refl (g • f)⟩

    instance isPreorderFunctor    [IsPreorder    R] : IsPreorderFunctor    R R (HasIdFun.idFun' _) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] : IsEquivalenceFunctor R R (HasIdFun.idFun' _) := ⟨⟩

  end idFun

  namespace constFun

    variable {U V : Universe} [HasInstanceArrows V] [HasExternalFunctors U V]
             [HasConstFun U V] (R : GeneralizedRelation α U) {β : V} (c : β)

    def idArrow : c ⇝ c := ident (HasInstanceArrows.Arrow β) c

    instance isReflFunctor  [HasRefl  R] : IsReflFunctor  R (ConstRel α c) (HasConstFun.constFun' _ c) :=
    ⟨λ _   => idArrow c⟩

    variable [HasInternalFunctors U] [HasInternalFunctors V] [HasAffineFunOp V]

    instance isSymmFunctor  [HasSymm  R] : IsSymmFunctor  R (ConstRel α c) (HasConstFun.constFun' _ c) :=
    ⟨λ _   => Eq.ndrec (motive := λ b : β => ⌈c ⇝ b⌉) (idArrow c) (Eq.symm (ConstRel.symmEq  α c))⟩

    instance isTransFunctor [HasTrans R] : IsTransFunctor R (ConstRel α c) (HasConstFun.constFun' _ c) :=
    ⟨λ _ _ => Eq.ndrec (motive := λ b : β => ⌈c ⇝ b⌉) (idArrow c) (Eq.symm (ConstRel.transEq α c))⟩

    instance isPreorderFunctor    [IsPreorder    R] : IsPreorderFunctor    R (ConstRel α c) (HasConstFun.constFun' _ c) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] : IsEquivalenceFunctor R (ConstRel α c) (HasConstFun.constFun' _ c) := ⟨⟩

  end constFun

  namespace compFun

    variable {U V W : Universe} [hV : HasInstanceArrows V] [hW : HasInstanceArrows W]
             [HasExternalFunctors U V] [HasExternalFunctors V W] [HasExternalFunctors U W]
             [HasExternalFunctors hV.arrowUniverse hW.arrowUniverse] [HasArrowCongrArg V W]
             [HasCompFun U V W]
             {R : GeneralizedRelation α U} {S : GeneralizedRelation α V} {T : GeneralizedRelation α W}
             (F : BaseFunctor R S) (G : BaseFunctor S T)

    instance isReflFunctor  [HasRefl  R] [HasRefl  S] [HasRefl  T] [hF : IsReflFunctor  R S F] [hG : IsReflFunctor  S T G] :
      IsReflFunctor  R T (G ⊙' F) :=
    ⟨λ a   => let e₁ : G (F (ident R a)) ⇝ G (ident S a) := HasArrowCongrArg.arrowCongrArg G (hF.respectsRefl a);
              let e₂ : G (ident S a) ⇝ ident T a         := hG.respectsRefl a;
              HasTrans.trans' e₁ e₂⟩

    variable [HasInternalFunctors U] [HasInternalFunctors V] [HasInternalFunctors W]

    instance isSymmFunctor  [HasSymm  R] [HasSymm  S] [HasSymm  T] [hF : IsSymmFunctor  R S F] [hG : IsSymmFunctor  S T G] :
      IsSymmFunctor  R T (G ⊙' F) :=
    ⟨λ f   => let e₁ : G (F f⁻¹) ⇝ G (F f)⁻¹   := HasArrowCongrArg.arrowCongrArg G (hF.respectsSymm f);
              let e₂ : G (F f)⁻¹ ⇝ (G (F f))⁻¹ := hG.respectsSymm (F f);
              HasTrans.trans' e₁ e₂⟩

    instance isTransFunctor [HasTrans R] [HasTrans S] [HasTrans T] [hF : IsTransFunctor R S F] [hG : IsTransFunctor S T G] :
      IsTransFunctor R T (G ⊙' F) :=
    ⟨λ f g => let e₁ : G (F (g • f)) ⇝ G (F g • F f)     := HasArrowCongrArg.arrowCongrArg G (hF.respectsTrans f g);
              let e₂ : G (F g • F f) ⇝ G (F g) • G (F f) := hG.respectsTrans (F f) (F g);
              HasTrans.trans' e₁ e₂⟩

    instance isPreorderFunctor    [IsPreorder    R] [IsPreorder    S] [IsPreorder    T] [IsPreorderFunctor    R S F] [IsPreorderFunctor    S T G] :
      IsPreorderFunctor    R T (G ⊙' F) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalence T] [IsEquivalenceFunctor R S F] [IsEquivalenceFunctor S T G] :
      IsEquivalenceFunctor R T (G ⊙' F) := ⟨⟩

  end compFun

end Functors



section NaturalTransformations

  variable {α : Sort u} {V W : Universe} [HasInternalFunctors W] [hW : HasFunctorialEquivalences W] [HasExternalFunctors V W]
           {β : Sort w} (R : GeneralizedRelation α V) (S : GeneralizedRelation β W)

  instance : HasFunctorialArrows W := hW.toHasFunctorialArrows W

  namespace IsNaturalTransformation

    def refl  [IsPreorder    S] [h : IsMorphismRelation    S] {mF       : α → β}
              (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) :
      IsNatural R S F F (λ a => ident S (mF a)) :=
    ⟨λ f => HasTrans.trans' (h.rightId (F f)) (HasSymm.symm' (h.leftId (F f)))⟩

    variable [HasLinearFunOp hW.equivUniverse]

    def symm  [IsEquivalence S] [h : IsIsomorphismRelation S] {mF mG    : α → β}
              (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) (G : ∀ {a b}, R a b ⟶' S (mG a) (mG b))
              (n : ∀ a, S (mF a) (mG a)) [hn : IsNatural R S F G n] :
      IsNatural R S G F (λ a => (n a)⁻¹) :=
    ⟨λ {a b} f => HasSymm.symm' ((IsIsomorphismRelation.leftRightMul (n a) (F f) (G f) (n b)).mpr (hn.nat f))⟩

    def trans [HasTrans      S] [h : IsCompositionRelation S] {mF mG mH : α → β}
              (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) (G : ∀ {a b}, R a b ⟶' S (mG a) (mG b)) (H : ∀ {a b}, R a b ⟶' S (mH a) (mH b))
              (nFG : ∀ a, S (mF a) (mG a))   (nGH : ∀ a, S (mG a) (mH a))
              [hnFG : IsNatural R S F G nFG] [hnGH : IsNatural R S G H nGH] :
      IsNatural R S F H (λ a => nGH a • nFG a) :=
    ⟨λ {a b} f => let e₁ := IsCompositionRelation.applyAssocLR_left ⟮IsCompositionRelation.comp_congrArg_left  (f := nFG a) (hnGH.nat f)⟯;
                  let e₂ := IsCompositionRelation.applyAssocRL      ⟮IsCompositionRelation.comp_congrArg_right (g := nGH b) (hnFG.nat f)⟯;
                  HasTrans.trans' e₁ e₂⟩

  end IsNaturalTransformation

end NaturalTransformations
