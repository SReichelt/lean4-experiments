--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- Lemmas following from axioms in `Axioms.lean`.



import Structure.Generic.Axioms
import mathlib4_experiments.Data.Equiv.Basic

open GeneralizedRelation



set_option autoBoundImplicitLocal false

universes u v w



@[simp] theorem elimRec {α : Sort u} {a a' : α} {ha : a = a'}
                        {T : α → Sort v} {x : T a}
                        {β : Sort w} {f : {a : α} → T a → β} :
  @f a' (ha ▸ x) = f x :=
by subst ha; rfl



namespace HasFunOp

  variable {U : Universe} [h : HasFunOp U]

  -- The "swap" functor swaps the arguments of a nested functor. Its plain version `swapFun` actually
  -- just fixes the second argument.

  def swapIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) : HasExternalFunctors.IsFun (λ a : α => F a b) :=
  h.compIsFun F (appFun' b γ)

  def swapFun' {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) : α ⟶' γ := HasInternalFunctors.mkFun' (swapIsFun F                                 b)
  def swapFun  {α β γ : U} (F : α ⟶  β ⟶ γ) (b : β) : α ⟶  γ := HasInternalFunctors.mkFun  (swapIsFun (HasInternalFunctors.toBundled F) b)

  @[simp] theorem swapFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) (a : α) :
    (swapFun F b) a = F⟮a⟯ b :=
  by apply HasInternalFunctors.mkFun.eff

  theorem swapFunFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) :
    HasInternalFunctors.mkFun (swapIsFun F b) = HasInternalFunctors.mkFun (h.compIsFun F (HasInternalFunctors.toBundled (appFun b γ))) :=
  HasInternalFunctors.toFromBundled (appFun' b γ) ▸ rfl

  def swapFunIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) : HasExternalFunctors.IsFun (λ b : β => HasInternalFunctors.mkFun (swapIsFun F b)) :=
  funext (swapFunFun.def F) ▸ h.compIsFun (appFunFun' β γ) (compFunFun' F γ)

  def swapFunFun' {α β γ : U} (F : α ⟶' β ⟶ γ) : β ⟶' α ⟶ γ := HasInternalFunctors.mkFun' (swapFunIsFun F)
  def swapFunFun  {α β γ : U} (F : α ⟶  β ⟶ γ) : β ⟶  α ⟶ γ := HasInternalFunctors.mkFun  (swapFunIsFun (HasInternalFunctors.toBundled F))

  @[simp] theorem swapFunFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) :
    (swapFunFun F)⟮b⟯ = swapFun F b :=
  by apply HasInternalFunctors.mkFun.eff

  theorem swapFunFunFun.def (α β γ : U) (F : α ⟶ β ⟶ γ) :
    swapFunFun F = HasInternalFunctors.mkFun (h.compIsFun (appFunFun' β γ) (HasInternalFunctors.toBundled (compFunFun F γ))) :=
  HasInternalFunctors.toFromBundled (compFunFun' (HasInternalFunctors.toBundled F) γ) ▸ elimRec

  def swapFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ F : α ⟶ β ⟶ γ => swapFunFun F) :=
  funext (swapFunFunFun.def α β γ) ▸ h.compIsFun (compFunFunFun' α (β ⟶ γ) γ)
                                                 (compFunFun' (appFunFun' β γ) (α ⟶ γ))

  def swapFunFunFun' (α β γ : U) : (α ⟶ β ⟶ γ) ⟶' (β ⟶ α ⟶ γ) := HasInternalFunctors.mkFun' (swapFunFunIsFun α β γ)
  def swapFunFunFun  (α β γ : U) : (α ⟶ β ⟶ γ) ⟶  (β ⟶ α ⟶ γ) := HasInternalFunctors.mkFun  (swapFunFunIsFun α β γ)

  @[simp] theorem swapFunFunFun.eff (α β γ : U) (F : α ⟶ β ⟶ γ) :
    (swapFunFunFun α β γ)⟮F⟯ = swapFunFun F :=
  by apply HasInternalFunctors.mkFun.eff

  -- In particular, reverse composition is also functorial.

  theorem revCompFunFun.def (α : U) {β γ : U} (G : β ⟶' γ) (F : α ⟶ β) :
    HasInternalFunctors.mkFun (h.compIsFun (HasInternalFunctors.toBundled F) G) = (compFunFun F γ)⟮HasInternalFunctors.fromBundled G⟯ :=
  Eq.subst (motive := λ H => HasInternalFunctors.mkFun (h.compIsFun (HasInternalFunctors.toBundled F) H) = (compFunFun F γ)⟮HasInternalFunctors.fromBundled G⟯)
           (HasInternalFunctors.toFromBundled G)
           (Eq.symm (compFunFun.eff F γ (HasInternalFunctors.fromBundled G)))

  def revCompFunIsFun (α : U) {β γ : U} (G : β ⟶' γ) :
    HasExternalFunctors.IsFun (λ F : α ⟶ β => HasInternalFunctors.mkFun (h.compIsFun (HasInternalFunctors.toBundled F) G)) :=
  funext (revCompFunFun.def α G) ▸ swapIsFun (compFunFunFun' α β γ) (HasInternalFunctors.fromBundled G)

  def revCompFunFun' (α : U) {β γ : U} (G : β ⟶' γ) : (α ⟶ β) ⟶' (α ⟶ γ) := HasInternalFunctors.mkFun' (revCompFunIsFun α G)
  def revCompFunFun  (α : U) {β γ : U} (G : β ⟶  γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasInternalFunctors.mkFun  (revCompFunIsFun α (HasInternalFunctors.toBundled G))

  @[simp] theorem revCompFunFun.eff (α : U) {β γ : U} (G : β ⟶ γ) (F : α ⟶ β) :
    (revCompFunFun α G)⟮F⟯ = G ⊙ F :=
  by apply HasInternalFunctors.mkFun.eff

  theorem revCompFunFunFun.def (α β γ : U) (G : β ⟶ γ) :
    HasInternalFunctors.mkFun (revCompFunIsFun α (HasInternalFunctors.toBundled G)) = HasInternalFunctors.mkFun (swapIsFun (compFunFunFun' α β γ) G) :=
  congrArg (λ H => HasInternalFunctors.mkFun (swapIsFun (compFunFunFun' α β γ) H)) (HasInternalFunctors.fromToBundled G) ▸ elimRec

  def revCompFunFunIsFun (α β γ : U) :
    HasExternalFunctors.IsFun (λ G : β ⟶ γ => revCompFunFun α G) :=
  funext (revCompFunFunFun.def α β γ) ▸ swapFunIsFun (compFunFunFun' α β γ)

  def revCompFunFunFun' (α β γ : U) : (β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.mkFun' (revCompFunFunIsFun α β γ)
  def revCompFunFunFun  (α β γ : U) : (β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.mkFun  (revCompFunFunIsFun α β γ)

  @[simp] theorem revCompFunFunFun.eff (α β γ : U) (G : β ⟶ γ) :
    (revCompFunFunFun α β γ)⟮G⟯ = revCompFunFun α G :=
  by apply HasInternalFunctors.mkFun.eff

  -- Composition of a function with two arguments.

  def compFun₂ {α β γ δ : U} (F : α ⟶ β ⟶ γ) (G : γ ⟶ δ) : α ⟶ β ⟶ δ := swapFunFun (revCompFunFun α G ⊙ swapFunFun F)

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `H : β ⟶ γ` and an argument `b : β`, then the
  -- construction of `H b` is also functorial.

  theorem substFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) (a : α) :
    F a (G a) = HasInternalFunctors.mkFun (swapIsFun F (G a)) a :=
  Eq.symm (HasInternalFunctors.mkFun.eff (swapIsFun F (G a)) a)

  def substIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : HasExternalFunctors.IsFun (λ a : α => F a (G a)) :=
  funext (substFun.def F G) ▸ h.dupIsFun (swapFunFun' F ⊙' G)

  def substFun' {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : α ⟶' γ := HasInternalFunctors.mkFun' (substIsFun F                    G)
  def substFun  {α β γ : U} (F : α ⟶  β ⟶ γ) (G : α ⟶  β) : α ⟶  γ := HasInternalFunctors.mkFun  (substIsFun (HasInternalFunctors.toBundled F) (HasInternalFunctors.toBundled G))

  @[simp] theorem substFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) :
    (substFun F G) a = F⟮a⟯ (G a) :=
  by apply HasInternalFunctors.mkFun.eff

  theorem substFunFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶ β) :
    HasInternalFunctors.mkFun (substIsFun F (HasInternalFunctors.toBundled G)) =
    HasInternalFunctors.mkFun (h.dupIsFun (HasInternalFunctors.toBundled (HasInternalFunctors.mkFun (h.compIsFun (HasInternalFunctors.toBundled G) (swapFunFun' F))))) :=
  HasInternalFunctors.toFromBundled _ ▸ elimRec

  def substFunIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) :
    HasExternalFunctors.IsFun (λ G : α ⟶ β => HasInternalFunctors.mkFun (substIsFun F (HasInternalFunctors.toBundled G))) :=
  funext (substFunFun.def F) ▸ h.compIsFun (revCompFunFun' α (swapFunFun' F)) (dupFunFun' α γ)

  def substFunFun' {α β γ : U} (F : α ⟶' β ⟶ γ) : (α ⟶ β) ⟶' (α ⟶ γ) := HasInternalFunctors.mkFun' (substFunIsFun F)
  def substFunFun  {α β γ : U} (F : α ⟶  β ⟶ γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasInternalFunctors.mkFun  (substFunIsFun (HasInternalFunctors.toBundled F))

  @[simp] theorem substFunFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) :
    (substFunFun F)⟮G⟯ = substFun F G :=
  by apply HasInternalFunctors.mkFun.eff

  theorem substFunFunFun.def (α β γ : U) (F : α ⟶ β ⟶ γ) :
    substFunFun F = HasInternalFunctors.mkFun (h.compIsFun (HasInternalFunctors.toBundled (revCompFunFun α (swapFunFun F))) (dupFunFun' α γ)) :=
  HasInternalFunctors.toFromBundled _ ▸ HasInternalFunctors.toFromBundled _ ▸ elimRec

  def substFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ F : α ⟶ β ⟶ γ => substFunFun F) :=
  funext (substFunFunFun.def α β γ) ▸ h.compIsFun (revCompFunFunFun' α β (α ⟶ γ) ⊙' swapFunFunFun' α β γ)
                                                  (revCompFunFun' (α ⟶ β) (dupFunFun' α γ))

  def substFunFunFun' (α β γ : U) : (α ⟶ β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.mkFun' (substFunFunIsFun α β γ)
  def substFunFunFun  (α β γ : U) : (α ⟶ β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.mkFun  (substFunFunIsFun α β γ)

  @[simp] theorem substFunFunFun.eff (α β γ : U) (F : α ⟶ β ⟶ γ) :
    (substFunFunFun α β γ)⟮F⟯ = substFunFun F :=
  by apply HasInternalFunctors.mkFun.eff



  -- Using the functoriality axioms and the constructions above, we can algorithmically prove
  -- functoriality of lambda terms. The algorithm to prove `HasExternalFunctors.IsFun (λ a : α => t)` is as follows:
  --
  --  Case                                 | Proof
  -- --------------------------------------+--------------------------------------------------------------
  --  `t` does not contain `a`             | `constIsFun α t`
  --  `t` is `a`                           | `idIsFun α`
  --  `t` is `G b` with `G : β ⟶ γ`:       |
  --    `a` appears only in `b`            | Prove that `λ a => b` is functorial, yielding a functor
  --                                       | `F : α ⟶ β`. Then the proof is `compIsFun F G`.
  --      `b` is `a`                       | Optimization: `HasInternalFunctors.isFun G`
  --    `a` appears only in `G`            | Prove that `λ a => G` is functorial, yielding a functor
  --                                       | `F : α ⟶ β ⟶ γ`. Then the proof is `swapIsFun F b`.
  --      `G` is `a`                       | Optimization: `appIsFun b γ`
  --    `a` appears in both                | Prove that `λ a => G` is functorial, yielding a functor
  --                                       | `F₁ : α ⟶ β ⟶ γ`. Prove that `λ a => b` is functorial,
  --                                       | yielding a functor `F₂ : α ⟶ β`. Then the proof is
  --                                       | `substIsFun F₁ F₂`.
  --  `t` is `HasInternalFunctors.mkFun (λ b : β => c)` | Prove that `λ a => c` is functorial when regarding `b` as a
  --                                       | constant, yielding a functor `F : α ⟶ γ` for every `b`.
  --                                       | Prove that  `λ b => F` is functorial, yielding a functor
  --                                       | `G : β ⟶ α ⟶ γ`. Then the proof is `swapFunIsFun G`.
  --
  -- (This list does not contain all possible optimizations.)



-- TODO: Add equivalences.
-- TODO: Add morphisms.

  instance : HasRefl    h.Fun := ⟨idFun⟩
  instance : HasTrans   h.Fun := ⟨compFunFunFun _ _ _⟩
  instance : IsPreorder h.Fun := ⟨⟩

  instance hasArrows : HasArrows ⌈U⌉ U := ⟨h.Fun⟩

end HasFunOp



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

    variable [HasFunOp V]

    instance hasSymm  : HasSymm  (ConstRel α c) := ⟨HasFunOp.idFun β⟩
    instance hasTrans : HasTrans (ConstRel α c) := ⟨HasFunOp.constFun β (HasFunOp.idFun β)⟩

    instance isPreorder    : IsPreorder    (ConstRel α c) := ⟨⟩
    instance isEquivalence : IsEquivalence (ConstRel α c) := ⟨⟩

    @[simp] theorem symmEq  {a₁ a₂    : α} : (hasSymm  α c).symm'  (a := a₁) (b := a₂)           c   = c :=
    HasFunOp.idFun.eff β c
    @[simp] theorem transEq {a₁ a₂ a₃ : α} : (hasTrans α c).trans' (a := a₁) (b := a₂) (c := a₃) c c = c :=
    let h₁ := congrArg HasInternalFunctors.funCoe (HasFunOp.constFun.eff β (HasFunOp.idFun β) c);
    Eq.trans (congrFun h₁ c) (HasFunOp.idFun.eff β c)

  end ConstRel

  variable {α : Sort u} {V : Universe} [HasFunOp V]

  def HasTrans.revTrans   {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} : R b c ⟶ R a b ⟶ R a c := HasFunOp.swapFunFun h.trans
  def HasTrans.revTrans'' {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} (g : R b c) : R a b ⟶ R a c := HasFunOp.swapFun h.trans g

end GeneralizedRelation

open GeneralizedRelation



namespace HasFunctorialArrows

  variable (U : Universe) [HasInternalFunctors U] [h : HasFunctorialArrows U]

  def arrowCongrArg  {α β : U} (F : α ⟶{U} β) {a b : α} : (a ⇝ b) ⟶{h.arrowUniverse} (F a ⇝ F b) := h.arrowCongr⟮HasRefl.refl F⟯
  def arrowCongrArg' {α β : U} (F : α ⟶'   β) {a b : α} : (a ⇝ b) ⟶{h.arrowUniverse} (F a ⇝ F b) := HasInternalFunctors.fromBundled.coe F ▸ arrowCongrArg U (HasInternalFunctors.fromBundled F)

  def arrowCongrFun {α β : U} {F G : α ⟶{U} β} (a : α) : (F ⇝ G) ⟶{h.arrowUniverse} (F a ⇝ G a) := HasFunOp.swapFun h.arrowCongr (HasRefl.refl a)

end HasFunctorialArrows

namespace HasFunctorialEquivalences

  variable (U : Universe) [HasInternalFunctors U] [h : HasFunctorialEquivalences U]

  def equivCongrArg  {α β : U} (F : α ⟶{U} β) {a b : α} : a ≃ b ⟶{h.equivUniverse} F a ≃ F b := h.equivCongr⟮HasRefl.refl F⟯
  def equivCongrArg' {α β : U} (F : α ⟶'   β) {a b : α} : a ≃ b ⟶{h.equivUniverse} F a ≃ F b := HasInternalFunctors.fromBundled.coe F ▸ equivCongrArg U (HasInternalFunctors.fromBundled F)

  def equivCongrFun {α β : U} {F G : α ⟶{U} β} (a : α) : F ≃ G ⟶{h.equivUniverse} F a ≃ G a := HasFunOp.swapFun h.equivCongr (HasRefl.refl a)

end HasFunctorialEquivalences



-- TODO: Should we use actual abstract equivalence here?

structure Iff' {U : Universe} [HasInternalFunctors U] (α β : U) where
(mp  : α ⟶ β)
(mpr : β ⟶ α)

notation:20 α:21 " ⟷{" U':0 "} " β:21 => Iff' (U := U') α β



section Morphisms

  variable {α : Sort u} {U : Universe} [HasInternalFunctors U] [he : HasFunctorialEquivalences U] {R : GeneralizedRelation α U}

  instance : HasFunctorialArrows U := HasFunctorialEquivalences.toHasFunctorialArrows U

  open IsCompositionRelation

  namespace IsCompositionRelation

    variable [HasTrans R] [IsCompositionRelation R]

    def comp_congrArg {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} : f₁ ≃ f₂ ⟶{he.equivUniverse} g₁ ≃ g₂ ⟶ g₁ • f₁ ≃ g₂ • f₂ :=
    he.equivCongr ⊙ HasFunctorialEquivalences.equivCongrArg U HasTrans.trans

    def comp_congrArg_left  {a b c : α} {f : R a b} {g₁ g₂ : R b c} : g₁ ≃ g₂ ⟶{he.equivUniverse} g₁ • f ≃ g₂ • f :=
    HasFunctorialEquivalences.equivCongrArg U (HasTrans.trans'' f)

    def comp_congrArg_right {a b c : α} {f₁ f₂ : R a b} {g : R b c} : f₁ ≃ f₂ ⟶{he.equivUniverse} g • f₁ ≃ g • f₂ :=
    HasFunOp.swapFun comp_congrArg (HasRefl.refl g)

    def comp_subst  {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} {e : R a c} : f₁ ≃ f₂ ⟶{he.equivUniverse} g₁ ≃ g₂ ⟶ g₂ • f₂ ≃ e ⟶ g₁ • f₁ ≃ e :=
    HasFunOp.compFun₂ comp_congrArg HasTrans.trans
    def comp_subst' {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} {e : R a c} : f₁ ≃ f₂ ⟶{he.equivUniverse} g₁ ≃ g₂ ⟶ e ≃ g₁ • f₁ ⟶ e ≃ g₂ • f₂ :=
    HasFunOp.compFun₂ comp_congrArg HasTrans.revTrans

    def comp_subst_left   {a b c : α} (f : R a b) {g₁ g₂ : R b c} {e : R a c} : g₁ ≃ g₂ ⟶{he.equivUniverse} g₂ • f ≃ e ⟶ g₁ • f ≃ e :=
    HasTrans.trans    ⊙ comp_congrArg_left
    def comp_subst_left'  {a b c : α} (f : R a b) {g₁ g₂ : R b c} {e : R a c} : g₁ ≃ g₂ ⟶{he.equivUniverse} e ≃ g₁ • f ⟶ e ≃ g₂ • f :=
    HasTrans.revTrans ⊙ comp_congrArg_left

    def comp_subst_right  {a b c : α} {f₁ f₂ : R a b} (g : R b c) {e : R a c} : f₁ ≃ f₂ ⟶{he.equivUniverse} g • f₂ ≃ e ⟶ g • f₁ ≃ e :=
    HasTrans.trans    ⊙ comp_congrArg_right
    def comp_subst_right' {a b c : α} {f₁ f₂ : R a b} (g : R b c) {e : R a c} : f₁ ≃ f₂ ⟶{he.equivUniverse} e ≃ g • f₁ ⟶ e ≃ g • f₂ :=
    HasTrans.revTrans ⊙ comp_congrArg_right

    def applyAssocLR_left  {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : (h • g) • f ≃ e ⟶{he.equivUniverse} h • (g • f) ≃ e :=
    HasTrans.trans'' (assocRL f g h)
    def applyAssocRL_left  {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : h • (g • f) ≃ e ⟶{he.equivUniverse} (h • g) • f ≃ e :=
    HasTrans.trans'' (assocLR f g h)
    def applyAssocLR_right {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : e ≃ (h • g) • f ⟶{he.equivUniverse} e ≃ h • (g • f) :=
    HasTrans.revTrans'' (assocLR f g h)
    def applyAssocRL_right {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : e ≃ h • (g • f) ⟶{he.equivUniverse} e ≃ (h • g) • f :=
    HasTrans.revTrans'' (assocRL f g h)

    def applyAssocLR {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : R a β₁} {f₂ : R a β₂} {g₁ : R β₁ γ₁} {g₂ : R β₂ γ₂} {h₁ : R γ₁ d} {h₂ : R γ₂ d} :
      (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ ⟶{he.equivUniverse} h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) :=
    applyAssocLR_right ⊙ applyAssocLR_left
    def applyAssocRL {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : R a β₁} {f₂ : R a β₂} {g₁ : R β₁ γ₁} {g₂ : R β₂ γ₂} {h₁ : R γ₁ d} {h₂ : R γ₂ d} :
      h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) ⟶{he.equivUniverse} (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ :=
    applyAssocRL_right ⊙ applyAssocRL_left

  end IsCompositionRelation

  namespace IsMorphismRelation

    variable [IsPreorder R] [IsMorphismRelation R]

    def leftCancelId  {a b : α} (f : R a b) {e : R b b} : e ≃ ident R b ⟶{he.equivUniverse} e • f ≃ f :=
    HasFunOp.swapFun (comp_subst_left  f) (leftId  f)
    def rightCancelId {a b : α} (f : R a b) {e : R a a} : e ≃ ident R a ⟶{he.equivUniverse} f • e ≃ f :=
    HasFunOp.swapFun (comp_subst_right f) (rightId f)

  end IsMorphismRelation

  open IsMorphismRelation

  namespace IsIsomorphismRelation

    variable [IsEquivalence R] [IsIsomorphismRelation R]

    def inv_congrArg {a b : α} {f₁ f₂ : R a b} : f₁ ≃ f₂ ⟶{he.equivUniverse} f₁⁻¹ ≃ f₂⁻¹ :=
    HasFunctorialEquivalences.equivCongrArg U HasSymm.symm

    def inv_subst  {a b : α} {f₁ f₂ : R a b} {e : R b a} : f₁ ≃ f₂ ⟶{he.equivUniverse} f₂⁻¹ ≃ e ⟶ f₁⁻¹ ≃ e :=
    HasTrans.trans    ⊙ inv_congrArg
    def inv_subst' {a b : α} {f₁ f₂ : R a b} {e : R b a} : f₁ ≃ f₂ ⟶{he.equivUniverse} e ≃ f₁⁻¹ ⟶ e ≃ f₂⁻¹ :=
    HasTrans.revTrans ⊙ inv_congrArg

    def leftCancel'     {a b c : α} (f : R a b) (g : R b c) : (g⁻¹ • g) • f ≃ f := (leftCancelId  f)⟮leftInv  g⟯
    def leftCancel      {a b c : α} (f : R a b) (g : R b c) : g⁻¹ • (g • f) ≃ f := applyAssocLR_left⟮leftCancel'     f g⟯
    def leftCancelInv'  {a b c : α} (f : R a b) (g : R c b) : (g • g⁻¹) • f ≃ f := (leftCancelId  f)⟮rightInv g⟯
    def leftCancelInv   {a b c : α} (f : R a b) (g : R c b) : g • (g⁻¹ • f) ≃ f := applyAssocLR_left⟮leftCancelInv'  f g⟯
    def rightCancel'    {a b c : α} (f : R a b) (g : R c a) : f • (g • g⁻¹) ≃ f := (rightCancelId f)⟮rightInv g⟯
    def rightCancel     {a b c : α} (f : R a b) (g : R c a) : (f • g) • g⁻¹ ≃ f := applyAssocRL_left⟮rightCancel'    f g⟯
    def rightCancelInv' {a b c : α} (f : R a b) (g : R a c) : f • (g⁻¹ • g) ≃ f := (rightCancelId f)⟮leftInv  g⟯
    def rightCancelInv  {a b c : α} (f : R a b) (g : R a c) : (f • g⁻¹) • g ≃ f := applyAssocRL_left⟮rightCancelInv' f g⟯

    def leftMulInv  {a b c : α} (f₁ : R a b) (f₂ : R a c) (g : R b c) : g • f₁ ≃ f₂ ⟷{he.equivUniverse} f₁ ≃ g⁻¹ • f₂ :=
    ⟨HasFunOp.swapFun (comp_subst_right' g⁻¹) (HasSymm.symm' (leftCancel f₁ g)),
     HasFunOp.swapFun (comp_subst_right  g)   (leftCancelInv f₂ g)⟩
    def leftMulInv' {a b c : α} (f₁ : R a b) (f₂ : R a c) (g : R c b) : g⁻¹ • f₁ ≃ f₂ ⟷{he.equivUniverse} f₁ ≃ g • f₂ :=
    ⟨HasFunOp.swapFun (comp_subst_right' g)   (HasSymm.symm' (leftCancelInv f₁ g)),
     HasFunOp.swapFun (comp_subst_right  g⁻¹) (leftCancel f₂ g)⟩

    def leftMul {a b c : α} (f₁ f₂ : R a b) (g : R b c) : g • f₁ ≃ g • f₂ ⟷{he.equivUniverse} f₁ ≃ f₂ :=
    ⟨HasTrans.revTrans'' (leftCancel f₂ g) ⊙ (leftMulInv f₁ (g • f₂) g).mp, comp_congrArg_right⟩

    def rightMulInv  {a b c : α} (f₁ : R a c) (f₂ : R b c) (g : R b a) : f₁ • g ≃ f₂ ⟷{he.equivUniverse} f₁ ≃ f₂ • g⁻¹ :=
    ⟨HasFunOp.swapFun (comp_subst_left' g⁻¹) (HasSymm.symm' (rightCancel f₁ g)),
     HasFunOp.swapFun (comp_subst_left  g)   (rightCancelInv f₂ g)⟩
    def rightMulInv' {a b c : α} (f₁ : R a c) (f₂ : R b c) (g : R a b) : f₁ • g⁻¹ ≃ f₂ ⟷{he.equivUniverse} f₁ ≃ f₂ • g :=
    ⟨HasFunOp.swapFun (comp_subst_left' g)   (HasSymm.symm' (rightCancelInv f₁ g)),
     HasFunOp.swapFun (comp_subst_left  g⁻¹) (rightCancel f₂ g)⟩

    def rightMul {a b c : α} (f₁ f₂ : R a b) (g : R c a) : f₁ • g ≃ f₂ • g ⟷{he.equivUniverse} f₁ ≃ f₂ :=
    ⟨HasTrans.revTrans'' (rightCancel f₂ g) ⊙ (rightMulInv f₁ (f₂ • g) g).mp, comp_congrArg_left⟩

    def eqInvIffInvEq {a b : α} (f : R a b) (g : R b a) : f ≃ g⁻¹ ⟷{he.equivUniverse} f⁻¹ ≃ g :=
    ⟨HasFunOp.swapFun inv_subst  (invInv g),
     HasFunOp.swapFun inv_subst' (HasSymm.symm' (invInv f))⟩

    def eqIffEqInv {a b : α} (f₁ f₂ : R a b) : f₁⁻¹ ≃ f₂⁻¹ ⟷{he.equivUniverse} f₁ ≃ f₂ :=
    ⟨HasTrans.revTrans'' (invInv f₂) ⊙ (eqInvIffInvEq f₁ f₂⁻¹).mpr, inv_congrArg⟩

    def leftRightMul {a b c d : α} (f₁ : R a b) (f₂ : R a c) (g₁ : R b d) (g₂ : R c d) :
      g₂⁻¹ • g₁ ≃ f₂ • f₁⁻¹ ⟷{he.equivUniverse} g₁ • f₁ ≃ g₂ • f₂ :=
    ⟨(leftMulInv' (g₁ • f₁) f₂ g₂).mp ⊙ applyAssocLR_left ⊙ (rightMulInv (g₂⁻¹ • g₁) f₂ f₁).mpr,
     (leftMulInv' g₁ (f₂ • f₁⁻¹) g₂).mpr ⊙ applyAssocLR_right ⊙ (rightMulInv g₁ (g₂ • f₂) f₁).mp⟩

    def swapInv  {a b c d : α} (f₁ : R a b) (f₂ : R c d) (g₁ : R d b) (g₂ : R c a) :
      g₁⁻¹ • f₁ ≃ f₂ • g₂⁻¹ ⟶{he.equivUniverse} f₁⁻¹ • g₁ ≃ g₂ • f₂⁻¹ :=
    (leftRightMul f₂ g₂ g₁ f₁).mpr ⊙ HasSymm.symm ⊙ (leftRightMul g₂ f₂ f₁ g₁).mp

    def swapInv' {a b c d : α} (f₁ : R a b) (f₂ : R c d) (g₁ : R d b) (g₂ : R c a) :
      f₂ • g₂⁻¹ ≃ g₁⁻¹ • f₁ ⟶{he.equivUniverse} g₂ • f₂⁻¹ ≃ f₁⁻¹ • g₁ :=
    HasSymm.symm ⊙ swapInv f₁ f₂ g₁ g₂ ⊙ HasSymm.symm

  end IsIsomorphismRelation

  open IsIsomorphismRelation

end Morphisms



section Functors

  variable {α : Sort u} {U : Universe} [HasFunOp U] [hasArrows : HasFunctorialArrows U]

  namespace idFun

    variable (R : GeneralizedRelation α U)

    instance isReflFunctor  [HasRefl  R] : IsReflFunctor  R R (HasFunOp.idFun' _) :=
    ⟨λ a   => HasRefl.refl (ident R a)⟩

    instance isSymmFunctor  [HasSymm  R] : IsSymmFunctor  R R (HasFunOp.idFun' _) :=
    ⟨λ f   => HasRefl.refl f⁻¹⟩

    instance isTransFunctor [HasTrans R] : IsTransFunctor R R (HasFunOp.idFun' _) :=
    ⟨λ f g => HasRefl.refl (g • f)⟩

    instance isPreorderFunctor    [IsPreorder    R] : IsPreorderFunctor    R R (HasFunOp.idFun' _) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] : IsEquivalenceFunctor R R (HasFunOp.idFun' _) := ⟨⟩

  end idFun

  namespace constFun

    variable (R : GeneralizedRelation α U) {β : U} (c : β)

    def idArrow : c ⇝ c := ident (hasArrows.Arrow β) c

    instance isReflFunctor  [HasRefl  R] : IsReflFunctor  R (ConstRel α c) (HasFunOp.constFun' _ c) :=
    ⟨λ _   => idArrow c⟩

    instance isSymmFunctor  [HasSymm  R] : IsSymmFunctor  R (ConstRel α c) (HasFunOp.constFun' _ c) :=
    ⟨λ _   => Eq.ndrec (motive := λ b : β => ⌈c ⇝ b⌉) (idArrow c) (Eq.symm (ConstRel.symmEq  α c))⟩

    instance isTransFunctor [HasTrans R] : IsTransFunctor R (ConstRel α c) (HasFunOp.constFun' _ c) :=
    ⟨λ _ _ => Eq.ndrec (motive := λ b : β => ⌈c ⇝ b⌉) (idArrow c) (Eq.symm (ConstRel.transEq α c))⟩

    instance isPreorderFunctor    [IsPreorder    R] : IsPreorderFunctor    R (ConstRel α c) (HasFunOp.constFun' _ c) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] : IsEquivalenceFunctor R (ConstRel α c) (HasFunOp.constFun' _ c) := ⟨⟩

  end constFun

  namespace compFun

    variable {R S T : GeneralizedRelation α U} (F : BaseFunctor R S) (G : BaseFunctor S T)

    instance isReflFunctor  [HasRefl  R] [HasRefl  S] [HasRefl  T] [hF : IsReflFunctor  R S F] [hG : IsReflFunctor  S T G] :
      IsReflFunctor  R T (G ⊙' F) :=
    ⟨λ a   => let e₁ : G (F (ident R a)) ⇝ G (ident S a) := HasFunctorialArrows.arrowCongrArg' U G (hF.respectsRefl a);
              let e₂ : G (ident S a) ⇝ ident T a         := hG.respectsRefl a;
              HasTrans.trans' e₁ e₂⟩

    instance isSymmFunctor  [HasSymm  R] [HasSymm  S] [HasSymm  T] [hF : IsSymmFunctor  R S F] [hG : IsSymmFunctor  S T G] :
      IsSymmFunctor  R T (G ⊙' F) :=
    ⟨λ f   => let e₁ : G (F f⁻¹) ⇝ G (F f)⁻¹   := HasFunctorialArrows.arrowCongrArg' U G (hF.respectsSymm f);
              let e₂ : G (F f)⁻¹ ⇝ (G (F f))⁻¹ := hG.respectsSymm (F f);
              HasTrans.trans' e₁ e₂⟩

    instance isTransFunctor [HasTrans R] [HasTrans S] [HasTrans T] [hF : IsTransFunctor R S F] [hG : IsTransFunctor S T G] :
      IsTransFunctor R T (G ⊙' F) :=
    ⟨λ f g => let e₁ : G (F (g • f)) ⇝ G (F g • F f)     := HasFunctorialArrows.arrowCongrArg' U G (hF.respectsTrans f g);
              let e₂ : G (F g • F f) ⇝ G (F g) • G (F f) := hG.respectsTrans (F f) (F g);
              HasTrans.trans' e₁ e₂⟩

    instance isPreorderFunctor    [IsPreorder    R] [IsPreorder    S] [IsPreorder    T] [IsPreorderFunctor    R S F] [IsPreorderFunctor    S T G] :
      IsPreorderFunctor    R T (G ⊙' F) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalence T] [IsEquivalenceFunctor R S F] [IsEquivalenceFunctor S T G] :
      IsEquivalenceFunctor R T (G ⊙' F) := ⟨⟩

  end compFun

  -- TODO: HasIdFun etc.

end Functors



section NaturalTransformations

  variable {α : Sort u} {V W : Universe} [HasInternalFunctors W] [HasFunctorialEquivalences W] [HasExternalFunctors V W]
           {β : Sort w} (R : GeneralizedRelation α V) (S : GeneralizedRelation β W)

  instance : HasFunctorialArrows W := HasFunctorialEquivalences.toHasFunctorialArrows W

  namespace IsNaturalTransformation

    def refl  [IsPreorder    S] [h : IsMorphismRelation    S] {mF       : α → β}
              (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) :
      IsNatural R S F F (λ a => ident S (mF a)) :=
    ⟨λ f => HasTrans.trans' (h.rightId (F f)) (HasSymm.symm' (h.leftId (F f)))⟩

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
    ⟨λ {a b} f => let e₁ := IsCompositionRelation.applyAssocLR_left⟮IsCompositionRelation.comp_congrArg_left  (f := nFG a) (hnGH.nat f)⟯;
                  let e₂ := IsCompositionRelation.applyAssocRL     ⟮IsCompositionRelation.comp_congrArg_right (g := nGH b) (hnFG.nat f)⟯;
                  HasTrans.trans' e₁ e₂⟩

  end IsNaturalTransformation

end NaturalTransformations
