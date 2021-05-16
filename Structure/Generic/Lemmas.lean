--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- Lemmas following from axioms in `Axioms.lean`.



import Structure.Generic.Axioms
import mathlib4_experiments.Data.Equiv.Basic



set_option autoBoundImplicitLocal false

universes u v w



@[simp] theorem elimRec {α : Sort u} {a a' : α} {ha : a = a'}
                        {T : α → Sort v} {x : T a}
                        {β : Sort w} {f : {a : α} → T a → β} :
  @f a' (ha ▸ x) = f x :=
by subst ha; rfl



namespace HasFunOp

  variable {V : Sort v} [HasFun V] [h : HasFunOp V]

  -- The "swap" functor swaps the arguments of a nested functor. Its plain version `swapFun` actually
  -- just fixes the second argument.

  def swapIsFun {α β γ : V} (F : α ⟶' β ⟶ γ) (b : β) : HasIsFun.IsFun (λ a : α => F a b) :=
  h.compIsFun F (appFun' b γ)

  def swapFun' {α β γ : V} (F : α ⟶' β ⟶ γ) (b : β) : α ⟶' γ := HasFun.mkFun' (swapIsFun F                    b)
  def swapFun  {α β γ : V} (F : α ⟶  β ⟶ γ) (b : β) : α ⟶  γ := HasFun.mkFun  (swapIsFun (HasFun.toBundled F) b)

  @[simp] theorem swapFun.eff {α β γ : V} (F : α ⟶ β ⟶ γ) (b : β) (a : α) :
    (swapFun F b) a = F a b :=
  by apply HasFun.mkFun.eff

  theorem swapFunFun.def {α β γ : V} (F : α ⟶' β ⟶ γ) (b : β) :
    HasFun.mkFun (swapIsFun F b) = HasFun.mkFun (h.compIsFun F (HasFun.toBundled (appFun b γ))) :=
  HasFun.toFromBundled (appFun' b γ) ▸ rfl

  def swapFunIsFun {α β γ : V} (F : α ⟶' β ⟶ γ) : HasIsFun.IsFun (λ b : β => HasFun.mkFun (swapIsFun F b)) :=
  funext (swapFunFun.def F) ▸ h.compIsFun (appFunFun' β γ) (compFunFun' F γ)

  def swapFunFun' {α β γ : V} (F : α ⟶' β ⟶ γ) : β ⟶' α ⟶ γ := HasFun.mkFun' (swapFunIsFun F)
  def swapFunFun  {α β γ : V} (F : α ⟶  β ⟶ γ) : β ⟶  α ⟶ γ := HasFun.mkFun  (swapFunIsFun (HasFun.toBundled F))

  @[simp] theorem swapFunFun.eff {α β γ : V} (F : α ⟶ β ⟶ γ) (b : β) :
    (swapFunFun F) b = swapFun F b :=
  by apply HasFun.mkFun.eff

  theorem swapFunFunFun.def (α β γ : V) (F : α ⟶ β ⟶ γ) :
    swapFunFun F = HasFun.mkFun (h.compIsFun (appFunFun' β γ) (HasFun.toBundled (compFunFun F γ))) :=
  HasFun.toFromBundled (compFunFun' (HasFun.toBundled F) γ) ▸ elimRec

  def swapFunFunIsFun (α β γ : V) : HasIsFun.IsFun (λ F : α ⟶ β ⟶ γ => swapFunFun F) :=
  funext (swapFunFunFun.def α β γ) ▸ h.compIsFun (compFunFunFun' α (β ⟶ γ) γ)
                                                 (compFunFun' (appFunFun' β γ) (α ⟶ γ))

  def swapFunFunFun' (α β γ : V) : (α ⟶ β ⟶ γ) ⟶' (β ⟶ α ⟶ γ) := HasFun.mkFun' (swapFunFunIsFun α β γ)
  def swapFunFunFun  (α β γ : V) : (α ⟶ β ⟶ γ) ⟶  (β ⟶ α ⟶ γ) := HasFun.mkFun  (swapFunFunIsFun α β γ)

  @[simp] theorem swapFunFunFun.eff (α β γ : V) (F : α ⟶ β ⟶ γ) :
    (swapFunFunFun α β γ) F = swapFunFun F :=
  by apply HasFun.mkFun.eff

  -- In particular, reverse composition is also functorial.

  theorem revCompFunFun.def (α : V) {β γ : V} (G : β ⟶' γ) (F : α ⟶ β) :
    HasFun.mkFun (h.compIsFun (HasFun.toBundled F) G) = (compFunFun F γ) (HasFun.fromBundled G) :=
  Eq.subst (motive := λ H => HasFun.mkFun (h.compIsFun (HasFun.toBundled F) H) = (compFunFun F γ) (HasFun.fromBundled G))
           (HasFun.toFromBundled G)
           (Eq.symm (compFunFun.eff F γ (HasFun.fromBundled G)))

  def revCompFunIsFun (α : V) {β γ : V} (G : β ⟶' γ) :
    HasIsFun.IsFun (λ F : α ⟶ β => HasFun.mkFun (h.compIsFun (HasFun.toBundled F) G)) :=
  funext (revCompFunFun.def α G) ▸ swapIsFun (compFunFunFun' α β γ) (HasFun.fromBundled G)

  def revCompFunFun' (α : V) {β γ : V} (G : β ⟶' γ) : (α ⟶ β) ⟶' (α ⟶ γ) := HasFun.mkFun' (revCompFunIsFun α G)
  def revCompFunFun  (α : V) {β γ : V} (G : β ⟶  γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasFun.mkFun  (revCompFunIsFun α (HasFun.toBundled G))

  @[simp] theorem revCompFunFun.eff (α : V) {β γ : V} (G : β ⟶ γ) (F : α ⟶ β) :
    (revCompFunFun α G) F = G ⊙ F :=
  by apply HasFun.mkFun.eff

  theorem revCompFunFunFun.def (α β γ : V) (G : β ⟶ γ) :
    HasFun.mkFun (revCompFunIsFun α (HasFun.toBundled G)) = HasFun.mkFun (swapIsFun (compFunFunFun' α β γ) G) :=
  congrArg (λ H => HasFun.mkFun (swapIsFun (compFunFunFun' α β γ) H)) (HasFun.fromToBundled G) ▸ elimRec

  def revCompFunFunIsFun (α β γ : V) :
    HasIsFun.IsFun (λ G : β ⟶ γ => revCompFunFun α G) :=
  funext (revCompFunFunFun.def α β γ) ▸ swapFunIsFun (compFunFunFun' α β γ)

  def revCompFunFunFun' (α β γ : V) : (β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := HasFun.mkFun' (revCompFunFunIsFun α β γ)
  def revCompFunFunFun  (α β γ : V) : (β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasFun.mkFun  (revCompFunFunIsFun α β γ)

  @[simp] theorem revCompFunFunFun.eff (α β γ : V) (G : β ⟶ γ) :
    (revCompFunFunFun α β γ) G = revCompFunFun α G :=
  by apply HasFun.mkFun.eff

  -- Composition of a function with two arguments.

  def compFun₂ {α β γ δ : V} (F : α ⟶ β ⟶ γ) (G : γ ⟶ δ) : α ⟶ β ⟶ δ := swapFunFun (revCompFunFun α G ⊙ swapFunFun F)

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `H : β ⟶ γ` and an argument `b : β`, then the
  -- construction of `H b` is also functorial.

  theorem substFun.def {α β γ : V} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) (a : α) :
    F a (G a) = HasFun.mkFun (swapIsFun F (G a)) a :=
  Eq.symm (HasFun.mkFun.eff (swapIsFun F (G a)) a)

  def substIsFun {α β γ : V} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : HasIsFun.IsFun (λ a : α => F a (G a)) :=
  funext (substFun.def F G) ▸ h.dupIsFun (swapFunFun' F ⊙' G)

  def substFun' {α β γ : V} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : α ⟶' γ := HasFun.mkFun' (substIsFun F                    G)
  def substFun  {α β γ : V} (F : α ⟶  β ⟶ γ) (G : α ⟶  β) : α ⟶  γ := HasFun.mkFun  (substIsFun (HasFun.toBundled F) (HasFun.toBundled G))

  @[simp] theorem substFun.eff {α β γ : V} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) :
    (substFun F G) a = F a (G a) :=
  by apply HasFun.mkFun.eff

  theorem substFunFun.def {α β γ : V} (F : α ⟶' β ⟶ γ) (G : α ⟶ β) :
    HasFun.mkFun (substIsFun F (HasFun.toBundled G)) =
    HasFun.mkFun (h.dupIsFun (HasFun.toBundled (HasFun.mkFun (h.compIsFun (HasFun.toBundled G) (swapFunFun' F))))) :=
  HasFun.toFromBundled _ ▸ elimRec

  def substFunIsFun {α β γ : V} (F : α ⟶' β ⟶ γ) :
    HasIsFun.IsFun (λ G : α ⟶ β => HasFun.mkFun (substIsFun F (HasFun.toBundled G))) :=
  funext (substFunFun.def F) ▸ h.compIsFun (revCompFunFun' α (swapFunFun' F)) (dupFunFun' α γ)

  def substFunFun' {α β γ : V} (F : α ⟶' β ⟶ γ) : (α ⟶ β) ⟶' (α ⟶ γ) := HasFun.mkFun' (substFunIsFun F)
  def substFunFun  {α β γ : V} (F : α ⟶  β ⟶ γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasFun.mkFun  (substFunIsFun (HasFun.toBundled F))

  @[simp] theorem substFunFun.eff {α β γ : V} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) :
    (substFunFun F) G = substFun F G :=
  by apply HasFun.mkFun.eff

  theorem substFunFunFun.def (α β γ : V) (F : α ⟶ β ⟶ γ) :
    substFunFun F = HasFun.mkFun (h.compIsFun (HasFun.toBundled (revCompFunFun α (swapFunFun F))) (dupFunFun' α γ)) :=
  HasFun.toFromBundled _ ▸ HasFun.toFromBundled _ ▸ elimRec

  def substFunFunIsFun (α β γ : V) : HasIsFun.IsFun (λ F : α ⟶ β ⟶ γ => substFunFun F) :=
  funext (substFunFunFun.def α β γ) ▸ h.compIsFun (revCompFunFunFun' α β (α ⟶ γ) ⊙' swapFunFunFun' α β γ)
                                                  (revCompFunFun' (α ⟶ β) (dupFunFun' α γ))

  def substFunFunFun' (α β γ : V) : (α ⟶ β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := HasFun.mkFun' (substFunFunIsFun α β γ)
  def substFunFunFun  (α β γ : V) : (α ⟶ β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasFun.mkFun  (substFunFunIsFun α β γ)

  @[simp] theorem substFunFunFun.eff (α β γ : V) (F : α ⟶ β ⟶ γ) :
    (substFunFunFun α β γ) F = substFunFun F :=
  by apply HasFun.mkFun.eff



  -- Using the functoriality axioms and the constructions above, we can algorithmically prove
  -- functoriality of lambda terms. The algorithm to prove `HasIsFun.IsFun (λ a : α => t)` is as follows:
  --
  --  Case                                 | Proof
  -- --------------------------------------+--------------------------------------------------------------
  --  `t` does not contain `a`             | `constIsFun α t`
  --  `t` is `a`                           | `idIsFun α`
  --  `t` is `G b` with `G : β ⟶ γ`:       |
  --    `a` appears only in `b`            | Prove that `λ a => b` is functorial, yielding a functor
  --                                       | `F : α ⟶ β`. Then the proof is `compIsFun F G`.
  --      `b` is `a`                       | Optimization: `HasFun.isFun G`
  --    `a` appears only in `G`            | Prove that `λ a => G` is functorial, yielding a functor
  --                                       | `F : α ⟶ β ⟶ γ`. Then the proof is `swapIsFun F b`.
  --      `G` is `a`                       | Optimization: `appIsFun b γ`
  --    `a` appears in both                | Prove that `λ a => G` is functorial, yielding a functor
  --                                       | `F₁ : α ⟶ β ⟶ γ`. Prove that `λ a => b` is functorial,
  --                                       | yielding a functor `F₂ : α ⟶ β`. Then the proof is
  --                                       | `substIsFun F₁ F₂`.
  --  `t` is `HasFun.mkFun (λ b : β => c)` | Prove that `λ a => c` is functorial when regarding `b` as a
  --                                       | constant, yielding a functor `F : α ⟶ γ` for every `b`.
  --                                       | Prove that  `λ b => F` is functorial, yielding a functor
  --                                       | `G : β ⟶ α ⟶ γ`. Then the proof is `swapFunIsFun G`.
  --
  -- (This list does not contain all possible optimizations.)

end HasFunOp



namespace GeneralizedRelation

  variable {α : Sort u} {V : Sort v} [s : IsKind V]

  def HasTrans.revTrans {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} : R b c ⟶ R a b ⟶ R a c := HasFunOp.swapFunFun h.trans

  def HasTrans.trans''  {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} (f : R a b) : R b c ⟶ R a c := h.trans f
  def HasTrans.revTrans'' {R : GeneralizedRelation α V} [h : HasTrans R] {a b c : α} (g : R b c) : R a b ⟶ R a c := HasFunOp.swapFun h.trans g

end GeneralizedRelation

open GeneralizedRelation



-- TODO: Add equivalences.
-- TODO: Add morphisms.

namespace IsKind

  variable (V : Sort v) [s : IsKind V]

  instance : HasRefl    s.Fun := ⟨HasFunOp.idFun⟩
  instance : HasTrans   s.Fun := ⟨HasFunOp.compFunFunFun _ _ _⟩
  instance : IsPreorder s.Fun := ⟨⟩

  instance hasArrows : HasArrows V V := ⟨s.Fun⟩

end IsKind



namespace HasInstanceArrows

  variable (V : Sort v) [IsKind V] [HasInstanceArrows V]

  def arrCongrArg  {α β : V} (F : α ⟶{V} β) {a b : α} : (a ⇝ b) ⟶ (F a ⇝ F b) := (HasFun.funCoe (arrCongr V)) (HasRefl.refl F)
  def arrCongrArg' {α β : V} (F : α ⟶'   β) {a b : α} : (a ⇝ b) ⟶ (F a ⇝ F b) := HasFun.fromBundled.coe F ▸ arrCongrArg V (HasFun.fromBundled F)

  def arrCongrFun {α β : V} {F G : α ⟶{V} β} (a : α) : (F ⇝ G) ⟶ (F a ⇝ G a) := HasFunOp.swapFun (arrCongr V) (HasRefl.refl a)

end HasInstanceArrows

namespace HasInstanceEquivalences

  variable (V : Sort v) [IsKind V] [HasInstanceEquivalences V]

  def funCongrArg  {α β : V} (F : α ⟶{V} β) {a b : α} : a ≃ b ⟶ F a ≃ F b := (HasFun.funCoe (funCongr V)) (HasRefl.refl F)
  def funCongrArg' {α β : V} (F : α ⟶'   β) {a b : α} : a ≃ b ⟶ F a ≃ F b := HasFun.fromBundled.coe F ▸ funCongrArg V (HasFun.fromBundled F)

  def funCongrFun {α β : V} {F G : α ⟶{V} β} (a : α) : F ≃ G ⟶ F a ≃ G a := HasFunOp.swapFun (funCongr V) (HasRefl.refl a)

end HasInstanceEquivalences



-- TODO: Should we use actual abstract equivalence here?

structure Iff' {V : Sort v} [IsKind V] (α β : V) where
(mp  : α ⟶ β)
(mpr : β ⟶ α)

notation:20 α:21 " ⟷{" W:0 "} " β:21 => Iff' (V := W) α β



section Morphisms

  variable {α : Sort u} (V : Sort v) [IsKind V] [he : HasInstanceEquivalences V] {R : GeneralizedRelation α V}

  open HasComposition

  namespace HasComposition

    variable [h : HasComposition R]

    def comp_congrArg {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} : f₁ ≃ f₂ ⟶ g₁ ≃ g₂ ⟶ g₁ • f₁ ≃ g₂ • f₂ :=
    HasInstanceEquivalences.funCongr V ⊙ HasInstanceEquivalences.funCongrArg V HasTrans.trans

    def comp_congrArg_left  {a b c : α} {f : R a b} {g₁ g₂ : R b c} : g₁ ≃ g₂ ⟶ g₁ • f ≃ g₂ • f :=
    HasInstanceEquivalences.funCongrArg V (HasTrans.trans'' f)

    def comp_congrArg_right {a b c : α} {f₁ f₂ : R a b} {g : R b c} : f₁ ≃ f₂ ⟶ g • f₁ ≃ g • f₂ :=
    HasFunOp.swapFun (comp_congrArg V) (HasRefl.refl g)

    def comp_subst  {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} {e : R a c} : f₁ ≃ f₂ ⟶ g₁ ≃ g₂ ⟶ g₂ • f₂ ≃ e ⟶ g₁ • f₁ ≃ e :=
    HasFunOp.compFun₂ (comp_congrArg V) HasTrans.trans
    def comp_subst' {a b c : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c} {e : R a c} : f₁ ≃ f₂ ⟶ g₁ ≃ g₂ ⟶ e ≃ g₁ • f₁ ⟶ e ≃ g₂ • f₂ :=
    HasFunOp.compFun₂ (comp_congrArg V) HasTrans.revTrans

    def comp_subst_left   {a b c : α} (f : R a b) {g₁ g₂ : R b c} {e : R a c} : g₁ ≃ g₂ ⟶ g₂ • f ≃ e ⟶ g₁ • f ≃ e :=
    HasTrans.trans    ⊙ comp_congrArg_left V
    def comp_subst_left'  {a b c : α} (f : R a b) {g₁ g₂ : R b c} {e : R a c} : g₁ ≃ g₂ ⟶ e ≃ g₁ • f ⟶ e ≃ g₂ • f :=
    HasTrans.revTrans ⊙ comp_congrArg_left V

    def comp_subst_right  {a b c : α} {f₁ f₂ : R a b} (g : R b c) {e : R a c} : f₁ ≃ f₂ ⟶ g • f₂ ≃ e ⟶ g • f₁ ≃ e :=
    HasTrans.trans    ⊙ comp_congrArg_right V
    def comp_subst_right' {a b c : α} {f₁ f₂ : R a b} (g : R b c) {e : R a c} : f₁ ≃ f₂ ⟶ e ≃ g • f₁ ⟶ e ≃ g • f₂ :=
    HasTrans.revTrans ⊙ comp_congrArg_right V

    def applyAssocLR_left  {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : (h • g) • f ≃ e ⟶ h • (g • f) ≃ e :=
    HasTrans.trans'' (assocRL f g h)
    def applyAssocRL_left  {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : h • (g • f) ≃ e ⟶ (h • g) • f ≃ e :=
    HasTrans.trans'' (assocLR f g h)
    def applyAssocLR_right {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : e ≃ (h • g) • f ⟶ e ≃ h • (g • f) :=
    HasTrans.revTrans'' (assocLR f g h)
    def applyAssocRL_right {a b c d : α} {f : R a b} {g : R b c} {h : R c d} {e : R a d} : e ≃ h • (g • f) ⟶ e ≃ (h • g) • f :=
    HasTrans.revTrans'' (assocRL f g h)

    def applyAssocLR {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : R a β₁} {f₂ : R a β₂} {g₁ : R β₁ γ₁} {g₂ : R β₂ γ₂} {h₁ : R γ₁ d} {h₂ : R γ₂ d} :
      (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ ⟶ h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) :=
    applyAssocLR_right V ⊙ applyAssocLR_left V
    def applyAssocRL {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : R a β₁} {f₂ : R a β₂} {g₁ : R β₁ γ₁} {g₂ : R β₂ γ₂} {h₁ : R γ₁ d} {h₂ : R γ₂ d} :
      h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) ⟶ (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ :=
    applyAssocRL_right V ⊙ applyAssocRL_left V

  end HasComposition

  namespace HasMorphisms

    variable [h : HasMorphisms R]

    def leftCancelId  {a b : α} (f : R a b) {e : R b b} : e ≃ ident R b ⟶ e • f ≃ f :=
    HasFunOp.swapFun (comp_subst_left  V f) (h.leftId  f)
    def rightCancelId {a b : α} (f : R a b) {e : R a a} : e ≃ ident R a ⟶ f • e ≃ f :=
    HasFunOp.swapFun (comp_subst_right V f) (h.rightId f)

  end HasMorphisms

  open HasMorphisms

  namespace HasIsomorphisms

    variable [HasIsomorphisms R]

    def inv_congrArg {a b : α} {f₁ f₂ : R a b} : f₁ ≃ f₂ ⟶ f₁⁻¹ ≃ f₂⁻¹ :=
    HasInstanceEquivalences.funCongrArg V HasSymm.symm

    def inv_subst  {a b : α} {f₁ f₂ : R a b} {e : R b a} : f₁ ≃ f₂ ⟶ f₂⁻¹ ≃ e ⟶ f₁⁻¹ ≃ e :=
    HasTrans.trans    ⊙ inv_congrArg V
    def inv_subst' {a b : α} {f₁ f₂ : R a b} {e : R b a} : f₁ ≃ f₂ ⟶ e ≃ f₁⁻¹ ⟶ e ≃ f₂⁻¹ :=
    HasTrans.revTrans ⊙ inv_congrArg V

    def leftCancel'     {a b c : α} (f : R a b) (g : R b c) : (g⁻¹ • g) • f ≃ f := leftCancelId  V f (leftInv  g)
    def leftCancel      {a b c : α} (f : R a b) (g : R b c) : g⁻¹ • (g • f) ≃ f := applyAssocLR_left V (leftCancel'     V f g)
    def leftCancelInv'  {a b c : α} (f : R a b) (g : R c b) : (g • g⁻¹) • f ≃ f := leftCancelId  V f (rightInv g)
    def leftCancelInv   {a b c : α} (f : R a b) (g : R c b) : g • (g⁻¹ • f) ≃ f := applyAssocLR_left V (leftCancelInv'  V f g)
    def rightCancel'    {a b c : α} (f : R a b) (g : R c a) : f • (g • g⁻¹) ≃ f := rightCancelId V f (rightInv g)
    def rightCancel     {a b c : α} (f : R a b) (g : R c a) : (f • g) • g⁻¹ ≃ f := applyAssocRL_left V (rightCancel'    V f g)
    def rightCancelInv' {a b c : α} (f : R a b) (g : R a c) : f • (g⁻¹ • g) ≃ f := rightCancelId V f (leftInv  g)
    def rightCancelInv  {a b c : α} (f : R a b) (g : R a c) : (f • g⁻¹) • g ≃ f := applyAssocRL_left V (rightCancelInv' V f g)

    def leftMulInv  {a b c : α} (f₁ : R a b) (f₂ : R a c) (g : R b c) : g • f₁ ≃ f₂ ⟷{he.ArrowType} f₁ ≃ g⁻¹ • f₂ :=
    ⟨HasFunOp.swapFun (comp_subst_right' V g⁻¹) ((he.arrowSymm (R a b)).symm' (leftCancel V f₁ g)),
     HasFunOp.swapFun (comp_subst_right  V g)   (leftCancelInv V f₂ g)⟩
    def leftMulInv' {a b c : α} (f₁ : R a b) (f₂ : R a c) (g : R c b) : g⁻¹ • f₁ ≃ f₂ ⟷{he.ArrowType} f₁ ≃ g • f₂ :=
    ⟨HasFunOp.swapFun (comp_subst_right' V g)   ((he.arrowSymm (R a b)).symm' (leftCancelInv V f₁ g)),
     HasFunOp.swapFun (comp_subst_right  V g⁻¹) (leftCancel V f₂ g)⟩

    def leftMul {a b c : α} (f₁ f₂ : R a b) (g : R b c) : g • f₁ ≃ g • f₂ ⟷{he.ArrowType} f₁ ≃ f₂ :=
    ⟨((he.hasArrows (R a b)).isPreorder).revTrans'' (leftCancel V f₂ g) ⊙ (leftMulInv V f₁ (g • f₂) g).mp,
     comp_congrArg_right V⟩

    def rightMulInv  {a b c : α} (f₁ : R a c) (f₂ : R b c) (g : R b a) : f₁ • g ≃ f₂ ⟷{he.ArrowType} f₁ ≃ f₂ • g⁻¹ :=
    ⟨HasFunOp.swapFun (comp_subst_left' V g⁻¹) ((he.arrowSymm (R a c)).symm' (rightCancel V f₁ g)),
     HasFunOp.swapFun (comp_subst_left  V g)   (rightCancelInv V f₂ g)⟩
    def rightMulInv' {a b c : α} (f₁ : R a c) (f₂ : R b c) (g : R a b) : f₁ • g⁻¹ ≃ f₂ ⟷{he.ArrowType} f₁ ≃ f₂ • g :=
    ⟨HasFunOp.swapFun (comp_subst_left' V g)   ((he.arrowSymm (R a c)).symm' (rightCancelInv V f₁ g)),
     HasFunOp.swapFun (comp_subst_left  V g⁻¹) (rightCancel V f₂ g)⟩

    def rightMul {a b c : α} (f₁ f₂ : R a b) (g : R c a) : f₁ • g ≃ f₂ • g ⟷{he.ArrowType} f₁ ≃ f₂ :=
    ⟨((he.hasArrows (R a b)).isPreorder).revTrans'' (rightCancel V f₂ g) ⊙ (rightMulInv V f₁ (f₂ • g) g).mp,
     comp_congrArg_left V⟩

    def eqInvIffInvEq {a b : α} (f : R a b) (g : R b a) : f ≃ g⁻¹ ⟷{he.ArrowType} f⁻¹ ≃ g :=
    ⟨HasFunOp.swapFun (inv_subst  V) (invInv g),
     HasFunOp.swapFun (inv_subst' V) ((he.arrowSymm (R a b)).symm' (invInv f))⟩

    def eqIffEqInv {a b : α} (f₁ f₂ : R a b) : f₁⁻¹ ≃ f₂⁻¹ ⟷{he.ArrowType} f₁ ≃ f₂ :=
    ⟨((he.hasArrows (R a b)).isPreorder).revTrans'' (invInv f₂) ⊙ (eqInvIffInvEq V f₁ f₂⁻¹).mpr,
     inv_congrArg V⟩

    def leftRightMul {a b c d : α} (f₁ : R a b) (f₂ : R a c) (g₁ : R b d) (g₂ : R c d) :
      g₂⁻¹ • g₁ ≃ f₂ • f₁⁻¹ ⟷{he.ArrowType} g₁ • f₁ ≃ g₂ • f₂ :=
    ⟨(leftMulInv' V (g₁ • f₁) f₂ g₂).mp ⊙ applyAssocLR_left V ⊙ (rightMulInv V (g₂⁻¹ • g₁) f₂ f₁).mpr,
     (leftMulInv' V g₁ (f₂ • f₁⁻¹) g₂).mpr ⊙ applyAssocLR_right V ⊙ (rightMulInv V g₁ (g₂ • f₂) f₁).mp⟩

    def swapInv  {a b c d : α} (f₁ : R a b) (f₂ : R c d) (g₁ : R d b) (g₂ : R c a) :
      g₁⁻¹ • f₁ ≃ f₂ • g₂⁻¹ ⟶ f₁⁻¹ • g₁ ≃ g₂ • f₂⁻¹ :=
    (leftRightMul V f₂ g₂ g₁ f₁).mpr ⊙ HasSymm.symm ⊙ (leftRightMul V g₂ f₂ f₁ g₁).mp

    def swapInv' {a b c d : α} (f₁ : R a b) (f₂ : R c d) (g₁ : R d b) (g₂ : R c a) :
      f₂ • g₂⁻¹ ≃ g₁⁻¹ • f₁ ⟶ g₂ • f₂⁻¹ ≃ f₁⁻¹ • g₁ :=
    HasSymm.symm ⊙ swapInv V f₁ f₂ g₁ g₂ ⊙ HasSymm.symm

  end HasIsomorphisms

  open HasIsomorphisms

end Morphisms



section Functors

  variable {α : Sort u} {V : Sort v} [IsKind V] [HasInstanceArrows V]

  namespace idFun

    variable (R : GeneralizedRelation α V)

    instance isReflFunctor  [HasRefl  R] : IsReflFunctor  R R (HasFunOp.idFun' _) :=
    ⟨λ a           => HasRefl.refl (ident R a)⟩

    instance isSymmFunctor  [HasSymm  R] : IsSymmFunctor  R R (HasFunOp.idFun' _) :=
    ⟨λ {a b}   f   => HasRefl.refl f⁻¹⟩

    instance isTransFunctor [HasTrans R] : IsTransFunctor R R (HasFunOp.idFun' _) :=
    ⟨λ {a b c} f g => HasRefl.refl (g • f)⟩

    instance isPreorderFunctor    [IsPreorder    R] : IsPreorderFunctor    R R (HasFunOp.idFun' _) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] : IsEquivalenceFunctor R R (HasFunOp.idFun' _) := ⟨⟩

  end idFun

  -- TODO: constFun, appFun, ...?

  namespace compFun

    variable {R S T : GeneralizedRelation α V} (F : BaseFunctor R S) (G : BaseFunctor S T)

    instance isReflFunctor  [HasRefl  R] [HasRefl  S] [HasRefl  T] [hF : IsReflFunctor  R S F] [hG : IsReflFunctor  S T G] :
      IsReflFunctor  R T (G ⊙' F) :=
    ⟨λ a   => let e₁ : G (F (ident R a)) ⇝ G (ident S a) := HasInstanceArrows.arrCongrArg' V G (hF.respectsRefl a);
              let e₂ : G (ident S a) ⇝ ident T a         := hG.respectsRefl a;
              HasTrans.trans' e₁ e₂⟩

    instance isSymmFunctor  [HasSymm  R] [HasSymm  S] [HasSymm  T] [hF : IsSymmFunctor  R S F] [hG : IsSymmFunctor  S T G] :
      IsSymmFunctor  R T (G ⊙' F) :=
    ⟨λ f   => let e₁ : G (F f⁻¹) ⇝ G (F f)⁻¹   := HasInstanceArrows.arrCongrArg' V G (hF.respectsSymm f);
              let e₂ : G (F f)⁻¹ ⇝ (G (F f))⁻¹ := hG.respectsSymm (F f);
              HasTrans.trans' e₁ e₂⟩

    instance isTransFunctor [HasTrans R] [HasTrans S] [HasTrans T] [hF : IsTransFunctor R S F] [hG : IsTransFunctor S T G] :
      IsTransFunctor R T (G ⊙' F) :=
    ⟨λ f g => let e₁ : G (F (g • f)) ⇝ G (F g • F f)     := HasInstanceArrows.arrCongrArg' V G (hF.respectsTrans f g);
              let e₂ : G (F g • F f) ⇝ G (F g) • G (F f) := hG.respectsTrans (F f) (F g);
              HasTrans.trans' e₁ e₂⟩

    instance isPreorderFunctor    [IsPreorder    R] [IsPreorder    S] [IsPreorder    T] [IsPreorderFunctor    R S F] [IsPreorderFunctor    S T G] :
      IsPreorderFunctor    R T (G ⊙' F) := ⟨⟩
    instance isEquivalenceFunctor [IsEquivalence R] [IsEquivalence S] [IsEquivalence T] [IsEquivalenceFunctor R S F] [IsEquivalenceFunctor S T G] :
      IsEquivalenceFunctor R T (G ⊙' F) := ⟨⟩

  end compFun

end Functors



section NaturalTransformations

  variable {α : Sort u} {V : Sort v} [IsKind V] [HasInstanceEquivalences V]
           {β : Sort w} (R : GeneralizedRelation α V) (S : GeneralizedRelation β V)

  namespace IsNaturalTransformation

    def refl  [h : HasMorphisms    S] {mF       : α → β}
              (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) :
      IsNaturalTransformation R S F F (λ a => h.refl (mF a)) :=
    ⟨λ f => HasTrans.trans' (h.rightId (F f)) (HasSymm.symm' (h.leftId (F f)))⟩

    def symm  [h : HasIsomorphisms S] {mF mG    : α → β}
              (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) (G : ∀ {a b}, R a b ⟶' S (mG a) (mG b))
              (n : ∀ a, S (mF a) (mG a)) [hn : IsNaturalTransformation R S F G n] :
      IsNaturalTransformation R S G F (λ a => h.symm (n a)) :=
    ⟨λ {a b} f => HasSymm.symm' ((HasIsomorphisms.leftRightMul V (n a) (F f) (G f) (n b)).mpr (hn.nat f))⟩

    def trans [h : HasComposition  S] {mF mG mH : α → β}
              (F : ∀ {a b}, R a b ⟶' S (mF a) (mF b)) (G : ∀ {a b}, R a b ⟶' S (mG a) (mG b)) (H : ∀ {a b}, R a b ⟶' S (mH a) (mH b))
              (nFG : ∀ a, S (mF a) (mG a))                 (nGH : ∀ a, S (mG a) (mH a))
              [hnFG : IsNaturalTransformation R S F G nFG] [hnGH : IsNaturalTransformation R S G H nGH] :
      IsNaturalTransformation R S F H (λ a => h.trans (nFG a) (nGH a)) :=
    ⟨λ {a b} f => let e₁ := HasComposition.applyAssocLR_left V (HasComposition.comp_congrArg_left  V (f := nFG a) (hnGH.nat f));
                  let e₂ := HasComposition.applyAssocRL      V (HasComposition.comp_congrArg_right V (g := nGH b) (hnFG.nat f));
                  HasTrans.trans' e₁ e₂⟩

  end IsNaturalTransformation

end NaturalTransformations
