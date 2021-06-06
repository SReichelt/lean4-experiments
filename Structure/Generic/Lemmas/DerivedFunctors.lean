import Structure.Generic.Axioms.Universes
import Structure.Generic.Axioms.AbstractFunctors



set_option autoBoundImplicitLocal false
--set_option pp.universes true



namespace HasLinearFunOp

  variable {U : Universe} [HasInternalFunctors U] [h : HasLinearFunOp U]

  -- The "swap" functor swaps the arguments of a nested functor. Its plain version `swapFun` actually
  -- just fixes the second argument.

  def swapIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) : HasExternalFunctors.IsFun (λ a : α => F a b) :=
  h.compIsFun F (appFun' b γ)

  def swapFun' {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) : α ⟶' γ := BundledFunctor.mkFun (swapIsFun F b)
  def swapFun  {α β γ : U} (F : α ⟶  β ⟶ γ) (b : β) : α ⟶  γ := HasInternalFunctors.fromBundled (swapFun' (HasInternalFunctors.toBundled F) b)

  @[simp] theorem swapFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) (a : α) : (swapFun F b) a = F a b :=
  by apply HasInternalFunctors.fromBundled.eff

  theorem swapFunFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (b : β) :
    HasInternalFunctors.fromBundled (swapFun' F b) = HasInternalFunctors.fromBundled (HasInternalFunctors.toBundled (appFun b γ) ⊙' F) :=
  HasInternalFunctors.toFromBundled (appFun' b γ) ▸ rfl

  def swapFunIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) : HasExternalFunctors.IsFun (λ b : β => HasInternalFunctors.fromBundled (swapFun' F b)) :=
  funext (swapFunFun.def F) ▸ h.compIsFun (appFunFun' β γ) (compFunFun' F γ)

  def swapFunFun' {α β γ : U} (F : α ⟶' β ⟶ γ) : β ⟶' α ⟶ γ := BundledFunctor.mkFun (swapFunIsFun F)
  def swapFunFun  {α β γ : U} (F : α ⟶  β ⟶ γ) : β ⟶  α ⟶ γ := HasInternalFunctors.fromBundled (swapFunFun' (HasInternalFunctors.toBundled F))

  @[simp] theorem swapFunFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) : (swapFunFun F) b = swapFun F b :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem swapFunFun.effEff {α β γ : U} (F : α ⟶ β ⟶ γ) (b : β) (a : α) : ((swapFunFun F) b) a = F a b :=
  by simp

  theorem swapFunFunFun.def (α β γ : U) (F : α ⟶ β ⟶ γ) :
    HasInternalFunctors.mkFun (swapFunIsFun (HasInternalFunctors.toBundled F)) = HasInternalFunctors.fromBundled (HasInternalFunctors.toBundled (compFunFun F γ) ⊙' appFunFun' β γ) :=
  HasInternalFunctors.toFromBundled (compFunFun' (HasInternalFunctors.toBundled F) γ) ▸ elimRec

  def swapFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ F : α ⟶ β ⟶ γ => swapFunFun F) :=
  funext (swapFunFunFun.def α β γ) ▸ h.compIsFun (compFunFunFun' α (β ⟶ γ) γ) (compFunFun' (appFunFun' β γ) (α ⟶ γ))

  def swapFunFunFun' (α β γ : U) : (α ⟶ β ⟶ γ) ⟶' (β ⟶ α ⟶ γ) := BundledFunctor.mkFun (swapFunFunIsFun α β γ)
  def swapFunFunFun  (α β γ : U) : (α ⟶ β ⟶ γ) ⟶  (β ⟶ α ⟶ γ) := HasInternalFunctors.fromBundled (swapFunFunFun' α β γ)

  @[simp] theorem swapFunFunFun.eff (α β γ : U) (F : α ⟶ β ⟶ γ) : (swapFunFunFun α β γ) F = swapFunFun F :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem swapFunFunFun.effEff (α β γ : U) (F : α ⟶ β ⟶ γ) (b : β) : ((swapFunFunFun α β γ) F) b = swapFun F b :=
  by simp

  @[simp] theorem swapFunFunFun.effEffEff (α β γ : U) (F : α ⟶ β ⟶ γ) (b : β) (a : α) : (((swapFunFunFun α β γ) F) b) a = F a b :=
  by simp

  -- In particular, reverse composition is also functorial.

  def revCompFun {α β γ : U} (G : β ⟶  γ) (F : α ⟶  β) : α ⟶ γ := compFun F G
  infixr:90 " ⊙ "  => HasLinearFunOp.revCompFun

  @[simp] theorem revCompFun.eff {α β γ : U} (F : α ⟶ β) (G : β ⟶ γ) (a : α) : (G ⊙ F) a = G (F a) :=
  compFun.eff F G a

  theorem revCompFunFun.def (α : U) {β γ : U} (G : β ⟶' γ) (F : α ⟶ β) :
    HasInternalFunctors.fromBundled (G ⊙' HasInternalFunctors.toBundled F) = (compFunFun F γ) (HasInternalFunctors.fromBundled G) :=
  Eq.subst (motive := λ H => HasInternalFunctors.fromBundled (H ⊙' HasInternalFunctors.toBundled F) = (compFunFun F γ) (HasInternalFunctors.fromBundled G))
           (HasInternalFunctors.toFromBundled G)
           (Eq.symm (compFunFun.eff F γ (HasInternalFunctors.fromBundled G)))

  def revCompFunIsFun (α : U) {β γ : U} (G : β ⟶' γ) :
    HasExternalFunctors.IsFun (λ F : α ⟶ β => HasInternalFunctors.fromBundled (G ⊙' HasInternalFunctors.toBundled F)) :=
  funext (revCompFunFun.def α G) ▸ swapIsFun (compFunFunFun' α β γ) (HasInternalFunctors.fromBundled G)

  def revCompFunFun' (α : U) {β γ : U} (G : β ⟶' γ) : (α ⟶ β) ⟶' (α ⟶ γ) := BundledFunctor.mkFun (revCompFunIsFun α G)
  def revCompFunFun  (α : U) {β γ : U} (G : β ⟶  γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasInternalFunctors.fromBundled (revCompFunFun' α (HasInternalFunctors.toBundled G))

  @[simp] theorem revCompFunFun.eff (α : U) {β γ : U} (G : β ⟶ γ) (F : α ⟶ β) : (revCompFunFun α G) F = G ⊙ F :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem revCompFunFun.effEff (α : U) {β γ : U} (G : β ⟶ γ) (F : α ⟶ β) (a : α) : ((revCompFunFun α G) F) a = G (F a) :=
  by simp

  theorem revCompFunFunFun.def (α β γ : U) (G : β ⟶ γ) :
    HasInternalFunctors.mkFun (revCompFunIsFun α (HasInternalFunctors.toBundled G)) = HasInternalFunctors.fromBundled (swapFun' (compFunFunFun' α β γ) G) :=
  congrArg (λ H => HasInternalFunctors.fromBundled (swapFun' (compFunFunFun' α β γ) H)) (HasInternalFunctors.fromToBundled G) ▸ elimRec

  def revCompFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ G : β ⟶ γ => revCompFunFun α G) :=
  funext (revCompFunFunFun.def α β γ) ▸ swapFunIsFun (compFunFunFun' α β γ)

  def revCompFunFunFun' (α β γ : U) : (β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := BundledFunctor.mkFun (revCompFunFunIsFun α β γ)
  def revCompFunFunFun  (α β γ : U) : (β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.fromBundled (revCompFunFunFun' α β γ)

  @[simp] theorem revCompFunFunFun.eff (α β γ : U) (G : β ⟶ γ) : (revCompFunFunFun α β γ) G = revCompFunFun α G :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem revCompFunFunFun.effEff (α β γ : U) (G : β ⟶ γ) (F : α ⟶ β) : ((revCompFunFunFun α β γ) G) F = G ⊙ F :=
  by simp

  @[simp] theorem revCompFunFunFun.effEffEff (α β γ : U) (G : β ⟶ γ) (F : α ⟶ β) (a : α) : (((revCompFunFunFun α β γ) G) F) a = G (F a) :=
  by simp

  -- Composition of a function with two arguments.

  def compFun₂ {α β γ δ : U} (F : α ⟶ β ⟶ γ) (G : γ ⟶ δ) : α ⟶ β ⟶ δ := swapFunFun (revCompFunFun α G ⊙ swapFunFun F)

end HasLinearFunOp



namespace HasFullFunOp

  variable {U : Universe} [HasInternalFunctors U] [h : HasFullFunOp U]

  -- The S combinator (see https://en.wikipedia.org/wiki/SKI_combinator_calculus), which in our case says
  -- that if we can functorially construct a functor `H : β ⟶ γ` and an argument `b : β`, then the
  -- construction of `H b` is also functorial.

  theorem substFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) (a : α) :
    F a (G a) = HasInternalFunctors.fromBundled (HasLinearFunOp.swapFun' F (G a)) a :=
  Eq.symm (HasInternalFunctors.fromBundled.eff (HasLinearFunOp.swapFun' F (G a)) a)

  def substIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : HasExternalFunctors.IsFun (λ a : α => F a (G a)) :=
  funext (substFun.def F G) ▸ h.dupIsFun (HasLinearFunOp.swapFunFun' F ⊙' G)

  def substFun' {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶' β) : α ⟶' γ := BundledFunctor.mkFun (substIsFun F G)
  def substFun  {α β γ : U} (F : α ⟶  β ⟶ γ) (G : α ⟶  β) : α ⟶  γ := HasInternalFunctors.fromBundled (substFun' (HasInternalFunctors.toBundled F) (HasInternalFunctors.toBundled G))

  @[simp] theorem substFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) : (substFun F G) a = F a (G a) :=
  by apply HasInternalFunctors.fromBundled.eff

  theorem substFunFun.def {α β γ : U} (F : α ⟶' β ⟶ γ) (G : α ⟶ β) :
    HasInternalFunctors.mkFun (substIsFun F (HasInternalFunctors.toBundled G)) =
    HasInternalFunctors.fromBundled (HasNonLinearFunOp.dupFun' (HasInternalFunctors.toBundled (HasInternalFunctors.fromBundled (HasLinearFunOp.swapFunFun' F ⊙' HasInternalFunctors.toBundled G)))) :=
  HasInternalFunctors.toFromBundled _ ▸ elimRec

  def substFunIsFun {α β γ : U} (F : α ⟶' β ⟶ γ) :
    HasExternalFunctors.IsFun (λ G : α ⟶ β => HasInternalFunctors.fromBundled (substFun' F (HasInternalFunctors.toBundled G))) :=
  funext (substFunFun.def F) ▸ h.compIsFun (HasLinearFunOp.revCompFunFun' α (HasLinearFunOp.swapFunFun' F)) (HasNonLinearFunOp.dupFunFun' α γ)

  def substFunFun' {α β γ : U} (F : α ⟶' β ⟶ γ) : (α ⟶ β) ⟶' (α ⟶ γ) := BundledFunctor.mkFun (substFunIsFun F)
  def substFunFun  {α β γ : U} (F : α ⟶  β ⟶ γ) : (α ⟶ β) ⟶  (α ⟶ γ) := HasInternalFunctors.fromBundled (substFunFun' (HasInternalFunctors.toBundled F))

  @[simp] theorem substFunFun.eff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) : (substFunFun F) G = substFun F G :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem substFunFun.effEff {α β γ : U} (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) : ((substFunFun F) G) a = F a (G a) :=
  by simp

  theorem substFunFunFun.def (α β γ : U) (F : α ⟶ β ⟶ γ) :
    HasInternalFunctors.mkFun (substFunIsFun (HasInternalFunctors.toBundled F)) = HasInternalFunctors.fromBundled (HasNonLinearFunOp.dupFunFun' α γ ⊙' HasInternalFunctors.toBundled (HasLinearFunOp.revCompFunFun α (HasLinearFunOp.swapFunFun F))) :=
  HasInternalFunctors.toFromBundled _ ▸ HasInternalFunctors.toFromBundled _ ▸ elimRec

  def substFunFunIsFun (α β γ : U) : HasExternalFunctors.IsFun (λ F : α ⟶ β ⟶ γ => substFunFun F) :=
  funext (substFunFunFun.def α β γ) ▸ h.compIsFun (HasLinearFunOp.revCompFunFunFun' α β (α ⟶ γ) ⊙' HasLinearFunOp.swapFunFunFun' α β γ)
                                                  (HasLinearFunOp.revCompFunFun' (α ⟶ β) (HasNonLinearFunOp.dupFunFun' α γ))

  def substFunFunFun' (α β γ : U) : (α ⟶ β ⟶ γ) ⟶' (α ⟶ β) ⟶ (α ⟶ γ) := BundledFunctor.mkFun (substFunFunIsFun α β γ)
  def substFunFunFun  (α β γ : U) : (α ⟶ β ⟶ γ) ⟶  (α ⟶ β) ⟶ (α ⟶ γ) := HasInternalFunctors.fromBundled (substFunFunFun' α β γ)

  @[simp] theorem substFunFunFun.eff (α β γ : U) (F : α ⟶ β ⟶ γ) : (substFunFunFun α β γ) F = substFunFun F :=
  by apply HasInternalFunctors.fromBundled.eff

  @[simp] theorem substFunFunFun.effEff (α β γ : U) (F : α ⟶ β ⟶ γ) (G : α ⟶ β) : ((substFunFunFun α β γ) F) G = substFun F G :=
  by simp

  @[simp] theorem substFunFunFun.effEffEff (α β γ : U) (F : α ⟶ β ⟶ γ) (G : α ⟶ β) (a : α) : (((substFunFunFun α β γ) F) G) a = F a (G a) :=
  by simp

end HasFullFunOp



-- Using the functoriality axioms and the constructions above, we can algorithmically prove
-- functoriality of lambda terms. The algorithm to prove `HasExternalFunctors.IsFun (λ a : α => t)`
-- is as follows:
--
--  Case                           | Proof
-- --------------------------------+--------------------------------------------------------------
--  `t` does not contain `a`       | `constIsFun α t`
--  `t` is `a`                     | `idIsFun α`
--  `t` is `G b` with `G : β ⟶ γ`: |
--    `a` appears only in `b`      | Prove that `λ a => b` is functorial, yielding a functor
--                                 | `F : α ⟶ β`. Then the proof is `compIsFun F G`.
--      `b` is `a`                 | Optimization: `HasInternalFunctors.isFun G`
--    `a` appears only in `G`      | Prove that `λ a => G` is functorial, yielding a functor
--                                 | `F : α ⟶ β ⟶ γ`. Then the proof is `swapIsFun F b`.
--      `G` is `a`                 | Optimization: `appIsFun b γ`
--    `a` appears in both          | Prove that `λ a => G` is functorial, yielding a functor
--                                 | `F₁ : α ⟶ β ⟶ γ`. Prove that `λ a => b` is functorial,
--                                 | yielding a functor `F₂ : α ⟶ β`. Then the proof is
--                                 | `substIsFun F₁ F₂`.
--  `t` is `mkFun (λ b : β => c)`  | Prove that `λ a => c` is functorial when regarding `b` as
--                                 | a constant, yielding a functor `F : α ⟶ γ` for every `b`.
--                                 | Prove that  `λ b => F` is functorial, yielding a functor
--                                 | `G : β ⟶ α ⟶ γ`. Then the proof is `swapFunIsFun G`.
--
-- (This list does not contain all possible optimizations.)
