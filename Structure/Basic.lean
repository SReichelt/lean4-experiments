--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- This file contains a very abstract and general definition of `Structure`, which is actually a variant
-- of an ∞-groupoid.
--
-- See `Structure.lean` for an explanation of the use case.



-- TODO: Improve naming:
-- * Make variable names consistent:
--   * Be more consistent with `e` vs. `φ` etc.
--   * Rename `F`, `G` etc. in generalized functors to e.g. `f`, `g` (warning: clashes with equivalences `e`, `f`, ...).
-- * Use snake case for theorem names.



import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Notation



set_option autoBoundImplicitLocal false

-- TODO: Can we avoid this?
set_option maxHeartbeats 500000

universes u v w



-- We want to formalize a very general "structure with equivalences", so we start with a very basic
-- abstraction for something that looks like an equivalence relation except that the codomain is `Sort u`
-- instead of `Prop`. Therefore, `⟨Equiv.refl, Equiv.symm, Equiv.trans⟩`, where `Equiv` is the Lean 4
-- version of the `equiv` type in Lean 3 mathlib, is also an instance of this type.

class IsType (β : Sort v) where
(type (b : β) : Sort u)

instance (β : Sort v) [h : IsType β] : CoeSort β (Sort u) := ⟨h.type⟩
instance realType : IsType (Sort u) := ⟨id⟩

class IsEquivalence {α : Sort u} {β : Sort v} [IsType β] (R : α → α → β) where
(refl  (a     : α) : R a a)
(symm  {a b   : α} : R a b → R b a)
(trans {a b c : α} : R a b → R b c → R a c)

namespace IsEquivalence

-- Every equivalence relation can trivially be converted to an instance of `IsEquivalence`.
instance relEquiv {α : Sort u} {r : α → α → Prop} (e : Equivalence r) : IsEquivalence r :=
⟨e.refl, e.symm, e.trans⟩

-- So these are the instances that we obtain directly from Lean.
instance iffIsEquiv                                : IsEquivalence Iff     := relEquiv Iff.isEquivalence
instance eqIsEquiv     (α : Sort u)                : IsEquivalence (@Eq α) := relEquiv Eq.isEquivalence
instance setoidIsEquiv (α : Sort u) [s : Setoid α] : IsEquivalence s.r     := relEquiv s.iseqv

end IsEquivalence

open IsEquivalence



-- We also need to compare equivalences for equivalence, and there are essentially two options:
-- * The equivalences could be instances of the `Structure` type we are going to define. This would
--   turn that definition into a large mutually inductive type which Lean refuses to accept.
-- * Fortunately, for comparison of equivalences, a setoid is sufficient. Since it is a different setoid
--   for each pair of inputs, we work with a bundled version of `Setoid`.

structure BundledSetoid where
(α : Sort u)
[s : Setoid α]

instance bundledSetoidIsType : IsType BundledSetoid := ⟨BundledSetoid.α⟩
instance bundledSetoid (s : BundledSetoid) : Setoid (IsType.type s) := s.s

def eqSetoid (α : Sort u) : BundledSetoid :=
{ α := α,
  s := ⟨Eq, Eq.isEquivalence⟩ }

def GeneralizedRelation (α : Sort u) := α → α → BundledSetoid

def unfoldGeneralizedRelation {α : Sort u} (R : GeneralizedRelation α) : α → α → Sort v :=
λ a b => bundledSetoidIsType.type (R a b)

def genRel {α : Sort u} (r : α → α → Sort v) : GeneralizedRelation α := λ a b => eqSetoid (r a b)



-- Sometimes we need to map instances of a type before comparing them; this structure combines the
-- necessary data for doing so.

structure MappedRelation (ω : Sort w) where
{α : Sort u}
(R : GeneralizedRelation α)
(f : ω → α)

def mappedToGeneralizedRelation {ω : Sort w} (R : MappedRelation ω) : GeneralizedRelation ω :=
λ a b => R.R (R.f a) (R.f b)

instance (ω : Sort w) : CoeFun (MappedRelation ω) (λ _ => GeneralizedRelation ω) :=
-- Apparently we need to duplicate this here to make type class resolution work.
⟨λ R a b => R.R (R.f a) (R.f b)⟩

def toMappedRelation {α : Sort u} (R : GeneralizedRelation α) : MappedRelation α := ⟨R, id⟩

instance (α : Sort u) : Coe (GeneralizedRelation α) (MappedRelation α) := ⟨toMappedRelation⟩

def generalizeRelation {α : Sort u} {ω : Sort w} (f : ω → α) (R : GeneralizedRelation α) :
  GeneralizedRelation ω :=
mappedToGeneralizedRelation ⟨R, f⟩



-- We would also like to be able to manipulate such equivalences, and we need them to behave like
-- isomorphisms when doing so, with `refl` as the identity, `symm` as inverse, and `trans` as composition.
-- In other words, a structure with its equivalences is a category where every morphism has an inverse (as
-- guaranteed by `symm`), i.e. it is a groupoid.
--
-- Of course, the same type may also have a category structure with more morphisms, but since we are
-- defining a generalization of an equivalence relation, not a category, we wish to ignore such extra
-- structure at this point. Note that for actual equivalence relations, the axioms are trivially satisfied
-- in a proof-irrelevant system such as Lean.
--
-- We add three redundant axioms to avoid unnecessary computations. (Actually, this list of axioms was
-- originally inspired by the seven corresponding lemmas in `data.equiv.basic` of mathlib in Lean 3:
-- `symm_symm`, `trans_refl`, etc.)
-- With `a b c d : α`, and writing `a ≃ b` for `R a b`, we have:
--
-- ` refl     : a ≃ a                           ` | `id`
-- ` symm     : a ≃ b → b ≃ a                   ` | `⁻¹`
-- ` trans    : a ≃ b → b ≃ c → a ≃ c           ` | `∘` (in reverse order)
-- ` assoc    (f : a ≃ b) (g : b ≃ c) (h : c ≃ d) : h ∘ (g ∘ f) = (h ∘ g) ∘ f `
-- ` leftId   (f : a ≃ b)                         : id ∘ f    = f             `
-- ` rightId  (f : a ≃ b)                         : f ∘ id    = f             `
-- ` leftInv  (f : a ≃ b)                         : f⁻¹ ∘ f   = id            `
-- ` rightInv (f : a ≃ b)                         : f ∘ f⁻¹   = id            `
-- ` invInv   (f : a ≃ b)                         : (f⁻¹)⁻¹   = f             `
-- ` compInv  (f : a ≃ b) (g : b ≃ c)             : (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹     `
-- ` idInv                                        : id⁻¹      = id            `
--
-- In order to avoid the non-constructive operation of taking quotients when our equivalences have
-- nontrivial structure, we replace `=` in the axioms with the setoid equivalence `≈` we just introduced.
-- This means `Structure` is not strictly a groupoid, but we are instead working in some variant of higher
-- groupoid theory.
-- Using setoid equivalence instead of equality also requires the addition of two new axioms asserting
-- that composition and inverses are compatible with this equivalence.
--
-- Remark: Interestingly, all axioms can be regarded as simplification rules (with the simplification for
-- associativity being the omission of parentheses). With the addition of the three redundant axioms, they
-- enable equational reasoning by transforming all possible terms into a "flat" canonical form. Besides
-- making proofs trivial, this observation also suggests an alternative formalization of the axioms in
-- terms of a simplification function.

namespace Morphisms

variable {α : Sort u}

class HasComp {β : Sort v} [IsType β] (R : α → α → β) where
(comp {a b c : α} : R a b → R b c → R a c)

-- Note that we use a nonstandard order in `HasComp.comp` so that it directly matches
-- `IsEquivalence.trans`. When using `•` notation (which we use to avoid clashing with `∘`), we reverse
-- the order to conform to function/morphism/functor composition.
def comp {β : Sort v} [h : IsType β] {R : α → α → β} [h : HasComp R] {a b c : α} (f : R a b) (g : R b c) := h.comp f g
@[reducible] def revComp {β : Sort v} [h : IsType β] {R : α → α → β} [h : HasComp R] {a b c : α} (g : R b c) (f : R a b) := comp f g
infixr:90 " • " => revComp

class HasComposition (R : GeneralizedRelation α) extends HasComp R where
(congrArgComp {a b c   : α} {f₁ f₂ : R a b} {g₁ g₂ : R b c}     : f₁ ≈ f₂ → g₁ ≈ g₂ → g₁ • f₁ ≈ g₂ • f₂)
(assoc        {a b c d : α} (f : R a b) (g : R b c) (h : R c d) : h • (g • f) ≈ (h • g) • f)

class HasId (R : GeneralizedRelation α) extends HasComposition R where
(id (a : α) : R a a)

def id_ {R : GeneralizedRelation α} [h : HasId R] (a : α) := @HasId.id α R h a

class HasMorphisms (R : GeneralizedRelation α) extends HasId R where
(leftId  {a b : α} (f : R a b) : id b • f ≈ f)
(rightId {a b : α} (f : R a b) : f • id a ≈ f)

class HasInv (R : GeneralizedRelation α) extends HasMorphisms R where
(inv {a b : α} : R a b → R b a)

def inv {R : GeneralizedRelation α} [h : HasInv R] {a b : α} (f : R a b) := @HasInv.inv α R h a b f 
postfix:max "⁻¹" => inv

class HasIsomorphisms (R : GeneralizedRelation α) extends HasInv R where
(congrArgInv {a b   : α} {f₁ f₂ : R a b}         : f₁ ≈ f₂ → f₁⁻¹ ≈ f₂⁻¹)
(leftInv     {a b   : α} (f : R a b)             : f⁻¹ • f   ≈ id a)
(rightInv    {a b   : α} (f : R a b)             : f • f⁻¹   ≈ id b)
(invInv      {a b   : α} (f : R a b)             : (f⁻¹)⁻¹   ≈ f)
(compInv     {a b c : α} (f : R a b) (g : R b c) : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹)
(idInv       (a     : α)                         : (id a)⁻¹  ≈ id a)

instance isoEquiv (R : GeneralizedRelation α) [h : HasIsomorphisms R] : IsEquivalence R :=
⟨h.id, h.inv, h.comp⟩

end Morphisms

open Morphisms



-- In Lean, we can use proof irrelevance to define one instance that works for all ordinary equivalence
-- relations.
--
-- TODO: Should we avoid proof irrelevance in order to obtain better computational properties?
-- Is that even a meaningful question in Lean?
-- In a proof-relevant system, would we need a different definition for `genRel`?

namespace PropEquiv

variable {α : Sort u} (r : α → α → Prop) [h : IsEquivalence r]

instance propEquivHasIso : HasIsomorphisms (genRel r) :=
{ comp         := h.trans,
  congrArgComp := λ _ _   => proofIrrel _ _,
  assoc        := λ _ _ _ => proofIrrel _ _,
  id           := h.refl,
  leftId       := λ _     => proofIrrel _ _,
  rightId      := λ _     => proofIrrel _ _,
  inv          := h.symm,
  congrArgInv  := λ _     => proofIrrel _ _,
  leftInv      := λ _     => proofIrrel _ _,
  rightInv     := λ _     => proofIrrel _ _,
  invInv       := λ _     => proofIrrel _ _,
  compInv      := λ _ _   => proofIrrel _ _,
  idInv        := λ _     => proofIrrel _ _ }

end PropEquiv



-- Bundle the generalized equivalence relation and its axioms into a single type class.

class HasStructure (α : Sort u) where
(M       : GeneralizedRelation α)
[hasIsos : HasIsomorphisms M]

namespace HasStructure

variable {α : Sort u} [h : HasStructure α]

instance hasComp : HasComp         h.M := h.hasIsos.toHasComp
instance hasCmp  : HasComposition  h.M := h.hasIsos.toHasComposition
instance hasId   : HasId           h.M := h.hasIsos.toHasId
instance hasMor  : HasMorphisms    h.M := h.hasIsos.toHasMorphisms
instance hasInv  : HasInv          h.M := h.hasIsos.toHasInv
instance hasIso  : HasIsomorphisms h.M := h.hasIsos
instance isEquiv : IsEquivalence   h.M := isoEquiv h.M

instance hasEquivalence : HasEquivalence α α := ⟨h.M⟩

instance equivalenceIsType : IsType (HasEquivalence.γ α α) := bundledSetoidIsType
instance (a b : α) : Setoid (IsType.type (a ≃ b)) := (h.M a b).s

instance hasComp' : HasComp         (@HasEquivalence.Equiv α α hasEquivalence) := hasComp
instance hasCmp'  : HasComposition  (@HasEquivalence.Equiv α α hasEquivalence) := hasCmp
instance hasId'   : HasId           (@HasEquivalence.Equiv α α hasEquivalence) := hasId
instance hasMor'  : HasMorphisms    (@HasEquivalence.Equiv α α hasEquivalence) := hasMor
instance hasInv'  : HasInv          (@HasEquivalence.Equiv α α hasEquivalence) := hasInv
instance hasIso'  : HasIsomorphisms (@HasEquivalence.Equiv α α hasEquivalence) := hasIso
instance isEquiv' : IsEquivalence   (@HasEquivalence.Equiv α α hasEquivalence) := isEquiv

def id' {a : α} := @id_ α h.M hasId a

        theorem congrArgComp {a b c   : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c}     : f₁ ≈ f₂ → g₁ ≈ g₂ → g₁ • f₁ ≈ g₂ • f₂ := hasIso.congrArgComp
        theorem assoc        {a b c d : α} (f : a ≃ b) (g : b ≃ c) (h : c ≃ d) : h • (g • f) ≈ (h • g) • f             := hasIso.assoc    f g h
        theorem assoc'       {a b c d : α} (f : a ≃ b) (g : b ≃ c) (h : c ≃ d) : (h • g) • f ≈ h • (g • f)             := Setoid.symm (assoc f g h)
@[simp] theorem leftId       {a b     : α} (f : a ≃ b)                         : id' • f   ≈ f                         := hasIso.leftId   f
@[simp] theorem rightId      {a b     : α} (f : a ≃ b)                         : f • id'   ≈ f                         := hasIso.rightId  f
        theorem congrArgInv  {a b     : α} {f₁ f₂ : a ≃ b}                     : f₁ ≈ f₂ → f₁⁻¹ ≈ f₂⁻¹                 := hasIso.congrArgInv
@[simp] theorem leftInv      {a b     : α} (f : a ≃ b)                         : f⁻¹ • f   ≈ id'                       := hasIso.leftInv  f
@[simp] theorem rightInv     {a b     : α} (f : a ≃ b)                         : f • f⁻¹   ≈ id'                       := hasIso.rightInv f
@[simp] theorem invInv       {a b     : α} (f : a ≃ b)                         : (f⁻¹)⁻¹   ≈ f                         := hasIso.invInv   f
@[simp] theorem compInv      {a b c   : α} (f : a ≃ b) (g : b ≃ c)             : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹                 := hasIso.compInv  f g
@[simp] theorem idInv        (a       : α)                                     : (id_ a)⁻¹ ≈ id'                       := hasIso.idInv    a

theorem congrArgCompLeft  {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} : g₁ ≈ g₂ → g₁ • f ≈ g₂ • f :=
λ h => congrArgComp (Setoid.refl f) h
theorem congrArgCompRight {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} : f₁ ≈ f₂ → g • f₁ ≈ g • f₂ :=
λ h => congrArgComp h (Setoid.refl g)

theorem substComp  {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → g₁ ≈ g₂ → g₂ • f₂ ≈ e → g₁ • f₁ ≈ e :=
λ h₁ h₂ h₃ => Setoid.trans (congrArgComp h₁ h₂) h₃
theorem substComp' {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → g₁ ≈ g₂ → e ≈ g₁ • f₁ → e ≈ g₂ • f₂ :=
λ h₁ h₂ h₃ => Setoid.trans h₃ (congrArgComp h₁ h₂)

theorem substCompLeft   {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : g₁ ≈ g₂ → g₂ • f ≈ e → g₁ • f ≈ e :=
λ h₁ h₂ => Setoid.trans (congrArgCompLeft h₁) h₂
theorem substCompLeft'  {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : g₁ ≈ g₂ → e ≈ g₁ • f → e ≈ g₂ • f :=
λ h₁ h₂ => Setoid.trans h₂ (congrArgCompLeft h₁)

theorem substCompRight  {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → g • f₂ ≈ e → g • f₁ ≈ e :=
λ h₁ h₂ => Setoid.trans (congrArgCompRight h₁) h₂
theorem substCompRight' {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → e ≈ g • f₁ → e ≈ g • f₂ :=
λ h₁ h₂ => Setoid.trans h₂ (congrArgCompRight h₁)

theorem substInv  {a b : α} {f₁ f₂ : a ≃ b} {e : b ≃ a} : f₁ ≈ f₂ → f₂⁻¹ ≈ e → f₁⁻¹ ≈ e :=
λ h₁ h₂ => Setoid.trans (congrArgInv h₁) h₂
theorem substInv' {a b : α} {f₁ f₂ : a ≃ b} {e : b ≃ a} : f₁ ≈ f₂ → e ≈ f₁⁻¹ → e ≈ f₂⁻¹ :=
λ h₁ h₂ => Setoid.symm (substInv (Setoid.symm h₁) (Setoid.symm h₂))

theorem leftCancelId  {a b : α} {f : a ≃ b} {e : b ≃ b} : e ≈ id' → e • f ≈ f :=
λ h => substCompLeft  h (leftId  f)
theorem rightCancelId {a b : α} {f : a ≃ b} {e : a ≃ a} : e ≈ id' → f • e ≈ f :=
λ h => substCompRight h (rightId f)

theorem applyAssocLeft   {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  h • (g • f) ≈ e → (h • g) • f ≈ e :=
λ h₁ => Setoid.trans (assoc' f g h) h₁
theorem applyAssocLeft'  {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  (h • g) • f ≈ e → h • (g • f) ≈ e :=
λ h₁ => Setoid.trans (assoc f g h) h₁
theorem applyAssocRight  {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  e ≈ h • (g • f) → e ≈ (h • g) • f :=
λ h₁ => Setoid.trans h₁ (assoc f g h)
theorem applyAssocRight' {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  e ≈ (h • g) • f → e ≈ h • (g • f) :=
λ h₁ => Setoid.trans h₁ (assoc' f g h)

theorem applyAssoc  {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : a ≃ β₁} {f₂ : a ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ d} {h₂ : γ₂ ≃ d} :
  h₁ • (g₁ • f₁) ≈ h₂ • (g₂ • f₂) → (h₁ • g₁) • f₁ ≈ (h₂ • g₂) • f₂ :=
λ h => applyAssocRight  (applyAssocLeft  h)
theorem applyAssoc' {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : a ≃ β₁} {f₂ : a ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ d} {h₂ : γ₂ ≃ d} :
  (h₁ • g₁) • f₁ ≈ (h₂ • g₂) • f₂ → h₁ • (g₁ • f₁) ≈ h₂ • (g₂ • f₂) :=
λ h => applyAssocRight' (applyAssocLeft' h)

@[simp] theorem leftCancel'     {a b c : α} (f : a ≃ b) (g : b ≃ c) : (g⁻¹ • g) • f ≈ f := leftCancelId  (leftInv  g)
@[simp] theorem leftCancel      {a b c : α} (f : a ≃ b) (g : b ≃ c) : g⁻¹ • (g • f) ≈ f := applyAssocLeft' (leftCancel'     f g)
@[simp] theorem leftCancelInv'  {a b c : α} (f : a ≃ b) (g : c ≃ b) : (g • g⁻¹) • f ≈ f := leftCancelId  (rightInv g)
@[simp] theorem leftCancelInv   {a b c : α} (f : a ≃ b) (g : c ≃ b) : g • (g⁻¹ • f) ≈ f := applyAssocLeft' (leftCancelInv'  f g)
@[simp] theorem rightCancel'    {a b c : α} (f : a ≃ b) (g : c ≃ a) : f • (g • g⁻¹) ≈ f := rightCancelId (rightInv g)
@[simp] theorem rightCancel     {a b c : α} (f : a ≃ b) (g : c ≃ a) : (f • g) • g⁻¹ ≈ f := applyAssocLeft  (rightCancel'    f g)
@[simp] theorem rightCancelInv' {a b c : α} (f : a ≃ b) (g : a ≃ c) : f • (g⁻¹ • g) ≈ f := rightCancelId (leftInv  g)
@[simp] theorem rightCancelInv  {a b c : α} (f : a ≃ b) (g : a ≃ c) : (f • g⁻¹) • g ≈ f := applyAssocLeft  (rightCancelInv' f g)

theorem leftMulInv  {a b c : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g : b ≃ c) : g • f₁ ≈ f₂ ↔ f₁ ≈ g⁻¹ • f₂ :=
⟨λ h => substCompRight' h (Setoid.symm (leftCancel f₁ g)), λ h => substCompRight h (leftCancelInv f₂ g)⟩
theorem leftMulInv' {a b c : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g : c ≃ b) : g⁻¹ • f₁ ≈ f₂ ↔ f₁ ≈ g • f₂ :=
⟨λ h => substCompRight' h (Setoid.symm (leftCancelInv f₁ g)), λ h => substCompRight h (leftCancel f₂ g)⟩

@[simp] theorem leftMul {a b c : α} (f₁ f₂ : a ≃ b) (g : b ≃ c) : g • f₁ ≈ g • f₂ ↔ f₁ ≈ f₂ :=
⟨λ h => Setoid.trans ((leftMulInv f₁ (g • f₂) g).mp h) (leftCancel f₂ g), congrArgCompRight⟩

theorem rightMulInv  {a b c : α} (f₁ : a ≃ c) (f₂ : b ≃ c) (g : b ≃ a) : f₁ • g ≈ f₂ ↔ f₁ ≈ f₂ • g⁻¹ :=
⟨λ h => substCompLeft' h (Setoid.symm (rightCancel f₁ g)), λ h => substCompLeft h (rightCancelInv f₂ g)⟩
theorem rightMulInv' {a b c : α} (f₁ : a ≃ c) (f₂ : b ≃ c) (g : a ≃ b) : f₁ • g⁻¹ ≈ f₂ ↔ f₁ ≈ f₂ • g :=
⟨λ h => substCompLeft' h (Setoid.symm (rightCancelInv f₁ g)), λ h => substCompLeft h (rightCancel f₂ g)⟩

@[simp] theorem rightMul {a b c : α} (f₁ f₂ : a ≃ b) (g : c ≃ a) : f₁ • g ≈ f₂ • g ↔ f₁ ≈ f₂ :=
⟨λ h => Setoid.trans ((rightMulInv f₁ (f₂ • g) g).mp h) (rightCancel f₂ g), congrArgCompLeft⟩

theorem eqInvIffInvEq {a b : α} (f : a ≃ b) (g : b ≃ a) : f ≈ g⁻¹ ↔ f⁻¹ ≈ g :=
⟨λ h => substInv h (invInv g), λ h => substInv' h (Setoid.symm (invInv f))⟩

@[simp] theorem eqIffEqInv {a b : α} (f₁ f₂ : a ≃ b) : f₁⁻¹ ≈ f₂⁻¹ ↔ f₁ ≈ f₂ :=
⟨λ h => Setoid.trans ((eqInvIffInvEq f₁ f₂⁻¹).mpr h) (invInv f₂), congrArgInv⟩

@[simp] theorem leftRightMul {a b c d : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g₁ : b ≃ d) (g₂ : c ≃ d) :
  g₂⁻¹ • g₁ ≈ f₂ • f₁⁻¹ ↔ g₁ • f₁ ≈ g₂ • f₂ :=
⟨λ h => let h₁ := (rightMulInv (g₂⁻¹ • g₁) f₂ f₁).mpr h;
        let h₂ := applyAssocLeft' h₁;
        (leftMulInv' (g₁ • f₁) f₂ g₂).mp h₂,
 λ h => let h₁ := (rightMulInv g₁ (g₂ • f₂) f₁).mp h;
        let h₂ := applyAssocRight' h₁;
        (leftMulInv' g₁ (f₂ • f₁⁻¹) g₂).mpr h₂⟩

theorem swapInv  {a b c d : α} (f₁ : a ≃ b) (f₂ : c ≃ d) (g₁ : d ≃ b) (g₂ : c ≃ a) :
  g₁⁻¹ • f₁ ≈ f₂ • g₂⁻¹ → f₁⁻¹ • g₁ ≈ g₂ • f₂⁻¹ :=
λ h => (leftRightMul f₂ g₂ g₁ f₁).mpr (Setoid.symm ((leftRightMul g₂ f₂ f₁ g₁).mp h))

theorem swapInv' {a b c d : α} (f₁ : a ≃ b) (f₂ : c ≃ d) (g₁ : d ≃ b) (g₂ : c ≃ a) :
  f₂ • g₂⁻¹ ≈ g₁⁻¹ • f₁ → g₂ • f₂⁻¹ ≈ f₁⁻¹ • g₁ :=
λ h => Setoid.symm (swapInv f₁ f₂ g₁ g₂ (Setoid.symm h))

end HasStructure

open HasStructure

instance propHasStructure                               : HasStructure Prop := ⟨genRel Iff⟩
def      typeHasStructure   (α : Sort u)                : HasStructure α    := ⟨genRel Eq⟩
def      setoidHasStructure (α : Sort u) [s : Setoid α] : HasStructure α    := ⟨genRel s.r⟩



-- Now we put everything together to define our general "structure with equivalence". Concrete instances are
-- any `Sort u` with `Equiv` as equivalence, any `α : Sort u` with `Eq` as equivalence, and so on, but also
-- some new structures we are going to define below.
--
-- As mentioned before, this type is also
-- * an ∞-groupoid where higher-level equivalences have been truncated to equivalence relations, and
-- * a model of a "set" in the HLM logic of the Slate theorem prover, with equality modeled by the notion of
--   equivalence we have just defined. This is significant because it inspires treating equivalence like an
--   abstract notion of equality throughout the rest of this file.

structure Structure where
(α         : Sort u)
[hasStruct : HasStructure α]

namespace Structure

instance structureIsType : IsType Structure := ⟨Structure.α⟩

def iso (S : Structure) : GeneralizedRelation (IsType.type S) := S.hasStruct.M

variable {S : Structure}

instance hasStructure : HasStructure (IsType.type S) := S.hasStruct

instance hasComp : HasComp         (iso S) := hasStructure.hasComp
instance hasCmp  : HasComposition  (iso S) := hasStructure.hasCmp
instance hasId   : HasId           (iso S) := hasStructure.hasId
instance hasMor  : HasMorphisms    (iso S) := hasStructure.hasMor
instance hasInv  : HasInv          (iso S) := hasStructure.hasInv
instance hasIso  : HasIsomorphisms (iso S) := hasStructure.hasIso
instance isEquiv : IsEquivalence   (iso S) := hasStructure.isEquiv

def id__ (a : S) : a ≃ a := id_ a
def id'' {a : S} := id__ a

end Structure

open Structure

def defaultStructure (α : Sort u) [h : HasStructure α] : Structure := ⟨α⟩
def instanceStructure (α : Sort u) := @defaultStructure α (typeHasStructure α)
def setoidInstanceStructure (α : Sort u) [s : Setoid α] := @defaultStructure α (setoidHasStructure α)
def bundledSetoidStructure (S : BundledSetoid) := setoidInstanceStructure (IsType.type S)



-- Since each equivalence/isomorphism of a structure is a bundled setoid, we can treat it as a
-- structure as well. This partially recovers the inductive definition of a structure as an ∞-groupoid.

def isoStructure {S : Structure} (a b : S) := bundledSetoidStructure (iso S a b)



-- We can "forget" the data held inside a `Structure` on two levels, obtaining modified instances of
-- `Structure`:
--
-- 1. We can truncate the equivalence to an equivalence _relation_, obtaining a "setoid structure."
--
-- 2. In Lean, where quotients are available, we can additionally take the quotient with respect to
--    equivalence, obtaining a "skeleton structure" where equivalence is equality.
--
-- In `Forgetfulness.lean`, we prove some properties of these operations.
--
-- Within this file, we truncate structures to setoids whenever we want to use structures as isomorphisms,
-- but we never use quotients. With an inductive version of `Structure` (i.e. an actual ∞-groupoid), we
-- could keep all data instead.

namespace Forgetfulness

variable (S : Structure)

def SetoidEquiv (a b : S) := Nonempty (IsType.type (a ≃ b))
def toSetoidEquiv {a b : S} (e : a ≃ b) : SetoidEquiv S a b := ⟨e⟩
def setoidEquiv : Equivalence (SetoidEquiv S) :=
⟨λ a => ⟨refl a⟩, λ ⟨e⟩ => ⟨symm e⟩, λ ⟨e⟩ ⟨f⟩ => ⟨trans e f⟩⟩

instance structureToSetoid : Setoid (IsType.type S) := ⟨SetoidEquiv S, setoidEquiv S⟩
def setoidStructure : Structure := setoidInstanceStructure (IsType.type S)

-- Make type class resolution happy.
instance : IsEquivalence (λ a b : IsType.type (setoidStructure S) => (structureToSetoid S).r a b) :=
setoidIsEquiv (IsType.type S)

theorem equivInSetoidStructure (a b : setoidStructure S) : a ≃ b ↔ a ≈ b := ⟨λ e => ⟨e⟩, λ ⟨e⟩ => e⟩

def StructureQuotient := Quotient (structureToSetoid S)
def skeletonStructure : Structure := instanceStructure (StructureQuotient S)

theorem equivInSkeletonStructure (a b : skeletonStructure S) : a ≃ b ↔ a = b := ⟨id, id⟩

end Forgetfulness

open Forgetfulness



-- As a simple example of a custom structure, we define a structure for the Cartesian product of two
-- structures.

def StructureProduct (S T : Structure) := PProd (IsType.type S) (IsType.type T)

namespace StructureProduct

variable {S T : Structure}

def ProductEquiv (P Q : StructureProduct S T) := PProd (IsType.type (P.fst ≃ Q.fst)) (IsType.type (P.snd ≃ Q.snd))

namespace ProductEquiv

def refl  (P     : StructureProduct S T)                                               : ProductEquiv P P :=
⟨IsEquivalence.refl  P.fst,       IsEquivalence.refl  P.snd⟩
def symm  {P Q   : StructureProduct S T} (e : ProductEquiv P Q)                        : ProductEquiv Q P :=
⟨IsEquivalence.symm  e.fst,       IsEquivalence.symm  e.snd⟩
def trans {P Q R : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) : ProductEquiv P R :=
⟨IsEquivalence.trans e.fst f.fst, IsEquivalence.trans e.snd f.snd⟩

def EquivEquiv {P Q : StructureProduct S T} (e f : ProductEquiv P Q) :=
e.fst ≈ f.fst ∧ e.snd ≈ f.snd

namespace EquivEquiv

variable {P Q : StructureProduct S T}

theorem refl  (e     : ProductEquiv P Q)                                           : EquivEquiv e e :=
⟨Setoid.refl  e.fst,         Setoid.refl  e.snd⟩
theorem symm  {e f   : ProductEquiv P Q} (φ : EquivEquiv e f)                      : EquivEquiv f e :=
⟨Setoid.symm  φ.left,        Setoid.symm  φ.right⟩
theorem trans {e f g : ProductEquiv P Q} (φ : EquivEquiv e f) (ψ : EquivEquiv f g) : EquivEquiv e g :=
⟨Setoid.trans φ.left ψ.left, Setoid.trans φ.right ψ.right⟩

instance productEquivSetoid : Setoid (ProductEquiv P Q) := ⟨EquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquiv

def productEquiv : GeneralizedRelation (StructureProduct S T) := λ P Q => ⟨ProductEquiv P Q⟩

theorem congrArgComp {P Q R : StructureProduct S T} {e₁ e₂ : ProductEquiv P Q} {f₁ f₂ : ProductEquiv Q R} (he : e₁ ≈ e₂) (hf : f₁ ≈ f₂) :
  trans e₁ f₁ ≈ trans e₂ f₂ :=
⟨HasStructure.congrArgComp he.left hf.left,   HasStructure.congrArgComp he.right hf.right⟩

theorem assoc {P Q R Z : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) (g : ProductEquiv R Z) :
  trans (trans e f) g ≈ trans e (trans f g) :=
⟨HasStructure.assoc        e.fst f.fst g.fst, HasStructure.assoc        e.snd f.snd g.snd⟩

theorem leftId  {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans e (refl Q) ≈ e :=
⟨HasStructure.leftId       e.fst,             HasStructure.leftId       e.snd⟩
theorem rightId {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans (refl P) e ≈ e :=
⟨HasStructure.rightId      e.fst,             HasStructure.rightId      e.snd⟩

theorem congrArgInv {P Q : StructureProduct S T} {e₁ e₂ : ProductEquiv P Q} (he : e₁ ≈ e₂) :
  symm e₁ ≈ symm e₂ :=
⟨HasStructure.congrArgInv  he.left,           HasStructure.congrArgInv  he.right⟩

theorem leftInv  {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans e (symm e) ≈ refl P :=
⟨HasStructure.leftInv      e.fst,             HasStructure.leftInv      e.snd⟩
theorem rightInv {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans (symm e) e ≈ refl Q :=
⟨HasStructure.rightInv     e.fst,             HasStructure.rightInv     e.snd⟩

theorem invInv {P Q : StructureProduct S T} (e : ProductEquiv P Q) : symm (symm e) ≈ e :=
⟨HasStructure.invInv       e.fst,             HasStructure.invInv       e.snd⟩

theorem compInv {P Q R : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) :
  symm (trans e f) ≈ trans (symm f) (symm e) :=
⟨HasStructure.compInv      e.fst f.fst,       HasStructure.compInv      e.snd f.snd⟩

theorem idInv (P : StructureProduct S T) : symm (refl P) ≈ refl P :=
⟨HasStructure.idInv        P.fst,             HasStructure.idInv        P.snd⟩

instance productEquivHasIso : HasIsomorphisms (@productEquiv S T) :=
{ comp         := trans,
  congrArgComp := congrArgComp,
  assoc        := assoc,
  id           := refl,
  leftId       := leftId,
  rightId      := rightId,
  inv          := symm,
  congrArgInv  := congrArgInv,
  leftInv      := leftInv,
  rightInv     := rightInv,
  invInv       := invInv,
  compInv      := compInv,
  idInv        := idInv }

end ProductEquiv

instance productHasStructure (S T : Structure) : HasStructure (StructureProduct S T) := ⟨ProductEquiv.productEquiv⟩
def productStructure (S T : Structure) : Structure := ⟨StructureProduct S T⟩

end StructureProduct



-- We will be dealing with many different operations that respect composition, identity, and inverses,
-- or equivalently reflexivity, symmetry, and transitivity. We formalize all such operations using a
-- generalized definition of a functor. An actual functor between two structures is a special case of
-- this generalized version.
--
-- For convenience and also to avoid unnecessary computation, we add the redundant requirement that a
-- functor must preserve inverses, as those are an integral part of our axiomatized structure.
--
-- We split the type classes into the three pieces of structure that we are dealing with, so we can
-- potentially reuse it in other contexts later.

namespace Functors

variable {ω : Sort w} (R S : MappedRelation ω) (m : ∀ {a b : ω}, R a b → S a b)

-- This corresponds to `m` also being a functor. With an inductive definition of `Structure`, the
-- definition of `StructureFunctor` would need to be recursive.
class IsSetoidFunctor where
(respectsSetoid {a b   : ω} {f₁ f₂ : R a b}         : f₁ ≈ f₂ → m f₁ ≈ m f₂)

class IsCompositionFunctor [HasComposition  R.R] [HasComposition  S.R]
  extends IsSetoidFunctor      R S m where
(respectsComp   {a b c : ω} (f : R a b) (g : R b c) : m (g • f)       ≈ m g • m f)

class IsMorphismFunctor    [HasMorphisms    R.R] [HasMorphisms    S.R]
  extends IsCompositionFunctor R S m where
(respectsId     (a     : ω)                         : m (id_ (R.f a)) ≈ id_ (S.f a))

class IsIsomorphismFunctor [HasIsomorphisms R.R] [HasIsomorphisms S.R]
  extends IsMorphismFunctor    R S m where
(respectsInv    {a b   : ω} (f : R a b)             : m f⁻¹           ≈ (m f)⁻¹)

end Functors

open Functors

-- If the target has equivalences in `Prop`, the functor axioms are satisfied trivially.

instance propFunctor {ω : Sort w} {R : MappedRelation ω} [HasIsomorphisms R.R]
  {α : Sort u} {S : α → α → Prop} [e : IsEquivalence S] {f : ω → α}
  {m : ∀ {a b : ω}, R a b → S (f a) (f b)} :
  IsIsomorphismFunctor R ⟨genRel S, f⟩ m :=
{ respectsSetoid := λ _   => proofIrrel _ _,
  respectsComp   := λ _ _ => proofIrrel _ _,
  respectsId     := λ _   => proofIrrel _ _,
  respectsInv    := λ _   => proofIrrel _ _ }



-- A bundled version of `IsIsomorphismFunctor` where the codomains are structures.

structure GeneralizedFunctor {ω : Sort w} {S T : Structure} (F : ω → S) (G : ω → T) where
(mapEquiv {a b : ω} : F a ≃ F b → G a ≃ G b)
[isFunctor          : IsIsomorphismFunctor ⟨iso S, F⟩ ⟨iso T, G⟩ mapEquiv]

namespace GeneralizedFunctor

@[reducible] def Functor {S T : Structure} (F : S → T) := GeneralizedFunctor id F

variable {ω : Sort w} {S T U : Structure}

instance (F : ω → S) (G : ω → T) :
  CoeFun (GeneralizedFunctor F G) (λ _ => ∀ {a b : ω}, F a ≃ F b → G a ≃ G b) :=
⟨GeneralizedFunctor.mapEquiv⟩

def generalizeFunctor {β : Sort v} {F : ω → S} {G : ω → T} (H : β → ω) (φ : GeneralizedFunctor F G) :
  GeneralizedFunctor (F ∘ H) (G ∘ H) :=
{ mapEquiv  := φ.mapEquiv,
  isFunctor := { respectsSetoid := φ.isFunctor.respectsSetoid,
                 respectsComp   := φ.isFunctor.respectsComp,
                 respectsId     := λ b => φ.isFunctor.respectsId (H b),
                 respectsInv    := φ.isFunctor.respectsInv } }

instance {β : Sort v} (F : ω → S) (G : ω → T) (H : β → ω) :
  Coe (GeneralizedFunctor F G) (GeneralizedFunctor (F ∘ H) (G ∘ H)) :=
⟨generalizeFunctor H⟩

namespace id

variable {F : ω → S}

instance isFunctor : IsIsomorphismFunctor ⟨iso S, F⟩ ⟨iso S, F⟩ id :=
{ respectsSetoid := id,
  respectsComp   := λ f g => Setoid.refl (g • f),
  respectsId     := λ a   => Setoid.refl (id_ (F a)),
  respectsInv    := λ f   => Setoid.refl f⁻¹ }

def genFun : GeneralizedFunctor F F := ⟨id⟩

end id

namespace comp

variable {F : ω → S} {G : ω → T} {H : ω → U} (φ : GeneralizedFunctor F G) (ψ : GeneralizedFunctor G H)

def compFF {a b : ω} (e : F a ≃ F b) := ψ (φ e)

namespace compFF

theorem respectsSetoid {a b :   ω} {e f : F a ≃ F b} (h : e ≈ f) :
  compFF φ ψ e ≈ compFF φ ψ f :=
ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsSetoid h)

theorem respectsComp   {a b c : ω} (e : F a ≃ F b) (f : F b ≃ F c) :
  compFF φ ψ (f • e) ≈ compFF φ ψ f • compFF φ ψ e :=
let h₁ : ψ (φ (f • e)) ≈ ψ (φ f • φ e)     := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsComp e f);
let h₂ : ψ (φ f • φ e) ≈ ψ (φ f) • ψ (φ e) := ψ.isFunctor.respectsComp (φ e) (φ f);
Setoid.trans h₁ h₂

theorem respectsId     (a     : ω) :
  compFF φ ψ (id_ (F a)) ≈ id' :=
let h₁ : ψ (φ (id_ (F a))) ≈ ψ (id_ (G a)) := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsId a);
let h₂ : ψ (id_ (G a))     ≈ id_ (H a)     := ψ.isFunctor.respectsId a;
Setoid.trans h₁ h₂

theorem respectsInv    {a b   : ω} (e : F a ≃ F b) :
  compFF φ ψ e⁻¹ ≈ (compFF φ ψ e)⁻¹ :=
let h₁ : ψ (φ e⁻¹) ≈ ψ (φ e)⁻¹   := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsInv e);
let h₂ : ψ (φ e)⁻¹ ≈ (ψ (φ e))⁻¹ := ψ.isFunctor.respectsInv (φ e);
Setoid.trans h₁ h₂

instance isFunctor : IsIsomorphismFunctor ⟨iso S, F⟩ ⟨iso U, H⟩ (compFF φ ψ) :=
{ respectsSetoid := compFF.respectsSetoid φ ψ,
  respectsComp   := compFF.respectsComp   φ ψ,
  respectsId     := compFF.respectsId     φ ψ,
  respectsInv    := compFF.respectsInv    φ ψ }

end compFF

def genFun : GeneralizedFunctor F H := ⟨compFF φ ψ⟩

end comp

def comp.genFun' {β : Sort v} {F : ω → S} {G : β → T} {H : β → U} (I : ω → β)
                 (φ : GeneralizedFunctor F (G ∘ I)) (ψ : GeneralizedFunctor G H) :
  GeneralizedFunctor F (H ∘ I) :=
comp.genFun φ (generalizeFunctor I ψ)

namespace const

variable {F : ω → S} (c : T)

def genFun : GeneralizedFunctor F (Function.const ω c) :=
{ mapEquiv  := λ _ => IsEquivalence.refl c,
  isFunctor := { respectsSetoid := λ _   => Setoid.refl (id_ c),
                 respectsComp   := λ _ _ => Setoid.symm (leftId (id_ c)),
                 respectsId     := λ _   => Setoid.refl (id_ c),
                 respectsInv    := λ _   => Setoid.symm (idInv c) } }

end const

end GeneralizedFunctor

open GeneralizedFunctor



-- If we have two functions that map from an arbitrary `ω` into the same structure `S`, and for each
-- instance of `ω` we have an equivalence between the values of both functions, that gives us something
-- that can act as an equivalence between the two functions. In particular:
--
-- * If both are functors, this gives us a definition of equivalence of functors.
--
-- * If only one of them is a functor, we can use the equivalence to turn the other function into a
--   functor as well.

def DependentStructure {ω : Sort w} (C : ω → Structure) := ∀ a, C a

namespace DependentStructure

variable {ω : Sort w} {C : ω → Structure}

def generalizeDependentStructure {β : Sort v} (H : β → ω) (F : DependentStructure C) : DependentStructure (C ∘ H) :=
λ b => F (H b)

def DependentEquiv (F G : DependentStructure C) := ∀ a, F a ≃ G a

namespace DependentEquiv

def refl  (F     : DependentStructure C)                                                   : DependentEquiv F F :=
λ a => IsEquivalence.refl  (F a)
def symm  {F G   : DependentStructure C} (φ : DependentEquiv F G)                          : DependentEquiv G F :=
λ a => IsEquivalence.symm  (φ a)
def trans {F G H : DependentStructure C} (φ : DependentEquiv F G) (ψ : DependentEquiv G H) : DependentEquiv F H :=
λ a => IsEquivalence.trans (φ a) (ψ a)

def dependentIsoStructure (F G : DependentStructure C) (a : ω) := isoStructure (F a) (G a)

def generalizeDependentEquiv {β : Sort v} (H : β → ω) {F G : DependentStructure C} (φ : DependentEquiv F G) :
  DependentEquiv (generalizeDependentStructure H F) (generalizeDependentStructure H G) :=
λ b => φ (H b)

def EquivEquiv {F G : DependentStructure C} (φ ψ : DependentEquiv F G) :=
@DependentEquiv ω (dependentIsoStructure F G) φ ψ

namespace EquivEquiv

variable {F G : DependentStructure C}

theorem refl  (φ     : DependentEquiv F G)                                           : EquivEquiv φ φ :=
@DependentEquiv.refl ω (dependentIsoStructure F G) φ
theorem symm  {φ ψ   : DependentEquiv F G} (e : EquivEquiv φ ψ)                      : EquivEquiv ψ φ :=
DependentEquiv.symm  e
theorem trans {φ ψ χ : DependentEquiv F G} (e : EquivEquiv φ ψ) (f : EquivEquiv ψ χ) : EquivEquiv φ χ :=
DependentEquiv.trans e f

instance dependentEquivSetoid : Setoid (DependentEquiv F G) := ⟨EquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquiv

def dependentEquiv : GeneralizedRelation (DependentStructure C) := λ F G => ⟨DependentEquiv F G⟩

@[reducible] def DependentDependentEquiv {β : Sort v} (H : β → DependentStructure C) (b c : β) := DependentEquiv (H b) (H c)

namespace DependentDependentEquiv

variable {β : Sort v} {H : β → DependentStructure C}

def refl  (b     : β)                                                                         : DependentDependentEquiv H b b :=
DependentEquiv.refl  (H b)
def symm  {b c   : β} (e : DependentDependentEquiv H b c)                                     : DependentDependentEquiv H c b :=
DependentEquiv.symm  e
def trans {b c d : β} (e : DependentDependentEquiv H b c) (f : DependentDependentEquiv H c d) : DependentDependentEquiv H b d :=
DependentEquiv.trans e f

instance EquivEquiv.dependentDependentEquivSetoid {b c : β} : Setoid (DependentDependentEquiv H b c) := EquivEquiv.dependentEquivSetoid

def dependentDependentEquiv : GeneralizedRelation β := λ b c => ⟨DependentDependentEquiv H b c⟩

instance dependentDependentEquivHasIso : HasIsomorphisms (@dependentDependentEquiv ω C β H) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ a => congrArgComp (hφ a) (hψ a),
  assoc        := λ φ ψ χ a => assoc        (φ a) (ψ a) (χ a),
  id           := refl,
  leftId       := λ φ     a => leftId       (φ a),
  rightId      := λ φ     a => rightId      (φ a),
  inv          := symm,
  congrArgInv  := λ hφ    a => congrArgInv  (hφ a),
  leftInv      := λ φ     a => leftInv      (φ a),
  rightInv     := λ φ     a => rightInv     (φ a),
  invInv       := λ φ     a => invInv       (φ a),
  compInv      := λ φ ψ   a => compInv      (φ a) (ψ a),
  idInv        := λ b     a => idInv        (H b a) }

end DependentDependentEquiv

instance dependentEquivHasIso : HasIsomorphisms (@dependentEquiv ω C) :=
DependentDependentEquiv.dependentDependentEquivHasIso (H := id)

end DependentEquiv

end DependentStructure

open DependentStructure



namespace DependentEquiv

variable {ω : Sort w} {S : Structure} {F G : ω → S} (φ : DependentEquiv F G)

-- We can "transport" an equivalence `e` between two values of `F` to an equivalence between the
-- corresponding two values of another equivalent function `G`.

def transport    {a b : ω} (e : F a ≃ F b) : G a ≃ G b := φ b • e • (φ a)⁻¹
def invTransport {a b : ω} (e : G a ≃ G b) : F a ≃ F b := (φ b)⁻¹ • e • φ a

namespace transport

theorem isInverse {a b : ω} (e : G a ≃ G b) :
  transport (DependentEquiv.symm φ) e ≈ invTransport φ e :=
congrArgCompRight (congrArgCompRight (invInv (φ a)))

theorem respectsSetoid {a b   : ω} {e₁ e₂ : F a ≃ F b} (h : e₁ ≈ e₂) :
  transport φ e₁ ≈ transport φ e₂ :=
congrArgCompRight (congrArgCompLeft h)

theorem respectsComp   {a b c : ω} (e : F a ≃ F b) (f : F b ≃ F c) :
  transport φ (f • e) ≈ transport φ f • transport φ e :=
let φa := φ a;
let φb := φ b;
let φc := φ c;
let h₁ : φc • (f • e) • φa⁻¹ ≈ φc • (f • (id' • e)) • φa⁻¹           := congrArgCompRight (congrArgCompLeft (congrArgCompRight (Setoid.symm (leftId e))));
let h₂ : φc • (f • e) • φa⁻¹ ≈ φc • (f • ((φb⁻¹ • φb) • e)) • φa⁻¹   := Setoid.trans h₁ (congrArgCompRight (congrArgCompLeft (congrArgCompRight (congrArgCompLeft (Setoid.symm (leftInv φb))))));
let h₃ : φc • (f • e) • φa⁻¹ ≈ φc • (f • (φb⁻¹ • (φb • e))) • φa⁻¹   := Setoid.trans h₂ (congrArgCompRight (congrArgCompLeft (congrArgCompRight (Setoid.symm (assoc e φb φb⁻¹)))));
let h₄ : φc • (f • e) • φa⁻¹ ≈ φc • ((f • φb⁻¹) • (φb • e)) • φa⁻¹   := Setoid.trans h₃ (congrArgCompRight (congrArgCompLeft (assoc (φb • e) φb⁻¹ f)));
let h₅ : φc • (f • e) • φa⁻¹ ≈ φc • (f • φb⁻¹) • ((φb • e) • φa⁻¹)   := Setoid.trans h₄ (congrArgCompRight (Setoid.symm (assoc φa⁻¹ (φb • e) (f • φb⁻¹))));
let h₆ : φc • (f • e) • φa⁻¹ ≈ (φc • (f • φb⁻¹)) • ((φb • e) • φa⁻¹) := Setoid.trans h₅ (assoc ((φb • e) • φa⁻¹) (f • φb⁻¹) φc);
let h₇ : φc • (f • e) • φa⁻¹ ≈ (φc • f • φb⁻¹) • (φb • e • φa⁻¹)     := Setoid.trans h₆ (congrArgCompRight (Setoid.symm (assoc φa⁻¹ e φb)));
h₇

theorem respectsId     (a     : ω) :
  transport φ (id_ (F a)) ≈ id' :=
let φa := φ a;
let h₁ : φa • id' • φa⁻¹ ≈ id' := substCompRight (leftId φa⁻¹) (rightInv φa);
h₁

theorem respectsInv    {a b   : ω} (e : F a ≃ F b) :
  transport φ e⁻¹ ≈ (transport φ e)⁻¹ :=
let φa := φ a;
let φb := φ b;
let h₁ : φa • e⁻¹ • φb⁻¹ ≈ (φa⁻¹)⁻¹ • (φb • e)⁻¹ := congrArgComp (Setoid.symm (compInv e φb)) (Setoid.symm (invInv φa));
let h₂ : φa • e⁻¹ • φb⁻¹ ≈ ((φb • e) • φa⁻¹)⁻¹   := Setoid.trans h₁ (Setoid.symm (compInv φa⁻¹ (φb • e)));
let h₃ : φa • e⁻¹ • φb⁻¹ ≈ (φb • e • φa⁻¹)⁻¹     := Setoid.trans h₂ (congrArgInv (Setoid.symm (assoc φa⁻¹ e φb)));
h₃

def functor : GeneralizedFunctor F G :=
{ mapEquiv  := transport φ,
  isFunctor := { respectsSetoid := respectsSetoid φ,
                 respectsComp   := respectsComp   φ,
                 respectsId     := respectsId     φ,
                 respectsInv    := respectsInv    φ } }

theorem invRespectsSetoid {a b   : ω} {e₁ e₂ : G a ≃ G b} (h : e₁ ≈ e₂) :
  invTransport φ e₁ ≈ invTransport φ e₂ :=
let h₁ := respectsSetoid (DependentEquiv.symm φ) h;
Setoid.trans (Setoid.symm (isInverse φ e₁)) (Setoid.trans h₁ (isInverse φ e₂))

theorem invRespectsComp   {a b c : ω} (e : G a ≃ G b) (f : G b ≃ G c) :
  invTransport φ (f • e) ≈ invTransport φ f • invTransport φ e :=
let h₁ := respectsComp (DependentEquiv.symm φ) e f;
Setoid.trans (Setoid.symm (isInverse φ (f • e))) (Setoid.trans h₁ (congrArgComp (isInverse φ e) (isInverse φ f)))

theorem invRespectsId     (a     : ω) :
  invTransport φ (id_ (G a)) ≈ id' :=
let h₁ := respectsId (DependentEquiv.symm φ) a;
Setoid.trans (Setoid.symm (isInverse φ (id_ (G a)))) h₁

theorem invRespectsInv    {a b   : ω} (e : G a ≃ G b) :
  invTransport φ e⁻¹ ≈ (invTransport φ e)⁻¹ :=
let h₁ := respectsInv (DependentEquiv.symm φ) e;
Setoid.trans (Setoid.symm (isInverse φ e⁻¹)) (Setoid.trans h₁ (congrArgInv (isInverse φ e)))

def invFunctor : GeneralizedFunctor G F :=
{ mapEquiv  := invTransport φ,
  isFunctor := { respectsSetoid := invRespectsSetoid φ,
                 respectsComp   := invRespectsComp   φ,
                 respectsId     := invRespectsId     φ,
                 respectsInv    := invRespectsInv    φ } }

end transport

end DependentEquiv



def GeneralizedNaturalityCondition {ω : Sort w} {S T : Structure} {F : ω → S} {G₁ G₂ : ω → T}
                                   (φ : GeneralizedFunctor F G₁) (ψ : GeneralizedFunctor F G₂)
                                   (ext : DependentEquiv G₁ G₂) :=
∀ {a b : ω} (e : F a ≃ F b), ψ e • ext a ≈ ext b • φ e

namespace GeneralizedNaturalityCondition

variable {ω : Sort w} {S T : Structure}

theorem refl  {F : ω → S} {G₁       : ω → T}
              (φ : GeneralizedFunctor F G₁) :
  GeneralizedNaturalityCondition φ φ (DependentEquiv.refl G₁) :=
λ e => Setoid.trans (rightId (φ e)) (Setoid.symm (leftId (φ e)))

theorem symm  {F : ω → S} {G₁ G₂    : ω → T}
              {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂}
              {ext : DependentEquiv G₁ G₂}
              (nat : GeneralizedNaturalityCondition φ ψ ext) :
  GeneralizedNaturalityCondition ψ φ (DependentEquiv.symm ext) :=
λ {a b} e => Setoid.symm ((leftRightMul (ext a) (φ e) (ψ e) (ext b)).mpr (nat e))

theorem trans {F : ω → S} {G₁ G₂ G₃ : ω → T}
              {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂} {χ : GeneralizedFunctor F G₃}
              {ext₁ : DependentEquiv G₁ G₂}                    {ext₂ : DependentEquiv G₂ G₃}
              (nat₁ : GeneralizedNaturalityCondition φ ψ ext₁) (nat₂ : GeneralizedNaturalityCondition ψ χ ext₂) :
  GeneralizedNaturalityCondition φ χ (DependentEquiv.trans ext₁ ext₂) :=
λ {a b} e => let h₁ := (rightMulInv (ψ e) (ext₁ b • φ e) (ext₁ a)).mp  (nat₁ e);
             let h₂ := (leftMulInv' (χ e • ext₂ a) (ψ e) (ext₂ b)).mpr (nat₂ e);
             let h₃ := (leftRightMul (ext₁ a) (ext₁ b • φ e) (χ e • ext₂ a) (ext₂ b)).mp (Setoid.trans h₂ h₁);
             applyAssocLeft' (applyAssocRight h₃)

end GeneralizedNaturalityCondition



structure GeneralizedNaturalTransformation {ω : Sort w} {S T : Structure} {F : ω → S} {G₁ G₂ : ω → T}
                                           (φ : GeneralizedFunctor F G₁) (ψ : GeneralizedFunctor F G₂) where
(ext : DependentEquiv G₁ G₂)
(nat : GeneralizedNaturalityCondition φ ψ ext)

namespace GeneralizedNaturalTransformation

variable {ω : Sort w} {S T : Structure}

def refl  {F : ω → S} {G₁       : ω → T} (φ : GeneralizedFunctor F G₁) :
  GeneralizedNaturalTransformation φ φ :=
⟨DependentEquiv.refl  G₁,          GeneralizedNaturalityCondition.refl  φ⟩

def symm  {F : ω → S} {G₁ G₂    : ω → T} {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂}
          (m : GeneralizedNaturalTransformation φ ψ) :
  GeneralizedNaturalTransformation ψ φ :=
⟨DependentEquiv.symm  m.ext,       GeneralizedNaturalityCondition.symm  m.nat⟩

def trans {F : ω → S} {G₁ G₂ G₃ : ω → T} {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂} {χ : GeneralizedFunctor F G₃}
          (m : GeneralizedNaturalTransformation φ ψ) (n : GeneralizedNaturalTransformation ψ χ) :
  GeneralizedNaturalTransformation φ χ :=
⟨DependentEquiv.trans m.ext n.ext, GeneralizedNaturalityCondition.trans m.nat n.nat⟩

instance naturalTransformationSetoid {F : ω → S} {G₁ G₂ : ω → T} (φ : GeneralizedFunctor F G₁) (ψ : GeneralizedFunctor F G₂) :
  Setoid (GeneralizedNaturalTransformation φ ψ) :=
⟨λ e f => DependentEquiv.EquivEquiv e.ext f.ext,
 ⟨λ e => DependentEquiv.EquivEquiv.refl e.ext, DependentEquiv.EquivEquiv.symm, DependentEquiv.EquivEquiv.trans⟩⟩

def generalizeNaturalTransformation {β : Sort v} {F : ω → S} {G₁ G₂ : ω → T} (H : β → ω)
                                    {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂}
                                    (n : GeneralizedNaturalTransformation φ ψ) :
  GeneralizedNaturalTransformation (generalizeFunctor H φ) (generalizeFunctor H ψ) :=
⟨DependentEquiv.generalizeDependentEquiv H n.ext, n.nat⟩

end GeneralizedNaturalTransformation



-- A functor between two `Structure`s is a map that also maps equivalences in a compatible way. On the
-- one hand, this is just a groupoid functor, but on the other hand, the mapping of equivalences also
-- matches exactly the `transport` map mentioned in the introduction.
--
-- Moreover, if we interpret `≃` as a generalization of equality, the mapping of equivalences is actually
-- the generalized version of `congrArg`, so we name it `congrArgMap`. Under this interpretation, it can
-- also be regarded as a well-definedness condition for the map: equality of arguments implies equality of
-- results.

structure StructureFunctor (S T : Structure) :=
(map     : S → T)
(functor : Functor map)

namespace StructureFunctor

variable {S T U V : Structure}

instance functorCoeFun : CoeFun (StructureFunctor S T) (λ _ => S → T) := ⟨StructureFunctor.map⟩

        theorem respectsSetoid (F : StructureFunctor S T) {a b   : S} {f₁ f₂ : a ≃ b} :
  f₁ ≈ f₂ → F.functor f₁ ≈ F.functor f₂         := F.functor.isFunctor.respectsSetoid
@[simp] theorem respectsComp   (F : StructureFunctor S T) {a b c : S} (f : a ≃ b) (g : b ≃ c) :
  F.functor (g • f) ≈ F.functor g • F.functor f := F.functor.isFunctor.respectsComp f g
@[simp] theorem respectsId     (F : StructureFunctor S T) (a     : S) :
  F.functor (id_ a) ≈ id'                       := F.functor.isFunctor.respectsId   a
@[simp] theorem respectsInv    (F : StructureFunctor S T) {a b   : S} (f : a ≃ b) :
  F.functor f⁻¹     ≈ (F.functor f)⁻¹           := F.functor.isFunctor.respectsInv  f



def congrArgMap (F : StructureFunctor S T) {a b : S} : a ≃ b → F a ≃ F b := F.functor.mapEquiv



-- We can define equivalence of functors by extensionality, using equivalence in `T` instead of equality.
-- This is an equivalence according to our definition, and it is compatible with isomorphisms via the
-- functor axioms, so we can use it to build an instance of `Structure` again.
--
-- For equivalence of functors to be well-behaved, we additionally need to require equivalences to be
-- natural transformations.

def FunExt (F G : StructureFunctor S T) := DependentEquiv.DependentDependentEquiv StructureFunctor.map F G

namespace FunExt

instance {F G : StructureFunctor S T} : Setoid (FunExt F G) :=
DependentEquiv.DependentDependentEquiv.EquivEquiv.dependentDependentEquivSetoid

def funExt : GeneralizedRelation (StructureFunctor S T) := λ F G => ⟨FunExt F G⟩

instance funExtHasIso : HasIsomorphisms (@funExt S T) := DependentEquiv.DependentDependentEquiv.dependentDependentEquivHasIso

end FunExt

def FunctorEquiv (F G : StructureFunctor S T) := GeneralizedNaturalTransformation F.functor G.functor

namespace FunctorEquiv

def refl  (F     : StructureFunctor S T)                                               : FunctorEquiv F F :=
GeneralizedNaturalTransformation.refl  F.functor
def symm  {F G   : StructureFunctor S T} (φ : FunctorEquiv F G)                        : FunctorEquiv G F :=
GeneralizedNaturalTransformation.symm  φ
def trans {F G H : StructureFunctor S T} (φ : FunctorEquiv F G) (ψ : FunctorEquiv G H) : FunctorEquiv F H :=
GeneralizedNaturalTransformation.trans φ ψ

instance (F G : StructureFunctor S T) : Setoid (FunctorEquiv F G) :=
GeneralizedNaturalTransformation.naturalTransformationSetoid F.functor G.functor

def functorEquiv : GeneralizedRelation (StructureFunctor S T) := λ F G => ⟨FunctorEquiv F G⟩

instance functorEquivHasIso : HasIsomorphisms (@functorEquiv S T) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ => FunExt.funExtHasIso.congrArgComp hφ hψ,
  assoc        := λ φ ψ χ => FunExt.funExtHasIso.assoc        φ.ext ψ.ext χ.ext,
  id           := refl,
  leftId       := λ φ     => FunExt.funExtHasIso.leftId       φ.ext,
  rightId      := λ φ     => FunExt.funExtHasIso.rightId      φ.ext,
  inv          := symm,
  congrArgInv  := λ hφ    => FunExt.funExtHasIso.congrArgInv  hφ,
  leftInv      := λ φ     => FunExt.funExtHasIso.leftInv      φ.ext,
  rightInv     := λ φ     => FunExt.funExtHasIso.rightInv     φ.ext,
  invInv       := λ φ     => FunExt.funExtHasIso.invInv       φ.ext,
  compInv      := λ φ ψ   => FunExt.funExtHasIso.compInv      φ.ext ψ.ext,
  idInv        := λ b     => FunExt.funExtHasIso.idInv        b }

end FunctorEquiv

instance functorHasStructure : HasStructure (StructureFunctor S T) := ⟨FunctorEquiv.functorEquiv⟩
def functorStructure (S T : Structure) : Structure := ⟨StructureFunctor S T⟩

instance : CoeFun (IsType.type (functorStructure S T)) (λ _ => S → T) := functorCoeFun



-- We have two alternative definitions of `congr` for functors, depending on the order in which we apply
-- the functor and argument equivalences. The natural transformation axiom says exactly that the order
-- does not matter.

def congrMap  {F₁ F₂ : StructureFunctor S T} {a b : S} : F₁ ≃ F₂ → a ≃ b → F₁ a ≃ F₂ b :=
λ φ e => trans (φ.ext a) (F₂.functor e)

def congrMap' {F₁ F₂ : StructureFunctor S T} {a b : S} : F₁ ≃ F₂ → a ≃ b → F₁ a ≃ F₂ b :=
λ φ e => trans (F₁.functor e) (φ.ext b)

theorem congrMap.wd {F₁ F₂ : StructureFunctor S T} {a b : S} (φ : F₁ ≃ F₂) (e : a ≃ b) :
  congrMap φ e ≈ congrMap' φ e :=
φ.nat e



-- Now we define identity and composition and prove that they are well-behaved with respect to equivalence.

def idFun : StructureFunctor S S := ⟨id, id.genFun⟩

def compMap     (F : StructureFunctor S T) (G : StructureFunctor T U) : S → U :=
λ f => G (F f)

def compFunctor (F : StructureFunctor S T) (G : StructureFunctor T U) : Functor (compMap F G) :=
comp.genFun' F.map F.functor G.functor

def compFun     (F : StructureFunctor S T) (G : StructureFunctor T U) : StructureFunctor S U :=
⟨compMap F G, compFunctor F G⟩

-- TODO: Unfortunately, this doesn't let us use `•` at the moment because of a strange defeq issue.
-- So we need to define a separate notation
instance hasComp : HasComp StructureFunctor := ⟨compFun⟩

@[reducible] def revCompFun (G : StructureFunctor T U) (F : StructureFunctor S T) : StructureFunctor S U := compFun F G
infixr:90 " ⊙ " => revCompFun



namespace compFun

def congrArgLeft {F : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} :
  G₁ ≃ G₂ → G₁ ⊙ F ≃ G₂ ⊙ F :=
λ φ => { ext := λ a => φ.ext (F a),
         nat := λ e => φ.nat (F.functor e) }

namespace congrArgLeft

theorem respectsSetoid {F : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U}
                       {φ₁ φ₂ : G₁ ≃ G₂} :
  φ₁ ≈ φ₂ → congrArgLeft (F := F) φ₁ ≈ congrArgLeft (F := F) φ₂ :=
λ hφ a => hφ (F a)

theorem respectsComp {F : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T U}
                     (φ₁ : G₁ ≃ G₂) (φ₂ : G₂ ≃ G₃) :
  congrArgLeft (F := F) (φ₂ • φ₁) ≈ congrArgLeft φ₂ • congrArgLeft φ₁ :=
λ a => Setoid.refl (φ₂.ext (F a) • φ₁.ext (F a))

theorem respectsId {F : StructureFunctor S T} (G : StructureFunctor T U) :
  congrArgLeft (id_ G) ≈ id_ (G ⊙ F) :=
λ a => Setoid.refl (id_ (G (F a)))

theorem respectsInv {F : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (φ : G₁ ≃ G₂) :
  congrArgLeft (F := F) φ⁻¹ ≈ (congrArgLeft φ)⁻¹ :=
λ a => Setoid.refl (φ.ext (F a))⁻¹

def functor (U : Structure) (F : StructureFunctor S T) : StructureFunctor (functorStructure T U) (functorStructure S U) :=
{ map     := λ G => G ⊙ F,
  functor := { mapEquiv  := congrArgLeft,
               isFunctor := { respectsSetoid := respectsSetoid,
                              respectsComp   := respectsComp,
                              respectsId     := respectsId,
                              respectsInv    := respectsInv } } }

end congrArgLeft

def congrArgRight {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U} :
  F₁ ≃ F₂ → G ⊙ F₁ ≃ G ⊙ F₂ :=
λ φ => { ext := λ a => G.functor (φ.ext a),
         nat := λ {a b} e => let h₁ := respectsSetoid G (φ.nat e);
                             let h₂ := Setoid.trans (Setoid.symm (respectsComp G (φ.ext a) (F₂.functor e))) h₁;
                             let h₄ := Setoid.trans h₂ (respectsComp G (F₁.functor e) (φ.ext b));
                             h₄ }

namespace congrArgRight

theorem respectsSetoid {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U}
                       {φ₁ φ₂ : F₁ ≃ F₂} :
  φ₁ ≈ φ₂ → congrArgRight (G := G) φ₁ ≈ congrArgRight (G := G) φ₂ :=
λ hφ a => StructureFunctor.respectsSetoid G (hφ a)

theorem respectsComp {F₁ F₂ F₃ : StructureFunctor S T} {G : StructureFunctor T U}
                     (φ₁ : F₁ ≃ F₂) (φ₂ : F₂ ≃ F₃) :
  congrArgRight (G := G) (φ₂ • φ₁) ≈ congrArgRight φ₂ • congrArgRight φ₁ :=
λ a => StructureFunctor.respectsComp G (φ₁.ext a) (φ₂.ext a)

theorem respectsId (F : StructureFunctor S T) {G : StructureFunctor T U} :
  congrArgRight (id_ F) ≈ id_ (G ⊙ F) :=
λ a => StructureFunctor.respectsId G (F a)

theorem respectsInv {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U} (φ : F₁ ≃ F₂) :
  congrArgRight (G := G) φ⁻¹ ≈ (congrArgRight φ)⁻¹ :=
λ a => StructureFunctor.respectsInv G (φ.ext a)

def functor (S : Structure) (G : StructureFunctor T U) : StructureFunctor (functorStructure S T) (functorStructure S U) :=
{ map     := λ F => G ⊙ F,
  functor := { mapEquiv  := congrArgRight,
               isFunctor := { respectsSetoid := respectsSetoid,
                              respectsComp   := respectsComp,
                              respectsId     := respectsId (G := G),
                              respectsInv    := respectsInv } } }

end congrArgRight

def congrArg  {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} :
  F₁ ≃ F₂ → G₁ ≃ G₂ → G₁ ⊙ F₁ ≃ G₂ ⊙ F₂ :=
λ φ ψ => FunctorEquiv.trans (congrArgLeft ψ) (congrArgRight φ)

def congrArg' {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} :
  F₁ ≃ F₂ → G₁ ≃ G₂ → G₁ ⊙ F₁ ≃ G₂ ⊙ F₂ :=
λ φ ψ => FunctorEquiv.trans (congrArgRight φ) (congrArgLeft ψ)

namespace congrArg

theorem wd {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (φ : F₁ ≃ F₂) (ψ : G₁ ≃ G₂) :
  congrArg φ ψ ≈ congrArg' φ ψ :=
λ a => ψ.nat (φ.ext a)

theorem respectsSetoid {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U}
                       {φ₁ φ₂ : F₁ ≃ F₂} {ψ₁ ψ₂ : G₁ ≃ G₂} :
  φ₁ ≈ φ₂ → ψ₁ ≈ ψ₂ → congrArg φ₁ ψ₁ ≈ congrArg φ₂ ψ₂ :=
λ hφ hψ => FunctorEquiv.functorEquivHasIso.congrArgComp (congrArgLeft.respectsSetoid hψ) (congrArgRight.respectsSetoid hφ)

theorem respectsComp {F₁ F₂ F₃ : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T U}
                     (φ₁ : F₁ ≃ F₂) (φ₂ : F₂ ≃ F₃) (ψ₁ : G₁ ≃ G₂) (ψ₂ : G₂ ≃ G₃) :
  congrArg (φ₂ • φ₁) (ψ₂ • ψ₁) ≈ congrArg φ₂ ψ₂ • congrArg φ₁ ψ₁ :=
let h₁ := FunctorEquiv.functorEquivHasIso.congrArgComp (congrArgLeft.respectsComp ψ₁ ψ₂) (congrArgRight.respectsComp φ₁ φ₂);
let h₂ := congrArgCompLeft (f := congrArgLeft ψ₁) (wd φ₁ ψ₂);
let h₃ := applyAssoc' h₂;
let h₄ := congrArgCompRight (g := congrArgRight φ₂) h₃;
let h₅ := applyAssoc h₄;
Setoid.trans h₁ h₅

theorem respectsId (F : StructureFunctor S T) (G : StructureFunctor T U) :
  congrArg (id_ F) (id_ G) ≈ id_ (G ⊙ F) :=
let h₁ := FunctorEquiv.functorEquivHasIso.congrArgComp (congrArgLeft.respectsId G) (congrArgRight.respectsId F);
Setoid.trans h₁ (leftId id')

theorem respectsInv {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (φ : F₁ ≃ F₂) (ψ : G₁ ≃ G₂) :
  congrArg φ⁻¹ ψ⁻¹ ≈ (congrArg φ ψ)⁻¹ :=
let h₁ := FunctorEquiv.functorEquivHasIso.congrArgComp (congrArgLeft.respectsInv ψ) (congrArgRight.respectsInv φ);
let h₂ := congrArgInv (wd φ ψ);
let h₃ := compInv (congrArgRight φ) (congrArgLeft ψ);
Setoid.trans h₁ (Setoid.symm (Setoid.trans h₂ h₃))

end congrArg

def assoc (F : StructureFunctor S T) (G : StructureFunctor T U) (H : StructureFunctor U V) :
  H ⊙ (G ⊙ F) ≃ (H ⊙ G) ⊙ F :=
FunctorEquiv.refl (H ⊙ G ⊙ F)

end compFun



namespace idFun

def leftId (F : StructureFunctor S T) : idFun ⊙ F ≃ F :=
{ ext := λ a => refl (F a),
  nat := GeneralizedNaturalityCondition.refl F.functor }

def rightId (F : StructureFunctor S T) : F ⊙ idFun ≃ F :=
{ ext := λ a => refl (F a),
  nat := GeneralizedNaturalityCondition.refl F.functor }

end idFun



namespace compFun.congrArgLeft.functor

def mapEquiv (U : Structure) {F₁ F₂ : StructureFunctor S T} (φ : F₁ ≃ F₂) : functor U F₁ ≃ functor U F₂ :=
{ ext := λ G => congrArgRight (G := G) φ,
  nat := λ ψ => Setoid.symm (congrArg.wd φ ψ) }

def functorFunctor (U : Structure)
  : StructureFunctor (functorStructure S T) (functorStructure (functorStructure T U) (functorStructure S U)) :=
{ map     := functor U,
  functor := { mapEquiv  := mapEquiv U,
               isFunctor := { respectsSetoid := λ h   G => congrArgRight.respectsSetoid (G := G) h,
                              respectsComp   := λ φ ψ G => congrArgRight.respectsComp   (G := G) φ ψ,
                              respectsId     := λ F   G => congrArgRight.respectsId     (G := G) F,
                              respectsInv    := λ φ   G => congrArgRight.respectsInv    (G := G) φ } } }

def respectsIdFun (T S : Structure) : functor T (@idFun S) ≃ @idFun (functorStructure S T) :=
{ ext := λ F   => idFun.rightId F,
  nat := λ φ a => let e := φ.ext a;
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

def respectsCompFun (V : Structure) (F : StructureFunctor S T) (G : StructureFunctor T U) :
  functor V (G ⊙ F) ≃ functor V F ⊙ functor V G :=
{ ext := λ H   => FunctorEquiv.refl (H ⊙ (G ⊙ F)),
  nat := λ φ a => let e := φ.ext (G (F a));
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

theorem respectsCompFun.nat (V : Structure) {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (φ : F₁ ≃ F₂) (ψ : G₁ ≃ G₂) :
  compFun.congrArg (mapEquiv V ψ) (mapEquiv V φ) • respectsCompFun V F₁ G₁ ≈ respectsCompFun V F₂ G₂ • mapEquiv V (compFun.congrArg φ ψ) :=
sorry

end compFun.congrArgLeft.functor

namespace compFun.congrArgRight.functor

def mapEquiv (S : Structure) {G₁ G₂ : StructureFunctor T U} (ψ : G₁ ≃ G₂) : functor S G₁ ≃ functor S G₂ :=
{ ext := λ F => congrArgLeft (F := F) ψ,
  nat := λ φ => congrArg.wd φ ψ }

def functorFunctor (S : Structure)
  : StructureFunctor (functorStructure T U) (functorStructure (functorStructure S T) (functorStructure S U)) :=
{ map     := functor S,
  functor := { mapEquiv  := mapEquiv S,
               isFunctor := { respectsSetoid := λ h   F => congrArgLeft.respectsSetoid (F := F) h,
                              respectsComp   := λ φ ψ F => congrArgLeft.respectsComp   (F := F) φ ψ,
                              respectsId     := λ G   F => congrArgLeft.respectsId     (F := F) G,
                              respectsInv    := λ φ   F => congrArgLeft.respectsInv    (F := F) φ } } }

def respectsIdFun (S T : Structure) : functor S (@idFun T) ≃ @idFun (functorStructure S T) :=
{ ext := λ F   => idFun.leftId F,
  nat := λ φ a => let e := φ.ext a;
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

def respectsCompFun (S : Structure) (G : StructureFunctor T U) (H : StructureFunctor U V) :
  functor S (H ⊙ G) ≃ functor S H ⊙ functor S G :=
{ ext := λ F   => FunctorEquiv.refl ((H ⊙ G) ⊙ F),
  nat := λ φ a => let e := congrArgMap (H ⊙ G) (φ.ext a);
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

theorem respectsCompFun.nat (S : Structure) {G₁ G₂ : StructureFunctor T U} {H₁ H₂ : StructureFunctor U V} (φ : G₁ ≃ G₂) (ψ : H₁ ≃ H₂) :
  compFun.congrArg (mapEquiv S φ) (mapEquiv S ψ) • respectsCompFun S G₁ H₁ ≈ respectsCompFun S G₂ H₂ • mapEquiv S (compFun.congrArg φ ψ) :=
sorry

end compFun.congrArgRight.functor



-- The constant functor.

def constFun (c : T) : StructureFunctor S T :=
{ map     := Function.const (IsType.type S) c,
  functor := const.genFun c }



-- A simple alias for the assertion that a functor is equivalent to the identity functor.

@[reducible] def IsId (F : StructureFunctor S S) := F ≃ @idFun S

namespace IsId

-- `ext` and `nat` have a slightly simpler form in this case.

def extDef {F : StructureFunctor S S} (φ : IsId F) (a : S) : F a ≃ a :=
φ.ext a

theorem natDef {F : StructureFunctor S S} (φ : IsId F) {a b : S} (e : a ≃ b) :
  e • φ.ext a ≈ φ.ext b • F.functor e :=
φ.nat e

-- When composing both sides with another functor, we can cancel `idFun`.

def rightMul {G : StructureFunctor T T} (ψ : IsId G) (F : StructureFunctor S T) :
  G ⊙ F ≃ F :=
FunctorEquiv.trans (compFun.congrArgLeft (F := F) ψ) (idFun.leftId F)

theorem rightMulDef {G : StructureFunctor T T} (ψ : IsId G) (F : StructureFunctor S T) (a : S) :
  (rightMul ψ F).ext a ≈ ψ.ext (F a) :=
leftId (ψ.ext (F a))

def leftMul {F : StructureFunctor S S} (φ : IsId F) (G : StructureFunctor S T) :
  G ⊙ F ≃ G :=
FunctorEquiv.trans (compFun.congrArgRight (G := G) φ) (idFun.rightId G)

theorem leftMulDef {F : StructureFunctor S S} (φ : IsId F) (G : StructureFunctor S T) (a : S) :
  (leftMul φ G).ext a ≈ G.functor (φ.ext a) :=
leftId (G.functor (φ.ext a))

-- We have some definitions resembling reflexivity and transitivity.

def refl (S : Structure) : IsId (@idFun S) := FunctorEquiv.refl idFun

def trans {F G : StructureFunctor S S} (φ : IsId F) (ψ : IsId G) : IsId (G ⊙ F) :=
FunctorEquiv.trans (rightMul ψ F) φ

theorem transDef {F G : StructureFunctor S S} (φ : IsId F) (ψ : IsId G) (a : S) :
  (trans φ ψ).ext a ≈ φ.ext a • ψ.ext (F a) :=
congrArgCompRight (rightMulDef ψ F a)

end IsId



-- A simple alias for the assertion that `G` is a left inverse of `F`.
-- Note that instead of defining `RightInv` analogously, we just swap the arguments of `F` and `G` where
-- necessary.

@[reducible] def LeftInv (F : StructureFunctor S T) (G : StructureFunctor T S) := IsId (G ⊙ F)

namespace LeftInv

def refl (S : Structure) : LeftInv (@idFun S) (@idFun S) := IsId.refl S

def trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
          (φ : LeftInv F G) (ψ : LeftInv H I) :
  LeftInv (H ⊙ F) (G ⊙ I) :=
let χ : (G ⊙ I) ⊙ (H ⊙ F) ≃ G ⊙ F := compFun.congrArgLeft (F := F) (IsId.leftMul ψ G);
FunctorEquiv.trans χ φ

theorem transDef {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
                 (φ : LeftInv F G) (ψ : LeftInv H I) (a : S) :
  (trans φ ψ).ext a ≈ φ.ext a • G.functor (ψ.ext (F a)) :=
congrArgCompRight (IsId.leftMulDef ψ G (F a))

theorem reflTrans {F : StructureFunctor S T} {G : StructureFunctor T S}
                  (φ : LeftInv F G) :
  trans (refl S) φ ≈ φ :=
λ a => let h₁ : (trans (refl S) φ).ext a ≈ id_ a • φ.ext a := transDef (refl S) φ a;
       let h₂ : id_ a • φ.ext a ≈ φ.ext a                  := leftId (φ.ext a);
       Setoid.trans h₁ h₂

theorem transRefl {F : StructureFunctor S T} {G : StructureFunctor T S}
                  (φ : LeftInv F G) :
  trans φ (refl T) ≈ φ :=
λ a => let h₁ := transDef φ (refl T) a;
       let h₂ := rightCancelId (respectsId G (F a));
       Setoid.trans h₁ h₂

theorem transAssoc {F : StructureFunctor S T} {G : StructureFunctor T S}
                   {H : StructureFunctor T U} {I : StructureFunctor U T}
                   {J : StructureFunctor U V} {K : StructureFunctor V U}
                   (φ : LeftInv F G) (ψ : LeftInv H I) (χ : LeftInv J K) :
  let l : LeftInv (J ⊙ H ⊙ F) (G ⊙ I ⊙ K) := trans (trans φ ψ) χ;
  let r : LeftInv (J ⊙ H ⊙ F) (G ⊙ I ⊙ K) := trans φ (trans ψ χ);
  l ≈ r :=
λ a => let h₁ := applyAssocRight' (substCompLeft' (transDef φ ψ a) (transDef (trans φ ψ) χ a));
       let h₂ := substCompRight' (Setoid.symm (respectsComp G (I.functor.mapEquiv (χ.ext (H (F a)))) (ψ.ext (F a)))) h₁;
       let h₃ := substCompRight' (respectsSetoid G (transDef ψ χ (F a))) (transDef φ (trans ψ χ) a);
       Setoid.trans h₂ (Setoid.symm h₃)

-- This definition asserts that an instance of `LeftInv` is compatible with a corresponding reversed
-- `LeftInv` instance. It corresponds to one of the two equations of an adjoint functor (the one about
-- `F`).

def Compat {F : StructureFunctor S T} {G : StructureFunctor T S} (φl : LeftInv F G) (φr : LeftInv G F) :=
∀ a, F.functor (φl.ext a) ≈ φr.ext (F a)

namespace Compat

theorem refl (S : Structure) : Compat (LeftInv.refl S) (LeftInv.refl S) :=
λ a => Setoid.refl (IsEquivalence.refl a)

theorem trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
              {φl : LeftInv F G} {φr : LeftInv G F} {ψl : LeftInv H I} {ψr : LeftInv I H}
              (c : Compat φl φr) (d : Compat ψl ψr) :
  Compat (LeftInv.trans φl ψl) (LeftInv.trans ψr φr) :=
λ a => let h₁ : φr.ext (F a) • F.functor (G.functor (ψl.ext (F a))) ≈ ψl.ext (F a) • φr.ext (I (H (F a)))                                 := Setoid.symm (φr.nat (ψl.ext (F a)));
       let h₂ : F.functor (φl.ext a) • F.functor (G.functor (ψl.ext (F a))) ≈ ψl.ext (F a) • φr.ext (I (H (F a)))                         := substCompLeft (c a) h₁;
       let h₃ : F.functor (φl.ext a • G.functor (ψl.ext (F a))) ≈ ψl.ext (F a) • φr.ext (I (H (F a)))                                     := Setoid.trans (respectsComp F (G.functor (ψl.ext (F a))) (φl.ext a)) h₂;
       let h₄ : H.functor (F.functor (φl.ext a • G.functor (ψl.ext (F a)))) ≈ H.functor (ψl.ext (F a)) • H.functor (φr.ext (I (H (F a)))) := Setoid.trans (respectsSetoid H h₃) (respectsComp H (φr.ext (I (H (F a)))) (ψl.ext (F a)));
       let h₅ : H.functor (F.functor (φl.ext a • G.functor (ψl.ext (F a)))) ≈ ψr.ext (H (F a)) • H.functor (φr.ext (I (H (F a))))         := substCompLeft' (d (F a)) h₄;
       let h₆ := Setoid.trans (respectsSetoid H (respectsSetoid F (transDef φl ψl a))) h₅;
       let h₇ := Setoid.trans h₆ (Setoid.symm (transDef ψr φr (H (F a))));
       h₇

end Compat

-- Given equivalences of functors, we can ask whether two instances of `LeftInv` are equivalent.

def Equiv {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T S}
          (φ : F₁ ≃ F₂) (ψ : G₁ ≃ G₂)
          (χ₁ : LeftInv F₁ G₁) (χ₂ : LeftInv F₂ G₂) :=
χ₁ ≈ χ₂ • compFun.congrArg φ ψ

namespace Equiv

theorem refl  {F : StructureFunctor S T} {G : StructureFunctor T S} (χ : LeftInv F G) :
  Equiv (FunctorEquiv.refl F) (FunctorEquiv.refl G) χ χ :=
Setoid.symm (rightCancelId (compFun.congrArg.respectsId F G))

theorem refl' {F : StructureFunctor S T} {G : StructureFunctor T S} {χ₁ χ₂ : LeftInv F G} (h : χ₁ ≈ χ₂) :
  Equiv (FunctorEquiv.refl F) (FunctorEquiv.refl G) χ₁ χ₂ :=
substCompLeft' h (refl χ₁)

theorem symm  {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T S}
              {φ : F₁ ≃ F₂} {ψ : G₁ ≃ G₂}
              {χ₁ : LeftInv F₁ G₁} {χ₂ : LeftInv F₂ G₂}
              (e : Equiv φ ψ χ₁ χ₂) :
  Equiv (FunctorEquiv.symm φ) (FunctorEquiv.symm ψ) χ₂ χ₁ :=
let h₁ := (rightMulInv χ₂ χ₁ (compFun.congrArg φ ψ)).mp (Setoid.symm e);
substCompRight' (Setoid.symm (compFun.congrArg.respectsInv φ ψ)) h₁

theorem trans {F₁ F₂ F₃ : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T S}
              {φ₁ : F₁ ≃ F₂} {φ₂ : F₂ ≃ F₃} {ψ₁ : G₁ ≃ G₂} {ψ₂ : G₂ ≃ G₃}
              {χ₁ : LeftInv F₁ G₁} {χ₂ : LeftInv F₂ G₂} {χ₃ : LeftInv F₃ G₃}
              (e : Equiv φ₁ ψ₁ χ₁ χ₂) (f : Equiv φ₂ ψ₂ χ₂ χ₃) :
  Equiv (FunctorEquiv.trans φ₁ φ₂) (FunctorEquiv.trans ψ₁ ψ₂) χ₁ χ₃ :=
let h₁ := applyAssocRight' (substCompLeft' f e);
substCompRight' (Setoid.symm (compFun.congrArg.respectsComp φ₁ φ₂ ψ₁ ψ₂)) h₁

end Equiv

end LeftInv



-- A type class asserting that two functors are inverse to each other. In addition to the condition that
-- the inverse functor is left-inverse and right-inverse, we also add compatibility conditions on these
-- two functor equivalences for both `F` and `G`. This is essentially the same as requiring the functors
-- to be adjoint.

class IsInverse (F : StructureFunctor S T) (G : StructureFunctor T S) :=
(leftInv  : LeftInv F G)
(rightInv : LeftInv G F)
(lrCompat : LeftInv.Compat leftInv rightInv)
(rlCompat : LeftInv.Compat rightInv leftInv)

namespace IsInverse

def refl  (S : Structure) :
  IsInverse (@idFun S) (@idFun S) :=
{ leftInv  := LeftInv.refl        S,
  rightInv := LeftInv.refl        S,
  lrCompat := LeftInv.Compat.refl S,
  rlCompat := LeftInv.Compat.refl S }

def symm  {F : StructureFunctor S T} {G : StructureFunctor T S}
          (e : IsInverse F G) :
  IsInverse G F :=
{ leftInv  := e.rightInv,
  rightInv := e.leftInv,
  lrCompat := e.rlCompat,
  rlCompat := e.lrCompat }

def trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
          (e : IsInverse F G) (f : IsInverse H I) :
  IsInverse (H ⊙ F) (G ⊙ I) :=
{ leftInv  := LeftInv.trans        e.leftInv  f.leftInv,
  rightInv := LeftInv.trans        f.rightInv e.rightInv,
  lrCompat := LeftInv.Compat.trans e.lrCompat f.lrCompat,
  rlCompat := LeftInv.Compat.trans f.rlCompat e.rlCompat }

theorem symm_symm {F : StructureFunctor S T} {G : StructureFunctor T S} (e : IsInverse F G) : symm (symm e) = e :=
match e with
| ⟨_, _, _, _⟩ => rfl 

end IsInverse



-- A functor between instance structures is actually just a function.

def congrArgFunctor {α : Sort u} {β : Sort v} (f : α → β) :
  @GeneralizedFunctor α (instanceStructure α) (instanceStructure β) id f :=
{ mapEquiv  := congrArg f,
  isFunctor := propFunctor }

def InstanceStructureFunctor (α β : Sort u) := StructureFunctor (instanceStructure α) (instanceStructure β)

def instanceStructureFunctor {α β : Sort u} (f : α → β) : InstanceStructureFunctor α β :=
{ map     := f,
  functor := congrArgFunctor f }



-- If we have a function `F` and an equivalent functor `G`, we can turn `F` into a functor as well.

def proxyFunctor {S T : Structure} (F : S → T) (G : StructureFunctor S T) (φ : DependentEquiv F G.map) :
  StructureFunctor S T :=
{ map     := F,
  functor := comp.genFun G.functor (DependentEquiv.transport.invFunctor φ) }

end StructureFunctor

open StructureFunctor



-- Based on the definition of a functor between two structures, we can define equivalence of two
-- structures similarly to equivalence of types in mathlib.

structure StructureEquiv (S T : Structure) where
(toFun  : StructureFunctor S T)
(invFun : StructureFunctor T S)
(isInv  : IsInverse toFun invFun)

namespace StructureEquiv

def refl  (S     : Structure)                                                   : StructureEquiv S S :=
{ toFun  := idFun,
  invFun := idFun,
  isInv  := IsInverse.refl  S }

def symm  {S T   : Structure} (e : StructureEquiv S T)                          : StructureEquiv T S :=
{ toFun  := e.invFun,
  invFun := e.toFun,
  isInv  := IsInverse.symm  e.isInv }

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) : StructureEquiv S U :=
{ toFun  := f.toFun  ⊙ e.toFun,
  invFun := e.invFun ⊙ f.invFun,
  isInv  := IsInverse.trans e.isInv f.isInv }

theorem symm_symm {S T : Structure} (e : StructureEquiv S T) : symm (symm e) = e :=
match e with
| ⟨toFun, invFun, isInv⟩ => IsInverse.symm_symm isInv ▸ rfl 



-- We can compare two instances of `StructureEquiv` by comparing `toFun` and `invFun` and then dependently
-- comparing `leftInv` and `rightInv`. That turns `StructureEquiv` into a structure.

structure EquivEquiv {S T : Structure} (e f : StructureEquiv S T) where
(toFunEquiv    : e.toFun  ≃ f.toFun)
(invFunEquiv   : e.invFun ≃ f.invFun)
(leftInvEquiv  : LeftInv.Equiv toFunEquiv  invFunEquiv e.isInv.leftInv  f.isInv.leftInv)
(rightInvEquiv : LeftInv.Equiv invFunEquiv toFunEquiv  e.isInv.rightInv f.isInv.rightInv)

namespace EquivEquiv

variable {S T : Structure}

def refl  (e     : StructureEquiv S T)                                           : EquivEquiv e e :=
{ toFunEquiv    := IsEquivalence.refl  e.toFun,
  invFunEquiv   := IsEquivalence.refl  e.invFun,
  leftInvEquiv  := LeftInv.Equiv.refl  e.isInv.leftInv,
  rightInvEquiv := LeftInv.Equiv.refl  e.isInv.rightInv }

def symm  {e f   : StructureEquiv S T} (φ : EquivEquiv e f)                      : EquivEquiv f e :=
{ toFunEquiv    := IsEquivalence.symm  φ.toFunEquiv,
  invFunEquiv   := IsEquivalence.symm  φ.invFunEquiv,
  leftInvEquiv  := LeftInv.Equiv.symm  φ.leftInvEquiv,
  rightInvEquiv := LeftInv.Equiv.symm  φ.rightInvEquiv }

def trans {e f g : StructureEquiv S T} (φ : EquivEquiv e f) (ψ : EquivEquiv f g) : EquivEquiv e g :=
{ toFunEquiv    := IsEquivalence.trans φ.toFunEquiv    ψ.toFunEquiv,
  invFunEquiv   := IsEquivalence.trans φ.invFunEquiv   ψ.invFunEquiv,
  leftInvEquiv  := LeftInv.Equiv.trans φ.leftInvEquiv  ψ.leftInvEquiv,
  rightInvEquiv := LeftInv.Equiv.trans φ.rightInvEquiv ψ.rightInvEquiv }



-- For equivalence of `EquivEquiv`, we can reuse the equivalence of `StructureProduct`, as `leftInvEquiv`
-- and `rightInvEquiv` are just proofs.

@[reducible] def FunProd (S T : Structure) :=
  StructureProduct (functorStructure S T) (functorStructure T S)

def funProd {S T : Structure} (e : StructureEquiv S T) : FunProd S T :=
⟨e.toFun, e.invFun⟩

def funEquivProd {e f : StructureEquiv S T} (φ : EquivEquiv e f) :
  funProd e ≃ funProd f :=
⟨φ.toFunEquiv, φ.invFunEquiv⟩

def EquivEquivEquiv {e f : StructureEquiv S T} (φ ψ : EquivEquiv e f) :=
funEquivProd φ ≈ funEquivProd ψ

namespace EquivEquivEquiv

variable {e f : StructureEquiv S T}

theorem refl  (φ     : EquivEquiv e f)                                                     : EquivEquivEquiv φ φ :=
StructureProduct.ProductEquiv.EquivEquiv.refl  (funEquivProd φ)

theorem symm  {φ ψ   : EquivEquiv e f} (h : EquivEquivEquiv φ ψ)                           : EquivEquivEquiv ψ φ :=
StructureProduct.ProductEquiv.EquivEquiv.symm  h

theorem trans {φ ψ χ : EquivEquiv e f} (h : EquivEquivEquiv φ ψ) (i : EquivEquivEquiv ψ χ) : EquivEquivEquiv φ χ :=
StructureProduct.ProductEquiv.EquivEquiv.trans h i

instance equivEquivSetoid : Setoid (EquivEquiv e f) := ⟨EquivEquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquivEquiv

def equivEquiv (e f : StructureEquiv S T) : BundledSetoid := ⟨EquivEquiv e f⟩

instance equivHasIso : HasIsomorphisms (@equivEquiv S T) :=
{ comp         := trans,
  congrArgComp := λ {e f g φ₁ φ₂ ψ₁ ψ₂} (hφ : EquivEquivEquiv φ₁ φ₂) (hψ : EquivEquivEquiv ψ₁ ψ₂) =>
                  HasStructure.congrArgComp hφ hψ,
  assoc        := λ φ ψ χ => HasStructure.assoc    (funEquivProd φ) (funEquivProd ψ) (funEquivProd χ),
  id           := refl,
  leftId       := λ φ     => HasStructure.leftId   (funEquivProd φ),
  rightId      := λ φ     => HasStructure.rightId  (funEquivProd φ),
  inv          := symm,
  congrArgInv  := λ {e f φ₁ φ₂} (hφ  : EquivEquivEquiv φ₁ φ₂) =>
                  HasStructure.congrArgInv hφ,
  leftInv      := λ φ     => HasStructure.leftInv  (funEquivProd φ),
  rightInv     := λ φ     => HasStructure.rightInv (funEquivProd φ),
  invInv       := λ φ     => HasStructure.invInv   (funEquivProd φ),
  compInv      := λ φ ψ   => HasStructure.compInv  (funEquivProd φ) (funEquivProd ψ),
  idInv        := λ e     => HasStructure.idInv    (funProd e) }

end EquivEquiv

instance equivHasStructure (S T : Structure) : HasStructure (StructureEquiv S T) := ⟨EquivEquiv.equivEquiv⟩
def equivStructure (S T : Structure) : Structure := ⟨StructureEquiv S T⟩



def toFunProj (S T : Structure) : StructureFunctor (equivStructure S T) (functorStructure S T) :=
{ map     := StructureEquiv.toFun,
  functor := { mapEquiv  := EquivEquiv.toFunEquiv,
               isFunctor := { respectsSetoid := And.left,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ.toFunEquiv • φ.toFunEquiv),
                              respectsId     := λ e   => Setoid.refl (id__ (S := functorStructure S T) e.toFun),
                              respectsInv    := λ φ   => Setoid.refl (φ.toFunEquiv)⁻¹ } } }

def invFunProj (S T : Structure) : StructureFunctor (equivStructure S T) (functorStructure T S) :=
{ map     := StructureEquiv.invFun,
  functor := { mapEquiv  := EquivEquiv.invFunEquiv,
               isFunctor := { respectsSetoid := And.right,
                              respectsComp   := λ φ ψ => Setoid.refl (ψ.invFunEquiv • φ.invFunEquiv),
                              respectsId     := λ e   => Setoid.refl (id__ (S := functorStructure T S) e.invFun),
                              respectsInv    := λ φ   => Setoid.refl (φ.invFunEquiv)⁻¹ } } }



def congrArgComp {S T U : Structure} {e₁ e₂ : StructureEquiv S T} {f₁ f₂ : StructureEquiv T U} (he : e₁ ≃ e₂) (hf : f₁ ≃ f₂) :
  trans e₁ f₁ ≃ trans e₂ f₂ :=
{ toFunEquiv    := compFun.congrArg he.toFunEquiv  hf.toFunEquiv,
  invFunEquiv   := compFun.congrArg hf.invFunEquiv he.invFunEquiv,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

theorem assocLeftInvEquiv {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  LeftInv.Equiv (FunctorEquiv.refl (g.toFun  ⊙ f.toFun  ⊙ e.toFun))
                (FunctorEquiv.refl (e.invFun ⊙ f.invFun ⊙ g.invFun))
                (IsInverse.trans (IsInverse.trans e.isInv f.isInv) g.isInv).leftInv
                (IsInverse.trans e.isInv (IsInverse.trans f.isInv g.isInv)).leftInv :=
LeftInv.Equiv.refl' (LeftInv.transAssoc e.isInv.leftInv f.isInv.leftInv g.isInv.leftInv)

theorem assocRightInvEquiv {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  LeftInv.Equiv (FunctorEquiv.refl (e.invFun ⊙ f.invFun ⊙ g.invFun))
                (FunctorEquiv.refl (g.toFun  ⊙ f.toFun  ⊙ e.toFun))
                (IsInverse.trans (IsInverse.trans e.isInv f.isInv) g.isInv).rightInv
                (IsInverse.trans e.isInv (IsInverse.trans f.isInv g.isInv)).rightInv :=
LeftInv.Equiv.refl' (Setoid.symm (LeftInv.transAssoc g.isInv.rightInv f.isInv.rightInv e.isInv.rightInv))

def assoc {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  trans (trans e f) g ≃ trans e (trans f g) :=
{ toFunEquiv    := compFun.assoc e.toFun  f.toFun  g.toFun,
  invFunEquiv   := compFun.assoc g.invFun f.invFun e.invFun,
  leftInvEquiv  := assocLeftInvEquiv  e f g,
  rightInvEquiv := assocRightInvEquiv e f g }

theorem leftIdLeftInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv (idFun.leftId e.toFun)
                (idFun.leftId e.invFun)
                (IsInverse.trans e.isInv (IsInverse.refl T)).leftInv
                e.isInv.leftInv :=
let h₁ := LeftInv.transRefl e.isInv.leftInv;
λ a => let h₂ := h₁ a;
       sorry

theorem rightIdLeftInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv (idFun.rightId e.toFun)
                (idFun.rightId e.invFun)
                (IsInverse.trans (IsInverse.refl S) e.isInv).leftInv
                e.isInv.leftInv :=
sorry

def leftId  {S T : Structure} (e : StructureEquiv S T) : trans e (refl T) ≃ e :=
{ toFunEquiv    := idFun.leftId e.toFun,
  invFunEquiv   := idFun.leftId e.invFun,
  leftInvEquiv  := leftIdLeftInvEquiv  e,
  rightInvEquiv := rightIdLeftInvEquiv (symm e) }

def rightId {S T : Structure} (e : StructureEquiv S T) : trans (refl S) e ≃ e :=
{ toFunEquiv    := idFun.rightId e.toFun,
  invFunEquiv   := idFun.rightId e.invFun,
  leftInvEquiv  := rightIdLeftInvEquiv e,
  rightInvEquiv := leftIdLeftInvEquiv  (symm e) }

def congrArgInv {S T : Structure} {e₁ e₂ : StructureEquiv S T} (he : e₁ ≃ e₂) :
  symm e₁ ≃ symm e₂ :=
{ toFunEquiv    := he.invFunEquiv,
  invFunEquiv   := he.toFunEquiv,
  leftInvEquiv  := he.rightInvEquiv,
  rightInvEquiv := he.leftInvEquiv }

theorem leftInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv e.isInv.leftInv e.isInv.leftInv (IsInverse.trans e.isInv (IsInverse.symm e.isInv)).leftInv (IsInverse.refl S).leftInv :=
let h₁ : LeftInv.trans e.isInv.leftInv e.isInv.rightInv ≈ compFun.congrArg' e.isInv.leftInv e.isInv.leftInv :=
    λ a => Setoid.trans (LeftInv.transDef e.isInv.leftInv e.isInv.rightInv a) (congrArgCompRight (respectsSetoid e.invFun (Setoid.symm (e.isInv.lrCompat a))));
let h₂ := Setoid.trans h₁ (Setoid.symm (compFun.congrArg.wd e.isInv.leftInv e.isInv.leftInv));
Setoid.trans h₂ (Setoid.symm (HasStructure.leftId (compFun.congrArg e.isInv.leftInv e.isInv.leftInv)))

def leftInv'  {S T : Structure} (e : StructureEquiv S T) : trans e (symm e) ≃ refl S :=
{ toFunEquiv    := e.isInv.leftInv,
  invFunEquiv   := e.isInv.leftInv,
  leftInvEquiv  := leftInvEquiv e,
  rightInvEquiv := leftInvEquiv e }

theorem rightInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv e.isInv.rightInv e.isInv.rightInv (IsInverse.trans (IsInverse.symm e.isInv) e.isInv).rightInv (IsInverse.refl T).rightInv :=
let h₁ : LeftInv.trans e.isInv.rightInv e.isInv.leftInv ≈ compFun.congrArg' e.isInv.rightInv e.isInv.rightInv :=
    λ a => Setoid.trans (LeftInv.transDef e.isInv.rightInv e.isInv.leftInv a) (congrArgCompRight (respectsSetoid e.toFun (Setoid.symm (e.isInv.rlCompat a))));
let h₂ := Setoid.trans h₁ (Setoid.symm (compFun.congrArg.wd e.isInv.rightInv e.isInv.rightInv));
Setoid.trans h₂ (Setoid.symm (HasStructure.leftId (compFun.congrArg e.isInv.rightInv e.isInv.rightInv)))

def rightInv' {S T : Structure} (e : StructureEquiv S T) : trans (symm e) e ≃ refl T :=
{ toFunEquiv    := e.isInv.rightInv,
  invFunEquiv   := e.isInv.rightInv,
  leftInvEquiv  := rightInvEquiv e,
  rightInvEquiv := rightInvEquiv e }

def invInv {S T : Structure} (e : StructureEquiv S T) : symm (symm e) ≃ e :=
symm_symm e ▸ EquivEquiv.refl e

def compInv {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) :
  symm (trans e f) ≃ trans (symm f) (symm e) :=
EquivEquiv.refl (symm (trans e f))

def idInv (S : Structure) : symm (refl S) ≃ refl S :=
EquivEquiv.refl (refl S)



-- When using `StructureEquiv` as an equivalence within the `universeStructure` we wish to define, we
-- need to truncate `EquivEquiv` to its setoid structure.
--
-- There are a lot of alternative places we could choose for this truncation. E.g. we could first define a
-- notion of a 2-structure, then define a 2-structure of (1-)structures, and then truncate that
-- 2-structure. If we additionally defined functors of those 2-structures, we could eliminate the setoid
-- truncations in `AbstractPiSigma.lean`. In particular, this would make Π and Σ structures fully
-- equivalent to functor and pair (1-)structures if they are independent. However, this would come at a
-- cost of essentially duplicating the basic definitions -- potentially endlessly, even.

instance equivIsSetoid (S T : Structure) : Setoid (StructureEquiv S T) := structureToSetoid (equivStructure S T)

def structureEquiv (S T : Structure) : BundledSetoid := ⟨StructureEquiv S T⟩

def congrArgCompS {S T U : Structure} {e₁ e₂ : StructureEquiv S T} {f₁ f₂ : StructureEquiv T U} :
  e₁ ≈ e₂ → f₁ ≈ f₂ → trans e₁ f₁ ≈ trans e₂ f₂ :=
λ ⟨he⟩ ⟨hf⟩ => ⟨congrArgComp he hf⟩

def assocS {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  trans (trans e f) g ≈ trans e (trans f g) :=
⟨assoc e f g⟩

def leftIdS  {S T : Structure} (e : StructureEquiv S T) : trans e (refl T) ≈ e := ⟨leftId  e⟩
def rightIdS {S T : Structure} (e : StructureEquiv S T) : trans (refl S) e ≈ e := ⟨rightId e⟩

def congrArgInvS {S T : Structure} {e₁ e₂ : StructureEquiv S T} : e₁ ≈ e₂ → symm e₁ ≈ symm e₂ :=
λ ⟨he⟩ => ⟨congrArgInv he⟩

def leftInvS  {S T : Structure} (e : StructureEquiv S T) : trans e (symm e) ≈ refl S := ⟨leftInv'  e⟩
def rightInvS {S T : Structure} (e : StructureEquiv S T) : trans (symm e) e ≈ refl T := ⟨rightInv' e⟩

def invInvS {S T : Structure} (e : StructureEquiv S T) : symm (symm e) ≈ e := ⟨invInv e⟩

def compInvS {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) :
  symm (trans e f) ≈ trans (symm f) (symm e) :=
⟨compInv e f⟩

def idInvS (S : Structure) : symm (refl S) ≈ refl S := ⟨idInv S⟩

instance equivHasIso : HasIsomorphisms structureEquiv :=
{ comp         := trans,
  congrArgComp := congrArgCompS,
  assoc        := assocS,
  id           := refl,
  leftId       := leftIdS,
  rightId      := rightIdS,
  inv          := symm,
  congrArgInv  := congrArgInvS,
  leftInv      := leftInvS,
  rightInv     := rightInvS,
  invInv       := invInvS,
  compInv      := compInvS,
  idInv        := idInvS }

end StructureEquiv



instance structureHasStructure : HasStructure Structure := ⟨StructureEquiv.structureEquiv⟩
instance structureHasEquivalence : HasEquivalence Structure Structure := ⟨StructureEquiv.structureEquiv⟩
instance structureEquivIsType : IsType (HasEquivalence.γ Structure Structure) := bundledSetoidIsType
instance (S T : Structure) : Setoid (IsType.type (S ≃ T)) := bundledSetoid (StructureEquiv.structureEquiv S T)
instance (S T : Structure) : HasStructure (IsType.type (S ≃ T)) := StructureEquiv.equivHasStructure S T

instance : HasComp         (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasComp'
instance : HasComposition  (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasCmp'
instance : HasId           (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasId'
instance : HasMorphisms    (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasMor'
instance : HasInv          (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasInv'
instance : HasIsomorphisms (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasIso'
instance : IsEquivalence   (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.isEquiv'



-- If we have a `StructureEquiv S T`, we can ask whether it maps `a : S` to `b : T`. This is similar to
-- an equivalence. It corresponds to a "dependent equivalence" or "pathover" in HoTT.

def InstanceEquiv {S T : Structure} (e : S ≃ T) (a : S) (b : T) := e.toFun a ≃ b

namespace InstanceEquiv

notation:25 a:26 " ≃[" e:0 "] " b:26 => InstanceEquiv e a b

def refl' (S     : Structure)                         {a b : S} (h : a ≃ b)   :
  a ≃[id_ S] b :=
h

def refl  (S     : Structure)                         (a : S)                 :
  a ≃[id_ S] a :=
refl' S (IsEquivalence.refl a)

def symm  {S T   : Structure} (e : S ≃ T)             (a : S) (b : T)         :
  a ≃[e] b → b ≃[e⁻¹] a :=
λ φ => IsEquivalence.trans (IsEquivalence.symm (congrArgMap e.invFun φ)) (e.isInv.leftInv.ext a)

def trans {S T U : Structure} (e : S ≃ T) (f : T ≃ U) (a : S) (b : T) (c : U) :
  a ≃[e] b → b ≃[f] c → a ≃[f • e] c :=
λ φ ψ => IsEquivalence.trans (congrArgMap f.toFun φ) ψ

-- TODO: We should probably replace `→` with `≃` here.
def congrArgEquiv {S T : Structure} {e₁ e₂ : S ≃ T} (φ : e₁ ≃ e₂) (a : S) (b : T) :
  a ≃[e₁] b → a ≃[e₂] b :=
IsEquivalence.trans (IsEquivalence.symm (φ.toFunEquiv.ext a))

end InstanceEquiv



-- Using `StructureEquiv`, we can build a "universe" structure where the objects are structures. This is
-- the same as the groupoid of lower-level groupoids.

def universeStructure : Structure := ⟨Structure⟩

instance : IsType (IsType.type universeStructure) := structureIsType
