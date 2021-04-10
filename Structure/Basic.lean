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
--   * Replace most greek letters with latin letters.
--   * Be more consistent with `e` vs. `φ` etc.
--   * Rename `F`, `G` etc. in generalized functors to e.g. `f`, `g`.
--   * Rename `U` to `α`, `V` to `β`, and `A` to `ω`.
-- * Rename `FF` to `mapEquiv`.
-- * Use snake case for theorem names.



import mathlib4_experiments.CoreExt
import mathlib4_experiments.Data.Notation



set_option autoBoundImplicitLocal false

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

class HasStructure (U : Sort u) where
(M : GeneralizedRelation U)
[h : HasIsomorphisms M]

namespace HasStructure

variable {U : Sort u} [h : HasStructure U]

instance hasEquivalence : HasEquivalence U U := ⟨h.M⟩

instance equivalenceIsType : IsType (HasEquivalence.γ U U) := bundledSetoidIsType
instance (α β : U) : Setoid (IsType.type (α ≃ β)) := (h.M α β).s

instance hasComp : HasComp         (@HasEquivalence.Equiv U U hasEquivalence) := h.h.toHasComp
instance hasCmp  : HasComposition  (@HasEquivalence.Equiv U U hasEquivalence) := h.h.toHasComposition
instance hasId   : HasId           (@HasEquivalence.Equiv U U hasEquivalence) := h.h.toHasId
instance hasMor  : HasMorphisms    (@HasEquivalence.Equiv U U hasEquivalence) := h.h.toHasMorphisms
instance hasInv  : HasInv          (@HasEquivalence.Equiv U U hasEquivalence) := h.h.toHasInv
instance hasIso  : HasIsomorphisms (@HasEquivalence.Equiv U U hasEquivalence) := h.h
instance isEquiv : IsEquivalence   (@HasEquivalence.Equiv U U hasEquivalence) := isoEquiv (@HasEquivalence.Equiv U U hasEquivalence)

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
(U : Sort u)
[h : HasStructure U]

namespace Structure

instance structureIsType : IsType Structure := ⟨Structure.U⟩

def iso (S : Structure) : GeneralizedRelation (IsType.type S) := S.h.M

variable {S : Structure}

instance hasStructure : HasStructure (IsType.type S) := S.h

instance hasComp : HasComp         (iso S) := hasStructure.hasComp
instance hasCmp  : HasComposition  (iso S) := hasStructure.hasCmp
instance hasId   : HasId           (iso S) := hasStructure.hasId
instance hasMor  : HasMorphisms    (iso S) := hasStructure.hasMor
instance hasInv  : HasInv          (iso S) := hasStructure.hasInv
instance hasIso  : HasIsomorphisms (iso S) := hasStructure.hasIso
instance isEquiv : IsEquivalence   (iso S) := hasStructure.isEquiv

def id__ (α : S) : α ≃ α := id_ α
def id' {α : S} := id__ α

        theorem congrArgComp {α β γ   : S} {f₁ f₂ : α ≃ β} {g₁ g₂ : β ≃ γ}     : f₁ ≈ f₂ → g₁ ≈ g₂ → g₁ • f₁ ≈ g₂ • f₂ := hasIso.congrArgComp
        theorem assoc        {α β γ δ : S} (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h • (g • f) ≈ (h • g) • f             := hasIso.assoc    f g h
        theorem assoc'       {α β γ δ : S} (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : (h • g) • f ≈ h • (g • f)             := Setoid.symm (assoc f g h)
@[simp] theorem leftId       {α β     : S} (f : α ≃ β)                         : id' • f   ≈ f                         := hasIso.leftId   f
@[simp] theorem rightId      {α β     : S} (f : α ≃ β)                         : f • id'   ≈ f                         := hasIso.rightId  f
        theorem congrArgInv  {α β     : S} {f₁ f₂ : α ≃ β}                     : f₁ ≈ f₂ → f₁⁻¹ ≈ f₂⁻¹                 := hasIso.congrArgInv
@[simp] theorem leftInv      {α β     : S} (f : α ≃ β)                         : f⁻¹ • f   ≈ id'                       := hasIso.leftInv  f
@[simp] theorem rightInv     {α β     : S} (f : α ≃ β)                         : f • f⁻¹   ≈ id'                       := hasIso.rightInv f
@[simp] theorem invInv       {α β     : S} (f : α ≃ β)                         : (f⁻¹)⁻¹   ≈ f                         := hasIso.invInv   f
@[simp] theorem compInv      {α β γ   : S} (f : α ≃ β) (g : β ≃ γ)             : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹                 := hasIso.compInv  f g
@[simp] theorem idInv        (α       : S)                                     : (id_ α)⁻¹ ≈ id'                       := hasIso.idInv    α

theorem congrArgCompLeft  {α β γ : S} {f : α ≃ β} {g₁ g₂ : β ≃ γ} : g₁ ≈ g₂ → g₁ • f ≈ g₂ • f :=
λ h => congrArgComp (Setoid.refl f) h
theorem congrArgCompRight {α β γ : S} {f₁ f₂ : α ≃ β} {g : β ≃ γ} : f₁ ≈ f₂ → g • f₁ ≈ g • f₂ :=
λ h => congrArgComp h (Setoid.refl g)

theorem substCompLeft   {α β γ : S} {f : α ≃ β} {g₁ g₂ : β ≃ γ} {e : α ≃ γ} : g₁ ≈ g₂ → g₂ • f ≈ e → g₁ • f ≈ e :=
λ h₁ h₂ => Setoid.trans (congrArgCompLeft h₁) h₂
theorem substCompLeft'  {α β γ : S} {f : α ≃ β} {g₁ g₂ : β ≃ γ} {e : α ≃ γ} : g₁ ≈ g₂ → e ≈ g₁ • f → e ≈ g₂ • f :=
λ h₁ h₂ => Setoid.trans h₂ (congrArgCompLeft h₁)

theorem substCompRight  {α β γ : S} {f₁ f₂ : α ≃ β} {g : β ≃ γ} {e : α ≃ γ} : f₁ ≈ f₂ → g • f₂ ≈ e → g • f₁ ≈ e :=
λ h₁ h₂ => Setoid.trans (congrArgCompRight h₁) h₂
theorem substCompRight' {α β γ : S} {f₁ f₂ : α ≃ β} {g : β ≃ γ} {e : α ≃ γ} : f₁ ≈ f₂ → e ≈ g • f₁ → e ≈ g • f₂ :=
λ h₁ h₂ => Setoid.trans h₂ (congrArgCompRight h₁)

theorem substInv  {α β : S} {f₁ f₂ : α ≃ β} {e : β ≃ α} : f₁ ≈ f₂ → f₂⁻¹ ≈ e → f₁⁻¹ ≈ e :=
λ h₁ h₂ => Setoid.trans (congrArgInv h₁) h₂
theorem substInv' {α β : S} {f₁ f₂ : α ≃ β} {e : β ≃ α} : f₁ ≈ f₂ → e ≈ f₁⁻¹ → e ≈ f₂⁻¹ :=
λ h₁ h₂ => Setoid.symm (substInv (Setoid.symm h₁) (Setoid.symm h₂))

theorem leftCancelId  {α β : S} {f : α ≃ β} {e : β ≃ β} : e ≈ id' → e • f ≈ f :=
λ h => substCompLeft  h (leftId  f)
theorem rightCancelId {α β : S} {f : α ≃ β} {e : α ≃ α} : e ≈ id' → f • e ≈ f :=
λ h => substCompRight h (rightId f)

theorem applyAssocLeft   {α β γ δ : S} {f : α ≃ β} {g : β ≃ γ} {h : γ ≃ δ} {e : α ≃ δ} :
  h • (g • f) ≈ e → (h • g) • f ≈ e :=
λ h₁ => Setoid.trans (assoc' f g h) h₁
theorem applyAssocLeft'  {α β γ δ : S} {f : α ≃ β} {g : β ≃ γ} {h : γ ≃ δ} {e : α ≃ δ} :
  (h • g) • f ≈ e → h • (g • f) ≈ e :=
λ h₁ => Setoid.trans (assoc f g h) h₁
theorem applyAssocRight  {α β γ δ : S} {f : α ≃ β} {g : β ≃ γ} {h : γ ≃ δ} {e : α ≃ δ} :
  e ≈ h • (g • f) → e ≈ (h • g) • f :=
λ h₁ => Setoid.trans h₁ (assoc f g h)
theorem applyAssocRight' {α β γ δ : S} {f : α ≃ β} {g : β ≃ γ} {h : γ ≃ δ} {e : α ≃ δ} :
  e ≈ (h • g) • f → e ≈ h • (g • f) :=
λ h₁ => Setoid.trans h₁ (assoc' f g h)

theorem applyAssoc  {α β₁ β₂ γ₁ γ₂ δ : S} {f₁ : α ≃ β₁} {f₂ : α ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ δ} {h₂ : γ₂ ≃ δ} :
  h₁ • (g₁ • f₁) ≈ h₂ • (g₂ • f₂) → (h₁ • g₁) • f₁ ≈ (h₂ • g₂) • f₂ :=
λ h => applyAssocRight  (applyAssocLeft  h)
theorem applyAssoc' {α β₁ β₂ γ₁ γ₂ δ : S} {f₁ : α ≃ β₁} {f₂ : α ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ δ} {h₂ : γ₂ ≃ δ} :
  (h₁ • g₁) • f₁ ≈ (h₂ • g₂) • f₂ → h₁ • (g₁ • f₁) ≈ h₂ • (g₂ • f₂) :=
λ h => applyAssocRight' (applyAssocLeft' h)

@[simp] theorem leftCancel'     {α β γ : S} (f : α ≃ β) (g : β ≃ γ) : (g⁻¹ • g) • f ≈ f := leftCancelId  (leftInv  g)
@[simp] theorem leftCancel      {α β γ : S} (f : α ≃ β) (g : β ≃ γ) : g⁻¹ • (g • f) ≈ f := applyAssocLeft' (leftCancel'     f g)
@[simp] theorem leftCancelInv'  {α β γ : S} (f : α ≃ β) (g : γ ≃ β) : (g • g⁻¹) • f ≈ f := leftCancelId  (rightInv g)
@[simp] theorem leftCancelInv   {α β γ : S} (f : α ≃ β) (g : γ ≃ β) : g • (g⁻¹ • f) ≈ f := applyAssocLeft' (leftCancelInv'  f g)
@[simp] theorem rightCancel'    {α β γ : S} (f : α ≃ β) (g : γ ≃ α) : f • (g • g⁻¹) ≈ f := rightCancelId (rightInv g)
@[simp] theorem rightCancel     {α β γ : S} (f : α ≃ β) (g : γ ≃ α) : (f • g) • g⁻¹ ≈ f := applyAssocLeft  (rightCancel'    f g)
@[simp] theorem rightCancelInv' {α β γ : S} (f : α ≃ β) (g : α ≃ γ) : f • (g⁻¹ • g) ≈ f := rightCancelId (leftInv  g)
@[simp] theorem rightCancelInv  {α β γ : S} (f : α ≃ β) (g : α ≃ γ) : (f • g⁻¹) • g ≈ f := applyAssocLeft  (rightCancelInv' f g)

theorem leftMulInv  {α β γ : S} (f₁ : α ≃ β) (f₂ : α ≃ γ) (g : β ≃ γ) : g • f₁ ≈ f₂ ↔ f₁ ≈ g⁻¹ • f₂ :=
⟨λ h => substCompRight' h (Setoid.symm (leftCancel f₁ g)), λ h => substCompRight h (leftCancelInv f₂ g)⟩
theorem leftMulInv' {α β γ : S} (f₁ : α ≃ β) (f₂ : α ≃ γ) (g : γ ≃ β) : g⁻¹ • f₁ ≈ f₂ ↔ f₁ ≈ g • f₂ :=
⟨λ h => substCompRight' h (Setoid.symm (leftCancelInv f₁ g)), λ h => substCompRight h (leftCancel f₂ g)⟩

@[simp] theorem leftMul {α β γ : S} (f₁ f₂ : α ≃ β) (g : β ≃ γ) : g • f₁ ≈ g • f₂ ↔ f₁ ≈ f₂ :=
⟨λ h => Setoid.trans ((leftMulInv f₁ (g • f₂) g).mp h) (leftCancel f₂ g), congrArgCompRight⟩

theorem rightMulInv  {α β γ : S} (f₁ : α ≃ γ) (f₂ : β ≃ γ) (g : β ≃ α) : f₁ • g ≈ f₂ ↔ f₁ ≈ f₂ • g⁻¹ :=
⟨λ h => substCompLeft' h (Setoid.symm (rightCancel f₁ g)), λ h => substCompLeft h (rightCancelInv f₂ g)⟩
theorem rightMulInv' {α β γ : S} (f₁ : α ≃ γ) (f₂ : β ≃ γ) (g : α ≃ β) : f₁ • g⁻¹ ≈ f₂ ↔ f₁ ≈ f₂ • g :=
⟨λ h => substCompLeft' h (Setoid.symm (rightCancelInv f₁ g)), λ h => substCompLeft h (rightCancel f₂ g)⟩

@[simp] theorem rightMul {α β γ : S} (f₁ f₂ : α ≃ β) (g : γ ≃ α) : f₁ • g ≈ f₂ • g ↔ f₁ ≈ f₂ :=
⟨λ h => Setoid.trans ((rightMulInv f₁ (f₂ • g) g).mp h) (rightCancel f₂ g), congrArgCompLeft⟩

theorem eqInvIffInvEq {α β : S} (f : α ≃ β) (g : β ≃ α) : f ≈ g⁻¹ ↔ f⁻¹ ≈ g :=
⟨λ h => substInv h (invInv g), λ h => substInv' h (Setoid.symm (invInv f))⟩

@[simp] theorem eqIffEqInv {α β : S} (f₁ f₂ : α ≃ β) : f₁⁻¹ ≈ f₂⁻¹ ↔ f₁ ≈ f₂ :=
⟨λ h => Setoid.trans ((eqInvIffInvEq f₁ f₂⁻¹).mpr h) (invInv f₂), congrArgInv⟩

@[simp] theorem leftRightMul {α β γ δ : S} (f₁ : α ≃ β) (f₂ : α ≃ γ) (g₁ : β ≃ δ) (g₂ : γ ≃ δ) :
  g₂⁻¹ • g₁ ≈ f₂ • f₁⁻¹ ↔ g₁ • f₁ ≈ g₂ • f₂ :=
⟨λ h => let h₁ := (rightMulInv (g₂⁻¹ • g₁) f₂ f₁).mpr h;
        let h₂ := applyAssocLeft' h₁;
        (leftMulInv' (g₁ • f₁) f₂ g₂).mp h₂,
 λ h => let h₁ := (rightMulInv g₁ (g₂ • f₂) f₁).mp h;
        let h₂ := applyAssocRight' h₁;
        (leftMulInv' g₁ (f₂ • f₁⁻¹) g₂).mpr h₂⟩

theorem swapInv  {α β γ δ : S} (f₁ : α ≃ β) (f₂ : γ ≃ δ) (g₁ : δ ≃ β) (g₂ : γ ≃ α) :
  g₁⁻¹ • f₁ ≈ f₂ • g₂⁻¹ → f₁⁻¹ • g₁ ≈ g₂ • f₂⁻¹ :=
λ h => (leftRightMul f₂ g₂ g₁ f₁).mpr (Setoid.symm ((leftRightMul g₂ f₂ f₁ g₁).mp h))

theorem swapInv' {α β γ δ : S} (f₁ : α ≃ β) (f₂ : γ ≃ δ) (g₁ : δ ≃ β) (g₂ : γ ≃ α) :
  f₂ • g₂⁻¹ ≈ g₁⁻¹ • f₁ → g₂ • f₂⁻¹ ≈ f₁⁻¹ • g₁ :=
λ h => Setoid.symm (swapInv f₁ f₂ g₁ g₂ (Setoid.symm h))

end Structure

open Structure

def defaultStructure (U : Sort u) [h : HasStructure U] : Structure := ⟨U⟩
def instanceStructure (α : Sort u) := @defaultStructure α (typeHasStructure α)
def setoidInstanceStructure (α : Sort u) [s : Setoid α] := @defaultStructure α (setoidHasStructure α)
def bundledSetoidStructure (S : BundledSetoid) := setoidInstanceStructure (IsType.type S)



-- Since each equivalence/isomorphism of a structure is a bundled setoid, we can treat it as a
-- structure as well. This partially recovers the inductive definition of a structure as an ∞-groupoid.

def isoStructure {S : Structure} (α β : S) := bundledSetoidStructure (iso S α β)



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

def SetoidEquiv (α β : S) := Nonempty (IsType.type (α ≃ β))
def toSetoidEquiv {α β : S} (e : α ≃ β) : SetoidEquiv S α β := ⟨e⟩
def setoidEquiv : Equivalence (SetoidEquiv S) :=
⟨λ α => ⟨refl α⟩, λ ⟨e⟩ => ⟨symm e⟩, λ ⟨e⟩ ⟨f⟩ => ⟨trans e f⟩⟩

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
⟨Structure.congrArgComp he.left hf.left,   Structure.congrArgComp he.right hf.right⟩

theorem assoc {P Q R Z : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) (g : ProductEquiv R Z) :
  trans (trans e f) g ≈ trans e (trans f g) :=
⟨Structure.assoc        e.fst f.fst g.fst, Structure.assoc        e.snd f.snd g.snd⟩

theorem leftId  {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans e (refl Q) ≈ e :=
⟨Structure.leftId       e.fst,             Structure.leftId       e.snd⟩
theorem rightId {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans (refl P) e ≈ e :=
⟨Structure.rightId      e.fst,             Structure.rightId      e.snd⟩

theorem congrArgInv {P Q : StructureProduct S T} {e₁ e₂ : ProductEquiv P Q} (he : e₁ ≈ e₂) :
  symm e₁ ≈ symm e₂ :=
⟨Structure.congrArgInv  he.left,           Structure.congrArgInv  he.right⟩

theorem leftInv  {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans e (symm e) ≈ refl P :=
⟨Structure.leftInv      e.fst,             Structure.leftInv      e.snd⟩
theorem rightInv {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans (symm e) e ≈ refl Q :=
⟨Structure.rightInv     e.fst,             Structure.rightInv     e.snd⟩

theorem invInv {P Q : StructureProduct S T} (e : ProductEquiv P Q) : symm (symm e) ≈ e :=
⟨Structure.invInv       e.fst,             Structure.invInv       e.snd⟩

theorem compInv {P Q R : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) :
  symm (trans e f) ≈ trans (symm f) (symm e) :=
⟨Structure.compInv      e.fst f.fst,       Structure.compInv      e.snd f.snd⟩

theorem idInv (P : StructureProduct S T) : symm (refl P) ≈ refl P :=
⟨Structure.idInv        P.fst,             Structure.idInv        P.snd⟩

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

variable {A : Sort w} (R S : MappedRelation A) (FF : ∀ {α β : A}, R α β → S α β)

-- This corresponds to `FF` also being a functor. With an inductive definition of `Structure`, the
-- definition of `StructureFunctor` would need to be recursive.
class IsSetoidFunctor where
(respectsSetoid {α β   : A} {f₁ f₂ : R α β}         : f₁ ≈ f₂ → FF f₁ ≈ FF f₂)

class IsCompositionFunctor [HasComposition  R.R] [HasComposition  S.R]
  extends IsSetoidFunctor      R S FF where
(respectsComp   {α β γ : A} (f : R α β) (g : R β γ) : FF (g • f)        ≈ FF g • FF f)

class IsMorphismFunctor    [HasMorphisms    R.R] [HasMorphisms    S.R]
  extends IsCompositionFunctor R S FF where
(respectsId     (α     : A)                         : FF (id_ (R.f α)) ≈ id_ (S.f α))

class IsIsomorphismFunctor [HasIsomorphisms R.R] [HasIsomorphisms S.R]
  extends IsMorphismFunctor    R S FF where
(respectsInv    {α β   : A} (f : R α β)             : FF f⁻¹            ≈ (FF f)⁻¹)

end Functors

open Functors

-- If the target has equivalences in `Prop`, the functor axioms are satisfied trivially.

instance propFunctor {A : Sort w} {R : MappedRelation A} [HasIsomorphisms R.R]
  {U : Sort u} {S : U → U → Prop} [e : IsEquivalence S] {F : A → U}
  {FF : ∀ {α β : A}, R α β → S (F α) (F β)} :
  IsIsomorphismFunctor R ⟨genRel S, F⟩ FF :=
{ respectsSetoid := λ _   => proofIrrel _ _,
  respectsComp   := λ _ _ => proofIrrel _ _,
  respectsId     := λ _   => proofIrrel _ _,
  respectsInv    := λ _   => proofIrrel _ _ }



-- A bundled version of `IsIsomorphismFunctor` where the codomains are structures.

structure GeneralizedFunctor {A : Sort w} {S T : Structure} (F : A → S) (G : A → T) where
(FF {α β : A} : F α ≃ F β → G α ≃ G β)
[isFunctor    : IsIsomorphismFunctor ⟨iso S, F⟩ ⟨iso T, G⟩ FF]

namespace GeneralizedFunctor

@[reducible] def Functor {S T : Structure} (F : S → T) := GeneralizedFunctor id F

variable {A : Sort w} {S T U : Structure}

instance (F : A → S) (G : A → T) :
  CoeFun (GeneralizedFunctor F G) (λ _ => ∀ {α β : A}, F α ≃ F β → G α ≃ G β) :=
⟨GeneralizedFunctor.FF⟩

def generalizeFunctor {B : Sort v} {F : A → S} {G : A → T} (H : B → A) (φ : GeneralizedFunctor F G) :
  GeneralizedFunctor (F ∘ H) (G ∘ H) :=
{ FF        := φ.FF,
  isFunctor := { respectsSetoid := φ.isFunctor.respectsSetoid,
                 respectsComp   := φ.isFunctor.respectsComp,
                 respectsId     := λ β => φ.isFunctor.respectsId (H β),
                 respectsInv    := φ.isFunctor.respectsInv } }

instance {B : Sort v} (F : A → S) (G : A → T) (H : B → A) :
  Coe (GeneralizedFunctor F G) (GeneralizedFunctor (F ∘ H) (G ∘ H)) :=
⟨generalizeFunctor H⟩

namespace id

variable {F : A → S}

instance isFunctor : IsIsomorphismFunctor ⟨iso S, F⟩ ⟨iso S, F⟩ id :=
{ respectsSetoid := id,
  respectsComp   := λ f g => Setoid.refl (g • f),
  respectsId     := λ α   => Setoid.refl (id_ (F α)),
  respectsInv    := λ f   => Setoid.refl f⁻¹ }

def genFun : GeneralizedFunctor F F := ⟨id⟩

end id

namespace comp

variable {F : A → S} {G : A → T} {H : A → U} (φ : GeneralizedFunctor F G) (ψ : GeneralizedFunctor G H)

def compFF {α β : A} (e : F α ≃ F β) := ψ (φ e)

namespace compFF

theorem respectsSetoid {α β :   A} {e f : F α ≃ F β} (h : e ≈ f) :
  compFF φ ψ e ≈ compFF φ ψ f :=
ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsSetoid h)

theorem respectsComp   {α β γ : A} (e : F α ≃ F β) (f : F β ≃ F γ) :
  compFF φ ψ (f • e) ≈ compFF φ ψ f • compFF φ ψ e :=
let h₁ : ψ (φ (f • e)) ≈ ψ (φ f • φ e)     := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsComp e f);
let h₂ : ψ (φ f • φ e) ≈ ψ (φ f) • ψ (φ e) := ψ.isFunctor.respectsComp (φ e) (φ f);
Setoid.trans h₁ h₂

theorem respectsId     (α     : A) :
  compFF φ ψ (id_ (F α)) ≈ id' :=
let h₁ : ψ (φ (id_ (F α))) ≈ ψ (id_ (G α)) := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsId α);
let h₂ : ψ (id_ (G α))     ≈ id_ (H α)     := ψ.isFunctor.respectsId α;
Setoid.trans h₁ h₂

theorem respectsInv    {α β   : A} (e : F α ≃ F β) :
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

def comp.genFun' {B : Sort v} {F : A → S} {G : B → T} {H : B → U} (I : A → B)
                 (φ : GeneralizedFunctor F (G ∘ I)) (ψ : GeneralizedFunctor G H) :
  GeneralizedFunctor F (H ∘ I) :=
comp.genFun φ (generalizeFunctor I ψ)

namespace const

variable {F : A → S} (c : T)

def genFun : GeneralizedFunctor F (Function.const A c) :=
{ FF        := λ _ => IsEquivalence.refl c,
  isFunctor := { respectsSetoid := λ _   => Setoid.refl (id_ c),
                 respectsComp   := λ _ _ => Setoid.symm (leftId (id_ c)),
                 respectsId     := λ _   => Setoid.refl (id_ c),
                 respectsInv    := λ _   => Setoid.symm (idInv c) } }

end const

end GeneralizedFunctor

open GeneralizedFunctor



-- If we have two functions that map from an arbitrary `A` into the same structure `S`, and for each
-- instance of `A` we have an equivalence between the values of both functions, that gives us something
-- that can act as an equivalence between the two functions. In particular:
--
-- * If both are functors, this gives us a definition of equivalence of functors.
--
-- * If only one of them is a functor, we can use the equivalence to turn the other function into a
--   functor as well.

def DependentStructure {A : Sort w} (C : A → Structure) := ∀ α, C α

namespace DependentStructure

variable {A : Sort w} {C : A → Structure}

def generalizeDependentStructure {B : Sort v} (H : B → A) (F : DependentStructure C) : DependentStructure (C ∘ H) :=
λ β => F (H β)

def DependentEquiv (F G : DependentStructure C) := ∀ α, F α ≃ G α

namespace DependentEquiv

def refl  (F     : DependentStructure C)                                                   : DependentEquiv F F :=
λ α => IsEquivalence.refl  (F α)
def symm  {F G   : DependentStructure C} (φ : DependentEquiv F G)                          : DependentEquiv G F :=
λ α => IsEquivalence.symm  (φ α)
def trans {F G H : DependentStructure C} (φ : DependentEquiv F G) (ψ : DependentEquiv G H) : DependentEquiv F H :=
λ α => IsEquivalence.trans (φ α) (ψ α)

def dependentIsoStructure (F G : DependentStructure C) (α : A) := isoStructure (F α) (G α)

def generalizeDependentEquiv {B : Sort v} (H : B → A) {F G : DependentStructure C} (φ : DependentEquiv F G) :
  DependentEquiv (generalizeDependentStructure H F) (generalizeDependentStructure H G) :=
λ β => φ (H β)

def EquivEquiv {F G : DependentStructure C} (φ ψ : DependentEquiv F G) :=
@DependentEquiv A (dependentIsoStructure F G) φ ψ

namespace EquivEquiv

variable {F G : DependentStructure C}

theorem refl  (φ     : DependentEquiv F G)                                           : EquivEquiv φ φ :=
@DependentEquiv.refl A (dependentIsoStructure F G) φ
theorem symm  {φ ψ   : DependentEquiv F G} (e : EquivEquiv φ ψ)                      : EquivEquiv ψ φ :=
DependentEquiv.symm  e
theorem trans {φ ψ χ : DependentEquiv F G} (e : EquivEquiv φ ψ) (f : EquivEquiv ψ χ) : EquivEquiv φ χ :=
DependentEquiv.trans e f

instance dependentEquivSetoid : Setoid (DependentEquiv F G) := ⟨EquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquiv

def dependentEquiv : GeneralizedRelation (DependentStructure C) := λ F G => ⟨DependentEquiv F G⟩

@[reducible] def DependentDependentEquiv {B : Sort v} (H : B → DependentStructure C) (β γ : B) := DependentEquiv (H β) (H γ)

namespace DependentDependentEquiv

variable {B : Sort v} {H : B → DependentStructure C}

def refl  (β     : B)                                                                         : DependentDependentEquiv H β β :=
DependentEquiv.refl  (H β)
def symm  {β γ   : B} (e : DependentDependentEquiv H β γ)                                     : DependentDependentEquiv H γ β :=
DependentEquiv.symm  e
def trans {β γ δ : B} (e : DependentDependentEquiv H β γ) (f : DependentDependentEquiv H γ δ) : DependentDependentEquiv H β δ :=
DependentEquiv.trans e f

instance EquivEquiv.dependentDependentEquivSetoid {β γ : B} : Setoid (DependentDependentEquiv H β γ) := EquivEquiv.dependentEquivSetoid

def dependentDependentEquiv : GeneralizedRelation B := λ β γ => ⟨DependentDependentEquiv H β γ⟩

instance dependentDependentEquivHasIso : HasIsomorphisms (@dependentDependentEquiv A C B H) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ α => congrArgComp (S := C α) (hφ α) (hψ α),
  assoc        := λ φ ψ χ α => assoc        (S := C α) (φ α) (ψ α) (χ α),
  id           := refl,
  leftId       := λ φ     α => leftId       (S := C α) (φ α),
  rightId      := λ φ     α => rightId      (S := C α) (φ α),
  inv          := symm,
  congrArgInv  := λ hφ    α => congrArgInv  (S := C α) (hφ α),
  leftInv      := λ φ     α => leftInv      (S := C α) (φ α),
  rightInv     := λ φ     α => rightInv     (S := C α) (φ α),
  invInv       := λ φ     α => invInv       (S := C α) (φ α),
  compInv      := λ φ ψ   α => compInv      (S := C α) (φ α) (ψ α),
  idInv        := λ β     α => idInv        (S := C α) (H β α) }

end DependentDependentEquiv

instance dependentEquivHasIso : HasIsomorphisms (@dependentEquiv A C) :=
DependentDependentEquiv.dependentDependentEquivHasIso (H := id)

end DependentEquiv

end DependentStructure

open DependentStructure



namespace DependentEquiv

variable {A : Sort w} {S : Structure} {F G : A → S} (φ : DependentEquiv F G)

-- We can "transport" an equivalence `e` between two values of `F` to an equivalence between the
-- corresponding two values of another equivalent function `G`.

def transport    {α β : A} (e : F α ≃ F β) : G α ≃ G β := φ β • e • (φ α)⁻¹
def invTransport {α β : A} (e : G α ≃ G β) : F α ≃ F β := (φ β)⁻¹ • e • φ α

namespace transport

theorem isInverse {α β : A} (e : G α ≃ G β) :
  transport (DependentEquiv.symm φ) e ≈ invTransport φ e :=
congrArgCompRight (congrArgCompRight (invInv (φ α)))

theorem respectsSetoid {α β   : A} {e₁ e₂ : F α ≃ F β} (h : e₁ ≈ e₂) :
  transport φ e₁ ≈ transport φ e₂ :=
congrArgCompRight (congrArgCompLeft h)

theorem respectsComp   {α β γ : A} (e : F α ≃ F β) (f : F β ≃ F γ) :
  transport φ (f • e) ≈ transport φ f • transport φ e :=
let a := φ α;
let b := φ β;
let c := φ γ;
let h₁ : c • (f • e) • a⁻¹ ≈ c • (f • (id' • e)) • a⁻¹         := congrArgCompRight (congrArgCompLeft (congrArgCompRight (Setoid.symm (leftId e))));
let h₂ : c • (f • e) • a⁻¹ ≈ c • (f • ((b⁻¹ • b) • e)) • a⁻¹   := Setoid.trans h₁ (congrArgCompRight (congrArgCompLeft (congrArgCompRight (congrArgCompLeft (Setoid.symm (leftInv b))))));
let h₃ : c • (f • e) • a⁻¹ ≈ c • (f • (b⁻¹ • (b • e))) • a⁻¹   := Setoid.trans h₂ (congrArgCompRight (congrArgCompLeft (congrArgCompRight (Setoid.symm (assoc e b b⁻¹)))));
let h₄ : c • (f • e) • a⁻¹ ≈ c • ((f • b⁻¹) • (b • e)) • a⁻¹   := Setoid.trans h₃ (congrArgCompRight (congrArgCompLeft (assoc (b • e) b⁻¹ f)));
let h₅ : c • (f • e) • a⁻¹ ≈ c • (f • b⁻¹) • ((b • e) • a⁻¹)   := Setoid.trans h₄ (congrArgCompRight (Setoid.symm (assoc a⁻¹ (b • e) (f • b⁻¹))));
let h₆ : c • (f • e) • a⁻¹ ≈ (c • (f • b⁻¹)) • ((b • e) • a⁻¹) := Setoid.trans h₅ (assoc ((b • e) • a⁻¹) (f • b⁻¹) c);
let h₇ : c • (f • e) • a⁻¹ ≈ (c • f • b⁻¹) • (b • e • a⁻¹)     := Setoid.trans h₆ (congrArgCompRight (Setoid.symm (assoc a⁻¹ e b)));
h₇

theorem respectsId     (α     : A) :
  transport φ (id_ (F α)) ≈ id' :=
let a := φ α;
let h₁ : a • id' • a⁻¹ ≈ id' := substCompRight (leftId a⁻¹) (rightInv a);
h₁

theorem respectsInv    {α β   : A} (e : F α ≃ F β) :
  transport φ e⁻¹ ≈ (transport φ e)⁻¹ :=
let a := φ α;
let b := φ β;
let h₁ : a • e⁻¹ • b⁻¹ ≈ (a⁻¹)⁻¹ • (b • e)⁻¹ := congrArgComp (Setoid.symm (compInv e b)) (Setoid.symm (invInv a));
let h₂ : a • e⁻¹ • b⁻¹ ≈ ((b • e) • a⁻¹)⁻¹   := Setoid.trans h₁ (Setoid.symm (compInv a⁻¹ (b • e)));
let h₃ : a • e⁻¹ • b⁻¹ ≈ (b • e • a⁻¹)⁻¹     := Setoid.trans h₂ (congrArgInv (Setoid.symm (assoc a⁻¹ e b)));
h₃

def functor : GeneralizedFunctor F G :=
{ FF        := transport φ,
  isFunctor := { respectsSetoid := respectsSetoid φ,
                 respectsComp   := respectsComp   φ,
                 respectsId     := respectsId     φ,
                 respectsInv    := respectsInv    φ } }

theorem invRespectsSetoid {α β   : A} {e₁ e₂ : G α ≃ G β} (h : e₁ ≈ e₂) :
  invTransport φ e₁ ≈ invTransport φ e₂ :=
let h₁ := respectsSetoid (DependentEquiv.symm φ) h;
Setoid.trans (Setoid.symm (isInverse φ e₁)) (Setoid.trans h₁ (isInverse φ e₂))

theorem invRespectsComp   {α β γ : A} (e : G α ≃ G β) (f : G β ≃ G γ) :
  invTransport φ (f • e) ≈ invTransport φ f • invTransport φ e :=
let h₁ := respectsComp (DependentEquiv.symm φ) e f;
Setoid.trans (Setoid.symm (isInverse φ (f • e))) (Setoid.trans h₁ (congrArgComp (isInverse φ e) (isInverse φ f)))

theorem invRespectsId     (α     : A) :
  invTransport φ (id_ (G α)) ≈ id' :=
let h₁ := respectsId (DependentEquiv.symm φ) α;
Setoid.trans (Setoid.symm (isInverse φ (id_ (G α)))) h₁

theorem invRespectsInv    {α β   : A} (e : G α ≃ G β) :
  invTransport φ e⁻¹ ≈ (invTransport φ e)⁻¹ :=
let h₁ := respectsInv (DependentEquiv.symm φ) e;
Setoid.trans (Setoid.symm (isInverse φ e⁻¹)) (Setoid.trans h₁ (congrArgInv (isInverse φ e)))

def invFunctor : GeneralizedFunctor G F :=
{ FF        := invTransport φ,
  isFunctor := { respectsSetoid := invRespectsSetoid φ,
                 respectsComp   := invRespectsComp   φ,
                 respectsId     := invRespectsId     φ,
                 respectsInv    := invRespectsInv    φ } }

end transport

end DependentEquiv



def GeneralizedNaturalityCondition {A : Sort w} {S T : Structure} {F : A → S} {G₁ G₂ : A → T}
                                   (φ : GeneralizedFunctor F G₁) (ψ : GeneralizedFunctor F G₂)
                                   (ext : DependentEquiv G₁ G₂) :=
∀ {α β : A} (e : F α ≃ F β), ψ e • ext α ≈ ext β • φ e

namespace GeneralizedNaturalityCondition

variable {A : Sort w} {S T : Structure}

theorem refl  {F : A → S} {G₁       : A → T}
              (φ : GeneralizedFunctor F G₁) :
  GeneralizedNaturalityCondition φ φ (DependentEquiv.refl G₁) :=
λ e => Setoid.trans (rightId (φ e)) (Setoid.symm (leftId (φ e)))

theorem symm  {F : A → S} {G₁ G₂    : A → T}
              {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂}
              {ext : DependentEquiv G₁ G₂}
              (nat : GeneralizedNaturalityCondition φ ψ ext) :
  GeneralizedNaturalityCondition ψ φ (DependentEquiv.symm ext) :=
λ {α β} e => Setoid.symm ((leftRightMul (ext α) (φ e) (ψ e) (ext β)).mpr (nat e))

theorem trans {F : A → S} {G₁ G₂ G₃ : A → T}
              {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂} {χ : GeneralizedFunctor F G₃}
              {ext₁ : DependentEquiv G₁ G₂}                    {ext₂ : DependentEquiv G₂ G₃}
              (nat₁ : GeneralizedNaturalityCondition φ ψ ext₁) (nat₂ : GeneralizedNaturalityCondition ψ χ ext₂) :
  GeneralizedNaturalityCondition φ χ (DependentEquiv.trans ext₁ ext₂) :=
λ {α β} e => let h₁ := (rightMulInv (ψ e) (ext₁ β • φ e) (ext₁ α)).mp  (nat₁ e);
             let h₂ := (leftMulInv' (χ e • ext₂ α) (ψ e) (ext₂ β)).mpr (nat₂ e);
             let h₃ := (leftRightMul (ext₁ α) (ext₁ β • φ e) (χ e • ext₂ α) (ext₂ β)).mp (Setoid.trans h₂ h₁);
             applyAssocLeft' (applyAssocRight h₃)

end GeneralizedNaturalityCondition



structure GeneralizedNaturalTransformation {A : Sort w} {S T : Structure} {F : A → S} {G₁ G₂ : A → T}
                                           (φ : GeneralizedFunctor F G₁) (ψ : GeneralizedFunctor F G₂) where
(ext : DependentEquiv G₁ G₂)
(nat : GeneralizedNaturalityCondition φ ψ ext)

namespace GeneralizedNaturalTransformation

variable {A : Sort w} {S T : Structure}

def refl  {F : A → S} {G₁       : A → T} (φ : GeneralizedFunctor F G₁) :
  GeneralizedNaturalTransformation φ φ :=
⟨DependentEquiv.refl  G₁,          GeneralizedNaturalityCondition.refl  φ⟩

def symm  {F : A → S} {G₁ G₂    : A → T} {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂}
          (m : GeneralizedNaturalTransformation φ ψ) :
  GeneralizedNaturalTransformation ψ φ :=
⟨DependentEquiv.symm  m.ext,       GeneralizedNaturalityCondition.symm  m.nat⟩

def trans {F : A → S} {G₁ G₂ G₃ : A → T} {φ : GeneralizedFunctor F G₁} {ψ : GeneralizedFunctor F G₂} {χ : GeneralizedFunctor F G₃}
          (m : GeneralizedNaturalTransformation φ ψ) (n : GeneralizedNaturalTransformation ψ χ) :
  GeneralizedNaturalTransformation φ χ :=
⟨DependentEquiv.trans m.ext n.ext, GeneralizedNaturalityCondition.trans m.nat n.nat⟩

instance naturalTransformationSetoid {F : A → S} {G₁ G₂ : A → T} (φ : GeneralizedFunctor F G₁) (ψ : GeneralizedFunctor F G₂) :
  Setoid (GeneralizedNaturalTransformation φ ψ) :=
⟨λ e f => DependentEquiv.EquivEquiv e.ext f.ext,
 ⟨λ e => DependentEquiv.EquivEquiv.refl e.ext, DependentEquiv.EquivEquiv.symm, DependentEquiv.EquivEquiv.trans⟩⟩

def generalizeNaturalTransformation {B : Sort v} {F : A → S} {G₁ G₂ : A → T} (H : B → A)
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

        theorem respectsSetoid (F : StructureFunctor S T) {α β   : S} {f₁ f₂ : α ≃ β} :
  f₁ ≈ f₂ → F.functor f₁ ≈ F.functor f₂         := F.functor.isFunctor.respectsSetoid
@[simp] theorem respectsComp   (F : StructureFunctor S T) {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  F.functor (g • f) ≈ F.functor g • F.functor f := F.functor.isFunctor.respectsComp f g
@[simp] theorem respectsId     (F : StructureFunctor S T) (α     : S) :
  F.functor (id_ α) ≈ id'                       := F.functor.isFunctor.respectsId   α
@[simp] theorem respectsInv    (F : StructureFunctor S T) {α β   : S} (f : α ≃ β) :
  F.functor f⁻¹     ≈ (F.functor f)⁻¹           := F.functor.isFunctor.respectsInv  f



def congrArgMap (F : StructureFunctor S T) {α β : S} : α ≃ β → F α ≃ F β := F.functor.FF



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
  idInv        := λ β     => FunExt.funExtHasIso.idInv        β }

end FunctorEquiv

instance functorHasStructure : HasStructure (StructureFunctor S T) := ⟨FunctorEquiv.functorEquiv⟩
def functorStructure (S T : Structure) : Structure := ⟨StructureFunctor S T⟩

instance : CoeFun (IsType.type (functorStructure S T)) (λ _ => S → T) := functorCoeFun



-- We have two alternative definitions of `congr` for functors, depending on the order in which we apply
-- the functor and argument equivalences. The natural transformation axiom says exactly that the order
-- does not matter.

def congrMap  {F₁ F₂ : StructureFunctor S T} {α β : S} : F₁ ≃ F₂ → α ≃ β → F₁ α ≃ F₂ β :=
λ φ e => trans (φ.ext α) (F₂.functor e)

def congrMap' {F₁ F₂ : StructureFunctor S T} {α β : S} : F₁ ≃ F₂ → α ≃ β → F₁ α ≃ F₂ β :=
λ φ e => trans (F₁.functor e) (φ.ext β)

theorem congrMap.wd {F₁ F₂ : StructureFunctor S T} {α β : S} (φ : F₁ ≃ F₂) (e : α ≃ β) :
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
λ φ => { ext := λ α => φ.ext (F α),
         nat := λ e => φ.nat (F.functor e) }

namespace congrArgLeft

theorem respectsComp {F : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T U}
                     (φ₁ : G₁ ≃ G₂) (φ₂ : G₂ ≃ G₃) :
  congrArgLeft (F := F) (φ₂ • φ₁) ≈ congrArgLeft φ₂ • congrArgLeft φ₁ :=
λ α => Setoid.refl (φ₂.ext (F α) • φ₁.ext (F α))

theorem respectsId {F : StructureFunctor S T} (G : StructureFunctor T U) :
  congrArgLeft (id_ G) ≈ id_ (G ⊙ F) :=
λ α => Setoid.refl (id_ (G (F α)))

theorem respectsInv {F : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (φ : G₁ ≃ G₂) :
  congrArgLeft (F := F) φ⁻¹ ≈ (congrArgLeft φ)⁻¹ :=
λ α => Setoid.refl (φ.ext (F α))⁻¹

end congrArgLeft

def congrArgRight {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U} :
  F₁ ≃ F₂ → G ⊙ F₁ ≃ G ⊙ F₂ :=
λ φ => { ext := λ α => G.functor (φ.ext α),
         nat := λ {α β} e => let h₁ := respectsSetoid G (φ.nat e);
                             let h₂ := Setoid.trans (Setoid.symm (respectsComp G (φ.ext α) (F₂.functor e))) h₁;
                             let h₄ := Setoid.trans h₂ (respectsComp G (F₁.functor e) (φ.ext β));
                             h₄ }

namespace congrArgRight

theorem respectsComp {F₁ F₂ F₃ : StructureFunctor S T} {G : StructureFunctor T U}
                     (φ₁ : F₁ ≃ F₂) (φ₂ : F₂ ≃ F₃) :
  congrArgRight (G := G) (φ₂ • φ₁) ≈ congrArgRight φ₂ • congrArgRight φ₁ :=
λ α => StructureFunctor.respectsComp G (φ₁.ext α) (φ₂.ext α)

theorem respectsId (F : StructureFunctor S T) {G : StructureFunctor T U} :
  congrArgRight (id_ F) ≈ id_ (G ⊙ F) :=
λ α => StructureFunctor.respectsId G (F α)

theorem respectsInv {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U} (φ : F₁ ≃ F₂) :
  congrArgRight (G := G) φ⁻¹ ≈ (congrArgRight φ)⁻¹ :=
λ α => StructureFunctor.respectsInv G (φ.ext α)

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
λ α => ψ.nat (φ.ext α)

theorem respectsComp {F₁ F₂ F₃ : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T U}
                     (φ₁ : F₁ ≃ F₂) (φ₂ : F₂ ≃ F₃) (ψ₁ : G₁ ≃ G₂) (ψ₂ : G₂ ≃ G₃) :
  congrArg (φ₂ • φ₁) (ψ₂ • ψ₁) ≈ congrArg φ₂ ψ₂ • congrArg φ₁ ψ₁ :=
let h₁ := FunctorEquiv.functorEquivHasIso.congrArgComp (congrArgLeft.respectsComp ψ₁ ψ₂) (congrArgRight.respectsComp φ₁ φ₂);
let h₂ := congrArgCompLeft (S := functorStructure S U) (f := congrArgLeft ψ₁) (wd φ₁ ψ₂);
let h₃ := applyAssoc' (S := functorStructure S U) h₂;
let h₄ := congrArgCompRight (S := functorStructure S U) (g := congrArgRight φ₂) h₃;
let h₅ := applyAssoc (S := functorStructure S U) h₄;
Setoid.trans h₁ h₅

theorem respectsId (F : StructureFunctor S T) (G : StructureFunctor T U) :
  congrArg (id_ F) (id_ G) ≈ id_ (G ⊙ F) :=
let h₁ := FunctorEquiv.functorEquivHasIso.congrArgComp (congrArgLeft.respectsId G) (congrArgRight.respectsId F);
Setoid.trans h₁ (leftId (S := functorStructure S U) id')

theorem respectsInv {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (φ : F₁ ≃ F₂) (ψ : G₁ ≃ G₂) :
  congrArg φ⁻¹ ψ⁻¹ ≈ (congrArg φ ψ)⁻¹ :=
let h₁ := FunctorEquiv.functorEquivHasIso.congrArgComp (congrArgLeft.respectsInv ψ) (congrArgRight.respectsInv φ);
let h₂ := congrArgInv (S := functorStructure S U) (wd φ ψ);
let h₃ := compInv (S := functorStructure S U) (congrArgRight φ) (congrArgLeft ψ);
Setoid.trans h₁ (Setoid.symm (Setoid.trans h₂ h₃))

end congrArg

def assoc (F : StructureFunctor S T) (G : StructureFunctor T U) (H : StructureFunctor U V) :
  H ⊙ (G ⊙ F) ≃ (H ⊙ G) ⊙ F :=
FunctorEquiv.refl (H ⊙ G ⊙ F)

end compFun

namespace idFun

def leftId  (F : StructureFunctor S T) : idFun ⊙ F ≃ F :=
{ ext := λ α => refl (F α),
  nat := GeneralizedNaturalityCondition.refl F.functor }

def rightId (F : StructureFunctor S T) : F ⊙ idFun ≃ F :=
{ ext := λ α => refl (F α),
  nat := GeneralizedNaturalityCondition.refl F.functor }

end idFun



-- The constant functor.

def constFun (c : T) : StructureFunctor S T :=
{ map     := Function.const (IsType.type S) c,
  functor := const.genFun c }



@[reducible] def IsId (F : StructureFunctor S S) := F ≃ @idFun S

namespace IsId

def extDef {F : StructureFunctor S S} (φ : IsId F) (α : S) : F α ≃ α :=
φ.ext α

theorem natDef {F : StructureFunctor S S} (φ : IsId F) {α β : S} (e : α ≃ β) :
  e • φ.ext α ≈ φ.ext β • F.functor e :=
φ.nat e

def rightMul {G : StructureFunctor T T} (ψ : IsId G) (F : StructureFunctor S T) :
  G ⊙ F ≃ F :=
FunctorEquiv.trans (compFun.congrArgLeft (F := F) ψ) (idFun.leftId F)

theorem rightMulDef {G : StructureFunctor T T} (ψ : IsId G) (F : StructureFunctor S T) (α : S) :
  (rightMul ψ F).ext α ≈ ψ.ext (F α) :=
leftId (ψ.ext (F α))

def leftMul {F : StructureFunctor S S} (φ : IsId F) (G : StructureFunctor S T) :
  G ⊙ F ≃ G :=
FunctorEquiv.trans (compFun.congrArgRight (G := G) φ) (idFun.rightId G)

theorem leftMulDef {F : StructureFunctor S S} (φ : IsId F) (G : StructureFunctor S T) (α : S) :
  (leftMul φ G).ext α ≈ G.functor (φ.ext α) :=
leftId (G.functor (φ.ext α))

def refl (S : Structure) : IsId (@idFun S) := FunctorEquiv.refl idFun

def trans {F G : StructureFunctor S S} (φ : IsId F) (ψ : IsId G) : IsId (G ⊙ F) :=
FunctorEquiv.trans (rightMul ψ F) φ

theorem transDef {F G : StructureFunctor S S} (φ : IsId F) (ψ : IsId G) (α : S) :
  (trans φ ψ).ext α ≈ φ.ext α • ψ.ext (F α) :=
congrArgCompRight (rightMulDef ψ F α)

end IsId



@[reducible] def LeftInv (F : StructureFunctor S T) (G : StructureFunctor T S) := IsId (G ⊙ F)

namespace LeftInv

def refl (S : Structure) : LeftInv (@idFun S) (@idFun S) := IsId.refl S

def trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
          (φ : LeftInv F G) (ψ : LeftInv H I) :
  LeftInv (H ⊙ F) (G ⊙ I) :=
let χ : (G ⊙ I) ⊙ (H ⊙ F) ≃ G ⊙ F := compFun.congrArgLeft (F := F) (IsId.leftMul ψ G);
FunctorEquiv.trans χ φ

theorem transDef {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
                 (φ : LeftInv F G) (ψ : LeftInv H I) (α : S) :
  (trans φ ψ).ext α ≈ φ.ext α • G.functor (ψ.ext (F α)) :=
congrArgCompRight (IsId.leftMulDef ψ G (F α))

def Compat {F : StructureFunctor S T} {G : StructureFunctor T S} (φl : LeftInv F G) (φr : LeftInv G F) :=
∀ α, F.functor (φl.ext α) ≈ φr.ext (F α)

namespace Compat

theorem refl (S : Structure) : Compat (LeftInv.refl S) (LeftInv.refl S) :=
λ α => Setoid.refl (IsEquivalence.refl α)

theorem trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
              {φl : LeftInv F G} {φr : LeftInv G F} {ψl : LeftInv H I} {ψr : LeftInv I H}
              (c : Compat φl φr) (d : Compat ψl ψr) :
  Compat (LeftInv.trans φl ψl) (LeftInv.trans ψr φr) :=
λ α => let h₁ : φr.ext (F α) • F.functor (G.functor (ψl.ext (F α))) ≈ ψl.ext (F α) • φr.ext (I (H (F α)))                                 := Setoid.symm (φr.nat (ψl.ext (F α)));
       let h₂ : F.functor (φl.ext α) • F.functor (G.functor (ψl.ext (F α))) ≈ ψl.ext (F α) • φr.ext (I (H (F α)))                         := substCompLeft (c α) h₁;
       let h₃ : F.functor (φl.ext α • G.functor (ψl.ext (F α))) ≈ ψl.ext (F α) • φr.ext (I (H (F α)))                                     := Setoid.trans (respectsComp F (G.functor (ψl.ext (F α))) (φl.ext α)) h₂;
       let h₄ : H.functor (F.functor (φl.ext α • G.functor (ψl.ext (F α)))) ≈ H.functor (ψl.ext (F α)) • H.functor (φr.ext (I (H (F α)))) := Setoid.trans (respectsSetoid H h₃) (respectsComp H (φr.ext (I (H (F α)))) (ψl.ext (F α)));
       let h₅ : H.functor (F.functor (φl.ext α • G.functor (ψl.ext (F α)))) ≈ ψr.ext (H (F α)) • H.functor (φr.ext (I (H (F α))))         := substCompLeft' (d (F α)) h₄;
       let h₆ := Setoid.trans (respectsSetoid H (respectsSetoid F (transDef φl ψl α))) h₅;
       let h₇ := Setoid.trans h₆ (Setoid.symm (transDef ψr φr (H (F α))));
       h₇

end Compat

def Equiv {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T S}
          (φ : F₁ ≃ F₂) (ψ : G₁ ≃ G₂)
          (χ₁ : LeftInv F₁ G₁) (χ₂ : LeftInv F₂ G₂) :=
χ₁ ≈ χ₂ • compFun.congrArg φ ψ

namespace Equiv

theorem refl  {F : StructureFunctor S T} {G : StructureFunctor T S} (χ : LeftInv F G) :
  Equiv (FunctorEquiv.refl F) (FunctorEquiv.refl G) χ χ :=
Setoid.symm (rightCancelId (S := functorStructure S S) (compFun.congrArg.respectsId F G))

theorem symm  {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T S}
              {φ : F₁ ≃ F₂} {ψ : G₁ ≃ G₂}
              {χ₁ : LeftInv F₁ G₁} {χ₂ : LeftInv F₂ G₂}
              (e : Equiv φ ψ χ₁ χ₂) :
  Equiv (FunctorEquiv.symm φ) (FunctorEquiv.symm ψ) χ₂ χ₁ :=
let h₁ := (rightMulInv (S := functorStructure S S) χ₂ χ₁ (compFun.congrArg φ ψ)).mp (Setoid.symm e);
substCompRight' (S := functorStructure S S) (Setoid.symm (compFun.congrArg.respectsInv φ ψ)) h₁

theorem trans {F₁ F₂ F₃ : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T S}
              {φ₁ : F₁ ≃ F₂} {φ₂ : F₂ ≃ F₃} {ψ₁ : G₁ ≃ G₂} {ψ₂ : G₂ ≃ G₃}
              {χ₁ : LeftInv F₁ G₁} {χ₂ : LeftInv F₂ G₂} {χ₃ : LeftInv F₃ G₃}
              (e : Equiv φ₁ ψ₁ χ₁ χ₂) (f : Equiv φ₂ ψ₂ χ₂ χ₃) :
  Equiv (FunctorEquiv.trans φ₁ φ₂) (FunctorEquiv.trans ψ₁ ψ₂) χ₁ χ₃ :=
let h₁ := applyAssocRight' (S := functorStructure S S) (substCompLeft' f e);
substCompRight' (S := functorStructure S S) (Setoid.symm (compFun.congrArg.respectsComp φ₁ φ₂ ψ₁ ψ₂)) h₁

end Equiv

end LeftInv



-- A type class asserting that two functors are inverse to each other. In addition to the condition that
-- the inverse functor is left-inverse and right-inverse, we also have a compatibility condition on these
-- two functor equivalences.

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

end IsInverse



-- A functor between instance structures is actually just a function.

def congrArgFunctor {α : Sort u} {β : Sort v} (f : α → β) :
  @GeneralizedFunctor α (instanceStructure α) (instanceStructure β) id f :=
{ FF        := congrArg f,
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
[isInv  : IsInverse toFun invFun]

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

def funProdStructure (S T : Structure) :=
  StructureProduct.productStructure (functorStructure S T) (functorStructure T S)

def funProd {S T : Structure} (e : StructureEquiv S T) : funProdStructure S T :=
⟨e.toFun, e.invFun⟩



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

def funEquivProd {e f : StructureEquiv S T} (φ : EquivEquiv e f) :
  StructureProduct.ProductEquiv (funProd e) (funProd f) :=
⟨φ.toFunEquiv, φ.invFunEquiv⟩



def EquivEquivEquiv {e f : StructureEquiv S T} (φ ψ : EquivEquiv e f) :=
StructureProduct.ProductEquiv.EquivEquiv (funEquivProd φ) (funEquivProd ψ)

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
  congrArgComp := λ hφ hψ => Structure.congrArgComp (S := funProdStructure S T) hφ hψ,
  assoc        := λ φ ψ χ => Structure.assoc        (S := funProdStructure S T) (funEquivProd φ) (funEquivProd ψ) (funEquivProd χ),
  id           := refl,
  leftId       := λ φ     => Structure.leftId       (S := funProdStructure S T) (funEquivProd φ),
  rightId      := λ φ     => Structure.rightId      (S := funProdStructure S T) (funEquivProd φ),
  inv          := symm,
  congrArgInv  := λ hφ    => Structure.congrArgInv  (S := funProdStructure S T) hφ,
  leftInv      := λ φ     => Structure.leftInv      (S := funProdStructure S T) (funEquivProd φ),
  rightInv     := λ φ     => Structure.rightInv     (S := funProdStructure S T) (funEquivProd φ),
  invInv       := λ φ     => Structure.invInv       (S := funProdStructure S T) (funEquivProd φ),
  compInv      := λ φ ψ   => Structure.compInv      (S := funProdStructure S T) (funEquivProd φ) (funEquivProd ψ),
  idInv        := λ e     => Structure.idInv        (S := funProdStructure S T) (funProd e) }

end EquivEquiv

instance equivHasStructure (S T : Structure) : HasStructure (StructureEquiv S T) := ⟨EquivEquiv.equivEquiv⟩
def equivStructure (S T : Structure) : Structure := ⟨StructureEquiv S T⟩



def congrArgComp {S T U : Structure} {e₁ e₂ : StructureEquiv S T} {f₁ f₂ : StructureEquiv T U} (he : e₁ ≃ e₂) (hf : f₁ ≃ f₂) :
  trans e₁ f₁ ≃ trans e₂ f₂ :=
{ toFunEquiv    := compFun.congrArg he.toFunEquiv  hf.toFunEquiv,
  invFunEquiv   := compFun.congrArg hf.invFunEquiv he.invFunEquiv,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def assoc {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  trans (trans e f) g ≃ trans e (trans f g) :=
{ toFunEquiv    := compFun.assoc e.toFun  f.toFun  g.toFun,
  invFunEquiv   := compFun.assoc g.invFun f.invFun e.invFun,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def leftId  {S T : Structure} (e : StructureEquiv S T) : trans e (refl T) ≃ e :=
{ toFunEquiv    := idFun.leftId e.toFun,
  invFunEquiv   := idFun.leftId e.invFun,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def rightId {S T : Structure} (e : StructureEquiv S T) : trans (refl S) e ≃ e :=
{ toFunEquiv    := idFun.rightId e.toFun,
  invFunEquiv   := idFun.rightId e.invFun,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

def congrArgInv {S T : Structure} {e₁ e₂ : StructureEquiv S T} (he : e₁ ≃ e₂) :
  symm e₁ ≃ symm e₂ :=
{ toFunEquiv    := he.invFunEquiv,
  invFunEquiv   := he.toFunEquiv,
  leftInvEquiv  := he.rightInvEquiv,
  rightInvEquiv := he.leftInvEquiv }

theorem leftInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv e.isInv.leftInv e.isInv.leftInv (IsInverse.trans e.isInv (IsInverse.symm e.isInv)).leftInv (IsInverse.refl S).leftInv :=
let h₁ : LeftInv.trans e.isInv.leftInv e.isInv.rightInv ≈ compFun.congrArg' e.isInv.leftInv e.isInv.leftInv :=
λ α => Setoid.trans (LeftInv.transDef e.isInv.leftInv e.isInv.rightInv α) (congrArgCompRight (respectsSetoid e.invFun (Setoid.symm (e.isInv.lrCompat α))));
let h₂ := Setoid.trans h₁ (Setoid.symm (compFun.congrArg.wd e.isInv.leftInv e.isInv.leftInv));
Setoid.trans h₂ (Setoid.symm (Structure.leftId (S := functorStructure S S) (compFun.congrArg e.isInv.leftInv e.isInv.leftInv)))

def leftInv'  {S T : Structure} (e : StructureEquiv S T) : trans e (symm e) ≃ refl S :=
{ toFunEquiv    := e.isInv.leftInv,
  invFunEquiv   := e.isInv.leftInv,
  leftInvEquiv  := leftInvEquiv e,
  rightInvEquiv := leftInvEquiv e }

theorem rightInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv e.isInv.rightInv e.isInv.rightInv (IsInverse.trans (IsInverse.symm e.isInv) e.isInv).rightInv (IsInverse.refl T).rightInv :=
let h₁ : LeftInv.trans e.isInv.rightInv e.isInv.leftInv ≈ compFun.congrArg' e.isInv.rightInv e.isInv.rightInv :=
λ α => Setoid.trans (LeftInv.transDef e.isInv.rightInv e.isInv.leftInv α) (congrArgCompRight (respectsSetoid e.toFun (Setoid.symm (e.isInv.rlCompat α))));
let h₂ := Setoid.trans h₁ (Setoid.symm (compFun.congrArg.wd e.isInv.rightInv e.isInv.rightInv));
Setoid.trans h₂ (Setoid.symm (Structure.leftId (S := functorStructure T T) (compFun.congrArg e.isInv.rightInv e.isInv.rightInv)))

def rightInv' {S T : Structure} (e : StructureEquiv S T) : trans (symm e) e ≃ refl T :=
{ toFunEquiv    := e.isInv.rightInv,
  invFunEquiv   := e.isInv.rightInv,
  leftInvEquiv  := rightInvEquiv e,
  rightInvEquiv := rightInvEquiv e }

def invInv {S T : Structure} (e : StructureEquiv S T) : symm (symm e) ≃ e :=
{ toFunEquiv    := FunctorEquiv.refl e.toFun,
  invFunEquiv   := FunctorEquiv.refl e.invFun,
  leftInvEquiv  := LeftInv.Equiv.refl e.isInv.leftInv,
  rightInvEquiv := LeftInv.Equiv.refl e.isInv.rightInv }

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

instance hasComp : HasComp         (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasComp
instance hasCmp  : HasComposition  (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasCmp
instance hasId   : HasId           (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasId
instance hasMor  : HasMorphisms    (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasMor
instance hasInv  : HasInv          (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasInv
instance hasIso  : HasIsomorphisms (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.hasIso
instance isEquiv : IsEquivalence   (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasStructure.isEquiv



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

def congrArgEquiv {S T : Structure} {e₁ e₂ : S ≃ T} (φ : e₁ ≃ e₂) (a : S) (b : T) :
  a ≃[e₁] b → a ≃[e₂] b :=
IsEquivalence.trans (IsEquivalence.symm (φ.toFunEquiv.ext a))

end InstanceEquiv



-- Using `StructureEquiv`, we can build a "universe" structure where the objects are structures. This is
-- the same as the groupoid of lower-level groupoids.

def universeStructure : Structure := ⟨Structure⟩

instance : IsType (IsType.type universeStructure) := structureIsType
