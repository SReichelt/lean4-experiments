--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- In this file, written for Lean 4, we introduce a generalization of the concept of "isomorphism" beyond
-- the areas traditionally covered by universal algebra and category theory. The goal is to capture the
-- notion of "equality up to relabeling" in a very abstract and composable way, such that it can be
-- applied automatically to many different type-theoretic structures -- ideally without having to write a
-- single proof for any particular structure.
--
-- Automatic generation of richer structure such as morphisms will follow once the aforementioned goal has
-- been achieved.
--
--  Initial idea
-- --------------
--
-- The starting point of this formalization is actually quite simple: Frequently in mathematics, we are
-- dealing with a set/type together with some structure on it; in Lean this is most commonly realized as a
-- type class `C : Type u → Type v`. If we have a type `α` together with an instance `x : C α` of the type
-- class `C`, we define the "bundled structure" to be `⟨α, x⟩ : Σ α, C α`. For such bundled structures, we
-- are able to give a definition of "isomorphism" as follows:
--
-- * Given an `e : Equiv α β`, i.e. a "relabeling" operation that maps from one carrier type to another,
--   we need to correspondingly relabel instances of `C α` to `C β`, i.e. transport them along `e`. We
--   axiomatize this as a `transport` map which takes `e` to an `f : Equiv (C α) (C β)` in a way that
--   commutes with `refl`, `symm`, and `trans`.
-- 
-- * Then we can define an isomorphism between two bundled instances `⟨α, x⟩ ⟨β, y⟩ : Σ α, C α` to be an
--   `e : Equiv α β` together with a proof that the equivalence given by `transport e` maps `x` to `y`.
--   In other words, we simply require the `transport` operation to correctly apply the given relabeling
--   operation on the right-hand side of the bundled instance.
--
-- The intent of this generic definition of "isomorphism" is that it should enable us to transport
-- elements and properties along concrete isomorphisms in a generic way, i.e. without writing either
-- individual proofs or tactics.
--
--  Generalization
-- ----------------
--
-- Although the initial version applies to a lot of basic algebraic structures, it does not compose very
-- well, as in Lean it is not the case that everything is a type. As a consequence, the `transport` map
-- needs to be defined individually for each type class `C` in the example above.
--
-- Instead, we would like to define e.g. the `transport` map for groups as a composition of a `transport`
-- map for semigroups which have have defined earlier, with another map that only takes care of the
-- additional structure of a group compared to a semigroup.
--
-- In general terms, we would like to treat any bundled structure `⟨α, ⟨x₁, x₂⟩⟩` as `⟨⟨α, x₁⟩, x₂⟩`
-- if `⟨α, x₁⟩` has already been defined as a bundled structure. However, in the initial version this
-- would not type-check because the left-hand side must be a type and `⟨α, x₁⟩` is not a type.
-- (TODO: What about systems where everything _is_ a type?)
--
-- Therefore, we generalize our initial version in two directions:
--
-- * In place of the type `α`, we also allow (among other things) a bundled instance `⟨α, x⟩`, replacing
--   `Equiv` on types with the isomorphism concept we just defined for bundled instances.
--
-- * Moreover, we also need to consider more carefully the case that `x` is again a bundled structure
--   `⟨β, y⟩` where `β` is or contains a type: Although we placed no restrictions on `x` in the
--   description above, we secretly relied on an equality comparison when giving the definition of
--   `transport`. If the right-hand side is actually a structure with isomorphisms, we need to check for
--   isomorphism instead.
--
--  Preliminary results
-- ---------------------
--
-- In order to unify the different cases, we define a generic `Structure` type which can hold various
-- objects with equivalences between them, such as:
--
--  Type                      | Equivalence
-- ---------------------------+---------------------------------
--  `Prop`                    | `Iff`
--  `α : Sort u`              | `Eq`
--  `α` with `[s : Setoid α]` | `s.r`
--  `Sort u`                  | `Equiv` from `data.equiv.basic`
--  `Structure`               | `StructureEquiv` defined below
--
-- It turns out that the required definition of `Structure` is something quite well-known: In theory, it
-- is best formalized as an ∞-groupoid, but instead of working with the entire infinite hierarchy, in Lean
-- we have to make a compromise by coercing equivalences of equivalences to equivalence _relations_, in
-- effect working with a single level of the hierarchy at a time.
--
-- The formalization brought to light some surprising properties of groupoids, which may or may not be
-- known. Most strikingly, we obtain the following result:
-- If we treat equivalence (i.e. isomorphism within a groupoid) as generalized equality, then groupoid
-- functors are just generalized functions. If we then define "injective", "surjective", and "bijective"
-- in a straightforward way, each "bijective" functor actually has an inverse -- even though the
-- formalization is entirely constructive.
--
-- Returning to the goal of defining isomorphism as "equality up to relabeling" for particular structures,
-- we can not only compose bundled structures as described above, but we are actually able to analyze
-- arbitrary structures in terms of their basic type-theoretic building blocks, and in particular:
-- * determine the correct definition of "isomorphism" for each structure,
-- * analyze whether a given property is isomorphism-invariant, and
-- * transport isomorphism-invariant properties along concrete isomorphisms.
--
-- It also looks like much of this analysis can be automated, but this is still WIP.
--
-- While the formalization in terms of ∞-groupoids is strongly related to HoTT, our formalization does not
-- use univalence in any way.


-- TODO:
-- * Finish basic building blocks.
-- * Compose building blocks automatically.
-- * Abstract over Lean's type classes.
-- * Create examples.
-- * Introduce skeletal version, and reference it where appropriate.
-- * Define "canonical isomorphism".
-- * Automatically deduce that properties are isomorphism-invariant.
-- * Introduce structures with morphisms.
-- * Automatically generate those structures automatically where appropriate.
-- * Prove that isomorphism according to those morphisms is the same as isomorphism defined as relabeling.
-- * Generate even more structure automatically.
-- * Explore connection to HLM in more detail.


-- Regarding the last point: HLM is the logic that is being implemented in the interactive theorem prover
-- Slate (https://slate-prover.org/).
--
-- HLM is classical and set-theoretic, but uses a custom set theory that can also be interpreted as a
-- dependent type theory. In fact, the contents of this file started out as an exploration of how to
-- translate from HLM to other dependently-typed systems such as Lean. The result of this exploration is
-- that a "set" in HLM is exactly an ∞-groupoid on the meta level. So this file should be able to serve
-- as a basis for a translation from HLM to Lean, and also to other theorem provers, especially those that
-- implement HoTT.



-- A quick&dirty port of the parts of data.equiv.basic we need; should be replaced once it becomes
-- available in Lean 4 mathlib.
import isomorphism.equiv



universes u v w



-- Iff and Eq are equivalence relations. (Should this be in Core?)
def iffEquiv              : Equivalence Iff     := ⟨Iff.refl, Iff.symm, Iff.trans⟩
def eqEquiv  {α : Sort u} : Equivalence (@Eq α) := ⟨Eq.refl,  Eq.symm,  Eq.trans⟩



-- We want to formalize a very general "structure with equivalences", so we start with a very basic
-- abstraction for something that looks like an equivalence relation except that the codomain is `Sort u`
-- instead of `Prop`. Therefore, `Equiv.refl`/`Equiv.symm`/`Equiv.trans`, where `Equiv` is the Lean 4
-- version of the `equiv` type in Lean 3 mathlib, is also an instance of this type.
--
-- We also need to compare equivalences for equivalence, and there are essentially two options:
-- * The equivalences could be instances of the `Structure` type we are going to define. This would
--   turn that definition into a large mutually inductive type which Lean refuses to accept.
-- * Fortunately, for comparison of equivalences, a setoid is sufficient. Since it is a different setoid
--   for each pair of inputs, we need a bundled version of `Setoid` here.
--
-- Even though `α`, `β` are not necessarily types, we use greek letters to raise awareness that they
-- frequently will be.

structure BundledSetoid where
(α : Sort u)
[s : Setoid α]

instance : CoeSort BundledSetoid (Sort u) := ⟨BundledSetoid.α⟩
instance (s : BundledSetoid) : Setoid s.α := s.s

def eqSetoid (α : Sort u) : BundledSetoid :=
{ α := α,
  s := ⟨Eq, eqEquiv⟩ }

def GeneralizedRelation (U : Sort u) := U → U → BundledSetoid
def genRel {U : Sort u} (r : U → U → Sort v) : GeneralizedRelation U := λ a b => eqSetoid (r a b)

class IsEquivalence {U : Sort u} (R : GeneralizedRelation U) where
(refl  (α     : U) : R α α)
(symm  {α β   : U} : R α β → R β α)
(trans {α β γ : U} : R α β → R β γ → R α γ)

namespace IsEquivalence

-- Every equivalence relation can trivially be converted to an instance of `IsEquivalence`.
instance relGenEquiv {α : Sort u} {r : α → α → Prop} (e : Equivalence r) : IsEquivalence (genRel r) :=
⟨e.refl, e.symm, e.trans⟩

-- Some common instances.
instance iffGenEquiv                                : IsEquivalence (genRel Iff)     := relGenEquiv iffEquiv
instance eqGenEquiv     (α : Sort u)                : IsEquivalence (genRel (@Eq α)) := relGenEquiv eqEquiv
instance setoidGenEquiv (α : Sort u) [s : Setoid α] : IsEquivalence (genRel s.r)     := relGenEquiv s.iseqv
instance equivGenEquiv                              : IsEquivalence (genRel Equiv)   := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end IsEquivalence

open IsEquivalence



-- We would also like to be able to manipulate such equivalences, and we need them to behave like
-- isomorphisms when doing so, with `refl` as the identity, `symm` as inverse, and `trans` as composition.
-- In other words, a structure with its equivalences is a category where every morphism has an inverse (as
-- guaranteed by `symm`), i.e. it is a groupoid.
--
-- Of course, this category can be a subcategory of one where not every morphism is invertible, but since
-- we are defining a generalization of an equivalence relation, we wish to ignore such extra structure at
-- this point. Note that for actual equivalence relations, the axioms are trivially satisfied in a
-- proof-irrelevant system such as Lean.
--
-- We add three redundant axioms to avoid unnecessary computations. (Actually, this list of axioms was
-- originally inspired by the seven corresponding lemmas in `data.equiv.basic` of mathlib in Lean 3:
-- `symm_symm`, `trans_refl`, etc.)
-- With `α β γ δ : U`, and writing `α ≃ β` for `R α β`, we have:
--
-- ` refl     : α ≃ α                           ` | `id`
-- ` symm     : α ≃ β → β ≃ α                   ` | `⁻¹`
-- ` trans    : α ≃ β → β ≃ γ → α ≃ γ           ` | `∘` (in reverse order)
-- ` assoc    (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h ∘ (g ∘ f) = (h ∘ g) ∘ f `
-- ` leftId   (f : α ≃ β)                         : id ∘ f    = f             `
-- ` rightId  (f : α ≃ β)                         : f ∘ id    = f             `
-- ` leftInv  (f : α ≃ β)                         : f⁻¹ ∘ f   = id            `
-- ` rightInv (f : α ≃ β)                         : f ∘ f⁻¹   = id            `
-- ` invInv   (f : α ≃ β)                         : (f⁻¹)⁻¹   = f             `
-- ` compInv  (f : α ≃ β) (g : β ≃ γ)             : (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹     `
-- ` idInv                                        : id⁻¹      = id            `
--
-- In order to avoid the non-constructive operation of taking quotients when our equivalences have
-- nontrivial structure, we replace `=` in the axioms with the setoid equivalence `≈` we just introduced.
-- This means `Structure` is not strictly a groupoid, but we are working in some variant of higher
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

variable {U : Sort u}

class HasComp (M : GeneralizedRelation U) where
(comp {α β γ : U} : M α β → M β γ → M α γ)

-- Note that we use a nonstandard order in `HasComp.comp` so that it directly matches
-- `IsEquivalence.trans`. When using `•` notation (which we use to avoid clashing with `∘`), we reverse
-- the order to conform to function/morphism/functor composition.
def comp {M : GeneralizedRelation U} [h : HasComp M] {α β γ : U} (f : M α β) (g : M β γ) := @HasComp.comp U M h α β γ f g
def revComp {M : GeneralizedRelation U} [h : HasComp M] {α β γ : U} (g : M β γ) (f : M α β) := comp f g
infixr:90 " • " => revComp

class HasComposition (M : GeneralizedRelation U) extends HasComp M where
(congrArgComp {α β γ   : U} {f₁ f₂ : M α β} {g₁ g₂ : M β γ}     : f₁ ≈ f₂ → g₁ ≈ g₂ → g₁ • f₁ ≈ g₂ • f₂)
(assoc        {α β γ δ : U} (f : M α β) (g : M β γ) (h : M γ δ) : h • (g • f) ≈ (h • g) • f)

class HasId (M : GeneralizedRelation U) extends HasComposition M where
(id (α : U) : M α α)

def id__ {M : GeneralizedRelation U} [h : HasId M] (α : U) := @HasId.id U M h α

class HasMorphisms (M : GeneralizedRelation U) extends HasId M where
(leftId  {α β : U} (f : M α β) : id β • f ≈ f)
(rightId {α β : U} (f : M α β) : f • id α ≈ f)

class HasInv (M : GeneralizedRelation U) extends HasMorphisms M where
(inv {α β : U} : M α β → M β α)

def inv {M : GeneralizedRelation U} [h : HasInv M] {α β : U} (f : M α β) := @HasInv.inv U M h α β f 
postfix:10000 "⁻¹"  => inv

class HasIsomorphisms (M : GeneralizedRelation U) extends HasInv M where
(congrArgInv {α β : U} {f₁ f₂ : M α β}         : f₁ ≈ f₂ → f₁⁻¹ ≈ f₂⁻¹)
(leftInv     {α β : U} (f : M α β)             : f⁻¹ • f   ≈ id α)
(rightInv    {α β : U} (f : M α β)             : f • f⁻¹   ≈ id β)
(invInv      {α β : U} (f : M α β)             : (f⁻¹)⁻¹   ≈ f)
(compInv     {α β : U} (f : M α β) (g : M β γ) : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹)
(idInv       (α   : U)                         : (id α)⁻¹  ≈ id α)

instance isoEquiv (M : GeneralizedRelation U) [h : HasIsomorphisms M] : IsEquivalence M :=
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

variable {α : Sort u} (r : α → α → Prop) [h : IsEquivalence (genRel r)]

instance propEquivHasComp : HasComp         (genRel r) := ⟨h.trans⟩
instance propEquivHasCmp  : HasComposition  (genRel r) := ⟨λ _ _ => proofIrrel _ _, λ _ _ _ => proofIrrel _ _⟩
instance propEquivHasId   : HasId           (genRel r) := ⟨h.refl⟩
instance propEquivHasMor  : HasMorphisms    (genRel r) := ⟨λ _ => proofIrrel _ _, λ _ => proofIrrel _ _⟩
instance propEquivHasInv  : HasInv          (genRel r) := ⟨h.symm⟩
instance propEquivHasIso  : HasIsomorphisms (genRel r) := ⟨λ _ => proofIrrel _ _, λ _ => proofIrrel _ _,
                                                           λ _ => proofIrrel _ _, λ _ => proofIrrel _ _,
                                                           λ _ _ => proofIrrel _ _, λ _ => proofIrrel _ _⟩

end PropEquiv

open PropEquiv



namespace SortEquiv

instance sortEquivHasComp : HasComp         (genRel Equiv) := ⟨Equiv.trans⟩

theorem congrArgComp {α β γ : Sort u} {f₁ f₂ : (genRel Equiv) α β} {g₁ g₂ : (genRel Equiv) β γ} (h₁ : f₁ ≈ f₂) (h₂ : g₁ ≈ g₂) :
  g₁ • f₁ ≈ g₂ • f₂ :=
let h := congr (congrArg Equiv.trans h₁) h₂;
h

instance sortEquivHasCmp  : HasComposition  (genRel Equiv) := ⟨congrArgComp, Equiv.transAssoc⟩

instance sortEquivHasId   : HasId           (genRel Equiv) := ⟨Equiv.refl⟩

theorem leftId  {α β : Sort u} (f : (genRel Equiv) α β) : id__ β • f ≈ f := Equiv.transRefl f
theorem rightId {α β : Sort u} (f : (genRel Equiv) α β) : f • id__ α ≈ f := Equiv.reflTrans f

instance sortEquivHasMor  : HasMorphisms    (genRel Equiv) := ⟨leftId, rightId⟩

instance sortEquivHasInv  : HasInv          (genRel Equiv) := ⟨Equiv.symm⟩

theorem congrArgInv {α β : Sort u} {f₁ f₂ : (genRel Equiv) α β} (h₁ : f₁ ≈ f₂) :
  f₁⁻¹ ≈ f₂⁻¹ :=
congrArg Equiv.symm h₁

instance sortEquivHasIso  : HasIsomorphisms (genRel Equiv) := ⟨congrArgInv, Equiv.transSymm, Equiv.symmTrans,
                                                               Equiv.symmSymm, Equiv.symmTransSymm, λ _ => Equiv.reflSymm⟩

end SortEquiv



-- Bundle the generalized equivalence relation and its axioms into a single type class.

class HasStructure (U : Sort u) where
(M : GeneralizedRelation U)
[h : HasIsomorphisms M]

namespace HasStructure

instance hasCmp  (U : Sort u) [h : HasStructure U] : HasComposition  h.M := h.h.toHasComposition
instance hasMor  (U : Sort u) [h : HasStructure U] : HasMorphisms    h.M := h.h.toHasMorphisms
instance hasIso  (U : Sort u) [h : HasStructure U] : HasIsomorphisms h.M := h.h
instance isEquiv (U : Sort u) [h : HasStructure U] : IsEquivalence   h.M := isoEquiv h.M

instance propHasStructure                                 : HasStructure Prop     := ⟨genRel Iff⟩
instance instanceHasStructure (α : Sort u)                : HasStructure α        := ⟨genRel Eq⟩
instance setoidHasStructure   (α : Sort u) [s : Setoid α] : HasStructure α        := ⟨genRel s.r⟩
instance sortHasStructure                                 : HasStructure (Sort u) := ⟨genRel Equiv⟩

end HasStructure

open HasStructure



-- Now we put everything together to define our general "structure with equivalence". Concrete instances are
-- any `Sort u` with `Equiv` as equivalence, any `α : Sort u` with `Eq` as equivalence, and so on, but also
-- some new structures we are going to define below.
--
-- As mentioned before, this type is also
-- * an ∞-groupoid where higher-level equivalences have been coerced to equivalence relations, and
-- * a model of a "set" in the HLM logic of the Slate theorem prover, with equality modeled by the notion of
--   equivalence we have just defined. This is significant because it inspires treating equivalence like an
--   abstract notion of equality throughout the rest of this file.

structure Structure where
(U : Sort u)
[h : HasStructure U]

namespace Structure

instance : CoeSort Structure (Sort u) := ⟨Structure.U⟩

variable {S : Structure}

instance hasStructure : HasStructure S.U := S.h

def iso := S.h.M
def Equv (α β : S) := (iso α β).α
infix:25 " ≃ " => Equv

instance (α β : S) : Setoid (α ≃ β) := (iso α β).s

instance hasCmp : HasComposition  (@iso S) := hasStructure.hasCmp
instance hasMor : HasMorphisms    (@iso S) := hasStructure.hasMor
instance hasIso : HasIsomorphisms (@iso S) := hasStructure.hasIso

def id_ (α : S) : α ≃ α := id__ α
def id' {α : S} := id_ α

        theorem congrArgComp {α β γ   : S} {f₁ f₂ : α ≃ β} {g₁ g₂ : β ≃ γ}     : f₁ ≈ f₂ → g₁ ≈ g₂ → g₁ • f₁ ≈ g₂ • f₂ := hasIso.congrArgComp
        theorem assoc        {α β γ δ : S} (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h • (g • f) ≈ (h • g) • f             := hasIso.assoc    f g h
@[simp] theorem leftId       {α β     : S} (f : α ≃ β)                         : id' • f   ≈ f                         := hasIso.leftId   f
@[simp] theorem rightId      {α β     : S} (f : α ≃ β)                         : f • id'   ≈ f                         := hasIso.rightId  f
        theorem congrArgInv  {α β     : S} {f₁ f₂ : α ≃ β}                     : f₁ ≈ f₂ → f₁⁻¹ ≈ f₂⁻¹                 := hasIso.congrArgInv
@[simp] theorem leftInv      {α β     : S} (f : α ≃ β)                         : f⁻¹ • f   ≈ id'                       := hasIso.leftInv  f
@[simp] theorem rightInv     {α β     : S} (f : α ≃ β)                         : f • f⁻¹   ≈ id'                       := hasIso.rightInv f
@[simp] theorem invInv       {α β     : S} (f : α ≃ β)                         : (f⁻¹)⁻¹   ≈ f                         := hasIso.invInv   f
@[simp] theorem compInv      {α β γ   : S} (f : α ≃ β) (g : β ≃ γ)             : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹                 := hasIso.compInv  f g
@[simp] theorem idInv        (α       : S)                                     : (id_ α)⁻¹ ≈ id'                       := hasIso.idInv    α

def defaultStructure (U : Sort u) [h : HasStructure U] : Structure := ⟨U⟩
def instanceStructure (α : Sort u) := @defaultStructure α (instanceHasStructure α)
def setoidInstanceStructure (α : Sort u) [s : Setoid α] := @defaultStructure α (setoidHasStructure α)
def bundledSetoidStructure (S : BundledSetoid) := setoidInstanceStructure S.α
def sortStructure : Structure := ⟨Sort u⟩

end Structure

open Structure



-- We can "forget" the data held inside a `Structure` on two levels, obtaining modified instances of
-- `Structure`:
--
-- 1. We can coerce the equivalence to an equivalence _relation_, obtaining a "setoid structure."
--    In comments, we will write `setoidStructure S` as `S_≈`.
--
-- 2. In a classical setting, we can additionally take the quotient with respect to equivalence, obtaining
--    a "skeleton structure" where equivalence is equality.
--    In comments, we will write `skeletonStructure S` as `S/≃`.
--
-- Later, we will prove some properties of these operations.
--
-- Within this file, we coerce structures to setoids whenever we want to use structures as isomorphisms,
-- but we never use quotients. With an inductive version of `Structure` (i.e. an actual ∞-groupoid), we
-- could keep all data instead.

namespace Forgetfulness

variable (S : Structure)

def SetoidEquiv (α β : S) := Nonempty (α ≃ β)
def toSetoidEquiv {α β : S} (e : α ≃ β) : SetoidEquiv S α β := ⟨e⟩
def setoidEquiv : Equivalence (SetoidEquiv S) :=
⟨λ α => ⟨refl α⟩, λ ⟨e⟩ => ⟨symm e⟩, λ ⟨e⟩ ⟨f⟩ => ⟨trans e f⟩⟩

instance structureToSetoid : Setoid S.U := ⟨SetoidEquiv S, setoidEquiv S⟩
def setoidStructure : Structure := setoidInstanceStructure S.U

namespace Classical

def StructureQuotient := Quotient (structureToSetoid S)
def skeletonStructure : Structure := ⟨StructureQuotient S⟩

end Classical

end Forgetfulness

open Forgetfulness



-- A functor between two `Structure`s is a map that also maps equivalences in a compatible way. On the
-- one hand, this is just a groupoid functor, but on the other hand, the mapping of equivalences also
-- matches exactly the `transport` map mentioned in the introduction.
--
-- Moreover, if we interpret `≃` as a generalization of equality, the `transport` map is actually the
-- generalized version of `congrArg`, so we name it `congrArgMap`. Under this interpretation, it can also
-- be regarded as a well-definedness condition for the map: equality of arguments implies equality of
-- results.
--
-- For convenience and also to avoid unnecessary computation, we add the redundant requirement that the
-- functor must preserve inverses, as those are an integral part of our axiomatized structure. First, we
-- give a more general definition of a functor, split into the three pieces of structure that we are
-- dealing with so we can potentially reuse it in other contexts.

namespace Functors

variable {U : Sort u} {V : Sort v} {W : Sort w}
         {X : GeneralizedRelation V} {Y : GeneralizedRelation W}
         (F : U → V) (G : U → W)
         (FF : ∀ {α β : U}, X (F α) (F β) → Y (G α) (G β))

-- This corresponds to `FF` also being a functor. With an inductive definition of `Structure`, the
-- definition of `StructureFunctor` would need to be recursive.
class IsSetoidFunctor where
(respectsSetoid {α β : U} {f g : X (F α) (F β)}                   : f ≈ g → FF f ≈ FF g)

class IsCompositionFunctor [cmpX : HasComposition  X] [cmpY : HasComposition  Y]
  extends @IsSetoidFunctor      U V W X Y F G FF                                             where
(respectsComp {α β γ : U} (f : X (F α) (F β)) (g : X (F β) (F γ)) : FF (g • f)      ≈ FF g • FF f)

class IsMorphismFunctor    [morX : HasMorphisms    X] [morY : HasMorphisms    Y]
  extends @IsCompositionFunctor U V W X Y F G FF morX.toHasComposition morY.toHasComposition where
(respectsId   (α     : U)                                         : FF (id__ (F α)) ≈ id__ (G α))

class IsIsomorphismFunctor [isoX : HasIsomorphisms X] [isoY : HasIsomorphisms Y]
  extends @IsMorphismFunctor    U V W X Y F G FF isoX.toHasMorphisms   isoY.toHasMorphisms   where
(respectsInv  {α β   : U} (f : X (F α) (F β))                     : FF f⁻¹          ≈ (FF f)⁻¹)

end Functors

open Functors



-- Now we define our specific version of a functor between structures.

structure StructureFunctor (S T : Structure) :=
(map                   : S     → T)
(congrArgMap {α β : S} : α ≃ β → map α ≃ map β)
[isFunctor             : IsIsomorphismFunctor id map congrArgMap]

namespace StructureFunctor

instance (S T : Structure) : CoeFun (StructureFunctor S T) (λ F => S → T) := ⟨StructureFunctor.map⟩

variable {S T U V : Structure}

-- Restate the axioms as theorems about `congrArgMap`.

        theorem respectsSetoid (F : StructureFunctor S T) {α β   : S} {f g : α ≃ β} :
  f ≈ g → congrArgMap F f ≈ congrArgMap F g                 := F.isFunctor.respectsSetoid
@[simp] theorem respectsComp   (F : StructureFunctor S T) {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  congrArgMap F (g • f) ≈ congrArgMap F g • congrArgMap F f := F.isFunctor.respectsComp f g
@[simp] theorem respectsId     (F : StructureFunctor S T) (α     : S) :
  congrArgMap F (id_ α) ≈ id'                               := F.isFunctor.respectsId   α
@[simp] theorem respectsInv    (F : StructureFunctor S T) {α β   : S} (f : α ≃ β) :
  congrArgMap F f⁻¹     ≈ (congrArgMap F f)⁻¹               := F.isFunctor.respectsInv  f



-- We can define equivalence of functors by extensionality, using equivalence in `T` instead of equality.
-- Note that although writing `∀` instead of `Π` (as required by Lean 4) looks beautiful, it obscures
-- that this definition does not live in `Prop`.
-- This is an equivalence according to our definition, and it is compatible with isomorphisms via the
-- functor axioms, so we can use it to build an instance of `Structure` again.

def FunExt (F G : StructureFunctor S T) := ∀ α, F α ≃ G α

namespace FunExt

def refl  (F     : StructureFunctor S T)                                   : FunExt F F :=
λ α => IsEquivalence.refl  (F α)
def symm  {F G   : StructureFunctor S T} (φ : FunExt F G)                  : FunExt G F :=
λ α => IsEquivalence.symm  (φ α)
def trans {F G H : StructureFunctor S T} (φ : FunExt F G) (ψ : FunExt G H) : FunExt F H :=
λ α => IsEquivalence.trans (φ α) (ψ α)

def FunExtEquiv {F G : StructureFunctor S T} (φ ψ : FunExt F G) := ∀ α, φ α ≈ ψ α

namespace FunExtEquiv

variable {F G : StructureFunctor S T}

theorem refl  (φ     : FunExt F G)                                             : FunExtEquiv φ φ :=
λ α => Setoid.refl  (φ α)

theorem symm  {φ ψ   : FunExt F G} (e : FunExtEquiv φ ψ)                       : FunExtEquiv ψ φ :=
λ α => Setoid.symm  (e α)

theorem trans {φ ψ χ : FunExt F G} (e : FunExtEquiv φ ψ) (f : FunExtEquiv ψ χ) : FunExtEquiv φ χ :=
λ α => Setoid.trans (e α) (f α)

instance funExtSetoid : Setoid (FunExt F G) := ⟨FunExtEquiv, ⟨refl, symm, trans⟩⟩

end FunExtEquiv

def funExt (F G : StructureFunctor S T) : BundledSetoid := ⟨FunExt F G⟩

instance funExtHasIso : HasIsomorphisms (@funExt S T) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ α => congrArgComp (hφ α) (hψ α),
  assoc        := λ φ ψ χ α => assoc        (φ α) (ψ α) (χ α),
  id           := refl,
  leftId       := λ φ     α => leftId       (φ α),
  rightId      := λ φ     α => rightId      (φ α),
  inv          := symm,
  congrArgInv  := λ hφ    α => congrArgInv  (hφ α),
  leftInv      := λ φ     α => leftInv      (φ α),
  rightInv     := λ φ     α => rightInv     (φ α),
  invInv       := λ φ     α => invInv       (φ α),
  compInv      := λ φ ψ   α => compInv      (φ α) (ψ α),
  idInv        := λ F     α => idInv        (F α) }

end FunExt

open FunExt

instance functorHasStructure : HasStructure (StructureFunctor S T) := ⟨funExt⟩
def functorStructure : Structure := ⟨StructureFunctor S T⟩



-- Given this definition of equivalence of functors, it makes sense to define identity and composition and
-- prove that they are well-behaved with respect to equivalence.

def idMap                : S     → S                 := id
def idCongrArg {α β : S} : α ≃ β → idMap α ≃ idMap β := id

instance idIsFunctor (S : Structure) :
  @IsIsomorphismFunctor S.U S.U S.U iso iso id idMap idCongrArg hasIso hasIso :=
{ respectsSetoid := id,
  respectsComp   := λ f g => Setoid.refl (g • f),
  respectsId     := λ α   => Setoid.refl (id_ α),
  respectsInv    := λ f   => Setoid.refl f⁻¹ }

def idFun : StructureFunctor S S := ⟨idMap, idCongrArg⟩

def compMap      (F : StructureFunctor S T) (G : StructureFunctor T U)           :
  S     → U                             := λ f => G (F f)
def compCongrArg (F : StructureFunctor S T) (G : StructureFunctor T U) {α β : S} :
  α ≃ β → compMap F G α ≃ compMap F G β := λ f => congrArgMap G (congrArgMap F f)

theorem compCongrArgComp {F : StructureFunctor S T} {G : StructureFunctor T U} {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  compCongrArg F G (g • f) ≈ compCongrArg F G g • compCongrArg F G f :=
let h₁ : congrArgMap G (congrArgMap F (g • f)) ≈ congrArgMap G (congrArgMap F g • congrArgMap F f) :=
respectsSetoid G (respectsComp F f g);
let h₂ : congrArgMap G (congrArgMap F g • congrArgMap F f) ≈ congrArgMap G (congrArgMap F g) • congrArgMap G (congrArgMap F f) :=
respectsComp G (congrArgMap F f) (congrArgMap F g);
Setoid.trans h₁ h₂

theorem compCongrArgId   {F : StructureFunctor S T} {G : StructureFunctor T U} (α     : S)                         :
  compCongrArg F G (id_ α) ≈ id' :=
let h₁ : congrArgMap G (congrArgMap F (id_ α)) ≈ congrArgMap G id' := respectsSetoid G (respectsId F α);
let h₂ : congrArgMap G id' ≈ id' := respectsId G (id (F α));
Setoid.trans h₁ h₂

theorem compCongrArgInv  {F : StructureFunctor S T} {G : StructureFunctor T U} {α β   : S} (f : α ≃ β)             :
  compCongrArg F G f⁻¹ ≈ (compCongrArg F G f)⁻¹ :=
let h₁ : congrArgMap G (congrArgMap F f⁻¹) ≈ congrArgMap G (congrArgMap F f)⁻¹ := respectsSetoid G (respectsInv F f);
let h₂ : congrArgMap G (congrArgMap F f)⁻¹ ≈ (congrArgMap G (congrArgMap F f))⁻¹ := respectsInv G (congrArgMap F f);
Setoid.trans h₁ h₂

instance compIsFunctor (F : StructureFunctor S T) (G : StructureFunctor T U) :
  @IsIsomorphismFunctor S.U S.U U.U iso iso id (compMap F G) (compCongrArg F G) hasIso hasIso :=
{ respectsSetoid := λ h => respectsSetoid G (respectsSetoid F h),
  respectsComp   := compCongrArgComp,
  respectsId     := compCongrArgId,
  respectsInv    := compCongrArgInv }

def compFun (F : StructureFunctor S T) (G : StructureFunctor T U) : StructureFunctor S U :=
⟨compMap F G, compCongrArg F G⟩

def compFunCongrArg {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (hF : FunExt F₁ F₂) (hG : FunExt G₁ G₂) :
  FunExt (compFun F₁ G₁) (compFun F₂ G₂) :=
λ α => trans (congrArgMap G₁ (hF α)) (hG (F₂ α))

def compFunAssoc (F : StructureFunctor S T) (G : StructureFunctor T U) (H : StructureFunctor U V) :
  FunExt (compFun (compFun F G) H) (compFun F (compFun G H)) := λ α => refl (H (G (F α)))

def compFunLeftId  (F : StructureFunctor S T) : FunExt (compFun F idFun) F := λ α => refl (F α)
def compFunRightId (F : StructureFunctor S T) : FunExt (compFun idFun F) F := λ α => refl (F α)



-- If we wish to use `•` for functors, we need to define them as a setoid first.
-- (Unfortunately, this does not help us in most cases because we would need to introduce our functors
-- as instances of `functorSetoid`, which we don't want.)

instance functorIsSetoid : Setoid (StructureFunctor S T) := structureToSetoid functorStructure
def functorSetoid : BundledSetoid := ⟨StructureFunctor S T⟩

instance hasComp : HasComp        @functorSetoid := ⟨@compFun⟩

theorem compFunCongrArg' {F₁ F₂ : @functorSetoid S T} {G₁ G₂ : @functorSetoid T U} :
  F₁ ≈ F₂ → G₁ ≈ G₂ → G₁ • F₁ ≈ G₂ • F₂ :=
λ ⟨hF⟩ ⟨hG⟩ => ⟨compFunCongrArg hF hG⟩

theorem compFunAssoc' (F : @functorSetoid S T) (G : @functorSetoid T U) (H : @functorSetoid U V) :
  H • (G • F) ≈ (H • G) • F :=
⟨compFunAssoc F G H⟩

instance hasCmp  : HasComposition @functorSetoid := ⟨compFunCongrArg', compFunAssoc'⟩

instance hasId   : HasId          @functorSetoid := ⟨@idFun⟩

theorem compFunLeftId'  (F : @functorSetoid S T) : hasId.id T • F ≈ F := ⟨compFunLeftId  F⟩
theorem compFunRightId' (F : @functorSetoid S T) : F • hasId.id S ≈ F := ⟨compFunRightId F⟩

instance hasMor  : HasMorphisms   @functorSetoid := ⟨compFunLeftId', compFunRightId'⟩



-- A structure for a function that respects a generalized version of the functor axioms but is not
-- actually a functor in the sense of category/groupoid theory.

structure GeneralizedFunctor (F : StructureFunctor S U) (G : StructureFunctor S V) where
(cond {α β : S} : F α ≃ F β → G α ≃ G β)
[isFunctor      : IsIsomorphismFunctor F.map G.map cond]



-- If we interpret `≃` as equality, we can pretend that functors are just functions and define their
-- properties accordingly. Again, note that these definitions contain data.
-- For injectivity, this is equivalent to writing `∀ {α β}, F α ≃ F β → α ≃ β` with the additional
-- requirement that everything must respect setoid and isomorphism operations.

def Injective  (F : StructureFunctor S T) := GeneralizedFunctor F idFun
def Surjective (F : StructureFunctor S T) := ∀ β, Σ α, F α ≃ β
def Bijective  (F : StructureFunctor S T) := Prod (Injective F) (Surjective F)

-- We can even build an inverse functor for any functor that is bijective according to this definition,
-- even though we do not assume classical logic. This works because the equivalences in `Structure` can
-- actually hold the data we are defining here. Note that if we were dealing with propositions and
-- using `∃` instead of `Σ`, obtaining the inverse functor would require (or be equivalent to) using
-- classical logic.
--
-- The inverse functor is unique (modulo equivalence, i.e. `FunExt`).

def inverseElement (F : StructureFunctor S T) (h : Bijective F) (β : T) :=
Sigma.fst (h.snd β)

namespace inverseElement

def isInverse (F : StructureFunctor S T) (h : Bijective F) (β : T) :
  F (inverseElement F h β) ≃ β :=
Sigma.snd (h.snd β)

def isInverse' (F : StructureFunctor S T) (h : Bijective F) (α : S) :
  inverseElement F h (F α) ≃ α :=
h.fst.cond (isInverse F h (F α))

def mapsUniquely (F : StructureFunctor S T) (h : Bijective F) {β γ : T} (e : β ≃ γ) :
  F (inverseElement F h β) ≃ F (inverseElement F h γ) :=
let f := isInverse F h β;
let g := isInverse F h γ;
let h₁ : F (inverseElement F h β) ≃ γ := trans f e;
let h₂ : γ ≃ F (inverseElement F h γ) := symm g;
trans h₁ h₂

def isUnique (F : StructureFunctor S T) (h : Bijective F) {β γ : T} (e : β ≃ γ) :
  inverseElement F h β ≃ inverseElement F h γ :=
h.fst.cond (mapsUniquely F h e)

theorem respectsSetoid {F : StructureFunctor S T} {h : Bijective F} {β γ : T} {e₁ e₂ : β ≃ γ} (φ : e₁ ≈ e₂) :
  isUnique F h e₁ ≈ isUnique F h e₂ :=
let f := isInverse F h β;
let g := isInverse F h γ;
let h₁ : e₁ • f ≈ e₂ • f := congrArgComp (Setoid.refl f) φ;
let h₂ : mapsUniquely F h e₁ ≈ mapsUniquely F h e₂ := congrArgComp h₁ (Setoid.refl g⁻¹);
h.fst.isFunctor.respectsSetoid h₂

theorem respectsComp {F : StructureFunctor S T} {h : Bijective F} {β γ δ : T} (e₁ : β ≃ γ) (e₂ : γ ≃ δ) :
  isUnique F h (e₂ • e₁) ≈ isUnique F h e₂ • isUnique F h e₁ :=
let f := isInverse F h β;
let i := isInverse F h γ;
let g := isInverse F h δ;
let h₁ : g⁻¹ • ((e₂ • e₁) • f) ≈ g⁻¹ • (((e₂ • id') • e₁) • f) := congrArgComp (congrArgComp (Setoid.refl f) (congrArgComp (Setoid.refl e₁) (Setoid.symm (rightId e₂)))) (Setoid.refl g⁻¹);
let h₂ : g⁻¹ • ((e₂ • e₁) • f) ≈ g⁻¹ • (((e₂ • (i • i⁻¹)) • e₁) • f) := Setoid.trans h₁ (congrArgComp (congrArgComp (Setoid.refl f) (congrArgComp (Setoid.refl e₁) (congrArgComp (Setoid.symm (rightInv i)) (Setoid.refl e₂)))) (Setoid.refl g⁻¹));
let h₃ : g⁻¹ • ((e₂ • e₁) • f) ≈ g⁻¹ • ((((e₂ • i) • i⁻¹) • e₁) • f) := Setoid.trans h₂ (congrArgComp (congrArgComp (Setoid.refl f) (congrArgComp (Setoid.refl e₁) (assoc i⁻¹ i e₂))) (Setoid.refl g⁻¹));
let h₄ : g⁻¹ • ((e₂ • e₁) • f) ≈ g⁻¹ • (((e₂ • i) • (i⁻¹ • e₁)) • f) := Setoid.trans h₃ (congrArgComp (congrArgComp (Setoid.refl f) (Setoid.symm (assoc e₁ i⁻¹ (e₂ • i)))) (Setoid.refl g⁻¹));
let h₅ : g⁻¹ • ((e₂ • e₁) • f) ≈ g⁻¹ • ((e₂ • i) • ((i⁻¹ • e₁) • f)) := Setoid.trans h₄ (congrArgComp (Setoid.symm (assoc f (i⁻¹ • e₁) (e₂ • i))) (Setoid.refl g⁻¹));
let h₆ : g⁻¹ • ((e₂ • e₁) • f) ≈ (g⁻¹ • (e₂ • i)) • ((i⁻¹ • e₁) • f) := Setoid.trans h₅ (assoc ((i⁻¹ • e₁) • f) (e₂ • i) g⁻¹);
let h₇ : g⁻¹ • ((e₂ • e₁) • f) ≈ (g⁻¹ • (e₂ • i)) • (i⁻¹ • (e₁ • f)) := Setoid.trans h₆ (congrArgComp (Setoid.symm (assoc f e₁ i⁻¹)) (Setoid.refl (g⁻¹ • (e₂ • i))));
Setoid.trans (h.fst.isFunctor.respectsSetoid h₇) (h.fst.isFunctor.respectsComp (mapsUniquely F h e₁) (mapsUniquely F h e₂))

theorem respectsId {F : StructureFunctor S T} {h : Bijective F} (β : T) :
  isUnique F h (id_ β) ≈ id' :=
let f := isInverse F h β;
let h₁ : f⁻¹ • (id_ β • f) ≈ f⁻¹ • f := congrArgComp (leftId f) (Setoid.refl f⁻¹);
let h₂ : f⁻¹ • (id_ β • f) ≈ id' := Setoid.trans h₁ (leftInv f);
Setoid.trans (h.fst.isFunctor.respectsSetoid h₂) (h.fst.isFunctor.respectsId (inverseElement F h β))

theorem respectsInv {F : StructureFunctor S T} {h : Bijective F} {β γ : T} (e : β ≃ γ) :
  isUnique F h e⁻¹ ≈ (isUnique F h e)⁻¹ :=
let f := isInverse F h β;
let g := isInverse F h γ;
let h₁ : (g⁻¹ • (e • f))⁻¹ ≈ (f⁻¹ • e⁻¹) • g := Setoid.trans (compInv (e • f) g⁻¹) (congrArgComp (invInv g) (compInv f e));
let h₂ : f⁻¹ • (e⁻¹ • g) ≈ (g⁻¹ • (e • f))⁻¹ := Setoid.symm (Setoid.trans h₁ (Setoid.symm (assoc g e⁻¹ f⁻¹)));
Setoid.trans (h.fst.isFunctor.respectsSetoid h₂) (h.fst.isFunctor.respectsInv (mapsUniquely F h e))

end inverseElement

def inverse (F : StructureFunctor S T) (h : Bijective F) : StructureFunctor T S :=
{ map         := inverseElement F h,
  congrArgMap := inverseElement.isUnique F h,
  isFunctor   := { respectsSetoid := inverseElement.respectsSetoid,
                   respectsComp   := inverseElement.respectsComp,
                   respectsId     := inverseElement.respectsId,
                   respectsInv    := inverseElement.respectsInv } }

namespace inverse

def leftInv  (F : StructureFunctor S T) (h : Bijective F) :
  FunExt (compFun F (inverse F h)) idFun :=
inverseElement.isInverse' F h

def rightInv (F : StructureFunctor S T) (h : Bijective F) :
  FunExt (compFun (inverse F h) F) idFun :=
inverseElement.isInverse  F h

end inverse



-- A functor between instance structures is actually just a function.

def InstanceStructureFunctor (α β : Sort u) := StructureFunctor (instanceStructure α) (instanceStructure β)

def instanceStructureFunctor {α β : Sort u} (f : α → β) : InstanceStructureFunctor α β :=
{ map         := f,
  congrArgMap := congrArg f,
  isFunctor   := { respectsSetoid := λ _   => rfl,
                   respectsComp   := λ _ _ => rfl,
                   respectsId     := λ _   => rfl,
                   respectsInv    := λ _   => rfl } }

instance {α β : Sort u} : Coe (α → β) (InstanceStructureFunctor α β) := ⟨instanceStructureFunctor⟩

end StructureFunctor

open StructureFunctor



-- Based on the definition of a functor between two structures, we can define equivalence of two
-- structures in the same way that equivalence of types is defined in mathlib, except that we need to
-- replace equality of functors with an instance of `FunExt`.

structure StructureEquiv (S T : Structure) where
(toFun    : StructureFunctor S T)
(invFun   : StructureFunctor T S)
(leftInv  : FunExt (compFun toFun invFun) idFun)
(rightInv : FunExt (compFun invFun toFun) idFun)

namespace StructureEquiv

def refl  (S     : Structure)                                                   : StructureEquiv S S :=
{ toFun    := idFun,
  invFun   := idFun,
  leftInv  := FunExt.refl idFun,
  rightInv := FunExt.refl idFun }

def symm  {S T   : Structure} (e : StructureEquiv S T)                          : StructureEquiv T S :=
{ toFun    := e.invFun,
  invFun   := e.toFun,
  leftInv  := e.rightInv,
  rightInv := e.leftInv }

def transLeftInv {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) :
  FunExt (compFun (compFun e.toFun f.toFun) (compFun f.invFun e.invFun)) idFun :=
λ α => trans (congrArgMap e.invFun (f.leftInv (e.toFun α))) (e.leftInv α)

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) : StructureEquiv S U :=
{ toFun    := compFun e.toFun  f.toFun,
  invFun   := compFun f.invFun e.invFun,
  leftInv  := transLeftInv e f,
  rightInv := transLeftInv (symm f) (symm e) }



-- If we have a `StructureEquiv S T`, we can ask whether it maps `a : S` to `b : T`, and this is
-- actually a generalized form of an equivalence.

def InstanceEquiv {S T : Structure} (e : StructureEquiv S T) (a : S) (b : T) := e.toFun a ≃ b

namespace InstanceEquiv

def refl  (S     : Structure)                                                   (a : S)                 :
  InstanceEquiv (refl S) a a :=
IsEquivalence.refl a

def symm  {S T   : Structure} (e : StructureEquiv S T)                          (a : S) (b : T)         :
  InstanceEquiv e a b → InstanceEquiv (symm e) b a :=
λ h₁ => IsEquivalence.trans (IsEquivalence.symm (e.invFun.congrArgMap h₁)) (e.leftInv a)

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (a : S) (b : T) (c : U) :
  InstanceEquiv e a b → InstanceEquiv f b c → InstanceEquiv (trans e f) a c :=
λ h₁ h₂ => IsEquivalence.trans (f.toFun.congrArgMap h₁) h₂

end InstanceEquiv



-- We can build a `StructureEquiv` from a bijective functor.

def functorToEquiv {S T : Structure} (F : StructureFunctor S T) (h : Bijective F) : StructureEquiv S T :=
{ toFun    := F,
  invFun   := inverse F h,
  leftInv  := inverse.leftInv  F h,
  rightInv := inverse.rightInv F h }



-- An equivalence between instance structures is actually the same as `Equiv`.

def InstanceStructureEquiv (α β : Sort u) := StructureEquiv (instanceStructure α) (instanceStructure β)

def instanceStructureEquiv {α β : Sort u} (e : Equiv α β) : InstanceStructureEquiv α β :=
{ toFun    := instanceStructureFunctor e.toFun,
  invFun   := instanceStructureFunctor e.invFun,
  leftInv  := e.leftInv,
  rightInv := e.rightInv }

instance {α β : Sort u} : Coe (Equiv α β) (InstanceStructureEquiv α β) := ⟨instanceStructureEquiv⟩

@[simp] theorem instanceEquiv {α β : Sort u} (e : Equiv α β) (a : α) (b : β) :
  InstanceEquiv (instanceStructureEquiv e) a b = (e.toFun a = b) :=
rfl

end StructureEquiv

open StructureEquiv



-- A functor between two structures induces a functor between their setoid structures, and in the
-- classical setting also between their skeleton structures. More specifically, we have the following
-- commutative diagram (modulo equivalence defined on functors, i.e. `FunExt`). If we assume classical
-- logic, all the horizontal functors are `Bijective`, thus we can construct corresponding instances of
-- `StructureEquiv` via `functorToEquiv`.
--
--    `S` -≃--> `S_≈` -≃-> `S/≃`
--     |          |          |
-- `F` |          |          |
--     v          v          v
--    `T` -≃--> `T_≈` -≃-> `T/≃`
--
-- This can be understood as the reason why isomorphism can generally be identified with equality: In all
-- operations that preserve structure, we can take the quotient with respect to equivalence/isomorphism
-- and work on the quotient structures. In particular, if `F` is also `Bijective`, then all structures
-- are equivalent, and thus they are all equal within the quotient structure of the `universeStructure`
-- which we are going to define.
--
-- The HLM logic implemented in Slate can be understood as completely living on the right side of this
-- diagram, as isomorphic structures are always equal in HLM. The same could probably be said about HoTT,
-- but equality in HoTT is a more complex topic.

namespace Forgetfulness

def toSetoidFunctor (S : Structure) : StructureFunctor S (setoidStructure S) :=
{ map         := id,
  congrArgMap := toSetoidEquiv S,
  isFunctor   := { respectsSetoid := λ _   => proofIrrel _ _,
                   respectsComp   := λ _ _ => proofIrrel _ _,
                   respectsId     := λ _   => proofIrrel _ _,
                   respectsInv    := λ _   => proofIrrel _ _ } }

def SetoidStructureFunctor (S T : Structure) := StructureFunctor (setoidStructure S) (setoidStructure T)

def setoidFunctor {S T : Structure} (F : StructureFunctor S T) : SetoidStructureFunctor S T :=
{ map         := F.map,
  congrArgMap := λ ⟨e⟩ => ⟨F.congrArgMap e⟩,
  isFunctor   := { respectsSetoid := λ _   => proofIrrel _ _,
                   respectsComp   := λ _ _ => proofIrrel _ _,
                   respectsId     := λ _   => proofIrrel _ _,
                   respectsInv    := λ _   => proofIrrel _ _ } }

namespace Classical

def setoidToSkeletonFunctor (S : Structure) : StructureFunctor (setoidStructure S) (skeletonStructure S) :=
{ map         := λ α => Quotient.mk α,
  congrArgMap := λ e => Quotient.sound e,
  isFunctor   := { respectsSetoid := λ _   => proofIrrel _ _,
                   respectsComp   := λ _ _ => proofIrrel _ _,
                   respectsId     := λ _   => proofIrrel _ _,
                   respectsInv    := λ _   => proofIrrel _ _ } }

def toSkeletonFunctor (S : Structure) : StructureFunctor S (skeletonStructure S) :=
compFun (toSetoidFunctor S) (setoidToSkeletonFunctor S)

def SkeletonStructureFunctor (S T : Structure) := StructureFunctor (skeletonStructure S) (skeletonStructure T)

variable {S T : Structure}

def skeletonMap (F : SetoidStructureFunctor S T) : skeletonStructure S → skeletonStructure T :=
Quotient.lift (Quotient.mk ∘ F.map) (λ _ _ => Quotient.sound ∘ F.congrArgMap)

def skeletonCongrArg (F : SetoidStructureFunctor S T) {a b : skeletonStructure S} :
  a = b → skeletonMap F a = skeletonMap F b :=
congrArg (skeletonMap F)

def skeletonFunctor (F : SetoidStructureFunctor S T) : StructureFunctor (skeletonStructure S) (skeletonStructure T) :=
{ map         := skeletonMap F,
  congrArgMap := skeletonCongrArg F,
  isFunctor   := { respectsSetoid := λ _   => proofIrrel _ _,
                   respectsComp   := λ _ _ => proofIrrel _ _,
                   respectsId     := λ _   => proofIrrel _ _,
                   respectsInv    := λ _   => proofIrrel _ _ } }

end Classical

end Forgetfulness

open Forgetfulness



-- We would like to use `StructureEquiv` as an equivalence in a `Structure` that can hold structures.
-- With an inductive definition of `Structure`, we could use it directly. However, with the definition
-- of `Structure` we are using, we need to make sure that all instances of `FunExt` inside our
-- equivalence are just propositions (bringing the equivalence down to the same level as `Equiv` in
-- mathlib).
--
-- This is where the `setoidFunctor` we just defined comes into play: If we replace the two functors
-- with the induced functors between the setoid structures, we get an equivalence that fulfills the
-- same role but where equivalence of two equivalences is just a proposition.

def SetoidStructureEquiv (S T : Structure) := StructureEquiv (setoidStructure S) (setoidStructure T)

namespace SetoidStructureEquiv

def toSetoidStructureEquiv {S T : Structure} (e : StructureEquiv S T) : SetoidStructureEquiv S T :=
{ toFun    := setoidFunctor e.toFun,
  invFun   := setoidFunctor e.invFun,
  leftInv  := λ α => ⟨e.leftInv  α⟩,
  rightInv := λ α => ⟨e.rightInv α⟩ }

def refl  (S     : Structure)                                                               : SetoidStructureEquiv S S :=
  StructureEquiv.refl  (setoidStructure S)
def symm  {S T   : Structure} (e : SetoidStructureEquiv S T)                                : SetoidStructureEquiv T S :=
  StructureEquiv.symm  e
def trans {S T U : Structure} (e : SetoidStructureEquiv S T) (f : SetoidStructureEquiv T U) : SetoidStructureEquiv S U :=
  StructureEquiv.trans e f

-- When working with `SetoidStructureEquiv`, we can ignore `leftInv` and `rightInv` because they are
-- just propositions.
def equivEquiv {S T : Structure} (e f : SetoidStructureEquiv S T) :=
e.toFun ≈ f.toFun ∧ e.invFun ≈ f.invFun

namespace equivEquiv

variable {S T : Structure}

theorem refl  (e     : SetoidStructureEquiv S T)                                           : equivEquiv e e :=
⟨Setoid.refl  e.toFun,       Setoid.refl  e.invFun⟩

theorem symm  {e f   : SetoidStructureEquiv S T} (φ : equivEquiv e f)                      : equivEquiv f e :=
⟨Setoid.symm  φ.left,        Setoid.symm  φ.right⟩

theorem trans {e f g : SetoidStructureEquiv S T} (φ : equivEquiv e f) (ψ : equivEquiv f g) : equivEquiv e g :=
⟨Setoid.trans φ.left ψ.left, Setoid.trans φ.right ψ.right⟩

instance equivSetoid : Setoid (SetoidStructureEquiv S T) := ⟨equivEquiv, ⟨refl, symm, trans⟩⟩

end equivEquiv

def structureEquiv (S T : Structure) : BundledSetoid := ⟨SetoidStructureEquiv S T⟩

theorem congrArgComp {S T U : Structure} {e₁ e₂ : SetoidStructureEquiv S T} {f₁ f₂ : SetoidStructureEquiv T U} (he : e₁ ≈ e₂) (hf : f₁ ≈ f₂) :
  trans e₁ f₁ ≈ trans e₂ f₂ :=
⟨compFunCongrArg' he.left hf.left, compFunCongrArg' hf.right he.right⟩

theorem assoc {S T U V : Structure} (e : SetoidStructureEquiv S T) (f : SetoidStructureEquiv T U) (g : SetoidStructureEquiv U V) :
  trans (trans e f) g ≈ trans e (trans f g) :=
⟨compFunAssoc' e.toFun f.toFun g.toFun, compFunAssoc' g.invFun f.invFun e.invFun⟩

theorem leftId  {S T : Structure} (e : SetoidStructureEquiv S T) : trans e (refl T) ≈ e := Setoid.refl e
theorem rightId {S T : Structure} (e : SetoidStructureEquiv S T) : trans (refl S) e ≈ e := Setoid.refl e

theorem congrArgInv {S T : Structure} {e₁ e₂ : SetoidStructureEquiv S T} (he : e₁ ≈ e₂) :
  symm e₁ ≈ symm e₂ :=
⟨he.right, he.left⟩

theorem leftInv'  {S T : Structure} (e : SetoidStructureEquiv S T) : compFun e.toFun e.invFun ≈ idFun :=
⟨e.leftInv⟩
theorem rightInv' {S T : Structure} (e : SetoidStructureEquiv S T) : compFun e.invFun e.toFun ≈ idFun :=
⟨e.rightInv⟩

theorem leftInv  {S T : Structure} (e : SetoidStructureEquiv S T) : trans e (symm e) ≈ refl S :=
⟨leftInv'  e, leftInv'  e⟩
theorem rightInv {S T : Structure} (e : SetoidStructureEquiv S T) : trans (symm e) e ≈ refl T :=
⟨rightInv' e, rightInv' e⟩

theorem invInv {S T : Structure} (e : SetoidStructureEquiv S T) : symm (symm e) ≈ e := Setoid.refl e

theorem compInv {S T U : Structure} (e : SetoidStructureEquiv S T) (f : SetoidStructureEquiv T U) :
  symm (trans e f) ≈ trans (symm f) (symm e) :=
Setoid.refl (trans (symm f) (symm e))

theorem idInv (S : Structure) : symm (refl S) ≈ refl S := Setoid.refl (refl S)

instance equivHasIso : HasIsomorphisms structureEquiv :=
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

theorem InstanceEquiv.congrArg {S T : Structure} {e₁ e₂ : SetoidStructureEquiv S T} (h : e₁ ≈ e₂) (a : S) (b : T) :
  InstanceEquiv e₁ a b → InstanceEquiv e₂ a b :=
let ⟨φ⟩ := h.left;
IsEquivalence.trans (IsEquivalence.symm (φ a))

end SetoidStructureEquiv

open SetoidStructureEquiv



-- Using this definition of equivalence, now we can actually build a "universe" structure, or
-- equivalently the groupoid of lower-level groupoids. Note that the objects are actual structures
-- (of a lower Lean universe), but the equivalences have been coerced to setoids, i.e. they no
-- longer contain their inner structure.

instance structureHasStructure : HasStructure Structure := ⟨structureEquiv⟩

def universeStructure : Structure := ⟨Structure⟩



-- When using `sortStructure` to encode `Sort u` as a `Structure` with equivalences given by `Equiv`,
-- the framework we have defined so far does not offer a way to transport an individual instance
-- `x : α` of a type `α : Sort u` along an encoded `Equiv`. Since the introductory description
-- contains precisely this operation, we need to provide an abstraction for it.
--
-- The `universeStructure` we have just defined enables us to do exactly that: The function
-- `instanceStructure`, which encodes a given Lean type as a `Structure` with equivalence given by
-- equality, is actually a functor from `sortStructure` to `universeStructure`. This functor
-- transports an `Equiv` between two types to a `StructureEquiv` between the corresponding instance
-- structures. And `StructureEquiv` provides the necessary operation of transporting an instance of
-- one structure to the other.
--
-- The benefit of this encoding is that `StructureEquiv` is much more general than the original
-- `Equiv` because many different objects can be encoded as instances of `Structure`.

theorem Setoid.fromEq {α : Sort u} [Setoid α] {a b : α} (h : a = b) : a ≈ b :=
Eq.subst h (Setoid.refl a)

def instanceStructureEquiv' {α β : Sort u} (e : Equiv α β) := toSetoidStructureEquiv (instanceStructureEquiv e)

def sortToStructureFunctor : StructureFunctor sortStructure universeStructure :=
{ map         := instanceStructure,
  congrArgMap := instanceStructureEquiv',
  isFunctor   := { respectsSetoid := λ h   => Setoid.fromEq (congrArg instanceStructureEquiv' h),
                   respectsComp   := λ e f => Setoid.refl (instanceStructureEquiv' (f • e)),
                   respectsId     := λ α   => Setoid.refl (instanceStructureEquiv' (id_ α)),
                   respectsInv    := λ e   => Setoid.refl (instanceStructureEquiv' e⁻¹) } }



-- After this tour across universes, we return to our original goal of automating the definition of
-- isomorphisms for arbitrary structures.

namespace BuildingBlocks

structure DependentFunctor where
(S : Structure)
(C : StructureFunctor S universeStructure)

def makeDependentFunctor {S : Structure} (C : StructureFunctor S sortStructure) : DependentFunctor :=
⟨S, compFun C sortToStructureFunctor⟩

structure EncodedPiExpr (T : DependentFunctor) where
(map (α : T.S) : (T.C α).U)

instance (T : DependentFunctor) : CoeFun (EncodedPiExpr T) (λ F => ∀ α : T.S, (T.C α).U) := ⟨EncodedPiExpr.map⟩

-- TODO: Σ may be redundant because everything is built on Π/∀ in Lean.

structure EncodedSigmaExpr (T : DependentFunctor) where
(α : T.S)
(x : (T.C α).U)

-- Every term of type `∀ x, C x` or `Σ' x, C x` where everything has structures and functors can be
-- converted to an instance of `EncodedPiExpr` or `EncodedSigmaExpr`, respectively.

-- TODO: Figure out in which cases we can determine the functor properties of `C` automatically.
-- Easiest case: `C` does not actually depend on `x`, i.e. we have a function...

def encodePiExpr    {α : Sort u} [h : HasStructure α] {C : StructureFunctor (defaultStructure α) sortStructure} (f : ∀  x : α, C x) :
  EncodedPiExpr    (makeDependentFunctor C) := ⟨f⟩

def encodeSigmaExpr {α : Sort u} [h : HasStructure α] {C : StructureFunctor (defaultStructure α) sortStructure} (f : Σ' x : α, C x) :
  EncodedSigmaExpr (makeDependentFunctor C) := ⟨f.fst, f.snd⟩



-- We can define equivalences between such Π and Σ expressions. These fulfill the isomorphism axioms
-- and thus turn the types `EncodedPiExpr T` and `EncodedSigmaExpr T` into structures.

def PiEquiv {T : DependentFunctor} (F G : EncodedPiExpr T) := ∀ x, F x ≃ G x

namespace PiEquiv

variable {T : DependentFunctor}

def refl  (F     : EncodedPiExpr T)                                     : PiEquiv F F :=
λ α => IsEquivalence.refl  (F α)
def symm  {F G   : EncodedPiExpr T} (φ : PiEquiv F G)                   : PiEquiv G F :=
λ α => IsEquivalence.symm  (φ α)
def trans {F G H : EncodedPiExpr T} (φ : PiEquiv F G) (ψ : PiEquiv G H) : PiEquiv F H :=
λ α => IsEquivalence.trans (φ α) (ψ α)

def PiEquivEquiv {F G : EncodedPiExpr T} (φ ψ : PiEquiv F G) := ∀ α, φ α ≈ ψ α

namespace PiEquivEquiv

variable {F G : EncodedPiExpr T}

theorem refl  (φ     : PiEquiv F G)                                               : PiEquivEquiv φ φ :=
λ α => Setoid.refl  (φ α)

theorem symm  {φ ψ   : PiEquiv F G} (e : PiEquivEquiv φ ψ)                        : PiEquivEquiv ψ φ :=
λ α => Setoid.symm  (e α)

theorem trans {φ ψ χ : PiEquiv F G} (e : PiEquivEquiv φ ψ) (f : PiEquivEquiv ψ χ) : PiEquivEquiv φ χ :=
λ α => Setoid.trans (e α) (f α)

instance piEquivSetoid : Setoid (PiEquiv F G) := ⟨PiEquivEquiv, ⟨refl, symm, trans⟩⟩

end PiEquivEquiv

def piEquiv (F G : EncodedPiExpr T) : BundledSetoid := ⟨PiEquiv F G⟩

instance piEquivHasIso : HasIsomorphisms (@piEquiv T) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ α => congrArgComp (hφ α) (hψ α),
  assoc        := λ φ ψ χ α => assoc        (φ α) (ψ α) (χ α),
  id           := refl,
  leftId       := λ φ     α => leftId       (φ α),
  rightId      := λ φ     α => rightId      (φ α),
  inv          := symm,
  congrArgInv  := λ hφ    α => congrArgInv  (hφ α),
  leftInv      := λ φ     α => leftInv      (φ α),
  rightInv     := λ φ     α => rightInv     (φ α),
  invInv       := λ φ     α => invInv       (φ α),
  compInv      := λ φ ψ   α => compInv      (φ α) (ψ α),
  idInv        := λ F     α => idInv        (F α) }

end PiEquiv

open PiEquiv

instance piHasStructure (T : DependentFunctor) : HasStructure (EncodedPiExpr T) := ⟨@piEquiv T⟩
def piStructure (T : DependentFunctor) : Structure := ⟨EncodedPiExpr T⟩



-- The equivalence between encoded Σ expressions is actually the generalized version of the example
-- in the introduction: A bundled instance of a Lean type class is an instance of the corresponding
-- Σ type. If the type class is a functor, we can define two bundled instances to be isomorphic iff
-- we have an equivalence between the types such that `congrArgMap` maps one instance of the type
-- class to the other.

def SigmaEquiv {T : DependentFunctor} (F G : EncodedSigmaExpr T) :=
Σ' e : F.α ≃ G.α, InstanceEquiv (T.C.congrArgMap e) F.x G.x

namespace SigmaEquiv

variable {T : DependentFunctor}

def refl  (F     : EncodedSigmaExpr T)                                           : SigmaEquiv F F :=
let h₁ := InstanceEquiv.refl (setoidStructure (T.C F.α)) F.x;
let h₂ := Setoid.symm (respectsId   T.C F.α);
⟨IsEquivalence.refl  F.α,         InstanceEquiv.congrArg h₂ F.x F.x h₁⟩

def symm  {F G   : EncodedSigmaExpr T} (φ : SigmaEquiv F G)                      : SigmaEquiv G F :=
let h₁ := InstanceEquiv.symm (congrArgMap T.C φ.fst) F.x G.x φ.snd;
let h₂ := Setoid.symm (respectsInv  T.C φ.fst);
⟨IsEquivalence.symm  φ.fst,       InstanceEquiv.congrArg h₂ G.x F.x h₁⟩

def trans {F G H : EncodedSigmaExpr T} (φ : SigmaEquiv F G) (ψ : SigmaEquiv G H) : SigmaEquiv F H :=
let h₁ := InstanceEquiv.trans (congrArgMap T.C φ.fst) (congrArgMap T.C ψ.fst) F.x G.x H.x φ.snd ψ.snd;
let h₂ := Setoid.symm (respectsComp T.C φ.fst ψ.fst);
⟨IsEquivalence.trans φ.fst ψ.fst, InstanceEquiv.congrArg h₂ F.x H.x h₁⟩

-- No need to compare `φ.snd` and `ψ.snd` because they are proofs.
def SigmaEquivEquiv {F G : EncodedSigmaExpr T} (φ ψ : SigmaEquiv F G) := φ.fst ≈ ψ.fst

namespace SigmaEquivEquiv

variable {F G : EncodedSigmaExpr T}

theorem refl  (φ     : SigmaEquiv F G)                                                     : SigmaEquivEquiv φ φ :=
Setoid.refl  φ.fst

theorem symm  {φ ψ   : SigmaEquiv F G} (e : SigmaEquivEquiv φ ψ)                           : SigmaEquivEquiv ψ φ :=
Setoid.symm  e

theorem trans {φ ψ χ : SigmaEquiv F G} (e : SigmaEquivEquiv φ ψ) (f : SigmaEquivEquiv ψ χ) : SigmaEquivEquiv φ χ :=
Setoid.trans e f

instance sigmaEquivSetoid : Setoid (SigmaEquiv F G) := ⟨SigmaEquivEquiv, ⟨refl, symm, trans⟩⟩

end SigmaEquivEquiv

def sigmaEquiv (F G : EncodedSigmaExpr T) : BundledSetoid := ⟨SigmaEquiv F G⟩

instance sigmaEquivHasIso : HasIsomorphisms (@sigmaEquiv T) :=
{ comp         := trans,
  congrArgComp := λ hφ hψ => congrArgComp hφ hψ,
  assoc        := λ φ ψ χ => assoc        φ.fst ψ.fst χ.fst,
  id           := refl,
  leftId       := λ φ     => leftId       φ.fst,
  rightId      := λ φ     => rightId      φ.fst,
  inv          := symm,
  congrArgInv  := λ hφ    => congrArgInv  hφ,
  leftInv      := λ φ     => leftInv      φ.fst,
  rightInv     := λ φ     => rightInv     φ.fst,
  invInv       := λ φ     => invInv       φ.fst,
  compInv      := λ φ ψ   => compInv      φ.fst ψ.fst,
  idInv        := λ F     => idInv        F.α }

end SigmaEquiv

open SigmaEquiv

instance sigmaHasStructure (T : DependentFunctor) : HasStructure (EncodedSigmaExpr T) := ⟨@sigmaEquiv T⟩
def sigmaStructure (T : DependentFunctor) : Structure := ⟨EncodedSigmaExpr T⟩

end BuildingBlocks
