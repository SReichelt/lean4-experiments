--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- In this file, written for Lean 4, we introduce a generalization of the concept of "isomorphism" beyond
-- universal algebra and category theory. It axiomatically captures the notion of "equality up to
-- relabeling" in a composable way, such that it can be applied in a computational way to all structures
-- that can be defined in type theory -- ideally without having to write a single proof for any particular
-- structure. Automatic generation of richer structure such as morphisms also seems within reach.
--
--  Initial idea
-- --------------
--
-- The starting point of this formalization is actually quite simple: Frequently in mathematics, we are
-- dealing with a set/type together with some structure on it; in Lean this is most commonly realized as a
-- type class `C : Type u → Type v`. If `α` is a type with an instance `x : C α` of `C`, we define its
-- "bundled structure" to be `⟨α, x⟩ : Σ α, C α`. For such bundled structures, we are able to give a
-- definition of "isomorphism" as follows:
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
-- However, we would really like to define e.g. the `transport` map for groups as a composition of a
-- `transport` map for semigroups which have have defined earlier, with another map that only takes care
-- of the additional structure of a group compared to a semigroup.
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
-- After determining what exactly this `Structure` type should be, the result is starting to look more and
-- more like a Rosetta stone that translates
-- * between different concepts of equivalence, isomorphism, and equality, but also
-- * between constructive dependent type theory and (a certain variant of) classical set theory:
--
-- In particular, while formalizing the "universe structure" which holds structures of a lower universe,
-- we encounter and leverage a "simulated" classical logic within our fully constructive formalization.
-- This classical logic becomes an integral part of the universe structure, or in other words constructive
-- type theory and classical set theory occur as just two different points on the path from one universe
-- to the next. In particular, we obtain a constructive interpretation of (a certain variant of) classical
-- set theory.
--
-- In addition, we can give a novel (?) explanation why isomorphism can generally be treated as equality.
--
-- Returning to the goal of defining isomorphism as "equality up to relabeling" for particular structures,
-- we can not only compose bundled structures as described above, but we are actually able to
-- automatically analyze arbitrary structures in terms of their basic building blocks, and in particular:
-- * determine the correct definition of "isomorphism" for each structure,
-- * automatically analyze whether a given property is isomorphism-invariant, and
-- * transport isomorphism-invariant properties along concrete isomorphisms.
--
-- All of this seems strongly related to HoTT but does not use univalence in any way. We give some
-- pointers to possible connections to other theories below. Mathematically some of this might also be a
-- reinvention of existing ideas, but there seems to be some novelty in the combination of these ideas.


-- TODO:
-- * Fill sorrys.
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
-- translate from HLM to other dependently-typed systems such as Lean. A very interesting preliminary
-- result is that apparently the translated theory can be made fully constructive, even though HLM is
-- built on classical logic in quite a fundamental way. How can this be?
--
-- One particular property of HLM plays an important role here: In HLM, equality on structures is not
-- "given" but instead defined individually for each structure. The result is that in a certain sense,
-- it is always possible to "unfold the definition" of an equality. One interpretation of the results
-- obtained in this formalization is that the possibility to unfold equalities is what gives every
-- theory in HLM a constructive interpretation. Note especially how in constructive type theory, many
-- equalities are neither provable nor disprovable, nor can they be "unfolded" in the way just described.



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

def propSetoid (p : Prop) : BundledSetoid :=
{ α := p,
  s := ⟨Eq, eqEquiv⟩ }

def GeneralizedRelation (U : Sort u) := U → U → BundledSetoid
def genRel (r : α → α → Prop) : GeneralizedRelation α := λ a b => propSetoid (r a b)

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
instance eqGenEquiv     {α : Sort u}                : IsEquivalence (genRel (@Eq α)) := relGenEquiv eqEquiv
instance setoidGenEquiv (α : Sort u) [s : Setoid α] : IsEquivalence (genRel s.r)     := relGenEquiv s.iseqv

end IsEquivalence

open IsEquivalence



-- We would also like to be able to manipulate such equivalences, and we need them to behave like
-- isomorphisms when doing so, with `refl` as the identity, `symm` as inverse, and `trans` as composition.
-- In other words, a structure with its equivalences is a category where every morphism has an inverse (as
-- guaranteed by `symm`).
--
-- Of course, this category can be a subcategory of one where not every morphism is invertible, but since
-- we are defining a generalization of an equivalence relation, we wish to ignore such extra structure at
-- this point. Note that for actual equivalence relations, the axioms are trivially satisfied in a
-- proof-irrelevant system such as Lean.
--
-- We add three redundant axioms to avoid unnecessary computations. (Actually, this list of axioms was
-- originally inspired by the seven corresponding lemmas in `data.equiv.basic` of mathlib in Lean 3:
-- `symm_symm`, `trans_refl`, etc.)
-- With `α β γ δ : U`, and writing `α ≃ β` for `equiv α β`, we have:
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
-- This also requires the addition of two new axioms asserting that composition and inverses are
-- compatible with this equivalence.
--
-- Remark: Interestingly, all axioms can be regarded as simplification rules (with the simplification for
-- associativity being the omission of parentheses). with the addition of the three redundant axioms, they
-- enable equational reasoning by transforming all possible terms into a canonical form. Besides making
-- proofs trivial, this observation also suggests an alternative formalization of the axioms in terms of a
-- simplification function.

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
(compInv     {α β : U} (f : M α β) (g : M β γ) : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹)
(leftInv     {α β : U} (f : M α β)             : f⁻¹ • f   ≈ id α)
(rightInv    {α β : U} (f : M α β)             : f • f⁻¹   ≈ id β)
(invInv      {α β : U} (f : M α β)             : (f⁻¹)⁻¹   ≈ f)
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
instance propEquivHasIso  : HasIsomorphisms (genRel r) := ⟨λ _ => proofIrrel _ _, λ _ _ => proofIrrel _ _,
                                                           λ _ => proofIrrel _ _, λ _ => proofIrrel _ _,
                                                           λ _ => proofIrrel _ _, λ _ => proofIrrel _ _⟩

end PropEquiv

open PropEquiv



-- Bundle the generalized equivalence relation and its axioms into a single type class.

class HasStructure (U : Sort u) where
(M : GeneralizedRelation U)
[h : HasIsomorphisms M]

namespace HasStructure

instance hasCmp  (U : Sort u) [h : HasStructure U] : HasComposition  h.M := h.h.toHasComposition
instance hasMor  (U : Sort u) [h : HasStructure U] : HasMorphisms    h.M := h.h.toHasMorphisms
instance hasIso  (U : Sort u) [h : HasStructure U] : HasIsomorphisms h.M := h.h
instance isEquiv (U : Sort u) [h : HasStructure U] : IsEquivalence   h.M := isoEquiv h.M

instance propHasStructure                                 : HasStructure Prop := ⟨genRel Iff⟩
instance instanceHasStructure (α : Sort u)                : HasStructure α    := ⟨genRel Eq⟩
instance setoidHasStructure   (α : Sort u) [s : Setoid α] : HasStructure α    := ⟨genRel s.r⟩

end HasStructure

open HasStructure



-- Now we put everything together to define our general "structure with equivalence". Concrete instances are
-- any `Type u` with `Equiv` as equivalence, any `α : Type u` with `Eq` as equivalence, and so on, but also
-- some new structures we are going to define below.
--
-- Side note: In HLM, the logic implemented for the Slate theorem prover, the most fundamental concept is a
-- "set," but sets in HLM must be understood more like sets in Lean than sets in axiomatic set theory. An
-- HLM set is essentially a type with an equality (following something like Cantor's original ideas instead
-- of ZFC), and this `Structure` is precisely the internalization of an HLM set in type theory.

structure Structure where
(U : Sort u)
[h : HasStructure U]

namespace Structure

instance : CoeSort Structure (Sort u) := ⟨Structure.U⟩

variable {S : Structure}

instance hasStructure : HasStructure S.U := S.h

def iso := S.h.M
def Equiv (α β : S) := (iso α β).α
infix:25 " ≃ " => Equiv

instance (α β : S) : Setoid (Equiv α β) := (iso α β).s

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
-- but we never use quotients. With an inductive version of `Structure`, we could keep all data instead.

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



-- We want to define a map between two `Structure`s that is compatible with their equivalences.
-- In particular, the map should be equipped with a function that transports "relabeling" operations as
-- described in the introduction, i.e. equivalences. If we interpret `≃` as a generalization of equality,
-- this function is actually the generalized version of `congrArg`, so we choose this name. Under this
-- interpretation, it can also be regarded as a well-definedness condition for the map.
--
-- `congrArg` must respect operations on isomorphisms, which is best understood as the combination of
-- `map` and `congrArg` being a functor. For convenience and also to avoid unnecessary computation, we
-- add the requirement that the functor must preserve inverses, as those are an integral part of our
-- axiomatized structure. So first we give a more general definition of a functor, split into the three
-- pieces of structure that we are dealing with so we can potentially reuse it in other contexts.

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
(map                : S     → T)
(congrArg {α β : S} : α ≃ β → map α ≃ map β)
[isFunctor          : IsIsomorphismFunctor id map congrArg]

namespace StructureFunctor

instance (S T : Structure) : CoeFun (StructureFunctor S T) (λ F => S → T) := ⟨StructureFunctor.map⟩

variable {S T U V : Structure}

-- Restate the axioms as theorems about `congrArg`.

        theorem respectsSetoid (F : StructureFunctor S T) {α β   : S} {f g : α ≃ β} :
  f ≈ g → congrArg F f ≈ congrArg F g              := F.isFunctor.respectsSetoid
@[simp] theorem respectsComp   (F : StructureFunctor S T) {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  congrArg F (g • f) ≈ congrArg F g • congrArg F f := F.isFunctor.respectsComp f g
@[simp] theorem respectsId     (F : StructureFunctor S T) (α     : S) :
  congrArg F (id_ α) ≈ id'                         := F.isFunctor.respectsId   α
@[simp] theorem respectsInv    (F : StructureFunctor S T) {α β   : S} (f : α ≃ β) :
  congrArg F f⁻¹     ≈ (congrArg F f)⁻¹            := F.isFunctor.respectsInv  f



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
  α ≃ β → compMap F G α ≃ compMap F G β := λ f => congrArg G (congrArg F f)

theorem compCongrArgComp {F : StructureFunctor S T} {G : StructureFunctor T U} {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  compCongrArg F G (g • f) ≈ compCongrArg F G g • compCongrArg F G f :=
let h₁ : congrArg G (congrArg F (g • f)) ≈ congrArg G (congrArg F g • congrArg F f) :=
respectsSetoid G (respectsComp F f g);
let h₂ : congrArg G (congrArg F g • congrArg F f) ≈ congrArg G (congrArg F g) • congrArg G (congrArg F f) :=
respectsComp G (congrArg F f) (congrArg F g);
Setoid.trans h₁ h₂

theorem compCongrArgId   {F : StructureFunctor S T} {G : StructureFunctor T U} (α     : S) :
  compCongrArg F G (id_ α) ≈ id' :=
let h₁ : congrArg G (congrArg F (id_ α)) ≈ congrArg G id' := respectsSetoid G (respectsId F α);
let h₂ : congrArg G id' ≈ id' := respectsId G (id (F α));
Setoid.trans h₁ h₂

theorem compCongrArgInv  {F : StructureFunctor S T} {G : StructureFunctor T U} {α β   : S} (f : α ≃ β) :
  compCongrArg F G f⁻¹ ≈ (compCongrArg F G f)⁻¹ :=
let h₁ : congrArg G (congrArg F f⁻¹) ≈ congrArg G (congrArg F f)⁻¹ := respectsSetoid G (respectsInv F f);
let h₂ : congrArg G (congrArg F f)⁻¹ ≈ (congrArg G (congrArg F f))⁻¹ := respectsInv G (congrArg F f);
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
λ α => trans (congrArg G₁ (hF α)) (hG (F₂ α))

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
-- actually a functor in the sense of category theory.

structure DependentFunctor (F : StructureFunctor S T) (G : StructureFunctor S U) where
(cond {α β : S} : F α ≃ F β → G α ≃ G β)
[isFunctor      : IsIsomorphismFunctor F.map G.map cond]



-- If we interpret `≃` as equality, we can pretend that functors are just functions and define their
-- properties accordingly. Again, note that these definitions contain data.
-- For injectivity, this is equivalent to writing `∀ {α β}, F α ≃ F β → α ≃ β` with the additional
-- requirement that everything must respect setoid and isomorphism operations.

def Injective  (F : StructureFunctor S T) := DependentFunctor F idFun
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
{ map       := inverseElement F h,
  congrArg  := inverseElement.isUnique F h,
  isFunctor := { respectsSetoid := inverseElement.respectsSetoid,
                 respectsComp   := inverseElement.respectsComp,
                 respectsId     := inverseElement.respectsId,
                 respectsInv    := inverseElement.respectsInv } }

namespace inverse

def leftInv (F : StructureFunctor S T) (h : Bijective F) :
  FunExt (compFun F (inverse F h)) idFun :=
inverseElement.isInverse' F h

def rightInv (F : StructureFunctor S T) (h : Bijective F) :
  FunExt (compFun (inverse F h) F) idFun :=
inverseElement.isInverse F h

end inverse

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
λ α => trans (congrArg e.invFun (f.leftInv (e.toFun α))) (e.leftInv α)

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) : StructureEquiv S U :=
{ toFun    := compFun e.toFun  f.toFun,
  invFun   := compFun f.invFun e.invFun,
  leftInv  := transLeftInv e f,
  rightInv := transLeftInv (symm f) (symm e) }

-- We can build a `StructureEquiv` from a bijective functor.

def functorToEquiv {S T : Structure} (F : StructureFunctor S T) (h : Bijective F) : StructureEquiv S T :=
{ toFun    := F,
  invFun   := inverse F h,
  leftInv  := inverse.leftInv  F h,
  rightInv := inverse.rightInv F h }

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
-- diagram. The same could be said about HoTT.

namespace Forgetfulness

def toSetoidFunctor (S : Structure) : StructureFunctor S (setoidStructure S) :=
{ map       := id,
  congrArg  := toSetoidEquiv S,
  isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                 respectsComp   := λ _ _ => proofIrrel _ _,
                 respectsId     := λ _   => proofIrrel _ _,
                 respectsInv    := λ _   => proofIrrel _ _ } }

def SetoidStructureFunctor (S T : Structure) := StructureFunctor (setoidStructure S) (setoidStructure T)

def setoidFunctor {S T : Structure} (F : StructureFunctor S T) : SetoidStructureFunctor S T :=
{ map       := F.map,
  congrArg  := λ ⟨e⟩ => ⟨F.congrArg e⟩,
  isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                 respectsComp   := λ _ _ => proofIrrel _ _,
                 respectsId     := λ _   => proofIrrel _ _,
                 respectsInv    := λ _   => proofIrrel _ _ } }

namespace Classical

def setoidToSkeletonFunctor (S : Structure) : StructureFunctor (setoidStructure S) (skeletonStructure S) :=
{ map       := λ α => Quotient.mk α,
  congrArg  := λ e => Quotient.sound e,
  isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                 respectsComp   := λ _ _ => proofIrrel _ _,
                 respectsId     := λ _   => proofIrrel _ _,
                 respectsInv    := λ _   => proofIrrel _ _ } }

def toSkeletonFunctor (S : Structure) : StructureFunctor S (skeletonStructure S) :=
compFun (toSetoidFunctor S) (setoidToSkeletonFunctor S)

def SkeletonStructureFunctor (S T : Structure) := StructureFunctor (skeletonStructure S) (skeletonStructure T)

variable {S T : Structure}

def skeletonMap (F : SetoidStructureFunctor S T) : skeletonStructure S → skeletonStructure T :=
Quotient.lift (Quotient.mk ∘ F.map) (λ _ _ => Quotient.sound ∘ F.congrArg)

def skeletonCongrArg (F : SetoidStructureFunctor S T) {a b : skeletonStructure S} :
  a = b → skeletonMap F a = skeletonMap F b :=
congrArg (skeletonMap F)

def skeletonFunctor (F : SetoidStructureFunctor S T) : StructureFunctor (skeletonStructure S) (skeletonStructure T) :=
{ map       := skeletonMap F,
  congrArg  := skeletonCongrArg F,
  isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                 respectsComp   := λ _ _ => proofIrrel _ _,
                 respectsId     := λ _   => proofIrrel _ _,
                 respectsInv    := λ _   => proofIrrel _ _ } }

end Classical

end Forgetfulness

open Forgetfulness



-- We would like to use `StructureEquiv` as an equivalence in a `Structure` that can hold structures.
-- With an inductive definition of `Structure`, we could use it directly. However, with the
-- definition of `Structure` we are using, we need to make sure that all instances of `FunExt` inside
-- our equivalence are just propositions (bringing the equivalence down to the same level as `Equiv`
-- in mathlib).
--
-- This is where the `setoidFunctor` we just defined comes into play: If we replace the two functors
-- with the induced functors between the setoid structures, we get an equivalence that fulfills the
-- same role but where equivalence of two equivalences is just a proposition.

def SetoidStructureEquiv (S T : Structure) := StructureEquiv (setoidStructure S) (setoidStructure T)

namespace SetoidStructureEquiv

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

end SetoidStructureEquiv

open SetoidStructureEquiv



-- Using this definition of equivalence, now we can actually build a "universe" structure, or rather
-- one which behaves like a universe for all our purposes: The objects are actual structures (of a
-- lower Lean universe), but the equivalences do not contain any inner structure.
--
-- Note how, in the process of encoding a universe, we remained purely constructive but simulated
-- classical logic. This shows that constructive type theory and (a specific variant of) classical
-- set theory are really just two different points on the path from one universe to the next, and
-- that much of classical mathematics can be interpreted constructively (and vice versa, of course).

instance structureHasStructure : HasStructure Structure := ⟨structureEquiv⟩

def universeStructure : Structure := ⟨Structure⟩



-- When using `typeStructure` to encode `Sort u` as a `Structure` with equivalences given by `Equiv`,
-- the framework we have defined so far does not offer a way to transport an individual instance
-- `x : α` of a type `α : Sort u` along an encoded `Equiv`. Since the introductory description
-- contains precisely this operation, we need to provide an abstraction for it.
--
-- The `universeStructure` we have just defined enables us to do exactly that: The function
-- `instanceStructure`, which encodes a given Lean type as a `Structure` with equivalence given by
-- equality, is actually a functor from `typeStructure` to `universeStructure`. This functor
-- transports an `Equiv` between two types to a `StructureEquiv` between the corresponding instance
-- structures. And `StructureEquiv` provides the necessary operation of transporting an instance of
-- one structure to the other.
--
-- The benefit of this encoding is that `StructureEquiv` is much more general than the original
-- `Equiv` because many different objects can be encoded as instances of `Structure`.

--def typeToStructureFunctor : StructureFunctor typeStructure universeStructure :=
--{ map       := instanceStructure,
--  congrArg  := sorry,
--  isFunctor := sorry }



-- We can encode every dependent product _type_ as an _instance_ of `DependentProduct`.

-- TODO: finish and clean up

structure DependentProduct where
{α : Sort u}
(C : α → Sort v)

namespace DependentProduct

instance : CoeSort DependentProduct (Sort _) := ⟨λ ⟨C⟩ => ∀ x, C x⟩

def pi {α : Sort u} (C : α → Sort v) : DependentProduct := ⟨C⟩




end DependentProduct



-- After this tour across universes, we return to our original goal of automating the definition of
-- isomorphisms for arbitrary structures.

namespace BuildingBlocks

structure EncodedPiType where
(α : Structure)
(C : α → Sort v) -- TODO: (C : StructureFunctor α universeStructure), using typeToStructureFunctor

def EncodedDependentFunction (T : EncodedPiType) := ∀ x : T.α, T.C x

-- Every term of type `∀ x, C x` can be converted to an instance of `EncodedDependentFunction`:

def encodeDependentFunction {α : Sort u} [h : HasStructure α] {C : α → Sort v} (f : ∀ x, C x) :
  EncodedDependentFunction ⟨defaultStructure α, C⟩ := f

end BuildingBlocks
