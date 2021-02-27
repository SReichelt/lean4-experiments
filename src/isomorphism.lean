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
-- After determining the necessary axioms of this `Structure` type, the result is starting to look more
-- and more like a Rosetta stone that translates
-- * between different concepts of equivalence, isomorphism, and equality, but also
-- * between constructive dependent type theory and (a certain variant of) classical set theory:
--
-- In particular, while formalizing the "universe structure" which holds structures of a lower universe,
-- we encounter and leverage a "simulated" classical logic within our fully constructive formalization.
-- This classical logic becomes an integral part of the universe structure, or in other words constructive
-- type theory and classical set theory occur as just two different points on the path from one universe
-- to the next.
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



universes u v



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
instance (s : BundledSetoid) : HasEquiv s.α := ⟨s.s.r⟩

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

def equiv {U : Sort u} {R : GeneralizedRelation U} (α β : U) := (R α β).α

instance {U : Sort u} {R : GeneralizedRelation U} (α β : U) : HasEquiv (equiv α β) := ⟨(R α β).s.r⟩

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
--
-- Starting with the seven corresponding lemmas in `data.equiv.basic` of mathlib in Lean 3 (`symm_symm`,
-- `trans_refl`, etc.), reformulating them in terms of morphisms, and adding one missing case, we arrive
-- at the following list of axioms (with variables `α β γ δ : U`, and writing `α ≃ β` for `equiv α β`):
--
-- ` refl     : α ≃ α                           ` | `id`
-- ` symm     : α ≃ β → β ≃ α                   ` | `⁻¹`
-- ` trans    : α ≃ β → β ≃ γ → α ≃ γ           ` | `∘` (in reverse order)
-- ` assoc    (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f `
-- ` leftId   (f : α ≃ β)                         : id ∘ f    ≈ f             `
-- ` rightId  (f : α ≃ β)                         : f ∘ id    ≈ f             `
-- ` compInv  (f : α ≃ β) (g : β ≃ γ)             : (g ∘ f)⁻¹ ≈ f⁻¹ ∘ g⁻¹     `
-- ` leftInv  (f : α ≃ β)                         : f⁻¹ ∘ f   ≈ id            `
-- ` rightInv (f : α ≃ β)                         : f ∘ f⁻¹   ≈ id            `
-- ` invInv   (f : α ≃ β)                         : (f⁻¹)⁻¹   ≈ f             `
-- ` idInv                                        : id⁻¹      ≈ id            `
--
-- `assoc`, `leftId`, and `rightId` are simply the axioms of a category, and the remaining axioms add
-- inverses (whose existence is guaranteed by `symm` aka `⁻¹`) as first-class structure.
-- (If this seems to contradict the initial statement that we are describing a generalization of
-- isomorphism compared to category theory, note that we are defining a generalized _equivalence relation_,
-- not a generalized category.)
--
-- Note that we do not compare equivalences/isomorphisms for equality, but use the setoid equivalence we
-- just introduced.
--
-- Remark: Interestingly, all axioms can be regarded as simplification rules that enable equational
-- reasoning by transforming all possible terms into a canonical form (with the simplification for
-- associativity being the omission of parentheses). Besides making proofs trivial, this observation also
-- suggests an alternative formalization of the axioms in terms of a "simplify" function.

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
(assoc {α β γ δ : U} (f : M α β) (g : M β γ) (h : M γ δ) : h • (g • f) ≈ (h • g) • f)

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
(compInv  {α β : U} (f : M α β) (g : M β γ) : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹)
(leftInv  {α β : U} (f : M α β)             : f⁻¹ • f   ≈ id α)
(rightInv {α β : U} (f : M α β)             : f • f⁻¹   ≈ id β)
(invInv   {α β : U} (f : M α β)             : (f⁻¹)⁻¹   ≈ f)
(idInv    (α   : U)                         : (id α)⁻¹  ≈ id α)

instance isoEquiv (M : GeneralizedRelation U) [h : HasIsomorphisms M] : IsEquivalence M :=
⟨h.id, h.inv, h.comp⟩

end Morphisms

open Morphisms



-- In Lean, we can use proof irrelevance to define one instance that works for all ordinary equivalence
-- relations.

namespace PropEquiv

variable {α : Sort u} (r : α → α → Prop) [h : IsEquivalence (genRel r)]

instance propEquivHasComp : HasComp         (genRel r) := ⟨h.trans⟩
instance propEquivHasCmp  : HasComposition  (genRel r) := ⟨λ _ _ _ => proofIrrel _ _⟩
instance propEquivHasId   : HasId           (genRel r) := ⟨h.refl⟩
instance propEquivHasMor  : HasMorphisms    (genRel r) := ⟨λ _ => proofIrrel _ _, λ _ => proofIrrel _ _⟩
instance propEquivHasInv  : HasInv          (genRel r) := ⟨h.symm⟩
instance propEquivHasIso  : HasIsomorphisms (genRel r) := ⟨λ _ _ => proofIrrel _ _,
                                                           λ _ => proofIrrel _ _, λ _ => proofIrrel _ _,
                                                           λ _ => proofIrrel _ _, λ _ => proofIrrel _ _⟩

end PropEquiv

open PropEquiv



-- Combine everything into a single type class.

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
def equiv (α β : S) := (iso α β).α
infix:25 " ≃ " => equiv

instance (α β : S) : HasEquiv (equiv α β) := ⟨(iso α β).s.r⟩

def refl  (α     : S) : α ≃ α                 := (isEquiv S.U).refl α
def symm  {α β   : S} : α ≃ β → β ≃ α         := (isEquiv S.U).symm
def trans {α β γ : S} : α ≃ β → β ≃ γ → α ≃ γ := (isEquiv S.U).trans

instance hasCmp : HasComposition  (@iso S) := hasStructure.hasCmp
instance hasMor : HasMorphisms    (@iso S) := hasStructure.hasMor
instance hasIso : HasIsomorphisms (@iso S) := hasStructure.hasIso

def id_ (α : S) : α ≃ α := id__ α
def id' {α : S} := id_ α

        theorem assoc    {α β γ δ : S} (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h • (g • f) ≈ (h • g) • f := hasIso.assoc    f g h
@[simp] theorem leftId   {α β     : S} (f : α ≃ β)                         : id' • f   ≈ f             := hasIso.leftId   f
@[simp] theorem rightId  {α β     : S} (f : α ≃ β)                         : f • id'   ≈ f             := hasIso.rightId  f
@[simp] theorem compInv  {α β γ   : S} (f : α ≃ β) (g : β ≃ γ)             : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹     := hasIso.compInv  f g
@[simp] theorem leftInv  {α β     : S} (f : α ≃ β)                         : f⁻¹ • f   ≈ id'           := hasIso.leftInv  f
@[simp] theorem rightInv {α β     : S} (f : α ≃ β)                         : f • f⁻¹   ≈ id'           := hasIso.rightInv f
@[simp] theorem invInv   {α β     : S} (f : α ≃ β)                         : (f⁻¹)⁻¹   ≈ f             := hasIso.invInv   f
@[simp] theorem idInv    (α       : S)                                     : (id_ α)⁻¹ ≈ id'           := hasIso.idInv    α

def defaultStructure (U : Sort u) [h : HasStructure U] : Structure := ⟨U⟩
def instanceStructure (α : Sort u) := @defaultStructure α (instanceHasStructure α)
def setoidInstanceStructure (α : Sort u) [s : Setoid α] := @defaultStructure α (setoidHasStructure α)

end Structure

open Structure



-- We can "forget" the data held inside a `Structure` on two levels, obtaining modified instances of
-- `Structure`:
--
-- 1. We can coerce the equivalence to `Prop` to obtain a setoid structure. The result is on the same
--    level as an `Equiv` in mathlib, so this coercion preserves quite a lot of data.
--    In comments, we will write `setoidStructure S` as `S_≈`.
--
-- 2. In a classical setting, we can additionally take the quotient with respect to equivalence, obtaining
--    a "skeleton" structure where equivalence is equality.
--    In comments, we will write `skeletonStructure S` as `S/≃`.
--
-- Later, we will prove some properties of these operations.
--
-- Within this file, we coerce structures to setoids whenever we want to use structures as isomorphisms,
-- but we never use quotients. With an inductive version of `Structure`, we could keep all data instead.

namespace Forgetfulness

variable (S : Structure)

def SetoidEquiv (α β : S) := Nonempty (α ≃ β)
def transportToSetoid {α β : S} (e : α ≃ β) : SetoidEquiv S α β := ⟨e⟩
def setoidEquiv : Equivalence (SetoidEquiv S) :=
⟨λ α => ⟨Structure.refl α⟩, λ ⟨e⟩ => ⟨Structure.symm e⟩, λ ⟨e⟩ ⟨f⟩ => ⟨Structure.trans e f⟩⟩

instance structureToSetoid : Setoid S.U := ⟨SetoidEquiv S, setoidEquiv S⟩
def setoidStructure : Structure := setoidInstanceStructure S.U

def StructureQuotient := Quotient (structureToSetoid S)
instance quotientHasStructure : HasStructure (StructureQuotient S) := instanceHasStructure (StructureQuotient S)
def skeletonStructure : Structure := ⟨StructureQuotient S⟩

end Forgetfulness

open Forgetfulness



-- We want to define a map between two `Structure`s that is compatible with their equivalences.
-- In particular, the map should be equipped with a `transport` function that transports "relabeling"
-- operations as described in the introduction, i.e. equivalences. `transport` can also be regarded as a
-- substitution principle, or generally as a well-definedness condition for the map if we interpret `≃` as
-- equality.
--
-- `transport` must respect operations on isomorphisms. This turns the combination of `map` and `transport`
-- into a functor with the additional requirement that it must also preserve inverses, as those are an
-- integral part of our axiomatized structure. So first we give a more general definition of a functor,
-- split into the three pieces of structure that we are dealing with so we can potentially reuse it in
-- other contexts.

namespace Functors

variable {U : Sort u}                {V : Sort v}
         {X : GeneralizedRelation U} {Y : GeneralizedRelation V}
         (F  :              U     → V)
         (FF : ∀ {α β : U}, X α β → Y (F α) (F β))

-- This corresponds to `FF` also being a functor. With an inductive definition of `Structure`, the
-- definition of a functor would need to be recursive.
class IsSetoidFunctor where
(transportSetoid {α β : U} (f g : X α β) : f ≈ g → FF f ≈ FF g)

class IsCompositionFunctor [cmpX : HasComposition X] [cmpY : HasComposition Y]
  extends @IsSetoidFunctor U V X Y F FF where
(transportComp {α β γ : U} (f : X α β) (g : X β γ) : FF (g • f) ≈ FF g • FF f)

class IsMorphismFunctor [morX : HasMorphisms X] [morY : HasMorphisms Y]
  extends @IsCompositionFunctor U V X Y F FF morX.toHasComposition morY.toHasComposition where
(transportId (α : U) : FF (id__ α) ≈ id__ (F α))

class IsIsomorphismFunctor [isoX : HasIsomorphisms X] [isoY : HasIsomorphisms Y]
  extends @IsMorphismFunctor U V X Y F FF isoX.toHasMorphisms isoY.toHasMorphisms where
(transportInv {α β : U} (f : X α β) : FF f⁻¹ ≈ (FF f)⁻¹)

end Functors

open Functors



-- Now we define our specific version of a functor between structures.

structure StructureFunctor (S T : Structure) :=
(map                 : S     → T)
(transport {α β : S} : α ≃ β → map α ≃ map β)
[isFunctor           : IsIsomorphismFunctor map transport]

namespace StructureFunctor

instance (S T : Structure) : CoeFun (StructureFunctor S T) (λ F => S → T) := ⟨λ F => F.map⟩

variable {S T U : Structure}

-- The transport function can be understood as a substitution principle. Note that, like much of this
-- file, it is a definition, not a theorem, because it needs to preserve data.

def congrArg {α β : S} (F : StructureFunctor S T) : α ≃ β → F α ≃ F β := F.transport

-- Restate the axioms as theorems about `congrArg`.

instance isIsoFunctor    (F : StructureFunctor S T) : @IsIsomorphismFunctor S.U T.U iso iso F.map F.transport hasIso hasIso :=
F.isFunctor
instance isMorFunctor    (F : StructureFunctor S T) : @IsMorphismFunctor    S.U T.U iso iso F.map F.transport hasMor hasMor :=
(isIsoFunctor F).toIsMorphismFunctor
instance isCompFunctor   (F : StructureFunctor S T) : @IsCompositionFunctor S.U T.U iso iso F.map F.transport hasCmp hasCmp :=
(isMorFunctor F).toIsCompositionFunctor
instance isSetoidFunctor (F : StructureFunctor S T) : @IsSetoidFunctor      S.U T.U iso iso F.map F.transport               :=
(isCompFunctor F).toIsSetoidFunctor

def transportSetoidDef (F : StructureFunctor S T) :=
@IsSetoidFunctor.transportSetoid    S.U T.U iso iso F.map F.transport
def transportInvDef    (F : StructureFunctor S T) :=
@IsIsomorphismFunctor.transportInv  S.U T.U iso iso F.map F.transport hasIso hasIso (isIsoFunctor  F)
def transportIdDef     (F : StructureFunctor S T) :=
@IsMorphismFunctor.transportId      S.U T.U iso iso F.map F.transport hasMor hasMor (isMorFunctor  F)
def transportCompDef   (F : StructureFunctor S T) :=
@IsCompositionFunctor.transportComp S.U T.U iso iso F.map F.transport hasCmp hasCmp (isCompFunctor F)

@[simp] theorem transportSetoid (F : StructureFunctor S T) {α β   : S} (f g : α ≃ β) :
  f ≈ g → congrArg F f ≈ congrArg F g              := transportSetoidDef F f g
@[simp] theorem transportComp   (F : StructureFunctor S T) {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  congrArg F (g • f) ≈ congrArg F g • congrArg F f := transportCompDef   F f g
@[simp] theorem transportId     (F : StructureFunctor S T) (α     : S) :
  congrArg F (id_ α) ≈ id'                         := transportIdDef     F α
@[simp] theorem transportInv    (F : StructureFunctor S T) {α β   : S} (f : α ≃ β) :
  congrArg F f⁻¹     ≈ (congrArg F f)⁻¹            := transportInvDef    F f



-- We can define equivalence of functors by extensionality, using equivalence in `T` instead of equality.
-- Note that although writing `∀` instead of `Π` (as required by Lean 4) looks beautiful, it obscures
-- that this definition does not live in `Prop`.
-- This is an equivalence according to our definition, and it is compatible with isomorphisms via the
-- functor axioms, so we can use it to build an instance of `Structure` again.

def FunExt (F G : StructureFunctor S T) := ∀ α, F α ≃ G α

namespace FunExt

def funExtEquiv {F G : StructureFunctor S T} (φ ψ : FunExt F G) := ∀ α, φ α ≈ ψ α
instance funExtSetoid (F G : StructureFunctor S T) : Setoid (FunExt F G) := ⟨funExtEquiv, ⟨sorry, sorry, sorry⟩⟩
def funExt (F G : StructureFunctor S T) : BundledSetoid := ⟨FunExt F G⟩

instance funExtHasIso : HasIsomorphisms (@funExt S T) :=
{ comp     := λ φ ψ α => ψ α • φ α,
  assoc    := sorry,
  id       := λ F α => id_ (F α)
  leftId   := sorry,
  rightId  := sorry,
  inv      := λ φ α => (φ α)⁻¹
  compInv  := sorry,
  leftInv  := sorry,
  rightInv := sorry,
  invInv   := sorry,
  idInv    := sorry }

instance functorHasStructure : HasStructure (StructureFunctor S T) := ⟨funExt⟩
def functorStructure : Structure := ⟨StructureFunctor S T⟩

instance functorIsSetoid : Setoid (StructureFunctor S T) := structureToSetoid functorStructure
def functorSetoidStructure := setoidStructure (@functorStructure S T)
def functorSetoid : BundledSetoid := ⟨(@functorSetoidStructure S T).U⟩

end FunExt

open FunExt



-- Given this definition of equivalence of functors, it makes sense to define identity and composition and
-- prove that they are well-behaved with respect to equivalence.

def mapId             : S     → S                 := id
def transId {α β : S} : α ≃ β → mapId α ≃ mapId β := id

instance idIsFunctor (S : Structure) :
  @IsIsomorphismFunctor S.U S.U iso iso mapId transId hasIso hasIso :=
{ transportSetoid := λ f g h => h,
  transportComp   := λ f g   => sorry,
  transportId     := λ α     => sorry,
  transportInv    := λ f     => sorry }

def idFun : StructureFunctor S S := ⟨mapId, transId⟩

def mapComp   (F : StructureFunctor S T) (G : StructureFunctor T U)           :
  S     → U                             := G.map       ∘ F.map
def transComp (F : StructureFunctor S T) (G : StructureFunctor T U) {α β : S} :
  α ≃ β → mapComp F G α ≃ mapComp F G β := G.transport ∘ F.transport

instance compIsFunctor (F : StructureFunctor S T) (G : StructureFunctor T U) :
  @IsIsomorphismFunctor S.U U.U iso iso (mapComp F G) (transComp F G) hasIso hasIso :=
{ transportSetoid := λ f g h => sorry,
  transportComp   := λ f g   => sorry,
  transportId     := λ α     => sorry,
  transportInv    := λ f     => sorry }

def compFun (F : StructureFunctor S T) (G : StructureFunctor T U) : StructureFunctor S U :=
{ map       := mapComp       F G,
  transport := transComp     F G,
  isFunctor := compIsFunctor F G }

instance hasComp : HasComp        @functorSetoid := ⟨@compFun⟩
instance hasCmp  : HasComposition @functorSetoid := ⟨sorry⟩
instance hasId   : HasId          @functorSetoid := ⟨@idFun⟩
instance hasMor  : HasMorphisms   @functorSetoid := ⟨sorry, sorry⟩

-- If we interpret `≃` as equality, we can pretend that functors are just functions and define their
-- properties accordingly. Again, note that these definitions contain data.

def Injective  (F : StructureFunctor S T) := ∀ α β, F α ≃ F β → α ≃ β
def Surjective (F : StructureFunctor S T) := ∀ β, Σ α, F α ≃ β
def Bijective  (F : StructureFunctor S T) := Prod (Injective F) (Surjective F)

-- We can even build an inverse functor for any functor that is bijective according to this definition,
-- even though we do not assume classical logic. This works because the equivalences in `Structure` can
-- actually hold the data we are defining here. Note that if we were dealing with propositions and
-- using `∃` instead of `Σ`, obtaining the inverse functor would require (or be equivalent to) using
-- classical logic.
--
-- TODO: Apparently using `Nonempty` together with `Σ`, as we implicitly do below, is still constructive?
--
-- The inverse functor is unique (modulo equivalence, i.e. `FunExt`).

def arbitraryInverseElement (F : StructureFunctor S T) (h : Surjective F) (β : T) : S :=
Sigma.fst (h β)

def inverseElementIsInverse (F : StructureFunctor S T) (h : Surjective F) (β : T) :
  F (arbitraryInverseElement F h β) ≃ β :=
Sigma.snd (h β)

def inverse (F : StructureFunctor S T) (h : Bijective F) : StructureFunctor T S :=
{ map       := arbitraryInverseElement F h.snd,
  transport := sorry,  -- TODO, important: should work using inverseElementIsInverse, congrArg, and symm
  isFunctor := sorry }

end StructureFunctor

open StructureFunctor



-- A functor between two structures induces a functor between their setoid structures, and in the
-- classical setting also between their skeleton structures. More specifically, we have the following
-- commutative diagram (modulo equivalence defined on functors, i.e. `FunExt`), where all the horizontal
-- functors are `Bijective`:
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
  transport := transportToSetoid S,
  isFunctor := sorry }

def setoidToSkeletonFunctor (S : Structure) : StructureFunctor (setoidStructure S) (skeletonStructure S) :=
{ map       := λ α => Quotient.mk α,
  transport := λ e => Quotient.sound e,
  isFunctor := sorry }

def toSkeletonFunctor (S : Structure) := compFun (toSetoidFunctor S) (setoidToSkeletonFunctor S)

variable {S T : Structure} (F : StructureFunctor S T)

def setoidFunctor : StructureFunctor (setoidStructure S) (setoidStructure T) :=
{ map       := F.map,
  transport := λ ⟨e⟩ => ⟨F.transport e⟩,
  isFunctor := sorry }

def mapToSkeleton : skeletonStructure S → skeletonStructure T :=
Quotient.lift (Quotient.mk ∘ F.map) sorry

def transportToSkeleton {a b : skeletonStructure S} (h : a = b) :
  mapToSkeleton F a ≃ mapToSkeleton F b :=
Eq.subst (motive := λ x => mapToSkeleton F a ≃ mapToSkeleton F x) h (Structure.refl (mapToSkeleton F a))

def skeletonFunctor : StructureFunctor (skeletonStructure S) (skeletonStructure T) :=
{ map       := mapToSkeleton F,
  transport := transportToSkeleton F,
  isFunctor := sorry }

end Forgetfulness

open Forgetfulness



-- Based on the definition of a functor between two structures, we can define equivalence of two
-- structures in the same way that equivalence of types is defined in mathlib, except that we need to
-- replace equality of functors with an instance of `FunExt`. For the purpose of using the equivalence
-- to define a `Structure`, we need to make sure that this `FunExt` does not have any inner structure
-- beyond a setoid.
--
-- This is where the `setoidFunctor` we just defined comes into play: We can declare our equivalence
-- to be one between setoid structures. Then the functors contained in the equivalences are really
-- just functions, so we can compare them for equality.

structure LargeStructureEquiv (S T : Structure) where
(toFun    : StructureFunctor S T)
(invFun   : StructureFunctor T S)
(leftInv  : FunExt (compFun toFun invFun) idFun)
(rightInv : FunExt (compFun invFun toFun) idFun)

def StructureEquiv (S T : Structure) := LargeStructureEquiv (setoidStructure S) (setoidStructure T)

namespace StructureEquiv

def refl (S : Structure) : StructureEquiv S S :=
{ toFun    := idFun,
  invFun   := idFun,
  leftInv  := sorry,
  rightInv := sorry }

def symm {S T : Structure} (e : StructureEquiv S T) : StructureEquiv T S :=
{ toFun    := e.invFun,
  invFun   := e.toFun,
  leftInv  := e.rightInv,
  rightInv := e.leftInv }

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) : StructureEquiv S U :=
{ toFun    := compFun e.toFun  f.toFun,
  invFun   := compFun f.invFun e.invFun,
  leftInv  := sorry,
  rightInv := sorry }

def equivEquiv {S T : Structure} (φ ψ : StructureEquiv S T) := φ.toFun ≈ ψ.toFun ∧ φ.invFun ≈ ψ.invFun
instance equivSetoid (S T : Structure) : Setoid (StructureEquiv S T) := ⟨equivEquiv, ⟨sorry, sorry, sorry⟩⟩
def structureEquiv (S T : Structure) : BundledSetoid := ⟨StructureEquiv S T⟩

instance equivHasIso : HasIsomorphisms structureEquiv :=
{ comp     := trans,
  assoc    := sorry,
  id       := refl,
  leftId   := sorry,
  rightId  := sorry,
  inv      := symm,
  compInv  := sorry,
  leftInv  := sorry,
  rightInv := sorry,
  invInv   := sorry,
  idInv    := sorry }

-- We can build a `StructureEquiv` from a bijective functor.

def functorToEquiv {S T : Structure} (F : StructureFunctor S T) (h : Bijective F) : StructureEquiv S T :=
{ toFun    := setoidFunctor F,
  invFun   := setoidFunctor (inverse F h),
  leftInv  := sorry,
  rightInv := sorry }

end StructureEquiv

open StructureEquiv



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
--  transport := sorry,
--  isFunctor := sorry }



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
