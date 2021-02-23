--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- In this file, written for Lean 4, we introduce a generalization of the concept of "isomorphism" beyond
-- universal algebra and category theory. It axiomatically captures the notion of "equality up to
-- relabeling" in a composable way, such that it can be applied in a computational way to all structures
-- that can be defined in type theory -- ideally without having to write a single proof for any particular
-- structure. Automatic generation of richer structure such as morphism also seems within reach.
--
-- The initial idea behind this formalization is actually quite simple: Frequently in mathematics, we are
-- dealing with a set/type together with some structure on it; in Lean this is most commonly realized as a
-- type class `C : Type u → Type v`. If `α` is a type with an instance `x : C α` of `C`, we define its
-- "bundled structure" to be `⟨α, x⟩ : Σ α, C α`. For such bundled structures, we are able to give a
-- definition of "isomorphism" as follows:
--
-- * Given an `e : Equiv α β`, i.e. a "relabeling" operation that maps from one carrier type to another,
--   we need to correspondingly relabel instances of `C α` to `C β`, i.e. transport them along `e`. We
--   axiomatize this as a `transport` map which takes `e` to an `f : Equiv (C α) (C β)` in a way that
--   commutes with operations on the `Equiv`s.
-- 
-- * Then we can define an isomorphism between two bundled instances `⟨α, x⟩ ⟨β, y⟩ : Σ α, C α` to be an
--   `e : Equiv α β` together with a proof that the equivalence given by `transport e` maps `x` to `y`.
--   In other words, we simply require the `transport` operation to correctly apply the given relabeling
--   operation on the right-hand side of the bundled instance.
--
-- Although this applies to a lot of basic structures, this initial version does not compose very well, as
-- in Lean it is not the case that everything is a type. Note that we _can_ compose structures, e.g. build
-- a group structure from a semigroup structure and then define an appropriate `transport` map for groups.
-- However, in this example we would really like to define the `transport` map for groups as a composition
-- of the already-defined map for semigroups with another map that only takes care of the additional
-- structure.
--
-- In general terms, we already have that any `⟨α, ⟨x₁, x₂⟩⟩` can be an instance of a bundled structure
-- (as it is just a special case of `⟨α, x⟩`), but we would also like to treat the same structure as
-- `⟨⟨α, x₁⟩, x₂⟩`, which would not type-check because `⟨α, x₁⟩` is not a type.
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
-- This leads to the insight that we first need to abstract over different variants of equality and
-- equivalence, and then define everything in terms of that abstraction. In a way, the resulting theory can
-- be regarded as a very abstract characterization of what equivalence really means. For example, the
-- `transport` map mentioned at the beginning can also be understood as either a special kind of functor or
-- as a substitution operation if equivalence is interpreted as equality.
--
-- Using the generalized framework, we can not only compose bundled structures as described above, but we
-- can actually define how to build arbitrary structures in terms of basic building blocks corresponding to
-- all fundamental type constructors. This way, we can really get a definition of "isomorphism" for any
-- structure that can be defined.
--
-- All of this seems strongly related to HoTT but does not use univalence in any way. We give some pointers
-- to possible connections to other theories below. Mathematically some of this might also be a reinvention
-- of existing ideas, but there seems to be some novelty in the combination of these ideas.


-- TODO:
-- * Finish basic definitions.
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



universes u v u' v'



-- We want to formalize a very general "structure with equivalences", so we start with a very basic
-- abstraction for something that looks like an equivalence relation except that the codomain is `Sort u`
-- instead of `Prop`.
-- Even though `α`, `β` are not necessarily types, we write them in this way to capture the fact that
-- the canonical instance in Lean is `Equiv` (which we don't reference to keep this file self-contained).

class IsEquivalence {U : Sort u} (equiv : U → U → Sort v) where
(refl  (α     : U) : equiv α α)
(symm  {α β   : U} : equiv α β → equiv β α)
(trans {α β γ : U} : equiv α β → equiv β γ → equiv α γ)

def ProofEq (p : Prop) := λ h₁ h₂ : p => True

instance proofEquiv {p : Prop}                                          : IsEquivalence (ProofEq p) := ⟨λ _ => trivial, λ _ => trivial, λ _ _ => trivial⟩
instance iffEquiv                                                       : IsEquivalence Iff         := ⟨Iff.refl,       Iff.symm,       Iff.trans⟩
instance eqEquiv    {α : Sort u}                                        : IsEquivalence (@Eq α)     := ⟨Eq.refl,        Eq.symm,        Eq.trans⟩
instance relEquiv   {α : Sort u} {r : α → α → Prop} (e : Equivalence r) : IsEquivalence r           := ⟨e.refl,         e.symm,         e.trans⟩

class HasEquivalence (U : Sort u) where
(equiv   : U → U → Sort v)
[isEquiv : IsEquivalence equiv]

instance (U : Sort u) [hasEquiv : HasEquivalence U] : IsEquivalence hasEquiv.equiv := hasEquiv.isEquiv

instance proofsHaveEquiv  {p : Prop}                  : HasEquivalence p    := ⟨ProofEq p⟩
instance propHasEquiv                                 : HasEquivalence Prop := ⟨Iff⟩
instance instanceHasEquiv (α : Sort u)                : HasEquivalence α    := ⟨Eq⟩
def      setoidHasEquiv   {α : Sort u} (s : Setoid α) : HasEquivalence α    := @HasEquivalence.mk α s.r (relEquiv s.iseqv)



-- We would also like to be able to manipulate equivalences, and we need them to behave like isomorphisms
-- when doing so, with `refl` as the identity, `symm` as inverse, and `trans` as composition. Therefore,
-- we add axioms for them that are the same as those of a category (for `trans` and `refl`) but with the
-- addition of inverses as first-class structure (for `symm`).
--
-- As currently written, the axioms contain equality comparisons on isomorphisms. However, later we will
-- have isomorphisms where this equality is actually replaced by an equivalence, i.e. it contains data.
-- Of course, it is possible to reformulate the axioms in a way that abstracts over equality, but it
-- turns out that
-- * it breaks type class inference and simplification in many cases,
-- * in Lean we don't benefit from it at all, and
-- * there is potentially a computational interpretation despite the use of equality.
--
-- The axioms were actually inspired by the seven corresponding lemmas in `data.equiv.basic` of Mathlib
-- in Lean 3, but reformulated in terms of operations on morphisms (and with one missing axiom added).

class HasCompositionOp {U : Sort u} (M : U → U → Sort v) where
(comp  {α β γ : U} : M α β → M β γ → M α γ)

-- Note that we use a nonstandard order in `HasCompositionOp.comp` so that it directly matches
-- `IsEquivalence.trans`. When using `•` notation (which we use to avoid clashing with `∘`), we reverse
-- the order to conform to function/morphism/functor composition.
def revComp {U : Sort u} {M : U → U → Sort v} [h : HasCompositionOp M] {α β γ : U} (g : M β γ) (f : M α β) :=
@HasCompositionOp.comp U M h α β γ f g
infixr:90 " • " => revComp

class HasComposition {U : Sort u} (M : U → U → Sort v) extends HasCompositionOp M where
(assoc {α β γ δ : U} (f : M α β) (g : M β γ) (h : M γ δ) : h • (g • f) = (h • g) • f)

class HasId {U : Sort u} (M : U → U → Sort v) extends HasComposition M where
(id (α : U) : M α α)

def id__ {U : Sort u} {M : U → U → Sort v} [h : HasId M] (α : U) := @HasId.id U M h α

class HasMorphisms {U : Sort u} (M : U → U → Sort v) extends HasId M where
(leftId  {α β : U} (f : M α β) : id β • f = f)
(rightId {α β : U} (f : M α β) : f • id α = f)

class HasInv {U : Sort u} (M : U → U → Sort v) extends HasMorphisms M where
(inv {α β : U} : M α β → M β α)

def inv {U : Sort u} {M : U → U → Sort v} [h : HasInv M] {α β : U} (f : M α β) := @HasInv.inv U M h α β f 
postfix:10000 "⁻¹"  => inv

class HasIsomorphisms {U : Sort u} (M : U → U → Sort v) extends HasInv M where
(compInv  {α β : U} (f : M α β) (g : M β γ) : (g • f)⁻¹ = f⁻¹ • g⁻¹)
(leftInv  {α β : U} (f : M α β)             : f⁻¹ • f = id α)
(rightInv {α β : U} (f : M α β)             : f • f⁻¹ = id β)
(invInv   {α β : U} (f : M α β)             : (f⁻¹)⁻¹ = f)
(idInv    (α   : U)                         : (id α)⁻¹ = id α)

-- Isomorphisms in `Prop` are trivial in Lean, so we can define one instance that works for all ordinary
-- equivalence relations such as those defined above.

instance propEquivHasCompOp {U : Sort u} (equiv : U → U → Prop) [isEquiv : IsEquivalence equiv] : HasCompositionOp equiv :=
⟨isEquiv.trans⟩
instance propEquivHasComp   {U : Sort u} (equiv : U → U → Prop) [isEquiv : IsEquivalence equiv] : HasComposition   equiv :=
⟨λ _ _ _ => proofIrrel _ _⟩
instance propEquivHasId     {U : Sort u} (equiv : U → U → Prop) [isEquiv : IsEquivalence equiv] : HasId            equiv :=
⟨isEquiv.refl⟩
instance propEquivHasMor    {U : Sort u} (equiv : U → U → Prop) [isEquiv : IsEquivalence equiv] : HasMorphisms     equiv :=
⟨λ _ => proofIrrel _ _, λ _ => proofIrrel _ _⟩
instance propEquivHasInv    {U : Sort u} (equiv : U → U → Prop) [isEquiv : IsEquivalence equiv] : HasInv           equiv :=
⟨isEquiv.symm⟩
instance propEquivHasIso    {U : Sort u} (equiv : U → U → Prop) [isEquiv : IsEquivalence equiv] : HasIsomorphisms  equiv :=
⟨λ _ _ => proofIrrel _ _, λ _ => proofIrrel _ _, λ _ => proofIrrel _ _, λ _ => proofIrrel _ _, λ _ => proofIrrel _ _⟩

instance setoidHasIso {α : Sort u} (s : Setoid α) : HasIsomorphisms (@HasEquivalence.equiv α (setoidHasEquiv s)) :=
@propEquivHasIso α s.r (relEquiv s.iseqv)



-- Combine everything into a single type class.

class HasEquivalenceStructure (U : Sort u) extends HasEquivalence U where
[hasIso : HasIsomorphisms equiv]

instance isEquiv (U : Sort u) [hasEq : HasEquivalenceStructure U] : IsEquivalence   hasEq.equiv := hasEq.isEquiv
instance hasComp (U : Sort u) [hasEq : HasEquivalenceStructure U] : HasComposition  hasEq.equiv := hasEq.hasIso.toHasComposition
instance hasMor  (U : Sort u) [hasEq : HasEquivalenceStructure U] : HasMorphisms    hasEq.equiv := hasEq.hasIso.toHasMorphisms
instance hasIso  (U : Sort u) [hasEq : HasEquivalenceStructure U] : HasIsomorphisms hasEq.equiv := hasEq.hasIso

instance equivalenceStructure (U : Sort u) [hasEquiv : HasEquivalence U] [hasIso : HasIsomorphisms hasEquiv.equiv] : HasEquivalenceStructure U :=
{ equiv   := hasEquiv.equiv,
  isEquiv := hasEquiv.isEquiv,
  hasIso  := hasIso }

def equality {α : Sort u} := @equivalenceStructure α (instanceHasEquiv α) (propEquivHasIso Eq)

instance setoidEquivalenceStructure {α : Sort u} (s : Setoid α) : HasEquivalenceStructure α :=
@equivalenceStructure α (setoidHasEquiv s) (setoidHasIso s)



-- Now we put everything together to define our general "structure with equivalence". Concrete instances are
-- any `Type u` with `Equiv` as equivalence, any `α : Type u` with `Eq` as equivalence, and so on, but also
-- a lot of structures we are going to define below.
--
-- Ideally, the domain of `equiv` should actually not be `Sort v` but `Structure` itself, i.e. the
-- equivalences should be allowed to have internal structure. However, that would require us to define
-- `Structure` mutually with declaring it as an instance of `HasIsomorphismStructure`, which seems
-- difficult or impossible in Lean. So at least for the moment, we just forget inner structure at a
-- carefully chosen point.
--
-- If we are interested in recovering computational properties, one way to do it would be to generate code
-- that creates copies of the definition up to any desired level of internal structure.
-- A wild guess: Can this be used to obtain what has been called a "computational interpretation of
-- univalence"? More specifically:
-- * In another theorem prover (e.g. Agda?) it may be possible to actually construct the inductive version of
--   this type, eliminating the need to forget inner structure and thus making everything fully constructive.
-- * Failing that, being able to remain constructive up to an arbitrary level seems like it might also
--   qualify.
-- * Or maybe in HoTT, using equality at the inner level is actually OK if we have a computational
--   interpretation that applies to any given individual universe level?
--
-- Side note: In HLM, the logic implemented for the Slate theorem prover, the most fundamental concept is a
-- "set," but sets in HLM must be understood more like sets in Lean than sets in axiomatic set theory. An
-- HLM set is essentially a type with an equality (following something like Cantor's original ideas instead
-- of ZFC), and `Structure` is precisely the internalization of this concept in type theory.

structure Structure where
(U     : Sort u)
[hasEq : HasEquivalenceStructure U]

namespace Structure

instance : CoeSort Structure (Sort u) := ⟨λ S => S.U⟩

variable {S : Structure}

def equiv := S.hasEq.equiv
infix:25 " ≃ " => equiv

instance isEquiv   : IsEquivalence    (@equiv S) := S.hasEq.isEquiv
instance hasCompOp : HasCompositionOp (@equiv S) := S.hasEq.hasIso.toHasCompositionOp
instance hasComp   : HasComposition   (@equiv S) := S.hasEq.hasIso.toHasComposition
instance hasId     : HasId            (@equiv S) := S.hasEq.hasIso.toHasId
instance hasMor    : HasMorphisms     (@equiv S) := S.hasEq.hasIso.toHasMorphisms
instance hasInv    : HasInv           (@equiv S) := S.hasEq.hasIso.toHasInv
instance hasIso    : HasIsomorphisms  (@equiv S) := S.hasEq.hasIso

def refl  (α     : S) : α ≃ α                 := isEquiv.refl α
def symm  {α β   : S} : α ≃ β → β ≃ α         := isEquiv.symm
def trans {α β γ : S} : α ≃ β → β ≃ γ → α ≃ γ := isEquiv.trans

def id_ (α : S) : α ≃ α := id__ α
def id' {α : S} := id_ α

        theorem assoc    {α β γ δ : S} (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h • (g • f) = (h • g) • f := hasIso.assoc    f g h
@[simp] theorem leftId   {α β     : S} (f : α ≃ β)                         : id' • f = f               := hasIso.leftId   f
@[simp] theorem rightId  {α β     : S} (f : α ≃ β)                         : f • id' = f               := hasIso.rightId  f
@[simp] theorem compInv  {α β γ   : S} (f : α ≃ β) (g : β ≃ γ)             : (g • f)⁻¹ = f⁻¹ • g⁻¹     := hasIso.compInv  f g
@[simp] theorem leftInv  {α β     : S} (f : α ≃ β)                         : f⁻¹ • f = id'             := hasIso.leftInv  f
@[simp] theorem rightInv {α β     : S} (f : α ≃ β)                         : f • f⁻¹ = id'             := hasIso.rightInv f
@[simp] theorem invInv   {α β     : S} (f : α ≃ β)                         : (f⁻¹)⁻¹ = f               := hasIso.invInv   f
@[simp] theorem idInv    (α       : S)                                     : (id_ α)⁻¹ = id'           := hasIso.idInv    α

def defaultStructure (U : Sort u) [hasEq : HasEquivalenceStructure U] : Structure := @Structure.mk U hasEq
def setoidInstanceStructure {α : Sort u} (s : Setoid α) := @defaultStructure α (setoidEquivalenceStructure s)

-- For reference, here is the complete list of axioms for an `S : Structure`, aligned to highlight
-- the two different points of view:
--
-- ` refl     (α       : S) : α ≃ α                 `  `id_ α` / `id'`
-- ` symm     {α β     : S} : α ≃ β → β ≃ α         `  `⁻¹`
-- ` trans    {α β γ   : S} : α ≃ β → β ≃ γ → α ≃ γ `  `•` (in reverse order)
-- ` assoc    {α β γ δ : S}                            (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h • (g • f) = (h • g) • f `
-- ` leftId   {α β     : S}                            (f : α ≃ β)                         : id' • f   = f             `
-- ` rightId  {α β     : S}                            (f : α ≃ β)                         : f • id'   = f             `
-- ` compInv  {α β γ   : S}                            (f : α ≃ β) (g : β ≃ γ)             : (g • f)⁻¹ = f⁻¹ • g⁻¹     `
-- ` leftInv  {α β     : S}                            (f : α ≃ β)                         : f⁻¹ • f   = id'           `
-- ` rightInv {α β     : S}                            (f : α ≃ β)                         : f • f⁻¹   = id'           `
-- ` invInv   {α β     : S}                            (f : α ≃ β)                         : (f⁻¹)⁻¹   = f             `
-- ` idInv    (α       : S)                                                                : (id_ α)⁻¹ = id'           `
--
-- Note how the axioms can actually be understood as simplification rules that enable equational
-- reasoning by transforming all possible terms into a canonical form (with the simplification for
-- associativity being the omission of parentheses). Besides making all proofs about them trivial, maybe
-- it also points to a constructive interpretation of the axioms as functions.

end Structure

open Structure



-- We want to define a map between two `Structure` that is compatible with their equivalences.
-- In particular, the map should be equipped with a `transport` function that transports "relabeling"
-- operations as described in the introduction, i.e. equivalences. `transport` can also be regarded as a
-- substitution principle, or generally as a well-definedness condition for the map if we interpret `≃` as
-- equality.
--
-- `transport` must respect operations on isomorphisms. This turns the combination of `map` and `transport`
-- into a functor with the additional requirement that it must also preserve inverses, as those are an
-- integral part of our axiomatized structure. So first we give a more general definition of a functor
-- (split into the three pieces of structure that we are dealing with, so we can potentially reuse it in
-- other contexts).

class IsCompositionFunctor {U : Sort u} {V : Sort v} {X : U → U → Sort u'} {Y : V → V → Sort v'}
  [compX : HasComposition X] [compY : HasComposition Y]
  (F : U → V) (FF : ∀ {α β : U}, X α β → Y (F α) (F β))
  where
(transportComp {α β γ : U} (f : X α β) (g : X β γ) : FF (g • f) = FF g • FF f)

class IsMorphismFunctor {U : Sort u} {V : Sort v} {X : U → U → Sort u'} {Y : V → V → Sort v'}
  [morX : HasMorphisms X] [morY : HasMorphisms Y]
  (F : U → V) (FF : ∀ {α β : U}, X α β → Y (F α) (F β))
  extends @IsCompositionFunctor U V X Y morX.toHasComposition morY.toHasComposition F FF
  where
(transportId (α : U) : FF (id__ α) = id__ (F α))

class IsIsomorphismFunctor {U : Sort u} {V : Sort v} {X : U → U → Sort u'} {Y : V → V → Sort v'}
  [isoX : HasIsomorphisms X] [isoY : HasIsomorphisms Y]
  (F : U → V) (FF : ∀ {α β : U}, X α β → Y (F α) (F β))
  extends @IsMorphismFunctor U V X Y isoX.toHasMorphisms isoY.toHasMorphisms F FF
  where
(transportInv {α β : U} (f : X α β) : FF f⁻¹ = (FF f)⁻¹)

structure StructureFunctor (S T : Structure) :=
(map                 : S     → T)
(transport {α β : S} : α ≃ β → map α ≃ map β)
[isFunctor           : IsIsomorphismFunctor map transport]

namespace StructureFunctor

instance (S T : Structure) : CoeFun (StructureFunctor S T) (λ F => S.U → T.U) := ⟨λ F => F.map⟩

variable {S T U : Structure}

-- The transport function can be understood as a substitution principle. Note that, like much of this
-- file, it is a definition, not a theorem, because it needs to preserve structure.

def congrArg {α β : S} (F : StructureFunctor S T) : α ≃ β → F α ≃ F β := F.transport

-- Restate the axioms as theorems about `congrArg`.

instance isIsoFunctor  (F : StructureFunctor S T) : @IsIsomorphismFunctor S.U T.U equiv equiv hasIso  hasIso  F.map F.transport :=
F.isFunctor
instance isMorFunctor  (F : StructureFunctor S T) : @IsMorphismFunctor    S.U T.U equiv equiv hasMor  hasMor  F.map F.transport :=
@IsIsomorphismFunctor.toIsMorphismFunctor S.U T.U equiv equiv hasIso hasIso F.map F.transport (isIsoFunctor F)
instance isCompFunctor (F : StructureFunctor S T) : @IsCompositionFunctor S.U T.U equiv equiv hasComp hasComp F.map F.transport :=
@IsMorphismFunctor.toIsCompositionFunctor S.U T.U equiv equiv hasMor hasMor F.map F.transport (isMorFunctor F)

def transportInvDef  (F : StructureFunctor S T) :=
@IsIsomorphismFunctor.transportInv  S.U T.U equiv equiv hasIso  hasIso  F.map F.transport (isIsoFunctor  F)
def transportIdDef   (F : StructureFunctor S T) :=
@IsMorphismFunctor.transportId      S.U T.U equiv equiv hasMor  hasMor  F.map F.transport (isMorFunctor  F)
def transportCompDef (F : StructureFunctor S T) :=
@IsCompositionFunctor.transportComp S.U T.U equiv equiv hasComp hasComp F.map F.transport (isCompFunctor F)

@[simp] theorem transportComp (F : StructureFunctor S T) {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  congrArg F (g • f) = congrArg F g • congrArg F f := transportCompDef F f g
@[simp] theorem transportId   (F : StructureFunctor S T) (α     : S) :
  congrArg F (id_ α) = id'                         := transportIdDef   F α
@[simp] theorem transportInv  (F : StructureFunctor S T) {α β   : S} (f : α ≃ β) :
  congrArg F f⁻¹     = (congrArg F f)⁻¹            := transportInvDef  F f

-- We can define equivalence of functors by extensionality, using equivalence in `T` instead of equality.
-- Note that despite the beautiful but misleading use of `∀`, this definition does not live in `Prop`.
-- This is an equivalence according to our definition, and it is compatible with isomorphisms via the
-- functor axioms, so we can use it to build an instance of `Structure` again.

def FunExt (F G : StructureFunctor S T) := ∀ α, F α ≃ G α

instance funExtIsEquiv : IsEquivalence (@FunExt S T) :=
{ refl  := λ F   α => refl (F α),
  symm  := λ φ   α => symm (φ α),
  trans := λ φ ψ α => trans (φ α) (ψ α) }

instance hasEquiv : HasEquivalence (StructureFunctor S T) := ⟨FunExt⟩

instance funExtHasIso : HasIsomorphisms (@FunExt S T) :=
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

instance functorHasEq : HasEquivalenceStructure (StructureFunctor S T) :=
-- Why can't we just write `⟨⟩` here?
{ equiv   := FunExt,
  isEquiv := funExtIsEquiv,
  hasIso  := funExtHasIso }

def functorStructure (S T : Structure) : Structure := 
-- Why can't we just write `⟨StructureFunctor S T⟩` here?
{ U     := StructureFunctor S T,
  hasEq := functorHasEq }

-- Given this definition of equivalence of functors, it makes sense to define identity and composition and
-- prove that they are well-behaved with respect to equivalence.

def mapId             : S     → S                 := id
def transId {α β : S} : α ≃ β → mapId α ≃ mapId β := id

instance idIsFunctor (S : Structure) :
  @IsIsomorphismFunctor S.U S.U equiv equiv hasIso hasIso mapId transId :=
{ transportComp := λ f g => rfl,
  transportId   := λ α   => rfl,
  transportInv  := λ f   => rfl }

def idFun : StructureFunctor S S := ⟨mapId, transId⟩

def mapComp   (F : StructureFunctor S T) (G : StructureFunctor T U)           :
  S     → U                             := G.map       ∘ F.map
def transComp (F : StructureFunctor S T) (G : StructureFunctor T U) {α β : S} :
  α ≃ β → mapComp F G α ≃ mapComp F G β := G.transport ∘ F.transport

instance compIsFunctor (F : StructureFunctor S T) (G : StructureFunctor T U) :
  @IsIsomorphismFunctor S.U U.U equiv equiv hasIso hasIso (mapComp F G) (transComp F G) :=
{ transportComp := λ f g => sorry,
  transportId   := λ α   => sorry,
  transportInv  := λ f   => sorry }

def compFun (F : StructureFunctor S T) (G : StructureFunctor T U) : StructureFunctor S U :=
{ map       := mapComp       F G,
  transport := transComp     F G,
  isFunctor := compIsFunctor F G }

instance hasComp : HasCompositionOp StructureFunctor := ⟨compFun⟩

-- If we interpret `≃` as equality, we can pretend that functors are just functions and define their
-- properties accordingly. Again, note that these definitions contain data.

def Injective  (F : StructureFunctor S T) := ∀ α β, F α ≃ F β → α ≃ β
def Surjective (F : StructureFunctor S T) := ∀ β, Σ α, F α ≃ β
def Bijective  (F : StructureFunctor S T) := Prod (Injective F) (Surjective F)

-- We can even build an inverse functor for any functor that is bijective according to this definition,
-- even though we do not assume classical logic. This works because the equivalences in
-- `Structure` can actually hold the data we are defining here. The inverse functor is unique
-- (modulo equivalence).

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



-- We can forget the structure held inside a `Structure` on two levels, obtaining modified instances of
-- `Structure` via functors that are actually bijective according to the definition above.
--
-- 1. We can coerce the equivalence to `Prop` to obtain a setoid structure. The result is on the same
--    level as an `Equiv` in Mathlib, so this coercion preserves quite a lot of data.
--    In comments, we will write `setoidStructure S` as `S_≈`.
--
-- 2. In a classical setting, we can additionally take the quotient with respect to equivalence, obtaining
--    a "skeleton" structure where equivalence is equality.
--    In comments, we will write `skeletonStructure S` as `S/≃`.
--
-- We currently use skeleton structures whenever we need to make sure that two objects depending on
-- structures can be compared for equality. We could use setoid structures instead if we replaced the
-- equalities in the axioms of `Structure` with equivalence relations. With an inductive version
-- of `Structure`, we would not need to forget any structure.

namespace Forgetfulness

def SetoidEquiv {S : Structure} (α β : S) := Nonempty (α ≃ β)
def transportToSetoid {S : Structure} {α β : S} (e : α ≃ β) : SetoidEquiv α β := ⟨e⟩
def setoidEquiv {S : Structure} : Equivalence (@SetoidEquiv S) := ⟨λ α => ⟨refl α⟩, λ ⟨e⟩ => ⟨symm e⟩, λ ⟨e⟩ ⟨f⟩ => ⟨trans e f⟩⟩

instance structureToSetoid (S : Structure) : Setoid S.U := ⟨SetoidEquiv, setoidEquiv⟩
def setoidStructure (S : Structure) := Structure.setoidInstanceStructure (structureToSetoid S)

def toSetoidFunctor (S : Structure) : StructureFunctor S (setoidStructure S) :=
{ map       := id,
  transport := transportToSetoid,
  isFunctor := sorry }

def StructureQuotient (S : Structure) := Quotient (structureToSetoid S)
def skeletonStructure (S : Structure) := @Structure.defaultStructure (StructureQuotient S) equality

def setoidToSkeletonFunctor (S : Structure) : StructureFunctor (setoidStructure S) (skeletonStructure S) :=
{ map       := λ α => Quotient.mk α,
  transport := λ e => Quotient.sound e,
  isFunctor := sorry }

def toSkeletonFunctor (S : Structure) := setoidToSkeletonFunctor S • toSetoidFunctor S



-- A functor between two structures induces a functor between their setoid structures, and in the
-- classical setting also between their skeleton structures. More specifically, we have the following
-- commutative diagram (modulo equivalence defined on functors), where all the horizontal functors are
-- bijective (also modulo equivalence):
--
--                      `S` -≅--> `S_≈` -≅-> `S/≃`
--                       |          |          |
--                       |          |          |
--                       v          v          v
--                      `T` -≅--> `T_≈` -≅-> `T/≃`
--
--     universe level:  u+n         u          0, at least conceptually
--
-- This can be understood as the reason why isomorphism can generally be identified with equality: In all
-- operations that preserve structure, we can take the quotient with respect to equivalence/isomorphism
-- and work on the quotient structures. It also suggests a reason why mathematicians are usually
-- unconcerned about universe issues (rightly so, apparently).
--
-- The HLM logic implemented in Slate can be understood as completely living on the right side of this
-- diagram. The same could be said about HoTT.

variable {S T : Structure}

def setoidFunctor (F : StructureFunctor S T) : StructureFunctor (setoidStructure S) (setoidStructure T) :=
{ map       := F.map,
  transport := λ ⟨e⟩ => ⟨F.transport e⟩,
  isFunctor := sorry }

def mapToSkeleton (F : StructureFunctor S T) : skeletonStructure S → skeletonStructure T :=
Quotient.lift (Quotient.mk ∘ F.map) sorry

def transportToSkeleton (F : StructureFunctor S T) {a b : skeletonStructure S} (h : a = b) :
  mapToSkeleton F a ≃ mapToSkeleton F b :=
Eq.subst (motive := λ x => mapToSkeleton F a ≃ mapToSkeleton F x) h (refl (mapToSkeleton F a))

def skeletonFunctor (F : StructureFunctor S T) : StructureFunctor (skeletonStructure S) (skeletonStructure T) :=
{ map       := mapToSkeleton F,
  transport := transportToSkeleton F,
  isFunctor := sorry }

end Forgetfulness

open Forgetfulness



-- Based on the definition of a functor between two structures, we can define equivalence of two
-- structures in the same way that equivalence of types is defined in Mathlib, except that we need to
-- replace equality on functors with an instance of `FunExt`.
--
-- We are actually defining equivalence of structures mainly for the purpose of using it as an
-- equivalence within a `Structure` itself, completing the round-trip. However, since the isomorphism
-- axioms of `Structure` are based on equality, we need to make sure that we can safely compare two
-- `Structure`s for equality.
--
-- This is where the `skeletonFunctor` we just defined comes into play: We can declare our equivalence
-- to be one between skeleton structures. Then the functors contained in the equivalences are really
-- just functions, so we can compare them for equality.

structure LargeStructureEquiv (S T : Structure) where
(toFun    : StructureFunctor S T)
(invFun   : StructureFunctor T S)
(leftInv  : FunExt (compFun toFun invFun) idFun)
(rightInv : FunExt (compFun invFun toFun) idFun)

def StructureEquiv (S T : Structure) := LargeStructureEquiv (skeletonStructure S) (skeletonStructure T)

namespace StructureEquiv

-- This part could be generalized to LargeStructureEquiv if necessary.

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

instance structureEquiv    : IsEquivalence  StructureEquiv     := ⟨refl, symm, trans⟩
instance structureHasEquiv : HasEquivalence Structure := ⟨StructureEquiv⟩

-- This part requires using skeleton structures.

instance structureHasIso : HasIsomorphisms StructureEquiv :=
{ comp     := trans,
  assoc    := sorry,
  id       := refl
  leftId   := sorry,
  rightId  := sorry,
  inv      := symm,
  compInv  := sorry,
  leftInv  := sorry,
  rightInv := sorry,
  invInv   := sorry,
  idInv    := sorry }

instance structureHasEq : HasEquivalenceStructure Structure :=
-- Why can't we just write `⟨⟩` here?
{ equiv   := StructureEquiv,
  isEquiv := structureEquiv,
  hasIso  := structureHasIso }

-- We can build a `StructureEquiv` from a bijective functor.

def functorToEquiv {S T : Structure} (F : StructureFunctor S T) (h : Bijective F) : StructureEquiv S T :=
{ toFun    := skeletonFunctor F,
  invFun   := skeletonFunctor (inverse F h),
  leftInv  := sorry,
  rightInv := sorry }

end StructureEquiv

open StructureEquiv



-- Using this definition of equivalence, now we can actually build a "universe" structure, or rather
-- one which behaves like a universe for all our purposes: The objects are actual structures (of a
-- lower Lean universe), but the equivalences do not contain any inner structure.
--
-- Note how, in the process of encoding a universe, we remained purely constructive but simulated
-- classical logic. This shows that constructive type theory and classical set theory are really
-- just two different points on the path from one universe to the next, and that constructive
-- mathematics can be interpreted classically and vice versa.

def universeStructure : Structure :=
-- Why can't we just write `⟨Structure⟩` here?
{ U     := Structure,
  hasEq := structureHasEq }



-- Now we can wrap the function `defaultStructure`, which encodes a given Lean type as a structure
-- (with equality), into a functor from typeStructure to universeStructure.

--def defaultStructureFunctor : StructureFunctor typeStructure universeStructure :=
--{ map       := defaultStructure,
--  transport := sorry,
--  isFunctor := sorry }



-- After this tour across universes, we return to our original goal of automating the definition of
-- isomorphisms for arbitrary structures.

namespace BuildingBlocks

structure EncodedPiType where
(α : Structure)
(C : α → Sort v) --(C : StructureFunctor α universeStructure)

def EncodedDependentFunction (T : EncodedPiType) := ∀ x : T.α, T.C x

-- Every term of type `∀ x, C x` can be converted to an instance of `EncodedDependentFunction`:

def encodeDependentFunction {α : Sort u} [hasEq : HasEquivalenceStructure α] {C : α → Sort v} (f : ∀ x, C x) :
  EncodedDependentFunction ⟨@defaultStructure α hasEq, C⟩ := f

end BuildingBlocks
