--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- In this file, we introduce a generalization of the concept of "isomorphism" beyond universal algebra
-- and category theory. It axiomatically captures the notion of "equality up to relabeling" in a
-- composable way, such that it can be applied to all structures one can build in type theory -- ideally
-- without having to write a single proof for any particular structure.
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
-- * Furthermore, we also need to consider more carefully the case that `x` is again a bundled structure
--   `⟨β, y⟩` where `β` is or contains a type: Although we placed no restrictions on `x` in the
--   description above, we secretly relied on an equality comparison when giving the definition of
--   `transport`. If the right-hand side is actually a structure with isomorphisms, we need to check for
--   isomorphism instead.
--
-- This leads to the insight that we first need to abstract over different variants of equality and
-- equivalence, and then define everything in terms of that abstraction. In a way, the resulting theory can
-- be regarded as a very abstract characterization of what equivalence really means. For example, the
-- `transport` map mentioned at the beginning can also be understood as a substitution operation based on
-- equivalence instead of equality.
--
-- Using the generalized framework, we can not only compose bundled structures as described above, but we
-- can actually define how to build arbitrary structures in terms of basic building blocks corresponding to
-- all fundamental type constructors. This way, we can really get a definition of "isomorphism" for any
-- structure that can be defined.
--
-- All of this seems strongly related to HoTT but does not use univalence in any way. However, the Lean
-- formalization relies on quotients to avoid having to define a very complicated mutually-inductive
-- construction that probably cannot even be carried out in Lean. We give some pointers regarding a possible
-- relationship with HoTT below.


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
-- result is that the translated theory always seems to be fully constructive (except for the Lean
-- limitation leading to the use of quotients), even though HLM is built on classical logic in quite a
-- fundamental way. How can this be?
--
-- One particular property of HLM plays an important role here: In HLM, equality on structures is not
-- "given" but instead defined individually for each structure. The result is that in a certain sense,
-- it is always possible to "unfold the definition" of an equality. This "unfolding" is constructive, of
-- course, and it seems that every theory in HLM has a constructive interpretation given by iterating the
-- process of unfolding. (This iteration is not meant literally as a computation that actually needs to
-- be carried out; the idea is that the process is captured by the definitions in this very file.)
--
-- So, if everything checks out as planned, we obtain a novel way of interpreting classical theories
-- constructively, i.e. there will then be three different ways to interpret them:
-- 1. by assuming classical axioms,
-- 2. via the double-negation translation,
-- 3. or by finding the computational content not in the classical proofs but in the process of unfolding
--    definitions. (Note that this only applies to excluded middle but not to the Axiom of Choice.)
--
-- Moreover, it looks like the translation should be something like HLM → HoTT → constructive type theory.



universes u v u' v'



-- We want to formalize a very general "structure with equivalences", so we start with a very basic
-- abstraction for something that looks like an equivalence relation except that the codomain is `Sort`
-- instead of `Prop`.
-- Even though `α`, `β` are not necessarily types, we write them in this way to capture the fact that
-- the canonical instance in Lean is `Equiv` (which we don't define to keep this file self-contained).

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



-- We would also like to be able to reason about those equivalences, and we need them to behave like
-- isomorphisms when doing so, with `refl` as the identity, `symm` as inverse, and `trans` as composition.
--
-- Therefore, we need to be able to decide whether two isomorphisms are equal. However, later we will have
-- isomorphisms where this equality is actually replaced by an equivalence, i.e. it contains structure.
-- Of course, it is possible to formulate the axioms in this general way, but it turns out that
-- * it breaks type class inference and simplification in many cases, and
-- * in Lean we don't benefit from it at all.
--
-- The axioms are strongly inspired by the seven corresponding lemmas in `data.equiv.basic` of Mathlib in
-- Lean 3, but reformulated in terms of operations on morphisms (and with one additional axiom which was
-- missing from those lemmas).
-- They can actually be understood as simplification rules that enable equational reasoning by transforming
-- all possible terms into a canonical form -- which luckily makes proofs in this file trivial, and maybe
-- it also points to some sort of constructive interpretation of the axioms, even though they are given as
-- equalities.

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

def useEq {α : Sort u} := @equivalenceStructure α (instanceHasEquiv α) (propEquivHasIso Eq)

instance setoidEquivalenceStructure {α : Sort u} (s : Setoid α) : HasEquivalenceStructure α :=
@equivalenceStructure α (setoidHasEquiv s) (setoidHasIso s)



-- Now we put everything together to define our general "structure with equivalence". Concrete instances are
-- any `Type u` with `Equiv` as equivalence, any `α : Type u` with `Eq` as equivalence, and so on, but also
-- a lot of structures we are going to define below.
--
-- Ideally, the domain of `equiv` should actually not be `Sort v` but `StructureWithEquiv` itself, i.e. the
-- equivalences should be allowed to have internal structure. However, that would require us to define
-- `StructureWithEquiv` mutually with declaring it as an instance of `HasIsomorphismStructure`, which seems
-- difficult or impossible in Lean. So at least for the moment, we just forget inner structure at a
-- carefully chosen location.
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
-- of ZFC), and `StructureWithEquiv` is precisely the internalization of this concept in type theory.

structure StructureWithEquiv where
(U     : Sort u)
[hasEq : HasEquivalenceStructure U]

namespace StructureWithEquiv

instance : CoeSort StructureWithEquiv (Sort u) := ⟨λ S => S.U⟩

variable {S : StructureWithEquiv}

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

def id_ (α : S) : α ≃ α := @id__ S.U equiv hasMor.toHasId α
def id' {α : S} := id_ α

@[simp] theorem assoc    {α β γ δ : S} (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h • (g • f) = (h • g) • f := hasIso.assoc    f g h
@[simp] theorem leftId   {α β     : S} (f : α ≃ β)                         : id' • f = f               := hasIso.leftId   f
@[simp] theorem rightId  {α β     : S} (f : α ≃ β)                         : f • id' = f               := hasIso.rightId  f
@[simp] theorem compInv  {α β γ   : S} (f : α ≃ β) (g : β ≃ γ)             : (g • f)⁻¹ = f⁻¹ • g⁻¹     := hasIso.compInv  f g
@[simp] theorem leftInv  {α β     : S} (f : α ≃ β)                         : f⁻¹ • f = id'             := hasIso.leftInv  f
@[simp] theorem rightInv {α β     : S} (f : α ≃ β)                         : f • f⁻¹ = id'             := hasIso.rightInv f
@[simp] theorem invInv   {α β     : S} (f : α ≃ β)                         : (f⁻¹)⁻¹ = f               := hasIso.invInv   f
@[simp] theorem idInv    (α       : S)                                     : (id_ α)⁻¹ = id'           := hasIso.idInv    α

def defaultStructure (U : Sort u) [hasEq : HasEquivalenceStructure U] : StructureWithEquiv := @StructureWithEquiv.mk U hasEq
def setoidInstanceStructure {α : Sort u} (s : Setoid α) := @defaultStructure α (setoidEquivalenceStructure s)

-- For reference, here is the complete list of axioms for an `S : StructureWithEquiv`, aligned to highlight
-- the two different points of view:
--
-- ` refl     (α       : S) : α ≃ α                 `  `id_ α` / `id'`
-- ` symm     {α β     : S} : α ≃ β → β ≃ α         `  `⁻¹`
-- ` trans    {α β γ   : S} : α ≃ β → β ≃ γ → α ≃ γ `  `•` (in reverse order)
-- ` assoc    {α β γ δ : S}                            (f : α ≃ β) (g : β ≃ γ) (h : γ ≃ δ) : h • (g • f) = (h • g) • f `
-- ` leftId   {α β     : S}                            (f : α ≃ β)                         : id' • f = f               `
-- ` rightId  {α β     : S}                            (f : α ≃ β)                         : f • id' = f               `
-- ` compInv  {α β γ   : S}                            (f : α ≃ β) (g : β ≃ γ)             : (g • f)⁻¹ = f⁻¹ • g⁻¹     `
-- ` leftInv  {α β     : S}                            (f : α ≃ β)                         : f⁻¹ • f = id'             `
-- ` rightInv {α β     : S}                            (f : α ≃ β)                         : f • f⁻¹ = id'             `
-- ` invInv   {α β     : S}                            (f : α ≃ β)                         : (f⁻¹)⁻¹ = f               `
-- ` idInv    (α       : S)                                                                : (id_ α)⁻¹ = id'           `

end StructureWithEquiv

open StructureWithEquiv



-- We want to define a map between two `StructureWithEquiv` that is compatible with their equivalences.
-- In particular, the map should be equipped with a `transport` function that transports "relabeling"
-- operations as described in the introduction, i.e. equivalences. `transport` can also be regarded as a
-- substitution principle, or generally as a well-definedness condition for the map if we interpret `≃` as
-- equality.
--
-- `transport` must respect operations on isomorphisms. This turns the combination of `map` and `transport`
-- into a functor with the additional requirement that it must also preserve inverses, as those are an
-- integral part of our axiomatized structure. So first we give a very general definition of a functor,
-- split into the three pieces of structure that we are dealing with, so we can reuse it in other contexts.

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

structure StructureFunctor (S T : StructureWithEquiv) :=
(map                 : S     → T)
(transport {α β : S} : α ≃ β → map α ≃ map β)
[isFunctor           : IsIsomorphismFunctor map transport]

namespace StructureFunctor

instance (S T : StructureWithEquiv) : CoeFun (StructureFunctor S T) (λ F => S.U → T.U) := ⟨λ F => F.map⟩

variable {S T U : StructureWithEquiv}

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
  F.transport (g • f) = F.transport g • F.transport f := transportCompDef F f g
@[simp] theorem transportId   (F : StructureFunctor S T) (α     : S) :
  F.transport (id_ α) = id'                           := transportIdDef   F α
@[simp] theorem transportInv  (F : StructureFunctor S T) {α β   : S} (f : α ≃ β) :
  F.transport f⁻¹ = (F.transport f)⁻¹                 := transportInvDef  F f

-- The transport function can be understood as a substitution principle. Note that, like much of this
-- file, it is a definition, not a theorem, because it needs to preserve structure.

def congrArg {α β : S} (F : StructureFunctor S T) : α ≃ β → F α ≃ F β := F.transport

-- We can define equivalence of functors by extensionality, using equivalence in place of equality.
-- Note that despite the use of `∀`, this is also a definition.

def ext (F G : StructureFunctor S T) := ∀ α, F α ≃ G α

instance extIsEquiv : IsEquivalence (@ext S T) :=
{ refl  := λ F   α => congrArg F (refl α),
  symm  := λ e   α => symm (e α),
  trans := λ e f α => trans (e α) (f α) }

instance hasEquiv : HasEquivalence (StructureFunctor S T) := ⟨ext⟩

-- Given this definition of equivalence of functors, it makes sense to define identity and composition and
-- prove that they are well-behaved with respect to equivalence.

def mapId   {S : StructureWithEquiv}           : S     → S                 := id
def transId {S : StructureWithEquiv} {α β : S} : α ≃ β → mapId α ≃ mapId β := id

instance idIsFunctor (S : StructureWithEquiv) :
  @IsIsomorphismFunctor S.U S.U equiv equiv hasIso hasIso mapId transId :=
{ transportComp := λ f g => rfl,
  transportId   := λ α   => rfl,
  transportInv  := λ f   => rfl }

def idFun {S : StructureWithEquiv} : StructureFunctor S S := ⟨mapId, transId⟩

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

instance extHasIso : HasIsomorphisms (@ext S T) := sorry

-- Why does type class resolution fail here?
instance functorHasEq : HasEquivalenceStructure (StructureFunctor S T) :=
{ equiv   := ext,
  isEquiv := extIsEquiv,
  hasIso  := extHasIso }

-- If we interpret `≃` as equality, we can pretend that these functors are just functions and define
-- their properties accordingly. Again, note that these definitions contain data.

def injective  (F : StructureFunctor S T) := ∀ α β, F α ≃ F β → α ≃ β
def surjective (F : StructureFunctor S T) := ∀ β, Σ α, F α ≃ β
def bijective  (F : StructureFunctor S T) := PProd.mk (injective F) (surjective F)

-- The functors between two structures form a structure, with equivalence given by extensionality.

-- Why does type class resolution fail here?
def functorStructure (S T : StructureWithEquiv) : StructureWithEquiv := 
{ U     := StructureFunctor S T,
  hasEq := functorHasEq }

end StructureFunctor

open StructureFunctor



-- We can forget the structure on a `StructureWithEquiv` on two levels, obtaining modified instances of
-- `StructureWithEquiv` via functors that are actually bijective according to the definition above.
--
-- 1. We can coerce the equivalence to `Prop` to obtain a setoid structure.
--    In comments, we will write `setoidStructure S` as `S_≈`.
--
-- 2. In a classical setting, we can additionally take the quotient with respect to equivalence, obtaining
--    a "skeleton" structure where equivalence is equality.
--    In comments, we will write `skeletonStructure S` as `S/≃`.
--
-- We need the first of these operations because of the single-level hierarchy, but it would not be
-- necessary with an inductive version of `StructureWithEquiv`.

namespace Forgetfulness

def SetoidEquiv {S : StructureWithEquiv} (α β : S) := Nonempty (α ≃ β)
def transportToSetoid {S : StructureWithEquiv} {α β : S} (e : α ≃ β) : SetoidEquiv α β := ⟨e⟩
def setoidEquiv {S : StructureWithEquiv} : Equivalence (@SetoidEquiv S) := ⟨λ α => ⟨refl α⟩, λ ⟨e⟩ => ⟨symm e⟩, λ ⟨e⟩ ⟨f⟩ => ⟨trans e f⟩⟩

instance structureToSetoid (S : StructureWithEquiv) : Setoid S.U := ⟨SetoidEquiv, setoidEquiv⟩
def setoidStructure (S : StructureWithEquiv) := StructureWithEquiv.setoidInstanceStructure (structureToSetoid S)

def toSetoidFunctor (S : StructureWithEquiv) : StructureFunctor S (setoidStructure S) :=
{ map       := id,
  transport := transportToSetoid,
  isFunctor := sorry }

def StructureQuotient (S : StructureWithEquiv) := Quotient (structureToSetoid S)
def skeletonStructure (S : StructureWithEquiv) := @StructureWithEquiv.defaultStructure (StructureQuotient S) useEq

def setoidToSkeletonFunctor (S : StructureWithEquiv) : StructureFunctor (setoidStructure S) (skeletonStructure S) :=
{ map       := λ α => Quotient.mk α,
  transport := λ e => Quotient.sound e,
  isFunctor := sorry }

def toSkeletonFunctor (S : StructureWithEquiv) := setoidToSkeletonFunctor S • toSetoidFunctor S



-- A functor between two structures induces a functor between their setoid structures, and in the
-- classical setting also between their skeleton structures. More specifically, we have the following
-- commutative diagram (commutative with respect to equivalence defined on functors, that is):
--
--   `S` ----> `S_≈` ---> `S/≃`
--    |          |          |
--    |          |          |
--    v          v          v
--   `T` ----> `T_≈` ---> `T/≃`
--
-- This can be understood as the reason why isomorphism can generally be identified with equality: In all
-- operations that preserve structure, we can take the quotient with respect to equivalence/isomorphism.

variable {S T : StructureWithEquiv}

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
-- structures in the same way that equivalence of types is defined in Mathlib. But we need to be a bit
-- careful about the equality contained within that definition.
--
-- Since our notion of equality of functors is given by `ext`, not literal equality, we need to use
-- that instead. However, we are actually defining equivalence of structures mainly for the purpose of
-- using it as an equivalence within a `StructureWithEquiv` itself, completing the round-trip. Since
-- `StructureWithEquiv` contains axioms for operations on isomorphisms, we will need to prove that those
-- axioms are satisfied by the two morphisms in our structure. But the axioms are written as propositions,
-- so at some point we end up coercing `ext` into an equivalence relation.
--
-- This is where the `setoidFunctor` we just defined comes into play: Instead of moving between `Prop`
-- and `Sort` while proving that our equiv type satisfies the isomorphism axioms, we can first write them
-- as data and then use `setoidFunctor` to convert the equivalence to a new one where the equivalences of
-- the functors live in `Prop`.

structure StructureEquiv (S T : StructureWithEquiv) where
(toFun    : StructureFunctor S T)
(invFun   : StructureFunctor T S)
(leftInv  : ext (compFun toFun invFun) idFun)
(rightInv : ext (compFun invFun toFun) idFun)

namespace StructureEquiv

def refl (S : StructureWithEquiv) : StructureEquiv S S :=
{ toFun    := idFun,
  invFun   := idFun,
  leftInv  := sorry,
  rightInv := sorry }

def symm {S T : StructureWithEquiv} (e : StructureEquiv S T) : StructureEquiv T S :=
{ toFun    := e.invFun,
  invFun   := e.toFun,
  leftInv  := e.rightInv,
  rightInv := e.leftInv }

def trans {S T U : StructureWithEquiv} (e : StructureEquiv S T) (f : StructureEquiv T U) : StructureEquiv S U :=
{ toFun    := compFun e.toFun  f.toFun,
  invFun   := compFun f.invFun e.invFun,
  leftInv  := sorry,
  rightInv := sorry }

instance structureEquiv    : IsEquivalence  StructureEquiv     := ⟨refl, symm, trans⟩
instance structureHasEquiv : HasEquivalence StructureWithEquiv := ⟨StructureEquiv⟩

-- TODO state isomorphism axioms for equivalences here; use them in structureEquivHasIso

def forgetMorphismEquivalenceStructure {S T : StructureWithEquiv} (e : StructureEquiv S T) :
  StructureEquiv (setoidStructure S) (setoidStructure T) :=
{ toFun    := setoidFunctor e.toFun,
  invFun   := setoidFunctor e.invFun,
  leftInv  := λ F => transportToSetoid (e.leftInv  F),
  rightInv := λ F => transportToSetoid (e.rightInv F) }

instance structureEquivHasIso : HasIsomorphisms StructureEquiv := sorry

instance structureHasEq : HasEquivalenceStructure StructureWithEquiv :=
{ equiv   := StructureEquiv,
  isEquiv := structureEquiv,
  hasIso  := structureEquivHasIso }

end StructureEquiv

open StructureEquiv
