--
--               An abstract formalization of "isomorphism is equality up to relabeling"
--              =========================================================================
--
-- This file contains a very abstract and general definition of `Structure`, which is actually a variant
-- of an ∞-groupoid.
--
-- See `Structure.lean` for an explanation of the use case.



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
--   for each pair of inputs, we work with a bundled version of `Setoid`.
--
-- Even though `α`, `β` are not necessarily types, we use greek letters to raise awareness that they
-- frequently will be. (However, the code where this is actually the case is outsourced into a separate
-- file `SortStructure.lean`.)

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

end IsEquivalence

open IsEquivalence



-- Sometimes we need to map instances of a type before comparing them; this structure combines the
-- necessary data for doing so.

structure MappedRelation (A : Sort w) where
{U : Sort u}
(R : GeneralizedRelation U)
(F : A → U)

instance (A : Sort w) : CoeFun (MappedRelation A) (λ R => GeneralizedRelation A) :=
⟨λ R α β => R.R (R.F α) (R.F β)⟩

def toMappedRelation {U : Sort u} (R : GeneralizedRelation U) : MappedRelation U := ⟨R, id⟩

instance (U : Sort u) : Coe (GeneralizedRelation U) (MappedRelation U) := ⟨toMappedRelation⟩



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



-- Bundle the generalized equivalence relation and its axioms into a single type class.

class HasStructure (U : Sort u) where
(M : GeneralizedRelation U)
[h : HasIsomorphisms M]

namespace HasStructure

variable {U : Sort u} [h : HasStructure U]

instance hasCmp  : HasComposition  h.M := h.h.toHasComposition
instance hasMor  : HasMorphisms    h.M := h.h.toHasMorphisms
instance hasIso  : HasIsomorphisms h.M := h.h
instance isEquiv : IsEquivalence   h.M := isoEquiv h.M

def Equv (α β : U) := (h.M α β).α
infix:25 " ≃ " => Equv

instance (α β : U) : Setoid (α ≃ β) := (h.M α β).s

end HasStructure

open HasStructure

instance propHasStructure                                 : HasStructure Prop := ⟨genRel Iff⟩
instance instanceHasStructure (α : Sort u)                : HasStructure α    := ⟨genRel Eq⟩
instance setoidHasStructure   (α : Sort u) [s : Setoid α] : HasStructure α    := ⟨genRel s.r⟩



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

def iso (S : Structure) := S.h.M

variable {S : Structure}

instance hasStructure : HasStructure S.U := S.h

instance hasCmp  : HasComposition  (iso S) := hasStructure.hasCmp
instance hasMor  : HasMorphisms    (iso S) := hasStructure.hasMor
instance hasIso  : HasIsomorphisms (iso S) := hasStructure.hasIso
instance isEquiv : IsEquivalence   (iso S) := hasStructure.isEquiv

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

end Structure

open Structure

def defaultStructure (U : Sort u) [h : HasStructure U] : Structure := ⟨U⟩
def instanceStructure (α : Sort u) := @defaultStructure α (instanceHasStructure α)
def setoidInstanceStructure (α : Sort u) [s : Setoid α] := @defaultStructure α (setoidHasStructure α)
def bundledSetoidStructure (S : BundledSetoid) := setoidInstanceStructure S.α

def isoStructure {S : Structure} (α β : S) := bundledSetoidStructure (iso S α β)



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

theorem equivInSetoidStructure (a b : setoidStructure S) : a ≃ b ↔ a ≈ b := ⟨λ e => ⟨e⟩, λ ⟨e⟩ => e⟩

namespace Classical

def StructureQuotient := Quotient (structureToSetoid S)
def skeletonStructure : Structure := ⟨StructureQuotient S⟩

theorem equivInSkeletonStructure (a b : skeletonStructure S) : a ≃ b ↔ a = b := ⟨id, id⟩

end Classical

end Forgetfulness

open Forgetfulness



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
(respectsId     (α     : A)                         : FF (id__ (R.F α)) ≈ id__ (S.F α))

class IsIsomorphismFunctor [HasIsomorphisms R.R] [HasIsomorphisms S.R]
  extends IsMorphismFunctor    R S FF where
(respectsInv    {α β   : A} (f : R α β)             : FF f⁻¹            ≈ (FF f)⁻¹)

end Functors

open Functors

-- If the target has equivalences in `Prop`, the functor axioms are satisfied trivially.

instance propFunctor {A : Sort w} {R : MappedRelation A} [HasIsomorphisms R.R]
  {U : Sort u} {S : U → U → Prop} [e : IsEquivalence (genRel S)] {F : A → U}
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

variable {A : Sort w} {S T U : Structure}

-- This doesn't work, unfortunately.
--instance (F : A → S) (G : A → T) {α β : A} :
--  CoeFun (GeneralizedFunctor F G) (λ φ => F α ≃ F β → G α ≃ G β) :=
--⟨λ φ => φ.FF⟩

def generalizeFunctor {B : Sort v} {F : A → S} {G : A → T} (φ : GeneralizedFunctor F G) (H : B → A) :
  GeneralizedFunctor (F ∘ H) (G ∘ H) :=
{ FF        := φ.FF,
  isFunctor := { respectsSetoid := φ.isFunctor.respectsSetoid,
                 respectsComp   := φ.isFunctor.respectsComp,
                 respectsId     := λ α => φ.isFunctor.respectsId (H α),
                 respectsInv    := φ.isFunctor.respectsInv } }

instance {B : Sort v} (F : A → S) (G : A → T) (H : B → A) :
  Coe (GeneralizedFunctor F G) (GeneralizedFunctor (F ∘ H) (G ∘ H)) :=
⟨λ φ => generalizeFunctor φ H⟩

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

def compFF {α β : A} (e : F α ≃ F β) := ψ.FF (φ.FF e)

namespace compFF

theorem respectsSetoid {α β :   A} {e f : F α ≃ F β} (h : e ≈ f) :
  compFF φ ψ e ≈ compFF φ ψ f :=
ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsSetoid h)

theorem respectsComp   {α β γ : A} (e : F α ≃ F β) (f : F β ≃ F γ) :
  compFF φ ψ (f • e) ≈ compFF φ ψ f • compFF φ ψ e :=
let h₁ : ψ.FF (φ.FF (f • e))    ≈ ψ.FF (φ.FF f • φ.FF e)        := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsComp e f);
let h₂ : ψ.FF (φ.FF f • φ.FF e) ≈ ψ.FF (φ.FF f) • ψ.FF (φ.FF e) := ψ.isFunctor.respectsComp (φ.FF e) (φ.FF f);
Setoid.trans h₁ h₂

theorem respectsId     (α     : A) :
  compFF φ ψ (id_ (F α)) ≈ id' :=
let h₁ : ψ.FF (φ.FF (id_ (F α))) ≈ ψ.FF (id_ (G α)) := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsId α);
let h₂ : ψ.FF (id_ (G α))        ≈ id_ (H α)        := ψ.isFunctor.respectsId α;
Setoid.trans h₁ h₂

theorem respectsInv    {α β   : A} (e : F α ≃ F β) :
  compFF φ ψ e⁻¹ ≈ (compFF φ ψ e)⁻¹ :=
let h₁ : ψ.FF (φ.FF e⁻¹) ≈ ψ.FF (φ.FF e)⁻¹   := ψ.isFunctor.respectsSetoid (φ.isFunctor.respectsInv e);
let h₂ : ψ.FF (φ.FF e)⁻¹ ≈ (ψ.FF (φ.FF e))⁻¹ := ψ.isFunctor.respectsInv (φ.FF e);
Setoid.trans h₁ h₂

instance isFunctor : IsIsomorphismFunctor ⟨iso S, F⟩ ⟨iso U, H⟩ (compFF φ ψ) :=
{ respectsSetoid := compFF.respectsSetoid φ ψ,
  respectsComp   := compFF.respectsComp   φ ψ,
  respectsId     := compFF.respectsId     φ ψ,
  respectsInv    := compFF.respectsInv    φ ψ }

end compFF

def genFun : GeneralizedFunctor F H := ⟨compFF φ ψ⟩

end comp

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

def DependentStructure {A : Sort w} (S : A → Structure) := ∀ α, S α

namespace DependentStructure

variable {A : Sort w} {S : A → Structure}

def DependentEquiv (F G : DependentStructure S) := ∀ α, F α ≃ G α

namespace DependentEquiv

def refl  (F     : DependentStructure S)                                                   : DependentEquiv F F :=
λ α => IsEquivalence.refl  (F α)
def symm  {F G   : DependentStructure S} (φ : DependentEquiv F G)                          : DependentEquiv G F :=
λ α => IsEquivalence.symm  (φ α)
def trans {F G H : DependentStructure S} (φ : DependentEquiv F G) (ψ : DependentEquiv G H) : DependentEquiv F H :=
λ α => IsEquivalence.trans (φ α) (ψ α)

def dependentIsoStructure (F G : DependentStructure S) (α : A) := isoStructure (F α) (G α)

def EquivEquiv {F G : DependentStructure S} (φ ψ : DependentEquiv F G) :=
@DependentEquiv A (dependentIsoStructure F G) φ ψ

namespace EquivEquiv

variable {F G : DependentStructure S}

def refl  (φ     : DependentEquiv F G)                                           : EquivEquiv φ φ :=
@DependentEquiv.refl A (dependentIsoStructure F G) φ
def symm  {φ ψ   : DependentEquiv F G} (e : EquivEquiv φ ψ)                      : EquivEquiv ψ φ :=
DependentEquiv.symm  e
def trans {φ ψ χ : DependentEquiv F G} (e : EquivEquiv φ ψ) (f : EquivEquiv ψ χ) : EquivEquiv φ χ :=
DependentEquiv.trans e f

instance dependentEquivSetoid : Setoid (DependentEquiv F G) := ⟨EquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquiv

def dependentEquiv (F G : DependentStructure S) : BundledSetoid := ⟨DependentEquiv F G⟩

-- Unfortunately, uncommenting this causes Lean to hang indefinitely, so we have to copy and paste the
-- code at two other places instead.
-- This only occured after moving `sortStructure` to a separate file, but `sortStructure` shouldn't be
-- used here because we are dealing with the arbitrary structure `S α`. Adding this argument explicitly
-- didn't help.
--instance dependentEquivHasIso : HasIsomorphisms (@dependentEquiv A S) :=
--{ comp         := trans,
--  congrArgComp := λ hφ hψ α => congrArgComp (S := S α) (hφ α) (hψ α),
--  assoc        := λ φ ψ χ α => assoc        (S := S α) (φ α) (ψ α) (χ α),
--  id           := refl,
--  leftId       := λ φ     α => leftId       (S := S α) (φ α),
--  rightId      := λ φ     α => rightId      (S := S α) (φ α),
--  inv          := symm,
--  congrArgInv  := λ hφ    α => congrArgInv  (S := S α) (hφ α),
--  leftInv      := λ φ     α => leftInv      (S := S α) (φ α),
--  rightInv     := λ φ     α => rightInv     (S := S α) (φ α),
--  invInv       := λ φ     α => invInv       (S := S α) (φ α),
--  compInv      := λ φ ψ   α => compInv      (S := S α) (φ α) (ψ α),
--  idInv        := λ F     α => idInv        (S := S α) (F α) }

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
let a := φ α;
let b := φ β;
congrArgComp (congrArgComp (invInv a) (Setoid.refl e)) (Setoid.refl b⁻¹)

theorem respectsSetoid {α β   : A} {e₁ e₂ : F α ≃ F β} (h : e₁ ≈ e₂) :
  transport φ e₁ ≈ transport φ e₂ :=
let a := φ α;
let b := φ β;
congrArgComp (congrArgComp (Setoid.refl a⁻¹) h) (Setoid.refl b)

theorem respectsComp   {α β γ : A} (e : F α ≃ F β) (f : F β ≃ F γ) :
  transport φ (f • e) ≈ transport φ f • transport φ e :=
let a := φ α;
let b := φ β;
let c := φ γ;
let h₁ : c • (f • e) • a⁻¹ ≈ c • (f • (id' • e)) • a⁻¹         := congrArgComp (congrArgComp (Setoid.refl a⁻¹) (congrArgComp (Setoid.symm (leftId e)) (Setoid.refl f))) (Setoid.refl c);
let h₂ : c • (f • e) • a⁻¹ ≈ c • (f • ((b⁻¹ • b) • e)) • a⁻¹   := Setoid.trans h₁ (congrArgComp (congrArgComp (Setoid.refl a⁻¹) (congrArgComp (congrArgComp (Setoid.refl e) (Setoid.symm (leftInv b))) (Setoid.refl f))) (Setoid.refl c));
let h₃ : c • (f • e) • a⁻¹ ≈ c • (f • (b⁻¹ • (b • e))) • a⁻¹   := Setoid.trans h₂ (congrArgComp (congrArgComp (Setoid.refl a⁻¹) (congrArgComp (Setoid.symm (assoc e b b⁻¹)) (Setoid.refl f))) (Setoid.refl c));
let h₄ : c • (f • e) • a⁻¹ ≈ c • ((f • b⁻¹) • (b • e)) • a⁻¹   := Setoid.trans h₃ (congrArgComp (congrArgComp (Setoid.refl a⁻¹) (assoc (b • e) b⁻¹ f)) (Setoid.refl c));
let h₅ : c • (f • e) • a⁻¹ ≈ c • (f • b⁻¹) • ((b • e) • a⁻¹)   := Setoid.trans h₄ (congrArgComp (Setoid.symm (assoc a⁻¹ (b • e) (f • b⁻¹))) (Setoid.refl c));
let h₆ : c • (f • e) • a⁻¹ ≈ (c • (f • b⁻¹)) • ((b • e) • a⁻¹) := Setoid.trans h₅ (assoc ((b • e) • a⁻¹) (f • b⁻¹) c);
let h₇ : c • (f • e) • a⁻¹ ≈ (c • f • b⁻¹) • (b • e • a⁻¹)     := Setoid.trans h₆ (congrArgComp (Setoid.symm (assoc a⁻¹ e b)) (Setoid.refl (c • f • b⁻¹)));
h₇

theorem respectsId     (α     : A) :
  transport φ (id_ (F α)) ≈ id' :=
let a := φ α;
let h₁ : a • id' • a⁻¹ ≈ a • a⁻¹ := congrArgComp (leftId a⁻¹) (Setoid.refl a);
let h₂ : a • id' • a⁻¹ ≈ id'     := Setoid.trans h₁ (rightInv a);
h₂

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



-- A functor between two `Structure`s is a map that also maps equivalences in a compatible way. On the
-- one hand, this is just a groupoid functor, but on the other hand, the mapping of equivalences also
-- matches exactly the `transport` map mentioned in the introduction.
--
-- Moreover, if we interpret `≃` as a generalization of equality, the `transport` map is actually the
-- generalized version of `congrArg`, so we name it `congrArgMap`. Under this interpretation, it can also
-- be regarded as a well-definedness condition for the map: equality of arguments implies equality of
-- results.

structure StructureFunctor (S T : Structure) :=
(map     : S → T)
(functor : GeneralizedFunctor id map)

namespace StructureFunctor

variable {S T U V : Structure}

instance : CoeFun (StructureFunctor S T) (λ F => S → T) := ⟨StructureFunctor.map⟩

def congrArgMap (F : StructureFunctor S T) {α β : S} : α ≃ β → F α ≃ F β := F.functor.FF

-- Restate the axioms as theorems about `congrArgMap`.

        theorem respectsSetoid (F : StructureFunctor S T) {α β   : S} {f₁ f₂ : α ≃ β} :
  f₁ ≈ f₂ → congrArgMap F f₁ ≈ congrArgMap F f₂             := F.functor.isFunctor.respectsSetoid
@[simp] theorem respectsComp   (F : StructureFunctor S T) {α β γ : S} (f : α ≃ β) (g : β ≃ γ) :
  congrArgMap F (g • f) ≈ congrArgMap F g • congrArgMap F f := F.functor.isFunctor.respectsComp f g
@[simp] theorem respectsId     (F : StructureFunctor S T) (α     : S) :
  congrArgMap F (id_ α) ≈ id'                               := F.functor.isFunctor.respectsId   α
@[simp] theorem respectsInv    (F : StructureFunctor S T) {α β   : S} (f : α ≃ β) :
  congrArgMap F f⁻¹     ≈ (congrArgMap F f)⁻¹               := F.functor.isFunctor.respectsInv  f



-- We can define equivalence of functors by extensionality, using equivalence in `T` instead of equality.
-- This is an equivalence according to our definition, and it is compatible with isomorphisms via the
-- functor axioms, so we can use it to build an instance of `Structure` again.

def FunExt (F G : StructureFunctor S T) := DependentEquiv F.map G.map

namespace FunExt

def refl  (F     : StructureFunctor S T)                                   : FunExt F F :=
DependentEquiv.refl F.map
def symm  {F G   : StructureFunctor S T} (e : FunExt F G)                  : FunExt G F :=
DependentEquiv.symm e
def trans {F G H : StructureFunctor S T} (e : FunExt F G) (f : FunExt G H) : FunExt F H :=
DependentEquiv.trans e f

def funExt (F G : StructureFunctor S T) := DependentEquiv.dependentEquiv F.map G.map

-- Unfortunately, uncommenting this line (after uncommenting DependentEquiv.dependentEquivHasIso first)
-- causes Lean to hang indefinitely, so we have to copy and paste the code instead.
--instance funExtHasIso : HasIsomorphisms (@funExt S T) := @DependentEquiv.dependentEquivHasIso S.U (λ _ => T)

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

instance functorHasStructure : HasStructure (StructureFunctor S T) := ⟨FunExt.funExt⟩
def functorStructure (S T : Structure) : Structure := ⟨StructureFunctor S T⟩



-- Given this definition of equivalence of functors, it makes sense to define identity and composition and
-- prove that they are well-behaved with respect to equivalence.

def idFun : StructureFunctor S S := ⟨id, id.genFun⟩

def compMap     (F : StructureFunctor S T) (G : StructureFunctor T U) : S → U :=
λ f => G (F f)

def compFunctor (F : StructureFunctor S T) (G : StructureFunctor T U) : GeneralizedFunctor id (compMap F G) :=
comp.genFun F.functor (generalizeFunctor G.functor F.map)

def compFun     (F : StructureFunctor S T) (G : StructureFunctor T U) : StructureFunctor S U :=
⟨compMap F G, compFunctor F G⟩

def compFun.congrArg {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (hF : FunExt F₁ F₂) (hG : FunExt G₁ G₂) :
  FunExt (compFun F₁ G₁) (compFun F₂ G₂) :=
λ α => trans (congrArgMap G₁ (hF α)) (hG (F₂ α))

def compFun.assoc (F : StructureFunctor S T) (G : StructureFunctor T U) (H : StructureFunctor U V) :
  FunExt (compFun (compFun F G) H) (compFun F (compFun G H)) := λ α => refl (H (G (F α)))

def idFun.leftId  (F : StructureFunctor S T) : FunExt (compFun F idFun) F := λ α => refl (F α)
def idFun.rightId (F : StructureFunctor S T) : FunExt (compFun idFun F) F := λ α => refl (F α)



-- The constant functor.

def constFun (c : T) : StructureFunctor S T :=
{ map     := Function.const S.U c,
  functor := { FF        := λ _ => IsEquivalence.refl c,
               isFunctor := { respectsSetoid := λ _   => Setoid.refl (id_ c),
                              respectsComp   := λ _ _ => Setoid.symm (leftId (id_ c)),
                              respectsId     := λ _   => Setoid.refl (id_ c),
                              respectsInv    := λ _   => Setoid.symm (idInv c) } } }



-- If we wish to use `•` for functors, we need to define them as a setoid first.
-- (Unfortunately, this does not help us in most cases because we would need to introduce our functors
-- as instances of `functorSetoid`, which we don't want.)

instance functorIsSetoid : Setoid (StructureFunctor S T) := structureToSetoid (functorStructure S T)
def functorSetoid : BundledSetoid := ⟨StructureFunctor S T⟩

instance hasComp : HasComp        @functorSetoid := ⟨@compFun⟩

theorem compFun.congrArg' {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} :
  F₁ ≈ F₂ → G₁ ≈ G₂ → compFun F₁ G₁ ≈ compFun F₂ G₂ :=
λ ⟨hF⟩ ⟨hG⟩ => ⟨compFun.congrArg hF hG⟩

theorem compFun.congrArg'' {F₁ F₂ : @functorSetoid S T} {G₁ G₂ : @functorSetoid T U} :
  F₁ ≈ F₂ → G₁ ≈ G₂ → G₁ • F₁ ≈ G₂ • F₂ :=
congrArg'

theorem compFun.assoc' (F : @functorSetoid S T) (G : @functorSetoid T U) (H : @functorSetoid U V) :
  compFun (compFun F G) H ≈ compFun F (compFun G H) :=
⟨assoc F G H⟩

theorem compFun.assoc'' (F : @functorSetoid S T) (G : @functorSetoid T U) (H : @functorSetoid U V) :
  H • (G • F) ≈ (H • G) • F :=
assoc' F G H

instance hasCmp  : HasComposition @functorSetoid := ⟨compFun.congrArg'', compFun.assoc''⟩

instance hasId   : HasId          @functorSetoid := ⟨@idFun⟩

theorem idFun.leftId'  (F : @functorSetoid S T) : hasId.id T • F ≈ F := ⟨leftId  F⟩
theorem idFun.rightId' (F : @functorSetoid S T) : F • hasId.id S ≈ F := ⟨rightId F⟩

instance hasMor  : HasMorphisms   @functorSetoid := ⟨idFun.leftId', idFun.rightId'⟩



section Properties

variable (F : StructureFunctor S T)

-- If we interpret `≃` as equality, we can pretend that functors are just functions and define their
-- properties accordingly. Again, note that these definitions contain data.
-- For injectivity, this is equivalent to writing `∀ {α β}, F α ≃ F β → α ≃ β` with the additional
-- requirement that everything must respect setoid and isomorphism operations.

def Injective  := GeneralizedFunctor F.map id
def Surjective := ∀ β, Σ α, F α ≃ β
def Bijective  := Prod (Injective F) (Surjective F)

-- We can even build an inverse functor for any functor that is bijective according to this definition,
-- even though we do not assume classical logic. This works because the equivalences in `Structure` can
-- hold the data we are defining here. Note that if we were dealing with propositions and using `∃` instead
-- of `Σ`, obtaining the inverse functor would require classical logic.
--
-- What we are doing here can be described as working in an internal logic of the `universeStructure` we
-- are going to define. Our functors model the functions of this internal logic. So in this internal logic,
-- * function extensionality holds, and
-- * every bijective function has an inverse,
-- even when using constructive logic externally.
--
-- Given how closely this formalization seems to be related to HoTT, maybe some variant of univalence also
-- holds in the internal logic. If this turned out to be the case, would it provide a "constructive
-- interpretation of univalence"?
--
-- The inverse functor is unique (modulo equivalence, i.e. `FunExt`).

section Inverse

variable (h : Bijective F)

def inverseElement (β : T) :=
(h.snd β).fst

namespace inverseElement

def isInverse (β : T) :
  F (inverseElement F h β) ≃ β :=
(h.snd β).snd

def isInverse' (α : S) :
  inverseElement F h (F α) ≃ α :=
h.fst.FF (isInverse F h (F α))

end inverseElement

-- This is just a very terse way of writing the classical proof that the inverse element is unique.
-- Writing it in this way has the advantage that `DependentEquiv.transport` already contains the proof
-- that the result is a functor.

def uniqueValueFunctor := DependentEquiv.transport.invFunctor (inverseElement.isInverse F h)
def inverseFunctor := comp.genFun (uniqueValueFunctor F h) (generalizeFunctor h.fst (inverseElement F h))

def inverse : StructureFunctor T S :=
{ map     := inverseElement F h,
  functor := inverseFunctor F h }

namespace inverse

def leftInv  :
  FunExt (compFun F (inverse F h)) idFun :=
inverseElement.isInverse' F h

def rightInv :
  FunExt (compFun (inverse F h) F) idFun :=
inverseElement.isInverse  F h

end inverse

end Inverse

end Properties



-- A functor between instance structures is actually just a function.

def congrArgFunctor {α : Sort u} {β : Sort v} (f : α → β) : @GeneralizedFunctor α (instanceStructure α) (instanceStructure β) id f :=
{ FF        := congrArg f,
  isFunctor := propFunctor }

def InstanceStructureFunctor (α β : Sort u) := StructureFunctor (instanceStructure α) (instanceStructure β)

def instanceStructureFunctor {α β : Sort u} (f : α → β) : InstanceStructureFunctor α β :=
{ map     := f,
  functor := congrArgFunctor f }

instance {α β : Sort u} : Coe (α → β) (InstanceStructureFunctor α β) := ⟨instanceStructureFunctor⟩



-- If we have a function `F` and an equivalent functor `G`, we can turn `F` into a functor as well.

def proxyFunctor {S T : Structure} (F : S → T) (G : StructureFunctor S T) (φ : DependentEquiv F G.map) : StructureFunctor S T :=
{ map     := F,
  functor := comp.genFun G.functor (DependentEquiv.transport.invFunctor φ) }

end StructureFunctor

open StructureFunctor



-- Based on the definition of a functor between two structures, we can define equivalence of two
-- structures in the same way that equivalence of types is defined in mathlib, except that we need to
-- replace equality of functors with an instance of `FunExt`.

structure StructureEquiv (S T : Structure) where
(toFun    : StructureFunctor S T)
(invFun   : StructureFunctor T S)
(leftInv  : compFun toFun invFun ≃ idFun)
(rightInv : compFun invFun toFun ≃ idFun)

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
  compFun (compFun e.toFun f.toFun) (compFun f.invFun e.invFun) ≃ idFun :=
λ α => trans (congrArgMap e.invFun (f.leftInv (e.toFun α))) (e.leftInv α)

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) : StructureEquiv S U :=
{ toFun    := compFun e.toFun  f.toFun,
  invFun   := compFun f.invFun e.invFun,
  leftInv  := transLeftInv e f,
  rightInv := transLeftInv (symm f) (symm e) }

end StructureEquiv



-- We can build a `StructureEquiv` from a bijective functor.

def functorToEquiv {S T : Structure} (F : StructureFunctor S T) (h : Bijective F) : StructureEquiv S T :=
{ toFun    := F,
  invFun   := inverse F h,
  leftInv  := inverse.leftInv  F h,
  rightInv := inverse.rightInv F h }



-- If we have a `StructureEquiv S T`, we can ask whether it maps `a : S` to `b : T`, and this is
-- actually a generalized form of an equivalence.

def InstanceEquiv {S T : Structure} (e : StructureEquiv S T) (a : S) (b : T) := e.toFun a ≃ b

namespace InstanceEquiv

def refl  (S     : Structure)                                                   (a : S)                 :
  InstanceEquiv (StructureEquiv.refl S) a a :=
IsEquivalence.refl a

def symm  {S T   : Structure} (e : StructureEquiv S T)                          (a : S) (b : T)         :
  InstanceEquiv e a b → InstanceEquiv (StructureEquiv.symm e) b a :=
λ h₁ => IsEquivalence.trans (IsEquivalence.symm (e.invFun.congrArgMap h₁)) (e.leftInv a)

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (a : S) (b : T) (c : U) :
  InstanceEquiv e a b → InstanceEquiv f b c → InstanceEquiv (StructureEquiv.trans e f) a c :=
λ h₁ h₂ => IsEquivalence.trans (f.toFun.congrArgMap h₁) h₂

end InstanceEquiv



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

-- `isFunctor` should be covered by `propFunctor` as in the quotient case, but that just causes lots of
-- type class resolution issues.

def toSetoidFunctor (S : Structure) : StructureFunctor S (setoidStructure S) :=
{ map     := id,
  functor := { FF        := toSetoidEquiv S,
               isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ => proofIrrel _ _,
                              respectsId     := λ _   => proofIrrel _ _,
                              respectsInv    := λ _   => proofIrrel _ _ } } }

def SetoidStructureFunctor (S T : Structure) := StructureFunctor (setoidStructure S) (setoidStructure T)

def setoidFunctor {S T : Structure} (F : StructureFunctor S T) : SetoidStructureFunctor S T :=
{ map     := F.map,
  functor := { FF        := λ ⟨e⟩ => ⟨F.congrArgMap e⟩,
               isFunctor := { respectsSetoid := λ _   => proofIrrel _ _,
                              respectsComp   := λ _ _ => proofIrrel _ _,
                              respectsId     := λ _   => proofIrrel _ _,
                              respectsInv    := λ _   => proofIrrel _ _ } } }

def setoidFunctorStructure (S T : Structure) := functorStructure (setoidStructure S) (setoidStructure T)

namespace Classical

def setoidToSkeletonFunctor (S : Structure) : StructureFunctor (setoidStructure S) (skeletonStructure S) :=
{ map     := λ α => Quotient.mk α,
  functor := { FF        := λ e => Quotient.sound e,
               isFunctor := propFunctor } }

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
{ map     := skeletonMap F,
  functor := { FF        := skeletonCongrArg F,
               isFunctor := propFunctor } }

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

def refl  (S     : Structure)                                                               : SetoidStructureEquiv S S :=
  StructureEquiv.refl  (setoidStructure S)
def symm  {S T   : Structure} (e : SetoidStructureEquiv S T)                                : SetoidStructureEquiv T S :=
  StructureEquiv.symm  e
def trans {S T U : Structure} (e : SetoidStructureEquiv S T) (f : SetoidStructureEquiv T U) : SetoidStructureEquiv S U :=
  StructureEquiv.trans e f

-- When working with `SetoidStructureEquiv`, we can ignore `leftInv` and `rightInv` because they are
-- proofs.
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
⟨compFun.congrArg' he.left hf.left, compFun.congrArg' hf.right he.right⟩

theorem assoc {S T U V : Structure} (e : SetoidStructureEquiv S T) (f : SetoidStructureEquiv T U) (g : SetoidStructureEquiv U V) :
  trans (trans e f) g ≈ trans e (trans f g) :=
⟨compFun.assoc' e.toFun f.toFun g.toFun, compFun.assoc' g.invFun f.invFun e.invFun⟩

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



-- We can convert any equivalence to one between setoid structures.

def toSetoidStructureEquiv {S T : Structure} (e : StructureEquiv S T) : SetoidStructureEquiv S T :=
{ toFun    := setoidFunctor e.toFun,
  invFun   := setoidFunctor e.invFun,
  leftInv  := λ α => ⟨e.leftInv  α⟩,
  rightInv := λ α => ⟨e.rightInv α⟩ }

-- An `InstanceEquiv` of a `SetoidStructureEquiv` is what we expect it to be.

theorem setoidInstanceEquiv {S T : Structure} (e : SetoidStructureEquiv S T) (a : S) (b : T) :
  InstanceEquiv e a b ↔ e.toFun a ≈ b :=
equivInSetoidStructure T (e.toFun a) b



-- Just a minor lemma about `InstanceEquiv` that we can only state with respect to
-- `SetoidStructureEquiv` because we have not defined any equivalence for the more general
-- `StructureEquiv`.

theorem InstanceEquiv.congrArg {S T : Structure} {e₁ e₂ : SetoidStructureEquiv S T} (h : e₁ ≈ e₂) (a : S) (b : T) :
  InstanceEquiv e₁ a b → InstanceEquiv e₂ a b :=
let ⟨φ⟩ := h.left;
let f := IsEquivalence.trans (IsEquivalence.symm (φ a));
f



-- Using `SetoidStructureEquiv`, now we can actually build a "universe" structure, or equivalently the
-- groupoid of lower-level groupoids. Note that the objects are actual structures (of a lower Lean
-- universe), but the equivalences have been coerced to setoids, i.e. they no longer contain their inner
-- structure.

instance structureHasStructure : HasStructure Structure := ⟨SetoidStructureEquiv.structureEquiv⟩
def universeStructure : Structure := ⟨Structure⟩
