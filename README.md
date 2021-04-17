# An abstract formalization of "isomorphism is equality up to relabeling"


This Lean 4 project aims to provide definitions and theorems that help automate reasoning based on
structural properties. Besides the obvious connections to universal algebra and category theory, we
also draw on ideas from Homotopy Type Theory (HoTT), in particular the Structure Identity Principle.
However, in constrast to a native HoTT implementation (which is certainly possible and would in fact be
much simpler), this formalization does not use any additional axioms, so that it can integrate well
with other libraries.

A Lean-specific way to state the main goal of this library is that it provides _definitions_ and
_theorems_ covering use cases of the "transport" _tactic_ from mathlib. This can be regarded as
replacing _metamathematical_ with _mathematical_ reasoning.


## Initial idea

The idea behind this formalization is actually quite simple to state using the `Equiv` (`≃`) type from
mathlib. This version applies to simple algebraic structures but not e.g. categories.

Consider a structure depending on a type, formalized in Lean as a type class `C : Type u → Type v`.
(E.g. `C` might be `Group`, `Ring`, ...) We would like to give a definition that specifies when an
instance `x : C α` is isomorphic to another instance `y : C β`. This very general definition will help
us when transporting objects along isomorphisms or reasoning about isomorphism-invariant properties.

As a prerequisite, we attach a function `mapEquiv : α ≃ β → C α ≃ C β` to the type class `C`, along
with proofs that `mapEquiv` commutes with `refl`, `symm`, and `trans`. This function can be understood
in multiple different ways:

* If `α` and `β` are equivalent, we demand the same of `C α` and `C β` in a compatible manner.
* We can regard the type equivalence as a relabeling operation. Then `mapEquiv` specifies how to apply
  this relabeling operation to an instance of the structure.
* When reading equivalence as equality, `mapEquiv` just says that `C` is a well-defined function.
  (Also note the similarity between `mapEquiv` and `congrArg C`.)
* `mapEquiv` turns `C` into a groupoid functor, by specifying how to map groupoid (iso)morphisms.
  (Thus, commutation with `symm` actually follows from commutation with `refl` and `trans`.)

Given these four interpretations, it should be evident that there is usually a single obvious
definition of `mapEquiv` for a given type class `C`.

Now we can define an `e : α ≃ β` to be an isomorphism between `x : C α` and `y : C β` iff `x` equals
`y` taking into account the relabeling given by `mapEquiv e`, i.e. `mapEquiv e x = y` (or, using HoTT
syntax, `x =[mapEquiv e] y`).

Equivalently, we can define an isomorphism between two _bundled instances_ `⟨α, x⟩ ⟨β, y⟩ : Σ α, C α`
to be an `e : α ≃ β` together with a proof that `mapEquiv e x = y`. Here, we can see a first connection
to HoTT because this definition matches the equivalence of sigma types given in section 2.7 of the HoTT
book, except that in our case the left side is a type which we need to compare via `≃` instead of `=`.


## Generalization
----------------

One obvious limitation of the above description is the use of equality when comparing instances of the
type class. If `x : C α` contains at least one type (with or without additional structure), we need to
replace equality with equivalence/isomorphism. Actually, even the return type of `mapEquiv` must take
this into account because the definition of `Equiv` in mathlib contains equality comparisons as well.

Moreover, we would like to automate
* the definition of `mapEquiv` for each type class `C` and
* the deduction of properties from that definition.

If we regard `mapEquiv` as describing the structure given by `C`, we would like to compose that
description from similar descriptions about individual parts of the structure. This is somewhat related
to the Structure Identity Principle from HoTT in that we need to attach "additional structure" to some
smaller existing structure. This enables us to build up `mapEquiv` analogously to how `C` is built up
from individual (dependent) fields.

Formally, we would like to treat a bundled structure `⟨α, ⟨x₁, x₂⟩⟩` (where `x₂` may depend on both `α`
and `x₁`) canonically also as a nested bundled structure `⟨⟨α, x₁⟩, x₂⟩`, with equivalence between
`⟨α, x₁⟩` and some `⟨β, y₁⟩` given by isomorphism. However, in the initial version given above the term
`⟨⟨α, x₁⟩, x₂⟩` does not type-check because `⟨α, x₁⟩` is not a type.

To conclude, the left side of the `Σ` instance needs to be something more general than a type, and the
right side needs to be something more general than an instance of a type.


## Preliminary results

In order to unify the different cases, we define a generic `Structure` type which can hold various
objects with equivalences between them, such as:

| Type                      | Equivalence          |
| ------------------------- | -------------------- |
| `Prop`                    | `Iff`                |
| `α : Sort u`              | `Eq`                 |
| `α` with `[s : Setoid α]` | `s.r`                |
| `Sort u`                  | `Equiv` from mathlib |
| `Structure`               | `StructureEquiv`     |

From our mentioning of HoTT, it may already be apparent that ideally, `Structure` should be a Lean type
defining an ∞-groupoid. However, a native definition of this type would be inductive-recursive in a way
not supported by Lean. Fortunately, a version where equivalences of equivalences are propositions is
sufficient for our use case. In other words, we define `Structure` to be a higher groupoid by replacing
equality of equivalences with an equivalence relation, but we do not preserve the entire (potentially)
infinite hierarchy of equivalences.

First, we work very generally within this framework. In `AbstractPiSigma.lean`, we define functorial
variants of Π and Σ expressions. Then, in `AbstractBuildingBlocks.lean`, we construct the individual
parts that can be composed into descriptions of larger structures. For each of the building blocks, we
can prove a _theorem_ that states when two instances of the building block are isomorphic, i.e.
equivalent as groupoids. Many common special cases of isomorphisms can be deduced directly from these
theorems; see in particular the table at `FunctorInstanceDef` in `AbstractBuildingBlocks.lean`.

After finishing the basic building blocks, we will be able to obtain the properties of structures by
"describing" them in terms of the framework. In Lean, this can likely be fully automated. However, this
part is still WIP.

In the same way, we can (and need to) define building-blocks for isomorphism-invariant properties. This
is also still WIP, but once finished, isomorphism invariance of a property will directly follow from
its syntactic definition.


## Remarks

While the formalization in terms of ∞-groupoids is strongly related to HoTT, our formalization does not
use univalence in any way. This is because we always work with groupoid equivalence instead of equality
(except where those coincide for a particular structure). As a result, we explicitly need to prove
functoriality in a lot of cases where we would obtain it for free from univalence.

The formalization brought to light some surprising properties of groupoids, which may or may not be
known. Most strikingly, we obtain the following result:
If we interpret equivalence/isomorphism of objects in a groupoid as generalized equality, then groupoid
functors are just generalized functions. If we then define "injective", "surjective", and "bijective"
in a straightforward way, each "bijective" functor actually has an inverse (i.e. adjoint) functor --
even though the formalization is entirely constructive.
(More details in `FunctorProperties.lean`.)


## TODO
* Finish abstract building blocks.
* Define the same building blocks in more concrete terms when restricted to types.
* Fill sorrys.
* Create examples.
* Determine structure automatically via type-class/tactic/attribute magic.
* Automatically deduce that properties are isomorphism-invariant.

Further enhancements:
* Introduce simpler "skeletal" version.
* Define "canonical isomorphism".
* Introduce structures with morphisms.
* Generate those structures automatically where appropriate.
* Prove that isomorphism according to those morphisms is the same as isomorphism defined as relabeling.
* Generate even more structure automatically.
* Explore connection to HLM in more detail.


Regarding the last point: HLM is the logic that is being implemented in the interactive theorem prover
Slate (https://slate-prover.org/).

HLM is classical and set-theoretic, but uses a custom set theory that can also be interpreted as a
dependent type theory. In fact, the contents of this file started out as an exploration of how to
translate from HLM to other dependently-typed systems such as Lean. The result of this exploration is
that a "set" in HLM is exactly an ∞-groupoid on the meta level. So this file should be able to serve
as a basis for a translation from HLM to Lean, and also to other theorem provers, especially those that
implement HoTT.
