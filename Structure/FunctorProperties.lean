import Structure.Basic

open GeneralizedFunctor
open StructureFunctor



set_option autoBoundImplicitLocal false



namespace FunctorProperties

variable {S T : Structure} (F : StructureFunctor S T)

-- If we interpret `≃` as equality, we can pretend that functors are just functions and define their
-- properties accordingly. Again, note that these definitions contain data.
-- However, the definitions are only well-behaved if we add some additional functoriality conditions.

def Injective  := GeneralizedFunctor F.map id  -- `∀ a b, F a ≃ F b → a ≃ b` plus functoriality
def Surjective := Σ' h : (∀ b, Σ' a, IsType.type (F a ≃ b)),
                     Σ' φ : Functor (λ b => (h b).fst),
                        GeneralizedNaturalTransformation (comp.genFun' F.map F.functor φ) id.genFun
def Bijective  := PProd (Injective F) (Surjective F)

-- We can even build an inverse functor for any functor that is bijective according to this definition,
-- even though we do not assume classical logic. This works because the equivalences in `Structure` can
-- hold the data we are defining here. Note that if we were dealing with propositions and using `∃` instead
-- of `Σ`, obtaining the inverse functor would require classical logic.
--
-- What we are doing here can be described as working in an internal logic of the `universeStructure`. Our
-- functors model the functions of this internal logic. So in this internal logic,
-- * function extensionality holds, and
-- * every bijective function has an inverse,
-- even when using constructive logic externally.
--
-- Given how closely this formalization seems to be related to HoTT, maybe some variant of univalence also
-- holds in the internal logic. If this turned out to be the case, would it provide a "constructive
-- interpretation of univalence"?
--
-- The inverse functor is unique (modulo functor equivalence).

section Inverse

variable (h : Bijective F)

def inverseElement (b : T) := (h.snd.fst b).fst

namespace inverseElement

def isInverse  (b : T) : F (inverseElement F h b) ≃ b := (h.snd.fst b).snd
def isInverse' (a : S) : inverseElement F h (F a) ≃ a := h.fst.mapEquiv (isInverse F h (F a))

end inverseElement

-- This is just a very terse way of writing the classical proof that the inverse element is unique.
-- Writing it in this way has the advantage that `PiEquiv.transport` already contains the proof
-- that the result is a functor.

def uniqueValueFunctor := Pi.PiEquiv.transport.invFunctor (inverseElement.isInverse F h)
def inverseFunctor := comp.genFun' (inverseElement F h) (uniqueValueFunctor F h) h.fst

def inverse : StructureFunctor T S :=
{ map     := inverseElement F h,
  functor := inverseFunctor F h }

namespace inverse

-- TODO: For the naturality condition, we should probably build some infrastructure around the
-- interaction between `PiEquiv` and `GeneralizedNaturalTransformation`.

def leftInv : inverse F h ⊙ F ≃ @idFun S :=
{ ext := inverseElement.isInverse' F h,
  nat := sorry }

def rightInv : F ⊙ inverse F h ≃ @idFun T :=
{ ext := inverseElement.isInverse F h,
  nat := sorry }

instance isInverse : IsInverse F (inverse F h) :=
{ leftInv  := leftInv  F h,
  rightInv := rightInv F h,
  lrCompat := sorry,
  rlCompat := sorry }

end inverse

-- Now we can build a `StructureEquiv` from any bijective functor.

def functorToEquiv : StructureEquiv S T :=
{ toFun  := F,
  invFun := inverse F h,
  isInv  := inverse.isInverse F h }

end Inverse

end FunctorProperties
