--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- Definitions related to `productStructure`.



import Structure.Basic
import Structure.UniverseFunctor

open Morphisms
open StructureProduct
open StructureFunctor



set_option autoBoundImplicitLocal false

universes u v



namespace PProd

def map {α₁ α₂ : Sort u} {β₁ β₂ : Sort v} (f : α₁ → α₂) (g : β₁ → β₂) :
  PProd α₁ β₁ → PProd α₂ β₂ :=
-- Note: Things stop being definitionally equal if we deconstruct `p`.
λ p => ⟨f p.fst, g p.snd⟩

def mapFst {α₁ α₂ : Sort u} {β : Sort v} (f : α₁ → α₂) : PProd α₁ β → PProd α₂ β := map f id
def mapSnd {α : Sort u} {β₁ β₂ : Sort v} (g : β₁ → β₂) : PProd α β₁ → PProd α β₂ := map id g

end PProd



namespace StructureProduct.productStructure

-- Introduction and projections of `StructureProduct` are functorial.

section MkProj

def mkFunctor {S T U : Structure} (F : StructureFunctor S T) (G : StructureFunctor S U) :
  StructureFunctor S (productStructure T U) :=
{ map     := λ a => ⟨F a, G a⟩,
  functor := { mapEquiv  := λ e => ⟨congrArg F e, congrArg G e⟩,
               isFunctor := { respectsSetoid := λ h   => ⟨respectsSetoid F h,   respectsSetoid G h⟩,
                              respectsComp   := λ e f => ⟨respectsComp   F e f, respectsComp   G e f⟩,
                              respectsId     := λ a   => ⟨respectsId     F a,   respectsId     G a⟩,
                              respectsInv    := λ e   => ⟨respectsInv    F e,   respectsInv    G e⟩ } } }

variable (S T : Structure)

def mkFstFunctor (b : T) : StructureFunctor S (productStructure S T) :=
mkFunctor idFun (constFun b)

def mkSndFunctor (a : S) : StructureFunctor T (productStructure S T) :=
mkFunctor (constFun a) idFun

def projFstFunctor : StructureFunctor (productStructure S T) S :=
{ map     := PProd.fst,
  functor := { mapEquiv  := PProd.fst,
               isFunctor := { respectsSetoid := λ h   => h.left,
                              respectsComp   := λ e f => Setoid.refl (f.fst • e.fst),
                              respectsId     := λ P   => Setoid.refl (id_ P.fst),
                              respectsInv    := λ e   => Setoid.refl e.fst⁻¹ } } }

def projSndFunctor : StructureFunctor (productStructure S T) T :=
{ map     := PProd.snd,
  functor := { mapEquiv  := PProd.snd,
               isFunctor := { respectsSetoid := λ h   => h.right,
                              respectsComp   := λ e f => Setoid.refl (f.snd • e.snd),
                              respectsId     := λ P   => Setoid.refl (id_ P.snd),
                              respectsInv    := λ e   => Setoid.refl e.snd⁻¹ } } }

end MkProj



-- `productStructure` is functorial in both arguments.

def mapProdFunctor {S₁ S₂ T₁ T₂ : Structure} (F : StructureFunctor S₁ S₂) (G : StructureFunctor T₁ T₂) :
  StructureFunctor (productStructure S₁ T₁) (productStructure S₂ T₂) :=
{ map     := PProd.map F G,
  functor := { mapEquiv  := PProd.map (congrArg F) (congrArg G),
               isFunctor := { respectsSetoid := λ h   => ⟨respectsSetoid F h.left,      respectsSetoid G h.right⟩,
                              respectsComp   := λ e f => ⟨respectsComp   F e.fst f.fst, respectsComp   G e.snd f.snd⟩,
                              respectsId     := λ P   => ⟨respectsId     F P.fst,       respectsId     G P.snd⟩,
                              respectsInv    := λ e   => ⟨respectsInv    F e.fst,       respectsInv    G e.snd⟩ } } }

def mapProdEquiv {S₁ S₂ T₁ T₂ : Structure} (e : S₁ ≃ S₂) (f : T₁ ≃ T₂) :
  productStructure S₁ T₁ ≃ productStructure S₂ T₂ :=
{ toFun  := mapProdFunctor e.toFun  f.toFun,
  invFun := mapProdFunctor e.invFun f.invFun,
  isInv  := sorry }

def productStructureFunctor : UniverseFunctor (productStructure universeStructure universeStructure) :=
{ map     := λ P => productStructure P.fst P.snd,
  functor := { mapEquiv  := λ e => mapProdEquiv e.fst e.snd,
               isFunctor := sorry } }

section OneSided

variable (S : Structure)

def fstFunctor : UniverseStructureFunctor :=
{ map           := λ T => productStructure T S,
  mapEquiv      := λ e => mapProdEquiv e (StructureEquiv.refl S),
  respectsEquiv := { mapEquiv  := sorry,
                     isFunctor := sorry },
  respectsComp  := sorry,
  respectsId    := sorry,
  respectsInv   := sorry }

def sndFunctor : UniverseStructureFunctor :=
{ map           := λ T => productStructure S T,
  mapEquiv      := λ e => mapProdEquiv (StructureEquiv.refl S) e,
  respectsEquiv := { mapEquiv  := sorry,
                     isFunctor := sorry },
  respectsComp  := sorry,
  respectsId    := sorry,
  respectsInv   := sorry }

end OneSided

end StructureProduct.productStructure



namespace FunctorProductEquivalences

-- Constructing a functor that takes a product as input is usually easier than constructing a functor that
-- outputs a functor. Therefore we use `curry` not only to prove the corresponding equivalence but also to
-- construct functors into `functorStructure`.

def curry {S T U : Structure} (F : StructureFunctor (productStructure S T) U) :
  StructureFunctor S (functorStructure T U) :=
{ map     := λ a => F ⊙ productStructure.mkSndFunctor S T a,
  functor := { mapEquiv  := λ e => { ext := λ b => congrArg F ⟨e, IsEquivalence.refl b⟩,
                                     nat := sorry },
               isFunctor := sorry } }

def uncurry {S T U : Structure} (F : StructureFunctor S (functorStructure T U)) :
  StructureFunctor (productStructure S T) U :=
{ map     := λ P => F P.fst P.snd,
  functor := { mapEquiv  := λ {P Q} e => IsEquivalence.trans ((StructureFunctor.congrArg F e.fst).ext P.snd) (congrArg (F Q.fst) e.snd),
               isFunctor := sorry } }

variable (S T U : Structure)

-- `S → (T → U) ≃ (S × T) → U`

def functorFunctorEquivToFun :
  StructureFunctor (functorStructure S (functorStructure T U))
                   (functorStructure (productStructure S T) U) :=
curry { map     := λ P => P.fst P.snd.fst P.snd.snd,
        functor := { mapEquiv  := λ e => congr (congr e.fst e.snd.fst) e.snd.snd,
                     isFunctor := sorry } }

def functorFunctorEquivInvFun :
  StructureFunctor (functorStructure (productStructure S T) U)
                   (functorStructure S (functorStructure T U)) :=
curry (curry { map     := λ P => P.fst.fst ⟨P.fst.snd, P.snd⟩,
               functor := { mapEquiv  := λ e => congr e.fst.fst ⟨e.fst.snd, e.snd⟩,
                            isFunctor := sorry } })

def functorFunctorEquiv :
  functorStructure S (functorStructure T U) ≃ functorStructure (productStructure S T) U :=
{ toFun  := functorFunctorEquivToFun  S T U,
  invFun := functorFunctorEquivInvFun S T U,
  isInv  := sorry }

-- `S × (T × U) ≃ (S × T) × U`

def productProductEquivToFun :
  StructureFunctor (productStructure S (productStructure T U))
                   (productStructure (productStructure S T) U) :=
{ map     := λ P => ⟨⟨P.fst, P.snd.fst⟩, P.snd.snd⟩,
  functor := { mapEquiv  := λ e => ⟨⟨e.fst, e.snd.fst⟩, e.snd.snd⟩,
               isFunctor := sorry } }

def productProductEquivInvFun :
  StructureFunctor (productStructure (productStructure S T) U)
                   (productStructure S (productStructure T U)) :=
{ map     := λ P => ⟨P.fst.fst, ⟨P.fst.snd, P.snd⟩⟩,
  functor := { mapEquiv  := λ e => ⟨e.fst.fst, ⟨e.fst.snd, e.snd⟩⟩,
               isFunctor := sorry } }

def productProductEquiv :
  productStructure S (productStructure T U) ≃ productStructure (productStructure S T) U :=
{ toFun  := productProductEquivToFun  S T U,
  invFun := productProductEquivInvFun S T U,
  isInv  := sorry }

-- `S → (T × U) ≃ (S → T) × (S → U)`

def functorProductEquivToFun :
  StructureFunctor (functorStructure S (productStructure T U))
                   (productStructure (functorStructure S T) (functorStructure S U)) :=
{ map     := λ F => ⟨productStructure.projFstFunctor T U ⊙ F, productStructure.projSndFunctor T U ⊙ F⟩,
  functor := { mapEquiv  := λ e => ⟨compFun.congrArg_right e, compFun.congrArg_right e⟩,
               isFunctor := sorry } }

def functorProductEquivInvFun :
  StructureFunctor (productStructure (functorStructure S T) (functorStructure S U))
                   (functorStructure S (productStructure T U)) :=
{ map     := λ P => productStructure.mkFunctor P.fst P.snd,
  functor := { mapEquiv  := λ e => { ext := λ a => ⟨e.fst.ext a, e.snd.ext a⟩,
                                     nat := λ ε => ⟨e.fst.nat ε, e.snd.nat ε⟩ },
               isFunctor := sorry } }

def functorProductEquiv :
  functorStructure S (productStructure T U) ≃ productStructure (functorStructure S T) (functorStructure S U) :=
{ toFun  := functorProductEquivToFun  S T U,
  invFun := functorProductEquivInvFun S T U,
  isInv  := sorry }

end FunctorProductEquivalences
