import Structure.Basic

open Morphisms
open Structure
open StructureFunctor



set_option autoBoundImplicitLocal false



-- A functor between two structures induces functors between their setoid and skeleton structures. More
-- specifically, we have the following commutative diagram (modulo equivalence defined on functors), where
-- `S_≈` stands for `setoidStructure S` and `S/≃` stands for `skeletonStructure S`.
--
--    `S` ----> `S_≈` ---> `S/≃`
--     |          |          |
-- `F` |          |          |
--     v          v          v
--    `T` ----> `T_≈` ---> `T/≃`
--
-- The horizontal functors can be "philosophically" regarded as equivalences: Although they cannot be
-- proved to be equivalences, we can see that all structural properties have an analogue in the setoid
-- and skeleton structures. (Also, we can prove certain idempotence properties.)
--
-- This can be understood as the reason why isomorphism can generally be identified with equality: In all
-- operations that preserve structure, in theory we can take the quotient with respect to equivalence/
-- isomorphism and work on the quotient structures.

namespace Forgetfulness

section Setoid

def makeToSetoidStructureFunctor {S T : Structure} (map : S → T) (FF : ∀ {α β : S}, α ≃ β → map α ≈ map β) :
  StructureFunctor S (setoidStructure T) :=
{ map     := map,
  functor := { FF        := FF,
               isFunctor := propFunctor } }

def makeToSetoidStructureFunctorEquiv' {S T : Structure} {F G : StructureFunctor S (setoidStructure T)} (ext : ∀ α, F α ≃ G α) :
  F ≃ G :=
{ ext := ext,
  nat := λ _ => proofIrrel _ _ }

def makeToSetoidStructureFunctorEquiv {S T : Structure} {F G : StructureFunctor S (setoidStructure T)} (ext : ∀ α, F α ≈ G α) :
  F ≃ G :=
makeToSetoidStructureFunctorEquiv' (λ α => let ⟨e⟩ := ext α; e)



def toSetoidFunctor (S : Structure) : StructureFunctor S (setoidStructure S) :=
makeToSetoidStructureFunctor id (toSetoidEquiv S)

@[reducible] def SetoidStructureFunctor (S T : Structure) := StructureFunctor (setoidStructure S) (setoidStructure T)

namespace SetoidStructureFunctor

def makeSetoidStructureFunctor {S T : Structure} (map : S → T) (FF : ∀ {α β : S}, α ≈ β → map α ≈ map β) :
  SetoidStructureFunctor S T :=
makeToSetoidStructureFunctor map FF

def makeSetoidStructureFunctorInverse {S T : Structure} {F : SetoidStructureFunctor S T} {G : SetoidStructureFunctor T S}
                                      (leftInv : LeftInv F G) (rightInv : LeftInv G F) :
  IsInverse F G :=
{ leftInv  := leftInv,
  rightInv := rightInv,
  lrCompat := λ _ => proofIrrel _ _,
  rlCompat := λ _ => proofIrrel _ _ }

def setoidIdempotenceFunctor (S : Structure) : SetoidStructureFunctor (setoidStructure S) S :=
makeSetoidStructureFunctor id (λ ⟨e⟩ => e)

def setoidIdempotence (S : Structure) : setoidStructure (setoidStructure S) ≃ setoidStructure S :=
{ toFun  := setoidIdempotenceFunctor S,
  invFun := toSetoidFunctor (setoidStructure S),
  isInv  := makeSetoidStructureFunctorInverse (makeToSetoidStructureFunctorEquiv Setoid.refl)
                                              (makeToSetoidStructureFunctorEquiv Setoid.refl) }

def setoidFunctor {S T : Structure} (F : StructureFunctor S T) : SetoidStructureFunctor S T :=
makeSetoidStructureFunctor F.map (λ ⟨e⟩ => ⟨F.functor e⟩)

namespace setoidFunctor

theorem respectsEquivalence {S T : Structure} {F₁ F₂ : StructureFunctor S T} :
  F₁ ≃ F₂ → setoidFunctor F₁ ≃ setoidFunctor F₂ :=
λ e => makeToSetoidStructureFunctorEquiv (λ α : S => ⟨⟨e.ext α⟩⟩)

theorem respectsComp {S T U : Structure} (F : StructureFunctor S T) (G : StructureFunctor T U) :
  setoidFunctor (G ⊙ F) ≃ setoidFunctor G ⊙ setoidFunctor F :=
makeToSetoidStructureFunctorEquiv (λ α : S => ⟨⟨IsEquivalence.refl (G (F α))⟩⟩)

theorem respectsId (S : Structure) :
  setoidFunctor (@idFun S) ≃ @idFun (setoidStructure S) :=
makeToSetoidStructureFunctorEquiv (λ α : S => ⟨⟨IsEquivalence.refl α⟩⟩)

end setoidFunctor

def setoidSquare {S T : Structure} (F : StructureFunctor S T) :
  toSetoidFunctor T ⊙ F ≃ setoidFunctor F ⊙ toSetoidFunctor S :=
makeToSetoidStructureFunctorEquiv (λ α => Setoid.refl ((setoidFunctor F) α))

def setoidIdempotenceSquare {S T : Structure} (F : SetoidStructureFunctor S T) :
  F ⊙ setoidIdempotenceFunctor S ≃ setoidIdempotenceFunctor T ⊙ setoidFunctor F :=
makeToSetoidStructureFunctorEquiv (λ α => Setoid.refl (F α))

def setoidFunctorStructure (S T : Structure) := functorStructure (setoidStructure S) (setoidStructure T)

theorem congrMap' {S T : Structure} {F₁ F₂ : SetoidStructureFunctor S T} {α β : S} :
  F₁ ≃ F₂ → α ≃ β → F₁ α ≃ F₂ β :=
λ φ e => StructureFunctor.congrMap φ ⟨e⟩

theorem congrMap {S T : Structure} {F₁ F₂ : SetoidStructureFunctor S T} {α β : S} :
  F₁ ≃ F₂ → α ≈ β → F₁ α ≈ F₂ β :=
λ φ ⟨e⟩ => ⟨congrMap' φ e⟩

end SetoidStructureFunctor

open SetoidStructureFunctor



@[reducible] def SetoidStructureEquiv (S T : Structure) := StructureEquiv (setoidStructure S) (setoidStructure T)

namespace SetoidStructureEquiv

def makeSetoidStructureEquivEquiv' {S T : Structure} {e₁ e₂ : SetoidStructureEquiv S T}
                                   (toFunEquiv : e₁.toFun ≃ e₂.toFun) (invFunEquiv : e₁.invFun ≃ e₂.invFun) :
  e₁ ≃ e₂ :=
{ toFunEquiv    := toFunEquiv,
  invFunEquiv   := invFunEquiv,
  leftInvEquiv  := λ _ => proofIrrel _ _,
  rightInvEquiv := λ _ => proofIrrel _ _ }

def makeSetoidStructureEquivEquiv {S T : Structure} {e₁ e₂ : SetoidStructureEquiv S T}
                                  (toFunEquiv : ∀ α, e₁.toFun α ≈ e₂.toFun α) (invFunEquiv : ∀ α, e₁.invFun α ≈ e₂.invFun α) :
  e₁ ≃ e₂ :=
makeSetoidStructureEquivEquiv' (makeToSetoidStructureFunctorEquiv toFunEquiv) (makeToSetoidStructureFunctorEquiv invFunEquiv)

-- We can convert any equivalence to one between setoid structures.

def toSetoidStructureEquiv {S T : Structure} (e : StructureEquiv S T) : SetoidStructureEquiv S T :=
{ toFun  := setoidFunctor e.toFun,
  invFun := setoidFunctor e.invFun,
  isInv  := makeSetoidStructureFunctorInverse (makeToSetoidStructureFunctorEquiv (λ α => ⟨⟨e.isInv.leftInv.ext  α⟩⟩))
                                              (makeToSetoidStructureFunctorEquiv (λ α => ⟨⟨e.isInv.rightInv.ext α⟩⟩)) }

namespace toSetoidStructureEquiv

theorem respectsSetoid {S T : Structure} {e₁ e₂ : StructureEquiv S T} :
  e₁ ≈ e₂ → toSetoidStructureEquiv e₁ ≈ toSetoidStructureEquiv e₂ :=
λ ⟨φ⟩ => ⟨makeSetoidStructureEquivEquiv' (setoidFunctor.respectsEquivalence φ.toFunEquiv) (setoidFunctor.respectsEquivalence φ.invFunEquiv)⟩

theorem respectsComp {S T U : Structure} (e : S ≃ T) (f : T ≃ U) :
  toSetoidStructureEquiv (StructureEquiv.trans e f) ≈ StructureEquiv.trans (toSetoidStructureEquiv e) (toSetoidStructureEquiv f) :=
⟨makeSetoidStructureEquivEquiv' (setoidFunctor.respectsComp e.toFun f.toFun) (setoidFunctor.respectsComp f.invFun e.invFun)⟩

theorem respectsId (S : Structure) :
  toSetoidStructureEquiv (StructureEquiv.refl S) ≈ StructureEquiv.refl (setoidStructure S) :=
⟨makeSetoidStructureEquivEquiv' (setoidFunctor.respectsId S) (setoidFunctor.respectsId S)⟩

theorem respectsInv {S T : Structure} (e : S ≃ T) :
  toSetoidStructureEquiv (StructureEquiv.symm e) ≈ StructureEquiv.symm (toSetoidStructureEquiv e) :=
⟨makeSetoidStructureEquivEquiv' (IsEquivalence.refl (setoidFunctor e.invFun)) (IsEquivalence.refl (setoidFunctor e.toFun))⟩

def genFun : GeneralizedFunctor.Functor (S := universeStructure) (T := universeStructure) setoidStructure :=
{ FF        := toSetoidStructureEquiv,
  isFunctor := { respectsSetoid := respectsSetoid,
                 respectsComp   := respectsComp,
                 respectsId     := respectsId,
                 respectsInv    := respectsInv } }

end toSetoidStructureEquiv

end SetoidStructureEquiv

open SetoidStructureEquiv



-- An `InstanceEquiv` of a `SetoidStructureEquiv` is what we expect it to be.

@[reducible] def SetoidInstanceEquiv {S T : Structure} (e : S ≃ T) (a : S) (b : T) : Prop :=
InstanceEquiv (toSetoidStructureEquiv e) a b

namespace SetoidInstanceEquiv

notation:25 a:26 " ≈[" e:0 "] " b:26 => SetoidInstanceEquiv e a b

theorem refl' (S     : Structure)                         {a b : S} (h : a ≈ b)   :
  a ≈[id_ S] b :=
h

theorem refl  (S     : Structure)                         (a : S)                 :
  a ≈[id_ S] a :=
refl' S (Setoid.refl a)

theorem symm  {S T   : Structure} (e : S ≃ T)             (a : S) (b : T)         :
  a ≈[e] b → b ≈[e⁻¹] a :=
InstanceEquiv.symm (toSetoidStructureEquiv e) a b

theorem trans {S T U : Structure} (e : S ≃ T) (f : T ≃ U) (a : S) (b : T) (c : U) :
  a ≈[e] b → b ≈[f] c → a ≈[f • e] c :=
λ φ ψ => let χ : f.toFun (e.toFun a) ≈ c := InstanceEquiv.trans (toSetoidStructureEquiv e) (toSetoidStructureEquiv f) a b c φ ψ;
         χ

theorem setoidInstanceEquiv' {S T : Structure} (e : SetoidStructureEquiv S T) (a : S) (b : T) :
  a ≃[e] b ↔ e.toFun a ≈ b :=
equivInSetoidStructure T (e.toFun a) b

theorem setoidInstanceEquiv {S T : Structure} (e : S ≃ T) (a : S) (b : T) :
  a ≈[e] b ↔ e.toFun a ≈ b :=
Iff.refl (e.toFun a ≈ b)

theorem congrArgEquiv' {S T : Structure} {e₁ e₂ : SetoidStructureEquiv S T} (h : e₁ ≈ e₂) (a : S) (b : T) :
  a ≃[e₁] b → a ≃[e₂] b :=
let ⟨φ⟩ := h;
InstanceEquiv.congrArgEquiv φ a b

theorem congrArgEquiv {S T : Structure} {e₁ e₂ : S ≃ T} (h : e₁ ≈ e₂) (a : S) (b : T) :
  a ≈[e₁] b → a ≈[e₂] b :=
congrArgEquiv' (toSetoidStructureEquiv.respectsSetoid h) a b

end SetoidInstanceEquiv

end Setoid

open SetoidStructureFunctor



section Skeleton

def makeToSkeletonStructureFunctor {S T : Structure} (map : S → StructureQuotient T) (FF : ∀ {α β : S}, α ≃ β → map α = map β) :
  StructureFunctor S (skeletonStructure T) :=
{ map     := map,
  functor := { FF        := FF,
               isFunctor := propFunctor } }

def makeToSkeletonStructureFunctorEquiv' {S T : Structure} {F G : StructureFunctor S (skeletonStructure T)} (ext : ∀ α, F α ≃ G α) :
  F ≃ G :=
{ ext := ext,
  nat := λ _ => proofIrrel _ _ }

def makeToSkeletonStructureFunctorEquiv {S T : Structure} {F G : StructureFunctor S (skeletonStructure T)} (ext : ∀ α, F α = G α) :
  F ≃ G :=
makeToSkeletonStructureFunctorEquiv' ext

def setoidToSkeletonFunctor (S : Structure) : StructureFunctor (setoidStructure S) (skeletonStructure S) :=
makeToSkeletonStructureFunctor (λ α => Quotient.mk α) (λ e => Quotient.sound e)

def toSkeletonFunctor (S : Structure) : StructureFunctor S (skeletonStructure S) :=
setoidToSkeletonFunctor S ⊙ toSetoidFunctor S

@[reducible] def SkeletonStructureFunctor (S T : Structure) := StructureFunctor (skeletonStructure S) (skeletonStructure T)

def makeSkeletonStructureFunctor {S T : Structure} (map : StructureQuotient S → StructureQuotient T) :
  SkeletonStructureFunctor S T :=
makeToSkeletonStructureFunctor map (congrArg map)

def makeSkeletonStructureFunctorInverse {S T : Structure} {F : SkeletonStructureFunctor S T} {G : SkeletonStructureFunctor T S}
                                        (leftInv : LeftInv F G) (rightInv : LeftInv G F) :
  IsInverse F G :=
{ leftInv  := leftInv,
  rightInv := rightInv,
  lrCompat := λ _ => proofIrrel _ _,
  rlCompat := λ _ => proofIrrel _ _ }

def skeletonSetoidIdempotenceFunctor (S : Structure) : StructureFunctor (setoidStructure (skeletonStructure S)) (skeletonStructure S) :=
makeToSkeletonStructureFunctor id (λ ⟨e⟩ => e)

def skeletonSetoidIdempotence (S : Structure) : setoidStructure (skeletonStructure S) ≃ skeletonStructure S :=
{ toFun  := skeletonSetoidIdempotenceFunctor S,
  invFun := toSetoidFunctor (skeletonStructure S),
  isInv  := { leftInv  := makeToSetoidStructureFunctorEquiv Setoid.refl,
              rightInv := makeToSkeletonStructureFunctorEquiv Eq.refl,
              lrCompat := λ _ => proofIrrel _ _,
              rlCompat := λ _ => proofIrrel _ _ } }

def skeletonIdempotenceFunctor (S : Structure) : SkeletonStructureFunctor (skeletonStructure S) S :=
makeSkeletonStructureFunctor (Quotient.lift id (λ a b ⟨e⟩ => e))

def skeletonIdempotence (S : Structure) : skeletonStructure (skeletonStructure S) ≃ skeletonStructure S :=
{ toFun  := skeletonIdempotenceFunctor S,
  invFun := toSkeletonFunctor (skeletonStructure S),
  isInv  := makeSkeletonStructureFunctorInverse (makeToSkeletonStructureFunctorEquiv
                                                   (λ a => let r := Quotient.existsRep a;
                                                           let h₁ : (skeletonIdempotenceFunctor S) (Quotient.mk r.1) = r.1 := rfl;
                                                           let h₂ := congrArg Quotient.mk h₁;
                                                           Eq.subst (motive := λ b => Quotient.mk ((skeletonIdempotenceFunctor S) b) = b) r.2 h₂))
                                                (makeToSkeletonStructureFunctorEquiv Eq.refl) }

variable {S T : Structure}

def skeletonMap (F : SetoidStructureFunctor S T) : skeletonStructure S → skeletonStructure T :=
Quotient.lift (Quotient.mk ∘ F.map) (λ _ _ => Quotient.sound ∘ F.functor.FF)

def skeletonFromSetoidFunctor (F : SetoidStructureFunctor S T) : SkeletonStructureFunctor S T :=
makeSkeletonStructureFunctor (skeletonMap F)

def skeletonSetoidIdempotenceSquare {S T : Structure} (F : SkeletonStructureFunctor S T) :
  F ⊙ skeletonSetoidIdempotenceFunctor S ≃ skeletonSetoidIdempotenceFunctor T ⊙ setoidFunctor F :=
sorry

def skeletonFunctor (F : StructureFunctor S T) : SkeletonStructureFunctor S T :=
skeletonFromSetoidFunctor (setoidFunctor F)

def setoidToSkeletonSquare {S T : Structure} (F : StructureFunctor S T) :
  setoidToSkeletonFunctor T ⊙ setoidFunctor F ≃ skeletonFunctor F ⊙ setoidToSkeletonFunctor S :=
makeToSkeletonStructureFunctorEquiv (λ _ => rfl)

def skeletonSquare {S T : Structure} (F : StructureFunctor S T) :
  toSkeletonFunctor T ⊙ F ≃ skeletonFunctor F ⊙ toSkeletonFunctor S :=
makeToSkeletonStructureFunctorEquiv (λ _ => rfl)

def skeletonIdempotenceSquare {S T : Structure} (F : SkeletonStructureFunctor S T) :
  F ⊙ skeletonIdempotenceFunctor S ≃ skeletonIdempotenceFunctor T ⊙ skeletonFunctor F :=
sorry

end Skeleton

end Forgetfulness
