--  An abstract formalization of "isomorphism is equality up to relabeling"
-- -------------------------------------------------------------------------
--
-- See `README.md` for more info.
--
-- This file contains the definition of `Structure` as a higher groupoid, along with related concepts, up
-- to a structure of structures called `universeStructure`.



import Structure.Generic.Axioms

import mathlib4_experiments.Data.Notation



#exit









structure Iff' {α β : Sort v} [IsType α] [IsType β] (a : α) (b : β) where
(mp  : a → b)
(mpr : b → a)

infix:20 " <->' " => Iff'
infix:20 " ↔' "   => Iff'

def Iff'.toIff {a b : Prop} (h : a ↔' b) : a ↔ b := ⟨h.mp, h.mpr⟩
instance (a b : Prop) : Coe (a ↔' b) (a ↔ b) := ⟨Iff'.toIff⟩



-- A type is an instance of `HasGeneralStructure` if it has an equivalence that satisfies the isomorphism
-- axioms. If equivalences of equivalences are propositions, this can be specialized to an instance of
-- `HasStructure`. We optimize for this case but sometimes need the more general version.

class HasGeneralStructure (α : Sort u) where
{equivType   : Sort v}
[equivIsType : IsTypeWithFunctorialEquivalence equivType]
(M           : GeneralizedRelation α equivType)
[hasIsos     : HasIsomorphisms M]

namespace HasGeneralStructure

variable {α : Sort u} [h : HasGeneralStructure α]

instance hasEquivalence : HasEquivalence α α := ⟨h.M⟩
instance isTypeWithEquiv : IsTypeWithFunctorialEquivalence h.equivType := h.equivIsType
instance hasIso : HasIsomorphisms h.M := h.hasIsos

instance hasInstEquiv : HasInstanceEquivalence α :=
{ equivType := h.equivType,
  Equiv     := h.M,
  isEquiv   := isoEquiv h.M }

instance : IsTypeWithFunctorialEquivalence (HasEquivalence.γ α α) := h.equivIsType
instance : HasIsomorphisms (@HasEquivalence.Equiv α α hasEquivalence) := hasIso

def id___ (a : α) : a ≃ a := ident h.M a

def comp_congrArg_left  {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} : g₁ ≃ g₂ → g₁ • f ≃ g₂ • f := (isTypeWithEquiv.funCond (b ≃ c) (a ≃ c) _).coe (hasIso.trans_left_functor  f)
def comp_congrArg_right {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} : f₁ ≃ f₂ → g • f₁ ≃ g • f₂ := (isTypeWithEquiv.funCond (a ≃ b) (a ≃ c) _).coe (hasIso.trans_right_functor g)
def comp_congrArg {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c}  : f₁ ≃ f₂ → g₁ ≃ g₂ → g₁ • f₁ ≃ g₂ • f₂ :=
λ h₁ h₂ => HasTrans.trans (comp_congrArg_left h₂) (comp_congrArg_right h₁)

def inv_congrArg {a b : α} {f₁ f₂ : a ≃ b} : f₁ ≃ f₂ → f₁⁻¹ ≃ f₂⁻¹ := (isTypeWithEquiv.funCond (a ≃ b) (b ≃ a) _).coe hasIso.symm_functor

        def assoc    {a b c d : α} (f : a ≃ b) (g : b ≃ c) (h : c ≃ d) : h • (g • f) ≃ (h • g) • f := hasIso.assoc    f g h
        def assoc'   {a b c d : α} (f : a ≃ b) (g : b ≃ c) (h : c ≃ d) : (h • g) • f ≃ h • (g • f) := HasSymm.symm (assoc f g h)
@[simp] def leftId   {a b     : α} (f : a ≃ b)                         : id___ b • f ≃ f           := hasIso.leftId   f
@[simp] def rightId  {a b     : α} (f : a ≃ b)                         : f • id___ a ≃ f           := hasIso.rightId  f
@[simp] def leftInv  {a b     : α} (f : a ≃ b)                         : f⁻¹ • f     ≃ id___ a     := hasIso.leftInv  f
@[simp] def rightInv {a b     : α} (f : a ≃ b)                         : f • f⁻¹     ≃ id___ b     := hasIso.rightInv f
@[simp] def invInv   {a b     : α} (f : a ≃ b)                         : (f⁻¹)⁻¹     ≃ f           := hasIso.invInv   f
@[simp] def compInv  {a b c   : α} (f : a ≃ b) (g : b ≃ c)             : (g • f)⁻¹   ≃ f⁻¹ • g⁻¹   := hasIso.compInv  f g
@[simp] def idInv    (a       : α)                                     : (id___ a)⁻¹ ≃ id___ a     := hasIso.idInv    a

def comp_subst  {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : f₁ ≃ f₂ → g₁ ≃ g₂ → g₂ • f₂ ≃ e → g₁ • f₁ ≃ e :=
λ h₁ h₂ h₃ => HasTrans.trans (comp_congrArg h₁ h₂) h₃
def comp_subst' {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : f₁ ≃ f₂ → g₁ ≃ g₂ → e ≃ g₁ • f₁ → e ≃ g₂ • f₂ :=
λ h₁ h₂ h₃ => HasTrans.trans h₃ (comp_congrArg h₁ h₂)

def comp_subst_left   {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : g₁ ≃ g₂ → g₂ • f ≃ e → g₁ • f ≃ e :=
λ h₁ h₂ => HasTrans.trans (comp_congrArg_left h₁) h₂
def comp_subst_left'  {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : g₁ ≃ g₂ → e ≃ g₁ • f → e ≃ g₂ • f :=
λ h₁ h₂ => HasTrans.trans h₂ (comp_congrArg_left h₁)

def comp_subst_right  {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} {e : a ≃ c} : f₁ ≃ f₂ → g • f₂ ≃ e → g • f₁ ≃ e :=
λ h₁ h₂ => HasTrans.trans (comp_congrArg_right h₁) h₂
def comp_subst_right' {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} {e : a ≃ c} : f₁ ≃ f₂ → e ≃ g • f₁ → e ≃ g • f₂ :=
λ h₁ h₂ => HasTrans.trans h₂ (comp_congrArg_right h₁)

def inv_subst  {a b : α} {f₁ f₂ : a ≃ b} {e : b ≃ a} : f₁ ≃ f₂ → f₂⁻¹ ≃ e → f₁⁻¹ ≃ e :=
λ h₁ h₂ => HasTrans.trans (inv_congrArg h₁) h₂
def inv_subst' {a b : α} {f₁ f₂ : a ≃ b} {e : b ≃ a} : f₁ ≃ f₂ → e ≃ f₁⁻¹ → e ≃ f₂⁻¹ :=
λ h₁ h₂ => HasSymm.symm (inv_subst (HasSymm.symm h₁) (HasSymm.symm h₂))

def leftCancelId  {a b : α} {f : a ≃ b} {e : b ≃ b} : e ≃ id___ b → e • f ≃ f :=
λ h => comp_subst_left  h (leftId  f)
def rightCancelId {a b : α} {f : a ≃ b} {e : a ≃ a} : e ≃ id___ a → f • e ≃ f :=
λ h => comp_subst_right h (rightId f)

def applyAssoc_left   {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  h • (g • f) ≃ e → (h • g) • f ≃ e :=
λ h₁ => HasTrans.trans (assoc' f g h) h₁
def applyAssoc_left'  {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  (h • g) • f ≃ e → h • (g • f) ≃ e :=
λ h₁ => HasTrans.trans (assoc f g h) h₁
def applyAssoc_right  {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  e ≃ h • (g • f) → e ≃ (h • g) • f :=
λ h₁ => HasTrans.trans h₁ (assoc f g h)
def applyAssoc_right' {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} :
  e ≃ (h • g) • f → e ≃ h • (g • f) :=
λ h₁ => HasTrans.trans h₁ (assoc' f g h)

def applyAssoc  {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : a ≃ β₁} {f₂ : a ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ d} {h₂ : γ₂ ≃ d} :
  h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) → (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ :=
λ h => applyAssoc_right  (applyAssoc_left  h)
def applyAssoc' {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : a ≃ β₁} {f₂ : a ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ d} {h₂ : γ₂ ≃ d} :
  (h₁ • g₁) • f₁ ≃ (h₂ • g₂) • f₂ → h₁ • (g₁ • f₁) ≃ h₂ • (g₂ • f₂) :=
λ h => applyAssoc_right' (applyAssoc_left' h)

@[simp] def leftCancel'     {a b c : α} (f : a ≃ b) (g : b ≃ c) : (g⁻¹ • g) • f ≃ f := leftCancelId  (leftInv  g)
@[simp] def leftCancel      {a b c : α} (f : a ≃ b) (g : b ≃ c) : g⁻¹ • (g • f) ≃ f := applyAssoc_left' (leftCancel'     f g)
@[simp] def leftCancelInv'  {a b c : α} (f : a ≃ b) (g : c ≃ b) : (g • g⁻¹) • f ≃ f := leftCancelId  (rightInv g)
@[simp] def leftCancelInv   {a b c : α} (f : a ≃ b) (g : c ≃ b) : g • (g⁻¹ • f) ≃ f := applyAssoc_left' (leftCancelInv'  f g)
@[simp] def rightCancel'    {a b c : α} (f : a ≃ b) (g : c ≃ a) : f • (g • g⁻¹) ≃ f := rightCancelId (rightInv g)
@[simp] def rightCancel     {a b c : α} (f : a ≃ b) (g : c ≃ a) : (f • g) • g⁻¹ ≃ f := applyAssoc_left  (rightCancel'    f g)
@[simp] def rightCancelInv' {a b c : α} (f : a ≃ b) (g : a ≃ c) : f • (g⁻¹ • g) ≃ f := rightCancelId (leftInv  g)
@[simp] def rightCancelInv  {a b c : α} (f : a ≃ b) (g : a ≃ c) : (f • g⁻¹) • g ≃ f := applyAssoc_left  (rightCancelInv' f g)

def leftMulInv  {a b c : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g : b ≃ c) : g • f₁ ≃ f₂ ↔' f₁ ≃ g⁻¹ • f₂ :=
⟨λ h => comp_subst_right' h (HasSymm.symm (leftCancel f₁ g)), λ h => comp_subst_right h (leftCancelInv f₂ g)⟩
def leftMulInv' {a b c : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g : c ≃ b) : g⁻¹ • f₁ ≃ f₂ ↔' f₁ ≃ g • f₂ :=
⟨λ h => comp_subst_right' h (HasSymm.symm (leftCancelInv f₁ g)), λ h => comp_subst_right h (leftCancel f₂ g)⟩

@[simp] def leftMul {a b c : α} (f₁ f₂ : a ≃ b) (g : b ≃ c) : g • f₁ ≃ g • f₂ ↔' f₁ ≃ f₂ :=
⟨λ h => HasTrans.trans ((leftMulInv f₁ (g • f₂) g).mp h) (leftCancel f₂ g), comp_congrArg_right⟩

def rightMulInv  {a b c : α} (f₁ : a ≃ c) (f₂ : b ≃ c) (g : b ≃ a) : f₁ • g ≃ f₂ ↔' f₁ ≃ f₂ • g⁻¹ :=
⟨λ h => comp_subst_left' h (HasSymm.symm (rightCancel f₁ g)), λ h => comp_subst_left h (rightCancelInv f₂ g)⟩
def rightMulInv' {a b c : α} (f₁ : a ≃ c) (f₂ : b ≃ c) (g : a ≃ b) : f₁ • g⁻¹ ≃ f₂ ↔' f₁ ≃ f₂ • g :=
⟨λ h => comp_subst_left' h (HasSymm.symm (rightCancelInv f₁ g)), λ h => comp_subst_left h (rightCancel f₂ g)⟩

@[simp] def rightMul {a b c : α} (f₁ f₂ : a ≃ b) (g : c ≃ a) : f₁ • g ≃ f₂ • g ↔' f₁ ≃ f₂ :=
⟨λ h => HasTrans.trans ((rightMulInv f₁ (f₂ • g) g).mp h) (rightCancel f₂ g), comp_congrArg_left⟩

def eqInvIffInvEq {a b : α} (f : a ≃ b) (g : b ≃ a) : f ≃ g⁻¹ ↔' f⁻¹ ≃ g :=
⟨λ h => inv_subst h (invInv g), λ h => inv_subst' h (HasSymm.symm (invInv f))⟩

@[simp] def eqIffEqInv {a b : α} (f₁ f₂ : a ≃ b) : f₁⁻¹ ≃ f₂⁻¹ ↔' f₁ ≃ f₂ :=
⟨λ h => HasTrans.trans ((eqInvIffInvEq f₁ f₂⁻¹).mpr h) (invInv f₂), inv_congrArg⟩

@[simp] def leftRightMul {a b c d : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g₁ : b ≃ d) (g₂ : c ≃ d) :
  g₂⁻¹ • g₁ ≃ f₂ • f₁⁻¹ ↔' g₁ • f₁ ≃ g₂ • f₂ :=
⟨λ h => let h₁ := (rightMulInv (g₂⁻¹ • g₁) f₂ f₁).mpr h;
        let h₂ := applyAssoc_left' h₁;
        (leftMulInv' (g₁ • f₁) f₂ g₂).mp h₂,
 λ h => let h₁ := (rightMulInv g₁ (g₂ • f₂) f₁).mp h;
        let h₂ := applyAssoc_right' h₁;
        (leftMulInv' g₁ (f₂ • f₁⁻¹) g₂).mpr h₂⟩

def swapInv  {a b c d : α} (f₁ : a ≃ b) (f₂ : c ≃ d) (g₁ : d ≃ b) (g₂ : c ≃ a) :
  g₁⁻¹ • f₁ ≃ f₂ • g₂⁻¹ → f₁⁻¹ • g₁ ≃ g₂ • f₂⁻¹ :=
λ h => (leftRightMul f₂ g₂ g₁ f₁).mpr (HasSymm.symm ((leftRightMul g₂ f₂ f₁ g₁).mp h))

def swapInv' {a b c d : α} (f₁ : a ≃ b) (f₂ : c ≃ d) (g₁ : d ≃ b) (g₂ : c ≃ a) :
  f₂ • g₂⁻¹ ≃ g₁⁻¹ • f₁ → g₂ • f₂⁻¹ ≃ f₁⁻¹ • g₁ :=
λ h => HasSymm.symm (swapInv f₁ f₂ g₁ g₂ (HasSymm.symm h))

end HasGeneralStructure



-- A variant of `HasGeneralStructure` where `equivType` is `BundledSetoid`, i.e. equivalences of
-- equivalences are propositions.

class HasStructure (α : Sort u) where
(M       : GeneralizedRelation α BundledSetoid)
[hasIsos : HasIsomorphisms M]

namespace HasStructure

variable {α : Sort u} [h : HasStructure α]

instance hasGeneralStructure : HasGeneralStructure α :=
{ equivType := BundledSetoid,
  M         := h.M,
  hasIsos   := h.hasIsos }

instance hasIso : HasIsomorphisms h.M := h.hasIsos
instance equivSetoid (a b : α) : Setoid (IsType.type (a ≃ b)) := BundledSetoid.isSetoid (a ≃ b)

def id_ (a : α) : a ≃ a := hasGeneralStructure.id___ a
def id' {a : α} := id_ a

theorem comp_congrArg_left  {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} : g₁ ≈ g₂ → g₁ • f ≈ g₂ • f := hasGeneralStructure.comp_congrArg_left
theorem comp_congrArg_right {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} : f₁ ≈ f₂ → g • f₁ ≈ g • f₂ := hasGeneralStructure.comp_congrArg_right
theorem comp_congrArg {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c}  : f₁ ≈ f₂ → g₁ ≈ g₂ → g₁ • f₁ ≈ g₂ • f₂ := hasGeneralStructure.comp_congrArg

theorem inv_congrArg  {a b : α} {f₁ f₂ : a ≃ b} : f₁ ≈ f₂ → f₁⁻¹ ≈ f₂⁻¹ := hasGeneralStructure.inv_congrArg

        theorem assoc    {a b c d : α} (f : a ≃ b) (g : b ≃ c) (h : c ≃ d) : h • (g • f) ≈ (h • g) • f := hasGeneralStructure.assoc    f g h
        theorem assoc'   {a b c d : α} (f : a ≃ b) (g : b ≃ c) (h : c ≃ d) : (h • g) • f ≈ h • (g • f) := hasGeneralStructure.assoc' f g h
@[simp] theorem leftId   {a b     : α} (f : a ≃ b)                         : id_ b • f ≈ f             := hasGeneralStructure.leftId   f
@[simp] theorem rightId  {a b     : α} (f : a ≃ b)                         : f • id_ a ≈ f             := hasGeneralStructure.rightId  f
@[simp] theorem leftInv  {a b     : α} (f : a ≃ b)                         : f⁻¹ • f   ≈ id_ a         := hasGeneralStructure.leftInv  f
@[simp] theorem rightInv {a b     : α} (f : a ≃ b)                         : f • f⁻¹   ≈ id_ b         := hasGeneralStructure.rightInv f
@[simp] theorem invInv   {a b     : α} (f : a ≃ b)                         : (f⁻¹)⁻¹   ≈ f             := hasGeneralStructure.invInv   f
@[simp] theorem compInv  {a b c   : α} (f : a ≃ b) (g : b ≃ c)             : (g • f)⁻¹ ≈ f⁻¹ • g⁻¹     := hasGeneralStructure.compInv  f g
@[simp] theorem idInv    (a       : α)                                     : (id_ a)⁻¹ ≈ id_ a         := hasGeneralStructure.idInv    a

theorem comp_subst  {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → g₁ ≈ g₂ → g₂ • f₂ ≈ e → g₁ • f₁ ≈ e := hasGeneralStructure.comp_subst
theorem comp_subst' {a b c : α} {f₁ f₂ : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → g₁ ≈ g₂ → e ≈ g₁ • f₁ → e ≈ g₂ • f₂ := hasGeneralStructure.comp_subst'

theorem comp_subst_left   {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : g₁ ≈ g₂ → g₂ • f ≈ e → g₁ • f ≈ e := hasGeneralStructure.comp_subst_left
theorem comp_subst_left'  {a b c : α} {f : a ≃ b} {g₁ g₂ : b ≃ c} {e : a ≃ c} : g₁ ≈ g₂ → e ≈ g₁ • f → e ≈ g₂ • f := hasGeneralStructure.comp_subst_left'

theorem comp_subst_right  {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → g • f₂ ≈ e → g • f₁ ≈ e := hasGeneralStructure.comp_subst_right
theorem comp_subst_right' {a b c : α} {f₁ f₂ : a ≃ b} {g : b ≃ c} {e : a ≃ c} : f₁ ≈ f₂ → e ≈ g • f₁ → e ≈ g • f₂ := hasGeneralStructure.comp_subst_right'

theorem inv_subst  {a b : α} {f₁ f₂ : a ≃ b} {e : b ≃ a} : f₁ ≈ f₂ → f₂⁻¹ ≈ e → f₁⁻¹ ≈ e := hasGeneralStructure.inv_subst
theorem inv_subst' {a b : α} {f₁ f₂ : a ≃ b} {e : b ≃ a} : f₁ ≈ f₂ → e ≈ f₁⁻¹ → e ≈ f₂⁻¹ := hasGeneralStructure.inv_subst'

theorem leftCancelId  {a b : α} {f : a ≃ b} {e : b ≃ b} : e ≈ id' → e • f ≈ f := hasGeneralStructure.leftCancelId
theorem rightCancelId {a b : α} {f : a ≃ b} {e : a ≃ a} : e ≈ id' → f • e ≈ f := hasGeneralStructure.rightCancelId

theorem applyAssoc_left   {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} : h • (g • f) ≈ e → (h • g) • f ≈ e := hasGeneralStructure.applyAssoc_left
theorem applyAssoc_left'  {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} : (h • g) • f ≈ e → h • (g • f) ≈ e := hasGeneralStructure.applyAssoc_left'
theorem applyAssoc_right  {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} : e ≈ h • (g • f) → e ≈ (h • g) • f := hasGeneralStructure.applyAssoc_right
theorem applyAssoc_right' {a b c d : α} {f : a ≃ b} {g : b ≃ c} {h : c ≃ d} {e : a ≃ d} : e ≈ (h • g) • f → e ≈ h • (g • f) := hasGeneralStructure.applyAssoc_right'

theorem applyAssoc  {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : a ≃ β₁} {f₂ : a ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ d} {h₂ : γ₂ ≃ d} :
  h₁ • (g₁ • f₁) ≈ h₂ • (g₂ • f₂) → (h₁ • g₁) • f₁ ≈ (h₂ • g₂) • f₂ :=
hasGeneralStructure.applyAssoc
theorem applyAssoc' {a β₁ β₂ γ₁ γ₂ d : α} {f₁ : a ≃ β₁} {f₂ : a ≃ β₂} {g₁ : β₁ ≃ γ₁} {g₂ : β₂ ≃ γ₂} {h₁ : γ₁ ≃ d} {h₂ : γ₂ ≃ d} :
  (h₁ • g₁) • f₁ ≈ (h₂ • g₂) • f₂ → h₁ • (g₁ • f₁) ≈ h₂ • (g₂ • f₂) :=
hasGeneralStructure.applyAssoc'

@[simp] theorem leftCancel'     {a b c : α} (f : a ≃ b) (g : b ≃ c) : (g⁻¹ • g) • f ≈ f := hasGeneralStructure.leftCancel'     f g
@[simp] theorem leftCancel      {a b c : α} (f : a ≃ b) (g : b ≃ c) : g⁻¹ • (g • f) ≈ f := hasGeneralStructure.leftCancel      f g
@[simp] theorem leftCancelInv'  {a b c : α} (f : a ≃ b) (g : c ≃ b) : (g • g⁻¹) • f ≈ f := hasGeneralStructure.leftCancelInv'  f g
@[simp] theorem leftCancelInv   {a b c : α} (f : a ≃ b) (g : c ≃ b) : g • (g⁻¹ • f) ≈ f := hasGeneralStructure.leftCancelInv   f g
@[simp] theorem rightCancel'    {a b c : α} (f : a ≃ b) (g : c ≃ a) : f • (g • g⁻¹) ≈ f := hasGeneralStructure.rightCancel'    f g
@[simp] theorem rightCancel     {a b c : α} (f : a ≃ b) (g : c ≃ a) : (f • g) • g⁻¹ ≈ f := hasGeneralStructure.rightCancel     f g
@[simp] theorem rightCancelInv' {a b c : α} (f : a ≃ b) (g : a ≃ c) : f • (g⁻¹ • g) ≈ f := hasGeneralStructure.rightCancelInv' f g
@[simp] theorem rightCancelInv  {a b c : α} (f : a ≃ b) (g : a ≃ c) : (f • g⁻¹) • g ≈ f := hasGeneralStructure.rightCancelInv  f g

theorem leftMulInv  {a b c : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g : b ≃ c) : g • f₁ ≈ f₂ ↔ f₁ ≈ g⁻¹ • f₂ := Iff'.toIff (hasGeneralStructure.leftMulInv  f₁ f₂ g)
theorem leftMulInv' {a b c : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g : c ≃ b) : g⁻¹ • f₁ ≈ f₂ ↔ f₁ ≈ g • f₂ := Iff'.toIff (hasGeneralStructure.leftMulInv' f₁ f₂ g)

@[simp] theorem leftMul {a b c : α} (f₁ f₂ : a ≃ b) (g : b ≃ c) : g • f₁ ≈ g • f₂ ↔ f₁ ≈ f₂ := Iff'.toIff (hasGeneralStructure.leftMul f₁ f₂ g)

theorem rightMulInv  {a b c : α} (f₁ : a ≃ c) (f₂ : b ≃ c) (g : b ≃ a) : f₁ • g ≈ f₂ ↔ f₁ ≈ f₂ • g⁻¹ := Iff'.toIff (hasGeneralStructure.rightMulInv  f₁ f₂ g)
theorem rightMulInv' {a b c : α} (f₁ : a ≃ c) (f₂ : b ≃ c) (g : a ≃ b) : f₁ • g⁻¹ ≈ f₂ ↔ f₁ ≈ f₂ • g := Iff'.toIff (hasGeneralStructure.rightMulInv' f₁ f₂ g)

@[simp] theorem rightMul {a b c : α} (f₁ f₂ : a ≃ b) (g : c ≃ a) : f₁ • g ≈ f₂ • g ↔ f₁ ≈ f₂ := Iff'.toIff (hasGeneralStructure.rightMul f₁ f₂ g)

theorem eqInvIffInvEq {a b : α} (f : a ≃ b) (g : b ≃ a) : f ≈ g⁻¹ ↔ f⁻¹ ≈ g := Iff'.toIff (hasGeneralStructure.eqInvIffInvEq f g)

@[simp] theorem eqIffEqInv {a b : α} (f₁ f₂ : a ≃ b) : f₁⁻¹ ≈ f₂⁻¹ ↔ f₁ ≈ f₂ := Iff'.toIff (hasGeneralStructure.eqIffEqInv f₁ f₂)

@[simp] theorem leftRightMul {a b c d : α} (f₁ : a ≃ b) (f₂ : a ≃ c) (g₁ : b ≃ d) (g₂ : c ≃ d) :
  g₂⁻¹ • g₁ ≈ f₂ • f₁⁻¹ ↔ g₁ • f₁ ≈ g₂ • f₂ :=
Iff'.toIff (hasGeneralStructure.leftRightMul f₁ f₂ g₁ g₂)

theorem swapInv  {a b c d : α} (f₁ : a ≃ b) (f₂ : c ≃ d) (g₁ : d ≃ b) (g₂ : c ≃ a) :
  g₁⁻¹ • f₁ ≈ f₂ • g₂⁻¹ → f₁⁻¹ • g₁ ≈ g₂ • f₂⁻¹ :=
hasGeneralStructure.swapInv f₁ f₂ g₁ g₂

theorem swapInv' {a b c d : α} (f₁ : a ≃ b) (f₂ : c ≃ d) (g₁ : d ≃ b) (g₂ : c ≃ a) :
  f₂ • g₂⁻¹ ≈ g₁⁻¹ • f₁ → g₂ • f₂⁻¹ ≈ f₁⁻¹ • g₁ :=
hasGeneralStructure.swapInv' f₁ f₂ g₁ g₂

end HasStructure

open HasStructure



instance propHasStructure                               : HasStructure Prop := ⟨RelationWithSetoid.relWithEq Iff⟩
def      typeHasStructure   (α : Sort u)                : HasStructure α    := ⟨RelationWithSetoid.relWithEq Eq⟩
def      setoidHasStructure (α : Sort u) [s : Setoid α] : HasStructure α    := ⟨RelationWithSetoid.relWithEq s.r⟩



-- We bundle a type with a structure together because we frequently parameterize definitions by
-- arbitrary structures.

structure Structure where
(α         : Sort u)
[hasStruct : HasStructure α]

namespace Structure

instance structureIsType : IsType Structure := ⟨Structure.α⟩

def iso (S : Structure) : RelationWithSetoid (IsType.type S) := S.hasStruct.M

variable {S : Structure}

instance hasStructure : HasStructure (IsType.type S) := S.hasStruct
instance hasGeneralStructure : HasGeneralStructure (IsType.type S) := HasStructure.hasGeneralStructure (h := hasStructure)
instance hasIso : HasIsomorphisms (t := BundledSetoid.isTypeWithFunctorialEquivalence) (iso S) := hasGeneralStructure.hasIso

instance structureIsTypeWithEquiv : IsTypeWithEquivalence Structure :=
{ type  := Structure.α,
  equiv := λ S => HasGeneralStructure.hasInstEquiv (h := hasGeneralStructure) }

def id__ (a : S) : a ≃ a := hasStructure.id_ a
def id'' {a : S} := id__ a

end Structure

open Structure

def defaultStructure (α : Sort u) [h : HasStructure α] : Structure :=
{ α         := α,
  hasStruct := h }

def instanceStructure (α : Sort u) := @defaultStructure α (typeHasStructure α)
def setoidInstanceStructure (α : Sort u) [s : Setoid α] := @defaultStructure α (setoidHasStructure α)
def bundledSetoidStructure (S : BundledSetoid) := setoidInstanceStructure (IsType.type S)



-- Since each equivalence/isomorphism of a structure is a bundled setoid, we can treat it as a
-- structure as well. This partially recovers the inductive definition of a structure as an ∞-groupoid.

def isoStructure {S : Structure} (a b : S) := bundledSetoidStructure (iso S a b)



-- We can "forget" the data held inside a `Structure` on two levels, obtaining modified instances of
-- `Structure`:
--
-- 1. We can truncate the equivalence to an equivalence _relation_, obtaining a "setoid structure."
--
-- 2. In Lean, where quotients are available, we can additionally take the quotient with respect to
--    equivalence, obtaining a "skeleton structure" where equivalence is equality.
--
-- Moreover, if we have a type with general equivalences, we can obtain a `Structure` by truncating them.
--
-- In `Forgetfulness.lean`, we prove some properties of these operations.
--
-- Within this file, we truncate structures to setoids whenever we want to use structures as isomorphisms,
-- but we never use quotients. With an inductive version of `Structure` (i.e. an actual ∞-groupoid), we
-- could keep all data instead.

namespace Forgetfulness

section SetoidEquiv

variable (α : Sort u) [HasInstanceEquivalence α]

def SetoidEquiv (a b : α) := Nonempty (IsType.type (a ≃ b))
def toSetoidEquiv {a b : α} (e : a ≃ b) : SetoidEquiv α a b := ⟨e⟩
def setoidEquiv : Equivalence (SetoidEquiv α) :=
⟨λ a => ⟨HasRefl.refl a⟩, λ ⟨e⟩ => ⟨HasSymm.symm e⟩, λ ⟨e⟩ ⟨f⟩ => ⟨HasTrans.trans e f⟩⟩

instance instanceEquivSetoid : Setoid α := ⟨SetoidEquiv α, setoidEquiv α⟩

end SetoidEquiv

section Structures

variable (S : Structure)

def structureSetoidEquiv {a b : S} (e : a ≃ b) := toSetoidEquiv (IsType.type S) e
def structureToSetoid := instanceEquivSetoid (IsType.type S)
def setoidStructure : Structure := setoidInstanceStructure (IsType.type S)

def StructureQuotient := Quotient (structureToSetoid S)
def skeletonStructure : Structure := instanceStructure (StructureQuotient S)

end Structures

section SetoidEquivEquiv

def equivSetoid {α : Sort u} [HasGeneralStructure α] (a b : α) : BundledSetoid :=
{ α := IsType.type (a ≃ b),
  s := instanceEquivSetoid (IsType.type (a ≃ b)) }

instance equivHasIso {α : Sort u} [h : HasGeneralStructure α] : HasIsomorphisms (@equivSetoid α h) :=
{ refl                := h.hasIsos.refl,
  symm                := h.hasIsos.symm,
  trans               := h.hasIsos.trans,
  trans_left_functor  := λ f g₁ g₂ ⟨he⟩ => ⟨HasGeneralStructure.comp_congrArg_left  he⟩,
  trans_right_functor := λ g f₁ f₁ ⟨he⟩ => ⟨HasGeneralStructure.comp_congrArg_right he⟩,
  trans_nat           := Unit.unit,
  symm_functor        := λ ⟨he⟩   => ⟨HasGeneralStructure.inv_congrArg  he⟩,
  assoc               := λ e f g  => ⟨HasGeneralStructure.assoc         e f g⟩,
  leftId              := λ e      => ⟨HasGeneralStructure.leftId        e⟩,
  rightId             := λ e      => ⟨HasGeneralStructure.rightId       e⟩,
  leftInv             := λ e      => ⟨HasGeneralStructure.leftInv       e⟩,
  rightInv            := λ e      => ⟨HasGeneralStructure.rightInv      e⟩,
  invInv              := λ e      => ⟨HasGeneralStructure.invInv        e⟩,
  compInv             := λ e f    => ⟨HasGeneralStructure.compInv       e f⟩,
  idInv               := λ a      => ⟨HasGeneralStructure.idInv         a⟩ }

instance hasTruncatedStructure (α : Sort u) [h : HasGeneralStructure α] : HasStructure α :=
⟨@equivSetoid α h⟩

end SetoidEquivEquiv

end Forgetfulness

open Forgetfulness



-- As a simple example of a custom structure, we define a structure for the Cartesian product of two
-- structures.

def StructureProduct (S T : Structure) := PProd (IsType.type S) (IsType.type T)

namespace StructureProduct

variable {S T : Structure}

def ProductEquiv (P Q : StructureProduct S T) := PProd (IsType.type (P.fst ≃ Q.fst)) (IsType.type (P.snd ≃ Q.snd))

namespace ProductEquiv

def refl  (P     : StructureProduct S T)                                               : ProductEquiv P P :=
⟨HasRefl.refl   P.fst,       HasRefl.refl   P.snd⟩
def symm  {P Q   : StructureProduct S T} (e : ProductEquiv P Q)                        : ProductEquiv Q P :=
⟨HasSymm.symm   e.fst,       HasSymm.symm   e.snd⟩
def trans {P Q R : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) : ProductEquiv P R :=
⟨HasTrans.trans e.fst f.fst, HasTrans.trans e.snd f.snd⟩

def EquivEquiv {P Q : StructureProduct S T} (e f : ProductEquiv P Q) :=
e.fst ≈ f.fst ∧ e.snd ≈ f.snd

namespace EquivEquiv

variable {P Q : StructureProduct S T}

theorem refl  (e     : ProductEquiv P Q)                                           : EquivEquiv e e :=
⟨Setoid.refl  e.fst,         Setoid.refl  e.snd⟩
theorem symm  {e f   : ProductEquiv P Q} (h : EquivEquiv e f)                      : EquivEquiv f e :=
⟨Setoid.symm  h.left,        Setoid.symm  h.right⟩
theorem trans {e f g : ProductEquiv P Q} (h : EquivEquiv e f) (i : EquivEquiv f g) : EquivEquiv e g :=
⟨Setoid.trans h.left i.left, Setoid.trans h.right i.right⟩

instance productEquivSetoid : Setoid (ProductEquiv P Q) := ⟨EquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquiv

def productEquiv : RelationWithSetoid (StructureProduct S T) := λ P Q => ⟨ProductEquiv P Q⟩

theorem comp_congrArg {P Q R : StructureProduct S T} {e₁ e₂ : ProductEquiv P Q} {f₁ f₂ : ProductEquiv Q R} (he : e₁ ≈ e₂) (hf : f₁ ≈ f₂) :
  trans e₁ f₁ ≈ trans e₂ f₂ :=
⟨HasStructure.comp_congrArg he.left hf.left,   HasStructure.comp_congrArg he.right hf.right⟩

theorem inv_congrArg {P Q : StructureProduct S T} {e₁ e₂ : ProductEquiv P Q} (he : e₁ ≈ e₂) :
  symm e₁ ≈ symm e₂ :=
⟨HasStructure.inv_congrArg  he.left,           HasStructure.inv_congrArg  he.right⟩

theorem assoc {P Q R Z : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) (g : ProductEquiv R Z) :
  trans (trans e f) g ≈ trans e (trans f g) :=
⟨HasStructure.assoc         e.fst f.fst g.fst, HasStructure.assoc         e.snd f.snd g.snd⟩

theorem leftId  {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans e (refl Q) ≈ e :=
⟨HasStructure.leftId        e.fst,             HasStructure.leftId        e.snd⟩
theorem rightId {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans (refl P) e ≈ e :=
⟨HasStructure.rightId       e.fst,             HasStructure.rightId       e.snd⟩

theorem leftInv  {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans e (symm e) ≈ refl P :=
⟨HasStructure.leftInv       e.fst,             HasStructure.leftInv       e.snd⟩
theorem rightInv {P Q : StructureProduct S T} (e : ProductEquiv P Q) : trans (symm e) e ≈ refl Q :=
⟨HasStructure.rightInv      e.fst,             HasStructure.rightInv      e.snd⟩

theorem invInv {P Q : StructureProduct S T} (e : ProductEquiv P Q) : symm (symm e) ≈ e :=
⟨HasStructure.invInv        e.fst,             HasStructure.invInv        e.snd⟩

theorem compInv {P Q R : StructureProduct S T} (e : ProductEquiv P Q) (f : ProductEquiv Q R) :
  symm (trans e f) ≈ trans (symm f) (symm e) :=
⟨HasStructure.compInv       e.fst f.fst,       HasStructure.compInv       e.snd f.snd⟩

theorem idInv (P : StructureProduct S T) : symm (refl P) ≈ refl P :=
⟨HasStructure.idInv         P.fst,             HasStructure.idInv         P.snd⟩

instance productEquivHasIso : HasIsomorphisms (t := BundledSetoid.isTypeWithFunctorialEquivalence) (@productEquiv S T) :=
{ refl          := refl,
  symm          := symm,
  trans         := trans,
  comp_congrArg := comp_congrArg,
  inv_congrArg  := inv_congrArg,
  assoc         := assoc,
  leftId        := leftId,
  rightId       := rightId,
  leftInv       := leftInv,
  rightInv      := rightInv,
  invInv        := invInv,
  compInv       := compInv,
  idInv         := idInv }

end ProductEquiv

instance productHasStructure (S T : Structure) : HasStructure (StructureProduct S T) := ⟨ProductEquiv.productEquiv⟩
def productStructure (S T : Structure) : Structure := ⟨StructureProduct S T⟩

end StructureProduct



-- A bundled version of `IsIsomorphismFunctor` where the codomains are structures.
-- Therefore, equivalences of equivalences are setoids.

@[reducible] def isoRel {α : Sort u} {S : Structure} (s : α → S) := mapRelation s (iso S)

structure GeneralizedFunctor {α : Sort u} {S T : Structure} (s : α → S) (t : α → T) where
(mapEquiv {a b : α} : s a ≃ s b → t a ≃ t b)
[isFunctor          : IsIsomorphismFunctor (isoRel s) (isoRel t) mapEquiv]

namespace GeneralizedFunctor

@[reducible] def Functor {S T : Structure} (s : S → T) := GeneralizedFunctor id s

variable {α : Sort u} {S T U : Structure}

instance (s : α → S) (t : α → T) :
  CoeFun (GeneralizedFunctor s t) (λ _ => ∀ {a b : α}, s a ≃ s b → t a ≃ t b) :=
⟨GeneralizedFunctor.mapEquiv⟩

def mapFunctor {ω : Sort w} {s : α → S} {t : α → T} (m : ω → α) (φ : GeneralizedFunctor s t) :
  GeneralizedFunctor (s ∘ m) (t ∘ m) :=
{ mapEquiv  := φ.mapEquiv,
  isFunctor := mapIsoFunctor (isoRel s) (isoRel t) φ.mapEquiv (h := φ.isFunctor) m }

instance {ω : Sort w} (s : α → S) (t : α → T) (m : ω → α) :
  Coe (GeneralizedFunctor s t) (GeneralizedFunctor (s ∘ m) (t ∘ m)) :=
⟨mapFunctor m⟩

namespace id

variable {s : α → S}

def genFun : GeneralizedFunctor s s := ⟨id⟩

end id

namespace comp

variable {s : α → S} {t : α → T} {u : α → U} (φ : GeneralizedFunctor s t) (ψ : GeneralizedFunctor t u)

instance : IsIsomorphismFunctor (isoRel s) (isoRel u) (mapEquiv ψ ∘ mapEquiv φ) :=
compIsoFunctor (isoRel s) (isoRel t) (isoRel u) φ.mapEquiv (hF := φ.isFunctor) ψ.mapEquiv (hG := ψ.isFunctor)

def genFun : GeneralizedFunctor s u := ⟨ψ.mapEquiv ∘ φ.mapEquiv⟩

end comp

def comp.genFun' {ω : Sort w} {s : α → S} {t : ω → T} {u : ω → U} (m : α → ω)
                 (φ : GeneralizedFunctor s (t ∘ m)) (ψ : GeneralizedFunctor t u) :
  GeneralizedFunctor s (u ∘ m) :=
comp.genFun φ (mapFunctor m ψ)

namespace const

variable {s : α → S} (c : T)

def genFun : GeneralizedFunctor s (Function.const α c) :=
{ mapEquiv  := λ _ => HasRefl.refl c,
  isFunctor := { respectsEquiv := λ _   => Setoid.refl (id_ c),
                 respectsComp  := λ _ _ => Setoid.symm (leftId (id_ c)),
                 respectsId    := λ _   => Setoid.refl (id_ c),
                 respectsInv   := λ _   => Setoid.symm (idInv c) } }

end const

end GeneralizedFunctor

open GeneralizedFunctor



def Pi {α : Sort u} (C : α → Structure) := ∀ a, C a

namespace Pi

variable {α : Sort u} {C : α → Structure}

def mapPi {ω : Sort w} (m : ω → α) (p : Pi C) : Pi (C ∘ m) :=
λ b => p (m b)

def PiEquiv (p q : Pi C) := ∀ a, p a ≃ q a

namespace PiEquiv

def refl  (p     : Pi C)                                     : PiEquiv p p :=
λ a => HasRefl.refl   (p a)
def symm  {p q   : Pi C} (η : PiEquiv p q)                   : PiEquiv q p :=
λ a => HasSymm.symm   (η a)
def trans {p q H : Pi C} (η : PiEquiv p q) (θ : PiEquiv q H) : PiEquiv p H :=
λ a => HasTrans.trans (η a) (θ a)

def piIsoStructure (p q : Pi C) (a : α) := isoStructure (p a) (q a)

def mapPiEquiv {ω : Sort w} (m : ω → α) {p q : Pi C} (η : PiEquiv p q) :
  PiEquiv (mapPi m p) (mapPi m q) :=
λ b => η (m b)

def EquivEquiv {p q : Pi C} (η θ : PiEquiv p q) :=
@PiEquiv α (piIsoStructure p q) η θ

namespace EquivEquiv

variable {p q : Pi C}

theorem refl  (η     : PiEquiv p q)                                           : EquivEquiv η η :=
@PiEquiv.refl α (piIsoStructure p q) η
theorem symm  {η θ   : PiEquiv p q} (h : EquivEquiv η θ)                      : EquivEquiv θ η :=
PiEquiv.symm  h
theorem trans {η θ ζ : PiEquiv p q} (h : EquivEquiv η θ) (i : EquivEquiv θ ζ) : EquivEquiv η ζ :=
PiEquiv.trans h i

instance piEquivSetoid : Setoid (PiEquiv p q) := ⟨EquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquiv

def piEquiv : RelationWithSetoid (Pi C) := λ p q => ⟨PiEquiv p q⟩

instance piEquivHasIso : HasIsomorphisms (t := BundledSetoid.isTypeWithFunctorialEquivalence) (@piEquiv α C) :=
{ refl          := refl,
  symm          := symm,
  trans         := trans,
  comp_congrArg := λ hη hθ a => comp_congrArg (hη a) (hθ a),
  inv_congrArg  := λ hη    a => inv_congrArg  (hη a),
  assoc         := λ η θ ζ a => assoc         (η a) (θ a) (ζ a),
  leftId        := λ η     a => leftId        (η a),
  rightId       := λ η     a => rightId       (η a),
  leftInv       := λ η     a => leftInv       (η a),
  rightInv      := λ η     a => rightInv      (η a),
  invInv        := λ η     a => invInv        (η a),
  compInv       := λ η θ   a => compInv       (η a) (θ a),
  idInv         := λ b     a => idInv         (b a) }

@[reducible] def MappedPiEquiv {ω : Sort w} (m : ω → Pi C) (b c : ω) := PiEquiv (m b) (m c)

namespace MappedPiEquiv

variable {ω : Sort w} {m : ω → Pi C}

def refl  (b     : ω)                                                     : MappedPiEquiv m b b :=
PiEquiv.refl  (m b)
def symm  {b c   : ω} (e : MappedPiEquiv m b c)                           : MappedPiEquiv m c b :=
PiEquiv.symm  e
def trans {b c d : ω} (e : MappedPiEquiv m b c) (f : MappedPiEquiv m c d) : MappedPiEquiv m b d :=
PiEquiv.trans e f

instance EquivEquiv.mappedPiEquivSetoid {b c : ω} : Setoid (MappedPiEquiv m b c) := EquivEquiv.piEquivSetoid

def mappedPiEquiv : RelationWithSetoid ω := λ b c => ⟨MappedPiEquiv m b c⟩

instance mappedPiEquivHasIso : HasIsomorphisms (@mappedPiEquiv α C ω m) :=
mapHasIso (t := BundledSetoid.isTypeWithFunctorialEquivalence) (@piEquiv α C) m

end MappedPiEquiv



-- If we have two functions that map from an arbitrary `α` into the same structure `S`, and for each
-- instance of `α` we have an equivalence between the values of both functions, that gives us something
-- that can act as an equivalence between the two functions. In particular:
--
-- * If both are functors, this gives us a definition of equivalence of functors.
--
-- * If only one of them is a functor, we can use the equivalence to turn the other function into a
--   functor as well.

variable {α : Sort u} {S : Structure} {p q : α → S} (η : PiEquiv p q)

-- We can "transport" an equivalence `e` between two values of `p` to an equivalence between the
-- corresponding two values of another equivalent function `q`.

def transport    {a b : α} (e : p a ≃ p b) : q a ≃ q b := η b • e • (η a)⁻¹
def invTransport {a b : α} (e : q a ≃ q b) : p a ≃ p b := (η b)⁻¹ • e • η a

namespace transport

theorem isInverse {a b : α} (e : q a ≃ q b) :
  transport (PiEquiv.symm η) e ≈ invTransport η e :=
comp_congrArg_right (comp_congrArg_right (invInv (η a)))

theorem respectsEquiv {a b   : α} {e₁ e₂ : p a ≃ p b} (h : e₁ ≈ e₂) :
  transport η e₁ ≈ transport η e₂ :=
comp_congrArg_right (comp_congrArg_left h)

theorem respectsComp  {a b c : α} (e : p a ≃ p b) (f : p b ≃ p c) :
  transport η (f • e) ≈ transport η f • transport η e :=
let ηa := η a;
let ηb := η b;
let ηc := η c;
let h₁ : ηc • (f • e) • ηa⁻¹ ≈ ηc • (f • (id' • e)) • ηa⁻¹           := comp_congrArg_right (comp_congrArg_left (comp_congrArg_right (Setoid.symm (leftId e))));
let h₂ : ηc • (f • e) • ηa⁻¹ ≈ ηc • (f • ((ηb⁻¹ • ηb) • e)) • ηa⁻¹   := Setoid.trans h₁ (comp_congrArg_right (comp_congrArg_left (comp_congrArg_right (comp_congrArg_left (Setoid.symm (leftInv ηb))))));
let h₃ : ηc • (f • e) • ηa⁻¹ ≈ ηc • (f • (ηb⁻¹ • (ηb • e))) • ηa⁻¹   := Setoid.trans h₂ (comp_congrArg_right (comp_congrArg_left (comp_congrArg_right (Setoid.symm (assoc e ηb ηb⁻¹)))));
let h₄ : ηc • (f • e) • ηa⁻¹ ≈ ηc • ((f • ηb⁻¹) • (ηb • e)) • ηa⁻¹   := Setoid.trans h₃ (comp_congrArg_right (comp_congrArg_left (assoc (ηb • e) ηb⁻¹ f)));
let h₅ : ηc • (f • e) • ηa⁻¹ ≈ ηc • (f • ηb⁻¹) • ((ηb • e) • ηa⁻¹)   := Setoid.trans h₄ (comp_congrArg_right (Setoid.symm (assoc ηa⁻¹ (ηb • e) (f • ηb⁻¹))));
let h₆ : ηc • (f • e) • ηa⁻¹ ≈ (ηc • (f • ηb⁻¹)) • ((ηb • e) • ηa⁻¹) := Setoid.trans h₅ (assoc ((ηb • e) • ηa⁻¹) (f • ηb⁻¹) ηc);
let h₇ : ηc • (f • e) • ηa⁻¹ ≈ (ηc • f • ηb⁻¹) • (ηb • e • ηa⁻¹)     := Setoid.trans h₆ (comp_congrArg_right (Setoid.symm (assoc ηa⁻¹ e ηb)));
h₇

theorem respectsId    (a     : α) :
  transport η (id_ (p a)) ≈ id' :=
let ηa := η a;
let h₁ : ηa • id' • ηa⁻¹ ≈ id' := comp_subst_right (leftId ηa⁻¹) (rightInv ηa);
h₁

theorem respectsInv   {a b   : α} (e : p a ≃ p b) :
  transport η e⁻¹ ≈ (transport η e)⁻¹ :=
let ηa := η a;
let ηb := η b;
let h₁ : ηa • e⁻¹ • ηb⁻¹ ≈ (ηa⁻¹)⁻¹ • (ηb • e)⁻¹ := comp_congrArg (Setoid.symm (compInv e ηb)) (Setoid.symm (invInv ηa));
let h₂ : ηa • e⁻¹ • ηb⁻¹ ≈ ((ηb • e) • ηa⁻¹)⁻¹   := Setoid.trans h₁ (Setoid.symm (compInv ηa⁻¹ (ηb • e)));
let h₃ : ηa • e⁻¹ • ηb⁻¹ ≈ (ηb • e • ηa⁻¹)⁻¹     := Setoid.trans h₂ (inv_congrArg (Setoid.symm (assoc ηa⁻¹ e ηb)));
h₃

def functor : GeneralizedFunctor p q :=
{ mapEquiv  := transport η,
  isFunctor := { respectsEquiv := respectsEquiv η,
                 respectsComp  := respectsComp  η,
                 respectsId    := respectsId    η,
                 respectsInv   := respectsInv   η } }

theorem invRespectsEquiv {a b   : α} {e₁ e₂ : q a ≃ q b} (h : e₁ ≈ e₂) :
  invTransport η e₁ ≈ invTransport η e₂ :=
let h₁ := respectsEquiv (PiEquiv.symm η) h;
Setoid.trans (Setoid.symm (isInverse η e₁)) (Setoid.trans h₁ (isInverse η e₂))

theorem invRespectsComp  {a b c : α} (e : q a ≃ q b) (f : q b ≃ q c) :
  invTransport η (f • e) ≈ invTransport η f • invTransport η e :=
let h₁ := respectsComp (PiEquiv.symm η) e f;
Setoid.trans (Setoid.symm (isInverse η (f • e))) (Setoid.trans h₁ (comp_congrArg (isInverse η e) (isInverse η f)))

theorem invRespectsId    (a     : α) :
  invTransport η (id_ (q a)) ≈ id' :=
let h₁ := respectsId (PiEquiv.symm η) a;
Setoid.trans (Setoid.symm (isInverse η (id_ (q a)))) h₁

theorem invRespectsInv   {a b   : α} (e : q a ≃ q b) :
  invTransport η e⁻¹ ≈ (invTransport η e)⁻¹ :=
let h₁ := respectsInv (PiEquiv.symm η) e;
Setoid.trans (Setoid.symm (isInverse η e⁻¹)) (Setoid.trans h₁ (inv_congrArg (isInverse η e)))

def invFunctor : GeneralizedFunctor q p :=
{ mapEquiv  := invTransport η,
  isFunctor := { respectsEquiv := invRespectsEquiv η,
                 respectsComp  := invRespectsComp  η,
                 respectsId    := invRespectsId    η,
                 respectsInv   := invRespectsInv   η } }

end transport

end PiEquiv

end Pi

open Pi



def GeneralizedNaturalityCondition {α : Sort u} {S T : Structure} {s : α → S} {t₁ t₂ : α → T}
                                   (φ : GeneralizedFunctor s t₁) (ψ : GeneralizedFunctor s t₂)
                                   (ext : PiEquiv t₁ t₂) :=
∀ {a b : α} (e : s a ≃ s b), ψ e • ext a ≈ ext b • φ e

namespace GeneralizedNaturalityCondition

variable {α : Sort u} {S T : Structure}

theorem refl  {s : α → S} {t₁       : α → T}
              (φ : GeneralizedFunctor s t₁) :
  GeneralizedNaturalityCondition φ φ (PiEquiv.refl t₁) :=
λ e => Setoid.trans (rightId (φ e)) (Setoid.symm (leftId (φ e)))

theorem symm  {s : α → S} {t₁ t₂    : α → T}
              {φ : GeneralizedFunctor s t₁} {ψ : GeneralizedFunctor s t₂}
              {ext : PiEquiv t₁ t₂}
              (nat : GeneralizedNaturalityCondition φ ψ ext) :
  GeneralizedNaturalityCondition ψ φ (PiEquiv.symm ext) :=
λ {a b} e => Setoid.symm ((leftRightMul (ext a) (φ e) (ψ e) (ext b)).mpr (nat e))

theorem trans {s : α → S} {t₁ t₂ t₃ : α → T}
              {φ : GeneralizedFunctor s t₁} {ψ : GeneralizedFunctor s t₂} {χ : GeneralizedFunctor s t₃}
              {ext₁ : PiEquiv t₁ t₂}                           {ext₂ : PiEquiv t₂ t₃}
              (nat₁ : GeneralizedNaturalityCondition φ ψ ext₁) (nat₂ : GeneralizedNaturalityCondition ψ χ ext₂) :
  GeneralizedNaturalityCondition φ χ (PiEquiv.trans ext₁ ext₂) :=
λ {a b} e => let h₁ := (rightMulInv (ψ e) (ext₁ b • φ e) (ext₁ a)).mp  (nat₁ e);
             let h₂ := (leftMulInv' (χ e • ext₂ a) (ψ e) (ext₂ b)).mpr (nat₂ e);
             let h₃ := (leftRightMul (ext₁ a) (ext₁ b • φ e) (χ e • ext₂ a) (ext₂ b)).mp (Setoid.trans h₂ h₁);
             applyAssoc_left' (applyAssoc_right h₃)

end GeneralizedNaturalityCondition



structure GeneralizedNaturalTransformation {α : Sort u} {S T : Structure} {s : α → S} {t₁ t₂ : α → T}
                                           (φ : GeneralizedFunctor s t₁) (ψ : GeneralizedFunctor s t₂) where
(ext : PiEquiv t₁ t₂)
(nat : GeneralizedNaturalityCondition φ ψ ext)

namespace GeneralizedNaturalTransformation

variable {α : Sort u} {S T : Structure}

def refl  {s : α → S} {t₁       : α → T} (φ : GeneralizedFunctor s t₁) :
  GeneralizedNaturalTransformation φ φ :=
⟨PiEquiv.refl  t₁,          GeneralizedNaturalityCondition.refl  φ⟩

def symm  {s : α → S} {t₁ t₂    : α → T} {φ : GeneralizedFunctor s t₁} {ψ : GeneralizedFunctor s t₂}
          (η : GeneralizedNaturalTransformation φ ψ) :
  GeneralizedNaturalTransformation ψ φ :=
⟨PiEquiv.symm  η.ext,       GeneralizedNaturalityCondition.symm  η.nat⟩

def trans {s : α → S} {t₁ t₂ t₃ : α → T} {φ : GeneralizedFunctor s t₁} {ψ : GeneralizedFunctor s t₂} {χ : GeneralizedFunctor s t₃}
          (η : GeneralizedNaturalTransformation φ ψ) (θ : GeneralizedNaturalTransformation ψ χ) :
  GeneralizedNaturalTransformation φ χ :=
⟨PiEquiv.trans η.ext θ.ext, GeneralizedNaturalityCondition.trans η.nat θ.nat⟩

instance naturalTransformationSetoid {s : α → S} {t₁ t₂ : α → T} (φ : GeneralizedFunctor s t₁) (ψ : GeneralizedFunctor s t₂) :
  Setoid (GeneralizedNaturalTransformation φ ψ) :=
⟨λ e f => PiEquiv.EquivEquiv e.ext f.ext,
 ⟨λ e => PiEquiv.EquivEquiv.refl e.ext, PiEquiv.EquivEquiv.symm, PiEquiv.EquivEquiv.trans⟩⟩

def mapNaturalTransformation {ω : Sort w} {s : α → S} {t₁ t₂ : α → T} (m : ω → α)
                             {φ : GeneralizedFunctor s t₁} {ψ : GeneralizedFunctor s t₂}
                             (η : GeneralizedNaturalTransformation φ ψ) :
  GeneralizedNaturalTransformation (mapFunctor m φ) (mapFunctor m ψ) :=
⟨PiEquiv.mapPiEquiv m η.ext, η.nat⟩

end GeneralizedNaturalTransformation



-- A functor between two `Structure`s is a map that also maps equivalences in a compatible way. On the
-- one hand, this is just a groupoid functor, but on the other hand, the mapping of equivalences also
-- matches exactly the `mapEquiv` map mentioned in the introduction.
--
-- Moreover, if we interpret `≃` as a generalization of equality, the mapping of equivalences is actually
-- the generalized version of `congrArg`. Under this interpretation, it can also be regarded as a
-- well-definedness condition for the map: equality of arguments implies equality of results.

structure StructureFunctor (S T : Structure) :=
(map     : S → T)
(functor : Functor map)

namespace StructureFunctor

variable {S T U V : Structure}

instance functorCoeFun : CoeFun (StructureFunctor S T) (λ _ => S → T) := ⟨StructureFunctor.map⟩

        theorem respectsSetoid (F : StructureFunctor S T) {a b   : S} {f₁ f₂ : a ≃ b} :
  f₁ ≈ f₂ → F.functor f₁ ≈ F.functor f₂         := F.functor.isFunctor.respectsEquiv
@[simp] theorem respectsComp   (F : StructureFunctor S T) {a b c : S} (f : a ≃ b) (g : b ≃ c) :
  F.functor (g • f) ≈ F.functor g • F.functor f := F.functor.isFunctor.respectsComp f g
@[simp] theorem respectsId     (F : StructureFunctor S T) (a     : S) :
  F.functor (id_ a) ≈ id'                       := F.functor.isFunctor.respectsId   a
@[simp] theorem respectsInv    (F : StructureFunctor S T) {a b   : S} (f : a ≃ b) :
  F.functor f⁻¹     ≈ (F.functor f)⁻¹           := F.functor.isFunctor.respectsInv  f



def congrArg (F : StructureFunctor S T) {a b : S} : a ≃ b → F a ≃ F b := F.functor.mapEquiv



-- We can define equivalence of functors by extensionality, using equivalence in `T` instead of equality.
-- This is an equivalence according to our definition, and it is compatible with isomorphisms via the
-- functor axioms, so we can use it to build an instance of `Structure` again.
--
-- For equivalence of functors to be well-behaved, we additionally need to require equivalences to be
-- natural transformations.

def FunExt (F G : StructureFunctor S T) := PiEquiv.MappedPiEquiv StructureFunctor.map F G

namespace FunExt

instance {F G : StructureFunctor S T} : Setoid (FunExt F G) :=
PiEquiv.MappedPiEquiv.EquivEquiv.mappedPiEquivSetoid

def funExt : RelationWithSetoid (StructureFunctor S T) := λ F G => ⟨FunExt F G⟩

instance funExtHasIso : HasIsomorphisms (@funExt S T) := PiEquiv.MappedPiEquiv.mappedPiEquivHasIso

end FunExt

def FunctorEquiv (F G : StructureFunctor S T) := GeneralizedNaturalTransformation F.functor G.functor

namespace FunctorEquiv

def refl  (F     : StructureFunctor S T)                                               : FunctorEquiv F F :=
GeneralizedNaturalTransformation.refl  F.functor
def symm  {F G   : StructureFunctor S T} (η : FunctorEquiv F G)                        : FunctorEquiv G F :=
GeneralizedNaturalTransformation.symm  η
def trans {F G H : StructureFunctor S T} (η : FunctorEquiv F G) (θ : FunctorEquiv G H) : FunctorEquiv F H :=
GeneralizedNaturalTransformation.trans η θ

instance (F G : StructureFunctor S T) : Setoid (FunctorEquiv F G) :=
GeneralizedNaturalTransformation.naturalTransformationSetoid F.functor G.functor

def functorEquiv : RelationWithSetoid (StructureFunctor S T) := λ F G => ⟨FunctorEquiv F G⟩

instance functorEquivHasIso : HasIsomorphisms (@functorEquiv S T) :=
{ refl          := refl,
  symm          := symm,
  trans         := trans,
  comp_congrArg := λ hη hθ => FunExt.funExtHasIso.comp_congrArg hη hθ,
  inv_congrArg  := λ hη    => FunExt.funExtHasIso.inv_congrArg  hη,
  assoc         := λ η θ ζ => FunExt.funExtHasIso.assoc         η.ext θ.ext ζ.ext,
  leftId        := λ η     => FunExt.funExtHasIso.leftId        η.ext,
  rightId       := λ η     => FunExt.funExtHasIso.rightId       η.ext,
  leftInv       := λ η     => FunExt.funExtHasIso.leftInv       η.ext,
  rightInv      := λ η     => FunExt.funExtHasIso.rightInv      η.ext,
  invInv        := λ η     => FunExt.funExtHasIso.invInv        η.ext,
  compInv       := λ η θ   => FunExt.funExtHasIso.compInv       η.ext θ.ext,
  idInv         := λ F     => FunExt.funExtHasIso.idInv         F }

end FunctorEquiv

instance functorHasStructure : HasStructure (StructureFunctor S T) := ⟨FunctorEquiv.functorEquiv⟩
def functorStructure (S T : Structure) : Structure := ⟨StructureFunctor S T⟩

instance : CoeFun (IsType.type (functorStructure S T)) (λ _ => S → T) := functorCoeFun



-- We have two alternative definitions of `congr` for functors, depending on the order in which we apply
-- the functor and argument equivalences. The natural transformation axiom says exactly that the order
-- does not matter.

def congr  {F₁ F₂ : StructureFunctor S T} {a b : S} : F₁ ≃ F₂ → a ≃ b → F₁ a ≃ F₂ b :=
λ η e => HasTrans.trans (η.ext a) (F₂.functor e)

def congr' {F₁ F₂ : StructureFunctor S T} {a b : S} : F₁ ≃ F₂ → a ≃ b → F₁ a ≃ F₂ b :=
λ η e => HasTrans.trans (F₁.functor e) (η.ext b)

theorem congr.wd {F₁ F₂ : StructureFunctor S T} {a b : S} (η : F₁ ≃ F₂) (e : a ≃ b) :
  congr η e ≈ congr' η e :=
η.nat e



-- Now we define identity and composition and prove that they are well-behaved with respect to equivalence.

def idFun : StructureFunctor S S := ⟨id, id.genFun⟩

def compMap     (F : StructureFunctor S T) (G : StructureFunctor T U) : S → U :=
λ f => G (F f)

def compFunctor (F : StructureFunctor S T) (G : StructureFunctor T U) : Functor (compMap F G) :=
comp.genFun' F.map F.functor G.functor

def compFun     (F : StructureFunctor S T) (G : StructureFunctor T U) : StructureFunctor S U :=
⟨compMap F G, compFunctor F G⟩

@[reducible] def revCompFun (G : StructureFunctor T U) (F : StructureFunctor S T) : StructureFunctor S U := compFun F G
infixr:90 " ⊙ " => revCompFun



namespace compFun

def congrArg_left {F : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} :
  G₁ ≃ G₂ → G₁ ⊙ F ≃ G₂ ⊙ F :=
λ η => { ext := λ a => η.ext (F a),
         nat := λ e => η.nat (F.functor e) }

namespace congrArg_left

theorem respectsEquiv {F : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U}
                      {η₁ η₂ : G₁ ≃ G₂} :
  η₁ ≈ η₂ → congrArg_left (F := F) η₁ ≈ congrArg_left (F := F) η₂ :=
λ hη a => hη (F a)

theorem respectsComp {F : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T U}
                     (η₁ : G₁ ≃ G₂) (η₂ : G₂ ≃ G₃) :
  congrArg_left (F := F) (η₂ • η₁) ≈ congrArg_left η₂ • congrArg_left η₁ :=
λ a => Setoid.refl (η₂.ext (F a) • η₁.ext (F a))

theorem respectsId {F : StructureFunctor S T} (G : StructureFunctor T U) :
  congrArg_left (id_ G) ≈ id_ (G ⊙ F) :=
λ a => Setoid.refl (id_ (G (F a)))

theorem respectsInv {F : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (η : G₁ ≃ G₂) :
  congrArg_left (F := F) η⁻¹ ≈ (congrArg_left η)⁻¹ :=
λ a => Setoid.refl (η.ext (F a))⁻¹

def functor (U : Structure) (F : StructureFunctor S T) : StructureFunctor (functorStructure T U) (functorStructure S U) :=
{ map     := λ G => G ⊙ F,
  functor := { mapEquiv  := congrArg_left,
               isFunctor := { respectsEquiv := respectsEquiv,
                              respectsComp  := respectsComp,
                              respectsId    := respectsId,
                              respectsInv   := respectsInv } } }

end congrArg_left

def congrArg_right {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U} :
  F₁ ≃ F₂ → G ⊙ F₁ ≃ G ⊙ F₂ :=
λ η => { ext := λ a => G.functor (η.ext a),
         nat := λ {a b} e => let h₁ := respectsSetoid G (η.nat e);
                             let h₂ := Setoid.trans (Setoid.symm (respectsComp G (η.ext a) (F₂.functor e))) h₁;
                             let h₄ := Setoid.trans h₂ (respectsComp G (F₁.functor e) (η.ext b));
                             h₄ }

namespace congrArg_right

theorem respectsEquiv {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U}
                      {η₁ η₂ : F₁ ≃ F₂} :
  η₁ ≈ η₂ → congrArg_right (G := G) η₁ ≈ congrArg_right (G := G) η₂ :=
λ hη a => StructureFunctor.respectsSetoid G (hη a)

theorem respectsComp {F₁ F₂ F₃ : StructureFunctor S T} {G : StructureFunctor T U}
                     (η₁ : F₁ ≃ F₂) (η₂ : F₂ ≃ F₃) :
  congrArg_right (G := G) (η₂ • η₁) ≈ congrArg_right η₂ • congrArg_right η₁ :=
λ a => StructureFunctor.respectsComp G (η₁.ext a) (η₂.ext a)

theorem respectsId (F : StructureFunctor S T) {G : StructureFunctor T U} :
  congrArg_right (id_ F) ≈ id_ (G ⊙ F) :=
λ a => StructureFunctor.respectsId G (F a)

theorem respectsInv {F₁ F₂ : StructureFunctor S T} {G : StructureFunctor T U} (η : F₁ ≃ F₂) :
  congrArg_right (G := G) η⁻¹ ≈ (congrArg_right η)⁻¹ :=
λ a => StructureFunctor.respectsInv G (η.ext a)

def functor (S : Structure) (G : StructureFunctor T U) : StructureFunctor (functorStructure S T) (functorStructure S U) :=
{ map     := λ F => G ⊙ F,
  functor := { mapEquiv  := congrArg_right,
               isFunctor := { respectsEquiv := respectsEquiv,
                              respectsComp  := respectsComp,
                              respectsId    := respectsId (G := G),
                              respectsInv   := respectsInv } } }

end congrArg_right

def congrArg  {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} :
  F₁ ≃ F₂ → G₁ ≃ G₂ → G₁ ⊙ F₁ ≃ G₂ ⊙ F₂ :=
λ η θ => FunctorEquiv.trans (congrArg_left θ) (congrArg_right η)

def congrArg' {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} :
  F₁ ≃ F₂ → G₁ ≃ G₂ → G₁ ⊙ F₁ ≃ G₂ ⊙ F₂ :=
λ η θ => FunctorEquiv.trans (congrArg_right η) (congrArg_left θ)

namespace congrArg

theorem wd {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (η : F₁ ≃ F₂) (θ : G₁ ≃ G₂) :
  congrArg η θ ≈ congrArg' η θ :=
λ a => θ.nat (η.ext a)

theorem respectsEquiv {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U}
                      {η₁ η₂ : F₁ ≃ F₂} {θ₁ θ₂ : G₁ ≃ G₂} :
  η₁ ≈ η₂ → θ₁ ≈ θ₂ → congrArg η₁ θ₁ ≈ congrArg η₂ θ₂ :=
λ hη hθ => FunctorEquiv.functorEquivHasIso.comp_congrArg (congrArg_left.respectsEquiv hθ) (congrArg_right.respectsEquiv hη)

theorem respectsComp {F₁ F₂ F₃ : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T U}
                     (η₁ : F₁ ≃ F₂) (η₂ : F₂ ≃ F₃) (θ₁ : G₁ ≃ G₂) (θ₂ : G₂ ≃ G₃) :
  congrArg (η₂ • η₁) (θ₂ • θ₁) ≈ congrArg η₂ θ₂ • congrArg η₁ θ₁ :=
let h₁ := FunctorEquiv.functorEquivHasIso.comp_congrArg (congrArg_left.respectsComp θ₁ θ₂) (congrArg_right.respectsComp η₁ η₂);
let h₂ := comp_congrArg_left (f := congrArg_left θ₁) (wd η₁ θ₂);
let h₃ := applyAssoc' h₂;
let h₄ := comp_congrArg_right (g := congrArg_right η₂) h₃;
let h₅ := applyAssoc h₄;
Setoid.trans h₁ h₅

theorem respectsId (F : StructureFunctor S T) (G : StructureFunctor T U) :
  congrArg (id_ F) (id_ G) ≈ id_ (G ⊙ F) :=
let h₁ := FunctorEquiv.functorEquivHasIso.comp_congrArg (congrArg_left.respectsId G) (congrArg_right.respectsId F);
Setoid.trans h₁ (leftId id')

theorem respectsInv {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (η : F₁ ≃ F₂) (θ : G₁ ≃ G₂) :
  congrArg η⁻¹ θ⁻¹ ≈ (congrArg η θ)⁻¹ :=
let h₁ := FunctorEquiv.functorEquivHasIso.comp_congrArg (congrArg_left.respectsInv θ) (congrArg_right.respectsInv η);
let h₂ := inv_congrArg (wd η θ);
let h₃ := compInv (congrArg_right η) (congrArg_left θ);
Setoid.trans h₁ (Setoid.symm (Setoid.trans h₂ h₃))

end congrArg

def assoc (F : StructureFunctor S T) (G : StructureFunctor T U) (H : StructureFunctor U V) :
  H ⊙ (G ⊙ F) ≃ (H ⊙ G) ⊙ F :=
FunctorEquiv.refl (H ⊙ G ⊙ F)

end compFun



namespace idFun

def leftId (F : StructureFunctor S T) : idFun ⊙ F ≃ F :=
{ ext := λ a => HasRefl.refl (F a),
  nat := GeneralizedNaturalityCondition.refl F.functor }

def rightId (F : StructureFunctor S T) : F ⊙ idFun ≃ F :=
{ ext := λ a => HasRefl.refl (F a),
  nat := GeneralizedNaturalityCondition.refl F.functor }

end idFun

#exit

instance hasMor : HasMorphisms functorStructure :=
{ refl          := @idFun,
  trans         := compFun,
  comp_congrArg := compFun.congrArg,
  assoc         := compFun.assoc,
  leftId        := idFun.leftId,
  rightId       := idFun.rightId }



namespace compFun.congrArg_left.functor

def mapEquiv (U : Structure) {F₁ F₂ : StructureFunctor S T} (η : F₁ ≃ F₂) : functor U F₁ ≃ functor U F₂ :=
{ ext := λ G => congrArg_right (G := G) η,
  nat := λ θ => Setoid.symm (congrArg.wd η θ) }

def functorFunctor (U : Structure)
  : StructureFunctor (functorStructure S T) (functorStructure (functorStructure T U) (functorStructure S U)) :=
{ map     := functor U,
  functor := { mapEquiv  := mapEquiv U,
               isFunctor := { respectsEquiv := λ h   G => congrArg_right.respectsEquiv (G := G) h,
                              respectsComp  := λ η θ G => congrArg_right.respectsComp  (G := G) η θ,
                              respectsId    := λ F   G => congrArg_right.respectsId    (G := G) F,
                              respectsInv   := λ η   G => congrArg_right.respectsInv   (G := G) η } } }

def respectsIdFun (T S : Structure) : functor T (@idFun S) ≃ @idFun (functorStructure S T) :=
{ ext := λ F   => idFun.rightId F,
  nat := λ η a => let e := η.ext a;
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

def respectsCompFun (V : Structure) (F : StructureFunctor S T) (G : StructureFunctor T U) :
  functor V (G ⊙ F) ≃ functor V F ⊙ functor V G :=
{ ext := λ H   => FunctorEquiv.refl (H ⊙ (G ⊙ F)),
  nat := λ η a => let e := η.ext (G (F a));
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

theorem respectsCompFun.nat (V : Structure) {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T U} (η : F₁ ≃ F₂) (θ : G₁ ≃ G₂) :
  compFun.congrArg (mapEquiv V θ) (mapEquiv V η) • respectsCompFun V F₁ G₁ ≈ respectsCompFun V F₂ G₂ • mapEquiv V (compFun.congrArg η θ) :=
sorry

end compFun.congrArg_left.functor

namespace compFun.congrArg_right.functor

def mapEquiv (S : Structure) {G₁ G₂ : StructureFunctor T U} (θ : G₁ ≃ G₂) : functor S G₁ ≃ functor S G₂ :=
{ ext := λ F => congrArg_left (F := F) θ,
  nat := λ η => congrArg.wd η θ }

def functorFunctor (S : Structure)
  : StructureFunctor (functorStructure T U) (functorStructure (functorStructure S T) (functorStructure S U)) :=
{ map     := functor S,
  functor := { mapEquiv  := mapEquiv S,
               isFunctor := { respectsEquiv := λ h   F => congrArg_left.respectsEquiv (F := F) h,
                              respectsComp  := λ η θ F => congrArg_left.respectsComp  (F := F) η θ,
                              respectsId    := λ G   F => congrArg_left.respectsId    (F := F) G,
                              respectsInv   := λ η   F => congrArg_left.respectsInv   (F := F) η } } }

def respectsIdFun (S T : Structure) : functor S (@idFun T) ≃ @idFun (functorStructure S T) :=
{ ext := λ F   => idFun.leftId F,
  nat := λ η a => let e := η.ext a;
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

def respectsCompFun (S : Structure) (G : StructureFunctor T U) (H : StructureFunctor U V) :
  functor S (H ⊙ G) ≃ functor S H ⊙ functor S G :=
{ ext := λ F   => FunctorEquiv.refl ((H ⊙ G) ⊙ F),
  nat := λ η a => let e := StructureFunctor.congrArg (H ⊙ G) (η.ext a);
                  Setoid.trans (rightId e) (Setoid.symm (leftId e)) }

theorem respectsCompFun.nat (S : Structure) {G₁ G₂ : StructureFunctor T U} {H₁ H₂ : StructureFunctor U V} (η : G₁ ≃ G₂) (θ : H₁ ≃ H₂) :
  compFun.congrArg (mapEquiv S η) (mapEquiv S θ) • respectsCompFun S G₁ H₁ ≈ respectsCompFun S G₂ H₂ • mapEquiv S (compFun.congrArg η θ) :=
sorry

end compFun.congrArg_right.functor



-- The constant functor.

def constFun (c : T) : StructureFunctor S T :=
{ map     := Function.const (IsType.type S) c,
  functor := const.genFun c }



-- A simple alias for the assertion that a functor is equivalent to the identity functor.

@[reducible] def IsId (F : StructureFunctor S S) := F ≃ @idFun S

namespace IsId

-- `ext` and `nat` have a slightly simpler form in this case.

def extDef {F : StructureFunctor S S} (η : IsId F) (a : S) : F a ≃ a :=
η.ext a

theorem natDef {F : StructureFunctor S S} (η : IsId F) {a b : S} (e : a ≃ b) :
  e • η.ext a ≈ η.ext b • F.functor e :=
η.nat e

-- When composing both sides with another functor, we can cancel `idFun`.

def rightMul {G : StructureFunctor T T} (θ : IsId G) (F : StructureFunctor S T) :
  G ⊙ F ≃ F :=
FunctorEquiv.trans (compFun.congrArg_left (F := F) θ) (idFun.leftId F)

theorem rightMulDef {G : StructureFunctor T T} (θ : IsId G) (F : StructureFunctor S T) (a : S) :
  (rightMul θ F).ext a ≈ θ.ext (F a) :=
leftId (θ.ext (F a))

def leftMul {F : StructureFunctor S S} (η : IsId F) (G : StructureFunctor S T) :
  G ⊙ F ≃ G :=
FunctorEquiv.trans (compFun.congrArg_right (G := G) η) (idFun.rightId G)

theorem leftMulDef {F : StructureFunctor S S} (η : IsId F) (G : StructureFunctor S T) (a : S) :
  (leftMul η G).ext a ≈ G.functor (η.ext a) :=
leftId (G.functor (η.ext a))

-- We have some definitions resembling reflexivity and transitivity.

def refl (S : Structure) : IsId (@idFun S) := FunctorEquiv.refl idFun

def trans {F G : StructureFunctor S S} (η : IsId F) (θ : IsId G) : IsId (G ⊙ F) :=
FunctorEquiv.trans (rightMul θ F) η

theorem transDef {F G : StructureFunctor S S} (η : IsId F) (θ : IsId G) (a : S) :
  (trans η θ).ext a ≈ η.ext a • θ.ext (F a) :=
comp_congrArg_right (rightMulDef θ F a)

end IsId



-- A simple alias for the assertion that `G` is a left inverse of `F`.
-- Note that instead of defining `RightInv` analogously, we just swap the arguments of `F` and `G` where
-- necessary.

@[reducible] def LeftInv (F : StructureFunctor S T) (G : StructureFunctor T S) := IsId (G ⊙ F)

namespace LeftInv

def refl (S : Structure) : LeftInv (@idFun S) (@idFun S) := IsId.refl S

def trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
          (η : LeftInv F G) (θ : LeftInv H I) :
  LeftInv (H ⊙ F) (G ⊙ I) :=
let ζ : (G ⊙ I) ⊙ (H ⊙ F) ≃ G ⊙ F := compFun.congrArg_left (F := F) (IsId.leftMul θ G);
FunctorEquiv.trans ζ η

theorem transDef {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
                 (η : LeftInv F G) (θ : LeftInv H I) (a : S) :
  (trans η θ).ext a ≈ η.ext a • G.functor (θ.ext (F a)) :=
comp_congrArg_right (IsId.leftMulDef θ G (F a))

theorem refl_trans {F : StructureFunctor S T} {G : StructureFunctor T S}
                   (η : LeftInv F G) :
  trans (refl S) η ≈ η :=
λ a => let h₁ : (trans (refl S) η).ext a ≈ id_ a • η.ext a := transDef (refl S) η a;
       let h₂ : id_ a • η.ext a ≈ η.ext a                  := leftId (η.ext a);
       Setoid.trans h₁ h₂

theorem trans_refl {F : StructureFunctor S T} {G : StructureFunctor T S}
                   (η : LeftInv F G) :
  trans η (refl T) ≈ η :=
λ a => let h₁ := transDef η (refl T) a;
       let h₂ := rightCancelId (respectsId G (F a));
       Setoid.trans h₁ h₂

theorem trans_assoc {F : StructureFunctor S T} {G : StructureFunctor T S}
                    {H : StructureFunctor T U} {I : StructureFunctor U T}
                    {J : StructureFunctor U V} {K : StructureFunctor V U}
                    (η : LeftInv F G) (θ : LeftInv H I) (ζ : LeftInv J K) :
  let l : LeftInv (J ⊙ H ⊙ F) (G ⊙ I ⊙ K) := trans (trans η θ) ζ;
  let r : LeftInv (J ⊙ H ⊙ F) (G ⊙ I ⊙ K) := trans η (trans θ ζ);
  l ≈ r :=
λ a => let h₁ := applyAssoc_right' (comp_subst_left' (transDef η θ a) (transDef (trans η θ) ζ a));
       let h₂ := comp_subst_right' (Setoid.symm (respectsComp G (I.functor.mapEquiv (ζ.ext (H (F a)))) (θ.ext (F a)))) h₁;
       let h₃ := comp_subst_right' (respectsSetoid G (transDef θ ζ (F a))) (transDef η (trans θ ζ) a);
       Setoid.trans h₂ (Setoid.symm h₃)

-- This definition asserts that an instance of `LeftInv` is compatible with a corresponding reversed
-- `LeftInv` instance. It corresponds to one of the two equations of an adjoint functor (the one about
-- `F`).

def Compat {F : StructureFunctor S T} {G : StructureFunctor T S} (ηl : LeftInv F G) (ηr : LeftInv G F) :=
∀ a, F.functor (ηl.ext a) ≈ ηr.ext (F a)

namespace Compat

theorem refl (S : Structure) : Compat (LeftInv.refl S) (LeftInv.refl S) :=
λ a => Setoid.refl (HasRefl.refl a)

theorem trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
              {ηl : LeftInv F G} {ηr : LeftInv G F} {θl : LeftInv H I} {θr : LeftInv I H}
              (c : Compat ηl ηr) (d : Compat θl θr) :
  Compat (LeftInv.trans ηl θl) (LeftInv.trans θr ηr) :=
λ a => let h₁ : ηr.ext (F a) • F.functor (G.functor (θl.ext (F a))) ≈ θl.ext (F a) • ηr.ext (I (H (F a)))                                 := Setoid.symm (ηr.nat (θl.ext (F a)));
       let h₂ : F.functor (ηl.ext a) • F.functor (G.functor (θl.ext (F a))) ≈ θl.ext (F a) • ηr.ext (I (H (F a)))                         := comp_subst_left (c a) h₁;
       let h₃ : F.functor (ηl.ext a • G.functor (θl.ext (F a))) ≈ θl.ext (F a) • ηr.ext (I (H (F a)))                                     := Setoid.trans (respectsComp F (G.functor (θl.ext (F a))) (ηl.ext a)) h₂;
       let h₄ : H.functor (F.functor (ηl.ext a • G.functor (θl.ext (F a)))) ≈ H.functor (θl.ext (F a)) • H.functor (ηr.ext (I (H (F a)))) := Setoid.trans (respectsSetoid H h₃) (respectsComp H (ηr.ext (I (H (F a)))) (θl.ext (F a)));
       let h₅ : H.functor (F.functor (ηl.ext a • G.functor (θl.ext (F a)))) ≈ θr.ext (H (F a)) • H.functor (ηr.ext (I (H (F a))))         := comp_subst_left' (d (F a)) h₄;
       let h₆ := Setoid.trans (respectsSetoid H (respectsSetoid F (transDef ηl θl a))) h₅;
       let h₇ := Setoid.trans h₆ (Setoid.symm (transDef θr ηr (H (F a))));
       h₇

end Compat

-- Given equivalences of functors, we can ask whether two instances of `LeftInv` are equivalent.

def Equiv {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T S}
          (η : F₁ ≃ F₂) (θ : G₁ ≃ G₂)
          (ζ₁ : LeftInv F₁ G₁) (ζ₂ : LeftInv F₂ G₂) :=
ζ₁ ≈ ζ₂ • compFun.congrArg η θ

namespace Equiv

theorem refl  {F : StructureFunctor S T} {G : StructureFunctor T S} (ζ : LeftInv F G) :
  Equiv (FunctorEquiv.refl F) (FunctorEquiv.refl G) ζ ζ :=
Setoid.symm (rightCancelId (compFun.congrArg.respectsId F G))

theorem refl' {F : StructureFunctor S T} {G : StructureFunctor T S} {ζ₁ ζ₂ : LeftInv F G} (h : ζ₁ ≈ ζ₂) :
  Equiv (FunctorEquiv.refl F) (FunctorEquiv.refl G) ζ₁ ζ₂ :=
comp_subst_left' h (refl ζ₁)

theorem symm  {F₁ F₂ : StructureFunctor S T} {G₁ G₂ : StructureFunctor T S}
              {η : F₁ ≃ F₂} {θ : G₁ ≃ G₂}
              {ζ₁ : LeftInv F₁ G₁} {ζ₂ : LeftInv F₂ G₂}
              (e : Equiv η θ ζ₁ ζ₂) :
  Equiv (FunctorEquiv.symm η) (FunctorEquiv.symm θ) ζ₂ ζ₁ :=
let h₁ := (rightMulInv ζ₂ ζ₁ (compFun.congrArg η θ)).mp (Setoid.symm e);
comp_subst_right' (Setoid.symm (compFun.congrArg.respectsInv η θ)) h₁

theorem trans {F₁ F₂ F₃ : StructureFunctor S T} {G₁ G₂ G₃ : StructureFunctor T S}
              {η₁ : F₁ ≃ F₂} {η₂ : F₂ ≃ F₃} {θ₁ : G₁ ≃ G₂} {θ₂ : G₂ ≃ G₃}
              {ζ₁ : LeftInv F₁ G₁} {ζ₂ : LeftInv F₂ G₂} {ζ₃ : LeftInv F₃ G₃}
              (e : Equiv η₁ θ₁ ζ₁ ζ₂) (f : Equiv η₂ θ₂ ζ₂ ζ₃) :
  Equiv (FunctorEquiv.trans η₁ η₂) (FunctorEquiv.trans θ₁ θ₂) ζ₁ ζ₃ :=
let h₁ := applyAssoc_right' (comp_subst_left' f e);
comp_subst_right' (Setoid.symm (compFun.congrArg.respectsComp η₁ η₂ θ₁ θ₂)) h₁

end Equiv

end LeftInv



-- A type class asserting that two functors are inverse to each other. In addition to the condition that
-- the inverse functor is left-inverse and right-inverse, we also add compatibility conditions on these
-- two functor equivalences for both `F` and `G`. This is essentially the same as requiring the functors
-- to be adjoint.

class IsInverse (F : StructureFunctor S T) (G : StructureFunctor T S) :=
(leftInv  : LeftInv F G)
(rightInv : LeftInv G F)
(lrCompat : LeftInv.Compat leftInv rightInv)
(rlCompat : LeftInv.Compat rightInv leftInv)

namespace IsInverse

def refl  (S : Structure) :
  IsInverse (@idFun S) (@idFun S) :=
{ leftInv  := LeftInv.refl        S,
  rightInv := LeftInv.refl        S,
  lrCompat := LeftInv.Compat.refl S,
  rlCompat := LeftInv.Compat.refl S }

def symm  {F : StructureFunctor S T} {G : StructureFunctor T S}
          (e : IsInverse F G) :
  IsInverse G F :=
{ leftInv  := e.rightInv,
  rightInv := e.leftInv,
  lrCompat := e.rlCompat,
  rlCompat := e.lrCompat }

def trans {F : StructureFunctor S T} {G : StructureFunctor T S} {H : StructureFunctor T U} {I : StructureFunctor U T}
          (e : IsInverse F G) (f : IsInverse H I) :
  IsInverse (H ⊙ F) (G ⊙ I) :=
{ leftInv  := LeftInv.trans        e.leftInv  f.leftInv,
  rightInv := LeftInv.trans        f.rightInv e.rightInv,
  lrCompat := LeftInv.Compat.trans e.lrCompat f.lrCompat,
  rlCompat := LeftInv.Compat.trans f.rlCompat e.rlCompat }

theorem symm_symm {F : StructureFunctor S T} {G : StructureFunctor T S} (e : IsInverse F G) : symm (symm e) = e :=
match e with
| ⟨_, _, _, _⟩ => rfl 

end IsInverse



-- A functor between instance structures is actually just a function.

def congrArgFunctor {α : Sort u} {β : Sort v} (f : α → β) :
  @GeneralizedFunctor.Functor (instanceStructure α) (instanceStructure β) f :=
{ mapEquiv  := _root_.congrArg f,
  isFunctor := propFunctor }

def InstanceStructureFunctor (α β : Sort u) := StructureFunctor (instanceStructure α) (instanceStructure β)

def instanceStructureFunctor {α β : Sort u} (f : α → β) : InstanceStructureFunctor α β :=
{ map     := f,
  functor := congrArgFunctor f }



-- If we have a function `F` and an equivalent functor `G`, we can turn `F` into a functor as well.

def proxyFunctor {S T : Structure} (F : S → T) (G : StructureFunctor S T) (η : PiEquiv F G.map) :
  StructureFunctor S T :=
{ map     := F,
  functor := comp.genFun G.functor (PiEquiv.transport.invFunctor η) }

end StructureFunctor

open StructureFunctor



-- Based on the definition of a functor between two structures, we can define equivalence of two
-- structures similarly to equivalence of types in mathlib.

structure StructureEquiv (S T : Structure) where
(toFun  : StructureFunctor S T)
(invFun : StructureFunctor T S)
(isInv  : IsInverse toFun invFun)

namespace StructureEquiv

def refl  (S     : Structure)                                                   : StructureEquiv S S :=
{ toFun  := idFun,
  invFun := idFun,
  isInv  := IsInverse.refl  S }

def symm  {S T   : Structure} (e : StructureEquiv S T)                          : StructureEquiv T S :=
{ toFun  := e.invFun,
  invFun := e.toFun,
  isInv  := IsInverse.symm  e.isInv }

def trans {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) : StructureEquiv S U :=
{ toFun  := f.toFun  ⊙ e.toFun,
  invFun := e.invFun ⊙ f.invFun,
  isInv  := IsInverse.trans e.isInv f.isInv }

theorem symm_symm {S T : Structure} (e : StructureEquiv S T) : symm (symm e) = e :=
match e with
| ⟨toFun, invFun, isInv⟩ => IsInverse.symm_symm isInv ▸ rfl 



-- We can compare two instances of `StructureEquiv` by comparing `toFun` and `invFun` and then dependently
-- comparing `leftInv` and `rightInv`. That turns `StructureEquiv` into a structure.

structure EquivEquiv {S T : Structure} (e f : StructureEquiv S T) where
(toFunEquiv    : e.toFun  ≃ f.toFun)
(invFunEquiv   : e.invFun ≃ f.invFun)
(leftInvEquiv  : LeftInv.Equiv toFunEquiv  invFunEquiv e.isInv.leftInv  f.isInv.leftInv)
(rightInvEquiv : LeftInv.Equiv invFunEquiv toFunEquiv  e.isInv.rightInv f.isInv.rightInv)

namespace EquivEquiv

variable {S T : Structure}

def refl  (e     : StructureEquiv S T)                                           : EquivEquiv e e :=
{ toFunEquiv    := HasRefl.refl   e.toFun,
  invFunEquiv   := HasRefl.refl   e.invFun,
  leftInvEquiv  := LeftInv.Equiv.refl  e.isInv.leftInv,
  rightInvEquiv := LeftInv.Equiv.refl  e.isInv.rightInv }

def symm  {e f   : StructureEquiv S T} (η : EquivEquiv e f)                      : EquivEquiv f e :=
{ toFunEquiv    := HasSymm.symm   η.toFunEquiv,
  invFunEquiv   := HasSymm.symm   η.invFunEquiv,
  leftInvEquiv  := LeftInv.Equiv.symm  η.leftInvEquiv,
  rightInvEquiv := LeftInv.Equiv.symm  η.rightInvEquiv }

def trans {e f g : StructureEquiv S T} (η : EquivEquiv e f) (θ : EquivEquiv f g) : EquivEquiv e g :=
{ toFunEquiv    := HasTrans.trans η.toFunEquiv    θ.toFunEquiv,
  invFunEquiv   := HasTrans.trans η.invFunEquiv   θ.invFunEquiv,
  leftInvEquiv  := LeftInv.Equiv.trans η.leftInvEquiv  θ.leftInvEquiv,
  rightInvEquiv := LeftInv.Equiv.trans η.rightInvEquiv θ.rightInvEquiv }



-- For equivalence of `EquivEquiv`, we can reuse the equivalence of `StructureProduct`, as `leftInvEquiv`
-- and `rightInvEquiv` are just proofs.

@[reducible] def FunProd (S T : Structure) := StructureProduct (functorStructure S T) (functorStructure T S)

def funProd {S T : Structure} (e : StructureEquiv S T) : FunProd S T :=
⟨e.toFun, e.invFun⟩

def funEquivProd {e f : StructureEquiv S T} (η : EquivEquiv e f) :
  funProd e ≃ funProd f :=
⟨η.toFunEquiv, η.invFunEquiv⟩

def EquivEquivEquiv {e f : StructureEquiv S T} (η θ : EquivEquiv e f) :=
funEquivProd η ≈ funEquivProd θ

namespace EquivEquivEquiv

variable {e f : StructureEquiv S T}

theorem refl  (η     : EquivEquiv e f)                                                     : EquivEquivEquiv η η :=
StructureProduct.ProductEquiv.EquivEquiv.refl  (funEquivProd η)

theorem symm  {η θ   : EquivEquiv e f} (h : EquivEquivEquiv η θ)                           : EquivEquivEquiv θ η :=
StructureProduct.ProductEquiv.EquivEquiv.symm  h

theorem trans {η θ ζ : EquivEquiv e f} (h : EquivEquivEquiv η θ) (i : EquivEquivEquiv θ ζ) : EquivEquivEquiv η ζ :=
StructureProduct.ProductEquiv.EquivEquiv.trans h i

instance equivEquivSetoid : Setoid (EquivEquiv e f) := ⟨EquivEquivEquiv, ⟨refl, symm, trans⟩⟩

end EquivEquivEquiv

def equivEquiv (e f : StructureEquiv S T) : BundledSetoid := ⟨EquivEquiv e f⟩

instance equivHasIso : HasIsomorphisms (@equivEquiv S T) :=
{ refl          := refl,
  symm          := symm,
  trans         := trans,
  comp_congrArg := λ {e f g η₁ η₂ θ₁ θ₂} (hη : EquivEquivEquiv η₁ η₂) (hθ : EquivEquivEquiv θ₁ θ₂) =>
                     HasStructure.comp_congrArg hη hθ,
  inv_congrArg  := λ {e f   η₁ η₂}       (hη : EquivEquivEquiv η₁ η₂)                              =>
                     HasStructure.inv_congrArg  hη,
  assoc         := λ η θ ζ => HasStructure.assoc    (funEquivProd η) (funEquivProd θ) (funEquivProd ζ),
  leftId        := λ η     => HasStructure.leftId   (funEquivProd η),
  rightId       := λ η     => HasStructure.rightId  (funEquivProd η),
  leftInv       := λ η     => HasStructure.leftInv  (funEquivProd η),
  rightInv      := λ η     => HasStructure.rightInv (funEquivProd η),
  invInv        := λ η     => HasStructure.invInv   (funEquivProd η),
  compInv       := λ η θ   => HasStructure.compInv  (funEquivProd η) (funEquivProd θ),
  idInv         := λ e     => HasStructure.idInv    (funProd e) }

end EquivEquiv

instance equivHasStructure (S T : Structure) : HasStructure (StructureEquiv S T) := ⟨EquivEquiv.equivEquiv⟩
def equivStructure (S T : Structure) : Structure := ⟨StructureEquiv S T⟩



def toFunProj (S T : Structure) : StructureFunctor (equivStructure S T) (functorStructure S T) :=
{ map     := StructureEquiv.toFun,
  functor := { mapEquiv  := EquivEquiv.toFunEquiv,
               isFunctor := { respectsEquiv := And.left,
                              respectsComp  := λ η θ => Setoid.refl (θ.toFunEquiv • η.toFunEquiv),
                              respectsId    := λ e   => Setoid.refl (id__ (S := functorStructure S T) e.toFun),
                              respectsInv   := λ η   => Setoid.refl (η.toFunEquiv)⁻¹ } } }

def invFunProj (S T : Structure) : StructureFunctor (equivStructure S T) (functorStructure T S) :=
{ map     := StructureEquiv.invFun,
  functor := { mapEquiv  := EquivEquiv.invFunEquiv,
               isFunctor := { respectsEquiv := And.right,
                              respectsComp  := λ η θ => Setoid.refl (θ.invFunEquiv • η.invFunEquiv),
                              respectsId    := λ e   => Setoid.refl (id__ (S := functorStructure T S) e.invFun),
                              respectsInv   := λ η   => Setoid.refl (η.invFunEquiv)⁻¹ } } }



def comp_congrArg {S T U : Structure} {e₁ e₂ : StructureEquiv S T} {f₁ f₂ : StructureEquiv T U} (he : e₁ ≃ e₂) (hf : f₁ ≃ f₂) :
  trans e₁ f₁ ≃ trans e₂ f₂ :=
{ toFunEquiv    := compFun.congrArg he.toFunEquiv  hf.toFunEquiv,
  invFunEquiv   := compFun.congrArg hf.invFunEquiv he.invFunEquiv,
  leftInvEquiv  := sorry,
  rightInvEquiv := sorry }

theorem assoc_leftInvEquiv {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  LeftInv.Equiv (FunctorEquiv.refl (g.toFun  ⊙ f.toFun  ⊙ e.toFun))
                (FunctorEquiv.refl (e.invFun ⊙ f.invFun ⊙ g.invFun))
                (IsInverse.trans (IsInverse.trans e.isInv f.isInv) g.isInv).leftInv
                (IsInverse.trans e.isInv (IsInverse.trans f.isInv g.isInv)).leftInv :=
LeftInv.Equiv.refl' (LeftInv.trans_assoc e.isInv.leftInv f.isInv.leftInv g.isInv.leftInv)

theorem assoc_rightInvEquiv {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  LeftInv.Equiv (FunctorEquiv.refl (e.invFun ⊙ f.invFun ⊙ g.invFun))
                (FunctorEquiv.refl (g.toFun  ⊙ f.toFun  ⊙ e.toFun))
                (IsInverse.trans (IsInverse.trans e.isInv f.isInv) g.isInv).rightInv
                (IsInverse.trans e.isInv (IsInverse.trans f.isInv g.isInv)).rightInv :=
LeftInv.Equiv.refl' (Setoid.symm (LeftInv.trans_assoc g.isInv.rightInv f.isInv.rightInv e.isInv.rightInv))

def assoc {S T U V : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) (g : StructureEquiv U V) :
  trans (trans e f) g ≃ trans e (trans f g) :=
{ toFunEquiv    := compFun.assoc e.toFun  f.toFun  g.toFun,
  invFunEquiv   := compFun.assoc g.invFun f.invFun e.invFun,
  leftInvEquiv  := assoc_leftInvEquiv  e f g,
  rightInvEquiv := assoc_rightInvEquiv e f g }

theorem leftId_leftInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv (idFun.leftId e.toFun)
                (idFun.leftId e.invFun)
                (IsInverse.trans e.isInv (IsInverse.refl T)).leftInv
                e.isInv.leftInv :=
let h₁ := LeftInv.trans_refl e.isInv.leftInv;
λ a => let h₂ := h₁ a;
       sorry

theorem rightId_leftInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv (idFun.rightId e.toFun)
                (idFun.rightId e.invFun)
                (IsInverse.trans (IsInverse.refl S) e.isInv).leftInv
                e.isInv.leftInv :=
sorry

def leftId  {S T : Structure} (e : StructureEquiv S T) : trans e (refl T) ≃ e :=
{ toFunEquiv    := idFun.leftId e.toFun,
  invFunEquiv   := idFun.leftId e.invFun,
  leftInvEquiv  := leftId_leftInvEquiv  e,
  rightInvEquiv := rightId_leftInvEquiv (symm e) }

def rightId {S T : Structure} (e : StructureEquiv S T) : trans (refl S) e ≃ e :=
{ toFunEquiv    := idFun.rightId e.toFun,
  invFunEquiv   := idFun.rightId e.invFun,
  leftInvEquiv  := rightId_leftInvEquiv e,
  rightInvEquiv := leftId_leftInvEquiv  (symm e) }

def inv_congrArg {S T : Structure} {e₁ e₂ : StructureEquiv S T} (he : e₁ ≃ e₂) :
  symm e₁ ≃ symm e₂ :=
{ toFunEquiv    := he.invFunEquiv,
  invFunEquiv   := he.toFunEquiv,
  leftInvEquiv  := he.rightInvEquiv,
  rightInvEquiv := he.leftInvEquiv }

theorem leftInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv e.isInv.leftInv e.isInv.leftInv (IsInverse.trans e.isInv (IsInverse.symm e.isInv)).leftInv (IsInverse.refl S).leftInv :=
let h₁ : LeftInv.trans e.isInv.leftInv e.isInv.rightInv ≈ compFun.congrArg' e.isInv.leftInv e.isInv.leftInv :=
    λ a => Setoid.trans (LeftInv.transDef e.isInv.leftInv e.isInv.rightInv a) (comp_congrArg_right (respectsSetoid e.invFun (Setoid.symm (e.isInv.lrCompat a))));
let h₂ := Setoid.trans h₁ (Setoid.symm (compFun.congrArg.wd e.isInv.leftInv e.isInv.leftInv));
Setoid.trans h₂ (Setoid.symm (HasStructure.leftId (compFun.congrArg e.isInv.leftInv e.isInv.leftInv)))

def leftInv'  {S T : Structure} (e : StructureEquiv S T) : trans e (symm e) ≃ refl S :=
{ toFunEquiv    := e.isInv.leftInv,
  invFunEquiv   := e.isInv.leftInv,
  leftInvEquiv  := leftInvEquiv e,
  rightInvEquiv := leftInvEquiv e }

theorem rightInvEquiv {S T : Structure} (e : StructureEquiv S T) :
  LeftInv.Equiv e.isInv.rightInv e.isInv.rightInv (IsInverse.trans (IsInverse.symm e.isInv) e.isInv).rightInv (IsInverse.refl T).rightInv :=
let h₁ : LeftInv.trans e.isInv.rightInv e.isInv.leftInv ≈ compFun.congrArg' e.isInv.rightInv e.isInv.rightInv :=
    λ a => Setoid.trans (LeftInv.transDef e.isInv.rightInv e.isInv.leftInv a) (comp_congrArg_right (respectsSetoid e.toFun (Setoid.symm (e.isInv.rlCompat a))));
let h₂ := Setoid.trans h₁ (Setoid.symm (compFun.congrArg.wd e.isInv.rightInv e.isInv.rightInv));
Setoid.trans h₂ (Setoid.symm (HasStructure.leftId (compFun.congrArg e.isInv.rightInv e.isInv.rightInv)))

def rightInv' {S T : Structure} (e : StructureEquiv S T) : trans (symm e) e ≃ refl T :=
{ toFunEquiv    := e.isInv.rightInv,
  invFunEquiv   := e.isInv.rightInv,
  leftInvEquiv  := rightInvEquiv e,
  rightInvEquiv := rightInvEquiv e }

def invInv {S T : Structure} (e : StructureEquiv S T) : symm (symm e) ≃ e :=
symm_symm e ▸ EquivEquiv.refl e

def compInv {S T U : Structure} (e : StructureEquiv S T) (f : StructureEquiv T U) :
  symm (trans e f) ≃ trans (symm f) (symm e) :=
EquivEquiv.refl (symm (trans e f))

def idInv (S : Structure) : symm (refl S) ≃ refl S :=
EquivEquiv.refl (refl S)

instance equivHasIso : HasIsomorphisms equivStructure :=
{ refl          := refl,
  symm          := symm,
  trans         := trans,
  comp_congrArg := comp_congrArg,
  inv_congrArg  := inv_congrArg,
  assoc         := assoc,
  leftId        := leftId,
  rightId       := rightId,
  leftInv       := leftInv',
  rightInv      := rightInv',
  invInv        := invInv,
  compInv       := compInv,
  idInv         := idInv }

end StructureEquiv



instance structureHasGeneralStructure : HasGeneralStructure Structure := ⟨StructureEquiv.equivStructure⟩
instance structureHasEquivalence : HasEquivalence Structure Structure := ⟨StructureEquiv.equivStructure⟩
instance structureEquivIsTypeWithEquiv : IsTypeWithEquivalence (HasEquivalence.γ Structure Structure) := Structure.structureIsTypeWithEquiv
instance structureEquivIsType : IsType (HasEquivalence.γ Structure Structure) := structureEquivIsTypeWithEquiv.toIsType
instance (S T : Structure) : Setoid (IsType.type (S ≃ T)) := instanceEquivSetoid (IsType.type (S ≃ T))
instance (S T : Structure) : HasStructure (IsType.type (S ≃ T)) := StructureEquiv.equivHasStructure S T
instance : HasIsomorphisms (@HasEquivalence.Equiv Structure Structure structureHasEquivalence) := HasGeneralStructure.hasIso



-- If we have a `StructureEquiv S T`, we can ask whether it maps `a : S` to `b : T`. This is similar to
-- an equivalence. It corresponds to a "dependent equivalence" or "pathover" in HoTT, so we adopt the same
-- notation `a ≃[e] b`.

def InstanceEquiv {S T : Structure} (e : S ≃ T) (a : S) (b : T) := e.toFun a ≃ b

namespace InstanceEquiv

notation:25 a:26 " ≃[" e:0 "] " b:26 => InstanceEquiv e a b

def fromEquiv (S : Structure) {a b : S} : a ≃ b → a ≃[id_ S] b := id
def toEquiv   (S : Structure) {a b : S} : a ≃[id_ S] b → a ≃ b := id

def refl  (S     : Structure)                         (a : S)                 :
  a ≃[id_ S] a :=
fromEquiv S (HasRefl.refl a)

def symm  {S T   : Structure} (e : S ≃ T)             (a : S) (b : T)         :
  a ≃[e] b → b ≃[e⁻¹] a :=
λ φ => HasTrans.trans (HasSymm.symm (congrArg e.invFun φ)) (e.isInv.leftInv.ext a)

def trans {S T U : Structure} (e : S ≃ T) (f : T ≃ U) (a : S) (b : T) (c : U) :
  a ≃[e] b → b ≃[f] c → a ≃[f • e] c :=
λ φ ψ => HasTrans.trans (congrArg f.toFun φ) ψ

def mapEquiv {S T : Structure} {e₁ e₂ : S ≃ T} (η : e₁ ≃ e₂) (a : S) (b : T) :
  a ≃[e₁] b → a ≃[e₂] b :=
HasTrans.trans (HasSymm.symm (η.toFunEquiv.ext a))

end InstanceEquiv



-- Using `StructureEquiv`, we can build a "universe" structure where the objects are structures. This is
-- the same as the groupoid of lower-level groupoids.
--
-- `universeStructure` contains an implicit truncation of `EquivEquiv` to a proposition, via
-- `hasTruncatedStructure`. In `TwoStructure.lean`, we give the definition of an enlarged structure that
-- allows us to keep this data instead.

def universeStructure : Structure := ⟨Structure⟩

instance : IsType (IsType.type universeStructure) := structureIsType
