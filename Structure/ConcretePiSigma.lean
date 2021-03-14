import Structure.Basic
import Structure.AbstractPiSigma
import Structure.SortStructure

open StructureFunctor
open PiSigma



namespace PiSigma

-- Every term of type `∀ x, F x` or `Σ' x, F x` where everything has structures and functors can be
-- converted to an instance of `PiExpr` or `SigmaExpr`, respectively.

def toStructureDependency {S : Structure} (F : StructureFunctor S sortStructure) : StructureDependency :=
⟨S, compFun F sortToStructureFunctor⟩

def encodePiExpr    {α : Sort u} [h : HasStructure α] (F : StructureFunctor (defaultStructure α) sortStructure) (f : ∀  x : α, F x) :
  PiExpr    (toStructureDependency F) := ⟨f⟩

def encodeSigmaExpr {α : Sort u} [h : HasStructure α] (F : StructureFunctor (defaultStructure α) sortStructure) (s : Σ' x : α, F x) :
  SigmaExpr (toStructureDependency F) := ⟨s.fst, s.snd⟩

end PiSigma
