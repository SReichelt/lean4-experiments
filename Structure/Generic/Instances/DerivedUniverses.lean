import Structure.Generic.Axioms



set_option autoBoundImplicitLocal false
--set_option pp.universes true

universes u v



structure UniverseProduct (U : Universe.{u}) (V : Universe.{v}) : Type (max 1 u v) where
(α : U)
(β : V)

def functorUniverse (U : Universe.{u}) (V : Universe.{v}) [HasExternalFunctors U V] : Universe.{max 1 u v} :=
{ α    := UniverseProduct U V,
  inst := ⟨λ P => P.α ⟶' P.β⟩ }

def equivalenceUniverse (U : Universe.{u}) (V : Universe.{v}) [HasExternalFunctors U V] [HasExternalFunctors V U]
                                                              [HasExternalEquivalences U V] : Universe.{max 1 u v} :=
{ α    := UniverseProduct U V,
  inst := ⟨λ P => P.α ⟷' P.β⟩ }

def productUniverse (U : Universe.{u}) (V : Universe.{v}) : Universe.{max 1 u v} :=
{ α    := UniverseProduct U V,
  inst := ⟨λ P => PProd ⌈P.α⌉ ⌈P.β⌉⟩ }
