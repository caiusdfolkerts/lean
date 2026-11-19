module

public import ToricPower.CellularFiniteDerivedModels
public import ToricPower.CellularInverseInjectiveComplex
public import ToricPower.CellularInverseNakayamaModel
public import ToricPower.DerivedFunctorOnInjectiveComplex
public import ToricPower.RightDerivedModelComparison

/-!
# Explicit finite injective models and their derived inverse Nakayama

A model is data representing the original derived object by a bounded
complex of finite-dimensional injective diagrams. Existence is supplied
by the proved truncation and finite-resolution theorem. The comparison
for inverse Nakayama is the actual right-derived functor's unit.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

/- Select the same literal parent instances as the generic abelian
Hom-complex API. Local instance aliases would introduce distinct constants
inside quotient-module types, forcing expensive normalization. -/
attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

structure FiniteInjectiveModel (X : DerivedCategory (C ⥤ ModuleCat.{u} k)) where
  plusComplex : CochainComplex.Plus (C ⥤ ModuleCat.{u} k)
  lower : ℤ
  upper : ℤ
  injective : ∀ q, Injective (plusComplex.obj.X q)
  finite : ∀ q c, FiniteDimensional k ((plusComplex.obj.X q).obj c)
  strictlyGE : plusComplex.obj.IsStrictlyGE lower
  strictlyLE : plusComplex.obj.IsStrictlyLE upper
  iso : DerivedCategory.Q.obj plusComplex.obj ≅ X

theorem nonempty_finiteInjectiveModel
    {X : DerivedCategory (C ⥤ ModuleCat.{u} k)} (h : finiteInjectiveModels k X) :
    Nonempty (FiniteInjectiveModel k X) := by
  obtain ⟨J, a, b, hI, hF, hge, hle, ⟨e⟩⟩ := h
  exact ⟨⟨⟨J, a, hge⟩, a, b, hI, hF, hge, hle, e⟩⟩

def chooseFiniteInjectiveModel
    {X : DerivedCategory (C ⥤ ModuleCat.{u} k)} (h : finiteInjectiveModels k X) :
    FiniteInjectiveModel k X :=
  Classical.choice (nonempty_finiteInjectiveModel k h)

namespace FiniteInjectiveModel

variable {k} {X : DerivedCategory (C ⥤ ModuleCat.{u} k)}
variable (M : FiniteInjectiveModel k X)

/-- The underlying complex of the stored bounded-below model. -/
abbrev complex : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ := M.plusComplex.obj

instance (q : ℤ) : Injective (M.complex.X q) := M.injective q
instance (q : ℤ) (c : C) : FiniteDimensional k ((M.complex.X q).obj c) := M.finite q c
instance : M.plusComplex.obj.IsStrictlyGE M.lower := M.strictlyGE
instance : M.plusComplex.obj.IsStrictlyLE M.upper := M.strictlyLE
instance : M.complex.IsKInjective :=
  CochainComplex.isKInjective_of_injective M.complex M.lower

theorem plusComplex_injective (q : ℤ) : Injective (M.plusComplex.obj.X q) :=
  M.injective q

variable [Finite C] [∀ c d : C, Finite (c ⟶ d)]

abbrev inverseComplex : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ :=
  SerrePairing.mappedCochainComplex (inverseNakayama k) M.complex

instance (q : ℤ) : Projective (M.inverseComplex.X q) :=
  inverseNakayama_projective_of_finite_injective k (M.complex.X q)

instance (q : ℤ) (c : C) : FiniteDimensional k ((M.inverseComplex.X q).obj c) :=
  inverseNakayama_finite k (M.complex.X q) c

instance : M.inverseComplex.IsStrictlyGE M.lower := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro q hq
  exact (inverseNakayama k).map_isZero (M.complex.isZero_of_isStrictlyGE M.lower q hq)

instance : M.inverseComplex.IsStrictlyLE M.upper := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro q hq
  exact (inverseNakayama k).map_isZero (M.complex.isZero_of_isStrictlyLE M.upper q hq)

instance : M.inverseComplex.IsKProjective :=
  CochainComplex.isKProjective_of_projective M.inverseComplex M.upper

end FiniteInjectiveModel

namespace FiniteInjectiveModel

variable {k} {X : DerivedCategory.Plus (C ⥤ ModuleCat.{u} k)}
variable (M : FiniteInjectiveModel k X.obj)

def plusIso : DerivedCategory.Plus.Q.obj M.plusComplex ≅ X :=
  DerivedCategory.Plus.ι.preimageIso M.iso


end FiniteInjectiveModel

end ToricPower.Cellular

end
