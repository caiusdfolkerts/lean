module

public import ToricPower.CechToricLinearCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# The actual toric Čech complex over the complex numbers

This comparison is between the ordinary complex-linear Čech complex of
an actual Cartier sheaf and the literal tuple space of supported Laurent
polynomials. Every tuple selection, hence every differential, preserves
its full Laurent polynomial. There is no choice of scalar structure or
restriction to finitely many characters.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.Toric
open scoped Simplicial Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones) (b : fan.Ray → ℤ)

/-- All full-character Laurent coefficients in a tuple degree. -/
def toricCechLaurentLinearDegree (q : ℕ) : ModuleCat ℂ :=
  ModuleCat.of ℂ (∀ tuple : Fin (q+1) → Index,
    toricCechLaurentLinearCoefficient fan charts b q tuple)

/-- Selection of tuple entries keeps each actual Laurent polynomial. -/
def toricCechLaurentLinearTupleMap {p q : ℕ}
    (selection : Fin (p+1) → Fin (q+1)) :
    toricCechLaurentLinearDegree fan charts b p ⟶
      toricCechLaurentLinearDegree fan charts b q :=
  ModuleCat.ofHom
    { toFun := fun a tuple => toricLaurentCoefficientRestriction fan b
        (toricCechCone_le_selection fan charts selection tuple) (a (tuple ∘ selection))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The complete cosimplicial module of actual Laurent polynomials. -/
def toricCechLaurentLinearCosimplicial : CosimplicialObject (ModuleCat ℂ) where
  obj a := toricCechLaurentLinearDegree fan charts b a.len
  map f := toricCechLaurentLinearTupleMap fan charts b f.toOrderHom
  map_id a := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The literal full complex-linear Laurent Čech complex. -/
def toricCechLaurentLinearComplex : CochainComplex (ModuleCat ℂ) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj
    (toricCechLaurentLinearCosimplicial fan charts b)

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)

/-- The ordinary Čech cosimplicial module of the actual Cartier sheaf. -/
def toricCechActualLinearCosimplicial : CosimplicialObject (ModuleCat ℂ) :=
  letI := toricSchemeIntegral fan nonempty
  (FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk Index (toricCechChartOpen fan charts)).cech).obj
      ((FiniteCover.schemeBasePresheaf ℂ fan.algebraicRealization).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf)

/-- The ordinary complex-linear Čech complex, with its specified scheme scalars. -/
def toricCechActualLinearComplex : CochainComplex (ModuleCat ℂ) ℕ :=
  letI := toricSchemeIntegral fan nonempty
  (cechComplexFunctor (toricCechChartOpen fan charts)).obj
    ((FiniteCover.schemeBasePresheaf ℂ fan.algebraicRealization).obj
      (invariantCartierDivisor fan nonempty regular b).sheaf)

/-- The actual sectionwise coordinate isomorphisms, followed by the
canonical identification of a product with its tuple functions. -/
def toricCechLinearDegreeIso (q : ℕ) :
    (toricCechActualLinearCosimplicial fan charts b nonempty regular).obj ⦋q⦌ ≅
      toricCechLaurentLinearDegree fan charts b q :=
  Limits.Pi.mapIso (fun tuple =>
    (toricCechCoefficientLinearEquiv fan charts nonempty regular b q tuple).toModuleIso) ≪≫
      ModuleCat.piIsoPi (toricCechLaurentLinearCoefficient fan charts b q)

/-- The degree isomorphism is the literal Laurent coordinate map at each tuple. -/
theorem toricCechLinearDegreeIso_hom_apply (q : ℕ)
    (x : (toricCechActualLinearCosimplicial fan charts b nonempty regular).obj ⦋q⦌)
    (tuple : Fin (q+1) → Index) :
    (toricCechLinearDegreeIso fan charts b nonempty regular q).hom x tuple =
      toricCechCoefficientLinearEquiv fan charts nonempty regular b q tuple
        (Limits.Pi.π (toricCechActualLinearCoefficient fan charts nonempty regular b q) tuple x) := by
  have h := ConcreteCategory.congr_hom
    (ModuleCat.piIsoPi_hom_ker_subtype
      (toricCechLaurentLinearCoefficient fan charts b q) tuple)
      ((Limits.Pi.mapIso (fun tuple =>
        (toricCechCoefficientLinearEquiv fan charts nonempty regular b q tuple).toModuleIso)).hom x)
  change _ = _ at h
  exact h.trans (ConcreteCategory.congr_hom
    (Limits.Pi.mapIso_hom_π (fun tuple =>
      (toricCechCoefficientLinearEquiv fan charts nonempty regular b q tuple).toModuleIso) tuple) x)

/-- The actual coefficient comparison commutes with every tuple selection. -/
theorem toricCechLinearDegreeIso_selection {p q : ℕ}
    (f : ⦋p⦌ ⟶ ⦋q⦌) :
    (toricCechActualLinearCosimplicial fan charts b nonempty regular).map f ≫
        (toricCechLinearDegreeIso fan charts b nonempty regular q).hom =
      (toricCechLinearDegreeIso fan charts b nonempty regular p).hom ≫
        toricCechLaurentLinearTupleMap fan charts b f.toOrderHom := by
  haveI := toricSchemeIntegral fan nonempty
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext tuple
  change (toricCechLinearDegreeIso fan charts b nonempty regular q).hom
      ((toricCechActualLinearCosimplicial fan charts b nonempty regular).map f x) tuple =
    toricLaurentCoefficientRestriction fan b
      (toricCechCone_le_selection fan charts f.toOrderHom tuple)
      ((toricCechLinearDegreeIso fan charts b nonempty regular p).hom x (tuple ∘ f.toOrderHom))
  rw [toricCechLinearDegreeIso_hom_apply, toricCechLinearDegreeIso_hom_apply]
  have projected := ConcreteCategory.congr_hom
    (Limits.Pi.lift_comp_π (fun t : Fin (q+1) → Index =>
      Limits.Pi.π (toricCechActualLinearCoefficient fan charts nonempty regular b p)
        (t ∘ f.toOrderHom) ≫
        ((FiniteCover.schemeBasePresheaf ℂ fan.algebraicRealization).obj
          (invariantCartierDivisor fan nonempty regular b).sheaf).map
          (Limits.Pi.lift (fun j : Fin (p+1) =>
            Limits.Pi.π (toricCechChartOpen fan charts ∘ t) (f.toOrderHom j))).op) tuple) x
  change Limits.Pi.π (toricCechActualLinearCoefficient fan charts nonempty regular b q) tuple
    ((toricCechActualLinearCosimplicial fan charts b nonempty regular).map f x) = _ at projected
  rw [projected]
  rw [toricCechCoefficientLinearEquiv_apply, toricCechCoefficientLinearEquiv_apply]
  exact toricCechCoefficientEquiv_selection fan charts nonempty regular b f.toOrderHom tuple _

/-- The complete cosimplicial comparison, including codegeneracies. -/
def toricCechLinearCosimplicialIso :
    toricCechActualLinearCosimplicial fan charts b nonempty regular ≅
      toricCechLaurentLinearCosimplicial fan charts b :=
  NatIso.ofComponents (fun q => toricCechLinearDegreeIso fan charts b nonempty regular q.len)
    (fun f => toricCechLinearDegreeIso_selection fan charts b nonempty regular f)

/-- The full actual complex-linear Čech complex is the literal Laurent
complex, by an isomorphism of complexes before any localization. -/
def toricCechLinearComplexIso :
    toricCechActualLinearComplex fan charts b nonempty regular ≅
      toricCechLaurentLinearComplex fan charts b :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat ℂ)).mapIso
    (toricCechLinearCosimplicialIso fan charts b nonempty regular)

end ToricPower
