module

public import ToricPower.CellularPointSerre
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Inverse Nakayama on the actual co-representable injectives

The ordinary functor Hom(I_c,−) sends I_d to the actual representable
P_d when the incidence Hom sets are finite. The map is the literal
Yoneda map determined by the identity of I_d; its invertibility is
checked by the dual basis of the finite function space on incidences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k]

def finiteFunctionDualEquiv (I : Type u) [Finite I] :
    (I →₀ k) ≃ₗ[k] Module.Dual k (I → k) :=
  letI := Fintype.ofFinite I
  (Pi.basisFun k I).dualBasis.repr.symm

@[simp]
theorem finiteFunctionDualEquiv_single (I : Type u) [Finite I] (i : I) (x : I → k) :
    finiteFunctionDualEquiv k I (Finsupp.single i 1) x = x i := by
  unfold finiteFunctionDualEquiv
  rw [Module.Basis.repr_symm_single_one, Module.Basis.dualBasis_apply, Pi.basisFun_repr]

variable {C : Type u} [Category.{u} C]

/-- The canonical map, determined by the actual identity incidence. -/
def inverseNakayamaPointMap (c : C) :
    representable k c ⟶ (inverseNakayama k).obj (pointCorepresentable k c) :=
  fromValue k ((inverseNakayama k).obj (pointCorepresentable k c)) c
    (𝟙 (pointCorepresentable k c))

theorem inverseNakayamaPointMap_evaluate (c d : C) (a : c ⟶ d) (x : (c ⟶ d) → k) :
    pointCoinducedHomLinearEquiv k (pointCorepresentable k d) c (ModuleCat.of k k)
      ((inverseNakayamaPointMap k c).app d (ModuleCat.freeMk a)) x = x a := by
  rw [inverseNakayamaPointMap, fromValue_app_freeMk]
  change x (𝟙 c ≫ a) = x a
  rw [Category.id_comp]

variable [∀ c d : C, Finite (c ⟶ d)]

theorem inverseNakayamaPointMap_isIso_app (c d : C) :
    IsIso ((inverseNakayamaPointMap k c).app d) := by
  let e := pointCoinducedHomLinearEquiv k (pointCorepresentable k d) c (ModuleCat.of k k)
  have equation : e.toLinearMap.comp ((inverseNakayamaPointMap k c).app d).hom =
      (finiteFunctionDualEquiv k (c ⟶ d)).toLinearMap := by
    apply (Finsupp.basisSingleOne : Module.Basis (c ⟶ d) k ((c ⟶ d) →₀ k)).ext
    intro a
    apply LinearMap.ext
    intro x
    exact (inverseNakayamaPointMap_evaluate k c d a x).trans
      (finiteFunctionDualEquiv_single k (c ⟶ d) a x).symm
  have bijective : Function.Bijective
      (e.toLinearMap.comp ((inverseNakayamaPointMap k c).app d).hom) := by
    rw [equation]
    exact (finiteFunctionDualEquiv k (c ⟶ d)).bijective
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y equal
    apply bijective.injective
    exact congrArg e equal
  · intro y
    obtain ⟨x, hx⟩ := bijective.surjective (e y)
    exact ⟨x, e.injective hx⟩

instance inverseNakayamaPointMap_isIso (c : C) : IsIso (inverseNakayamaPointMap k c) := by
  letI (d : C) := inverseNakayamaPointMap_isIso_app k c d
  exact NatIso.isIso_of_isIso_app _

/-- The resulting isomorphism includes every original incidence map. -/
def inverseNakayamaCorepresentableIso (c : C) :
    (inverseNakayama k).obj (pointCorepresentable k c) ≅ representable k c :=
  (asIso (inverseNakayamaPointMap k c)).symm

theorem inverseNakayamaCorepresentable_projective (c : C) :
    Projective ((inverseNakayama k).obj (pointCorepresentable k c)) :=
  Projective.of_iso (inverseNakayamaCorepresentableIso k c).symm inferInstance

end ToricPower.Cellular

end

