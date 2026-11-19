module

public import ToricPower.CellularFiniteDerivedModels
public import ToricPower.FiniteDiagramHomSpace
public import ToricPower.SerrePairingDerivedComplex
public import Mathlib.Data.Int.Interval

/-!
# Finite-dimensional morphisms between bounded finite diagrams

Finite injective models compute the actual derived Hom spaces. Their
signed Hom complex has finite-dimensional terms: only finitely many
target degrees contribute, and every natural-transformation space is
a subspace of a finite product of finite-dimensional coefficient Hom
spaces. Passing to homology preserves finiteness.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [Finite C] [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

theorem finiteDiagramCochain_finite
    (J K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q c, FiniteDimensional k ((J.X q).obj c)]
    [∀ q c, FiniteDimensional k ((K.X q).obj c)]
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] (n : ℤ) :
    FiniteDimensional k (Cochain J K n) := by
  let support := Finset.Icc a b
  have outside (q : ℤ) (hq : q ∉ support) : IsZero (K.X q) := by
    by_cases h : q < a
    · exact K.isZero_of_isStrictlyGE a q h
    · exact K.isZero_of_isStrictlyLE b q (by
        simp only [support, Finset.mem_Icc] at hq
        omega)
  letI (q : support) : FiniteDimensional k (J.X (q.val - n) ⟶ K.X q) :=
    finiteDiagramHom_finite_of_finite_objects k _ _
  let e := SerrePairing.cochainFiniteTargetValues k J K n support outside
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

theorem finiteInjectiveModel_derivedHom_finite
    {X Y : DerivedCategory (C ⥤ ModuleCat.{u} k)}
    (modelX : finiteInjectiveModels k X) (modelY : finiteInjectiveModels k Y) :
    FiniteDimensional k (X ⟶ Y) := by
  obtain ⟨J, a, b, hIJ, hFJ, hgeJ, hleJ, ⟨eJ⟩⟩ := modelX
  obtain ⟨K, c, d, hIK, hFK, hgeK, hleK, ⟨eK⟩⟩ := modelY
  letI := hFJ
  letI := hFK
  letI := hIK
  letI := hgeK
  letI := hleK
  letI : K.IsKInjective := CochainComplex.isKInjective_of_injective K c
  letI : FiniteDimensional k ((linearHomComplex k J K).X 0) :=
    finiteDiagramCochain_finite k J K c d 0
  letI : FiniteDimensional k ((linearHomComplex k J K).homology 0) :=
    complexHomology_finiteDimensional (linearHomComplex k J K) 0
  let e := (HomComplex.homologyLinearEquiv k J K 0).trans
    ((SerrePairing.homClassDerivedZeroEquivOfKInjective k J K).trans
      (Linear.homCongr k eJ eK))
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

variable [∀ c d : C, Finite (c ⟶ d)] [∀ c : C, Subsingleton (c ⟶ c)]
variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  (N : ℕ) (bound : ∀ c, grade c ≤ N)

include grade grade_le eq_of_grade_eq N bound

theorem boundedFiniteDerived_hom_finite
    (X Y : DerivedCategory (C ⥤ ModuleCat.{u} k))
    (boundedX : DerivedCategory.TStructure.t.bounded X)
    (boundedY : DerivedCategory.TStructure.t.bounded Y)
    (finiteX : pointwiseFiniteDerived k X) (finiteY : pointwiseFiniteDerived k Y) :
    FiniteDimensional k (X ⟶ Y) :=
  finiteInjectiveModel_derivedHom_finite k
    (bounded_finiteInjectiveModel k grade grade_le eq_of_grade_eq N bound X boundedX finiteX)
    (bounded_finiteInjectiveModel k grade grade_le eq_of_grade_eq N bound Y boundedY finiteY)

end ToricPower.Cellular

end
