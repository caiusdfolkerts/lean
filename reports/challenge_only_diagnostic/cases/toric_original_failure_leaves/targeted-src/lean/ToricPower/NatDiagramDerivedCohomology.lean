module

public import ToricPower.ComplexDiagramTranspose
public import ToricPower.CellularFiniteDerivedModels
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Actual cohomology of nonnegative complex-valued diagrams

Extension by zero and literal diagram transposition retain each scalar
module and every incidence map. The resulting derived homology is the
original homology in nonnegative degrees and zero in negative degrees.
Thus a uniform cohomology bound and degreewise finite-dimensionality
transfer to the actual derived category of full diagrams.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]
  (D : C ⥤ CochainComplex (ModuleCat.{u} k) ℕ)

abbrev natDiagramDerivedObject : DerivedCategory (C ⥤ ModuleCat.{u} k) :=
  DerivedCategory.Q.obj (complexDiagramTranspose
    (D ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} k)))

/-- The comparison is obtained from actual localization and the exact
point-evaluation functor, before computing the extension's homology. -/
def natDiagramDerivedHomologyIso (q : ℤ) (c : C) :
    (((DerivedCategory.homologyFunctor _ q).obj
      (natDiagramDerivedObject k D)).obj c) ≅
      ((D.obj c).extend ComplexShape.embeddingUpNat).homology q := by
  let K := complexDiagramTranspose
    (D ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} k))
  exact ((DerivedCategory.homologyFunctorFactors _ q).app K).app c ≪≫
    ((K.sc q).mapHomologyIso ((evaluation C (ModuleCat.{u} k)).obj c)).symm

/-- In a nonnegative degree, the original scalar cohomology is unchanged. -/
def natDiagramDerivedHomologyNatIso (q : ℕ) (c : C) :
    (((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
      (natDiagramDerivedObject k D)).obj c) ≅ (D.obj c).homology q :=
  natDiagramDerivedHomologyIso k D (q : ℤ) c ≪≫
    (D.obj c).extendHomologyIso ComplexShape.embeddingUpNat rfl

theorem natDiagramDerivedHomology_isZero_of_neg (q : ℤ) (negative : q < 0) (c : C) :
    IsZero (((DerivedCategory.homologyFunctor _ q).obj
      (natDiagramDerivedObject k D)).obj c) := by
  apply (natDiagramDerivedHomologyIso k D q c).isZero_iff.mpr
  exact (HomologicalComplex.ExactAt.of_isZero
    ((D.obj c).isZero_extend_X ComplexShape.embeddingUpNat q (by
      intro j
      change (j : ℤ) ≠ q
      omega))).isZero_homology

theorem natDiagramDerived_pointwiseFinite
    (finite : ∀ (q : ℕ) (c : C), FiniteDimensional k ((D.obj c).homology q)) :
    Cellular.pointwiseFiniteDerived k (natDiagramDerivedObject k D) := by
  intro q c
  cases q with
  | ofNat q =>
    letI := finite q c
    exact Module.Finite.equiv (natDiagramDerivedHomologyNatIso k D q c).symm.toLinearEquiv
  | negSucc q =>
    letI := ModuleCat.subsingleton_of_isZero
      (natDiagramDerivedHomology_isZero_of_neg k D (Int.negSucc q) (by omega) c)
    infer_instance

theorem natDiagramDerived_bounded (bound : ℕ)
    (high : ∀ (q : ℕ), bound < q → ∀ (c : C), IsZero ((D.obj c).homology q)) :
    DerivedCategory.TStructure.t.bounded (natDiagramDerivedObject k D) := by
  constructor
  · refine ⟨0, ?_⟩
    change (natDiagramDerivedObject k D).IsGE 0
    rw [DerivedCategory.isGE_iff]
    intro q negative
    rw [Functor.isZero_iff]
    exact natDiagramDerivedHomology_isZero_of_neg k D q negative
  · refine ⟨(bound : ℤ), ?_⟩
    change (natDiagramDerivedObject k D).IsLE (bound : ℤ)
    rw [DerivedCategory.isLE_iff]
    intro q hq
    rw [Functor.isZero_iff]
    intro c
    cases q with
    | ofNat q =>
      exact (natDiagramDerivedHomologyNatIso k D q c).isZero_iff.mpr
        (high q (by
          change (bound : ℤ) < (q : ℤ) at hq
          omega) c)
    | negSucc q => omega

end ToricPower
end
