module
public import graph_results.closed_graph_universal_resolution
public import graph_results.closed_graph_internal_grading
public import shared_results.part002
public import shared_results.part010

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphSpecializedResolution -/
section

/-!
# Polynomial free resolutions in every coefficient specialization

The chain group in degree p is the finitely supported polynomial module on
the same finite set of integral homology-basis indices for every coefficient
ring. Its differential is polynomial-linear; every matrix entry is the
coefficient specialization of the original entry. The target is the literal
specialized ideal power, through the separately proved ideal base-change
equivalence. Exactness is transported from the actual split augmented chain
complex, including for nonflat coefficient algebras.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CategoryTheory HomologicalComplex MvPolynomial
open PolynomialCoefficientBaseChange
open scoped TensorProduct
attribute [local instance] integralGraphFreeModel_scalarTower integralGraphModule_scalarTower
attribute [local instance 2000] LinearMap.IsScalarTower.compatibleSMul
attribute [local irreducible] integralGraphResolutionBasis integralGraphResolutionDegree
  integralGraphTransferredModel

section IdealRealization
variable {R₀ V₀ : Type*} [CommRing R₀]
  (A₀ : Type*) [CommRing A₀] [Algebra R₀ A₀]
  (I₀ : Ideal (MvPolynomial V₀ R₀)) (J₀ : Ideal (MvPolynomial V₀ A₀))
  (e : (A₀ ⊗[R₀] I₀) ≃ₗ[A₀] J₀)
  (he : ∀ (a : A₀) (f : I₀), (e (a ⊗ₜ[R₀] f)).val =
    a • MvPolynomial.map (algebraMap R₀ A₀) f.val)

/-- The coefficientwise ideal formula is sufficient to transport the
whole polynomial action, before a concrete ideal is substituted. -/
def idealCoefficientRealization :
    Realization (R := R₀) (V := V₀) A₀ I₀ J₀ where
  equivalence := e
  multiply p x := by
    induction x using TensorProduct.induction_on with
    | zero =>
        rw [LinearMap.map_zero, LinearEquiv.map_zero, smul_zero]
    | add x y hx hy =>
        rw [LinearMap.map_add, LinearEquiv.map_add, hx, hy,
          LinearEquiv.map_add, smul_add]
    | tmul a f =>
        apply Subtype.ext
        rw [LinearMap.baseChange_tmul, he]
        change a • MvPolynomial.map (algebraMap R₀ A₀) (p * f.val) =
          MvPolynomial.map (algebraMap R₀ A₀) p * (e (a ⊗ₜ[R₀] f)).val
        rw [he, map_mul, mul_smul_comm]

end IdealRealization

variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
  (s : ℕ) (hs : 0 < s)
  (A : Type*) [CommRing A] [Algebra GraphIntegralCoefficientRing A]

@[instance_reducible] def integralGraphResolutionTerm_addCommGroup (p : ℕ) :=
  Submodule.addCommGroup (R := GraphIntegralPolynomialRing N)
    (M := IntegralGraphFreeModel hG s) (IntegralGraphResolutionTerm hG s hs p)

@[instance_reducible] def integralGraphResolutionTerm_polynomialModule (p : ℕ) :=
  Submodule.module (R := GraphIntegralPolynomialRing N)
    (M := IntegralGraphFreeModel hG s) (IntegralGraphResolutionTerm hG s hs p)

@[instance_reducible] def integralGraphResolutionTerm_coefficientModule (p : ℕ) :=
  Submodule.module' (R := GraphIntegralPolynomialRing N) (S := GraphIntegralCoefficientRing)
    (M := IntegralGraphFreeModel hG s) (IntegralGraphResolutionTerm hG s hs p)

@[instance_reducible] def integralGraphResolutionTerm_scalarTower (p : ℕ) :=
  Submodule.isScalarTower (R := GraphIntegralPolynomialRing N) (S := GraphIntegralCoefficientRing)
    (M := IntegralGraphFreeModel hG s) (IntegralGraphResolutionTerm hG s hs p)

attribute [local instance] integralGraphResolutionTerm_addCommGroup
  integralGraphResolutionTerm_polynomialModule integralGraphResolutionTerm_coefficientModule
  integralGraphResolutionTerm_scalarTower

def integralGraphIdealRealization :
    Realization (R := GraphIntegralCoefficientRing) (V := GraphIntegralVariables N) A
      (IntegralGraphModule hG s) (IntegralGraphSpecializedModule (G := G) s A) :=
  idealCoefficientRealization (R₀ := GraphIntegralCoefficientRing)
    (V₀ := GraphIntegralVariables N) A (IntegralGraphModule hG s)
    (IntegralGraphSpecializedModule (G := G) s A)
    (integralGraphIdealBaseChangeEquiv hG s A)
    (integralGraphIdealBaseChangeEquiv_tmul_val hG s A)

abbrev IntegralGraphSpecializedFreeTerm (p : ℕ) :=
  IntegralGraphDegreeIndex hG s hs p →₀ MvPolynomial (GraphIntegralVariables N) A

def integralGraphTermRealization (p : ℕ) :=
  basisRealization (R := GraphIntegralCoefficientRing) (V := GraphIntegralVariables N)
    (F := IntegralGraphResolutionTerm hG s hs p) (I := IntegralGraphDegreeIndex hG s hs p)
    A (integralGraphResolutionTermBasis hG s hs p)

def integralGraphSpecializedFreeDifferential (p : ℕ) :
    IntegralGraphSpecializedFreeTerm hG s hs A (p+1) →ₗ[MvPolynomial (GraphIntegralVariables N) A]
      IntegralGraphSpecializedFreeTerm hG s hs A p :=
  Realization.transfer A (integralGraphTermRealization hG s hs A (p+1))
    (integralGraphTermRealization hG s hs A p) (integralGraphResolutionDifferential hG s hs p)

def integralGraphSpecializedFreeAugmentation :
    IntegralGraphSpecializedFreeTerm hG s hs A 0 →ₗ[MvPolynomial (GraphIntegralVariables N) A]
      IntegralGraphSpecializedModule (G := G) s A :=
  Realization.transfer A (integralGraphTermRealization hG s hs A 0)
    (integralGraphIdealRealization hG s A) (integralGraphResolutionAugmentation hG s hs)

theorem integralGraphSpecializedFreeDifferential_comp (p : ℕ) :
    (integralGraphSpecializedFreeDifferential hG s hs A p).comp
      (integralGraphSpecializedFreeDifferential hG s hs A (p+1)) = 0 := by
  unfold integralGraphSpecializedFreeDifferential
  rw [← Realization.transfer_comp]
  have he : (integralGraphResolutionDifferential hG s hs p).comp
      (integralGraphResolutionDifferential hG s hs (p+1)) = 0 :=
    (integralGraphResolutionData hG s hs).differential_comp p
  rw [he, Realization.transfer_zero]

theorem integralGraphSpecializedFreeAugmentation_comp :
    (integralGraphSpecializedFreeAugmentation hG s hs A).comp
      (integralGraphSpecializedFreeDifferential hG s hs A 0) = 0 := by
  unfold integralGraphSpecializedFreeAugmentation integralGraphSpecializedFreeDifferential
  rw [← Realization.transfer_comp]
  have he : (integralGraphResolutionAugmentation hG s hs).comp
      (integralGraphResolutionDifferential hG s hs 0) = 0 := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (integralGraphAugmentedContraction hG s hs).augmentation_boundary x
  rw [he, Realization.transfer_zero]

theorem integralGraphSpecializedFree_exact_positive (p : ℕ) :
    Function.Exact (integralGraphSpecializedFreeDifferential hG s hs A (p+1))
      (integralGraphSpecializedFreeDifferential hG s hs A p) :=
  Realization.transfer_exact A
    (integralGraphTermRealization hG s hs A (p+2))
    (integralGraphTermRealization hG s hs A (p+1))
    (integralGraphTermRealization hG s hs A p)
    (integralGraphResolutionDifferential hG s hs (p+1))
    (integralGraphResolutionDifferential hG s hs p)
    (((integralGraphAugmentedContraction hG s hs).baseChange A).exact_positive p)

theorem integralGraphSpecializedFree_exact_at_augmentation :
    Function.Exact (integralGraphSpecializedFreeDifferential hG s hs A 0)
      (integralGraphSpecializedFreeAugmentation hG s hs A) :=
  Realization.transfer_exact A
    (integralGraphTermRealization hG s hs A 1)
    (integralGraphTermRealization hG s hs A 0)
    (integralGraphIdealRealization hG s A)
    (integralGraphResolutionDifferential hG s hs 0)
    (integralGraphResolutionAugmentation hG s hs)
    (((integralGraphAugmentedContraction hG s hs).baseChange A).exact_augmentation)

theorem integralGraphSpecializedFree_augmentation_surjective :
    Function.Surjective (integralGraphSpecializedFreeAugmentation hG s hs A) :=
  Realization.transfer_surjective A
    (integralGraphTermRealization hG s hs A 0)
    (integralGraphIdealRealization hG s A)
    (integralGraphResolutionAugmentation hG s hs)
    (((integralGraphAugmentedContraction hG s hs).baseChange A).augmentation_surjective)

/-- An actual polynomial chain complex in the specialized ring. -/
def integralGraphSpecializedFreeComplex :
    ChainComplex (ModuleCat (MvPolynomial (GraphIntegralVariables N) A)) ℕ :=
  ChainComplex.of
    (fun p => ModuleCat.of (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p))
    (fun p => ModuleCat.ofHom (integralGraphSpecializedFreeDifferential hG s hs A p))
    (fun p => ModuleCat.hom_ext (integralGraphSpecializedFreeDifferential_comp hG s hs A p))

def integralGraphSpecializedFreeBasis (p : ℕ) :
    Module.Basis (IntegralGraphDegreeIndex hG s hs p) (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p) := Finsupp.basisSingleOne

theorem integralGraphSpecializedFreeTerm_free (p : ℕ) :
    Module.Free (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p) :=
  Module.Free.of_basis (integralGraphSpecializedFreeBasis hG s hs A p)

theorem integralGraphSpecializedFreeTerm_finite (p : ℕ) :
    Module.Finite (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p) := by
  letI := integralGraphResolutionIndex_finite hG s hs
  exact Module.Finite.of_basis (integralGraphSpecializedFreeBasis hG s hs A p)

theorem integralGraphSpecializedFreeTerm_zero_above (p : ℕ)
    (hp : Fintype.card (GraphIntegralVariables N) < p) :
    Subsingleton (IntegralGraphSpecializedFreeTerm hG s hs A p) := by
  have hi : IsEmpty (IntegralGraphDegreeIndex hG s hs p) := ⟨fun i => by
    have hle := integralGraphResolutionDegree_le hG s hs i.val
    rw [i.property] at hle
    exact Nat.not_lt_of_ge hle hp⟩
  letI := hi
  infer_instance

/-- The specialized differential has exactly the coefficientwise image of
the original integral matrix in the same basis-index sets. -/
theorem integralGraphSpecializedFree_matrix_entry (p : ℕ)
    (i : IntegralGraphDegreeIndex hG s hs (p+1))
    (j : IntegralGraphDegreeIndex hG s hs p) :
    (integralGraphSpecializedFreeDifferential hG s hs A p (Finsupp.single i 1)) j =
      MvPolynomial.map (algebraMap GraphIntegralCoefficientRing A)
        ((integralGraphResolutionTermBasis hG s hs p).repr
          (integralGraphResolutionDifferential hG s hs p
            (integralGraphResolutionTermBasis hG s hs (p+1) i)) j) :=
  basisRealization_transfer_entry (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N)
    (F := IntegralGraphResolutionTerm hG s hs (p+1))
    (G := IntegralGraphResolutionTerm hG s hs p)
    (I := IntegralGraphDegreeIndex hG s hs (p+1))
    (J := IntegralGraphDegreeIndex hG s hs p) A
    (integralGraphResolutionTermBasis hG s hs (p+1))
    (integralGraphResolutionTermBasis hG s hs p)
    (integralGraphResolutionDifferential hG s hs p) i j

theorem coefficientMap_idealOfVars {R B V : Type*} [CommRing R] [CommRing B]
    (φ : R →+* B) :
    (MvPolynomial.idealOfVars V R).map (MvPolynomial.map φ) = MvPolynomial.idealOfVars V B := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, MvPolynomial.map_X, MvPolynomial.idealOfVars]

theorem coefficientMap_mem_idealOfVars {R B V : Type*} [CommRing R] [CommRing B]
    (φ : R →+* B) {f : MvPolynomial V R} (hf : f ∈ MvPolynomial.idealOfVars V R) :
    MvPolynomial.map φ f ∈ MvPolynomial.idealOfVars V B := by
  rw [← coefficientMap_idealOfVars φ]
  exact Ideal.mem_map_of_mem _ hf

theorem integralGraphSpecializedFree_entries_in_variableIdeal (p : ℕ)
    (i : IntegralGraphDegreeIndex hG s hs (p+1))
    (j : IntegralGraphDegreeIndex hG s hs p) :
    (integralGraphSpecializedFreeDifferential hG s hs A p (Finsupp.single i 1)) j ∈
      MvPolynomial.idealOfVars (GraphIntegralVariables N) A := by
  have hm := coefficientMap_mem_idealOfVars (V := GraphIntegralVariables N)
    (algebraMap GraphIntegralCoefficientRing A)
    (integralGraphResolution_entries_in_variableIdeal hG s hs p i j)
  exact Eq.mpr (congrArg (fun f : MvPolynomial (GraphIntegralVariables N) A =>
    f ∈ MvPolynomial.idealOfVars (GraphIntegralVariables N) A)
      (integralGraphSpecializedFree_matrix_entry hG s hs A p i j)) hm

/-- After setting all polynomial variables to zero every differential
matrix entry is zero. Over a field this is the minimality criterion. -/
theorem integralGraphSpecializedFree_residue_entry_zero (p : ℕ)
    (i : IntegralGraphDegreeIndex hG s hs (p+1))
    (j : IntegralGraphDegreeIndex hG s hs p) :
    MvPolynomial.constantCoeff
      ((integralGraphSpecializedFreeDifferential hG s hs A p (Finsupp.single i 1)) j) = 0 := by
  have hk : MvPolynomial.idealOfVars (GraphIntegralVariables N) A ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (GraphIntegralVariables N) A →+* A) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact MvPolynomial.constantCoeff_X A v
  exact hk (integralGraphSpecializedFree_entries_in_variableIdeal hG s hs A p i j)

/-- The shift of each displayed free generator is independent of the
coefficient algebra and of the image chosen for the deformation parameter. -/
def integralGraphSpecializedFreeShift (p : ℕ) (i : IntegralGraphDegreeIndex hG s hs p) : ℕ :=
  integralGraphResolutionShift hG s hs i.val

theorem integralGraphSpecializedFree_matrix_degree (p : ℕ)
    (i : IntegralGraphDegreeIndex hG s hs (p+1))
    (j : IntegralGraphDegreeIndex hG s hs p)
    (a : GraphIntegralVariables N →₀ ℕ)
    (ha : ((integralGraphSpecializedFreeDifferential hG s hs A p
      (Finsupp.single i 1)) j).coeff a ≠ 0) :
    a.degree + integralGraphSpecializedFreeShift hG s hs p j =
      integralGraphSpecializedFreeShift hG s hs (p+1) i := by
  rw [integralGraphSpecializedFree_matrix_entry hG s hs A p i j,
    integralGraphResolution_matrix_entry hG s hs p i j,
    MvPolynomial.coeff_map] at ha
  apply integralGraphResolution_matrix_degree hG s hs i.val j.val a
  intro hz
  exact ha (by rw [hz, map_zero])

/-- The ordinary graded pieces are actual coefficient submodules of the
specialized free terms, with total degree polynomial degree plus shift. -/
def integralGraphSpecializedFreeOrdinaryPiece (p q : ℕ) :
    Submodule A (IntegralGraphSpecializedFreeTerm hG s hs A p) :=
  ShiftedPolynomialFree.piece (R := A) (V := GraphIntegralVariables N)
    (I := IntegralGraphDegreeIndex hG s hs p)
    (integralGraphSpecializedFreeShift hG s hs p) q

theorem integralGraphSpecializedFree_differential_preserves_ordinary (p q : ℕ)
    {x : IntegralGraphSpecializedFreeTerm hG s hs A (p+1)}
    (hx : x ∈ integralGraphSpecializedFreeOrdinaryPiece hG s hs A (p+1) q) :
    integralGraphSpecializedFreeDifferential hG s hs A p x ∈
      integralGraphSpecializedFreeOrdinaryPiece hG s hs A p q :=
  ShiftedPolynomialFree.map_piece (R := A) (V := GraphIntegralVariables N)
    (I := IntegralGraphDegreeIndex hG s hs (p+1))
    (J := IntegralGraphDegreeIndex hG s hs p)
    (integralGraphSpecializedFreeShift hG s hs (p+1))
    (integralGraphSpecializedFreeShift hG s hs p)
    (integralGraphSpecializedFreeDifferential hG s hs A p)
    (integralGraphSpecializedFree_matrix_degree hG s hs A p) q hx

set_option maxHeartbeats 1000000 in
theorem integralGraphSpecializedFreeAugmentation_single_val
    (i : IntegralGraphDegreeIndex hG s hs 0) :
    (integralGraphSpecializedFreeAugmentation hG s hs A (Finsupp.single i 1)).val =
      MvPolynomial.map (algebraMap GraphIntegralCoefficientRing A)
        (integralGraphAugmentation hG s hs (integralGraphResolutionBasis hG s hs i.val)).val := by
  rw [← basisCoordinates_one_tmul_basis (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N) (F := IntegralGraphResolutionTerm hG s hs 0)
    (I := IntegralGraphDegreeIndex hG s hs 0) A
    (integralGraphResolutionTermBasis hG s hs 0) i]
  change (Realization.transfer A (integralGraphTermRealization hG s hs A 0)
    (integralGraphIdealRealization hG s A) (integralGraphResolutionAugmentation hG s hs)
    ((integralGraphTermRealization hG s hs A 0).equivalence
      (1 ⊗ₜ[GraphIntegralCoefficientRing]
        integralGraphResolutionTermBasis hG s hs 0 i))).val = _
  rw [Realization.transfer_equivalence (R := GraphIntegralCoefficientRing)
    (V := GraphIntegralVariables N) A
    (integralGraphTermRealization hG s hs A 0) (integralGraphIdealRealization hG s A)
    (integralGraphResolutionAugmentation hG s hs)]
  change (integralGraphIdealBaseChangeEquiv hG s A
    (((integralGraphResolutionAugmentation hG s hs).restrictScalars GraphIntegralCoefficientRing).baseChange
      A (1 ⊗ₜ[GraphIntegralCoefficientRing]
        integralGraphResolutionTermBasis hG s hs 0 i))).val = _
  rw [LinearMap.baseChange_tmul (R := GraphIntegralCoefficientRing) (A := A)
    (M := IntegralGraphResolutionTerm hG s hs 0) (N := IntegralGraphModule hG s)
    ((integralGraphResolutionAugmentation hG s hs).restrictScalars GraphIntegralCoefficientRing)
    (1 : A) (integralGraphResolutionTermBasis hG s hs 0 i)]
  rw [integralGraphIdealBaseChangeEquiv_tmul_val hG s A]
  rw [one_smul]
  change MvPolynomial.map (algebraMap GraphIntegralCoefficientRing A)
    (integralGraphAugmentation hG s hs
      (ProjectedFreeResolution.pieceBasis (S := GraphIntegralPolynomialRing N)
        (F := IntegralGraphFreeModel hG s) (I := IntegralGraphResolutionIndex hG s hs)
        (integralGraphResolutionBasis hG s hs)
        (integralGraphResolutionDegree hG s hs) 0 i).val).val = _
  rw [ProjectedFreeResolution.pieceBasis_val (S := GraphIntegralPolynomialRing N)
    (F := IntegralGraphFreeModel hG s) (I := IntegralGraphResolutionIndex hG s hs)
    (integralGraphResolutionBasis hG s hs) (integralGraphResolutionDegree hG s hs) 0 i]

theorem integralGraphSpecializedFreeAugmentation_homogeneous
    (i : IntegralGraphDegreeIndex hG s hs 0) :
    IsWeightedHomogeneous (fun _ : GraphIntegralVariables N => (1 : ℕ))
      (integralGraphSpecializedFreeAugmentation hG s hs A (Finsupp.single i 1)).val
      (integralGraphSpecializedFreeShift hG s hs 0 i) := by
  rw [integralGraphSpecializedFreeAugmentation_single_val hG s hs A i]
  intro a ha
  rw [MvPolynomial.coeff_map] at ha
  apply integralGraphAugmentation_internal_basis hG s hs i.val
  intro hz
  exact ha (by rw [hz, map_zero])

theorem integralGraphSpecializedFree_augmentation_preserves_ordinary (q : ℕ)
    {x : IntegralGraphSpecializedFreeTerm hG s hs A 0}
    (hx : x ∈ integralGraphSpecializedFreeOrdinaryPiece hG s hs A 0 q) :
    IsWeightedHomogeneous (fun _ : GraphIntegralVariables N => (1 : ℕ))
      (integralGraphSpecializedFreeAugmentation hG s hs A x).val q :=
  ShiftedPolynomialFree.augmentation_piece (R := A) (V := GraphIntegralVariables N)
    (I := IntegralGraphDegreeIndex hG s hs 0)
    (integralGraphSpecializedFreeShift hG s hs 0)
    (IntegralGraphSpecializedModule (G := G) s A)
    (integralGraphSpecializedFreeAugmentation hG s hs A)
    (integralGraphSpecializedFreeAugmentation_homogeneous hG s hs A) q hx

/-- Every actual specialized differential becomes zero upon taking the
polynomial residue. For a field coefficient algebra, this is a minimal
graded free resolution, not merely a matrix with a selected vanishing entry. -/
theorem integralGraphSpecializedFree_residue_differential_zero (p : ℕ) :
    letI : Algebra (MvPolynomial (GraphIntegralVariables N) A) A :=
      (MvPolynomial.constantCoeff : MvPolynomial (GraphIntegralVariables N) A →+* A).toAlgebra
    (integralGraphSpecializedFreeDifferential hG s hs A p).baseChange A = 0 := by
  letI : Algebra (MvPolynomial (GraphIntegralVariables N) A) A :=
    (MvPolynomial.constantCoeff : MvPolynomial (GraphIntegralVariables N) A →+* A).toAlgebra
  apply basis_baseChange_zero_of_coefficients
    (S := MvPolynomial (GraphIntegralVariables N) A) (B := A)
    (F := IntegralGraphSpecializedFreeTerm hG s hs A (p+1))
    (G := IntegralGraphSpecializedFreeTerm hG s hs A p)
    (I := IntegralGraphDegreeIndex hG s hs (p+1))
    (J := IntegralGraphDegreeIndex hG s hs p)
    (integralGraphSpecializedFreeBasis hG s hs A (p+1))
    (integralGraphSpecializedFreeBasis hG s hs A p)
    (integralGraphSpecializedFreeDifferential hG s hs A p)
  intro i j
  change MvPolynomial.constantCoeff
    ((integralGraphSpecializedFreeDifferential hG s hs A p (Finsupp.single i 1)) j) = 0
  exact integralGraphSpecializedFree_residue_entry_zero hG s hs A p i j

theorem integralGraphSpecializedFree_finrank [Nontrivial A] (p : ℕ) :
    Module.finrank (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p) =
        Nat.card (IntegralGraphDegreeIndex hG s hs p) :=
  Module.finrank_eq_nat_card_basis (R := MvPolynomial (GraphIntegralVariables N) A)
    (M := IntegralGraphSpecializedFreeTerm hG s hs A p)
    (integralGraphSpecializedFreeBasis hG s hs A p)

/-- The specialized polynomial complex is finite free and exact, with the
actual specialized ideal power as its augmentation target. -/
theorem integralGraphSpecializedFree_resolution :
    (∀ p, Module.Free (MvPolynomial (GraphIntegralVariables N) A)
      (IntegralGraphSpecializedFreeTerm hG s hs A p) ∧
      Module.Finite (MvPolynomial (GraphIntegralVariables N) A)
        (IntegralGraphSpecializedFreeTerm hG s hs A p)) ∧
    (∀ p, Fintype.card (GraphIntegralVariables N) < p →
      Subsingleton (IntegralGraphSpecializedFreeTerm hG s hs A p)) ∧
    Function.Surjective (integralGraphSpecializedFreeAugmentation hG s hs A) ∧
    Function.Exact (integralGraphSpecializedFreeDifferential hG s hs A 0)
      (integralGraphSpecializedFreeAugmentation hG s hs A) ∧
    (∀ p, Function.Exact (integralGraphSpecializedFreeDifferential hG s hs A (p+1))
      (integralGraphSpecializedFreeDifferential hG s hs A p)) ∧
    (∀ p i j, (integralGraphSpecializedFreeDifferential hG s hs A p
      (Finsupp.single i 1)) j ∈ MvPolynomial.idealOfVars (GraphIntegralVariables N) A) :=
  ⟨fun p => ⟨integralGraphSpecializedFreeTerm_free hG s hs A p,
      integralGraphSpecializedFreeTerm_finite hG s hs A p⟩,
    integralGraphSpecializedFreeTerm_zero_above hG s hs A,
    integralGraphSpecializedFree_augmentation_surjective hG s hs A,
    integralGraphSpecializedFree_exact_at_augmentation hG s hs A,
    integralGraphSpecializedFree_exact_positive hG s hs A,
    integralGraphSpecializedFree_entries_in_variableIdeal hG s hs A⟩

end FourPapers.Sublattice

end
end
end


end
