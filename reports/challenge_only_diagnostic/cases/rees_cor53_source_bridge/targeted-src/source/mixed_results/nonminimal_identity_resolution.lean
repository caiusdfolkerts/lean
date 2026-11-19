module
public import shared_results.part003
public import mixed_results.part001
public import graph_foundation.part004
public import Mathlib.Tactic.FinCases

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.NonminimalIdentityResolution -/
section

/-!
# Identity substitution does not minimize an arbitrary free resolution

The singleton one-row sublattice has ideal `(x)`. We construct an actual
free resolution with a contractible summand, giving a differential entry `1`.
Identity substitution satisfies the positive homogeneous regular-sequence
hypotheses and leaves that entry equal to `1`. Thus minimality of the source
resolution is necessary in the universal base-change statement.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice.NonminimalIdentityResolution
open Classical CategoryTheory CommAlg MvPolynomial
open HomologicalPerturbation
open scoped TensorProduct

abbrev widths : Fin 1 → ℕ := fun _ => 1
abbrev Variable := FiniteVariable.{0} widths
abbrev Ring := MvPolynomial Variable ℚ
abbrev Total := Fin 3 →₀ Ring

def coordinate : Variable := ⟨0, ULift.up 0⟩
def tuple : FiniteTuple widths := fun _ => 0
def lattice : Finset (FiniteTuple widths) := {tuple}
def ideal : Ideal Ring := Ideal.span {X coordinate}

theorem lattice_nonempty : lattice.Nonempty := ⟨tuple, by simp [lattice]⟩
theorem lattice_closed : finiteLatticeClosed widths lattice := by
  simp [finiteLatticeClosed, lattice]

theorem ideal_eq_sublattice : ideal = finiteSublatticeIdeal widths (k := ℚ) lattice := by
  simp [ideal, finiteSublatticeIdeal, lattice, finiteRowMonomial, tuple, coordinate]

def basis : Module.Basis (Fin 3) Ring Total := Finsupp.basisSingleOne

def degree (i : Fin 3) : ℕ := if i = 2 then 1 else 0

/-- All three generators carry the same internal shift. Thus the extra
contractible summand lies in the category of graded free resolutions. -/
def internalDegree (_i : Fin 3) : ℕ := 1

def differential : Module.End Ring Total :=
  (Finsupp.lsingle 1).comp (Finsupp.lapply 2)
def augmentation : Total →ₗ[Ring] Ring := Finsupp.lapply 0
def inclusion : Ring →ₗ[Ring] Total := Finsupp.lsingle 0
def homotopy : Module.End Ring Total :=
  (Finsupp.lsingle 2).comp (Finsupp.lapply 1)

@[simp] theorem differential_basis (i : Fin 3) :
    differential (basis i) = if i = 2 then basis 1 else 0 := by
  fin_cases i <;> simp [differential, basis, Finsupp.coe_basisSingleOne]

/-- Every matrix entry has the degree prescribed by the internal shifts. -/
theorem differential_entry_homogeneous (i j : Fin 3) :
    (basis.repr (differential (basis i)) j).IsHomogeneous
      (internalDegree i - internalDegree j) := by
  fin_cases i <;> fin_cases j <;>
    simp [internalDegree, differential_basis, Module.Basis.repr_self,
      MvPolynomial.isHomogeneous_one, MvPolynomial.isHomogeneous_zero]

/-- The contractible summand is explicit: `d(e₂)=e₁`, `h(e₁)=e₂`. -/
def contraction : LinearDeformationRetract (R := Ring) (M := Total) (H := Ring) where
  sourceD := differential
  targetD := 0
  inclusion := inclusion
  projection := augmentation
  homotopy := homotopy
  source_square := by
    apply LinearMap.ext
    intro x
    ext i
    fin_cases i <;> simp [Module.End.mul_apply, differential]
  target_square := by simp
  inclusion_chain := by
    apply LinearMap.ext
    intro x
    ext i
    fin_cases i <;> simp [differential, inclusion]
  projection_chain := by
    apply LinearMap.ext
    intro x
    simp [differential, augmentation]
  retract := by
    apply LinearMap.ext
    intro x
    simp [augmentation, inclusion]
  deformation := by
    apply LinearMap.ext
    intro x
    ext i
    fin_cases i <;> simp [Module.End.mul_apply, differential, homotopy,
      inclusion, augmentation]

theorem differential_lowers (p : ℕ) :
    differential.comp (Grading.projection basis degree (p+1)) =
      (Grading.projection basis degree p).comp differential := by
  apply homogeneous_projection_lowering (R := Ring) basis degree differential
  · intro i
    fin_cases i
    · simpa [differential_basis, degree] using
        (Submodule.zero_mem (Grading.Piece basis degree 0))
    · simpa [differential_basis, degree] using
        (Submodule.zero_mem (Grading.Piece basis degree 0))
    · simpa [differential_basis, degree] using
        Grading.basis_mem_piece basis degree (1 : Fin 3)
  · intro i hi
    rw [differential_basis, if_neg]
    intro h
    subst i
    simp [degree] at hi

theorem differential_zero : differential.comp (Grading.projection basis degree 0) = 0 := by
  apply basis.ext
  intro i
  fin_cases i <;> simp [LinearMap.comp_apply, Grading.projection_basis,
    degree, differential_basis]

theorem augmentation_zero : augmentation.comp (Grading.projection basis degree 0) = augmentation := by
  apply basis.ext
  intro i
  simp only [LinearMap.comp_apply, Grading.projection_basis]
  fin_cases i <;> simp [degree, augmentation, basis, Finsupp.coe_basisSingleOne]

/-- A genuine finite free resolution with an extra contractible summand. -/
def freeRingResolution : ProjectiveResolution (ModuleCat.of Ring Ring) :=
  ProjectedFreeResolution.resolution (R := Ring) basis degree differential augmentation
    contraction rfl rfl rfl differential_lowers differential_zero augmentation_zero

def principalEquiv : Ring ≃ₗ[Ring] ideal :=
  LinearEquiv.toSpanNonzeroSingleton Ring Ring (X coordinate) (MvPolynomial.X_ne_zero coordinate)

/-- The displayed augmentation sends every generator to a degree-one
polynomial, with zero allowed as usual for a homogeneous map. -/
theorem augmentation_basis_homogeneous (i : Fin 3) :
    ((principalEquiv (augmentation (basis i)) : ideal) : Ring).IsHomogeneous
      (internalDegree i) := by
  change (augmentation (basis i) * X coordinate).IsHomogeneous 1
  fin_cases i <;>
    simp [augmentation, basis, Finsupp.coe_basisSingleOne,
      MvPolynomial.isHomogeneous_X, MvPolynomial.isHomogeneous_zero]

/-- The same actual complex resolves the literal singleton sublattice ideal. -/
def resolution : ProjectiveResolution (ModuleCat.of Ring ideal) where
  complex := freeRingResolution.complex
  projective := freeRingResolution.projective
  π := freeRingResolution.π ≫ (ChainComplex.single₀ (ModuleCat Ring)).map principalEquiv.toModuleIso.hom
  quasiIso := by infer_instance

def resolutionBasis (p : ℕ) :
    Module.Basis {i : Fin 3 // degree i = p} Ring (resolution.complex.X p) :=
  ProjectedFreeResolution.pieceBasis basis degree p

instance resolution_free (p : ℕ) : Module.Free Ring (resolution.complex.X p) :=
  Module.Free.of_basis (resolutionBasis p)
instance resolution_finite (p : ℕ) : Module.Finite Ring (resolution.complex.X p) :=
  Module.Finite.of_basis (resolutionBasis p)

/-- All terms above homological degree one are zero. -/
theorem resolution_bounded (p : ℕ) (hp : 1 < p) : Subsingleton (resolution.complex.X p) := by
  change Subsingleton (ProjectedFreeResolution.piece basis degree p)
  apply ProjectedFreeResolution.piece_zero_above basis degree 1 _ p hp
  intro i
  dsimp [degree]
  split_ifs <;> omega

def sourceGenerator : {i : Fin 3 // degree i = 1} := ⟨2, by simp [degree]⟩
def targetGenerator : {i : Fin 3 // degree i = 0} := ⟨1, by simp [degree]⟩

theorem actual_entry :
    (resolutionBasis 0).repr
      (resolution.complex.d 1 0 (resolutionBasis 1 sourceGenerator)) targetGenerator = 1 := by
  change (ProjectedFreeResolution.pieceBasis basis degree 0).repr
    ((ProjectedFreeResolution.data basis degree differential contraction rfl differential_lowers).complex.d 1 0
      (ProjectedFreeResolution.pieceBasis basis degree 1 sourceGenerator)) targetGenerator = 1
  rw [SubmoduleComplexData.complex_d, ProjectedFreeResolution.pieceBasis_repr]
  change basis.repr (differential ((ProjectedFreeResolution.pieceBasis basis degree 1
    sourceGenerator).val)) targetGenerator.val = 1
  rw [ProjectedFreeResolution.pieceBasis_val, differential_basis]
  simp [sourceGenerator, targetGenerator, Module.Basis.repr_self]

/-- These are the entries of the actual projective-resolution differential,
so the equal internal shifts genuinely grade the constructed complex. -/
theorem actual_entry_homogeneous (p : ℕ)
    (i : {i : Fin 3 // degree i = p+1}) (j : {i : Fin 3 // degree i = p}) :
    ((resolutionBasis p).repr
      (resolution.complex.d (p+1) p (resolutionBasis (p+1) i)) j).IsHomogeneous
        (internalDegree i.val - internalDegree j.val) := by
  change ((ProjectedFreeResolution.pieceBasis basis degree p).repr
    ((ProjectedFreeResolution.data basis degree differential contraction rfl differential_lowers).complex.d
      (p+1) p (ProjectedFreeResolution.pieceBasis basis degree (p+1) i)) j).IsHomogeneous _
  rw [SubmoduleComplexData.complex_d, ProjectedFreeResolution.pieceBasis_repr]
  change (basis.repr (differential ((ProjectedFreeResolution.pieceBasis basis degree (p+1) i).val))
    j.val).IsHomogeneous _
  rw [ProjectedFreeResolution.pieceBasis_val]
  exact differential_entry_homogeneous i.val j.val

/-- The actual augmented complex has the same internal grading. -/
theorem actual_augmentation_homogeneous (i : {i : Fin 3 // degree i = 0}) :
    (resolution.π.f 0 (resolutionBasis 0 i)).val.IsHomogeneous (internalDegree i.val) := by
  change (principalEquiv (freeRingResolution.π.f 0 (resolutionBasis 0 i))).val.IsHomogeneous _
  unfold freeRingResolution
  rw [ProjectedFreeResolution.resolution_π_f_zero]
  change (principalEquiv (augmentation
    ((ProjectedFreeResolution.pieceBasis basis degree 0 i).val))).val.IsHomogeneous _
  rw [ProjectedFreeResolution.pieceBasis_val]
  exact augmentation_basis_homogeneous i.val

theorem actual_entry_nonminimal :
    (resolutionBasis 0).repr
      (resolution.complex.d 1 0 (resolutionBasis 1 sourceGenerator)) targetGenerator ∉
        MvPolynomial.idealOfVars Variable ℚ := by
  rw [actual_entry, ← CommAlg.Koszul.ker_constantCoeff, RingHom.mem_ker]
  simp

/-- The identity family is a positive homogeneous regular sequence. -/
theorem identity_regular : RegularFamilyKoszul.IsRegularFamily (X : Variable → Ring) := by
  have h := DisjointMonomialRegularity.disjoint_monomials_regular
    (K := ℚ) (fun v : Variable => Finsupp.single v 1)
    (fun v => by simp) (by
      intro v w hvw
      simpa only [Finsupp.support_single_ne_zero _ (show (1 : ℕ) ≠ 0 by decide),
        Finset.disjoint_singleton] using hvw)
  exact h

theorem identity_homogeneous (v : Variable) : (X v : Ring).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_X ℚ v

theorem substitution_identity :
    (MvPolynomial.aeval (X : Variable → Ring) : Ring →ₐ[ℚ] Ring) = AlgHom.id ℚ Ring :=
  MvPolynomial.aeval_X_left

theorem ideal_map_identity :
    ideal.map (MvPolynomial.aeval (X : Variable → Ring)).toRingHom = ideal := by
  rw [MvPolynomial.aeval_X_left]
  exact ideal.map_id

/-- This is the actual scalar-extended resolution of the literal extended ideal. -/
def identityResolution :=
  PolynomialRegularSubstitution.idealResolution (X : Variable → Ring) (fun _ => 1)
    identity_homogeneous identity_regular (fun _ => by decide) (fun _ => rfl)
    ideal resolution

def identityResolutionBasis (p : ℕ) :
    Module.Basis {i : Fin 3 // degree i = p} Ring (identityResolution.complex.X p) :=
  PolynomialRegularSubstitution.baseChangedResolutionBasis (X : Variable → Ring) (fun _ => 1)
    identity_homogeneous identity_regular (fun _ => by decide) (fun _ => rfl)
    resolution resolutionBasis p

instance identityResolution_free (p : ℕ) : Module.Free Ring (identityResolution.complex.X p) :=
  Module.Free.of_basis (identityResolutionBasis p)
instance identityResolution_finite (p : ℕ) : Module.Finite Ring (identityResolution.complex.X p) :=
  Module.Finite.of_basis (identityResolutionBasis p)

/-- Scalar extension by identity does not remove the actual unit entry. -/
theorem identity_baseChange_entry :
    ((resolutionBasis 0).baseChange Ring).repr
      ((resolution.complex.d 1 0).hom.baseChange Ring
        (((resolutionBasis 1).baseChange Ring) sourceGenerator)) targetGenerator = 1 := by
  rw [PolynomialRegularSubstitution.baseChange_entry (X : Variable → Ring)
    (fun _ => rfl), actual_entry, map_one]

theorem identity_baseChange_nonminimal :
    ((resolutionBasis 0).baseChange Ring).repr
      ((resolution.complex.d 1 0).hom.baseChange Ring
        (((resolutionBasis 1).baseChange Ring) sourceGenerator)) targetGenerator ∉
          MvPolynomial.idealOfVars Variable ℚ := by
  rw [identity_baseChange_entry, ← CommAlg.Koszul.ker_constantCoeff, RingHom.mem_ker]
  simp

/-- The actual resulting free resolution is nonminimal, witnessed by a unit entry. -/
theorem identity_resolution_nonminimal :
    (identityResolutionBasis 0).repr
      (identityResolution.complex.d 1 0
        (identityResolutionBasis 1 sourceGenerator)) targetGenerator ∉
          MvPolynomial.idealOfVars Variable ℚ := by
  exact identity_baseChange_nonminimal

end FourPapers.Sublattice.NonminimalIdentityResolution

end
end
end

end
