module
public import graph_foundation.part012
public import shared_results.part013

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialFineCoordinates -/
section

/-!
# Literal polynomial Koszul coordinates for the integral contraction

The map sends `X^a ⊗ e_F` to the exterior vector `e_F` in fine degree
`a + 1_F`. Its inverse restores the actual polynomial monomial
`X^(α - 1_F)`. The formula is a bijection of bases, and it intertwines the
ordinary variable-multiplication Koszul differential with the normalized
fine-strand boundary.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.PolynomialFineContraction

open Classical DirectSum CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Sublattice
open scoped TensorProduct

universe u
variable {R V : Type u} [CommRing R] [Fintype V] [LinearOrder V]

abbrev PolynomialKoszulTotal := MvPolynomial V R ⊗[R] Simplicial.Ambient V R

abbrev TensorIndex := Exponent V × Finset V
abbrev FineIndex := Σ α : Exponent V, {F : Finset V // fullKoszulFaces α F}

def indexEquiv : TensorIndex (V := V) ≃ FineIndex (V := V) where
  toFun a := ⟨a.1 + faceExponent a.2,
    ⟨a.2, le_add_of_nonneg_left zero_le⟩⟩
  invFun a := (a.1 - faceExponent a.2.val, a.2.val)
  left_inv a := by
    apply Prod.ext
    · exact add_tsub_cancel_right _ _
    · rfl
  right_inv a := by
    rcases a with ⟨α, F, hF⟩
    have h : α - faceExponent F + faceExponent F = α := tsub_add_cancel_of_le hF
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun G => by
      change fullKoszulFaces (α - faceExponent F + faceExponent F) G ↔
        fullKoszulFaces α G
      rw [h])).mpr rfl

def tensorBasis : Module.Basis (TensorIndex (V := V)) R
    (PolynomialKoszulTotal (R := R) (V := V)) :=
  (MvPolynomial.basisMonomials V R).tensorProduct (Simplicial.basis (V := V) (k := R))

def fineBasis : Module.Basis (FineIndex (V := V)) R (FineTotal (R := R) (V := V)) :=
  DFinsupp.basis (fun α => totalFaceBasis (k := R) (fullKoszulFaces α))

@[simp] lemma tensorBasis_apply (a : Exponent V) (F : Finset V) :
    tensorBasis (R := R) (a,F) = monomial a 1 ⊗ₜ[R] Simplicial.basis F := by
  simp only [tensorBasis, Module.Basis.tensorProduct_apply,
    MvPolynomial.coe_basisMonomials]

@[simp] lemma fineBasis_apply (α : Exponent V)
    (F : {F : Finset V // fullKoszulFaces α F}) :
    fineBasis (R := R) ⟨α,F⟩ = DirectSum.lof R (Exponent V)
      (fun α => ↥(FullFaceModule (k := R) α)) α (totalFaceBasis (k := R) (fullKoszulFaces α) F) := by
  apply (fineBasis (R := R) (V := V)).repr.injective
  ext a
  rcases a with ⟨β,G⟩
  rw [Module.Basis.repr_self]
  change (Finsupp.single (⟨α,F⟩ : FineIndex (V := V)) (1 : R)) ⟨β,G⟩ =
    (totalFaceBasis (k := R) (fullKoszulFaces β)).repr
      ((DFinsupp.single α (totalFaceBasis (k := R) (fullKoszulFaces α) F) :
        FineTotal (R := R) (V := V)) β) G
  by_cases h : α = β
  · subst β
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hh : (⟨α,F⟩ : FineIndex (V := V)) ≠ ⟨β,G⟩ :=
      fun he => h (congrArg Sigma.fst he)
    simp [h, hh]

def coordinates : PolynomialKoszulTotal (R := R) (V := V) ≃ₗ[R]
    FineTotal (R := R) (V := V) :=
  tensorBasis.equiv fineBasis indexEquiv

lemma coordinates_basis (a : Exponent V) (F : Finset V) :
    coordinates (R := R) (monomial a 1 ⊗ₜ[R] Simplicial.basis F) =
      fineBasis (indexEquiv (a,F)) := by
  rw [← tensorBasis_apply]
  exact Module.Basis.equiv_apply tensorBasis (a,F) fineBasis indexEquiv

lemma coordinates_basis_coefficient (a β : Exponent V) (F : Finset V) :
    ((coordinates (R := R) (monomial a 1 ⊗ₜ[R] Simplicial.basis F)) β).val =
      if a + faceExponent F = β then Simplicial.basis F else 0 := by
  rw [coordinates_basis]
  have hF : fullKoszulFaces (a + faceExponent F) F :=
    le_add_of_nonneg_left zero_le
  change (fineBasis (R := R)
    ⟨a + faceExponent F, ⟨F, hF⟩⟩ β).val = _
  rw [fineBasis_apply, DirectSum.lof_eq_of]
  by_cases h : a + faceExponent F = β
  · subst β
    rw [if_pos rfl, DirectSum.of_eq_same, totalFaceBasis_val]
  · rw [if_neg h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    rfl

lemma coordinates_contraction_coefficient (a β : Exponent V) (F : Finset V) (v : V) :
    ((coordinates (R := R)
      ((X v * monomial a 1) ⊗ₜ[R] Simplicial.contraction v (Simplicial.basis F))) β).val =
        if a + faceExponent F = β then
          Simplicial.contraction v (Simplicial.basis F) else 0 := by
  rw [Simplicial.contraction_basis]
  by_cases hv : v ∈ F
  · rw [if_pos hv, TensorProduct.tmul_smul]
    have hp : (X v * monomial a (1 : R)) = monomial (a + Finsupp.single v 1) 1 := by
      simp only [X, monomial_mul_monomial, one_mul, add_comm]
    rw [hp]
    erw [LinearMapClass.map_smul_of_tower (S := R)]
    change (TauCeti.ExteriorAlgebra.basisEraseSign v F) •
      ((coordinates (R := R)
        (monomial (a + Finsupp.single v 1) 1 ⊗ₜ[R]
          Simplicial.basis (F.erase v))) β).val = _
    rw [coordinates_basis_coefficient]
    have he : (a + Finsupp.single v 1) + faceExponent (F.erase v) =
        a + faceExponent F := by
      rw [add_assoc, add_comm (Finsupp.single v 1), faceExponent_erase_add hv]
    rw [he]
    split_ifs <;> simp only [smul_zero]
  · rw [if_neg hv, TensorProduct.tmul_zero, map_zero]
    split_ifs <;> rfl

@[simp] lemma differential_coefficient (x : FineTotal (R := R) (V := V))
    (α : Exponent V) :
    (differential x α).val = Simplicial.boundary (x α).val := rfl

/-- The coordinate differential is exactly the usual polynomial Koszul
differential. The normalized boundary is not an alternate definition of Tor. -/
theorem coordinates_differential (x : PolynomialKoszulTotal (R := R) (V := V)) :
    coordinates (TensorExteriorKoszul.differential
      (K := R) (M := MvPolynomial V R) (X : V → MvPolynomial V R) x) =
        differential (coordinates x) := by
  have he : coordinates.toLinearMap.comp
      (TensorExteriorKoszul.differential (K := R) (M := MvPolynomial V R)
        (X : V → MvPolynomial V R)) = differential.comp coordinates.toLinearMap := by
    apply (tensorBasis (R := R) (V := V)).ext
    rintro ⟨a,F⟩
    rw [tensorBasis_apply]
    apply DFinsupp.ext
    intro β
    apply Subtype.ext
    change ((coordinates (TensorExteriorKoszul.differential
      (K := R) (M := MvPolynomial V R) (X : V → MvPolynomial V R)
      (monomial a 1 ⊗ₜ[R] Simplicial.basis F))) β).val =
      (differential (coordinates (monomial a 1 ⊗ₜ[R] Simplicial.basis F)) β).val
    rw [TensorExteriorKoszul.differential_tmul, map_sum]
    simp only [smul_eq_mul, differential_coefficient, coordinates_basis_coefficient]
    have hs (g : V → FineTotal (R := R) (V := V)) :
        ((∑ v, g v) β).val = ∑ v, (g v β).val := by
      change ((FullFaceModule (k := R) β).subtype.comp
        (DirectSum.component R (Exponent V)
          (fun α => ↥(FullFaceModule (k := R) α)) β)) (∑ v, g v) = _
      exact map_sum _ g Finset.univ
    rw [hs]
    change (∑ v : V, ((coordinates (R := R)
      ((X v * monomial a 1) ⊗ₜ[R]
        Simplicial.contraction v (Simplicial.basis F))) β).val) =
      Simplicial.boundary
        (if a + faceExponent F = β then Simplicial.basis F else 0)
    calc
      _ = ∑ v : V, if a + faceExponent F = β then
          Simplicial.contraction v (Simplicial.basis F) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        exact coordinates_contraction_coefficient a β F v
      _ = _ := by
        by_cases h : a + faceExponent F = β
        · simp only [h, if_true, Simplicial.boundary_eq_sum]
        · simp only [h, if_false, map_zero, Finset.sum_const_zero]
  exact LinearMap.congr_fun he x

/-- An actual strong contraction of the literal polynomial tensor Koszul
complex onto the coefficient ring. -/
def polynomialContraction : HomologicalPerturbation.LinearContraction
    (R := R) (M := PolynomialKoszulTotal (R := R) (V := V)) (H := R) :=
  (contraction (R := R) (V := V)).changeSource coordinates.symm

theorem polynomialContraction_d :
    (polynomialContraction (R := R) (V := V)).d =
      TensorExteriorKoszul.differential (K := R) (M := MvPolynomial V R)
        (X : V → MvPolynomial V R) := by
  apply LinearMap.ext
  intro x
  apply (coordinates (R := R) (V := V)).injective
  change coordinates (coordinates.symm (differential (coordinates x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (coordinates_differential x).symm

lemma projection_fineBasis (α : Exponent V)
    (F : {F : Finset V // fullKoszulFaces α F}) :
    projection (fineBasis (R := R) ⟨α,F⟩) = if α = 0 then 1 else 0 := by
  rw [fineBasis_apply]
  by_cases hα : α = 0
  · subst α
    rw [if_pos rfl, projection_lof_zero]
    simp only [zeroFaceEquiv, Module.Basis.equiv_apply, Module.Basis.singleton_apply]
  · rw [if_neg hα, projection_lof_ne α hα]

theorem polynomialContraction_projection_monomial (a : Exponent V) (F : Finset V) :
    (polynomialContraction (R := R) (V := V)).projection
      (monomial a 1 ⊗ₜ[R] Simplicial.basis F) =
        if F = ∅ then (if a = 0 then 1 else 0) else 0 := by
  change projection (coordinates (monomial a 1 ⊗ₜ[R] Simplicial.basis F)) = _
  rw [coordinates_basis, projection_fineBasis]
  change (if a + faceExponent F = 0 then (1 : R) else 0) = _
  by_cases hF : F = ∅
  · subst F
    simp only [faceExponent_empty, add_zero, if_pos rfl, if_true]
  · have he : a + faceExponent F ≠ 0 := by
      intro h
      have hf : fullKoszulFaces (0 : Exponent V) F := by
        rw [← h]
        exact le_add_of_nonneg_left zero_le
      exact hF (zero_face_eq_empty F hf)
    rw [if_neg he, if_neg hF]

/-- The projection is exactly the constant polynomial coefficient in
exterior degree zero. In particular it vanishes in every positive degree. -/
theorem polynomialContraction_projection_tmul_basis
    (f : MvPolynomial V R) (F : Finset V) :
    (polynomialContraction (R := R) (V := V)).projection
      (f ⊗ₜ[R] Simplicial.basis F) = if F = ∅ then constantCoeff f else 0 := by
  let L := (polynomialContraction (R := R) (V := V)).projection.comp
    ((TensorProduct.mk R (MvPolynomial V R) (Simplicial.Ambient V R)).flip
      (Simplicial.basis F))
  have he : L = if F = ∅ then MvPolynomial.lcoeff (R := R) (0 : Exponent V) else 0 := by
    apply (MvPolynomial.basisMonomials V R).ext
    intro a
    change (polynomialContraction (R := R) (V := V)).projection
      (monomial a 1 ⊗ₜ[R] Simplicial.basis F) = _
    rw [polynomialContraction_projection_monomial]
    by_cases hF : F = ∅
    · rw [if_pos hF, if_pos hF]
      change (if a = 0 then (1 : R) else 0) = (monomial a 1).coeff 0
      simp only [coeff_monomial, eq_comm]
    · rw [if_neg hF, if_neg hF]
      rfl
  have hf : (polynomialContraction (R := R) (V := V)).projection
      (f ⊗ₜ[R] Simplicial.basis F) =
        (if F = ∅ then MvPolynomial.lcoeff (R := R) (0 : Exponent V) else 0) f :=
    LinearMap.congr_fun he f
  have h_eval :
      (if F = ∅ then MvPolynomial.lcoeff (R := R) (0 : Exponent V) else 0) f =
        if F = ∅ then constantCoeff f else 0 := by
    split_ifs <;> rfl
  exact hf.trans h_eval

end FourPapers.PolynomialFineContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialDiagonalContraction -/
section

/-!
# A split polynomial diagonal complex over an arbitrary coefficient ring

Translation conjugates the explicit polynomial Koszul contraction to the
Koszul complex on `X i - C (a i)`. Tensoring this contraction with any module
over the coefficient ring retains every identity. No flatness hypothesis is
used. With the coefficient ring itself polynomial, this is the diagonal
resolution used in the integral minimal-resolution construction.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.PolynomialDiagonalContraction

open MvPolynomial CommAlg
open scoped TensorProduct
open HomologicalPerturbation PolynomialFineContraction

universe u
variable {R V : Type u} [CommRing R] [Fintype V] [LinearOrder V]

abbrev Total := PolynomialKoszulTotal (R := R) (V := V)

def translate (a : V → R) :
    Total (R := R) (V := V) ≃ₗ[R] Total (R := R) (V := V) :=
  (PolynomialDiagonalResolution.translation a).symm.toLinearEquiv.rTensor
    (Simplicial.Ambient V R)

@[simp] theorem translate_tmul (a : V → R) (f : MvPolynomial V R)
    (z : Simplicial.Ambient V R) :
    translate a (f ⊗ₜ[R] z) =
      (PolynomialDiagonalResolution.translation a).symm f ⊗ₜ[R] z := rfl

@[simp] theorem translate_symm_tmul (a : V → R) (f : MvPolynomial V R)
    (z : Simplicial.Ambient V R) :
    (translate a).symm (f ⊗ₜ[R] z) =
      PolynomialDiagonalResolution.translation a f ⊗ₜ[R] z := rfl

/-- The differential on the actual displayed diagonal sequence. -/
def differential (a : V → R) : Module.End R (Total (R := R) (V := V)) :=
  TensorExteriorKoszul.differential (K := R) (M := MvPolynomial V R)
    (fun v => X v - C (a v))

theorem translate_differential (a : V → R) (x : Total (R := R) (V := V)) :
    translate a ((polynomialContraction (R := R) (V := V)).d
      ((translate a).symm x)) = differential a x := by
  have he : (translate a).toLinearMap.comp
      ((polynomialContraction (R := R) (V := V)).d.comp
        (translate a).symm.toLinearMap) = differential a := by
    apply TensorProduct.ext'
    intro f z
    change translate a ((polynomialContraction (R := R) (V := V)).d
      ((translate a).symm (f ⊗ₜ[R] z))) = differential a (f ⊗ₜ[R] z)
    rw [translate_symm_tmul, polynomialContraction_d,
      TensorExteriorKoszul.differential_tmul, map_sum]
    change (∑ v : V, translate a
      ((X v * PolynomialDiagonalResolution.translation a f) ⊗ₜ[R]
        Simplicial.contraction v z)) = _
    rw [differential, TensorExteriorKoszul.differential_tmul]
    apply Finset.sum_congr rfl
    intro v _
    rw [translate_tmul, map_mul,
      PolynomialDiagonalResolution.translation_symm_X,
      AlgEquiv.symm_apply_apply]
    rfl
  exact LinearMap.congr_fun he x

/-- The genuine diagonal Koszul complex contracts to the coefficient ring. -/
def contraction (a : V → R) :
    LinearContraction (R := R) (M := Total (R := R) (V := V)) (H := R) :=
  (polynomialContraction (R := R) (V := V)).changeSource (translate a)

@[simp] theorem contraction_d (a : V → R) :
    (contraction a).d = differential a := by
  apply LinearMap.ext
  intro x
  exact translate_differential a x

theorem differential_square (a : V → R) :
    differential a * differential a = 0 := by
  rw [← contraction_d a]
  exact (contraction a).differential

theorem contraction_projection_tmul_basis (a : V → R)
    (f : MvPolynomial V R) (F : Finset V) :
    (contraction a).projection (f ⊗ₜ[R] Simplicial.basis F) =
      if F = ∅ then aeval a f else 0 := by
  change (polynomialContraction (R := R) (V := V)).projection
    ((translate a).symm (f ⊗ₜ[R] Simplicial.basis F)) = _
  rw [translate_symm_tmul, polynomialContraction_projection_tmul_basis,
    PolynomialDiagonalResolution.constantCoeff_translation]

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- An actual split diagonal resolution after tensoring with an arbitrary
coefficient module. The target is the original module, through the tensor
unitor, not a new module postulated to be its homology. -/
def moduleContraction (a : V → R) :
    LinearContraction (R := R) (M := Total (R := R) (V := V) ⊗[R] M) (H := M) :=
  ((contraction a).tensorRight M).changeTarget (TensorProduct.lid R M)

@[simp] theorem moduleContraction_d_tmul (a : V → R)
    (x : Total (R := R) (V := V)) (m : M) :
    (moduleContraction M a).d (x ⊗ₜ[R] m) = differential a x ⊗ₜ[R] m := by
  change (contraction a).d x ⊗ₜ[R] m = _
  rw [contraction_d]

/-- Every cycle in the augmentation kernel has a specified preimage. This
is the exactness statement retained by every coefficient specialization. -/
theorem module_cycle_boundary (a : V → R)
    (x : Total (R := R) (V := V) ⊗[R] M)
    (hx : (moduleContraction M a).d x = 0)
    (hε : (moduleContraction M a).projection x = 0) :
    (moduleContraction M a).d ((moduleContraction M a).h x) = x := by
  have he := LinearMap.congr_fun (moduleContraction M a).homotopy x
  change (moduleContraction M a).d ((moduleContraction M a).h x) +
    (moduleContraction M a).h ((moduleContraction M a).d x) =
      x - (moduleContraction M a).inclusion
        ((moduleContraction M a).projection x) at he
  rw [hx, hε, map_zero, map_zero, add_zero] at he
  exact he.trans (sub_zero x)

end FourPapers.PolynomialDiagonalContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialModuleResolution -/
section

/-!
# The actual polynomial-module diagonal resolution

There are two copies of the polynomial variables. The coefficient copy acts
on the original module; the free copy acts on the resolution. The coordinate
equivalence below identifies the translated diagonal Koszul complex with
`S ⊗ (M ⊗ exterior)`, retaining the original module in every coefficient.
The distinction between these two actions is explicit throughout.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.PolynomialModuleResolution

open Classical MvPolynomial CommAlg CommAlg.Polymatroid
open scoped TensorProduct
open HomologicalPerturbation PolynomialFineContraction

universe u
variable {R V : Type u} [CommRing R] [Fintype V] [LinearOrder V]
  (M : Type u) [AddCommGroup M] [Module (MvPolynomial V R) M]
  [Module R M] [IsScalarTower R (MvPolynomial V R) M]

local notation "S" => MvPolynomial V R
local notation "E" => Simplicial.Ambient V R

abbrev CoefficientKoszul := TensorExteriorKoszul.Total (K := R) (V := V) (M := M)
abbrev Bar := S ⊗[R] CoefficientKoszul (R := R) (V := V) M
abbrev DiagonalSource :=
  PolynomialDiagonalContraction.Total (R := S) (V := V) ⊗[S] M

def diagonalCoordinates : DiagonalSource (R := R) (V := V) M ≃ₗ[R]
    (TensorIndex (V := V) →₀ M) :=
  (TensorProduct.equivFinsuppOfBasisLeft
    (tensorBasis (R := S) (V := V))).restrictScalars R

def barCoordinates : Bar (R := R) (V := V) M ≃ₗ[R]
    (TensorIndex (V := V) →₀ M) :=
  (TensorProduct.assoc R S M E).symm.trans
    ((TensorProduct.rightComm R S M E).trans
      (TensorProduct.equivFinsuppOfBasisLeft (tensorBasis (R := R) (V := V))))

lemma basis_tensor_coordinates {A P N J : Type*} [CommRing A]
    [AddCommMonoid P] [Module A P] [AddCommMonoid N] [Module A N] [DecidableEq J]
    (b : Module.Basis J A P) (j : J) (n : N) :
    TensorProduct.equivFinsuppOfBasisLeft b (b j ⊗ₜ[A] n) = Finsupp.single j n := by
  ext k
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self]
  by_cases h : j = k
  · subst k
    simp only [Finsupp.single_eq_same, one_smul]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm h), zero_smul]

@[simp] theorem diagonalCoordinates_basis (a : Exponent V) (F : Finset V) (m : M) :
    diagonalCoordinates M
      ((monomial a (1 : S) ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m) =
        Finsupp.single (a,F) m := by
  change TensorProduct.equivFinsuppOfBasisLeft (tensorBasis (R := S) (V := V))
    ((monomial a 1 ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m) = _
  simpa only [tensorBasis_apply] using
    (basis_tensor_coordinates (A := S) (N := M)
      (tensorBasis (R := S) (V := V)) (a, F) m)

@[simp] theorem barCoordinates_basis (a : Exponent V) (F : Finset V) (m : M) :
    barCoordinates M (monomial a (1 : R) ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.basis F)) =
      Finsupp.single (a,F) m := by
  change TensorProduct.equivFinsuppOfBasisLeft (tensorBasis (R := R) (V := V))
    ((monomial a 1 ⊗ₜ[R] Simplicial.basis F) ⊗ₜ[R] m) = _
  simpa only [tensorBasis_apply] using
    (basis_tensor_coordinates (A := R) (N := M)
      (tensorBasis (R := R) (V := V)) (a, F) m)

@[simp] theorem diagonalCoordinates_symm_single (a : Exponent V) (F : Finset V) (m : M) :
    (diagonalCoordinates (R := R) M).symm (Finsupp.single (a,F) m) =
      (monomial a (1 : S) ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m := by
  exact (diagonalCoordinates (R := R) (V := V) M).symm_apply_eq.mpr
    (diagonalCoordinates_basis (R := R) (V := V) M a F m).symm

@[simp] theorem barCoordinates_symm_single (a : Exponent V) (F : Finset V) (m : M) :
    (barCoordinates (R := R) M).symm (Finsupp.single (a,F) m) =
      monomial a (1 : R) ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.basis F) := by
  exact (barCoordinates (R := R) (V := V) M).symm_apply_eq.mpr
    (barCoordinates_basis (R := R) (V := V) M a F m).symm

def diagonalToBar : DiagonalSource (R := R) (V := V) M ≃ₗ[R]
    Bar (R := R) (V := V) M :=
  (diagonalCoordinates M).trans (barCoordinates M).symm

@[simp] theorem diagonalToBar_basis (a : Exponent V) (F : Finset V) (m : M) :
    diagonalToBar M ((monomial a (1 : S) ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m) =
      monomial a (1 : R) ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.basis F) := by
  change (barCoordinates M).symm (diagonalCoordinates M _) = _
  rw [diagonalCoordinates_basis, barCoordinates_symm_single]

/-- This contraction is obtained from the actual translated Koszul complex
by tensoring with `M` and the displayed coordinate equivalence. -/
def barContraction :
    LinearContraction (R := R) (M := Bar (R := R) (V := V) M) (H := M) :=
  ((PolynomialDiagonalContraction.moduleContraction M (X : V → S)).restrictScalars R).changeSource
    (diagonalToBar M)

/-- Exterior contraction leaves the original coefficient module unchanged. -/
def removeExterior (v : V) : Module.End R (CoefficientKoszul (R := R) (V := V) M) :=
  TensorProduct.map LinearMap.id (Simplicial.contraction v)

def externalDifferential : Module.End S (Bar (R := R) (V := V) M) :=
  ∑ v : V, (X v : S) • (removeExterior M v).baseChange S

def internalDifferential : Module.End S (Bar (R := R) (V := V) M) :=
  (TensorExteriorKoszul.differential (K := R) (M := M) (X : V → S)).baseChange S

/-- `X_external - X_module` is the literal diagonal differential. -/
def differential : Module.End S (Bar (R := R) (V := V) M) :=
  externalDifferential M - internalDifferential M

theorem externalDifferential_tmul (f : S) (m : M) (z : E) :
    externalDifferential M (f ⊗ₜ[R] (m ⊗ₜ[R] z)) =
      ∑ v : V, (X v * f) ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.contraction v z) := by
  simp only [externalDifferential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, removeExterior, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.smul_tmul', smul_eq_mul]

theorem internalDifferential_tmul (f : S) (m : M) (z : E) :
    internalDifferential M (f ⊗ₜ[R] (m ⊗ₜ[R] z)) =
      ∑ v : V, f ⊗ₜ[R] (((X v : S) • m) ⊗ₜ[R] Simplicial.contraction v z) := by
  rw [internalDifferential, LinearMap.baseChange_tmul,
    TensorExteriorKoszul.differential_tmul, TensorProduct.tmul_sum]

lemma diagonalToBar_monomial (a : Exponent V) (c : S) (F : Finset V) (m : M) :
    diagonalToBar M ((monomial a c ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m) =
      monomial a (1 : R) ⊗ₜ[R] ((c • m) ⊗ₜ[R] Simplicial.basis F) := by
  have hc : monomial a c = c • monomial a (1 : S) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, ← TensorProduct.smul_tmul', TensorProduct.smul_tmul,
    diagonalToBar_basis]

lemma diagonalToBar_difference_basis (v : V) (a : Exponent V)
    (F : Finset V) (m : M) :
    diagonalToBar M
      ((((X v - C (X v : S)) * monomial a 1) ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m) =
      (X v * monomial a (1 : R)) ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.basis F) -
        monomial a 1 ⊗ₜ[R] (((X v : S) • m) ⊗ₜ[R] Simplicial.basis F) := by
  have hxA : X v * monomial a (1 : S) = monomial (a + Finsupp.single v 1) 1 := by
    simp only [X, monomial_mul_monomial, one_mul, add_comm]
  have hxR : X v * monomial a (1 : R) = monomial (a + Finsupp.single v 1) 1 := by
    simp only [X, monomial_mul_monomial, one_mul, add_comm]
  have hc : C (X v : S) * monomial a 1 = monomial a (X v : S) := by
    simp only [MvPolynomial.C_mul_monomial, mul_one]
  rw [sub_mul, hxA, hc, TensorProduct.sub_tmul, TensorProduct.sub_tmul,
    map_sub, diagonalToBar_basis, diagonalToBar_monomial, hxR]

lemma diagonalToBar_difference_contraction (v : V) (a : Exponent V)
    (F : Finset V) (m : M) :
    diagonalToBar M
      ((((X v - C (X v : S)) * monomial a 1) ⊗ₜ[S]
        Simplicial.contraction v (Simplicial.basis F)) ⊗ₜ[S] m) =
      (X v * monomial a (1 : R)) ⊗ₜ[R]
        (m ⊗ₜ[R] Simplicial.contraction v (Simplicial.basis F)) -
      monomial a 1 ⊗ₜ[R]
        (((X v : S) • m) ⊗ₜ[R] Simplicial.contraction v (Simplicial.basis F)) := by
  rw [Simplicial.contraction_basis, Simplicial.contraction_basis]
  by_cases hv : v ∈ F
  · simp only [if_pos hv, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
    erw [LinearMapClass.map_smul_of_tower («S» := R)]
    rw [diagonalToBar_difference_basis, smul_sub]
    simp only [TensorProduct.smul_tmul']
  · simp only [if_neg hv, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
      map_zero, sub_zero]

/-- The coordinate equivalence intertwines the translated diagonal
differential with the difference of the two literal polynomial actions. -/
theorem diagonalToBar_d (x : DiagonalSource (R := R) (V := V) M) :
    diagonalToBar M
      ((PolynomialDiagonalContraction.moduleContraction M (X : V → S)).d x) =
        differential M (diagonalToBar M x) := by
  let ds := (PolynomialDiagonalContraction.moduleContraction M (X : V → S)).d
  have he : ((diagonalToBar M).toLinearMap.comp (ds.restrictScalars R)).comp
      (diagonalCoordinates M).symm.toLinearMap =
    ((differential M).restrictScalars R).comp
      ((diagonalToBar M).toLinearMap.comp (diagonalCoordinates M).symm.toLinearMap) := by
    apply Finsupp.lhom_ext
    rintro ⟨a,F⟩ m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.restrictScalars_apply, diagonalCoordinates_symm_single]
    change diagonalToBar M
      ((PolynomialDiagonalContraction.moduleContraction M (X : V → S)).d
        ((monomial a 1 ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m)) = _
    rw [PolynomialDiagonalContraction.moduleContraction_d_tmul,
      PolynomialDiagonalContraction.differential,
      TensorExteriorKoszul.differential_tmul, TensorProduct.sum_tmul, map_sum,
      diagonalToBar_basis]
    change (∑ v : V, diagonalToBar M
      ((((X v - C (X v : S)) * monomial a 1) ⊗ₜ[S]
        Simplicial.contraction v (Simplicial.basis F)) ⊗ₜ[S] m)) = _
    rw [differential, LinearMap.sub_apply, externalDifferential_tmul,
      internalDifferential_tmul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact diagonalToBar_difference_contraction M v a F m
  have h := LinearMap.congr_fun he (diagonalCoordinates M x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, LinearEquiv.symm_apply_apply] using h

theorem barContraction_d :
    (barContraction (R := R) (V := V) M).d = (differential M).restrictScalars R := by
  apply LinearMap.ext
  intro x
  change diagonalToBar M
    ((PolynomialDiagonalContraction.moduleContraction M (X : V → S)).d
      ((diagonalToBar M).symm x)) = differential M x
  rw [diagonalToBar_d, LinearEquiv.apply_symm_apply]

theorem differential_square :
    differential (R := R) (V := V) M * differential M = 0 := by
  apply LinearMap.ext
  intro x
  have hd := LinearMap.congr_fun (barContraction (R := R) (V := V) M).differential x
  rw [barContraction_d] at hd
  exact hd

theorem bar_cycle_boundary (x : Bar (R := R) (V := V) M)
    (hx : differential M x = 0) (hε : (barContraction M).projection x = 0) :
    differential M ((barContraction M).h x) = x := by
  have he := LinearMap.congr_fun (barContraction (R := R) (V := V) M).homotopy x
  rw [barContraction_d] at he
  change differential M ((barContraction M).h x) +
    (barContraction M).h (differential M x) =
      x - (barContraction M).inclusion ((barContraction M).projection x) at he
  have hb : differential M ((barContraction M).h x) = x - 0 := by
    simpa only [hx, hε, map_zero, add_zero] using he
  exact hb.trans (sub_zero x)

def coefficientAugmentation : CoefficientKoszul (R := R) (V := V) M →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap.comp
    (TensorProduct.map LinearMap.id ((Simplicial.basis (V := V) (k := R)).coord ∅))

@[simp] theorem coefficientAugmentation_tmul_basis (m : M) (F : Finset V) :
    coefficientAugmentation (R := R) M (m ⊗ₜ[R] Simplicial.basis F) =
      if F = ∅ then m else 0 := by
  change ((Simplicial.basis (V := V) (k := R)).repr (Simplicial.basis F) ∅) • m = _
  rw [Module.Basis.repr_self]
  by_cases h : F = ∅
  · subst F
    simp only [Finsupp.single_eq_same, one_smul, if_pos rfl, if_true]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm h), zero_smul, if_neg h]

/-- The augmentation uses multiplication in the original module. It is
linear over the free polynomial ring, with its given action on `M`. -/
def augmentation : Bar (R := R) (V := V) M →ₗ[S] M :=
  (coefficientAugmentation M).liftBaseChange S

@[simp] theorem augmentation_tmul_basis (f : S) (m : M) (F : Finset V) :
    augmentation M (f ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.basis F)) =
      if F = ∅ then f • m else 0 := by
  rw [augmentation, LinearMap.liftBaseChange_tmul, coefficientAugmentation_tmul_basis]
  split_ifs <;> simp only [smul_zero]

theorem barContraction_projection_basis (a : Exponent V) (m : M) (F : Finset V) :
    (barContraction (R := R) (V := V) M).projection
      (monomial a 1 ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.basis F)) =
        if F = ∅ then (monomial a (1 : R)) • m else 0 := by
  have he : (diagonalToBar (R := R) M).symm
      (monomial a 1 ⊗ₜ[R] (m ⊗ₜ[R] Simplicial.basis F)) =
        (monomial a (1 : S) ⊗ₜ[S] Simplicial.basis F) ⊗ₜ[S] m := by
    apply (diagonalToBar M).injective
    rw [LinearEquiv.apply_symm_apply, diagonalToBar_basis]
  change (PolynomialDiagonalContraction.moduleContraction M (X : V → S)).projection
    ((diagonalToBar M).symm _) = _
  rw [he]
  change (PolynomialDiagonalContraction.contraction (X : V → S)).projection
    (monomial a 1 ⊗ₜ[S] Simplicial.basis F) • m = _
  rw [PolynomialDiagonalContraction.contraction_projection_tmul_basis]
  have hm : aeval (X : V → S) (monomial a (1 : S)) = monomial a (1 : R) := by
    rw [aeval_monomial, map_one, one_mul]
    simp only [monomial_eq, map_one, one_mul]
  rw [hm]
  split_ifs <;> simp only [zero_smul]

/-- The constructed split projection is the literal module augmentation. -/
theorem barContraction_projection :
    (barContraction (R := R) (V := V) M).projection =
      (augmentation M).restrictScalars R := by
  have he : (barContraction (R := R) (V := V) M).projection.comp
      (barCoordinates M).symm.toLinearMap =
    ((augmentation M).restrictScalars R).comp (barCoordinates M).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨a,F⟩ m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      barCoordinates_symm_single, LinearMap.restrictScalars_apply,
      barContraction_projection_basis, augmentation_tmul_basis]
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun he (barCoordinates M x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply] using hx

theorem augmentation_boundary :
    (augmentation (R := R) (V := V) M).comp (differential M) = 0 := by
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun (barContraction (R := R) (V := V) M).projection_boundary x
  rw [barContraction_d, barContraction_projection] at hx
  exact hx

theorem augmentation_surjective :
    Function.Surjective (augmentation (R := R) (V := V) M) := by
  intro m
  refine ⟨(barContraction M).inclusion m, ?_⟩
  have h := (barContraction (R := R) (V := V) M).projection_inclusion_apply m
  rw [barContraction_projection] at h
  exact h

/-- Exactness is witnessed by the explicit diagonal homotopy, with the
actual module-action augmentation. This form survives arbitrary base change. -/
theorem cycle_in_augmentation_kernel_is_boundary
    (x : Bar (R := R) (V := V) M) (hx : differential M x = 0)
    (hε : augmentation M x = 0) :
    differential M ((barContraction M).h x) = x := by
  apply bar_cycle_boundary M x hx
  rw [barContraction_projection]
  exact hε

end FourPapers.PolynomialModuleResolution

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialPerturbation -/
section

/-!
# Transferring the actual diagonal resolution to Koszul homology

The external-variable differential strictly lowers coefficient Koszul
internal degree. The inverse operators are therefore constructed, and the
resulting differential on `S ⊗ H` has every entry in the variable ideal.
The actual diagonal augmentation supplies exactness and remains split over
the coefficient ring. Applications must supply the proved graded Koszul
contraction and actual finiteness of its homology, not a rank surrogate.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.PolynomialPerturbation

open Classical CommAlg MvPolynomial HomologicalPerturbation
open scoped TensorProduct
open PolynomialModuleResolution

universe u
variable {R V : Type u} [CommRing R] [Fintype V] [LinearOrder V]
  (M : Type u) [AddCommGroup M] [Module (MvPolynomial V R) M]
  [Module R M] [IsScalarTower R (MvPolynomial V R) M]

local notation "S" => MvPolynomial V R

def tensorBasis {I : Type*} (b : Module.Basis I R M) :
    Module.Basis (I × Finset V) R (CoefficientKoszul (R := R) (V := V) M) :=
  b.tensorProduct Simplicial.basis

def internalDegree {I : Type*} (degree : I → ℕ) (a : I × Finset V) : ℕ :=
  degree a.1 + a.2.card

/-- Each external contraction removes exactly one exterior variable while
retaining the original coefficient basis vector. -/
theorem externalDifferential_decreases {I : Type*} (b : Module.Basis I R M)
    (degree : I → ℕ) :
    DegreeDecreasing ((tensorBasis M b).baseChange S) (internalDegree degree)
      (externalDifferential (R := R) (V := V) M) := by
  apply degreeDecreasing_of_mem_span
  rintro ⟨i,F⟩
  let B := (tensorBasis (R := R) (V := V) M b).baseChange S
  let L := Submodule.span S (B '' {a | internalDegree degree a < internalDegree degree (i,F)})
  change externalDifferential M (B (i,F)) ∈ L
  rw [show B (i,F) = 1 ⊗ₜ[R] (b i ⊗ₜ[R] Simplicial.basis F) by
    simp only [B, Module.Basis.baseChange_apply, tensorBasis, Module.Basis.tensorProduct_apply],
    externalDifferential_tmul]
  apply L.sum_mem
  intro v _
  rw [mul_one, Simplicial.contraction_basis]
  by_cases hv : v ∈ F
  · rw [if_pos hv, TensorProduct.tmul_smul, TensorProduct.tmul_smul]
    have hr : internalDegree degree (i,F.erase v) < internalDegree degree (i,F) := by
      simp only [internalDegree]
      exact Nat.add_lt_add_left (Finset.card_erase_lt_of_mem hv) _
    have hb : B (i,F.erase v) ∈ L := Submodule.subset_span ⟨(i,F.erase v),hr,rfl⟩
    have hs : (X v : S) ⊗ₜ[R] (b i ⊗ₜ[R] Simplicial.basis (F.erase v)) ∈ L := by
      have he : (X v : S) ⊗ₜ[R] (b i ⊗ₜ[R] Simplicial.basis (F.erase v)) =
          (X v : S) • B (i,F.erase v) := by
        simp only [B, Module.Basis.baseChange_apply, tensorBasis,
          Module.Basis.tensorProduct_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he]
      exact L.smul_mem _ hb
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul S]
    exact L.smul_mem _ hs
  · rw [if_neg hv, TensorProduct.tmul_zero, TensorProduct.tmul_zero]
    exact L.zero_mem

theorem externalDifferential_mem_variableIdeal (x : Bar (R := R) (V := V) M) :
    externalDifferential M x ∈ MvPolynomial.idealOfVars V R • (⊤ : Submodule S (Bar M)) := by
  rw [externalDifferential, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro v _
  change (X v : S) • (removeExterior M v).baseChange S x ∈ _
  exact Submodule.smul_mem_smul
    (Ideal.subset_span (Set.mem_range_self v)) (Submodule.mem_top : _ ∈ (⊤ : Submodule S (Bar M)))

variable {H : Type u} [AddCommGroup H] [Module R H]
variable (C : LinearContraction (R := R)
  (M := CoefficientKoszul (R := R) (V := V) M) (H := H))
variable (hCd : C.d = TensorExteriorKoszul.differential (K := R) (M := M)
  (X : V → MvPolynomial V R))

def extendedContraction :
    LinearContraction (R := S) (M := Bar (R := R) (V := V) M) (H := S ⊗[R] H) :=
  (C.baseChange S).negDifferential

include hCd in
theorem extended_differential :
    (extendedContraction M C).d + externalDifferential M = differential M := by
  change -(C.d.baseChange S) + externalDifferential M = _
  rw [hCd]
  change -internalDifferential (R := R) (V := V) M +
      externalDifferential (R := R) (V := V) M =
    externalDifferential (R := R) (V := V) M - internalDifferential (R := R) (V := V) M
  exact (add_comm (-internalDifferential (R := R) (V := V) M)
    (externalDifferential (R := R) (V := V) M)).trans
      (sub_eq_add_neg (externalDifferential (R := R) (V := V) M)
        (internalDifferential (R := R) (V := V) M)).symm

variable {I : Type*} (b : Module.Basis I R M) (degree : I → ℕ)
  (hh : DegreeNonincreasing (tensorBasis M b) (internalDegree degree) C.h)

def transferred : LinearDeformationRetract
    (R := S) (M := Bar (R := R) (V := V) M) (H := S ⊗[R] H) :=
  (extendedContraction M C).perturbByDegree
    ((tensorBasis M b).baseChange S) (internalDegree degree)
    (externalDifferential M) (externalDifferential_decreases M b degree)
    ((hh.baseChange S).neg)
    (by rw [extended_differential M C hCd]; exact differential_square M)

theorem transferred_sourceD :
    (transferred M C hCd b degree hh).sourceD = differential M :=
  extended_differential M C hCd

def augmentation : (S ⊗[R] H) →ₗ[S] M :=
  (PolynomialModuleResolution.augmentation M).comp
    (transferred M C hCd b degree hh).inclusion

/-- The finite model inherits the original module as its augmentation
target, with an actual coefficient-linear splitting. -/
def splitAugmentation :
    LinearDeformationRetract (R := R) (M := S ⊗[R] H) (H := M) :=
  ((transferred M C hCd b degree hh).restrictScalars R).descendZeroContraction
    (barContraction M) (by
      change ((transferred M C hCd b degree hh).sourceD).restrictScalars R = _
      rw [transferred_sourceD, barContraction_d])

theorem splitAugmentation_projection :
    (splitAugmentation M C hCd b degree hh).projection =
      (augmentation M C hCd b degree hh).restrictScalars R := by
  apply LinearMap.ext
  intro x
  change (barContraction M).projection ((transferred M C hCd b degree hh).inclusion x) = _
  rw [barContraction_projection]
  rfl

theorem differential_entries_in_variableIdeal {J : Type*}
    (c : Module.Basis J S (S ⊗[R] H)) (i j : J) :
    c.repr ((transferred M C hCd b degree hh).targetD (c i)) j ∈
      MvPolynomial.idealOfVars V R :=
  (extendedContraction M C).perturbByDegree_coefficient_mem_ideal
    ((tensorBasis M b).baseChange S) (internalDegree degree)
    (externalDifferential M) (externalDifferential_decreases M b degree)
    ((hh.baseChange S).neg)
    (by rw [extended_differential M C hCd]; exact differential_square M)
    c (MvPolynomial.idealOfVars V R) (externalDifferential_mem_variableIdeal M) i j

end FourPapers.PolynomialPerturbation

end
end
end


end
