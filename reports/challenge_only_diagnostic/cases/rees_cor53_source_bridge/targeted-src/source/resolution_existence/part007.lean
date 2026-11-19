module
public import resolution_existence.part003
public import resolution_existence.part004
public import resolution_existence.part005
public import resolution_existence.part006

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialFineResolutionGrading -/
section

/-! # Fine shifts and actual minimal matrices

The polynomial perturbation preserves the complete exponent vector. Every
matrix coefficient is therefore the single monomial prescribed by the two
fine shifts, and is zero when their difference is not a nonnegative exponent.
The basis index is proved finite using genuine fine Koszul homology.
-/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice.MonomialFineResolution
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial CategoryTheory
open HomologicalPerturbation PolynomialModuleResolution
open scoped TensorProduct
attribute [local instance] Classical.propDecidable

section PolynomialExtension
variable {k W M₀ H₀ I₀ J₀ : Type*} [CommRing k]
  [AddCommGroup M₀] [Module k M₀] [AddCommGroup H₀] [Module k H₀]
  (C₀ : LinearContraction (R := k) (M := M₀) (H := H₀))
  (b : Module.Basis I₀ k M₀) (c : Module.Basis J₀ k H₀)
  (degree : I₀ → W →₀ ℕ) (degree' : J₀ → W →₀ ℕ)

/-- Scalar extension and the Koszul sign change preserve the fine
homotopy degree. The assertion concerns the actual extended contraction. -/
theorem polynomialExtended_h_fine
    (hh : ∀ i, C₀.h (b i) ∈ Grading.Piece b degree (degree i))
    (a : (W →₀ ℕ) × I₀) :
    ((C₀.baseChange (MvPolynomial W k)).negDifferential).h.restrictScalars k
        (polynomialTensorBasis b a) ∈
      Grading.Piece (polynomialTensorBasis b) (polynomialTensorFineDegree degree)
        (polynomialTensorFineDegree degree a) := by
  change -((C₀.h.baseChange (MvPolynomial W k)).restrictScalars k
    (polynomialTensorBasis b a)) ∈ _
  exact Submodule.neg_mem _
    (polynomialTensor_baseChange_finePiece b b degree degree C₀.h hh a)

theorem polynomialExtended_inclusion_fine
    (hi : ∀ j, C₀.inclusion (c j) ∈ Grading.Piece b degree (degree' j))
    (a : (W →₀ ℕ) × J₀) :
    ((C₀.baseChange (MvPolynomial W k)).negDifferential).inclusion.restrictScalars k
        (polynomialTensorBasis c a) ∈
      Grading.Piece (polynomialTensorBasis b) (polynomialTensorFineDegree degree)
        (polynomialTensorFineDegree degree' a) :=
  polynomialTensor_baseChange_finePiece c b degree' degree C₀.inclusion hi a

theorem polynomialExtended_projection_fine
    (hp : ∀ i, C₀.projection (b i) ∈ Grading.Piece c degree' (degree i))
    (a : (W →₀ ℕ) × I₀) :
    ((C₀.baseChange (MvPolynomial W k)).negDifferential).projection.restrictScalars k
        (polynomialTensorBasis b a) ∈
      Grading.Piece (polynomialTensorBasis c) (polynomialTensorFineDegree degree')
        (polynomialTensorFineDegree degree a) :=
  polynomialTensor_baseChange_finePiece b c degree degree' C₀.projection hp a

end PolynomialExtension

section ProjectedEntries
universe w
variable {R₀ S₀ F₀ M₁ : Type w} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
  [AddCommGroup F₀] [Module S₀ F₀] [Module R₀ F₀] [IsScalarTower R₀ S₀ F₀]
  [AddCommGroup M₁] [Module S₀ M₁] [Module R₀ M₁] [IsScalarTower R₀ S₀ M₁]
  {I₁ : Type*} (b : Module.Basis I₁ S₀ F₀) (degree : I₁ → ℕ)
  (D : Module.End S₀ F₀)
  (C₁ : LinearDeformationRetract (R := R₀) (M := F₀) (H := M₁))
  (hD : C₁.sourceD = D.restrictScalars R₀)
  (hlower : ∀ p, D.comp (Grading.projection b degree (p+1)) =
    (Grading.projection b degree p).comp D)

/-- Restricting an actual differential to its homogeneous pieces retains
the corresponding entries of its original basis matrix. -/
theorem projectedComplex_entry (p : ℕ)
    (i : {i : I₁ // degree i = p+1}) (j : {j : I₁ // degree j = p}) :
    (ProjectedFreeResolution.pieceBasis b degree p).repr
      ((ProjectedFreeResolution.data b degree D C₁ hD hlower).complex.d (p+1) p
        (ProjectedFreeResolution.pieceBasis b degree (p+1) i)) j =
      b.repr (D (b i.val)) j.val := by
  rw [SubmoduleComplexData.complex_d]
  change (ProjectedFreeResolution.pieceBasis b degree p).repr
    ((ProjectedFreeResolution.data b degree D C₁ hD hlower).differential p
      (ProjectedFreeResolution.pieceBasis b degree (p+1) i)) j = _
  have hrepr := ProjectedFreeResolution.pieceBasis_repr (S := S₀) (F := F₀)
    b degree p ((ProjectedFreeResolution.data b degree D C₁ hD hlower).differential p
      (ProjectedFreeResolution.pieceBasis b degree (p+1) i)) j
  have hv : ((ProjectedFreeResolution.data b degree D C₁ hD hlower).differential p
      (ProjectedFreeResolution.pieceBasis b degree (p+1) i)).val = D (b i.val) := by
    change D (ProjectedFreeResolution.pieceBasis b degree (p+1) i).val = _
    rw [ProjectedFreeResolution.pieceBasis_val]
  exact hrepr.trans (congrArg (fun x : F₀ => b.repr x j.val) hv)

end ProjectedEntries

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V] (B : Family V)
local instance : DecidableEq V := LinearOrder.toDecidableEq
local notation "S" => MvPolynomial V K
local notation "M" => monomialIdeal K B
local notation "C" => contraction (K := K) B

/-- The same actual component retains its full exponent label. -/
def homologyLof_mem_fine :=
  nestedLof_mem_piece (R := K) (chooseBasisFamily (K := K) B)
    (fun (α : Exponent V) (_p : ℕ) => α)

set_option backward.isDefEq.respectTransparency true in
theorem homotopy_basis_mem_fine (a : Index B) :
    (contraction (K := K) B).h (tensorBasis (K := K) B a)∈Grading.Piece (tensorBasis (K := K) B) (fineDegree B) (fineDegree B a) := by
  have hle : Grading.Piece (tensorBasis (K := K) B)
      (fun i : Index B => (fineDegree B i, homological B i))
      (fineDegree B a, homological B a+1) ≤
      Grading.Piece (tensorBasis (K := K) B) (fineDegree B) (fineDegree B a) := by
    apply Submodule.span_mono
    apply Set.image_mono
    intro i hi
    exact congrArg (Prod.fst : Exponent V × ℕ → Exponent V) hi
  exact hle (contraction_h_fine (K := K) B (fineDegree B a) (homological B a)
    ⟨tensorBasis (K := K) B a, Grading.basis_mem_piece (R := K) (tensorBasis (K := K) B)
      (fun i => (fineDegree B i, homological B i)) a⟩)

set_option backward.isDefEq.respectTransparency true in
/-- The same verified maps retain the full exponent vector. -/
def inclusion_basis_mem_fine :=
  chosen_inclusion_basis_degree (K := K) («M» := TensorModule (K := K) B)
    (I := Index B) (Γ := Exponent V)
    (tensorBasis (K := K) B) (fineDegree B) (homological B) (differential (K := K) B)
    (differential_square (K := K) B) (differential_lowers (K := K) B) Prod.fst

set_option backward.isDefEq.respectTransparency true in
def projection_basis_mem_fine :=
  chosen_projection_basis_degree (K := K) («M» := TensorModule (K := K) B)
    (I := Index B) (Γ := Exponent V)
    (tensorBasis (K := K) B) (fineDegree B) (homological B) (differential (K := K) B)
    (differential_square (K := K) B) (differential_lowers (K := K) B) Prod.fst

abbrev barFineBasis := polynomialTensorBasis
  (k := K) (V := V) («M» := TensorModule (K := K) B) (I := Index B)
  (tensorBasis (K := K) B)
abbrev modelFineBasis := polynomialTensorBasis
  (k := K) (V := V) («M» := Homology (K := K) B) (I := HomologyIndex (K := K) B)
  (homologyBasis (K := K) B)
abbrev barFineDegree := polynomialTensorFineDegree (fineDegree B)
abbrev modelFineDegree := polynomialTensorFineDegree (fun a : HomologyIndex (K := K) B => a.1)

theorem extended_h_fine (a : Exponent V × Index B) :
    (extended (K := K) B).h.restrictScalars K (barFineBasis (K := K) B a)∈
      Grading.Piece (barFineBasis (K := K) B) (barFineDegree B) (barFineDegree B a) :=
  polynomialExtended_h_fine (k := K) (W := V)
    (M₀ := TensorModule (K := K) B) (H₀ := Homology (K := K) B) (I₀ := Index B)
    (contraction (K := K) B) (tensorBasis (K := K) B) (fineDegree B)
    (homotopy_basis_mem_fine (K := K) B) a

theorem extended_inclusion_fine (a : Exponent V × HomologyIndex (K := K) B) :
    (extended (K := K) B).inclusion.restrictScalars K (modelFineBasis (K := K) B a)∈
      Grading.Piece (barFineBasis (K := K) B) (barFineDegree B) (modelFineDegree (K := K) B a) :=
  polynomialExtended_inclusion_fine (k := K) (W := V)
    (M₀ := TensorModule (K := K) B) (H₀ := Homology (K := K) B)
    (I₀ := Index B) (J₀ := HomologyIndex (K := K) B)
    (contraction (K := K) B) (tensorBasis (K := K) B) (homologyBasis (K := K) B)
    (fineDegree B) (fun a => a.1) (inclusion_basis_mem_fine (K := K) B) a

theorem extended_projection_fine (a : Exponent V × Index B) :
    (extended (K := K) B).projection.restrictScalars K (barFineBasis (K := K) B a)∈
      Grading.Piece (modelFineBasis (K := K) B) (modelFineDegree (K := K) B) (barFineDegree B a) :=
  polynomialExtended_projection_fine (k := K) (W := V)
    (M₀ := TensorModule (K := K) B) (H₀ := Homology (K := K) B)
    (I₀ := Index B) (J₀ := HomologyIndex (K := K) B)
    (contraction (K := K) B) (tensorBasis (K := K) B) (homologyBasis (K := K) B)
    (fineDegree B) (fun a => a.1) (projection_basis_mem_fine (K := K) B) a

theorem external_fine (a : Exponent V × Index B) :
    (externalDifferential M).restrictScalars K (barFineBasis (K := K) B a)∈
      Grading.Piece (barFineBasis (K := K) B) (barFineDegree B) (barFineDegree B a) := by
  rcases a with ⟨β,a,F⟩
  let L := Grading.Piece (barFineBasis (K := K) B) (barFineDegree B)
    (barFineDegree B (β,a,F))
  change externalDifferential M (barFineBasis (K := K) B (β,a,F)) ∈ L
  rw [barFineBasis, polynomialTensorBasis_apply, tensorBasis_apply,
    externalDifferential_tmul]
  apply Submodule.sum_mem
  intro v hv
  rw [Simplicial.contraction_basis]
  by_cases hvF : v∈F
  · rw [if_pos hvF, Units.smul_def, ← Int.cast_smul_eq_zsmul K,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]
    have hpoly : (X v : S)*monomial β 1=monomial (β+Finsupp.single v 1) 1 := by
      rw [X,monomial_mul,one_mul,add_comm]
    rw [hpoly]
    have hdeg : barFineDegree B (β+Finsupp.single v 1,a,F.erase v)=
        barFineDegree B (β,a,F) := by
      change (β+Finsupp.single v 1)+(a.val+faceExponent (F.erase v))=
        β+(a.val+faceExponent F)
      rw [←faceExponent_erase_add hvF]
      abel
    have hb := Grading.basis_mem_piece (barFineBasis (K := K) B)
      (barFineDegree B) (β+Finsupp.single v 1,a,F.erase v)
    rw [hdeg] at hb
    have hb' : monomial (β+Finsupp.single v 1) 1 ⊗ₜ[K]
        (monomialBasis B a ⊗ₜ[K] Simplicial.basis (F.erase v)) ∈ L := by
      simpa only [barFineBasis, polynomialTensorBasis_apply, tensorBasis_apply] using hb
    exact Submodule.smul_mem L _ hb'
  · rw [if_neg hvF,TensorProduct.tmul_zero,TensorProduct.tmul_zero]
    exact L.zero_mem

abbrev fineUnit := restrictScalarsUnit (K := K) (perturbationUnit (K := K) B)

theorem fineUnit_val : (fineUnit (K := K) B : Module.End K (Bar (R := K) M))=
    1+(externalDifferential M).restrictScalars K*(extended (K := K) B).h.restrictScalars K := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun ((extended (K := K) B).leftPerturbationUnit_val
    ((PolynomialPerturbation.tensorBasis (R := K) (V := V) M
      (monomialBasis (k := K) B)).baseChange S)
    (PolynomialPerturbation.internalDegree (fun a : {a : Exponent V // Contains B a} => a.val.degree))
    (externalDifferential M) (PolynomialPerturbation.externalDifferential_decreases M
      (monomialBasis B) (fun a => a.val.degree))
    (((contraction_h_nonincreasing (K := K) B).baseChange S).neg)) x

theorem freeModel_fine (α : Exponent V) (x : S ⊗[K] Homology (K := K) B)
    (hx : x∈Grading.Piece (modelFineBasis (K := K) B) (modelFineDegree (K := K) B) α) :
    (freeModel (K := K) B).targetD x∈Grading.Piece (modelFineBasis (K := K) B) (modelFineDegree (K := K) B) α := by
  change ((extended (K := K) B).restrictScalars K).transferredDifferential
    ((externalDifferential M).restrictScalars K) (fineUnit (K := K) B) x∈_
  exact ((extended (K := K) B).restrictScalars K).transferredDifferential_mem_finePiece
    (barFineBasis (K := K) B) (modelFineBasis (K := K) B) (barFineDegree B) (modelFineDegree (K := K) B)
    ((externalDifferential M).restrictScalars K) (fineUnit (K := K) B) (fineUnit_val (K := K) B)
    (extended_h_fine (K := K) B) (external_fine (K := K) B) (extended_inclusion_fine (K := K) B)
    (extended_projection_fine (K := K) B) α x hx

theorem freeBasis_fine (a : HomologyIndex (K := K) B) :
    freeBasis (K := K) B a∈Grading.Piece (modelFineBasis (K := K) B) (modelFineDegree (K := K) B) a.1 := by
  have h := Grading.basis_mem_piece (modelFineBasis (K := K) B) (modelFineDegree (K := K) B) (0,a)
  simpa only [modelFineDegree,polynomialTensorFineDegree,zero_add,modelFineBasis,
    polynomialTensorBasis_apply,monomial_zero',map_one,freeBasis,Module.Basis.baseChange_apply] using h

/-- The actual matrix entry is the unique monomial prescribed by the
complete fine shifts. -/
theorem freeModel_matrix_monomial (i j : HomologyIndex (K := K) B) :
    (freeBasis (K := K) B).repr ((freeModel (K := K) B).targetD (freeBasis (K := K) B i)) j=
      monomial (i.1-j.1)
        (((freeBasis (K := K) B).repr ((freeModel (K := K) B).targetD (freeBasis (K := K) B i)) j).coeff (i.1-j.1)) :=
  polynomialTensor_coefficient_eq_monomial
    (k := K) (V := V) («M» := Homology (K := K) B) (I := HomologyIndex (K := K) B)
    (homologyBasis (K := K) B) (fun a => a.1) i.1
    (freeModel_fine (K := K) B i.1 _ (freeBasis_fine (K := K) B i)) j

theorem freeModel_matrix_zero_of_not_le (i j : HomologyIndex (K := K) B) (hij : ¬ j.1 ≤ i.1) :
    (freeBasis (K := K) B).repr ((freeModel (K := K) B).targetD (freeBasis (K := K) B i)) j=0 :=
  polynomialTensor_coefficient_zero_of_not_le
    (k := K) (V := V) («M» := Homology (K := K) B) (I := HomologyIndex (K := K) B)
    (homologyBasis (K := K) B) (fun a => a.1) i.1
    (freeModel_fine (K := K) B i.1 _ (freeBasis_fine (K := K) B i)) j hij

theorem freeModel_matrix_weighted (w : V → ℕ) (i j : HomologyIndex (K := K) B) :
    ((freeBasis (K := K) B).repr
      ((freeModel (K := K) B).targetD (freeBasis (K := K) B i)) j).IsWeightedHomogeneous w
        (Finsupp.weight w i.1-Finsupp.weight w j.1) :=
  polynomialTensor_coefficient_weighted
    (k := K) (V := V) («M» := Homology (K := K) B) (I := HomologyIndex (K := K) B)
    (homologyBasis (K := K) B) (fun a => a.1) i.1
    (freeModel_fine (K := K) B i.1 _ (freeBasis_fine (K := K) B i)) w j

abbrev ResolutionIndex (p : ℕ) := {i : HomologyIndex (K := K) B // i.2.1=p}

def resolutionShiftIndexEquiv (α : Exponent V) (p : ℕ) :
    {i : ResolutionIndex (K := K) B p // i.val.1=α} ≃
      Module.Free.ChooseBasisIndex K (Strand (K := K) B α p) where
  toFun a := by
    rcases a with ⟨⟨⟨β,q,j⟩,hq⟩,hβ⟩
    dsimp at hq hβ
    subst q
    subst β
    exact j
  invFun j := ⟨⟨⟨α,p,j⟩,rfl⟩,rfl⟩
  left_inv a := by
    rcases a with ⟨⟨⟨β,q,j⟩,hq⟩,hβ⟩
    dsimp at hq hβ
    subst q
    subst β
    rfl
  right_inv _ := rfl

/-- The number of generators at each fine shift is the genuine fine
Betti number, established by the actual homology comparison. -/
theorem resolution_shift_multiplicity (α : Exponent V) (p : ℕ) :
    Nat.card {i : ResolutionIndex (K := K) B p // i.val.1=α}=
      bettiNumber (k := K) B α p := by
  rw [Nat.card_congr (resolutionShiftIndexEquiv (K := K) B α p),Nat.card_eq_fintype_card,
    ←Module.finrank_eq_card_chooseBasisIndex]
  exact (strandEquivFineHomology (K := K) B α p).finrank_eq.trans
    (monomialFineHomology_finrank B α p)

def resolutionBasis (p : ℕ) : Module.Basis (ResolutionIndex (K := K) B p) S
    ((resolution (K := K) B).complex.X p) :=
  ProjectedFreeResolution.pieceBasis (freeBasis (K := K) B) (fun a => a.2.1) p

instance resolution_free (p : ℕ) : Module.Free S ((resolution (K := K) B).complex.X p) :=
  Module.Free.of_basis (resolutionBasis (K := K) B p)

instance resolution_finite (p : ℕ) : Module.Finite S ((resolution (K := K) B).complex.X p) :=
  Module.Finite.of_basis (resolutionBasis (K := K) B p)

theorem homologyIndex_homological_le (a : HomologyIndex (K := K) B) :
    a.2.1≤Fintype.card V := by
  by_contra h
  letI := strand_zero_of_exterior_gt (K := K) B a.1 a.2.1 (Nat.lt_of_not_ge h)
  exact (Module.Free.chooseBasis K (Strand (K := K) B a.1 a.2.1)).ne_zero a.2.2
    (Subsingleton.elim _ _)

/-- The constructed free complex is bounded, not only finite in each term. -/
theorem resolution_zero_above (p : ℕ) (hp : Fintype.card V<p) :
    Subsingleton ((resolution (K := K) B).complex.X p) :=
  ProjectedFreeResolution.piece_zero_above (freeBasis (K := K) B) (fun a => a.2.1)
    (Fintype.card V) (homologyIndex_homological_le (K := K) B) p hp

/-- These are coefficients of the actual adjacent resolution map. -/
theorem resolution_entry (p : ℕ) (i : ResolutionIndex (K := K) B (p+1))
    (j : ResolutionIndex (K := K) B p) :
    (resolutionBasis (K := K) B p).repr ((resolution (K := K) B).complex.d (p+1) p
      (resolutionBasis (K := K) B (p+1) i)) j=
        (freeBasis (K := K) B).repr ((freeModel (K := K) B).targetD (freeBasis (K := K) B i.val)) j.val :=
  projectedComplex_entry (R₀ := K) (S₀ := S)
    (F₀ := S ⊗[K] Homology (K := K) B) (M₁ := M)
    (I₁ := HomologyIndex (K := K) B)
    (freeBasis (K := K) B) (fun a => a.2.1) (freeModel (K := K) B).targetD
    (splitAugmentation (K := K) B) rfl (freeModel_basis_lowers (K := K) B) p i j

theorem resolution_minimal (p : ℕ) (i : ResolutionIndex (K := K) B (p+1))
    (j : ResolutionIndex (K := K) B p) :
    (resolutionBasis (K := K) B p).repr ((resolution (K := K) B).complex.d (p+1) p
      (resolutionBasis (K := K) B (p+1) i)) j∈MvPolynomial.idealOfVars V K :=
  (congrArg (fun f : S => f ∈ MvPolynomial.idealOfVars V K)
    (resolution_entry (K := K) B p i j)).mpr (freeModel_minimal B i.val j.val)

/-- An incomparable target shift has zero coefficient in the actual
resolution map. This also rules out a negative weighted shift difference. -/
theorem resolution_entry_zero_of_not_le (p : ℕ)
    (i : ResolutionIndex (K := K) B (p+1)) (j : ResolutionIndex (K := K) B p)
    (hij : ¬j.val.1 ≤ i.val.1) :
    (resolutionBasis (K := K) B p).repr ((resolution (K := K) B).complex.d (p+1) p
      (resolutionBasis (K := K) B (p+1) i)) j = 0 :=
  (resolution_entry (K := K) B p i j).trans
    (freeModel_matrix_zero_of_not_le (K := K) B i.val j.val hij)

/-- Every assignment of variable weights reads the same actual fine
matrix as a weighted homogeneous matrix. -/
theorem resolution_weighted_entry (w : V → ℕ) (p : ℕ)
    (i : ResolutionIndex (K := K) B (p+1)) (j : ResolutionIndex (K := K) B p) :
    ((resolutionBasis (K := K) B p).repr ((resolution (K := K) B).complex.d (p+1) p
      (resolutionBasis (K := K) B (p+1) i)) j).IsWeightedHomogeneous w
        (Finsupp.weight w i.val.1-Finsupp.weight w j.val.1) :=
  (congrArg (fun f : S => f.IsWeightedHomogeneous w
    (Finsupp.weight w i.val.1-Finsupp.weight w j.val.1))
      (resolution_entry (K := K) B p i j)).mpr
        (freeModel_matrix_weighted (K := K) B w i.val j.val)

end FourPapers.Sublattice.MonomialFineResolution

end
end
end

end
