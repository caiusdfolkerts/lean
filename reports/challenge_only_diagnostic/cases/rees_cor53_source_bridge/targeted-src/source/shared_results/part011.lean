module
public import graph_foundation.part012
public import shared_results.part010

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientTensorCoordinates -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid FourPapers.Universal
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
namespace QuotientGroebnerData

def coordinateTensorIndex (P : QuotientGroebnerData V k) (i : ℕ)
    (t : QuotientIndex P.family i) : P.TensorIndex := (t.2,t.1.val)

lemma lift_coefficient_basis (P : QuotientGroebnerData V k) (i : ℕ)
    (t : QuotientIndex P.family i) :
    FourPapers.TensorExteriorKoszul.lift (K := k) (V := V)
        (M := CoefficientQuotient (k := k) P.family) i
      (quotientCoefficientBasis P.family i t)=P.tensorBasis (P.coordinateTensorIndex i t) := by
  rw [quotientCoefficientBasis_apply,FourPapers.TensorExteriorKoszul.lift_single,
    tensorBasis,Module.Basis.tensorProduct_apply',quotientMonomialBasis_apply]
  rfl

lemma tensorEquiv_lift (P : QuotientGroebnerData V k) (i : ℕ)
    (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) :
    P.tensorEquiv (FourPapers.TensorExteriorKoszul.lift (K := k) i z)=
      FourPapers.TensorExteriorKoszul.lift (K := k) i (P.coordinates i z) := by
  have he : P.tensorEquiv.toLinearMap.comp (FourPapers.TensorExteriorKoszul.lift (K := k) i)=
      (FourPapers.TensorExteriorKoszul.lift (K := k) i).comp (P.coordinates i).toLinearMap := by
    apply Finsupp.lhom_ext
    intro F a
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,
      FourPapers.TensorExteriorKoszul.lift_single,coordinates,groebnerKoszulCoordinates,
      Finsupp.mapRange.linearEquiv_apply,Finsupp.mapRange_single,
      tensorEquiv,TensorProduct.congr_tmul,LinearEquiv.refl_apply,coefficientEquiv]
  exact LinearMap.congr_fun he z

lemma tensorDifferential_lift (P : QuotientGroebnerData V k) (i : ℕ)
    (z : Set.powersetCard V (i+1) →₀ CoefficientQuotient (k := k) P.family) :
    P.tensorDifferential (FourPapers.TensorExteriorKoszul.lift (K := k) (i+1) z)=
      FourPapers.TensorExteriorKoszul.lift (K := k) i (P.differential i z) := by
  apply P.tensorEquiv.injective
  rw [P.tensorEquiv_differential,P.tensorEquiv_lift,
    FourPapers.TensorExteriorKoszul.differential_lift,P.tensorEquiv_lift]
  change FourPapers.TensorExteriorKoszul.lift (K := k) i
    (coordinateDifferential (MvPolynomial.X : V → MvPolynomial V k)
      (ModuleCat.of (MvPolynomial V k) (MvPolynomial V k ⧸ P.ideal)) i
        (P.coordinates (i+1) z))=_
  simp only [differential,groebnerQuotientDifferential,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearMap.restrictScalars_apply,coordinates,
    LinearEquiv.apply_symm_apply]

lemma lift_mem_weightFiltration (P : QuotientGroebnerData V k) (w : V → ℕ)
    (i n : ℕ) (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family)
    (hz : z∈(basisFiltration (quotientCoefficientBasis P.family i)
      (fun t => Finsupp.weight w (quotientDegree t))).level n) :
    FourPapers.TensorExteriorKoszul.lift (K := k) i z∈
      (basisFiltration P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))).level n := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t,ht,rfl⟩ := hx
    rw [P.lift_coefficient_basis]
    exact Submodule.subset_span ⟨P.coordinateTensorIndex i t,ht,rfl⟩
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

lemma lift_mem_auxPiece (P : QuotientGroebnerData V k) {A : Type*}
    (deg : Exponent V → A) (a : A) (i : ℕ)
    (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family)
    (hz : z∈Grading.Piece (quotientCoefficientBasis P.family i)
      (fun t => deg (quotientDegree t)) a) :
    FourPapers.TensorExteriorKoszul.lift (K := k) i z∈
      Grading.Piece P.tensorBasis (fun t => deg (P.tensorDegree t)) a := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t,ht,rfl⟩ := hx
    rw [P.lift_coefficient_basis]
    exact Submodule.subset_span ⟨P.coordinateTensorIndex i t,ht,rfl⟩
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

end QuotientGroebnerData
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.TensorCycleLifting -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid FourPapers.Universal
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
namespace QuotientGroebnerData

def tensorWeightFiltration (P : QuotientGroebnerData V k) (w : V → ℕ) :
    FourPapers.FilteredHomology.Filtration (K := k) P.TensorModel :=
  basisFiltration (K := k) (X := P.TensorModel) P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))

def fineCycleLiftSpace (P : QuotientGroebnerData V k) (w : V → ℕ) (α : Exponent V) :
    Submodule k (TotalFaceModule (k := k) (quotientKoszulFaces P.family α)) :=
  FourPapers.cycleLiftSubmodule P.tensorDifferential (P.faceTensorLift α)
    ((P.tensorWeightFiltration w).level (Finsupp.weight w α))

lemma mem_fineCycleLiftSpace_iff (P : QuotientGroebnerData V k) (w : V → ℕ) (α : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α)) :
    x∈P.fineCycleLiftSpace w α ↔ ∃y : P.TensorModel,P.tensorDifferential y=0 ∧
      P.faceTensorLift α x-y∈(P.tensorWeightFiltration w).level (Finsupp.weight w α) :=
  FourPapers.mem_cycleLiftSubmodule_iff ..

lemma faceTensorLift_weight_le (P : QuotientGroebnerData V k) (w : V → ℕ) (α : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α)) :
    P.faceTensorLift α x∈(P.tensorWeightFiltration w).level (Finsupp.weight w α+1) := by
  rw [tensorWeightFiltration,basisFiltration_mem]
  intro t ht
  by_contra hn
  have he : P.tensorDegree t = α :=
    (Grading.mem_piece P.tensorBasis P.tensorDegree α (P.faceTensorLift α x)).mp
      (P.faceTensorLift_fine α x) t hn
  rw [he] at ht
  omega

/-- Actual products of lifts give lifts of the literal projected face product. -/
theorem fineCycleLiftSpace_mul (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀g∈P.generators,g≠0→∀b∈(MvPolynomial.monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (P.order.degree g))
    (α β : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α))
    (y : TotalFaceModule (k := k) (quotientKoszulFaces P.family β))
    (hx : x∈P.fineCycleLiftSpace w α) (hy : y∈P.fineCycleLiftSpace w β) :
    quotientFaceMul P.family α β x y∈P.fineCycleLiftSpace w (α+β) := by
  obtain ⟨x',hdx,hxx⟩ := (P.mem_fineCycleLiftSpace_iff w α x).mp hx
  obtain ⟨y',hdy,hyy⟩ := (P.mem_fineCycleLiftSpace_iff w β y).mp hy
  apply (P.mem_fineCycleLiftSpace_iff w (α+β) _).mpr
  refine ⟨P.tensorMul x' y',P.tensorCycles_mul x' y' hdx hdy,?_⟩
  rw [P.faceTensorLift_mul,map_add]
  exact P.tensorMul_preserves_leading_product w htail (Finsupp.weight w α) (Finsupp.weight w β)
    (P.faceTensorLift α x) x' (P.faceTensorLift β y) y'
    (P.faceTensorLift_weight_le w α x) (P.faceTensorLift_weight_le w β y) hxx hyy

theorem fineCycleLiftSpace_contains_boundaries (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀g∈P.generators,g≠0→∀b∈(MvPolynomial.monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (P.order.degree g))
    (α : Exponent V) :
    LinearMap.range (quotientTotalDifferential P.family α)≤P.fineCycleLiftSpace w α := by
  rintro z ⟨x,rfl⟩
  apply FourPapers.boundary_mem_cycleLiftSubmodule P.tensorDifferential
    (quotientTotalDifferential P.family α) (P.faceTensorLift α)
    ((P.tensorWeightFiltration w).level (Finsupp.weight w α)) P.tensorDifferential_comp
  rw [←P.faceTensorLift_differential]
  have hh := P.tensorDifferential_fine_strict_correction w htail α
    (P.faceTensorLift α x) (P.faceTensorLift_fine α x)
  simpa only [neg_sub] using ((P.tensorWeightFiltration w).level (Finsupp.weight w α)).neg_mem hh

theorem fineCycleLiftSpace_unit (P : QuotientGroebnerData V k) (w : V → ℕ)
    (hzero : QuotientAllowed P.family 0) :
    (⟨quotientFaceProjection P.family 0 (1 : Simplicial.Ambient V k),
        relativeProjection_mem _ _ _ _⟩ :
      TotalFaceModule (k := k) (quotientKoszulFaces P.family 0))∈P.fineCycleLiftSpace w 0 := by
  apply (P.mem_fineCycleLiftSpace_iff w 0 _).mpr
  refine ⟨1,P.tensorDifferential_one hzero,?_⟩
  rw [←faceBasis_empty,P.faceTensorLift_projected_basis 0 ∅
    (by simp [fullKoszulFaces,faceExponent])]
  have he : quotientMonomial (k := k) P.family (0-faceExponent (∅ : Finset V))
      ⊗ₜ[k] Simplicial.basis ∅=(1 : P.TensorModel) := by
    simp [faceExponent,quotientMonomial,faceBasis_empty,Algebra.TensorProduct.one_def]
  rw [he,sub_self]
  exact Submodule.zero_mem _

end QuotientGroebnerData
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientTensorGrading -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
namespace QuotientGroebnerData
variable {A : Type*} [AddCommMonoid A]

def tensorAuxDegree (P : QuotientGroebnerData V k) (deg : V → A) (t : P.TensorIndex) : A × ℤ :=
  (Finsupp.weight deg (P.tensorDegree t),(t.2.card : ℤ))

def tensorAuxShift (a : A × ℤ) : A × ℤ := (a.1,a.2-1)

lemma tensorAuxShift_injective : Function.Injective (tensorAuxShift (A := A)) := by
  intro a b hab
  apply Prod.ext
  · simpa only [tensorAuxShift] using congrArg (fun x : A × ℤ => x.1) hab
  · have hh := congrArg Prod.snd hab
    dsimp only [tensorAuxShift] at hh
    omega

/-- The genuine quotient differential preserves every grading of the
polynomial ideal and lowers the exterior degree by exactly one. -/
theorem tensorDifferential_aux_basis (P : QuotientGroebnerData V k) (deg : V → A)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg)) (t : P.TensorIndex) :
    P.tensorDifferential (P.tensorBasis t)∈Grading.Piece P.tensorBasis (P.tensorAuxDegree deg)
      (tensorAuxShift (P.tensorAuxDegree deg t)) := by
  rw [P.tensorDifferential_basis]
  apply Submodule.sum_mem
  intro v hv
  rw [Simplicial.contraction_basis]
  by_cases ht : v∈t.2
  · rw [if_pos ht,TensorProduct.tmul_smul]
    apply (Submodule.smul_mem_iff' _ (TauCeti.ExteriorAlgebra.basisEraseSign v t.2)).mpr
    rw [Grading.mem_piece]
    intro s hs
    rw [tensorBasis,Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.repr_self,
      Finsupp.single_apply] at hs
    by_cases hface : t.2.erase v=s.2
    · rw [if_pos hface,one_smul] at hs
      rw [coefficientEquiv,groebnerCoefficientEquiv_symm_repr] at hs
      have hnf := groebner_normalForm_homogeneous P.order P.ideal P.generators P.groebner
        P.unitLeading deg hJ (Finsupp.weight deg (t.1.val+Finsupp.single v 1))
        (monomial (t.1.val+Finsupp.single v 1) 1)
        (isWeightedHomogeneous_monomial deg _ _ rfl)
      have ha := hnf hs
      apply Prod.ext
      · change Finsupp.weight deg (s.1.val+faceExponent s.2)=
          Finsupp.weight deg (t.1.val+faceExponent t.2)
        rw [map_add,ha,←map_add,←hface,add_assoc,add_comm (Finsupp.single v 1),
          faceExponent_erase_add ht]
      · change (s.2.card : ℤ)=(t.2.card : ℤ)-1
        rw [←hface,Finset.card_erase_of_mem ht]
        have hpos := Finset.card_pos.mpr ⟨v,ht⟩
        omega
    · rw [if_neg hface,zero_smul] at hs
      exact (hs rfl).elim
  · rw [if_neg ht,TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

theorem tensor_cycle_lift_homogeneous (P : QuotientGroebnerData V k) (deg : V → A)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (w : V → ℕ) (a : A × ℤ) (n : ℕ) (x y : P.TensorModel)
    (hx : x∈Grading.Piece P.tensorBasis (P.tensorAuxDegree deg) a)
    (hy : P.tensorDifferential y=0)
    (herror : x-y∈(FourPapers.Universal.basisFiltration P.tensorBasis
      (fun t => Finsupp.weight w (P.tensorDegree t))).level n) :
    ∃z : P.TensorModel,z∈Grading.Piece P.tensorBasis (P.tensorAuxDegree deg) a ∧
      P.tensorDifferential z=0 ∧
      x-z∈(FourPapers.Universal.basisFiltration P.tensorBasis
        (fun t => Finsupp.weight w (P.tensorDegree t))).level n :=
  FourPapers.homogeneous_cycle_lift P.tensorBasis (P.tensorAuxDegree deg) tensorAuxShift
    tensorAuxShift_injective P.tensorDifferential (P.tensorDifferential_aux_basis deg hJ)
    a {t | Finsupp.weight w (P.tensorDegree t)<n} x y hx hy herror

/-- Transport the unique natural scalar action and equality decision on the
auxiliary grading before applying the homogeneous lifting theorem. -/
theorem tensor_cycle_lift_homogeneous_withNatModule
    [hNat : Module ℕ A] [hDec : DecidableEq A] (P : QuotientGroebnerData V k) (deg : V → A)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (w : V → ℕ) (a : A × ℤ) (n : ℕ) (x y : P.TensorModel)
    (hx : x∈Grading.Piece P.tensorBasis (P.tensorAuxDegree deg) a)
    (hy : P.tensorDifferential y=0)
    (herror : x-y∈(FourPapers.Universal.basisFiltration P.tensorBasis
      (fun t => Finsupp.weight w (P.tensorDegree t))).level n) :
    ∃z : P.TensorModel,z∈Grading.Piece P.tensorBasis (P.tensorAuxDegree deg) a ∧
      P.tensorDifferential z=0 ∧
      x-z∈(FourPapers.Universal.basisFiltration P.tensorBasis
        (fun t => Finsupp.weight w (P.tensorDegree t))).level n := by
  have hd : hDec = Classical.decEq A := Subsingleton.elim _ _
  subst hDec
  have hn : hNat = (AddCommMonoid.toNatModule : Module ℕ A) := Subsingleton.elim _ _
  subst hNat
  exact tensor_cycle_lift_homogeneous P deg hJ w a n x y hx hy herror

/-- Actual homogeneous coordinate preservation with explicit canonical
instances for the auxiliary degree monoid. -/
theorem differential_homogeneous_withNatModule
    [hNat : Module ℕ A] [hDec : DecidableEq A]
    (P : QuotientGroebnerData V k) (deg : V → A)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (a : A) (i : ℕ)
    (x : Set.powersetCard V (i+1) →₀ CoefficientQuotient (k := k) P.family)
    (hx : x ∈ Grading.Piece (quotientCoefficientBasis (k := k) P.family (i+1))
      (fun s => Finsupp.weight deg (quotientDegree s)) a) :
    P.differential i x ∈
      Grading.Piece (quotientCoefficientBasis (k := k) P.family i)
        (fun s => Finsupp.weight deg (quotientDegree s)) a := by
  have hd : hDec = Classical.decEq A := Subsingleton.elim _ _
  subst hDec
  have hn : hNat = (AddCommMonoid.toNatModule : Module ℕ A) := Subsingleton.elim _ _
  subst hNat
  exact groebnerQuotientDifferential_homogeneous P.order P.ideal P.generators
    P.groebner P.unitLeading P.family P.standard deg hJ a i x hx

end QuotientGroebnerData
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphCoordinatePrelude -/
section

/-! # Coordinates shared by the graph cycle-lifting proofs

These are literal coordinate and grading identifications for the quotient
Koszul complex. Keeping them separate from the graph spanning induction
lets the parameter-family proof use the explicit smaller-degree induction
in `ClosedGraphSpanning` without importing a second graph recursion.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid FourPapers.Universal
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [IsDomain k]

namespace QuotientGroebnerData

lemma faceTensorLift_aux_degree (P : QuotientGroebnerData V k)
    {A : Type*} [AddCommMonoid A] (deg : V → A)
    (α : Exponent V) (i : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α))
    (hx : x∈totalFacePiece (quotientKoszulFaces P.family α) i) :
    P.faceTensorLift α x∈Grading.Piece P.tensorBasis (P.tensorAuxDegree deg)
      (Finsupp.weight deg α,(i : ℤ)) := by
  rw [totalFacePiece_eq_basis_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F,hF,rfl⟩ := hx
    have he : P.faceTensorLift α (totalFaceBasis (k := k) (quotientKoszulFaces P.family α) F)=
        P.tensorBasis (P.tensorFineIndexEquiv α F).val := by
      exact P.faceTensorLift_basis_index α F
    rw [he]
    apply Submodule.subset_span
    refine ⟨(P.tensorFineIndexEquiv α F).val,?_,rfl⟩
    apply Prod.ext
    · exact congrArg (Finsupp.weight deg) (P.tensorFineIndexEquiv α F).property
    · exact congrArg (fun n : ℕ => (n : ℤ)) hF
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih


/-- Explicit transport of the unique natural-number action on auxiliary degrees. -/
lemma faceTensorLift_aux_degree_withNatModule (P : QuotientGroebnerData V k)
    {A : Type*} [AddCommMonoid A] [hNat : Module ℕ A] (deg : V → A)
    (α : Exponent V) (i : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α))
    (hx : x∈totalFacePiece (quotientKoszulFaces P.family α) i) :
    P.faceTensorLift α x∈Grading.Piece P.tensorBasis (P.tensorAuxDegree deg)
      (Finsupp.weight deg α,(i : ℤ)) := by
  have he : hNat = (AddCommMonoid.toNatModule : Module ℕ A) := Subsingleton.elim _ _
  subst hNat
  exact P.faceTensorLift_aux_degree deg α i x hx

/-- Forgetting the exterior component of the tensor grading preserves
membership in the literal auxiliary-degree piece. -/
lemma tensorAuxPiece_first (P : QuotientGroebnerData V k)
    {A : Type*} [AddCommMonoid A] (deg : V → A) (a : A) (i : ℤ)
    (Y : P.TensorModel)
    (hY : Y ∈ Grading.Piece P.tensorBasis (P.tensorAuxDegree deg) (a, i)) :
    Y ∈ Grading.Piece P.tensorBasis
      (fun t => Finsupp.weight deg (P.tensorDegree t)) a :=
  piece_regrade P.tensorBasis (P.tensorAuxDegree deg) (a, i) Prod.fst hY

/-- The same projection with an explicitly supplied natural scalar action. -/
lemma tensorAuxPiece_first_withNatModule (P : QuotientGroebnerData V k)
    {A : Type*} [AddCommMonoid A] [hNat : Module ℕ A]
    (deg : V → A) (a : A) (i : ℤ) (Y : P.TensorModel)
    (hY : Y ∈ Grading.Piece P.tensorBasis (P.tensorAuxDegree deg) (a, i)) :
    Y ∈ Grading.Piece P.tensorBasis
      (fun t => Finsupp.weight deg (P.tensorDegree t)) a := by
  have he : hNat = (AddCommMonoid.toNatModule : Module ℕ A) := Subsingleton.elim _ _
  subst hNat
  exact P.tensorAuxPiece_first deg a i Y hY

def coordinateTensorIndexEquiv (P : QuotientGroebnerData V k) (i : ℕ) :
    QuotientIndex P.family i ≃ {t : P.TensorIndex // t.2.card=i} where
  toFun t := ⟨P.coordinateTensorIndex i t,t.1.property⟩
  invFun t := ⟨⟨t.val.2,t.property⟩,t.val.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma coordinateTensorIndex_injective (P : QuotientGroebnerData V k) (i : ℕ) :
    Function.Injective (P.coordinateTensorIndex i) := by
  intro t s h
  apply (P.coordinateTensorIndexEquiv i).injective
  exact Subtype.ext h

/-- Literal fixed-exterior-degree coordinates, with no cycle condition. -/
def coordinateTensorEquiv (P : QuotientGroebnerData V k) (i : ℕ) :
    (Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) ≃ₗ[k]
      Grading.Piece P.tensorBasis (fun t => t.2.card) i :=
  (quotientCoefficientBasis (k := k) P.family i).equiv
    (Grading.restrictedBasis P.tensorBasis (fun t => t.2.card=i))
    (P.coordinateTensorIndexEquiv i)

/-- The coordinate equivalence sends a coefficient basis vector to its
literal tensor basis vector. Keeping the subtype map explicit avoids
normalizing the two equivalent graded-submodule presentations. -/
lemma coordinateTensorEquiv_basis_val (P : QuotientGroebnerData V k) (i : ℕ)
    (t : QuotientIndex P.family i) :
    (P.coordinateTensorEquiv i (quotientCoefficientBasis (k := k) P.family i t)).val =
      P.tensorBasis (P.coordinateTensorIndex i t) := by
  calc
    _ = (Grading.restrictedBasis P.tensorBasis (fun a => a.2.card = i)
          (P.coordinateTensorIndexEquiv i t)).val :=
      congrArg (fun z : Submodule.span k
          (P.tensorBasis '' {a | a.2.card = i}) => z.val)
        (Module.Basis.equiv_apply (quotientCoefficientBasis (k := k) P.family i) t
          (Grading.restrictedBasis P.tensorBasis (fun a => a.2.card = i))
          (P.coordinateTensorIndexEquiv i))
    _ = _ := Grading.restrictedBasis_val P.tensorBasis (fun a => a.2.card = i)
      (P.coordinateTensorIndexEquiv i t)

lemma coordinateTensorEquiv_val (P : QuotientGroebnerData V k) (i : ℕ)
    (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) :
    (P.coordinateTensorEquiv i z).val=FourPapers.TensorExteriorKoszul.lift (K := k) i z := by
  have he : (Grading.Piece P.tensorBasis (fun t => t.2.card) i).subtype.comp
      (P.coordinateTensorEquiv i).toLinearMap=FourPapers.TensorExteriorKoszul.lift (K := k) i := by
    apply (quotientCoefficientBasis (k := k) P.family i).ext
    intro t
    change (P.coordinateTensorEquiv i (quotientCoefficientBasis (k := k) P.family i t)).val=_
    exact (P.coordinateTensorEquiv_basis_val i t).trans (P.lift_coefficient_basis i t).symm
  exact LinearMap.congr_fun he z

lemma lift_repr (P : QuotientGroebnerData V k) (i : ℕ)
    (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family)
    (t : QuotientIndex P.family i) :
    P.tensorBasis.repr (FourPapers.TensorExteriorKoszul.lift (K := k) i z)
      (P.coordinateTensorIndex i t)=(quotientCoefficientBasis (k := k) P.family i).repr z t := by
  have he : (P.tensorBasis.coord (P.coordinateTensorIndex i t)).comp
      (FourPapers.TensorExteriorKoszul.lift (K := k) i)=
        (quotientCoefficientBasis (k := k) P.family i).coord t := by
    apply (quotientCoefficientBasis (k := k) P.family i).ext
    intro s
    simp only [LinearMap.comp_apply,Module.Basis.coord_apply,P.lift_coefficient_basis,
      Module.Basis.repr_self,Finsupp.single_apply]
    simp only [show P.coordinateTensorIndex i s=P.coordinateTensorIndex i t ↔ s=t from
      (P.coordinateTensorIndex_injective i).eq_iff]
  exact LinearMap.congr_fun he z

lemma lift_mem_weightFiltration_iff (P : QuotientGroebnerData V k) (w : V → ℕ)
    (i n : ℕ) (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) :
    FourPapers.TensorExteriorKoszul.lift (K := k) i z∈
      (basisFiltration (K := k) P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))).level n ↔
    z∈(basisFiltration (K := k) (quotientCoefficientBasis (k := k) P.family i)
      (fun t => Finsupp.weight w (quotientDegree t))).level n := by
  constructor
  · intro hz
    rw [basisFiltration_mem] at hz ⊢
    intro t ht
    rw [←P.lift_repr]
    exact hz (P.coordinateTensorIndex i t) ht
  · exact P.lift_mem_weightFiltration w i n z

lemma lift_mem_auxPiece_iff (P : QuotientGroebnerData V k) {A : Type*}
    (deg : Exponent V → A) (a : A) (i : ℕ)
    (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) P.family) :
    FourPapers.TensorExteriorKoszul.lift (K := k) i z∈
      Grading.Piece P.tensorBasis (fun t => deg (P.tensorDegree t)) a ↔
    z∈Grading.Piece (quotientCoefficientBasis (k := k) P.family i)
      (fun t => deg (quotientDegree t)) a := by
  constructor
  · intro hz
    rw [Grading.mem_piece] at hz ⊢
    intro t ht
    exact hz (P.coordinateTensorIndex i t) (by simpa only [P.lift_repr] using ht)
  · exact P.lift_mem_auxPiece deg a i z

end QuotientGroebnerData

variable {N : ℕ} {G : SimpleGraph (Fin N)}

lemma graphEdgeFamily_zero_allowed (G : SimpleGraph (Fin N)) :
    QuotientAllowed (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (0 : Exponent (FiniteVariable.{u} (GraphRows N))) := by
  rintro ⟨b,hb,hle⟩
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  have hh := degree_mono hle
  simp only [finiteRowExponent_degree,map_zero] at hh
  omega

def GraphRectangle.unrestrictedFace {A : ∀r,Finset (Fin (GraphRows N r))}
    (R : GraphRectangle.{u} G A) :
    TotalFaceModule (k := k) (quotientKoszulFaces
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) R.fineDegree) :=
  ⟨R.vector,rectangleFaceVector_mem _ R.X R.Y R.disjoint
    (fun x _ => graphEdgeFamily_no_linear G x)⟩

def graphRectangleListFace (G : SimpleGraph (Fin N))
    (L : List (GraphRectangle.{u} G (fun _ => Finset.univ))) :
    TotalFaceModule (k := k) (quotientKoszulFaces
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) (graphRectangleListDegree L)) :=
  ⟨quotientFaceProjection (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphRectangleListDegree L) (graphRectangleListVector L),relativeProjection_mem _ _ _ _⟩

lemma graphRectangleListFace_cons (R : GraphRectangle.{u} G (fun _ => Finset.univ))
    (L : List (GraphRectangle.{u} G (fun _ => Finset.univ))) :
    graphRectangleListFace (k := k) G (R::L)=
      quotientFaceMul (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        R.fineDegree (graphRectangleListDegree L) R.unrestrictedFace (graphRectangleListFace G L) := by
  apply Subtype.ext
  change quotientFaceProjection (k := k) _ (R.fineDegree+graphRectangleListDegree L)
    (R.vector*graphRectangleListVector L)=
      quotientFaceProjection (k := k) _ (R.fineDegree+graphRectangleListDegree L)
        (R.vector*quotientFaceProjection (k := k) _ (graphRectangleListDegree L) (graphRectangleListVector L))
  exact (quotientFaceProjection_mul_right _ _ _
    (Submodule.span_mono (Set.image_mono (fun _ h => h.1)) R.unrestrictedFace.property)
    (graphRectangleListVector_full (k := k) L)).symm

lemma quotientDifferential_basis_fine {V : Type u} [Fintype V] [LinearOrder V]
    (B : Family V) (p : ℕ) (t : QuotientIndex B (p+1)) :
    quotientDifferential (k := k) B p (quotientCoefficientBasis (k := k) B (p+1) t)∈
      Grading.Piece (quotientCoefficientBasis (k := k) B p) quotientDegree (quotientDegree t) :=
  quotientDifferential_homogeneous (k := k) B (quotientDegree t) p
    (Grading.basis_mem_piece _ _ t)

lemma quotientDifferential_basis_regrade {V : Type u} [Fintype V] [LinearOrder V]
    {A : Type*} (B : Family V) (deg : Exponent V → A) (p : ℕ)
    (t : QuotientIndex B (p+1)) :
    quotientDifferential (k := k) B p (quotientCoefficientBasis (k := k) B (p+1) t)∈
      Grading.Piece (quotientCoefficientBasis (k := k) B p) (fun s => deg (quotientDegree s))
        (deg (quotientDegree t)) :=
  piece_regrade _ _ _ deg (quotientDifferential_basis_fine (k := k) B p t)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphParameterLifting -/
section

/-! # Integral cycle lifting in the displayed graph family

The coefficient ring may be `ℤ[z]`. Rectangle cycles are first lifted inside
their complete interval clique, using the proved linear-colon fillings there.
The literal quotient map transfers the lift to the graph. Multiplication and
the full rectangle spanning theorem then lift every fine cycle. Finally the
actual auxiliary and exterior grading projections retain all degrees.

No equality of Betti numbers or freeness of the family homology is a premise.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {N : ℕ} {k : Type u} [CommRing k] [IsDomain k]

local instance : DecidableEq (FiniteVariable.{u} (GraphRows N)) :=
  (inferInstance : LinearOrder (FiniteVariable.{u} (GraphRows N))).toDecidableEq

def graphParameterQuotientData (t : k) (ht : t ≠ 0)
    (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G) :
    QuotientGroebnerData (FiniteVariable.{u} (GraphRows N)) k where
  order := graphLexOrder
  ideal := graphParameterIdeal t G
  generators := graphParameterGenerators t G
  groebner := closedGraph_parameter_groebner t ht hG
  unitLeading := graphParameterGenerators_unit_leading t ht G
  family := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
  standard := closedGraph_parameter_standardMonomials t ht hG

theorem graphParameter_clique_linear_cycle_lift (t : k) (ht : t ≠ 0) (l r : Fin N)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ)
    (hα : α.degree = p + 2) (n : ℕ)
    (z : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))))
    (hza : z ∈ Grading.Piece (quotientCoefficientBasis (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun a => Finsupp.weight graphVertexRowDegree (quotientDegree a))
      (Finsupp.weight graphVertexRowDegree α))
    (hzw : z ∈ Grading.Piece (quotientCoefficientBasis (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a)) n)
    (hdz : quotientDifferential (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) p z = 0) :
    let P := graphParameterQuotientData t ht (intervalCliqueGraph l r)
      (intervalCliqueGraph_closed l r)
    ∃ y : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
        CoefficientQuotient (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))),
      y ∈ Grading.Piece (quotientCoefficientBasis (k := k) P.family (p+1))
      (fun a => Finsupp.weight graphVertexRowDegree (quotientDegree a))
      (Finsupp.weight graphVertexRowDegree α) ∧ P.differential p y = 0 ∧
      z-y ∈ (basisFiltration (K := k) (quotientCoefficientBasis (k := k) P.family (p+1))
        (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))).level n := by
  exact groebnerIntervalClique_linear_cycle_lift_withNatModule
    (A := (Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))
    (hNat := (inferInstance : Module ℕ ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    (hDec := (inferInstance : DecidableEq ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ)))) l r graphLexOrder
    (graphParameterIdeal t (intervalCliqueGraph l r))
    (graphParameterGenerators t (intervalCliqueGraph l r))
    (closedGraph_parameter_groebner t ht (intervalCliqueGraph_closed l r))
    (graphParameterGenerators_unit_leading t ht (intervalCliqueGraph l r))
    (closedGraph_parameter_standardMonomials t ht (intervalCliqueGraph_closed l r))
    graphDiagonalWeight (graphParameterGenerators_weight_tails t ht (intervalCliqueGraph l r))
    graphVertexRowDegree (graphParameterIdeal_vertexRow_homogeneous t (intervalCliqueGraph l r))
    (Finsupp.weight graphVertexRowDegree α) p
    (fun β hβ => (graphVertexRowDegree_eq_total β α hβ).trans hα) n z hza hzw hdz

variable {G : SimpleGraph (Fin N)}

lemma GraphRectangle.parameter_cliqueIdeal_le
    {A : ∀ r, Finset (Fin (GraphRows N r))} (R : GraphRectangle.{u} G A)
    (hG : IntervalLabeling G) (t : k) :
    graphParameterIdeal t (intervalCliqueGraph R.lowerVertex R.upperVertex) ≤
      graphParameterIdeal t G := by
  apply Ideal.span_le.mpr
  rintro f ⟨i, j, hij, hadj, rfl⟩
  exact Ideal.subset_span (graphParameterBinomial_mem t hij (R.interval_le hG hadj))

/-- The specified rectangle lifts in the actual parameter quotient, not
merely in an abstract filtered complex with the same initial differential. -/
theorem GraphRectangle.parameter_cycle_lift
    {A : ∀ r, Finset (Fin (GraphRows N r))} (R : GraphRectangle.{u} G A)
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0)
    (p : ℕ) (hcard : R.X.card + R.Y.card = p + 2) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    let z := rectangleCoordinate (k := k) P.family R.X R.Y p R.disjoint hcard
      (fun x _ => graphEdgeFamily_no_linear G x)
    ∃ y, y ∈ Grading.Piece (quotientCoefficientBasis (k := k) P.family (p+1))
      (fun a => Finsupp.weight graphVertexRowDegree (quotientDegree a))
      (Finsupp.weight graphVertexRowDegree R.fineDegree) ∧ P.differential p y = 0 ∧
      z-y ∈ (basisFiltration (K := k) (quotientCoefficientBasis (k := k) P.family (p+1))
        (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))).level
          (Finsupp.weight graphDiagonalWeight R.fineDegree) := by
  let H := intervalCliqueGraph R.lowerVertex R.upperVertex
  let P := graphParameterQuotientData t ht H (intervalCliqueGraph_closed _ _)
  let Q := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  let hPQ : P.ideal ≤ Q.ideal := R.parameter_cliqueIdeal_le hG t
  let zP := rectangleCoordinate (k := k) P.family R.X R.Y p R.disjoint hcard
    (fun x _ => graphEdgeFamily_no_linear H x)
  have hdeg : R.fineDegree.degree = p + 2 :=
    (rectangleFaceDegree_degree R.X R.Y R.disjoint).trans hcard
  obtain ⟨y, hya, hdy, herr⟩ := graphParameter_clique_linear_cycle_lift t ht
    R.lowerVertex R.upperVertex R.fineDegree p hdeg
    (Finsupp.weight graphDiagonalWeight R.fineDegree) zP
    (rectangleCoordinate_regraded (k := k) (Finsupp.weight graphVertexRowDegree)
      P.family R.X R.Y p R.disjoint hcard _)
    (rectangleCoordinate_regraded (k := k) (Finsupp.weight graphDiagonalWeight)
      P.family R.X R.Y p R.disjoint hcard _)
    (rectangleCoordinate_closed (k := k) P.family R.X R.Y p R.disjoint hcard _
      R.inInterval.edge_contains_unrestricted)
  have hzw := rectangleCoordinate_regraded (k := k) (Finsupp.weight graphDiagonalWeight)
    P.family R.X R.Y p R.disjoint hcard (fun x _ => graphEdgeFamily_no_linear H x)
  have hh := P.koszulFactor_transfers_lift_withNatModule
    (hNat := (inferInstance : Module ℕ ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    (hDec := (inferInstance : DecidableEq ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ)))) Q hPQ graphVertexRowDegree
    (graphParameterIdeal_vertexRow_homogeneous t G) graphDiagonalWeight
    (graphParameterGenerators_weight_tails t ht G) p
    (Finsupp.weight graphDiagonalWeight R.fineDegree)
    (Finsupp.weight graphVertexRowDegree R.fineDegree) zP y hzw hya hdy herr
  refine ⟨P.koszulFactor Q hPQ (p+1) y, hh.1, hh.2.1, ?_⟩
  have he := initialKoszulFactor_rectangle P Q R.X R.Y p R.disjoint hcard
    (fun x _ => graphEdgeFamily_no_linear H x) (fun x _ => graphEdgeFamily_no_linear G x)
  have herr' := hh.2.2
  dsimp only [zP] at herr'
  rw [he] at herr'
  exact herr' 

theorem GraphRectangle.parameter_tensor_cycle_lift
    {A : ∀ r, Finset (Fin (GraphRows N r))} (R : GraphRectangle.{u} G A)
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) :
    R.unrestrictedFace (k := k) ∈
      (graphParameterQuotientData t ht G (intervalLabeling_closed hG)).fineCycleLiftSpace
        graphDiagonalWeight R.fineDegree := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  let p := R.X.card + R.Y.card - 2
  have hcard : R.X.card + R.Y.card = p + 2 := by
    have hx := Finset.card_pos.mpr R.nonemptyX
    have hy := Finset.card_pos.mpr R.nonemptyY
    dsimp only [p]
    omega
  let z := rectangleCoordinate (k := k) P.family R.X R.Y p R.disjoint hcard
    (fun x _ => graphEdgeFamily_no_linear G x)
  obtain ⟨y, _, hdy, herr⟩ := R.parameter_cycle_lift hG t ht p hcard
  apply (P.mem_fineCycleLiftSpace_iff graphDiagonalWeight R.fineDegree _).mpr
  refine ⟨FourPapers.TensorExteriorKoszul.lift (K := k)
        (V := FiniteVariable.{u} (GraphRows N))
        (M := CoefficientQuotient (k := k) P.family) (p+1) y, ?_, ?_⟩
  · rw [P.tensorDifferential_lift p y, hdy, map_zero]
  · let zc : Simplicial.Chains (k := k) (quotientKoszulFaces P.family R.fineDegree) (p+1) :=
      ⟨R.vector, by
        have hc : R.X.card + R.Y.card - 1 = p + 1 := by omega
        simpa only [GraphRectangle.vector, GraphRectangle.fineDegree, hc] using rectangleFaceVector_chains (k := k) P.family R.X R.Y R.disjoint
          (fun x _ => graphEdgeFamily_no_linear G x)⟩
    have he : P.faceTensorLift R.fineDegree R.unrestrictedFace =
        FourPapers.TensorExteriorKoszul.lift (K := k)
        (V := FiniteVariable.{u} (GraphRows N))
        (M := CoefficientQuotient (k := k) P.family) (p+1) z :=
      P.faceTensorLift_degree R.fineDegree (p+1) zc
    rw [he, ← map_sub]
    exact P.lift_mem_weightFiltration graphDiagonalWeight (p+1)
      (Finsupp.weight graphDiagonalWeight R.fineDegree) (z-y) herr

theorem graphParameterRectangleList_lifts (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0)
    (L : List (GraphRectangle.{u} G (fun _ => Finset.univ))) :
    graphRectangleListFace (k := k) G L ∈
      (graphParameterQuotientData t ht G (intervalLabeling_closed hG)).fineCycleLiftSpace
        graphDiagonalWeight (graphRectangleListDegree L) := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  induction L with
  | nil => exact P.fineCycleLiftSpace_unit graphDiagonalWeight (graphEdgeFamily_zero_allowed G)
  | cons R L ih =>
    rw [graphRectangleListFace_cons]
    exact P.fineCycleLiftSpace_mul graphDiagonalWeight (graphParameterGenerators_weight_tails t ht G)
      R.fineDegree (graphRectangleListDegree L) R.unrestrictedFace (graphRectangleListFace G L)
      (R.parameter_tensor_cycle_lift hG t ht) ih

lemma closedGraphProduct_eq_projectedList
    (L : List (GraphRectangle.{u} G (fun _ => Finset.univ))) :
    closedGraphProduct (k := k) (graphRectangleListDegree L) ⟨L, rfl⟩ =
      graphRectangleListFace (k := k) G L := by
  apply Subtype.ext
  change graphRectangleListVector L = quotientFaceProjection (k := k) _ _ (graphRectangleListVector L)
  exact (relativeProjection_eq_self
    (closedGraphProduct (k := k) (graphRectangleListDegree L) ⟨L, rfl⟩).property).symm

theorem graphParameterRectangleSpan_lifts (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    closedGraphProductSpan (k := k) G α ≤
      (graphParameterQuotientData t ht G (intervalLabeling_closed hG)).fineCycleLiftSpace
        graphDiagonalWeight α := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨L, hL⟩, rfl⟩
  subst α
  rw [closedGraphProduct_eq_projectedList]
  exact graphParameterRectangleList_lifts hG t ht L

/-- All fine cycles lift integrally in the literal parameter family. -/
theorem intervalGraph_parameter_fine_cycle_lift (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0)
    (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (x : TotalFaceModule (k := k) (quotientKoszulFaces
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α))
    (hx : quotientTotalDifferential (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α x = 0) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    ∃ y : P.TensorModel, P.tensorDifferential y = 0 ∧
      P.faceTensorLift α x-y ∈ (P.tensorWeightFiltration graphDiagonalWeight).level
        (Finsupp.weight graphDiagonalWeight α) := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  apply (P.mem_fineCycleLiftSpace_iff graphDiagonalWeight α x).mp
  exact (sup_le (graphParameterRectangleSpan_lifts hG t ht α)
    (P.fineCycleLiftSpace_contains_boundaries graphDiagonalWeight
      (graphParameterGenerators_weight_tails t ht G) α))
    (closedGraph_quotient_cycles_generated hG α hx)

theorem intervalGraph_parameter_homogeneous_cycle_lift
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (i : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α))
    (hxi : x ∈ totalFacePiece _ i)
    (hx : quotientTotalDifferential (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α x = 0) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    ∃ y : P.TensorModel, y ∈ Grading.Piece P.tensorBasis (P.tensorAuxDegree graphVertexRowDegree)
      (Finsupp.weight graphVertexRowDegree α, (i : ℤ)) ∧ P.tensorDifferential y = 0 ∧
      P.faceTensorLift α x-y ∈ (P.tensorWeightFiltration graphDiagonalWeight).level
        (Finsupp.weight graphDiagonalWeight α) := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  obtain ⟨y, hy, herr⟩ := intervalGraph_parameter_fine_cycle_lift hG t ht α x hx
  exact P.tensor_cycle_lift_homogeneous_withNatModule
    (hNat := (inferInstance : Module ℕ ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    (hDec := (inferInstance : DecidableEq ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    graphVertexRowDegree
    (graphParameterIdeal_vertexRow_homogeneous t G) graphDiagonalWeight
    (Finsupp.weight graphVertexRowDegree α, (i : ℤ))
    (Finsupp.weight graphDiagonalWeight α) (P.faceTensorLift α x) y
    (P.faceTensorLift_aux_degree_withNatModule
      (hNat := (inferInstance : Module ℕ ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
      graphVertexRowDegree α i x hxi) hy herr

/-- Fixed exterior-degree coordinates of the actual family quotient
Koszul complex. Both vertex/row degree and the complete leading vector are
preserved, over the integral parameter ring as well as over fields. -/
theorem intervalGraph_parameter_coordinate_cycle_lift
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ)
    (z : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)))
    (hz : z ∈ quotientPiece (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α (p+1))
    (hdz : quotientDifferential (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) p z = 0) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    ∃ y : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
        CoefficientQuotient (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)),
      y ∈ Grading.Piece (quotientCoefficientBasis (k := k) P.family (p+1))
      (fun a => Finsupp.weight graphVertexRowDegree (quotientDegree a))
      (Finsupp.weight graphVertexRowDegree α) ∧ P.differential p y = 0 ∧
      z-y ∈ (basisFiltration (K := k) (quotientCoefficientBasis (k := k) P.family (p+1))
        (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))).level
          (Finsupp.weight graphDiagonalWeight α) := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  let zP : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k) P.family := z
  have hzP : zP ∈ quotientPiece (k := k) P.family α (p+1) := hz
  have hdzP : quotientDifferential (k := k) P.family p zP = 0 := hdz
  change ∃ y : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k) P.family,
    y ∈ Grading.Piece (quotientCoefficientBasis (k := k) P.family (p+1))
      (fun a => Finsupp.weight graphVertexRowDegree (quotientDegree a))
      (Finsupp.weight graphVertexRowDegree α) ∧ P.differential p y = 0 ∧
    zP-y ∈ (basisFiltration (K := k) (quotientCoefficientBasis (k := k) P.family (p+1))
      (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))).level
        (Finsupp.weight graphDiagonalWeight α)
  let xf := (quotientFaceHomogeneousEquiv (k := k) P.family α (p+1)).symm ⟨zP, hzP⟩
  let x : TotalFaceModule (k := k) (quotientKoszulFaces P.family α) :=
    ⟨xf.val, chains_mem_basisSpan xf.property⟩
  have hxi : x ∈ totalFacePiece (quotientKoszulFaces P.family α) (p+1) := xf.property
  have hxval : P.faceTensorLift α x = FourPapers.TensorExteriorKoszul.lift (K := k)
        (V := FiniteVariable.{u} (GraphRows N))
        (M := CoefficientQuotient (k := k) P.family) (p+1) zP := by
    rw [P.faceTensorLift_degree]
    simp only [xf, LinearEquiv.apply_symm_apply]
  have hdx : quotientTotalDifferential (k := k) P.family α x = 0 := by
    apply P.faceTensorLift_injective α
    rw [map_zero, ← P.faceTensorLift_differential, hxval,
      P.initialTensorDifferential_lift p zP, hdzP, map_zero]
  obtain ⟨Y, hYdegree, hDY, herr⟩ :=
    intervalGraph_parameter_homogeneous_cycle_lift hG t ht α (p+1) x hxi hdx
  have hYcard : Y ∈ Grading.Piece P.tensorBasis (fun a => a.2.card) (p+1) := by
    apply Submodule.span_mono (Set.image_mono (fun a ha => ?_)) hYdegree
    have hh := congrArg Prod.snd ha
    change (a.2.card : ℤ) = ((p+1 : ℕ) : ℤ) at hh
    exact_mod_cast hh
  let y := (P.coordinateTensorEquiv (p+1)).symm ⟨Y, hYcard⟩
  have hyval : FourPapers.TensorExteriorKoszul.lift (K := k)
        (V := FiniteVariable.{u} (GraphRows N))
        (M := CoefficientQuotient (k := k) P.family) (p+1) y = Y := by
    rw [← P.coordinateTensorEquiv_val]
    exact congrArg Subtype.val ((P.coordinateTensorEquiv (p+1)).apply_symm_apply ⟨Y, hYcard⟩)
  refine ⟨y, ?_, ?_, ?_⟩
  · apply (P.lift_mem_auxPiece_iff (Finsupp.weight graphVertexRowDegree)
      (Finsupp.weight graphVertexRowDegree α) (p+1) y).mp
    rw [hyval]
    exact P.tensorAuxPiece_first_withNatModule
      (hNat := (inferInstance : Module ℕ ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
      graphVertexRowDegree (Finsupp.weight graphVertexRowDegree α) ((p+1 : ℕ) : ℤ) Y hYdegree
  · apply FourPapers.TensorExteriorKoszul.lift_injective (K := k)
      (V := FiniteVariable.{u} (GraphRows N))
      (M := CoefficientQuotient (k := k) P.family) p
    rw [map_zero, ← P.tensorDifferential_lift, hyval]
    exact hDY
  · apply (P.lift_mem_weightFiltration_iff graphDiagonalWeight (p+1)
      (Finsupp.weight graphDiagonalWeight α) (zP-y)).mp
    rw [map_sub, hyval, ← hxval]
    exact herr

theorem graphParameterIdeal_total_homogeneous (t : k) (G : SimpleGraph (Fin N)) :
    (graphParameterIdeal t G).IsHomogeneous
      (weightedHomogeneousSubmodule k (1 : FiniteVariable.{u} (GraphRows N) → ℕ)) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i, j, _, _, rfl⟩
  refine ⟨2, (isWeightedHomogeneous_monomial _ _ (1 : k) ?_).sub
    (isWeightedHomogeneous_monomial _ _ (t ^ (j.val-i.val)) ?_)⟩
  all_goals simp [graphPairExponent, Finsupp.weight_single]

def graphOrdinaryCoordinatePiece (G : SimpleGraph (Fin N)) (q i : ℕ) :=
  Grading.Piece (quotientCoefficientBasis (k := k)
    (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) i)
    (fun a => (quotientDegree a).degree) q

def graphOrdinaryCoordinateBasis (G : SimpleGraph (Fin N)) (q i : ℕ) :=
  Grading.restrictedBasis (quotientCoefficientBasis (k := k)
    (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) i)
    (fun a => (quotientDegree a).degree = q)

def graphOrdinaryFiltration (G : SimpleGraph (Fin N)) (q i : ℕ) :
    Filtration (K := k) (graphOrdinaryCoordinatePiece (k := k) G q i) :=
  basisFiltration (K := k) (X := graphOrdinaryCoordinatePiece (k := k) G q i)
    (graphOrdinaryCoordinateBasis (k := k) G q i)
    (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a.val))

lemma graphParameterDifferential_ordinary (t : k) (ht : t ≠ 0) (hG : ClosedLabeling G)
    (q p : ℕ)
    (x : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)))
    (hx : x ∈ graphOrdinaryCoordinatePiece (k := k) G q (p+1)) :
    (graphParameterQuotientData t ht G hG).differential p x ∈
      graphOrdinaryCoordinatePiece (k := k) G q p := by
  change (graphParameterQuotientData t ht G hG).differential p x ∈
    Grading.Piece (quotientCoefficientBasis (k := k)
      (graphParameterQuotientData t ht G hG).family p)
      (fun a => (quotientDegree a).degree) q
  have hx' : x ∈ Grading.Piece (quotientCoefficientBasis (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) (p+1))
      (fun a => Finsupp.weight (1 : FiniteVariable.{u} (GraphRows N) → ℕ)
        (quotientDegree a)) q := by
    simpa only [graphOrdinaryCoordinatePiece, Finsupp.degree_eq_weight_one, Pi.one_def] using hx
  have hh := (graphParameterQuotientData t ht G hG).differential_homogeneous_withNatModule
    (hNat := (inferInstance : Module ℕ ℕ)) (hDec := (inferInstance : DecidableEq ℕ))
    (1 : FiniteVariable.{u} (GraphRows N) → ℕ)
    (graphParameterIdeal_total_homogeneous t G) q p x hx'
  simpa only [graphOrdinaryCoordinatePiece, Finsupp.degree_eq_weight_one, Pi.one_def] using hh

lemma graphInitialDifferential_ordinary (G : SimpleGraph (Fin N)) (q p : ℕ)
    (x : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)))
    (hx : x ∈ graphOrdinaryCoordinatePiece (k := k) G q (p+1)) :
    quotientDifferential (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) p x ∈
      graphOrdinaryCoordinatePiece (k := k) G q p :=
  map_mem_piece_of_basis _ _ _ _ _
    (quotientDifferential_basis_regrade (k := k) _ Finsupp.degree p) q hx

def graphParameterOrdinaryDifferential (t : k) (ht : t ≠ 0) (hG : ClosedLabeling G)
    (q p : ℕ) :
    graphOrdinaryCoordinatePiece (k := k) G q (p+1) →ₗ[k] graphOrdinaryCoordinatePiece (k := k) G q p :=
  basisSpanMap (quotientCoefficientBasis (k := k) _ (p+1)) (quotientCoefficientBasis (k := k) _ p)
    (fun a => (quotientDegree a).degree = q) (fun a => (quotientDegree a).degree = q)
    ((graphParameterQuotientData t ht G hG).differential p)
    (graphParameterDifferential_ordinary t ht hG q p)

def graphInitialOrdinaryDifferential (G : SimpleGraph (Fin N)) (q p : ℕ) :
    graphOrdinaryCoordinatePiece (k := k) G q (p+1) →ₗ[k] graphOrdinaryCoordinatePiece (k := k) G q p :=
  basisSpanMap (quotientCoefficientBasis (k := k) _ (p+1)) (quotientCoefficientBasis (k := k) _ p)
    (fun a => (quotientDegree a).degree = q) (fun a => (quotientDegree a).degree = q)
    (quotientDifferential (k := k) _ p) (graphInitialDifferential_ordinary (k := k) G q p)

/-- The actual fixed ordinary-degree differential lifts all its leading
cycles over the parameter domain. This is the precise hypothesis required
by the integral filtered-homology comparison. -/
theorem intervalGraph_parameter_filtered_cycle_lifts
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) (q p : ℕ) :
    LiftsCycles (graphOrdinaryFiltration (k := k) G q (p+1))
      (graphOrdinaryFiltration (k := k) G q p)
      (graphParameterOrdinaryDifferential t ht (intervalLabeling_closed hG) q p) := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  apply basisLeadingCycles_liftsCycles_on_span
    (quotientCoefficientBasis (k := k) P.family (p+1)) (quotientCoefficientBasis (k := k) P.family p)
    (fun a => (quotientDegree a).degree = q) (fun a => (quotientDegree a).degree = q)
    (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))
    (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))
    (P.differential p) (quotientDifferential (k := k) P.family p)
    (graphParameterDifferential_ordinary t ht (intervalLabeling_closed hG) q p)
    (graphInitialDifferential_ordinary (k := k) G q p)
  · exact quotientDifferential_basis_regrade (k := k) P.family (Finsupp.weight graphDiagonalWeight) p
  · exact groebnerQuotientDifferential_strictly_lowers P.order P.ideal P.generators
      P.groebner P.unitLeading P.family P.standard graphDiagonalWeight
      (graphParameterGenerators_weight_tails t ht G) p
  · intro n x hxq hxn hdx
    apply fineCycleLifting_assemble_two_gradings
      (quotientCoefficientBasis (k := k) P.family (p+1)) (quotientCoefficientBasis (k := k) P.family p)
      quotientDegree quotientDegree Finsupp.degree (Finsupp.weight graphDiagonalWeight)
      q n (P.differential p) (quotientDifferential (k := k) P.family p)
      (quotientDifferential_basis_fine (k := k) P.family p)
      ((basisFiltration (K := k) (quotientCoefficientBasis (k := k) P.family (p+1))
        (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))).level n)
      ?_ x hxq hxn hdx
    intro α hαq hαn z hz hdz
    obtain ⟨y, hya, hDy, herr⟩ := intervalGraph_parameter_coordinate_cycle_lift hG t ht α p z hz hdz
    refine ⟨y, ?_, hDy, by simpa only [hαn] using herr⟩
    apply Submodule.span_mono (Set.image_mono (fun a ha => ?_)) hya
    exact (graphVertexRowDegree_eq_total (quotientDegree a) α ha).trans hαq

lemma graphDiagonalWeight_le (v : FiniteVariable.{u} (GraphRows N)) :
    graphDiagonalWeight v ≤ N := by
  unfold graphDiagonalWeight
  split_ifs <;> omega

lemma graphDiagonalWeight_exponent_le (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Finsupp.weight graphDiagonalWeight α ≤ N * α.degree := by
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add α β ihα ihβ =>
      simpa only [map_add, Nat.mul_add] using Nat.add_le_add ihα ihβ
  | single v n =>
      simpa only [Finsupp.weight_single, Finsupp.degree_single, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
        using Nat.mul_le_mul_left n (graphDiagonalWeight_le v)

/-- An explicit common upper bound on the variable-weight filtration in
every fixed ordinary degree, independent of the coefficient parameter. -/
theorem graphOrdinaryFiltration_top (G : SimpleGraph (Fin N)) (q p : ℕ) :
    (graphOrdinaryFiltration (k := k) G q p).level (N*q+1) = ⊤ := by
  apply top_unique
  intro x _
  rw [graphOrdinaryFiltration, basisFiltration_mem]
  intro a ha
  have hb := graphDiagonalWeight_exponent_le (quotientDegree a.val)
  rw [a.property] at hb
  omega

theorem graphOrdinaryCoordinatePiece_free (G : SimpleGraph (Fin N)) (q p : ℕ) :
    Module.Free k (graphOrdinaryCoordinatePiece (k := k) G q p) :=
  Module.Free.of_basis (graphOrdinaryCoordinateBasis (k := k) G q p)

theorem graphOrdinaryCoordinatePiece_finite (G : SimpleGraph (Fin N)) (q p : ℕ) :
    Module.Finite k (graphOrdinaryCoordinatePiece (k := k) G q p) := by
  let B := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
  let I := {a : QuotientIndex B p // (quotientDegree a).degree = q}
  let Q := {a : Exponent (FiniteVariable.{u} (GraphRows N)) // a.degree ≤ q}
  letI : Finite Q := (Finsupp.finite_of_degree_le q).to_subtype
  have hb (a : I) : a.val.2.val.degree ≤ q := by
    exact (degree_mono (le_add_of_nonneg_right zero_le :
      a.val.2.val ≤ quotientDegree a.val)).trans_eq a.property
  let f : I → Q × Set.powersetCard (FiniteVariable.{u} (GraphRows N)) p :=
    fun a => (⟨a.val.2.val, hb a⟩, a.val.1)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Sigma.ext (congrArg Prod.snd hab)
    exact heq_of_eq (Subtype.ext (congrArg (fun z : Q ×
      Set.powersetCard (FiniteVariable.{u} (GraphRows N)) p => z.1.val) hab))
  letI : Finite I := Finite.of_injective f hf
  exact Module.Finite.of_basis (graphOrdinaryCoordinateBasis (k := k) G q p)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealCycleLifting -/
section

/-! # The graph instance of the filtered ideal connecting argument -/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

section Graph
variable [IsDomain k] {N : ℕ} {G : SimpleGraph (Fin N)}

/-- Full-coordinate quotient cycle lifting, before fixing an ordinary
degree. The finite fine-degree decomposition assembles the graph lifts. -/
theorem intervalGraph_parameter_quotient_coordinate_lifts
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) (p : ℕ) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    LiftsCycles (quotientCoordinateFiltration P.family graphDiagonalWeight (p+1))
      (quotientCoordinateFiltration P.family graphDiagonalWeight p) (P.differential p) := by
  let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
  apply basisLeadingCycles_liftsCycles (quotientCoefficientBasis P.family (p+1))
    (quotientCoefficientBasis P.family p)
    (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))
    (fun a => Finsupp.weight graphDiagonalWeight (quotientDegree a))
    (P.differential p) (quotientDifferential P.family p)
    (quotientDifferential_basis_regraded P.family (Finsupp.weight graphDiagonalWeight) p)
    (groebnerQuotientDifferential_strictly_lowers P.order P.ideal P.generators
      P.groebner P.unitLeading P.family P.standard graphDiagonalWeight
      (graphParameterGenerators_weight_tails t ht G) p)
  intro n x hx hdx
  have hunit : x ∈ Grading.Piece (quotientCoefficientBasis P.family (p+1))
      (fun _ => ()) () := by
    apply (quotientCoefficientBasis P.family (p+1)).mem_span_image.mpr
    intro a _
    rfl
  obtain ⟨y, _, hDy, herr⟩ := fineCycleLifting_assemble_two_gradings
    (quotientCoefficientBasis P.family (p+1)) (quotientCoefficientBasis P.family p)
    quotientDegree quotientDegree (fun _ => ()) (Finsupp.weight graphDiagonalWeight)
    () n (P.differential p) (quotientDifferential P.family p)
    (quotientDifferential_basis_fine P.family p)
    ((quotientCoordinateFiltration P.family graphDiagonalWeight (p+1)).level n)
    (by
      intro α _ hαn z hz hdz
      obtain ⟨y, _, hDy, herr⟩ := intervalGraph_parameter_coordinate_cycle_lift hG t ht α p z hz hdz
      let yP : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
          CoefficientQuotient (k := k) P.family := y
      have hDyP : P.differential p yP = 0 := hDy
      refine ⟨yP, ?_, hDyP, ?_⟩
      · apply (quotientCoefficientBasis (k := k) P.family (p+1)).mem_span_image.mpr
        intro a _
        rfl
      · have herr' : z-yP ∈
            (quotientCoordinateFiltration (k := k) P.family graphDiagonalWeight (p+1)).level
              (Finsupp.weight graphDiagonalWeight α) := herr
        simpa only [hαn] using herr') x hunit hx hdx
  exact ⟨y, hDy, herr⟩

/-- Actual leading-cycle lifts in the kernel of the polynomial quotient
map. Every exterior degree is included, in particular ideal homology degree
zero. The next equivalence identifies this kernel with the literal ideal. -/
theorem intervalGraph_parameter_kernel_cycle_lifts
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) (p : ℕ) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    LiftsCycles
      (kernelFiltration (quotientCoordinateFiltration ∅ graphDiagonalWeight p)
        (ambientKoszulProjection P p))
      (kernelFiltration (quotientCoordinateFiltration ∅ graphDiagonalWeight p.pred)
        (ambientKoszulProjection P p.pred)) (ambientKernelDifferential P p) :=
  ambientKernel_cycle_lifts _ (graphEdgeFamily_zero_allowed G) graphDiagonalWeight
    (graphParameterGenerators_weight_tails t ht G) p
    (intervalGraph_parameter_quotient_coordinate_lifts hG t ht p)

end Graph
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealCoordinates -/
section

/-! # First-power coordinate lifts for the actual graph parameter ideal -/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- First-power leading-cycle lifting for the literal parameter ideal,
with its actual variable-multiplication Koszul differential. The theorem
includes all exterior degrees, including zero. -/
theorem intervalGraph_parameter_ideal_coordinate_lifts [IsDomain k]
    {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    (t : k) (ht : t ≠ 0) (p : ℕ) :
    let P := graphParameterQuotientData t ht G (intervalLabeling_closed hG)
    LiftsCycles (actualIdealCoordinateFiltration P graphDiagonalWeight p)
      (actualIdealCoordinateFiltration P graphDiagonalWeight p.pred)
      (actualIdealPreviousDifferential P.ideal p) :=
  actualIdealCoordinate_lifts_of_kernel _ graphDiagonalWeight
    (graphParameterGenerators_weight_tails t ht G) p
    (intervalGraph_parameter_kernel_cycle_lifts hG t ht p)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialCoordinateTor -/
section

/-! # Polynomial Tor in the literal coefficient Koszul coordinates

This includes homological degree zero, where the outgoing map is explicitly
zero.  The comparison starts from Mathlib's actual derived `Tor` functor.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.PolynomialCoordinateTor

open Classical CategoryTheory CommAlg CommAlg.Koszul FilteredHomology

universe u
variable {K V M : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  [AddCommGroup M] [Module (MvPolynomial V K) M] [Module K M]
  [IsScalarTower K (MvPolynomial V K) M]

abbrev Coordinates (p : ℕ) := Set.powersetCard V p →₀ M

def differential (p : ℕ) : Coordinates (V:=V) (M:=M) (p+1) →ₗ[K] Coordinates (V:=V) (M:=M) p :=
  (coordinateDifferential (MvPolynomial.X : V → MvPolynomial V K)
    (ModuleCat.of (MvPolynomial V K) M) p).restrictScalars K

def previous : ∀ p : ℕ, Coordinates (V:=V) (M:=M) p →ₗ[K] Coordinates (V:=V) (M:=M) p.pred
  | 0 => 0
  | p+1 => differential p

theorem differential_comp (p : ℕ) :
    (differential (K:=K) (V:=V) (M:=M) p).comp (differential (p+1))=0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (coordinateDifferential_comp
    (MvPolynomial.X : V → MvPolynomial V K) (ModuleCat.of (MvPolynomial V K) M) p) x

theorem previous_comp (p : ℕ) :
    (previous (K:=K) (V:=V) (M:=M) p).comp (differential p)=0 := by
  cases p with
  | zero => exact LinearMap.zero_comp _
  | succ p => exact differential_comp p

abbrev Homology (p : ℕ) := FilteredHomology.Homology
  (differential (K:=K) (V:=V) (M:=M) p) (previous p) (previous_comp p)

def complex : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of K (Coordinates (V:=V) (M:=M) p))
    (fun p => ModuleCat.ofHom (differential p))
    (fun p => ModuleCat.hom_ext (differential_comp p))

@[simp] theorem complex_d (p : ℕ) :
    (complex (K:=K) (V:=V) (M:=M)).d (p+1) p = ModuleCat.ofHom (differential p) := by
  simp only [complex,ChainComplex.of_d]

theorem complex_previous (p : ℕ) :
    (complex (K:=K) (V:=V) (M:=M)).d p p.pred = ModuleCat.ofHom (previous p) := by
  cases p with
  | zero =>
    change ChainComplex.of.d
      (fun p => ModuleCat.of K (Coordinates (V:=V) (M:=M) p))
      (fun p => ModuleCat.ofHom (differential (K:=K) p)) 0 0 = 0
    exact ChainComplex.of_d_ne _ _ (by decide)
  | succ p => exact complex_d p

def tensorIso : complex (K:=K) (V:=V) (M:=M) ≅
    TensorExteriorKoszul.complex (K:=K) (M:=M) (MvPolynomial.X : V → MvPolynomial V K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (TensorExteriorKoszul.pieceCoordinates (K:=K) (M:=M) p).symm.toModuleIso)
    (by
      intro i j hij
      obtain rfl : i=j+1 := hij.symm
      simp only [complex_d,TensorExteriorKoszul.complex,ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change TensorExteriorKoszul.pieceDifferential (K:=K)
          (MvPolynomial.X : V → MvPolynomial V K) j
          ((TensorExteriorKoszul.pieceCoordinates (K:=K) (V:=V) (M:=M) (j+1)).symm x) =
        (TensorExteriorKoszul.pieceCoordinates (K:=K) (V:=V) (M:=M) j).symm
          (differential j x)
      simp only [TensorExteriorKoszul.pieceDifferential,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,differential])

def shortComplexIso (p : ℕ) :
    (complex (K:=K) (V:=V) (M:=M)).sc' (p+1) p p.pred ≅
      linearShortComplex (differential (K:=K) (V:=V) (M:=M) p) (previous p) (previous_comp p) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by change (𝟙 _) ≫ ModuleCat.ofHom (differential p) =
          complex.d (p+1) p ≫ (𝟙 _)
        simp only [Category.id_comp,Category.comp_id,complex_d])
    (by change (𝟙 _) ≫ ModuleCat.ofHom (previous p) =
          complex.d p p.pred ≫ (𝟙 _)
        simp only [Category.id_comp,Category.comp_id,complex_previous])

def complexHomologyIso (p : ℕ) :
    (complex (K:=K) (V:=V) (M:=M)).homology p ≅ ModuleCat.of K (Homology (K:=K) (V:=V) (M:=M) p) :=
  (complex.homologyIsoSc' (p+1) p p.pred (by simp) (by cases p <;> simp)) ≪≫
    ShortComplex.homologyMapIso (shortComplexIso p) ≪≫
    categoricalHomologyIso (differential p) (previous p) (previous_comp p)

abbrev Tor (p : ℕ) :=
  (ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))).obj
    (((CategoryTheory.Tor (ModuleCat (MvPolynomial V K)) p).obj
      (ModuleCat.of (MvPolynomial V K) M)).obj
        (residueCoefficientModule (V:=V) (k:=K)))

/-- The exact argument order is `Tor^S(M,K)` with evaluation-at-zero on K. -/
def torIso (p : ℕ) : Tor (K:=K) (V:=V) (M:=M) p ≅
    ModuleCat.of K (Homology (K:=K) (V:=V) (M:=M) p) :=
  TensorExteriorKoszul.polynomialTorIso p ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat K) (ComplexShape.down ℕ) p).mapIso
      tensorIso.symm ≪≫ complexHomologyIso p

end FourPapers.PolynomialCoordinateTor

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.OrdinaryIdealTor -/
section

/-! # Ordinary graded pieces of the genuine derived Tor of an ideal

The ordinary Koszul homology embeds in the full homology by the actual
coordinate inclusion. Injectivity is proved by projecting a polynomial
boundary filling to its prescribed ordinary degree. Its image under the
proved derived-functor comparison is the ordinary graded Tor submodule.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CategoryTheory CommAlg CommAlg.Koszul MvPolynomial FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

/-- Give the induced map an explicit name before specializing injectivity.
This keeps the actual quotient map fixed while applying boundary reflection. -/
private theorem namedThreeTermHomologyMap_injective
    {K X Y Z X' Y' Z' : Type*} [CommRing K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] [AddCommGroup X'] [Module K X']
    [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
    (a : X →ₗ[K] X') (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
    (hf : ∀ x, b (f x) = f' (a x))
    (hg : ∀ y, c (g y) = g' (b y))
    (L : Homology f g hfg → Homology f' g' hfg')
    (hL : ∀ z, L z = threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg z)
    (hreflect : ∀ y, g y = 0 → (∃ x', f' x' = b y) → ∃ x, f x = y) :
    Function.Injective L := by
  have he : L = fun z => threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg z :=
    funext hL
  rw [he]
  exact threeTermHomologyMap_injective_of_reflects_boundaries
    f g hfg f' g' hfg' a b c hf hg hreflect

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

abbrev actualIdealCoordinateHomology (p : ℕ) :=
  PolynomialCoordinateTor.Homology (K:=K) (V:=V) (M:=P.ideal) p

-- Pin the literal kernel structures before constructing quotient maps.  The
-- instances are the canonical submodule structures, with no new assumptions.
local instance ordinaryCyclesAddCommGroup (q p : ℕ) :
    AddCommGroup (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)) :=
  Submodule.addCommGroup (R := K) (M := actualIdealOrdinaryPiece P q p)
    (module_M := inferInstance) (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p))

local instance ordinaryCyclesModule (q p : ℕ) :
    Module K (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)) :=
  Submodule.module (R := K) (M := actualIdealOrdinaryPiece P q p)
    (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p))

local instance coordinateCyclesAddCommGroup (J : Ideal (MvPolynomial V K)) (p : ℕ) :
    AddCommGroup (LinearMap.ker
      (PolynomialCoordinateTor.previous (K := K) (V := V) (M := J) p)) :=
  Submodule.addCommGroup (R := K) (M := Set.powersetCard V p →₀ J)
    (module_M := inferInstance) (LinearMap.ker
      (PolynomialCoordinateTor.previous (K := K) (V := V) (M := J) p))

local instance coordinateCyclesModule (J : Ideal (MvPolynomial V K)) (p : ℕ) :
    Module K (LinearMap.ker
      (PolynomialCoordinateTor.previous (K := K) (V := V) (M := J) p)) :=
  Submodule.module (R := K) (M := Set.powersetCard V p →₀ J)
    (LinearMap.ker (PolynomialCoordinateTor.previous (K := K) (V := V) (M := J) p))

theorem ordinaryIdealDifferential_toPolynomialCoordinates (q p : ℕ)
    (x : actualIdealOrdinaryPiece P q (p+1)) :
    (actualIdealOrdinaryDifferential P hJ q p x).val =
      PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=P.ideal) p x.val := rfl

theorem ordinaryIdealPrevious_toPolynomialCoordinates (q p : ℕ)
    (x : actualIdealOrdinaryPiece P q p) :
    (actualIdealOrdinaryPrevious P hJ q p x).val =
      PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=P.ideal) p x.val := by
  cases p <;> rfl

section

attribute [local irreducible] actualIdealOrdinaryDifferential actualIdealOrdinaryPrevious
  PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous

set_option backward.isDefEq.respectTransparency true in
/-- The induced homology map uses the three literal homogeneous-coordinate
inclusions. Explicit module types keep the quotient construction local. -/
def ordinaryIdealHomologyInclusion (q p : ℕ) :
    actualIdealOrdinaryHomology P hJ q p →ₗ[K] actualIdealCoordinateHomology P p :=
  threeTermHomologyMap (K:=K)
    (X:=actualIdealOrdinaryPiece P q (p+1))
    (Y:=actualIdealOrdinaryPiece P q p)
    (Z:=actualIdealOrdinaryPiece P q p.pred)
    (X':=Set.powersetCard V (p+1) →₀ P.ideal)
    (Y':=Set.powersetCard V p →₀ P.ideal)
    (Z':=Set.powersetCard V p.pred →₀ P.ideal)
    (actualIdealOrdinaryDifferential P hJ q p)
    (actualIdealOrdinaryPrevious P hJ q p)
    (actualIdealOrdinaryDifferential_comp P hJ q p)
    (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=P.ideal) p)
    (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=P.ideal) p)
    (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=P.ideal) p)
    (actualIdealOrdinaryPiece P q (p+1)).subtype
    (actualIdealOrdinaryPiece P q p).subtype
    (actualIdealOrdinaryPiece P q p.pred).subtype
    (ordinaryIdealDifferential_toPolynomialCoordinates P hJ q p)
    (ordinaryIdealPrevious_toPolynomialCoordinates P hJ q p)

end

/-- Projecting a genuine ambient boundary filling to its ordinary degree
keeps its differential and gives a filling in the homogeneous component. -/
theorem ordinaryIdeal_boundary_reflects (q p : ℕ)
    (z : actualIdealOrdinaryPiece P q p)
    (a : Set.powersetCard V (p+1) →₀ P.ideal)
    (ha : PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=P.ideal) p a = z.val) :
    ∃ y, actualIdealOrdinaryDifferential P hJ q p y = z := by
  let y : actualIdealOrdinaryPiece P q (p+1) :=
    ⟨Grading.projection (actualIdealCoefficientBasis P (p+1))
      (fun b => (actualIdealDegree b).degree) q a, Grading.projection_mem _ _ _ _⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hc := LinearMap.congr_fun (fineProjection_commutes (R:=K)
    (X:=Set.powersetCard V (p+1) →₀ P.ideal)
    (Y:=Set.powersetCard V p →₀ P.ideal)
    (I:=ActualIdealIndex P (p+1)) (J:=ActualIdealIndex P p) (Γ:=ℕ)
    (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
    (fun b => (actualIdealDegree b).degree) (fun b => (actualIdealDegree b).degree)
    (actualIdealCoordinateDifferential P.ideal p)
    (fun b => actualIdealCoordinateDifferential_ordinary P hJ _ p _
      (Grading.basis_mem_piece _ _ b)) q) a
  change actualIdealCoordinateDifferential P.ideal p
    (Grading.projection _ _ q a) =
      Grading.projection _ _ q (actualIdealCoordinateDifferential P.ideal p a) at hc
  change actualIdealCoordinateDifferential P.ideal p a = z.val at ha
  change actualIdealCoordinateDifferential P.ideal p
    (Grading.projection _ _ q a) = z.val
  rw [hc, ha, Grading.projection_eq_self z.property]

section
attribute [local irreducible] actualIdealOrdinaryDifferential actualIdealOrdinaryPrevious
  PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous
  ordinaryIdealHomologyInclusion

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 250000 in
set_option diagnostics true in
/-- The homogeneous boundary-filling property proves injectivity of the
actual induced quotient map. -/
theorem ordinaryIdealHomologyInclusion_injective (q p : ℕ) :
    Function.Injective (ordinaryIdealHomologyInclusion P hJ q p) := by
  unfold ordinaryIdealHomologyInclusion
  apply threeTermHomologyMap_injective_of_reflects_boundaries
  intro z _ hz
  obtain ⟨a, ha⟩ := hz
  exact ordinaryIdeal_boundary_reflects P hJ q p z a ha

end

abbrev actualIdealTor (p : ℕ) :=
  PolynomialCoordinateTor.Tor (K:=K) (V:=V) (M:=P.ideal) p

/-- Map actual ordinary homogeneous cycle classes into the standard
derived `Tor^S_p(J,K)`. The map is induced by literal Koszul inclusion. -/
def ordinaryIdealHomologyToTor (q p : ℕ) :
    actualIdealOrdinaryHomology P hJ q p →ₗ[K] actualIdealTor P p :=
  ((PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=P.ideal) p).toLinearEquiv.symm.toLinearMap).comp
    (ordinaryIdealHomologyInclusion P hJ q p)

theorem ordinaryIdealHomologyToTor_injective (q p : ℕ) :
    Function.Injective (ordinaryIdealHomologyToTor P hJ q p) :=
  (PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=P.ideal) p).toLinearEquiv.symm.injective.comp
    (ordinaryIdealHomologyInclusion_injective P hJ q p)

/-- The ordinary degree-q submodule of the actual derived Tor object.
Its cycles have the standard polynomial-plus-exterior degree, as proved
by `actualIdealOrdinaryPiece_mem_iff`. -/
def ordinaryIdealGradedTor (q p : ℕ) : Submodule K (actualIdealTor P p) :=
  LinearMap.range (ordinaryIdealHomologyToTor P hJ q p)

def ordinaryIdealGradedTorEquiv (q p : ℕ) :
    actualIdealOrdinaryHomology P hJ q p ≃ₗ[K] ordinaryIdealGradedTor P hJ q p :=
  LinearEquiv.ofInjective (ordinaryIdealHomologyToTor P hJ q p)
    (ordinaryIdealHomologyToTor_injective P hJ q p)

end FourPapers.Sublattice

namespace FourPapers.Sublattice

open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

def ordinaryIdealBettiNumber (p q : ℕ) : ℕ :=
  Module.finrank K (ordinaryIdealGradedTor P hJ q p)

theorem ordinaryIdealBettiNumber_eq_finrank (p q : ℕ) :
    ordinaryIdealBettiNumber P hJ p q = Module.finrank K (actualIdealOrdinaryHomology P hJ q p) :=
  (ordinaryIdealGradedTorEquiv P hJ q p).finrank_eq.symm

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SymbolicFiniteBridge -/
section

/-! # Exact variable transport for the symbolic and homological constructions

The symbolic proof uses `Σ r, Fin (n r)`, while the Koszul constructions use
the universe lift `FiniteVariable n`.  The explicit renaming below identifies
their polynomial rings, row generators, ideals, powers and Rees algebras.
Monomial orders are transported rather than replaced by a preferred order.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

open Classical MvPolynomial
open scoped MonomialOrder

variable {V W K : Type*}

/-- Pull a monomial order back along an actual bijection of variables. -/
def monomialOrderReindex (e : V ≃ W) (m : MonomialOrder W) : MonomialOrder V where
  syn := m.syn
  toSyn := (Finsupp.mapDomain.linearEquiv (R := ℕ) (M := ℕ) e).toAddEquiv.trans m.toSyn
  toSyn_monotone := by
    intro a b hab
    change m.toSyn (a.mapDomain e) ≤ m.toSyn (b.mapDomain e)
    exact m.toSyn_monotone (Finsupp.mapDomain_mono hab)

@[simp] theorem monomialOrderReindex_toSyn (e : V ≃ W) (m : MonomialOrder W)
    (a : V →₀ ℕ) :
    (monomialOrderReindex e m).toSyn a = m.toSyn (a.mapDomain e) := rfl

@[simp] theorem monomialOrderReindex_symm_toSyn (e : V ≃ W) (m : MonomialOrder V)
    (a : V →₀ ℕ) :
    (monomialOrderReindex e.symm m).toSyn (a.mapDomain e) = m.toSyn a := by
  rw [monomialOrderReindex_toSyn]
  congr 1
  exact (Finsupp.mapDomain.linearEquiv (R := ℕ) (M := ℕ) e).symm_apply_apply a

variable [CommRing K]

/-- Leading-term ideals commute with a variable renaming that carries the
given order. The statement concerns the actual ideals, not just their bases. -/
theorem initialIdeal_rename (e : V ≃ W) (m : MonomialOrder V) (m' : MonomialOrder W)
    (hm : ∀ a b : V →₀ ℕ, a ≼[m] b ↔ a.mapDomain e ≼[m'] b.mapDomain e)
    (J : Ideal (MvPolynomial V K)) :
    Ideal.map (MvPolynomial.rename e).toRingHom (initialIdeal m J) =
      initialIdeal m' (Ideal.map (MvPolynomial.rename e).toRingHom J) := by
  rw [initialIdeal, initialIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨MvPolynomial.rename e p, Ideal.mem_map_of_mem _ hp, ?_⟩
    exact m'.leadingTerm_rename hm p
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (MvPolynomial.rename e).toRingHom
        (MvPolynomial.renameEquiv K e).surjective).mp hp
    exact ⟨m.leadingTerm q, ⟨q, hq, rfl⟩, (m'.leadingTerm_rename hm q).symm⟩

end FourPapers

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped MonomialOrder

universe u v
variable {d : ℕ} (n : Fin d → ℕ) {K : Type v} [CommRing K]

def finiteLabelPolynomialEquiv :
    MvPolynomial (FiniteVariable.{u} n) K ≃ₐ[K]
      MvPolynomial (RowCutNetwork.Label n) K :=
  MvPolynomial.renameEquiv K (finiteVariableEquiv n)

theorem finiteRowExponent_rename (a : FiniteTuple n) :
    (finiteRowExponent n a).mapDomain (finiteVariableEquiv n) =
      RowCutNetwork.exponent n a := by
  simp only [finiteRowExponent, RowCutNetwork.exponent, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single]
  rfl

theorem finiteRowMonomial_rename (a : FiniteTuple n) :
    finiteLabelPolynomialEquiv (K := K) n (finiteRowMonomial n a) =
      monomial (RowCutNetwork.exponent n a) 1 := by
  rw [finiteRowMonomial_eq_monomial]
  change MvPolynomial.rename (finiteVariableEquiv n) (monomial (finiteRowExponent n a) 1) = _
  rw [MvPolynomial.rename_monomial, finiteRowExponent_rename]

/-- The two modules use exactly the same monomial ideal under the displayed
variable bijection; the universe lift introduces no variables. -/
theorem finiteSublatticeIdeal_rename (E : Finset (FiniteTuple n)) :
    Ideal.map (finiteLabelPolynomialEquiv (K := K) n).toRingHom
      (finiteSublatticeIdeal n E) = RowCutNetwork.monomialIdeal n K E := by
  rw [finiteSublatticeIdeal, Ideal.map_span, RowCutNetwork.monomialIdeal]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (finiteRowMonomial_rename n a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨finiteRowMonomial n a, ⟨a, ha, rfl⟩, finiteRowMonomial_rename n a⟩

theorem finiteSublatticeIdeal_power_rename (E : Finset (FiniteTuple n)) (s : ℕ) :
    Ideal.map (finiteLabelPolynomialEquiv (K := K) n).toRingHom
      ((finiteSublatticeIdeal n E) ^ s) = (RowCutNetwork.monomialIdeal n K E) ^ s := by
  rw [Ideal.map_pow, finiteSublatticeIdeal_rename]

def finiteSublatticeReesRename (E : Finset (FiniteTuple n)) :
    coefficientRees (finiteSublatticeIdeal n (k := K) E) ≃ₐ[K]
      coefficientRees (RowCutNetwork.monomialIdeal n K E) :=
  coefficientReesCongr _ _ (finiteLabelPolynomialEquiv n)
    (finiteSublatticeIdeal_rename n E)

end FourPapers.Sublattice

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped MonomialOrder

universe u v
variable {d : ℕ} (n : Fin d → ℕ) {K : Type v} [Field K]

/-- The all-power initial-ideal theorem in precisely the variable type used
by the Koszul and closed-graph formalizations, for the original arbitrary
monomial order and every power. -/
theorem finite_initialIdeal_power_eq
    (m : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal m J = finiteSublatticeIdeal n E) (s : ℕ) :
    initialIdeal m (J ^ s) = (finiteSublatticeIdeal n E) ^ s := by
  let e := finiteLabelPolynomialEquiv (K := K) n
  let m' := monomialOrderReindex (finiteVariableEquiv n).symm m
  have hm : ∀ a b : FiniteVariable.{u} n →₀ ℕ,
      a ≼[m] b ↔ a.mapDomain (finiteVariableEquiv n) ≼[m']
        b.mapDomain (finiteVariableEquiv n) := by
    intro a b
    simp only [m', monomialOrderReindex_symm_toSyn]
  have hinit' : initialIdeal m' (Ideal.map e.toRingHom J) =
      RowCutNetwork.monomialIdeal n K E := by
    change initialIdeal m' (Ideal.map (MvPolynomial.rename (finiteVariableEquiv n)).toRingHom J) = _
    rw [← initialIdeal_rename (finiteVariableEquiv n) m m' hm J, hinit]
    exact finiteSublatticeIdeal_rename n E
  have hs := RowCutNetwork.initialIdeal_power_eq n m'
    (Ideal.map e.toRingHom J) E hE.1 hE.2 hinit' s
  apply e.toRingEquiv.idealComapOrderIso.symm.injective
  change Ideal.map e.toRingHom (initialIdeal m (J ^ s)) =
    Ideal.map e.toRingHom ((finiteSublatticeIdeal n E) ^ s)
  have hmap : Ideal.map e.toRingHom (initialIdeal m (J ^ s)) =
      initialIdeal m' (Ideal.map e.toRingHom (J ^ s)) := by
    change Ideal.map (MvPolynomial.rename (finiteVariableEquiv n)).toRingHom
      (initialIdeal m (J ^ s)) =
      initialIdeal m' (Ideal.map (MvPolynomial.rename (finiteVariableEquiv n)).toRingHom (J ^ s))
    exact initialIdeal_rename (finiteVariableEquiv n) m m' hm (J ^ s)
  rw [hmap, Ideal.map_pow, finiteSublatticeIdeal_power_rename]
  exact hs

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteReesCoefficientEquiv -/
section

/-! # Identifying the two actual presentations of the Rees algebra

The finite presentation image inside `k[t,x]` and the coefficientwise Rees
subalgebra of `k[x][t]` are related by Mathlib's ordinary polynomial-variable
equivalence. The proof below verifies the restriction on every monomial of
every actual ideal power.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial

universe u
variable {K : Type u} [CommRing K]
  {d : ℕ} {n : Fin d → ℕ} (E : Finset (FiniteTuple n))

def finitePowerIdealEquiv (s : ℕ) :
    monomialIdeal K (exponentPowerFamily (finiteRowFamily n E) s) ≃ₗ[K]
      idealPowerPiece (finiteSublatticeIdeal n (k := K) E) s where
  toFun x := ⟨x.val, by
    change x.val ∈ (finiteSublatticeIdeal n (k := K) E) ^ s
    rw [← finitePowerFamily_ideal (n := n) E s]
    exact x.property⟩
  invFun x := ⟨x.val, by rw [finitePowerFamily_ideal (n := n) E s]; exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finitePowerMonomialBasis (s : ℕ) :
    Module.Basis {a : Exponent (FiniteVariable.{u} n) //
      Contains (exponentPowerFamily (finiteRowFamily n E) s) a} K
      (idealPowerPiece (finiteSublatticeIdeal n (k := K) E) s) :=
  (monomialBasis (k := K) (exponentPowerFamily (finiteRowFamily n E) s)).map
    (finitePowerIdealEquiv (K := K) E s)

@[simp] theorem finitePowerMonomialBasis_val (s : ℕ)
    (a : {a : Exponent (FiniteVariable.{u} n) //
      Contains (exponentPowerFamily (finiteRowFamily n E) s) a}) :
    (finitePowerMonomialBasis (K := K) E s a).val = monomial a.val 1 := by
  rw [finitePowerMonomialBasis, Module.Basis.map_apply]
  exact monomialBasis_val _ a

abbrev FiniteCoefficientReesIndex := Σ s : ℕ,
  {a : Exponent (FiniteVariable.{u} n) // Contains (exponentPowerFamily (finiteRowFamily n E) s) a}

def finiteCoefficientReesBasis : Module.Basis (FiniteCoefficientReesIndex.{u} E) K
    (coefficientRees (finiteSublatticeIdeal n (k := K) E)) :=
  gradedCoefficientBasis (idealPowerPiece (finiteSublatticeIdeal n (k := K) E))
    (idealPowerPiece_one _) (idealPowerPiece_mul _) (finitePowerMonomialBasis (K := K) E)

theorem finiteCoefficientReesBasis_val (a : FiniteCoefficientReesIndex.{u} E) :
    (finiteCoefficientReesBasis (K := K) E a).val = AddMonoidAlgebra.single a.1 (monomial a.2.val 1) := by
  rw [finiteCoefficientReesBasis, gradedCoefficientBasis_apply, coefficientSingle_val,
    finitePowerMonomialBasis_val]

def finiteCoefficientReesIndexEquiv : FiniteCoefficientReesIndex.{u} E ≃ finiteReesExponentMonoid.{u} E :=
  (Equiv.sigmaCongrRight (fun s => (finiteReesPowerIndexEquiv (E := E) s).symm)).trans
    (Equiv.sigmaFiberEquiv (fun a : finiteReesExponentMonoid.{u} E => a.val none))

@[simp] theorem finiteCoefficientReesIndexEquiv_symm_fst (a : finiteReesExponentMonoid.{u} E) :
    ((finiteCoefficientReesIndexEquiv E).symm a).1 = a.val none := rfl

@[simp] theorem finiteCoefficientReesIndexEquiv_symm_val (a : finiteReesExponentMonoid.{u} E) :
    ((finiteCoefficientReesIndexEquiv E).symm a).2.val = finiteReesFineExponent a := rfl

def finiteReesCoefficientLinearEquiv : finiteReesImage E K ≃ₗ[K]
    coefficientRees (finiteSublatticeIdeal n (k := K) E) :=
  (finiteReesImageBasis E K).equiv (finiteCoefficientReesBasis (K := K) E)
    (finiteCoefficientReesIndexEquiv E).symm

@[simp] theorem finiteReesCoefficientLinearEquiv_basis (a : finiteReesExponentMonoid.{u} E) :
    finiteReesCoefficientLinearEquiv (K := K) E (finiteReesImageBasis E K a) =
      finiteCoefficientReesBasis (K := K) E ((finiteCoefficientReesIndexEquiv E).symm a) :=
  Module.Basis.equiv_apply _ a _ _

def optionPolynomialCoefficientEquiv :
    MvPolynomial (Option (FiniteVariable.{u} n)) K ≃ₐ[K]
      AddMonoidAlgebra (MvPolynomial (FiniteVariable.{u} n) K) ℕ :=
  (MvPolynomial.optionEquivLeft K (FiniteVariable.{u} n)).trans
    ((Polynomial.toFinsuppIsoAlg (MvPolynomial (FiniteVariable.{u} n) K)).restrictScalars K)

theorem optionPolynomialCoefficientEquiv_monomial (a : finiteReesExponentMonoid.{u} E) :
    optionPolynomialCoefficientEquiv (K := K) (n := n) (monomial a.val 1) =
      AddMonoidAlgebra.single (a.val none) (monomial (finiteReesFineExponent a) 1) := by
  change ((MvPolynomial.optionEquivLeft K (FiniteVariable.{u} n)) (monomial a.val 1)).toFinsupp = _
  rw [MvPolynomial.optionEquivLeft_monomial, Polynomial.toFinsupp_monomial]
  congr 2

/-- On every polynomial, the constructed module equivalence is exactly the
ordinary change from `k[t,x]` to coefficient lists in `k[x][t]`. -/
theorem finiteReesCoefficientLinearEquiv_val (x : finiteReesImage E K) :
    (finiteReesCoefficientLinearEquiv (K := K) E x).val =
      optionPolynomialCoefficientEquiv (K := K) (n := n) x.val := by
  have he : (coefficientRees (finiteSublatticeIdeal n (k := K) E)).val.toLinearMap.comp
        (finiteReesCoefficientLinearEquiv (K := K) E).toLinearMap =
      (optionPolynomialCoefficientEquiv (K := K) (n := n)).toLinearMap.comp
        (finiteReesImage E K).val.toLinearMap := by
    apply (finiteReesImageBasis E K).ext
    intro a
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
      Subalgebra.val_apply, AlgEquiv.toLinearMap_apply,
      finiteReesCoefficientLinearEquiv_basis, finiteCoefficientReesBasis_val,
      finiteCoefficientReesIndexEquiv_symm_fst, finiteCoefficientReesIndexEquiv_symm_val,
      finiteReesImageBasis_val, optionPolynomialCoefficientEquiv_monomial]
  exact LinearMap.congr_fun he x

def finiteReesCoefficientEquiv : finiteReesImage E K ≃ₐ[K]
    coefficientRees (finiteSublatticeIdeal n (k := K) E) :=
  AlgEquiv.ofLinearEquiv (finiteReesCoefficientLinearEquiv (K := K) E)
    (by
      apply Subtype.ext
      rw [finiteReesCoefficientLinearEquiv_val, OneMemClass.coe_one, map_one]
      rfl)
    (by
      intro x y
      apply Subtype.ext
      rw [finiteReesCoefficientLinearEquiv_val, Subalgebra.coe_mul, map_mul,
        Subalgebra.coe_mul, finiteReesCoefficientLinearEquiv_val,
        finiteReesCoefficientLinearEquiv_val])

@[simp] theorem finiteReesCoefficientEquiv_val (x : finiteReesImage E K) :
    (finiteReesCoefficientEquiv (K := K) E x).val =
      optionPolynomialCoefficientEquiv (K := K) (n := n) x.val :=
  finiteReesCoefficientLinearEquiv_val E x

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.TensorExteriorRename -/
section

/-! # Renaming the actual tensor Koszul complex

The exterior map is the functorial map of exterior algebras. Its signs are
retained as integral units relative to the chosen ordered face bases.
The resulting coordinate maps commute with the actual variable-action
differential and retain every exterior degree, including degree zero.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.TensorExteriorKoszul

open Classical CommAlg CommAlg.Koszul MvPolynomial CategoryTheory
open scoped TensorProduct

universe u
variable {K V W : Type u} [CommRing K]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  (e : V ≃ W)

def vectorRename : (V → K) ≃ₗ[K] (W → K) :=
  LinearEquiv.funCongrLeft K K e.symm

@[simp] theorem vectorRename_basis (v : V) :
    vectorRename (K := K) e (Pi.basisFun K V v) = Pi.basisFun K W (e v) := by
  ext w
  change (Pi.basisFun K V v) (e.symm w) = (Pi.basisFun K W (e v)) w
  simp only [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    simpa only [Equiv.apply_symm_apply] using congrArg e h
  · intro h
    simpa only [Equiv.symm_apply_apply] using congrArg e.symm h

def exteriorRename : Simplicial.Ambient V K ≃ₗ[K] Simplicial.Ambient W K where
  toFun := ExteriorAlgebra.map (vectorRename (K := K) e).toLinearMap
  invFun := ExteriorAlgebra.map (vectorRename (K := K) e).symm.toLinearMap
  left_inv := ExteriorAlgebra.leftInverse_map_iff.mpr (vectorRename e).left_inv
  right_inv := ExteriorAlgebra.leftInverse_map_iff.mpr (vectorRename e).right_inv
  map_add' := map_add _
  map_smul' := map_smul _

theorem exteriorRename_basis_unit (F : Finset V) :
    ∃ ε : ℤˣ, exteriorRename (K := K) e (Simplicial.basis F) =
      ε • Simplicial.basis (F.image e) := by
  obtain ⟨ε,hε⟩ := Sublattice.exterior_word_unit_basis (Pi.basisFun K W)
    (F.sort.map e) (List.Nodup.map e.injective (F.sort_nodup _))
  refine ⟨ε, ?_⟩
  change ExteriorAlgebra.map (vectorRename e).toLinearMap
    ((Pi.basisFun K V).ExteriorAlgebra F) = _
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort, map_list_prod]
  have hset : (F.sort.map e).toFinset=F.image e := by ext w; simp
  have hfun : (fun v => ExteriorAlgebra.map (vectorRename e).toLinearMap
      (ExteriorAlgebra.ι K ((Pi.basisFun K V) v))) =
      fun v => ExteriorAlgebra.ι K ((Pi.basisFun K W) (e v)) := by
    funext v
    rw [ExteriorAlgebra.map_apply_ι]
    change ExteriorAlgebra.ι K (vectorRename e ((Pi.basisFun K V) v))=_
    rw [vectorRename_basis]
  simpa only [List.map_map,Function.comp_def,hfun,hset,Simplicial.basis] using hε

def exteriorRenameSign (F : Finset V) : ℤˣ :=
  (exteriorRename_basis_unit (K := K) e F).choose

theorem exteriorRename_basis (F : Finset V) :
    exteriorRename (K := K) e (Simplicial.basis F) =
      exteriorRenameSign (K := K) e F • Simplicial.basis (F.image e) :=
  (exteriorRename_basis_unit (K := K) e F).choose_spec

theorem coordinate_pullback (v : V) :
    ((Pi.basisFun K W).coord (e v)).comp (vectorRename e).toLinearMap =
      (Pi.basisFun K V).coord v := by
  apply (Pi.basisFun K V).ext
  intro j
  change ((Pi.basisFun K W).coord (e v)) (vectorRename e ((Pi.basisFun K V) j))=_
  rw [vectorRename_basis]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    Equiv.apply_eq_iff_eq]

theorem exteriorRename_contraction (v : V) (z : Simplicial.Ambient V K) :
    exteriorRename e (Simplicial.contraction v z) =
      Simplicial.contraction (e v) (exteriorRename e z) := by
  change ExteriorAlgebra.map (vectorRename e).toLinearMap
    (CliffordAlgebra.contractLeft ((Pi.basisFun K V).coord v) z) =
      CliffordAlgebra.contractLeft ((Pi.basisFun K W).coord (e v))
        (ExteriorAlgebra.map (vectorRename e).toLinearMap z)
  rw [ExteriorAlgebra.contractLeft_map,
    coordinate_pullback]

variable {M L : Type u} [AddCommGroup M] [AddCommGroup L]
  [Module K M] [Module K L]
  (c : M ≃ₗ[K] L)

def renameTensor :
    Total (K := K) (V := V) (M := M) ≃ₗ[K] Total (K := K) (V := W) (M := L) :=
  TensorProduct.congr c (exteriorRename e)

@[simp] theorem renameTensor_tmul (m : M) (z : Simplicial.Ambient V K) :
    renameTensor e c (m ⊗ₜ[K] z) = c m ⊗ₜ[K] exteriorRename e z :=
  TensorProduct.congr_tmul _ _ _ _

theorem renameTensor_tmul_basis (m : M) (F : Finset V) :
    renameTensor e c (m ⊗ₜ[K] Simplicial.basis F) =
      exteriorRenameSign (K := K) e F • (c m ⊗ₜ[K] Simplicial.basis (F.image e)) := by
  rw [renameTensor_tmul, exteriorRename_basis, TensorProduct.tmul_smul]

theorem tmul_basis_mem_piece (p : ℕ) (F : Finset V) (hF : F.card=p) (m : M) :
    m ⊗ₜ[K] Simplicial.basis F ∈ piece (K := K) (V := V) (M := M) p := by
  have h := ((pieceCoordinates (K := K) (V := V) (M := M) p).symm
    (Finsupp.single (⟨F,hF⟩ : Set.powersetCard V p) m)).property
  change lift (K := K) p (Finsupp.single (⟨F,hF⟩ : Set.powersetCard V p) m) ∈ _ at h
  rwa [lift_single] at h

theorem renameTensor_lift_mem (p : ℕ) (x : Set.powersetCard V p →₀ M) :
    renameTensor e c (lift (K := K) p x) ∈ piece (K := K) (V := W) (M := L) p := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
  | single F m =>
      rw [lift_single, renameTensor_tmul_basis]
      exact (piece (K := K) (V := W) (M := L) p).toAddSubgroup.zsmul_mem
        (tmul_basis_mem_piece p (F.val.image e)
          ((Finset.card_image_iff.mpr e.injective.injOn).trans F.property) (c m))
        (exteriorRenameSign (K := K) e F.val : ℤ)

theorem renameTensor_mem_piece (p : ℕ) (x : piece (K := K) (V := V) (M := M) p) :
    renameTensor e c x.val ∈ piece (K := K) (V := W) (M := L) p := by
  have h := renameTensor_lift_mem e c p (pieceCoordinates p x)
  simpa only [lift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,Submodule.subtype_apply] using h

theorem renameTensor_symm_eq : (renameTensor e c).symm = renameTensor e.symm c.symm := by
  apply LinearEquiv.toLinearMap_injective
  ext l z
  rfl

def renamePiece (p : ℕ) :
    piece (K := K) (V := V) (M := M) p ≃ₗ[K]
      piece (K := K) (V := W) (M := L) p where
  toFun x := ⟨renameTensor e c x.val, renameTensor_mem_piece e c p x⟩
  invFun y := ⟨(renameTensor e c).symm y.val, by
    rw [renameTensor_symm_eq]
    exact renameTensor_mem_piece e.symm c.symm p y⟩
  left_inv x := Subtype.ext ((renameTensor e c).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((renameTensor e c).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((renameTensor e c).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((renameTensor e c).map_smul r x.val)

/-- The actual coordinate change in each exterior degree. -/
def renameCoordinates (p : ℕ) :
    (Set.powersetCard V p →₀ M) ≃ₗ[K] (Set.powersetCard W p →₀ L) :=
  (pieceCoordinates p).symm.trans ((renamePiece e c p).trans (pieceCoordinates p))

theorem renameCoordinates_symm_eq (p : ℕ) :
    (renameCoordinates e c p).symm = renameCoordinates e.symm c.symm p := by
  ext x
  rfl

theorem renameCoordinates_lift (p : ℕ) (x : Set.powersetCard V p →₀ M) :
    lift (K := K) p (renameCoordinates e c p x) = renameTensor e c (lift (K := K) p x) := by
  simp only [renameCoordinates, LinearEquiv.trans_apply, lift, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

theorem renameCoordinates_single (p : ℕ) (F : Set.powersetCard V p) (m : M) :
    renameCoordinates e c p (Finsupp.single F m) =
      exteriorRenameSign (K := K) e F.val •
        Finsupp.single (⟨F.val.image e,
          (Finset.card_image_iff.mpr e.injective.injOn).trans F.property⟩ : Set.powersetCard W p) (c m) := by
  apply lift_injective (K := K) p
  rw [renameCoordinates_lift, lift_single, renameTensor_tmul_basis, map_zsmul_unit, lift_single]

variable [Module (MvPolynomial V K) M] [IsScalarTower K (MvPolynomial V K) M]
  [Module (MvPolynomial W K) L] [IsScalarTower K (MvPolynomial W K) L]
  (hc : ∀ v m, c ((X v : MvPolynomial V K) • m) =
    (X (e v) : MvPolynomial W K) • c m)

include hc in
theorem renameTensor_differential (x : Total (K := K) (V := V) (M := M)) :
    renameTensor e c (differential (X : V → MvPolynomial V K) x) =
      differential (X : W → MvPolynomial W K) (renameTensor e c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m z =>
      rw [differential_tmul, map_sum, renameTensor_tmul, differential_tmul]
      apply Fintype.sum_equiv e
      intro v
      rw [renameTensor_tmul, hc, exteriorRename_contraction]

include hc in
/-- The literal variable-action differentials commute in all positive
exterior degrees. The separate zero outgoing map is preserved automatically. -/
theorem renameCoordinates_differential (p : ℕ) (x : Set.powersetCard V (p+1) →₀ M) :
    renameCoordinates e c p
      (coordinateDifferential (X : V → MvPolynomial V K)
        (ModuleCat.of (MvPolynomial V K) M) p x) =
      coordinateDifferential (X : W → MvPolynomial W K)
        (ModuleCat.of (MvPolynomial W K) L) p (renameCoordinates e c (p+1) x) := by
  apply lift_injective (K := K) p
  rw [renameCoordinates_lift, ← differential_lift, renameTensor_differential e c hc,
    ← renameCoordinates_lift, differential_lift]

end FourPapers.TensorExteriorKoszul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.OrdinaryIntegerTor -/
section

/-! # Integer ordinary degrees of the actual ideal Tor modules

The ordinary degree of a polynomial Koszul basis vector is a natural
number: polynomial degree plus exterior degree. Its integer grading is
the regrading along the injective map `ℕ → ℤ`. The basis-piece comparison
below identifies this regrading with the literal integer degree function;
in particular, negative strands have no basis vectors.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra


universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

def ordinaryIntegerIdealCoordinatePiece (q : ℤ) (p : ℕ) :=
  ordinaryIntegerRegrade (fun n => actualIdealOrdinaryPiece P n p) q

theorem ordinaryIntegerIdealCoordinatePiece_eq (q : ℤ) (p : ℕ) :
    ordinaryIntegerIdealCoordinatePiece P q p =
      Grading.Piece (actualIdealCoefficientBasis P p)
        (fun b => ((actualIdealDegree b).degree : ℤ)) q :=
  ordinaryIntegerRegrade_basisPiece (actualIdealCoefficientBasis P p)
    (fun b => (actualIdealDegree b).degree) q

/-- A homogeneous submodule of the genuine derived `Tor`, in every
integer ordinary degree. The grading is induced by polynomial Koszul
cycles through the proved natural-degree inclusion. -/
def ordinaryIntegerIdealGradedTor (q : ℤ) (p : ℕ) :
    Submodule K (actualIdealTor P p) :=
  ordinaryIntegerRegrade (fun n => ordinaryIdealGradedTor P hJ n p) q

@[simp] theorem ordinaryIntegerIdealGradedTor_nat (q p : ℕ) :
    ordinaryIntegerIdealGradedTor P hJ (q : ℤ) p = ordinaryIdealGradedTor P hJ q p :=
  ordinaryIntegerRegrade_nat _ q

theorem ordinaryIntegerIdealGradedTor_negative (q : ℤ) (hq : q < 0) (p : ℕ) :
    ordinaryIntegerIdealGradedTor P hJ q p = ⊥ :=
  ordinaryIntegerRegrade_negative _ q hq

end FourPapers.Sublattice

namespace FourPapers.Sublattice

open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

def ordinaryIntegerIdealBettiNumber (p : ℕ) (q : ℤ) : ℕ :=
  Module.finrank K (ordinaryIntegerIdealGradedTor P hJ q p)

@[simp] theorem ordinaryIntegerIdealBettiNumber_nat (p q : ℕ) :
    ordinaryIntegerIdealBettiNumber P hJ p (q : ℤ) = ordinaryIdealBettiNumber P hJ p q := by
  unfold ordinaryIntegerIdealBettiNumber ordinaryIdealBettiNumber
  rw [ordinaryIntegerIdealGradedTor_nat]

theorem ordinaryIntegerIdealBettiNumber_negative (p : ℕ) (q : ℤ) (hq : q < 0) :
    ordinaryIntegerIdealBettiNumber P hJ p q = 0 := by
  unfold ordinaryIntegerIdealBettiNumber
  rw [ordinaryIntegerIdealGradedTor_negative P hJ q hq p]
  exact Module.finrank_zero_of_subsingleton

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedPolynomialModuleTor -/
section

/-!
# Genuine graded Tor of an arbitrary graded polynomial module

No ideal, monomial basis, or Rees-algebra hypothesis occurs here. The
coefficient module has its given integer grading, and each polynomial
variable raises that grading by one. The Koszul component of total degree q
has its p-th coefficient in the original component M_(q-p).
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers.GradedPolynomialModuleTor

open Classical CommAlg CommAlg.Koszul CategoryTheory FilteredHomology

universe u
variable {K V M : Type u} [Field K] [Fintype V] [LinearOrder V]
  [AddCommGroup M] [Module (MvPolynomial V K) M] [Module K M]
  [IsScalarTower K (MvPolynomial V K) M]
  (P : ℤ → Submodule K M) [DirectSum.Decomposition P]

abbrev CoefficientIndex := Σ q : ℤ, Module.Free.ChooseBasisIndex K (P q)

def coefficientBasis : Module.Basis (CoefficientIndex P) K M :=
  (DirectSum.Decomposition.isInternal P).collectedBasis
    (fun q => Module.Free.chooseBasis K (P q))

theorem coefficientBasis_mem (a : CoefficientIndex P) : coefficientBasis P a ∈ P a.1 :=
  (DirectSum.Decomposition.isInternal P).collectedBasis_mem
    (fun q => Module.Free.chooseBasis K (P q)) a

/-- The basis grading agrees with the original given grading. -/
theorem coefficientBasis_piece (q : ℤ) :
    Grading.Piece (coefficientBasis P) (fun a => a.1) q = P q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    change a.1 = q at ha
    rw [← ha]
    exact coefficientBasis_mem P a
  · intro x hx
    rw [Grading.mem_piece]
    intro a ha
    by_contra hne
    apply ha
    exact (DirectSum.Decomposition.isInternal P).collectedBasis_repr_of_mem_ne
      (fun q => Module.Free.chooseBasis K (P q)) (Ne.symm hne) hx

abbrev CoordinateIndex (p : ℕ) := Σ _ : Set.powersetCard V p, CoefficientIndex P

def coordinateBasis (p : ℕ) : Module.Basis (CoordinateIndex (V:=V) P p) K
    (PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p) :=
  Finsupp.basis (fun _ => coefficientBasis P)

def coordinateDegree (p : ℕ) (a : CoordinateIndex (V:=V) P p) : ℤ := a.2.1 + (p:ℤ)

@[simp] theorem coordinateBasis_apply (p : ℕ) (a : CoordinateIndex (V:=V) P p) :
    coordinateBasis P p a = Finsupp.single a.1 (coefficientBasis P a.2) := by
  simp only [coordinateBasis,Finsupp.coe_basis]

@[simp] theorem coordinateBasis_repr (p : ℕ)
    (x : PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p)
    (a : CoordinateIndex (V:=V) P p) :
    (coordinateBasis P p).repr x a = (coefficientBasis P).repr (x a.1) a.2 := rfl

def piece (q : ℤ) (p : ℕ) :
    Submodule K (PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p) :=
  Grading.Piece (coordinateBasis P p) (coordinateDegree P p) q

/-- The usual polynomial-plus-exterior grading, expressed without any
chosen-basis convention. This includes every integer internal degree. -/
theorem mem_piece (q : ℤ) (p : ℕ)
    (x : PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p) :
    x ∈ piece (V:=V) P q p ↔ ∀ F, x F ∈ P (q-(p:ℤ)) := by
  rw [piece,Grading.mem_piece]
  constructor
  · intro h F
    rw [← coefficientBasis_piece P (q-(p:ℤ)), Grading.mem_piece]
    intro a ha
    have hd := h ⟨F,a⟩ ha
    change a.1+(p:ℤ)=q at hd
    omega
  · intro h a ha
    have hd := (Grading.mem_piece (coefficientBasis P) (fun b => b.1)
      (q-(p:ℤ)) (x a.1)).mp (by rw [coefficientBasis_piece]; exact h a.1) a.2 ha
    change a.2.1+(p:ℤ)=q
    omega

variable (hX : ∀ v q x, x ∈ P q → (MvPolynomial.X v : MvPolynomial V K) • x ∈ P (q+1))

include hX in
theorem differential_basis_mem (p : ℕ) (a : CoordinateIndex (V:=V) P (p+1)) :
    PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p
      (coordinateBasis P (p+1) a) ∈ piece (V:=V) P (coordinateDegree P (p+1) a) p := by
  rw [coordinateBasis_apply]
  change coordinateDifferential (MvPolynomial.X : V → MvPolynomial V K)
    (ModuleCat.of (MvPolynomial V K) M) p
      (Finsupp.single a.1 (coefficientBasis P a.2)) ∈ _
  rw [coordinateDifferential_single]
  apply Submodule.sum_mem
  intro v _
  rw [mem_piece]
  intro F
  by_cases he : eraseIndex a.1 v = F
  · rw [Finsupp.single_apply, if_pos he]
    have hm := hX v.val a.2.1
      (TauCeti.ExteriorAlgebra.basisEraseSign v.val a.1.val • coefficientBasis P a.2)
      ((P a.2.1).toAddSubgroup.zsmul_mem (coefficientBasis_mem P a.2)
        (TauCeti.ExteriorAlgebra.basisEraseSign v.val a.1.val : ℤ))
    convert hm using 1
    unfold coordinateDegree
    congr 1
    omega
  · rw [Finsupp.single_apply,if_neg he]
    exact Submodule.zero_mem _

include hX in
theorem differential_mem (q : ℤ) (p : ℕ)
    {x : PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) (p+1)}
    (hx : x ∈ piece (V:=V) P q (p+1)) :
    PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p x ∈ piece (V:=V) P q p :=
  map_mem_piece_of_basis (coordinateBasis P (p+1)) (coordinateBasis P p)
    (coordinateDegree P (p+1)) (coordinateDegree P p)
    (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p) (differential_basis_mem P hX p) q hx

def differential (q : ℤ) (p : ℕ) : piece (V:=V) P q (p+1) →ₗ[K] piece (V:=V) P q p :=
  ((PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p).domRestrict
    (piece (V:=V) P q (p+1))).codRestrict (piece (V:=V) P q p)
      (fun x => differential_mem P hX q p x.property)

@[simp] theorem differential_val (q : ℤ) (p : ℕ)
    (x : piece (V:=V) P q (p+1)) :
    (differential P hX q p x).val =
      PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p x.val := rfl

def previous (q : ℤ) : ∀ p : ℕ, piece (V:=V) P q p →ₗ[K] piece (V:=V) P q p.pred
  | 0 => 0
  | p+1 => differential P hX q p

@[simp] theorem previous_val (q : ℤ) (p : ℕ) (x : piece (V:=V) P q p) :
    (previous P hX q p x).val =
      PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=M) p x.val := by
  cases p <;> rfl

theorem previous_comp (q : ℤ) (p : ℕ) :
    (previous P hX q p).comp (differential P hX q p)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (previous P hX q p (differential P hX q p x)).val = 0
  rw [previous_val]
  exact LinearMap.congr_fun (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=M) p) x.val

abbrev Homology (q : ℤ) (p : ℕ) := FilteredHomology.Homology
  (differential P hX q p) (previous P hX q p) (previous_comp P hX q p)

/-- An actual linear embedding into the finite product of original
coefficient pieces; it proves finite-dimensionality of every Koszul strand. -/
def pieceCoordinates (q : ℤ) (p : ℕ) :
    piece (V:=V) P q p →ₗ[K] (Set.powersetCard V p → P (q-(p:ℤ))) where
  toFun x F := ⟨x.val F,(mem_piece (V:=V) P q p x.val).mp x.property F⟩
  map_add' x y := by ext F; rfl
  map_smul' c x := by ext F; rfl

theorem pieceCoordinates_injective (q : ℤ) (p : ℕ) :
    Function.Injective (pieceCoordinates (V:=V) P q p) := by
  intro x y h
  apply Subtype.ext
  ext F
  exact congrArg (fun z : Set.powersetCard V p → P (q-(p:ℤ)) => (z F).val) h

theorem piece_finite [∀ q, Module.Finite K (P q)] (q : ℤ) (p : ℕ) :
    Module.Finite K (piece (V:=V) P q p) :=
  Module.Finite.of_injective (pieceCoordinates P q p) (pieceCoordinates_injective P q p)

def cyclesInclusion (q : ℤ) (p : ℕ) :
    LinearMap.ker (previous P hX q p) →ₗ[K]
      LinearMap.ker (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=M) p) :=
  (((piece (V:=V) P q p).subtype).comp (LinearMap.ker (previous P hX q p)).subtype).codRestrict _ (by
      intro z
      change PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=M) p z.val.val=0
      rw [← previous_val P hX q p z.val]
      exact congrArg Subtype.val z.property)

theorem cyclesInclusion_boundary (q : ℤ) (p : ℕ) (y : piece (V:=V) P q (p+1)) :
    cyclesInclusion P hX q p
        (boundaryMap (K:=K) (differential P hX q p) (previous P hX q p)
          (previous_comp P hX q p) y) =
      boundaryMap (K:=K)
        (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p)
        (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=M) p)
        (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=M) p) y.val := by
  apply Subtype.ext
  change (differential P hX q p y).val =
    PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p y.val
  rfl

section

attribute [local irreducible] piece differential previous
  PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- Inclusion is induced by the three literal coordinate inclusions. The
abstract constructor keeps the ambient module structures explicit. -/
def homologyInclusion (q : ℤ) (p : ℕ) :
    Homology P hX q p →ₗ[K] PolynomialCoordinateTor.Homology (K:=K) (V:=V) (M:=M) p :=
  FilteredHomology.threeTermHomologyMap (K:=K)
    (X:=piece (V:=V) P q (p+1)) (Y:=piece (V:=V) P q p)
    (Z:=piece (V:=V) P q p.pred)
    (X':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) (p+1))
    (Y':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p)
    (Z':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p.pred)
    (differential (V:=V) P hX q p) (previous (V:=V) P hX q p)
    (previous_comp (V:=V) P hX q p)
    (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p)
    (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=M) p)
    (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=M) p)
    (piece (V:=V) P q (p+1)).subtype (piece (V:=V) P q p).subtype
    (piece (V:=V) P q p.pred).subtype
    (differential_val P hX q p) (previous_val P hX q p)

end

#check homologyInclusion

@[simp] theorem homologyInclusion_class (q : ℤ) (p : ℕ)
    (z : LinearMap.ker (previous P hX q p)) :
    homologyInclusion P hX q p
      (homologyClass (differential P hX q p) (previous P hX q p)
        (previous_comp P hX q p) z) =
    homologyClass (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p) (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=M) p)
      (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=M) p) (cyclesInclusion P hX q p z) := rfl

#check homologyInclusion_class
/-- Projecting an ambient boundary preimage to degree q gives a preimage
inside the same homogeneous Koszul component. -/
theorem boundary_reflects (q : ℤ) (p : ℕ) (y : piece (V:=V) P q p)
    (a : PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) (p+1))
    (ha : PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p a = y.val) :
    ∃ x, differential P hX q p x = y := by
  let x : piece (V:=V) P q (p+1) :=
    ⟨Grading.projection (coordinateBasis (V:=V) P (p+1))
      (coordinateDegree (V:=V) P (p+1)) q a, Grading.projection_mem _ _ _ _⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  have hc := LinearMap.congr_fun (shiftedProjection_commutes (k:=K)
    (X:=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) (p+1))
    (Y:=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p)
    (I:=CoordinateIndex (V:=V) P (p+1)) (J:=CoordinateIndex (V:=V) P p)
    (A:=ℤ) (B:=ℤ)
    (coordinateBasis (V:=V) P (p+1)) (coordinateBasis (V:=V) P p)
    (coordinateDegree (V:=V) P (p+1)) (coordinateDegree (V:=V) P p)
    id Function.injective_id (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p)
    (differential_basis_mem (V:=V) P hX p) q) a
  change PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p
    (Grading.projection _ _ q a) =
      Grading.projection _ _ q (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p a) at hc
  change PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p
    (Grading.projection _ _ q a) = y.val
  rw [hc, ha, Grading.projection_eq_self y.property]

section
attribute [local irreducible] piece differential previous
  PolynomialCoordinateTor.differential PolynomialCoordinateTor.previous

set_option backward.isDefEq.respectTransparency true in
theorem homologyInclusion_injective (q : ℤ) (p : ℕ) :
    Function.Injective (homologyInclusion (V:=V) P hX q p) :=
  FilteredHomology.threeTermHomologyMap_injective_of_reflects_boundaries (K:=K)
    (X:=piece (V:=V) P q (p+1)) (Y:=piece (V:=V) P q p)
    (Z:=piece (V:=V) P q p.pred)
    (X':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) (p+1))
    (Y':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p)
    (Z':=PolynomialCoordinateTor.Coordinates (V:=V) (M:=M) p.pred)
    (differential (V:=V) P hX q p) (previous (V:=V) P hX q p)
    (previous_comp (V:=V) P hX q p)
    (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=M) p)
    (PolynomialCoordinateTor.previous (K:=K) (V:=V) (M:=M) p)
    (PolynomialCoordinateTor.previous_comp (K:=K) (V:=V) (M:=M) p)
    (piece (V:=V) P q (p+1)).subtype (piece (V:=V) P q p).subtype
    (piece (V:=V) P q p.pred).subtype
    (differential_val P hX q p) (previous_val P hX q p)
    (fun y _ ⟨a, ha⟩ => boundary_reflects P hX q p y a ha)
end

#check homologyInclusion_injective

def homologyToTor (q : ℤ) (p : ℕ) :
    Homology P hX q p →ₗ[K] PolynomialCoordinateTor.Tor (K:=K) (V:=V) (M:=M) p :=
  ((PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=M) p).toLinearEquiv.symm.toLinearMap).comp (homologyInclusion P hX q p)

theorem homologyToTor_injective (q : ℤ) (p : ℕ) :
    Function.Injective (homologyToTor (V:=V) P hX q p) :=
  (PolynomialCoordinateTor.torIso (K:=K) (V:=V) (M:=M) p).toLinearEquiv.symm.injective.comp
    (homologyInclusion_injective P hX q p)

/-- The actual degree-q submodule of derived Tor, defined by the inclusion
of ordinary homogeneous Koszul cycle classes. -/
def gradedTor (q : ℤ) (p : ℕ) :
    Submodule K (PolynomialCoordinateTor.Tor (K:=K) (V:=V) (M:=M) p) :=
  LinearMap.range (homologyToTor P hX q p)

def gradedTorEquiv (q : ℤ) (p : ℕ) : Homology P hX q p ≃ₗ[K] gradedTor P hX q p :=
  LinearEquiv.ofInjective (homologyToTor P hX q p) (homologyToTor_injective P hX q p)

def bettiNumber (p : ℕ) (q : ℤ) : ℕ := Module.finrank K (gradedTor P hX q p)

theorem bettiNumber_eq_finrank (p : ℕ) (q : ℤ) :
    bettiNumber P hX p q=Module.finrank K (Homology P hX q p) :=
  (gradedTorEquiv P hX q p).finrank_eq.symm

end FourPapers.GradedPolynomialModuleTor

end
end
end


end
