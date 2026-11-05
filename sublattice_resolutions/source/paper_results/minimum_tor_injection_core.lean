module
public import paper_results.bottom_rees_injection
public import shared_results.part021
public import paper_results.part002
public import Mathlib.Data.Finsupp.MonomialOrder

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MinimumLiftReesInjection -/
section

/-! # The specified minimum lift acts injectively on the original Rees homology

The lift is the monic triangular polynomial with leading exponent `u_μ`.
The ordered associated-algebra equivalence identifies its actual symbol
with the literal minimum monomial, whose injection was proved separately.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct
universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J=finiteSublatticeIdeal n E)
  (μ : E)

local notation "G" => canonicalPowerGenerators n J
local notation "hG" => canonicalPowerGroebner n m J
local notation "hu" => canonicalPowerUnitLeading n m J
local notation "I" => finiteSublatticeIdeal n (k:=K) E
local notation "hi" => sublatticePowerInitial n m J E hE hinit
local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "c" => initialReesKoszulBasis m J I hi G hG hu

def minimumLiftIndex : NonstandardIndex m (J^1) :=
  ⟨finiteRowExponent n μ.val,by
    apply (monomial_mem_initial_iff_not_standard m (J^1) (G 1) (hG 1) (hu 1) _).mp
    change monomial (finiteRowExponent n μ.val) (1 : K) ∈ initialIdealForBasis m (J^1)
    rw [hi 1,pow_one,← finiteRowMonomial_eq_monomial]
    exact Ideal.subset_span ⟨μ.val,μ.property,rfl⟩⟩

def minimumReesIndex : IdealReesKoszulIndex m J :=
  (⟨1,minimumLiftIndex n m J E hE hinit μ⟩,∅)

/-- The actual polynomial generator chosen by the first-power triangular
basis, with no homology class or comparison built into its definition. -/
def minimumLiftGenerator : MvPolynomial (FiniteVariable.{u} n) K :=
  (idealLift m (J^1) (G 1) (hG 1) (hu 1) (minimumLiftIndex n m J E hE hinit μ)).val

theorem minimumLiftGenerator_mem : minimumLiftGenerator n m J E hE hinit μ ∈ J := by
  have h := (idealLift m (J^1) (G 1) (hG 1) (hu 1)
    (minimumLiftIndex n m J E hE hinit μ)).property
  simpa only [minimumLiftGenerator, pow_one] using! h

theorem minimumLiftGenerator_coefficient :
    (minimumLiftGenerator n m J E hE hinit μ).coeff (finiteRowExponent n μ.val)=1 := by
  exact (idealLift_nonstandard_coeff m (J^1) (G 1) (hG 1) (hu 1)
    (minimumLiftIndex n m J E hE hinit μ)
    (minimumLiftIndex n m J E hE hinit μ)).trans (if_pos rfl)

theorem minimumLiftGenerator_degree :
    m.degree (minimumLiftGenerator n m J E hE hinit μ)=finiteRowExponent n μ.val := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply m.degree_le_iff.mpr
    exact (mem_restrictSupport_iff K).mp
      (idealLift_mem_orderBound m (J^1) (G 1) (hG 1) (hu 1)
        (minimumLiftIndex n m J E hE hinit μ))
  · apply m.le_degree
    rw [mem_support_iff,minimumLiftGenerator_coefficient]
    exact one_ne_zero

theorem minimumRees_basis_cycle :
    (idealReesKoszulDGA J).d (b (minimumReesIndex n m J E hE hinit μ))=0 := by
  rw [groebnerReesKoszul_d_basis]
  simp only [minimumReesIndex,Simplicial.contraction_basis,Finset.notMem_empty,
    if_false,TensorProduct.tmul_zero,Finset.sum_const_zero]

theorem minimumRees_basis_even :
    (idealReesKoszulDGA J).parity (b (minimumReesIndex n m J E hE hinit μ))=
      b (minimumReesIndex n m J E hE hinit μ) := by
  rw [groebnerReesKoszul_parity_basis]
  simp only [minimumReesIndex,Finset.card_empty,pow_zero,one_smul]

theorem minimumInitialRees_basis_cycle :
    (idealReesKoszulDGA I).d (c (minimumReesIndex n m J E hE hinit μ))=0 := by
  rw [initialReesKoszul_d_basis]
  simp only [minimumReesIndex,Simplicial.contraction_basis,Finset.notMem_empty,
    if_false,TensorProduct.tmul_zero,Finset.sum_const_zero]

def minimumFiniteReesExponent : finiteReesExponentMonoid.{u} E :=
  ⟨finiteTargetExponent (finiteRowExponent n μ.val) 1,by
    apply (finiteTarget_mem_rees_iff _ _).mpr
    refine ⟨finiteRowExponent n μ.val,?_,le_rfl⟩
    change finiteRowExponent n μ.val ∈
      (({0} : Finset (Exponent (FiniteVariable.{u} n))).product (finiteRowFamily n E)).image
        (fun bc => bc.1+bc.2)
    exact Finset.mem_image.mpr ⟨(0,finiteRowExponent n μ.val),
      Finset.mem_product.mpr ⟨Finset.mem_singleton_self 0,
        Finset.mem_image.mpr ⟨μ.val,μ.property,rfl⟩⟩,zero_add _⟩⟩

theorem minimumFiniteReesExponent_fine :
    finiteReesFineExponent (minimumFiniteReesExponent n E μ)=finiteRowExponent n μ.val := by
  ext v
  simp only [minimumFiniteReesExponent, finiteReesFineExponent,
    Finsupp.comapDomain_apply, finiteTargetExponent_some]

theorem minimumRees_tensor_coordinate :
    reesTensorCoordinateAlgEquiv (k:=K) hE
      (finiteReesImageBasis E K (minimumFiniteReesExponent n E μ) ⊗ₜ[K]
        Simplicial.basis ∅) = (bottomReesCycle μ hE).val := by
  apply Subtype.ext
  change (reesTensorCoordinateLinearEquiv (k:=K) hE
    (finiteReesImageBasis E K (minimumFiniteReesExponent n E μ) ⊗ₜ[K]
      Simplicial.basis ∅)).val = _
  rw [reesTensorCoordinateLinearEquiv_basis,minimumFiniteReesExponent_fine,
    faceExponent_empty,add_zero,faceBasis_empty,bottomReesCycle_val]
  simp only [minimumFiniteReesExponent, finiteTargetExponent_none]

theorem minimumInitialRees_basis_tensor :
    c (minimumReesIndex n m J E hE hinit μ) =
      finiteReesKoszulCoefficientEquiv E
        (finiteReesImageBasis E K (minimumFiniteReesExponent n E μ) ⊗ₜ[K]
          Simplicial.basis ∅) := by
  rw [initialReesKoszulBasis,Module.Basis.tensorProduct_apply,
    finiteReesKoszulCoefficientEquiv_tmul]
  congr 1
  apply Subtype.ext
  rw [initialReesBasis_val,finiteReesCoefficientEquiv_val,finiteReesImageBasis_val,
    optionPolynomialCoefficientEquiv_monomial,minimumFiniteReesExponent_fine]
  simp only [minimumReesIndex, minimumLiftIndex, minimumFiniteReesExponent,
    finiteTargetExponent_none]

/-- The special-side injection is transferred through the proved actual
Rees algebra and homology equivalences, with its generator identified. -/
theorem minimumInitialRees_homology_mul_injective
    (hμ : ∀ a : E, μ.val≤a.val) :
    Function.Injective (fun z : (idealReesKoszulDGA I).Homology =>
      (idealReesKoszulDGA I).classMap
        ⟨c (minimumReesIndex n m J E hE hinit μ),
          ((idealReesKoszulDGA I).mem_cycles _).mpr
            (minimumInitialRees_basis_cycle n m J E hE hinit μ)⟩ * z) := by
  let e₁ := reesKoszulHomologyCoordinateEquiv (k:=K) hE
  let e₂ := finiteReesKoszulHomologyEquiv (K:=K) E hE
  let x := (ParityDifferential.cyclesEquiv (reesKoszulTensorDGA (k:=K) hE)
    (reesKoszulCoordinateDifferential hE) (reesTensorCoordinateAlgEquiv hE)
    ((reesKoszulCoordinateDifferential hE).pullback_intertwines
      (reesTensorCoordinateAlgEquiv hE))).symm (bottomReesCycle μ hE)
  have hxval : x.val = finiteReesImageBasis E K (minimumFiniteReesExponent n E μ) ⊗ₜ[K]
      Simplicial.basis ∅ := by
    apply (reesTensorCoordinateAlgEquiv hE).injective
    exact (AlgEquiv.apply_symm_apply _ _).trans
      (minimumRees_tensor_coordinate n E hE μ).symm
  have he₁ : e₁ ((reesKoszulTensorDGA hE).classMap x)=
      (reesKoszulCoordinateDifferential hE).classMap (bottomReesCycle μ hE) := by
    change ParityDifferential.homologyEquiv
      (reesKoszulTensorDGA (k := K) hE) (reesKoszulCoordinateDifferential (k := K) hE)
      (reesTensorCoordinateAlgEquiv (k := K) hE)
      ((reesKoszulCoordinateDifferential (k := K) hE).pullback_intertwines
        (reesTensorCoordinateAlgEquiv (k := K) hE))
      ((reesKoszulTensorDGA hE).classMap x) = _
    exact (ParityDifferential.homologyEquiv_classMap
      (reesKoszulTensorDGA (k := K) hE) (reesKoszulCoordinateDifferential (k := K) hE)
      (reesTensorCoordinateAlgEquiv (k := K) hE)
      ((reesKoszulCoordinateDifferential (k := K) hE).pullback_intertwines
        (reesTensorCoordinateAlgEquiv (k := K) hE)) x).trans
      (congrArg (reesKoszulCoordinateDifferential hE).classMap (AlgEquiv.apply_symm_apply _ _))
  have he₂ : e₂ ((reesKoszulTensorDGA hE).classMap x)=
      (idealReesKoszulDGA I).classMap
        ⟨c (minimumReesIndex n m J E hE hinit μ),
          ((idealReesKoszulDGA I).mem_cycles _).mpr
            (minimumInitialRees_basis_cycle n m J E hE hinit μ)⟩ := by
    change ParityDifferential.homologyEquiv
      (reesKoszulTensorDGA (k := K) hE) (idealReesKoszulDGA I)
      (finiteReesKoszulCoefficientEquiv (K := K) E)
      (finiteReesKoszulCoefficientEquiv_d E hE)
      ((reesKoszulTensorDGA hE).classMap x) = _
    rw [ParityDifferential.homologyEquiv_classMap]
    apply congrArg (idealReesKoszulDGA I).classMap
    apply Subtype.ext
    change finiteReesKoszulCoefficientEquiv E x.val =
      c (minimumReesIndex n m J E hE hinit μ)
    exact (congrArg (finiteReesKoszulCoefficientEquiv (K := K) E) hxval).trans
      (minimumInitialRees_basis_tensor n m J E hE hinit μ).symm
  intro z t hzt
  apply e₂.symm.injective
  apply e₁.injective
  apply bottomReesHomologyMul_injective μ hμ hE
  have h := congrArg (fun a => e₁ (e₂.symm a)) hzt
  rw [← he₂,map_mul e₂.symm,map_mul e₂.symm,e₂.symm_apply_apply,
    map_mul e₁,map_mul e₁,he₁] at h
  exact h

variable (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
  (fun _ : FiniteVariable.{u} n => (1:ℕ))))

/-- Under exactly the first-power Betti hypothesis, multiplication by the
specified lift of the minimum generator is injective on actual Rees Koszul
homology. The proof keeps the original monomial order throughout. -/
theorem minimumLiftRees_homology_mul_injective (hμ : ∀ a : E, μ.val≤a.val)
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) :
    Function.Injective (fun z : (idealReesKoszulDGA J).Homology =>
      (idealReesKoszulDGA J).classMap
        ⟨b (minimumReesIndex n m J E hE hinit μ),
          ((idealReesKoszulDGA J).mem_cycles _).mpr
            (minimumRees_basis_cycle n m J E hE hinit μ)⟩ * z) := by
  apply OrderedBasis.basis_homology_mul_injective b c (reesKoszulWeight m J)
    (initialReesKoszul_product_homogeneous m J I hi G hG hu)
    (groebnerReesKoszul_product_leading m J I hi G hG hu)
    (fun a ha => (groebnerReesKoszul_one_weight m J G hG hu a ha).le)
    (groebnerReesKoszul_leading_one m J I hi G hG hu)
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (OrderedRees.differential_homogeneous m J I hi G hG hu)
    (OrderedRees.differential_leading m J I hi G hG hu)
    (OrderedRees.parity_homogeneous m J I hi G hG hu)
    (OrderedRees.parity_leading m J I hi G hG hu)
    (OrderedRees.all_cycle_lifts m J I hi G hG hu
      (sublattice_initial_homology_generated n m J E hE hinit)
      (ordered_relative_lifts_of_power_coordinate_lifts m J G hG hu I hi 1
        (sublattice_first_ordered_lifts n m J E hE hinit hJ hβ)))
    (minimumReesIndex n m J E hE hinit μ)
    (minimumRees_basis_cycle n m J E hE hinit μ)
    (minimumRees_basis_even n m J E hE hinit μ)
    (minimumInitialRees_basis_cycle n m J E hE hinit μ)
    (minimumInitialRees_homology_mul_injective n m J E hE hinit μ hμ)

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.MinimumLiftTorInjection -/
section

/-! # Corollary 5.3: the specified multiplier on actual derived Tor

The map is the genuine derived tensor functor applied to multiplication by
the specified polynomial. Total Rees boundary reflection descends to every
power and every homological degree by the literal coefficient projections.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial CategoryTheory
open scoped TensorProduct
universe u

section Multiplier
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (J : Ideal (MvPolynomial V K)) (f : MvPolynomial V K) (hf : f∈J)

/-- Literal polynomial multiplication as a morphism of the actual ideal
power modules. This is the input to the derived Tor functor. -/
def idealPowerMultiplication (s : ℕ) :
    ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s) ⟶
      ModuleCat.of (MvPolynomial V K) (idealPowerPiece J (s+1)) :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨f*x.val,by
        change f*x.val∈J^(s+1)
        rw [pow_succ,mul_comm f]
        exact Ideal.mul_mem_mul x.property hf⟩
      map_add' := fun x y => Subtype.ext (mul_add f x.val y.val)
      map_smul' := fun r x => Subtype.ext (by
        change f*(r*x.val)=r*(f*x.val)
        ring) }

@[simp] theorem idealPowerMultiplication_val (s : ℕ) (x : idealPowerPiece J s) :
    (idealPowerMultiplication J f hf s x).val=f*x.val := rfl

def multiplierReesCoefficient : coefficientRees J :=
  idealReesSingle J 1 ⟨f,by
    change f ∈ J^1
    simpa only [pow_one] using hf⟩

theorem multiplierReesCoefficient_mul_single (s : ℕ) (x : idealPowerPiece J s) :
    multiplierReesCoefficient J f hf * idealReesSingle J s x =
      idealReesSingle J (s+1) (idealPowerMultiplication J f hf s x) := by
  apply Subtype.ext
  change AddMonoidAlgebra.single 1 f * AddMonoidAlgebra.single s x.val =
    AddMonoidAlgebra.single (s+1) (f*x.val)
  rw [AddMonoidAlgebra.single_mul_single,Nat.add_comm 1 s]

theorem powerCoordinateInclusion_multiplication (s p : ℕ)
    (x : PowerIdealCoordinates J s p) :
    (multiplierReesCoefficient J f hf ⊗ₜ[K] (1 : Simplicial.Ambient V K)) *
        powerCoordinateInclusion J s p x =
      powerCoordinateInclusion J (s+1) p
        (PolynomialTorNaturality.coordinateMap (idealPowerMultiplication J f hf s) p x) := by
  have he : (LinearMap.mulLeft K
      (multiplierReesCoefficient J f hf ⊗ₜ[K] (1 : Simplicial.Ambient V K))).comp
        (powerCoordinateInclusion J s p) =
      (powerCoordinateInclusion J (s+1) p).comp
        ((PolynomialTorNaturality.coordinateMap (idealPowerMultiplication J f hf s) p).restrictScalars K) := by
    apply Finsupp.lhom_ext
    intro F a
    change (multiplierReesCoefficient J f hf ⊗ₜ[K] (1 : Simplicial.Ambient V K)) *
      powerCoordinateInclusion J s p (Finsupp.single F a) = _
    simp only [powerCoordinateInclusion,LinearMap.comp_apply,LinearMap.restrictScalars_apply,
      TensorExteriorKoszul.lift_single,
      powerKoszulInclusion,TensorProduct.map_tmul,LinearMap.id_apply,
      PolynomialTorNaturality.coordinateMap,Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single,Algebra.TensorProduct.tmul_mul_tmul,one_mul,
      multiplierReesCoefficient_mul_single]
  exact LinearMap.congr_fun he x

/-- The degree-zero exterior cycle determined by the literal multiplier. -/
def multiplierReesCycle : (idealReesKoszulDGA J).cycles :=
  ⟨multiplierReesCoefficient J f hf ⊗ₜ[K] (1 : Simplicial.Ambient V K),by
    change TensorExteriorKoszul.differential (idealReesBaseVariable J)
      (multiplierReesCoefficient J f hf ⊗ₜ[K] (1 : Simplicial.Ambient V K))=0
    have hc : ∀ v : V, Simplicial.contraction v (1 : Simplicial.Ambient V K) = 0 := by
      intro v
      exact CliffordAlgebra.contractLeft_one _ _
    have he := TensorExteriorKoszul.differential_tmul (K := K)
      (R := coefficientRees J) (V := V) (M := coefficientRees J)
      (idealReesBaseVariable J) (multiplierReesCoefficient J f hf)
      (1 : Simplicial.Ambient V K)
    simpa only [hc, TensorProduct.tmul_zero, Finset.sum_const_zero] using he⟩

/-- Total Rees boundary reflection is enough for the literal map in every
power. The exact auxiliary and exterior projections supply the fillings. -/
theorem multiplier_coordinate_reflects_boundaries
    (hinj : Function.Injective (fun z : (idealReesKoszulDGA J).Homology =>
      (idealReesKoszulDGA J).classMap (multiplierReesCycle J f hf)*z))
    (s p : ℕ) (z : PowerIdealCoordinates J s p)
    (hz : powerPreviousDifferential J s p z=0)
    (hb : ∃ w : PowerIdealCoordinates J (s+1) (p+1),
      powerPreviousDifferential J (s+1) (p+1) w=
        PolynomialTorNaturality.coordinateMap (idealPowerMultiplication J f hf s) p z) :
    ∃ y : PowerIdealCoordinates J s (p+1),powerPreviousDifferential J s (p+1) y=z := by
  have hzcycle : (idealReesKoszulDGA J).d (powerCoordinateInclusion J s p z)=0 := by
    rw [powerCoordinateInclusion_d,hz,(powerCoordinateInclusion J s p.pred).map_zero]
  let x : (idealReesKoszulDGA J).cycles :=
    ⟨powerCoordinateInclusion J s p z,
      ((idealReesKoszulDGA J).mem_cycles _).mpr hzcycle⟩
  have hp : (idealReesKoszulDGA J).classMap (multiplierReesCycle J f hf)*
      (idealReesKoszulDGA J).classMap x=0 := by
    rw [← map_mul (idealReesKoszulDGA J).classMap]
    apply ((idealReesKoszulDGA J).classMap_eq_zero _).mpr
    obtain ⟨w,hw⟩ := hb
    refine ⟨powerCoordinateInclusion J (s+1) (p+1) w,?_⟩
    rw [powerCoordinateInclusion_d,hw]
    exact (powerCoordinateInclusion_multiplication J f hf s p z).symm
  have hx : (idealReesKoszulDGA J).classMap x=0 :=
    hinj (hp.trans (mul_zero ((idealReesKoszulDGA J).classMap
      (multiplierReesCycle J f hf))).symm)
  exact powerCoordinateInclusion_reflects_boundaries J s p z
    (((idealReesKoszulDGA J).classMap_eq_zero x).mp hx)

/-- A genuine Rees-homology multiplier injection gives injection of the
actual derived Tor map induced by the same polynomial. -/
theorem multiplier_Tor_injective_of_Rees
    (hinj : Function.Injective (fun z : (idealReesKoszulDGA J).Homology =>
      (idealReesKoszulDGA J).classMap (multiplierReesCycle J f hf)*z)) (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s)) := by
  apply PolynomialTorNaturality.torMap_injective_of_coordinate_reflection
  intro z hz hb
  apply multiplier_coordinate_reflects_boundaries J f hf hinj s p z
  · cases p <;> exact hz
  · exact hb

end Multiplier

variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J=finiteSublatticeIdeal n E)
  (μ : E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1:ℕ))))

local notation "fμ" => minimumLiftGenerator n m J E hE hinit μ
local notation "hfμ" => minimumLiftGenerator_mem n m J E hE hinit μ
local notation "b" => groebnerReesKoszulBasis m J (canonicalPowerGenerators n J)
  (canonicalPowerGroebner n m J) (canonicalPowerUnitLeading n m J)
local notation "D" => idealReesKoszulDGA J

theorem minimumRees_basis_coefficient :
    b (minimumReesIndex n m J E hE hinit μ)=
      multiplierReesCoefficient J fμ hfμ ⊗ₜ[K]
        (1 : Simplicial.Ambient (FiniteVariable.{u} n) K) := by
  rw [groebnerReesKoszulBasis,Module.Basis.tensorProduct_apply]
  change groebnerReesBasis J m (canonicalPowerGenerators n J)
      (canonicalPowerGroebner n m J) (canonicalPowerUnitLeading n m J)
      ⟨1,minimumLiftIndex n m J E hE hinit μ⟩ ⊗ₜ[K]
      Simplicial.basis (∅ : Finset (FiniteVariable.{u} n)) = _
  rw [faceBasis_empty]
  apply congrArg (fun a : coefficientRees J =>
    a ⊗ₜ[K] (1 : Simplicial.Ambient (FiniteVariable.{u} n) K))
  exact groebnerReesBasis_apply J m (canonicalPowerGenerators n J)
    (canonicalPowerGroebner n m J) (canonicalPowerUnitLeading n m J) 1
    (minimumLiftIndex n m J E hE hinit μ)

include hJ in
/-- The internal degree shift is exactly the common generator degree `d`. -/
theorem minimumLiftGenerator_homogeneous :
    IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1:ℕ)) fμ d := by
  have h := idealLift_homogeneous_withNatModule m (J^1) (canonicalPowerGenerators n J 1)
    (canonicalPowerGroebner n m J 1) (canonicalPowerUnitLeading n m J 1)
    (fun _ : FiniteVariable.{u} n => (1:ℕ)) (homogeneousIdealPower n J hJ 1)
    (minimumLiftIndex n m J E hE hinit μ)
  simpa only [minimumLiftIndex,← Finsupp.degree_eq_weight_one,finiteRowExponent_degree] using! h

theorem minimumLift_coordinate_reflects_boundaries
    (hμ : ∀ a : E,μ.val≤a.val)
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q)
    (s p : ℕ) (z : PowerIdealCoordinates J s p)
    (hz : powerPreviousDifferential J s p z=0)
    (hb : ∃ w : PowerIdealCoordinates J (s+1) (p+1),
      powerPreviousDifferential J (s+1) (p+1) w=
        PolynomialTorNaturality.coordinateMap (idealPowerMultiplication J fμ hfμ s) p z) :
    ∃ y : PowerIdealCoordinates J s (p+1),powerPreviousDifferential J s (p+1) y=z := by
  have hzcycle : (D).d (powerCoordinateInclusion J s p z)=0 := by
    rw [powerCoordinateInclusion_d,hz,(powerCoordinateInclusion J s p.pred).map_zero]
  let x : (D).cycles := ⟨powerCoordinateInclusion J s p z,((D).mem_cycles _).mpr hzcycle⟩
  let a : (D).cycles := ⟨b (minimumReesIndex n m J E hE hinit μ),
    ((D).mem_cycles _).mpr (minimumRees_basis_cycle n m J E hE hinit μ)⟩
  have hp : (D).classMap a * (D).classMap x=0 := by
    rw [← map_mul (D).classMap]
    apply ((D).classMap_eq_zero _).mpr
    obtain ⟨w,hw⟩ := hb
    refine ⟨powerCoordinateInclusion J (s+1) (p+1) w,?_⟩
    rw [powerCoordinateInclusion_d,hw]
    change _ = b (minimumReesIndex n m J E hE hinit μ)*powerCoordinateInclusion J s p z
    rw [minimumRees_basis_coefficient]
    simpa only [Nat.add_one,Nat.pred_succ] using!
      (powerCoordinateInclusion_multiplication J fμ hfμ s p z).symm
  have hx : (D).classMap x=0 :=
    minimumLiftRees_homology_mul_injective n m J E hE hinit μ hJ hμ hβ
      (hp.trans (mul_zero ((D).classMap a)).symm)
  exact powerCoordinateInclusion_reflects_boundaries J s p z (((D).classMap_eq_zero x).mp hx)

/-- **The multiplication assertion of Corollary 5.3 for `J`.** This is
Mathlib's actual derived Tor map of literal multiplication by `fμ`, for
every power and every homological degree. Its shift is proved above. -/
theorem corollary53_minimumLiftTor_injective
    (hμ : ∀ a : E,μ.val≤a.val)
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p (idealPowerMultiplication J fμ hfμ s)) := by
  apply PolynomialTorNaturality.torMap_injective_of_coordinate_reflection
  intro z hz hb
  apply minimumLift_coordinate_reflects_boundaries n m J E hE hinit μ hJ hμ hβ s p z
  · cases p <;> exact hz
  · exact hb

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.ChosenMinimumLiftTorInjection -/
section

/-! # Corollary 5.3 for every chosen monic lift of the minimum generator

The multiplier is an arbitrary supplied polynomial in J with the prescribed
leading monomial and leading coefficient one. It is not replaced by the
canonical triangular representative. If the supplied generators are
homogeneous, their usual internal degree shift is unchanged.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct
universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J=finiteSublatticeIdeal n E)
  (μ : E)

local notation "G" => canonicalPowerGenerators n J
local notation "hG" => canonicalPowerGroebner n m J
local notation "hu" => canonicalPowerUnitLeading n m J
local notation "I" => finiteSublatticeIdeal n (k:=K) E
local notation "hi" => sublatticePowerInitial n m J E hE hinit
local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "c" => initialReesKoszulBasis m J I hi G hG hu
local notation "w" => reesKoszulWeight m J
local notation "iμ" => minimumReesIndex n m J E hE hinit μ

variable (f : MvPolynomial (FiniteVariable.{u} n) K) (hf : f∈J)

/-- The actual tensor-basis coefficient has support only in power one and
exterior degree zero; its remaining coordinate is the polynomial coefficient. -/
theorem multiplierRees_repr (a : IdealReesKoszulIndex m J) :
    (b).repr (multiplierReesCycle J f hf).val a=
      (if ∅=a.2 then (1:K) else 0) •
        (if 1=a.1.1 then f.coeff a.1.2.val else 0) := by
  change (b).repr (multiplierReesCoefficient J f hf ⊗ₜ[K]
    (1 : Simplicial.Ambient (FiniteVariable.{u} n) K)) a=_
  rw [groebnerReesKoszulBasis,Module.Basis.tensorProduct_repr_tmul_apply,
    groebnerReesBasis_repr,← faceBasis_empty,Module.Basis.repr_self,Finsupp.single_apply]
  congr 1
  change ((AddMonoidAlgebra.single 1 f).coeff a.1.1).coeff a.1.2.val=_
  rw [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> rfl

theorem multiplierRees_repr_nonzero (a : IdealReesKoszulIndex m J)
    (ha : (b).repr (multiplierReesCycle J f hf).val a≠0) :
    a.1.1=1 ∧ a.2=∅ ∧ f.coeff a.1.2.val≠0 := by
  rw [multiplierRees_repr n m J f hf] at ha
  by_cases hF : ∅=a.2
  · rw [if_pos hF,one_smul] at ha
    by_cases hs : 1=a.1.1
    · rw [if_pos hs] at ha
      exact ⟨hs.symm,hF.symm,ha⟩
    · rw [if_neg hs] at ha
      exact (ha rfl).elim
  · rw [if_neg hF,zero_smul] at ha
    exact (ha rfl).elim

theorem multiplierRees_even :
    (idealReesKoszulDGA J).parity (multiplierReesCycle J f hf).val=
      (multiplierReesCycle J f hf).val := by
  change TensorExteriorKoszul.involute
    (multiplierReesCoefficient J f hf ⊗ₜ[K] (1 : Simplicial.Ambient (FiniteVariable.{u} n) K))=_
  rw [TensorExteriorKoszul.involute_tmul,map_one]
  rfl

variable (hdegree : m.degree f=finiteRowExponent n μ.val)
  (hmonic : m.leadingCoeff f=1)

include hdegree in
theorem chosenMinimumRees_level :
    (multiplierReesCycle J f hf).val∈OrderedBasis.level b w (w iμ) := by
  rw [OrderedBasis.level,(b).mem_span_image]
  intro a ha
  obtain ⟨hs,hF,hc⟩ := multiplierRees_repr_nonzero n m J f hf a
    (Finsupp.mem_support_iff.mp ha)
  have hh := m.le_degree (mem_support_iff.mpr hc)
  simpa only [Set.mem_setOf_eq,reesKoszulWeight,reesKoszulFineDegree,hF,faceExponent_empty,
    add_zero,minimumReesIndex,minimumLiftIndex,hdegree] using hh

include hdegree hmonic in
theorem chosenMinimumRees_leading :
    OrderedBasis.leadingProjection b c w (w iμ) (multiplierReesCycle J f hf).val=c iμ := by
  apply OrderedBasis.leadingProjection_eq_basis b c w iμ
  · rw [multiplierRees_repr]
    simp only [minimumReesIndex,minimumLiftIndex,if_pos rfl,one_smul]
    change f.coeff (m.degree f)=1 at hmonic
    simpa only [hdegree,ite_true,one_smul] using hmonic
  · rintro ⟨⟨s,a⟩,F⟩ ha hw
    obtain ⟨hs,hF,hc⟩ := multiplierRees_repr_nonzero n m J f hf (⟨s,a⟩,F) ha
    dsimp only at hs hF
    subst s
    subst F
    have he : a.val=finiteRowExponent n μ.val := by
      apply m.toSyn.injective
      simpa only [reesKoszulWeight,reesKoszulFineDegree,faceExponent_empty,add_zero,
        minimumReesIndex,minimumLiftIndex] using hw
    have hai : a=minimumLiftIndex n m J E hE hinit μ := Subtype.ext he
    exact congrArg (fun a : NonstandardIndex m (J^1) =>
      ((⟨1,a⟩ : GroebnerReesIndex J m),∅)) hai

variable (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
  (fun _ : FiniteVariable.{u} n => (1:ℕ))))

include hdegree hmonic in
/-- The ordered degeneration transports injection for every supplied monic
polynomial lift of the minimum generator. The polynomial itself is retained. -/
theorem chosenMinimumLiftRees_homology_mul_injective
    (hμ : ∀ a : E,μ.val≤a.val)
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) :
    Function.Injective (fun z : (idealReesKoszulDGA J).Homology =>
      (idealReesKoszulDGA J).classMap (multiplierReesCycle J f hf)*z) := by
  apply OrderedBasis.element_homology_mul_injective b c w
    (initialReesKoszul_product_homogeneous m J I hi G hG hu)
    (groebnerReesKoszul_product_leading m J I hi G hG hu)
    (fun a ha => (groebnerReesKoszul_one_weight m J G hG hu a ha).le)
    (groebnerReesKoszul_leading_one m J I hi G hG hu)
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (OrderedRees.differential_homogeneous m J I hi G hG hu)
    (OrderedRees.differential_leading m J I hi G hG hu)
    (OrderedRees.parity_homogeneous m J I hi G hG hu)
    (OrderedRees.parity_leading m J I hi G hG hu)
    (OrderedRees.all_cycle_lifts m J I hi G hG hu
      (sublattice_initial_homology_generated n m J E hE hinit)
      (ordered_relative_lifts_of_power_coordinate_lifts m J G hG hu I hi 1
        (sublattice_first_ordered_lifts n m J E hE hinit hJ hβ)))
    (w iμ) ⟨(multiplierReesCycle J f hf).val,
      chosenMinimumRees_level n m J E hE hinit μ f hf hdegree⟩
    (multiplierReesCycle J f hf).property (multiplierRees_even n J f hf)
    (c iμ) (minimumInitialRees_basis_cycle n m J E hE hinit μ)
    (chosenMinimumRees_leading n m J E hE hinit μ f hf hdegree hmonic)
    (minimumInitialRees_homology_mul_injective n m J E hE hinit μ hμ)

include hdegree hmonic in
/-- **Corollary 5.3 for the user's chosen corresponding generator.**
The actual derived map multiplies by the given f, for every s and p. -/
theorem corollary53_chosenMinimumLiftTor_injective
    (hμ : ∀ a : E,μ.val≤a.val)
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q) (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s)) :=
  multiplier_Tor_injective_of_Rees J f hf
    (chosenMinimumLiftRees_homology_mul_injective n m J E hE hinit μ f hf
      hdegree hmonic hJ hμ hβ) s p

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.MinimumMonomialTorInjection -/
section

/-! # Corollary 5.3: multiplication by the literal minimum row monomial

The coefficient map is polynomial multiplication by `u_μ`. The proof first
identifies this element inside the actual initial Rees algebra, then uses
the coefficient and exterior projections to obtain every actual Tor map.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct
universe u
variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E) (μ : E)

local notation "I" => finiteSublatticeIdeal n (k:=K) E

theorem minimumMonomial_mem : finiteRowMonomial n (k:=K) μ.val∈I :=
  Ideal.subset_span ⟨μ.val,μ.property,rfl⟩

/-- The displayed row ideal is fixed by every monomial initial operation. -/
theorem minimumMonomial_initial (o : MonomialOrder (FiniteVariable.{u} n)) :
    FourPapers.initialIdeal o I = I := by
  rw [finiteSublatticeIdeal_eq_monomialIdeal (k := K)]
  simpa only [CommAlg.Polymatroid.monomialIdeal] using!
    (FourPapers.initialIdeal_monomialSpan (k := K) (V := FiniteVariable.{u} n)
      o (finiteRowFamily n E : Set (Exponent (FiniteVariable.{u} n))))

include hE in
theorem minimumMonomialRees_homology_mul_injective
    (hμ : ∀ a : E,μ.val≤a.val) :
    Function.Injective (fun z : (idealReesKoszulDGA I).Homology =>
      (idealReesKoszulDGA I).classMap
        (multiplierReesCycle I (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ))*z) := by
  let m : MonomialOrder (FiniteVariable.{u} n) := MonomialOrder.lex
  have hinit : FourPapers.initialIdeal m I = I :=
    minimumMonomial_initial (K := K) n E m
  let c := initialReesKoszulBasis m I I (sublatticePowerInitial n m I E hE hinit)
    (canonicalPowerGenerators n I) (canonicalPowerGroebner n m I)
    (canonicalPowerUnitLeading n m I)
  have hval : c (minimumReesIndex n m I E hE hinit μ)=
      multiplierReesCoefficient I (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) ⊗ₜ[K]
        (1 : Simplicial.Ambient (FiniteVariable.{u} n) K) := by
    rw [show c=initialReesKoszulBasis m I I (sublatticePowerInitial n m I E hE hinit)
        (canonicalPowerGenerators n I) (canonicalPowerGroebner n m I)
        (canonicalPowerUnitLeading n m I) from rfl,
      initialReesKoszulBasis, minimumReesIndex, Module.Basis.tensorProduct_apply,
      faceBasis_empty]
    congr 1
    apply Subtype.ext
    rw [initialReesBasis_val]
    change AddMonoidAlgebra.single 1 (monomial (finiteRowExponent n μ.val) (1:K))=
      AddMonoidAlgebra.single 1 (finiteRowMonomial n μ.val)
    rw [finiteRowMonomial_eq_monomial]
  have he : (⟨c (minimumReesIndex n m I E hE hinit μ),
      ((idealReesKoszulDGA I).mem_cycles _).mpr
          (minimumInitialRees_basis_cycle n m I E hE hinit μ)⟩ : (idealReesKoszulDGA I).cycles)=
      multiplierReesCycle I (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) :=
    Subtype.ext hval
  have hi := minimumInitialRees_homology_mul_injective n m I E hE hinit μ hμ
  change Function.Injective (fun z : (idealReesKoszulDGA I).Homology =>
    (idealReesKoszulDGA I).classMap
      ⟨c (minimumReesIndex n m I E hE hinit μ),
        ((idealReesKoszulDGA I).mem_cycles _).mpr
          (minimumInitialRees_basis_cycle n m I E hE hinit μ)⟩*z) at hi
  simpa only [he] using hi

include hE in
/-- **The monomial multiplication assertion of Corollary 5.3.** It holds
for the actual derived Tor map and the actual polynomial `u_μ`, in every
power and every homological degree. -/
theorem corollary53_minimumMonomialTor_injective
    (hμ : ∀ a : E,μ.val≤a.val) (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p
      (idealPowerMultiplication I (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) s)) :=
  multiplier_Tor_injective_of_Rees I (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ)
    (minimumMonomialRees_homology_mul_injective n E hE μ hμ) s p

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.MinimumLiftGradedTorInjection -/
section

/-! # Corollary 5.3 with its exact internal degree shift

The actual derived multiplication map carries every homogeneous class of
integer internal degree q to degree q+d. This is proved on its literal
Koszul representative and retained together with injectivity.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg CommAlg.Koszul MvPolynomial CategoryTheory
universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

/-- Actual homogeneous polynomial coefficients of an ideal-power module. -/
def idealPowerDegree (J : Ideal (MvPolynomial V K)) (s : ℕ) (q : ℤ) :
    Set (idealPowerPiece J s) :=
  {a | IsWeightedHomogeneous (fun _ : V => (1:ℤ)) a.val q}

def idealPowerTorHasDegree (J : Ideal (MvPolynomial V K)) (s p : ℕ) (q : ℤ)
    (z : finitePolynomialTor p (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s))) : Prop :=
  PolynomialTorNaturality.HasDegree (idealPowerDegree J s) q p z

theorem homogeneous_nat_to_int (f : MvPolynomial V K) (d : ℕ)
    (hf : IsWeightedHomogeneous (fun _ : V => (1:ℕ)) f d) :
    IsWeightedHomogeneous (fun _ : V => (1:ℤ)) f (d:ℤ) := by
  intro a ha
  have he : Finsupp.weight (fun _ : V => (1:ℤ)) a=
      (Finsupp.weight (fun _ : V => (1:ℕ)) a : ℤ) := by
    simp only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,mul_one,Nat.cast_sum,Nat.cast_id]
  rw [he,hf ha]

/-- The exact integer internal-degree shift of literal polynomial
multiplication on Mathlib's derived Tor. -/
theorem idealPowerMultiplication_Tor_degree (J : Ideal (MvPolynomial V K))
    (f : MvPolynomial V K) (hf : f∈J) (d : ℕ)
    (hhom : IsWeightedHomogeneous (fun _ : V => (1:ℕ)) f d)
    (s p : ℕ) (q : ℤ)
    (z : finitePolynomialTor p (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s)))
    (hz : idealPowerTorHasDegree J s p q z) :
    idealPowerTorHasDegree J (s+1) p (q+(d:ℤ))
      (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s) z) := by
  unfold idealPowerTorHasDegree at hz ⊢
  apply PolynomialTorNaturality.torMap_hasDegree (k := K) (V := V)
    (M := ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s))
    (N := ModuleCat.of (MvPolynomial V K) (idealPowerPiece J (s+1)))
    (idealPowerDegree J s) (idealPowerDegree J (s+1)) (d:ℤ)
    (idealPowerMultiplication J f hf s) ?_ p q z hz
  intro r a ha
  change IsWeightedHomogeneous (fun _ : V => (1:ℤ)) (f*a.val) (r+(d:ℤ))
  simpa only [add_comm (d:ℤ) r] using (homogeneous_nat_to_int f d hhom).mul ha

variable {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J=finiteSublatticeIdeal n (k := K) E)
  (μ : E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1:ℕ))))

/-- **Corollary 5.3, every chosen homogeneous monic corresponding lift.**
This combines the literal derived injection and its exact shift in every
integer internal degree. -/
theorem corollary53_chosenMinimumLift_graded
    (hμ : ∀ a : E,μ.val≤a.val)
    (hβ : ∀ p q,sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q=
      sublatticeMonomialPowerBettiNumber (K:=K) n E 1 p q)
    (f : MvPolynomial (FiniteVariable.{u} n) K) (hf : f∈J)
    (hdegree : m.degree f=finiteRowExponent n μ.val) (hmonic : m.leadingCoeff f=1)
    (hhom : IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1:ℕ)) f d)
    (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s)) ∧
    (∀ (q : ℤ) z,idealPowerTorHasDegree J s p q z→
      idealPowerTorHasDegree J (s+1) p (q+(d:ℤ))
        (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s) z)) :=
  ⟨corollary53_chosenMinimumLiftTor_injective n m J E hE hinit μ f hf hdegree hmonic hJ hμ hβ s p,
    fun q z hz => idealPowerMultiplication_Tor_degree J f hf d hhom s p q z hz⟩

include hE in
/-- The literal monomial multiplier has the same exact integer degree
shift, for every homogeneous Tor class and every power. -/
theorem corollary53_minimumMonomial_graded
    (hμ : ∀ a : E,μ.val≤a.val) (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p
      (idealPowerMultiplication (finiteSublatticeIdeal n (k:=K) E)
        (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) s)) ∧
    (∀ (q : ℤ) z,idealPowerTorHasDegree (finiteSublatticeIdeal n (k := K) E) s p q z→
      idealPowerTorHasDegree (finiteSublatticeIdeal n (k := K) E) (s+1) p (q+(d:ℤ))
        (PolynomialTorNaturality.torMap p
          (idealPowerMultiplication (finiteSublatticeIdeal n (k := K) E)
            (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) s) z)) := by
  refine ⟨corollary53_minimumMonomialTor_injective n E hE μ hμ s p,?_⟩
  have hhom : IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1:ℕ))
      (finiteRowMonomial n (k:=K) μ.val) d := by
    rw [finiteRowMonomial_eq_monomial]
    simpa only [MvPolynomial.IsHomogeneous, Pi.one_def] using
      MvPolynomial.isHomogeneous_monomial (1 : K) (finiteRowExponent_degree (n := n) μ.val)
  intro q z hz
  exact idealPowerMultiplication_Tor_degree (finiteSublatticeIdeal n (k := K) E)
    (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) d hhom s p q z hz

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.MinimumLiftScalarNormalization -/
section

/-! # The minimum-generator map without a leading-coefficient convention

Every nonzero corresponding generator is a nonzero field scalar times a
monic corresponding generator. The proof below retains the literal Rees
cycle and actual derived multiplication map throughout this normalization.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 650000
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg CommAlg.Koszul MvPolynomial CategoryTheory
open scoped TensorProduct
universe u

section Scalar
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

/-- Scalar normalization preserves the actual coefficient and exterior cycle. -/
theorem multiplierReesCycle_smul (J : Ideal (MvPolynomial V K))
    (f : MvPolynomial V K) (hf : f ∈ J) (c : K) (hcf : c • f ∈ J) :
    multiplierReesCycle J (c • f) hcf = c • multiplierReesCycle J f hf := by
  apply Subtype.ext
  change multiplierReesCoefficient J (c • f) hcf ⊗ₜ[K]
      (1 : Simplicial.Ambient V K) =
    c • (multiplierReesCoefficient J f hf ⊗ₜ[K] (1 : Simplicial.Ambient V K))
  rw [TensorProduct.smul_tmul']
  congr 1
  apply Subtype.ext
  change AddMonoidAlgebra.single 1 (c • f) = c • AddMonoidAlgebra.single 1 f
  exact (AddMonoidAlgebra.smul_single c 1 f).symm

end Scalar

variable {K : Type u} [Field K] {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J = finiteSublatticeIdeal n E)
  (μ : E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

/-- Every nonzero supplied polynomial with the minimum leading monomial
gives an injective multiplier on the actual Rees Koszul homology. -/
theorem chosenMinimumGeneratorRees_homology_mul_injective
    (hμ : ∀ a : E, μ.val ≤ a.val)
    (hβ : ∀ p q, sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q =
      sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)
    (f : MvPolynomial (FiniteVariable.{u} n) K) (hf : f ∈ J) (hf0 : f ≠ 0)
    (hdegree : m.degree f = finiteRowExponent n μ.val) :
    Function.Injective (fun z : (idealReesKoszulDGA J).Homology =>
      (idealReesKoszulDGA J).classMap (multiplierReesCycle J f hf) * z) := by
  let c : K := m.leadingCoeff f
  have hc : c ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf0
  let g : MvPolynomial (FiniteVariable.{u} n) K := c⁻¹ • f
  have hg : g ∈ J := (J.restrictScalars K).smul_mem c⁻¹ hf
  have hgdegree : m.degree g = finiteRowExponent n μ.val :=
    (m.degree_smul_of_isRegular (IsRegular.of_ne_zero (inv_ne_zero hc))).trans hdegree
  have hgmonic : m.leadingCoeff g = 1 := by
    change g.coeff (m.degree g) = 1
    rw [hgdegree, ← hdegree]
    change (c⁻¹ • f).coeff (m.degree f) = 1
    rw [coeff_smul]
    exact inv_mul_cancel₀ hc
  have hfg : f = c • g := by
    change f = c • (c⁻¹ • f)
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hcycle : multiplierReesCycle J f hf = c • multiplierReesCycle J g hg := by
    have hcf : c • g ∈ J := hfg ▸ hf
    simpa only [← hfg] using multiplierReesCycle_smul J g hg c hcf
  have hclass : (idealReesKoszulDGA J).classMap (multiplierReesCycle J f hf) =
      c • (idealReesKoszulDGA J).classMap (multiplierReesCycle J g hg) := by
    rw [hcycle, map_smul (idealReesKoszulDGA J).classMap]
  have hinj := chosenMinimumLiftRees_homology_mul_injective n m J E hE hinit μ
    g hg hgdegree hgmonic hJ hμ hβ
  intro z t hzt
  apply hinj
  apply smul_right_injective (M := (idealReesKoszulDGA J).Homology) hc
  simpa only [hclass, smul_mul_assoc] using hzt

/-- **Corollary 5.3, arbitrary chosen corresponding generator.**
The supplied generator is normalized by its own nonzero leading coefficient;
no normalization assumption remains in the actual Tor map. -/
theorem corollary53_chosenMinimumGeneratorTor_injective
    (hμ : ∀ a : E, μ.val ≤ a.val)
    (hβ : ∀ p q, sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q =
      sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)
    (f : MvPolynomial (FiniteVariable.{u} n) K) (hf : f ∈ J) (hf0 : f ≠ 0)
    (hdegree : m.degree f = finiteRowExponent n μ.val) (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s)) :=
  multiplier_Tor_injective_of_Rees J f hf
    (chosenMinimumGeneratorRees_homology_mul_injective n m J E hE hinit μ hJ
      hμ hβ f hf hf0 hdegree) s p

/-- The same specified generator shifts every actual integer Tor degree by d. -/
theorem corollary53_chosenMinimumGenerator_graded
    (hμ : ∀ a : E, μ.val ≤ a.val)
    (hβ : ∀ p q, sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q =
      sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)
    (f : MvPolynomial (FiniteVariable.{u} n) K) (hf : f ∈ J) (hf0 : f ≠ 0)
    (hdegree : m.degree f = finiteRowExponent n μ.val)
    (hhom : IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1 : ℕ)) f d)
    (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s)) ∧
    (∀ (q : ℤ) z, idealPowerTorHasDegree J s p q z →
      idealPowerTorHasDegree J (s+1) p (q+(d : ℤ))
        (PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s) z)) :=
  ⟨corollary53_chosenMinimumGeneratorTor_injective n m J E hE hinit μ hJ hμ hβ
      f hf hf0 hdegree s p,
    fun q z hz => idealPowerMultiplication_Tor_degree J f hf d hhom s p q z hz⟩

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.MinimumGeneratorPaperTor -/
section

/-! # The minimum-generator injections after swapping the Tor arguments

Corollary 5.3 displays `Tor^S(k,-)`; the preceding graded endpoints use that
order. These companions use Mathlib's literal `Tor^S(-,k)` map and prove the
same assertion through the natural tensor-braiding comparison. The integer
grading is the standard Koszul grading transported through that comparison.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open CategoryTheory CommAlg.Koszul MvPolynomial

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

/-- The usual internal grading on actual `Tor^S(J^s,k)`, read through the
fixed natural Koszul comparison. Every integer degree is allowed. -/
def idealPowerPaperTorHasDegree (J : Ideal (MvPolynomial V K)) (s p : ℕ) (q : ℤ)
    (z : ((Tor (ModuleCat (MvPolynomial V K)) p).obj
      (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s))).obj
        (residueCoefficientModule (V := V) (k := K))) : Prop :=
  idealPowerTorHasDegree J s p q
    ((finitePolynomialTorPaperIso p
      (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s))).inv z)

/-- Literal polynomial multiplication has the expected shift on
`Tor^S(-,k)` itself. -/
theorem idealPowerMultiplication_paperTor_degree (J : Ideal (MvPolynomial V K))
    (f : MvPolynomial V K) (hf : f ∈ J) (d : ℕ)
    (hhom : IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) f d)
    (s p : ℕ) (q : ℤ) (z)
    (hz : idealPowerPaperTorHasDegree J s p q z) :
    idealPowerPaperTorHasDegree J (s+1) p (q+(d : ℤ))
      (PolynomialTorNaturality.paperTorMap p (idealPowerMultiplication J f hf s) z) := by
  have h := PolynomialTorNaturality.finitePolynomialTorPaperIso_inv_naturality p
    (idealPowerMultiplication J f hf s)
  have he := congrArg (fun a => ModuleCat.Hom.hom a z) h
  change PolynomialTorNaturality.torMap p (idealPowerMultiplication J f hf s)
      ((finitePolynomialTorPaperIso p
        (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s))).inv z) =
    (finitePolynomialTorPaperIso p
      (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J (s+1)))).inv
        (PolynomialTorNaturality.paperTorMap p (idealPowerMultiplication J f hf s) z) at he
  change idealPowerTorHasDegree J (s+1) p (q+(d : ℤ)) _
  rw [← he]
  exact idealPowerMultiplication_Tor_degree J f hf d hhom s p q _ hz

variable {d : ℕ} (n : Fin d → ℕ)
  (m : MonomialOrder (FiniteVariable.{u} n))
  (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
  (hinit : FourPapers.initialIdeal m J = finiteSublatticeIdeal n (k := K) E)
  (μ : E)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K
    (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

/-- **Corollary 5.3, the specified lift in the swapped Tor convention.**
No monic normalization is required of the supplied corresponding generator. -/
theorem corollary53_chosenMinimumGenerator_paperTor
    (hμ : ∀ a : E, μ.val ≤ a.val)
    (hβ : ∀ p q, sublatticePowerBettiNumber n m J E hE hinit hJ 1 p q =
      sublatticeMonomialPowerBettiNumber (K := K) n E 1 p q)
    (f : MvPolynomial (FiniteVariable.{u} n) K) (hf : f ∈ J) (hf0 : f ≠ 0)
    (hdegree : m.degree f = finiteRowExponent n μ.val)
    (hhom : IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1 : ℕ)) f d)
    (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.paperTorMap p
      (idealPowerMultiplication J f hf s)) ∧
    (∀ (q : ℤ) z, idealPowerPaperTorHasDegree J s p q z →
      idealPowerPaperTorHasDegree J (s+1) p (q+(d : ℤ))
        (PolynomialTorNaturality.paperTorMap p (idealPowerMultiplication J f hf s) z)) :=
  ⟨PolynomialTorNaturality.paperTorMap_injective p (idealPowerMultiplication J f hf s)
      (corollary53_chosenMinimumGeneratorTor_injective n m J E hE hinit μ hJ
        hμ hβ f hf hf0 hdegree s p),
    fun q z hz => idealPowerMultiplication_paperTor_degree J f hf d hhom s p q z hz⟩

include hE in
/-- **Corollary 5.3, the minimum monomial in the swapped Tor convention.** -/
theorem corollary53_minimumMonomial_paperTor
    (hμ : ∀ a : E, μ.val ≤ a.val) (s p : ℕ) :
    Function.Injective (PolynomialTorNaturality.paperTorMap p
      (idealPowerMultiplication (finiteSublatticeIdeal n (k := K) E)
        (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) s)) ∧
    (∀ (q : ℤ) z, idealPowerPaperTorHasDegree (finiteSublatticeIdeal n (k := K) E) s p q z →
      idealPowerPaperTorHasDegree (finiteSublatticeIdeal n (k := K) E) (s+1) p (q+(d : ℤ))
        (PolynomialTorNaturality.paperTorMap p
          (idealPowerMultiplication (finiteSublatticeIdeal n (k := K) E)
            (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) s) z)) := by
  refine ⟨PolynomialTorNaturality.paperTorMap_injective p _
    (corollary53_minimumMonomialTor_injective n E hE μ hμ s p), ?_⟩
  have hhom : IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1 : ℕ))
      (finiteRowMonomial n (k := K) μ.val) d := by
    rw [finiteRowMonomial_eq_monomial]
    simpa only [MvPolynomial.IsHomogeneous, Pi.one_def] using
      MvPolynomial.isHomogeneous_monomial (1 : K) (finiteRowExponent_degree (n := n) μ.val)
  intro q z hz
  exact idealPowerMultiplication_paperTor_degree (finiteSublatticeIdeal n (k := K) E)
    (finiteRowMonomial n μ.val) (minimumMonomial_mem n E μ) d hhom s p q z hz

end FourPapers.Sublattice

end
end


end
