module
public import graph_foundation.part014
public import shared_results.part020_groebner_rees_order_comparison

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedReesHomologyGeneration -/
section

/-! # Unit-color generation of the actual multi-Rees Koszul homology

Every class used here is represented by a genuine Koszul cycle. The
minimum-color algebra equivalence transports the ordinary colored Rees
generation theorem to the original mixed-product tensor algebra. The final
statement is independent of the particular triangular Gröbner basis chosen
for the filtered transfer argument.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open IntegerFiltered.MultiplicativeFiltration
open scoped TensorProduct
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {E : Fin r → Finset (FiniteTuple n)}
variable {k : Type u} [Field k]

/-- Actual total color degree one in the monomial/exterior tensor basis. -/
def actualMixedFirstPiece : Submodule k (MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E)) :=
  Submodule.span k (mixedTensorBasis '' {a : MixedTensorIndex.{u} E | a.1.1.degree=1})

variable (hE : ColoredLatticeClosed n E)

abbrev minimumColorRetraction :=
  MinimumDegreeDiagonal.retraction (coloredPowerPieces (E := E) (k := k))
    (powerFace_one_mem (coloredReesClosure hE))
    (powerFace_mul_mem (coloredReesClosure hE))
    coloredFineColorDegree coloredFineReesDegree (coloredPowerFace_below_zero (E := E))

lemma mixedMinimum_symm_single_first
    (g : ReesFineDegree.{u} (coloredRows (r := r) n))
    (hg : g.1=1) (hcolor : coloredFineColorDegree g=coloredFineReesDegree g)
    (x : coloredPowerPieces (E := E) (k := k) g) :
    (mixedMinimumLinearEquiv hE).symm
      (minimumColorRetraction hE (reesKoszulSingle (coloredReesClosure hE) g x)) ∈
        actualMixedFirstPiece (E := E) (k := k) := by
  let b := totalFaceBasis (k := k) (koszulFaces (exponentPowerFamily
    (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) g.1) g.2)
  let f := (mixedMinimumLinearEquiv (k := k) hE).symm.toLinearMap.comp
    ((minimumColorRetraction hE).toLinearMap.comp (reesKoszulSingle (coloredReesClosure hE) g))
  have hf : (⊤ : Submodule k (coloredPowerPieces (E := E) (k := k) g)) ≤
      (actualMixedFirstPiece (E := E) (k := k)).comap f := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨F,rfl⟩
    let i : MinimumColorIndex.{u} E := ⟨⟨g,F⟩,hcolor⟩
    have he : minimumColorRetraction (k := k) hE
        (reesKoszulSingle (coloredReesClosure hE) g (b F)) = minimumColorBasis hE i := by
      apply Subtype.ext
      apply Subtype.ext
      change (MinimumDegreeDiagonal.projectionLinear
        (coloredPowerPieces (E := E) (k := k))
        (powerFace_one_mem (coloredReesClosure hE))
        (powerFace_mul_mem (coloredReesClosure hE))
        coloredFineColorDegree coloredFineReesDegree
        (coefficientSingle (coloredPowerPieces (E := E) (k := k))
          (powerFace_one_mem (coloredReesClosure hE))
          (powerFace_mul_mem (coloredReesClosure hE)) g (b F))).val = _
      rw [MinimumDegreeDiagonal.projectionLinear_single,if_pos hcolor,coefficientSingle_val,
        totalFaceBasis_val,minimumColorBasis_val]
    have hinv : (mixedMinimumLinearEquiv (k := k) hE).symm (minimumColorBasis hE i)=
        mixedTensorBasis (mixedMinimumIndexEquiv.symm i) := by
      apply (mixedMinimumLinearEquiv (k := k) hE).injective
      rw [LinearEquiv.apply_symm_apply]
      change minimumColorBasis hE i =
        mixedTensorBasis.equiv (minimumColorBasis hE) mixedMinimumIndexEquiv
          (mixedTensorBasis (mixedMinimumIndexEquiv.symm i))
      rw [Module.Basis.equiv_apply,Equiv.apply_symm_apply]
    change (mixedMinimumLinearEquiv hE).symm
      (minimumColorRetraction hE (reesKoszulSingle (coloredReesClosure hE) g (b F))) ∈
        actualMixedFirstPiece (E := E) (k := k)
    rw [he,hinv]
    apply Submodule.subset_span
    refine ⟨mixedMinimumIndexEquiv.symm i,?_,rfl⟩
    have hi := congrArg (fun a : MinimumColorIndex.{u} E => a.val.1.1)
      (mixedMinimumIndexEquiv.apply_symm_apply i)
    exact hi.trans hg
  exact hf (show x∈(⊤ : Submodule k (coloredPowerPieces (E := E) (k := k) g)) from trivial)

set_option maxHeartbeats 250000 in
set_option backward.isDefEq.respectTransparency true in
lemma firstMinimumColorClasses_transport
    (z : (minimumColorReesDifferential (k := k) hE).Homology)
    (hz : z∈firstMinimumColorClasses (k := k) hE) :
    (mixedMinimumHomologyEquiv (k := k) hE).symm z∈
      selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E))
        (actualMixedFirstPiece (E := E) (k := k)) := by
  obtain ⟨α,hα,x,rfl⟩ := hz
  let D := MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E)
  let D' := minimumColorReesDifferential (k := k) hE
  let e := mixedMinimumAlgEquiv (k := k) hE
  have hd : ∀ y, e (D.d y) = D'.d (e y) := by
    intro y
    exact mixedMinimum_intertwines (k := k) hE y
  let c := ParityDifferential.cyclesEquiv D D' e hd
  let y' : D'.cycles := ParityDifferential.cyclesMap
    (reesKoszulCoordinateDifferential (k := k) (coloredReesClosure hE)) D' (minimumColorRetraction (k := k) hE)
    (fun y => Subtype.ext (MinimumDegreeDiagonal.projection_differential
      (coloredPowerPieces (E := E) (k := k)) (powerFace_one_mem (coloredReesClosure hE))
      (powerFace_mul_mem (coloredReesClosure hE)) coloredFineColorDegree coloredFineReesDegree
      (coloredPowerFace_below_zero (E := E)) exteriorParityDifferential
      (coloredPieceBoundary (E := E)) (coloredPieceParity (E := E)) y))
    (reesCycleSingle (k := k) (coloredReesClosure hE) (1,α) x)
  let y := c.symm y'
  refine ⟨y,?_,?_⟩
  · exact mixedMinimum_symm_single_first hE (1,α) rfl hα x.val
  · apply (mixedMinimumHomologyEquiv (k := k) hE).injective
    rw [AlgEquiv.apply_symm_apply]
    change ParityDifferential.homologyEquiv D D' e hd
      (D.classMap y)=D'.classMap y'
    exact (ParityDifferential.homologyEquiv_classMap D D' e hd y).trans
      (congrArg D'.classMap (c.apply_symm_apply y'))

include hE in
/-- Generation in total color degree one in the literal multi-Rees Koszul algebra. -/
theorem mixedReesHomology_generated_in_total_color_one :
    Algebra.adjoin k (selectedHomologyClasses
      (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E))
      (actualMixedFirstPiece (E := E) (k := k)))=⊤ := by
  let S := Algebra.adjoin k (selectedHomologyClasses
    (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E))
    (actualMixedFirstPiece (E := E) (k := k)))
  let e := mixedMinimumHomologyEquiv (k := k) hE
  have hh : Algebra.adjoin k (firstMinimumColorClasses (k := k) hE) ≤ S.comap e.symm.toAlgHom := by
    apply Algebra.adjoin_le
    intro z hz
    exact Algebra.subset_adjoin (firstMinimumColorClasses_transport hE z hz)
  rw [minimumColorReesHomology_generated hE k] at hh
  apply top_unique
  intro z _
  have hz := hh (show e z∈(⊤ : Subalgebra k (minimumColorReesDifferential (k := k) hE).Homology) from trivial)
  change e.symm (e z)∈S at hz
  simpa only [e.symm_apply_apply] using hz

variable (o : MonomialOrder (FiniteVariable.{u} n))
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) k))
  (hinit : ∀ a, initialIdealForBasis o (powerProduct J a)=powerProduct (coloredIdeals (k := k) n E) a)
  (G : (ULift.{u} (Fin r) →₀ ℕ) → Set (MvPolynomial (FiniteVariable.{u} n) k))
  (hG : ∀ a, o.IsGroebnerBasis (G a) (powerProduct J a))
  (hu : ∀ a g, g∈G a → g≠0 → IsUnit (o.leadingCoeff g))

lemma actualMixedFirstPiece_le_initialSelected :
    actualMixedFirstPiece (E := E) (k := k) ≤
      MixedTransfer.Auxiliary.initialSelectedPiece o J (coloredIdeals (k := k) n E) hinit G hG hu
        (Set.range (fun c : ULift.{u} (Fin r) => Finsupp.single c 1)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,F⟩,ha,rfl⟩
  have hm : monomial a.2.val (1:k) ∈ initialIdealForBasis o (powerProduct J a.1) := by
    rw [hinit,← mixedRowPowerFamily_ideal]
    exact (monomial_mem_iff (k := k) _ _).mpr a.2.property
  let b : NonstandardIndex o (powerProduct J a.1) :=
    (nonstandardInitialIndexEquiv o (powerProduct J a.1) (G a.1) (hG a.1) (hu a.1)).symm ⟨a.2.val,hm⟩
  have hb : mixedCoefficientBasis (k := k) a =
      MixedTransfer.initialReesBasis o J (coloredIdeals (k := k) n E) hinit G hG hu ⟨a.1,b⟩ := by
    apply Subtype.ext
    rw [mixedCoefficientBasis_val,MixedTransfer.initialReesBasis_val]
    rfl
  have hc : a.1∈Set.range (fun c : ULift.{u} (Fin r) => Finsupp.single c 1) := by
    obtain ⟨c,hc⟩ := color_degree_one_eq_unit a.1 ha
    exact ⟨c,hc.symm⟩
  let Q := MixedTransfer.Auxiliary.initialSelectedPiece o J (coloredIdeals (k := k) n E)
    hinit G hG hu (Set.range (fun c : ULift.{u} (Fin r) => Finsupp.single c 1))
  have ht : mixedTensorBasis (k := k) (a,F) =
      mixedCoefficientBasis (k := k) a ⊗ₜ[k] mixedExteriorBasis (k := k) r F :=
    Module.Basis.tensorProduct_apply _ _ a F
  change mixedTensorBasis (k := k) (a,F) ∈ Q
  rw [ht,hb]
  -- Selection restricts only the coefficient degree. The entire exterior
  -- factor is included, so it is independent of the basis orientation.
  let f : Simplicial.Ambient (FiniteVariable.{u} n) k →ₗ[k]
      MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E) :=
    TensorProduct.mk k _ _
      (MixedTransfer.initialReesBasis o J (coloredIdeals (k := k) n E) hinit G hG hu ⟨a.1,b⟩)
  have htop : ⊤ ≤ Q.comap f := by
    rw [← (Simplicial.basis (V := FiniteVariable.{u} n) (k := k)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨G,rfl⟩
    refine Submodule.subset_span ⟨(⟨a.1,b⟩,G),hc,?_⟩
    rw [MixedTransfer.initialReesKoszulBasis, Module.Basis.tensorProduct_apply]
    rfl
  exact htop (show mixedExteriorBasis r F∈(⊤ : Submodule k
    (Simplicial.Ambient (FiniteVariable.{u} n) k)) from trivial)

include hE in
/-- **The monomial multi-Rees generation input in Theorem 5.5.** The selected
color degrees are precisely the coordinate units. The ideals and Koszul
differential are the literal ones used by the filtered transfer theorem. -/
theorem mixedReesHomology_generated_in_unit_colors :
    Algebra.adjoin k (selectedHomologyClasses
      (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E))
      (MixedTransfer.Auxiliary.initialSelectedPiece o J (coloredIdeals (k := k) n E) hinit G hG hu
        (Set.range (fun c : ULift.{u} (Fin r) => Finsupp.single c 1))))=⊤ := by
  apply top_unique
  rw [← mixedReesHomology_generated_in_total_color_one (k := k) hE]
  apply Algebra.adjoin_mono
  rintro z ⟨x,hx,hz⟩
  exact ⟨x,actualMixedFirstPiece_le_initialSelected o J hinit G hG hu hx,hz⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.mixedMinimum_intertwines
#print axioms FourPapers.Sublattice.mixedReesHomology_generated_in_unit_colors

end
end
end


end
