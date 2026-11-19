module
public import SourceBridges
public import Cor53GradedSupport
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Classical MvPolynomial CategoryTheory
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace PalomarSublatticeCor53
universe u
variable {V k : Type u} [Field k] [Fintype V] [LinearOrder V]

/-- The source uses scalar-restricted ideal coefficients with the identical
polynomials and polynomial action. Its outgoing differential is the same
literal coordinate Koszul differential, including degree zero. -/
private theorem sourcePrevious_eq (J : Ideal (MvPolynomial V k)) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) p) :
    FourPapers.Sublattice.powerPreviousDifferential J s p z = Koszul.previous (J^s) p z := by
  cases p with
  | zero => rfl
  | succ p =>
    exact (LinearMap.congr_fun
      (PalomarSublatticeCor53Core.Koszul.differential_eq_source (J^s) p) z).symm

private theorem sourceCoefficientMap_eq (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ) (z : Koszul.Coordinates (J^s) p) :
    FourPapers.PolynomialTorNaturality.coordinateMap
      (FourPapers.Sublattice.idealPowerMultiplication J f hf s) p z =
        coefficientMap J f hf s p z := by
  apply Finsupp.ext
  intro a
  apply Subtype.ext
  rw [coefficientMap_apply_val]
  simp [FourPapers.PolynomialTorNaturality.coordinateMap,
    FourPapers.Sublattice.idealPowerMultiplication]

/-- Literal Rees boundary reflection and the genuine homogeneous filling
projector give injectivity of this very graded quotient map. -/
private theorem homologyMap_injective_of_rees
    (o : MonomialOrder V) (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ)
    (hJs : (J^s).IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (hRees : Function.Injective (fun z : (FourPapers.Sublattice.idealReesKoszulDGA J).Homology =>
      (FourPapers.Sublattice.idealReesKoszulDGA J).classMap
        (FourPapers.Sublattice.multiplierReesCycle J f hf) * z)) :
    Function.Injective (homologyMap J f hf d hhom s p q) := by
  apply homologyMap_injective_of_boundary_reflection
  intro z hz
  by_cases hq : 0 ≤ q
  · have hQ : (q.toNat : ℤ)=q := Int.toNat_of_nonneg hq
    change coefficientMap J f hf s p z.val ∈
      Submodule.map (Koszul.differential (J^(s+1)) p)
        (Koszul.piece (J^(s+1)) (q+(d : ℤ)) (p+1)) at hz
    obtain ⟨b,hb,hbz⟩ := hz
    have hzcycle : FourPapers.Sublattice.powerPreviousDifferential J s p z.val=0 := by
      rw [sourcePrevious_eq]
      exact z.property.1
    have hboundary : ∃ b' : FourPapers.Sublattice.PowerIdealCoordinates J (s+1) (p+1),
        FourPapers.Sublattice.powerPreviousDifferential J (s+1) (p+1) b' =
          FourPapers.PolynomialTorNaturality.coordinateMap
            (FourPapers.Sublattice.idealPowerMultiplication J f hf s) p z.val := by
      refine ⟨b,?_⟩
      rw [sourcePrevious_eq,sourceCoefficientMap_eq]
      exact hbz
    obtain ⟨w,hw⟩ := FourPapers.Sublattice.multiplier_coordinate_reflects_boundaries J f hf hRees s p z.val
      hzcycle hboundary
    let P := FourPapers.Sublattice.canonicalQuotientGroebnerData o (J^s)
    let H := hJs
    have hpiece : z.val ∈ FourPapers.Sublattice.actualIdealOrdinaryPiece P q.toNat p := by
      apply (PalomarSublatticeCor53Core.Koszul.piece_nat_eq P H q.toNat p).le
      rw [hQ]
      exact z.property.2
    have hw' : FourPapers.PolynomialCoordinateTor.differential
        (K := k) (V := V) (M := P.ideal) p w = z.val := by
      change FourPapers.Sublattice.actualIdealCoordinateDifferential (J^s) p w=z.val
      rw [← PalomarSublatticeCor53Core.Koszul.differential_eq_source]
      exact (sourcePrevious_eq J s (p+1) w).symm.trans hw
    obtain ⟨y,hy⟩ := FourPapers.Sublattice.ordinaryIdeal_boundary_reflects P H q.toNat p ⟨z.val,hpiece⟩ w hw'
    change z.val ∈ Submodule.map (Koszul.differential (J^s) p)
      (Koszul.piece (J^s) q (p+1))
    let t : Koszul.Coordinates (J^s) (p+1) := y.val
    refine ⟨t,?_,?_⟩
    · have ht : t ∈ Koszul.piece (J^s) (q.toNat : ℤ) (p+1) :=
        (PalomarSublatticeCor53Core.Koszul.piece_nat_eq P H q.toNat (p+1)).ge y.property
      exact (congrArg (fun a : ℤ => t ∈ Koszul.piece (J^s) a (p+1)) hQ).mp ht
    · have hv := congrArg (fun a : FourPapers.Sublattice.actualIdealOrdinaryPiece P q.toNat p => a.val) hy
      rw [FourPapers.Sublattice.actualIdealOrdinaryDifferential_val] at hv
      rw [← PalomarSublatticeCor53Core.Koszul.differential_eq_source] at hv
      exact hv
  · have hzero : Koszul.piece (J^s) q p=⊥ :=
      PalomarSublatticeCor53Core.Koszul.piece_negative (J^s) (lt_of_not_ge hq) p
    have hcycles : Koszul.cycles (J^s) q p = ⊥ := by
      simp [Koszul.cycles,hzero]
    haveI : Subsingleton (Koszul.cycles (J^s) q p) := by
      rw [hcycles]
      infer_instance
    have hz0 : z=0 := Subsingleton.elim _ _
    rw [hz0]
    exact Submodule.zero_mem _


end PalomarSublatticeCor53

namespace PalomarSublatticeCor53
open FourPapers.Sublattice
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]

/-- Corollary5.3 with the actual chosen non-monic generator: its literal Tor
multiplication is injective, as is the same multiplication on every actual
integer homogeneous component. No normalization or injectivity certificate is assumed. -/
theorem corollary53_chosen_generator_graded
    (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E) (μ : E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hμ : ∀ a : E, μ.val ≤ a.val)
    (hβ : ∀ p q : ℕ, Koszul.betti J p (q : ℤ) =
      Koszul.betti (sublatticeIdeal n (k := k) E) p (q : ℤ))
    (f : MvPolynomial (FiniteVariable.{u} n) k) (hf : f ∈ J) (hf0 : f ≠ 0)
    (hdegree : o.degree f = finiteRowExponent n μ.val)
    (hhom : f.IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1 : ℕ)) d)
    (s p : ℕ) :
    Function.Injective (coefficientFirstTorMap J f hf s p) ∧
      Function.Injective (torMap J f hf s p) ∧
      ∀ q : ℤ, Function.Injective (homologyMap J f hf d hhom s p q) := by
  have htor := chosen_generator_actualTor_injective n o J E hE hinit μ hJ hμ hβ
    f hf hf0 hdegree hhom s p
  refine ⟨coefficientFirstTorMap_injective_of_torMap J f hf s p htor,htor,?_⟩
  have hβsource := firstPower_bridge n o J E hE hinit hJ hβ
  have hRees := FourPapers.Sublattice.chosenMinimumGeneratorRees_homology_mul_injective
    n o J E hE hinit μ hJ hμ hβsource f hf hf0 hdegree
  intro q
  exact homologyMap_injective_of_rees o J f hf d hhom s p q
    (FourPapers.Sublattice.homogeneousIdealPower n J hJ s) hRees


/-- The minimum row monomial is literally a generator of the displayed ideal. -/
theorem minimum_monomial_mem (E : Finset (FiniteTuple n)) (μ : E) :
    rowMonomial n (k := k) μ.val ∈ sublatticeIdeal n E :=
  Ideal.subset_span ⟨μ.val,μ.property,rfl⟩
/-- The actual row product has its original total degree d, including d=0. -/
theorem rowMonomial_homogeneous (a : FiniteTuple n) :
    (rowMonomial n (k := k) a).IsWeightedHomogeneous
      (fun _ : FiniteVariable.{u} n => (1 : ℕ)) d := by
  change (FourPapers.Sublattice.finiteRowMonomial n (k := k) a).IsWeightedHomogeneous _ d
  rw [FourPapers.Sublattice.finiteRowMonomial_eq_monomial]
  simpa only [MvPolynomial.IsHomogeneous,Pi.one_def] using
    MvPolynomial.isHomogeneous_monomial (1 : k)
      (FourPapers.Sublattice.finiteRowExponent_degree (n := n) a)
/-- The explicit monomial assertion of Corollary5.3 has no deformation or
first-power Betti premise. Its two maps use the literal minimum row product. -/
theorem corollary53_minimum_monomial_graded
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E) (μ : E)
    (hμ : ∀ a : E, μ.val ≤ a.val) (s p : ℕ) :
    Function.Injective (coefficientFirstTorMap (sublatticeIdeal n (k := k) E)
      (rowMonomial n μ.val) (minimum_monomial_mem n E μ) s p) ∧
    Function.Injective (torMap (sublatticeIdeal n (k := k) E) (rowMonomial n μ.val)
      (minimum_monomial_mem n E μ) s p) ∧
    ∀ q : ℤ, Function.Injective (homologyMap (sublatticeIdeal n (k := k) E)
      (rowMonomial n μ.val) (minimum_monomial_mem n E μ) d
      (rowMonomial_homogeneous n μ.val) s p q) := by
  let o : MonomialOrder (FiniteVariable.{u} n) :=
    @MonomialOrder.degLex (FiniteVariable.{u} n) (finiteVariableLinearOrder n)
      (@Finite.to_wellFoundedGT (FiniteVariable.{u} n) (inferInstance)
        (finiteVariableLinearOrder n).toPreorder)
  have htor : Function.Injective (torMap (sublatticeIdeal n (k := k) E)
      (rowMonomial n μ.val) (minimum_monomial_mem n E μ) s p) := by
    apply nativeTorMap_injective_of_source
    exact (FourPapers.Sublattice.corollary53_minimumMonomial_paperTor
      (K := k) n E hE μ hμ s p).1
  refine ⟨coefficientFirstTorMap_injective_of_torMap _ _ _ s p htor,htor,?_⟩
  intro q
  have hJs : ((sublatticeIdeal n (k := k) E)^s).IsHomogeneous
      (weightedHomogeneousSubmodule k (fun _ : FiniteVariable.{u} n => (1 : ℕ))) := by
    rw [← powerFamily_ideal n E s]
    exact FourPapers.Sublattice.monomialIdeal_isOrdinaryHomogeneous _
  exact homologyMap_injective_of_rees o (sublatticeIdeal n (k := k) E)
    (rowMonomial n μ.val) (minimum_monomial_mem n E μ) d
    (rowMonomial_homogeneous n μ.val) s p q hJs
    (FourPapers.Sublattice.minimumMonomialRees_homology_mul_injective
      (K := k) n E hE μ hμ)

end PalomarSublatticeCor53
