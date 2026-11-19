module
public import SourceBridges
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Classical MvPolynomial CategoryTheory
open scoped BigOperators
namespace PalomarSublatticeCor53
universe u
variable {V k : Type u} [Field k] [Fintype V] [LinearOrder V]

private theorem coefficientMap_single (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (a : Set.powersetCard V p) (x : ↥(J^s)) :
    coefficientMap J f hf s p (Finsupp.single a x) =
      Finsupp.single a (multiplication J f hf s x) := by
  simp [coefficientMap]

private theorem coefficientMap_apply_val (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) p) (a : Set.powersetCard V p) :
    (coefficientMap J f hf s p z a).val = f*(z a).val := by
  simp [coefficientMap,multiplication]

private theorem differential_single (I : Ideal (MvPolynomial V k)) (p : ℕ)
    (a : Set.powersetCard V (p+1)) (x : I) :
    Koszul.differential I p (Finsupp.single a x) =
      ∑ j : {j // j ∈ a.val}, Finsupp.single (Koszul.eraseIndex a j)
        ((X j.val * (((Koszul.eraseSign j.val a.val : ℤˣ) : ℤ) : MvPolynomial V k)) • x) := by
  simp only [Koszul.differential,LinearMap.restrictScalars_apply,Finsupp.lsum_single,
    LinearMap.sum_apply,LinearMap.comp_apply,Finsupp.lsingle_apply,LinearMap.lsmul_apply]

/-- The actual coefficient multiplier commutes with the deletion differential. -/
private theorem coefficientMap_differential (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) (p+1)) :
    coefficientMap J f hf s p (Koszul.differential (J^s) p z) =
      Koszul.differential (J^(s+1)) p (coefficientMap J f hf s (p+1) z) := by
  have h : (coefficientMap J f hf s p).comp (Koszul.differential (J^s) p) =
      (Koszul.differential (J^(s+1)) p).comp (coefficientMap J f hf s (p+1)) := by
    apply Finsupp.lhom_ext
    intro a x
    simp only [LinearMap.comp_apply,coefficientMap_single,differential_single,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [coefficientMap_single]
    congr 1
    exact (multiplication J f hf s).hom.map_smul _ x
  exact LinearMap.congr_fun h z

private theorem coefficientMap_previous (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s p : ℕ)
    (z : Koszul.Coordinates (J^s) p) :
    coefficientMap J f hf s p.pred (Koszul.previous (J^s) p z) =
      Koszul.previous (J^(s+1)) p (coefficientMap J f hf s p z) := by
  cases p with
  | zero => simp only [Koszul.previous,LinearMap.zero_apply,map_zero]
  | succ p => exact coefficientMap_differential J f hf s p z

private theorem coefficientMap_piece (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) (z : Koszul.Coordinates (J^s) p)
    (hz : z ∈ Koszul.piece (J^s) q p) :
    coefficientMap J f hf s p z ∈ Koszul.piece (J^(s+1)) (q+(d : ℤ)) p := by
  simp only [Koszul.piece,Submodule.mem_iInf,Submodule.mem_comap] at hz ⊢
  intro a
  have ha := hz a
  change (z a).val.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) (q-(p : ℤ)) at ha
  change (coefficientMap J f hf s p z a).val.IsWeightedHomogeneous
    (fun _ : V => (1 : ℤ)) ((q+(d : ℤ))-(p : ℤ))
  rw [coefficientMap_apply_val]
  convert (FourPapers.Sublattice.homogeneous_nat_to_int f d hhom).mul ha using 1 <;> omega

theorem multiplication_cycles (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) (z : Koszul.cycles (J^s) q p) :
    coefficientMap J f hf s p z.val ∈ Koszul.cycles (J^(s+1)) (q+(d : ℤ)) p := by
  refine ⟨?_,coefficientMap_piece J f hf d hhom s p q z.val z.property.2⟩
  change Koszul.previous (J^(s+1)) p (coefficientMap J f hf s p z.val)=0
  rw [← coefficientMap_previous,show Koszul.previous (J^s) p z.val=0 from z.property.1,map_zero]

/-- The induced linear map on the actual homogeneous cycles. -/
def cyclesMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.cycles (J^s) q p →ₗ[k] Koszul.cycles (J^(s+1)) (q+(d : ℤ)) p :=
  ((coefficientMap J f hf s p).domRestrict _).codRestrict _
    (fun z => multiplication_cycles J f hf d hhom s p q z)

theorem multiplication_boundaries (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.boundaries (J^s) q p ≤
      (Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p).comap
        (cyclesMap J f hf d hhom s p q) := by
  intro z hz
  change z.val ∈ Submodule.map (Koszul.differential (J^s) p)
    (Koszul.piece (J^s) q (p+1)) at hz
  obtain ⟨w,hw,hwz⟩ := hz
  change coefficientMap J f hf s p z.val ∈
    Submodule.map (Koszul.differential (J^(s+1)) p)
      (Koszul.piece (J^(s+1)) (q+(d : ℤ)) (p+1))
  refine ⟨coefficientMap J f hf s (p+1) w,
    coefficientMap_piece J f hf d hhom s (p+1) q w hw,?_⟩
  rw [← coefficientMap_differential,hwz]

/-- The literal induced map on the genuine degree-q Koszul homology quotient.
Its target degree is q+d for every signed integer q. -/
def homologyMap (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ) :
    Koszul.Homology (J^s) q p →ₗ[k] Koszul.Homology (J^(s+1)) (q+(d : ℤ)) p :=
  (Koszul.boundaries (J^s) q p).mapQ
    (Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p)
    (cyclesMap J f hf d hhom s p q) (multiplication_boundaries J f hf d hhom s p q)

/-- Actual boundary reflection is the exact quotient-injectivity criterion. -/
private theorem homologyMap_injective_of_boundary_reflection
    (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k) (hf : f ∈ J) (d : ℕ)
    (hhom : f.IsWeightedHomogeneous (fun _ : V => (1 : ℕ)) d)
    (s p : ℕ) (q : ℤ)
    (h : ∀ z : Koszul.cycles (J^s) q p,
      cyclesMap J f hf d hhom s p q z ∈ Koszul.boundaries (J^(s+1)) (q+(d : ℤ)) p →
        z ∈ Koszul.boundaries (J^s) q p) :
    Function.Injective (homologyMap J f hf d hhom s p q) := by
  apply LinearMap.ker_eq_bot.mp
  rw [homologyMap,Submodule.ker_mapQ]
  apply le_antisymm
  · rintro z ⟨x,hx,rfl⟩
    change (Koszul.boundaries (J^s) q p).mkQ x=0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact h x hx
  · exact bot_le

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
  ext a
  apply Subtype.ext
  simp [FourPapers.PolynomialTorNaturality.coordinateMap,
    FourPapers.Sublattice.idealPowerMultiplication,coefficientMap,multiplication]

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
    Function.Injective (torMap J f hf s p) ∧
      ∀ q : ℤ, Function.Injective (homologyMap J f hf d hhom s p q) := by
  refine ⟨chosen_generator_actualTor_injective n o J E hE hinit μ hJ hμ hβ
    f hf hf0 hdegree hhom s p,?_⟩
  have hβsource := firstPower_bridge n o J E hE hinit hJ hβ
  have hRees := FourPapers.Sublattice.chosenMinimumGeneratorRees_homology_mul_injective
    n o J E hE hinit μ hJ hμ hβsource f hf hf0 hdegree
  intro q
  apply homologyMap_injective_of_boundary_reflection
  intro z hz
  by_cases hq : 0 ≤ q
  · have hQ : (q.toNat : ℤ)=q := Int.toNat_of_nonneg hq
    change coefficientMap J f hf s p z.val ∈
      Submodule.map (Koszul.differential (J^(s+1)) p)
        (Koszul.piece (J^(s+1)) (q+(d : ℤ)) (p+1)) at hz
    obtain ⟨b,hb,hbz⟩ := hz
    have hzcycle : powerPreviousDifferential J s p z.val=0 := by
      rw [sourcePrevious_eq]
      exact z.property.1
    have hboundary : ∃ b' : PowerIdealCoordinates J (s+1) (p+1),
        powerPreviousDifferential J (s+1) (p+1) b' =
          FourPapers.PolynomialTorNaturality.coordinateMap
            (idealPowerMultiplication J f hf s) p z.val := by
      refine ⟨b,?_⟩
      rw [sourcePrevious_eq,sourceCoefficientMap_eq]
      exact hbz
    obtain ⟨w,hw⟩ := multiplier_coordinate_reflects_boundaries J f hf hRees s p z.val
      hzcycle hboundary
    let P := sublatticePowerQuotientData n o J E hE hinit s
    let H := homogeneousIdealPower n J hJ s
    have hpiece : z.val ∈ actualIdealOrdinaryPiece P q.toNat p := by
      apply (PalomarSublatticeCor53Core.Koszul.piece_nat_eq P H q.toNat p).le
      rw [hQ]
      exact z.property.2
    have hw' : FourPapers.PolynomialCoordinateTor.differential
        (K := k) (V := FiniteVariable.{u} n) (M := P.ideal) p w = z.val := by
      change actualIdealCoordinateDifferential (J^s) p w=z.val
      rw [← PalomarSublatticeCor53Core.Koszul.differential_eq_source]
      exact (sourcePrevious_eq J s (p+1) w).symm.trans hw
    obtain ⟨y,hy⟩ := ordinaryIdeal_boundary_reflects P H q.toNat p ⟨z.val,hpiece⟩ w hw'
    change z.val ∈ Submodule.map (Koszul.differential (J^s) p)
      (Koszul.piece (J^s) q (p+1))
    refine ⟨y.val,?_,?_⟩
    · rw [← hQ]
      exact (PalomarSublatticeCor53Core.Koszul.piece_nat_eq P H q.toNat (p+1)).ge y.property
    · have hv := congrArg (fun a : actualIdealOrdinaryPiece P q.toNat p => a.val) hy
      rw [actualIdealOrdinaryDifferential_val] at hv
      rw [← PalomarSublatticeCor53Core.Koszul.differential_eq_source] at hv
      exact hv
  · have hzero : Koszul.piece (J^s) q p=⊥ :=
      PalomarSublatticeCor53Core.Koszul.piece_negative (J^s) (lt_of_not_ge hq) p
    have hzval : z.val=0 := by
      have hzpiece := z.property.2
      rw [hzero] at hzpiece
      simpa only [Submodule.mem_bot] using hzpiece
    have hz0 : z=0 := Subtype.ext hzval
    rw [hz0]
    exact Submodule.zero_mem _

end PalomarSublatticeCor53
