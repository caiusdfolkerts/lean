module

public import PaperVerification.FermionLocalHilbert

/-!
# The separated data satisfy the original global theorem

The bridge uses the actual monic univariate polynomials, with their full
degrees and lower coefficients.  It proves the weighted highest-form
conditions rather than assuming them.  The resulting global rank and
exterior formulas agree with the sum over all actual ramified local factors.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section MonicEmbedding

variable {R : Type*} [CommRing R] {n : ℕ}

theorem separated_aeval_X_eq_sum (p : Polynomial R) (i : Fin n) :
    Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p =
      ∑ j∈p.support,MvPolynomial.monomial (Finsupp.single i j) (p.coeff j) := by
  simp only [Polynomial.aeval_def,Polynomial.eval₂_eq_sum,Polynomial.sum,
    MvPolynomial.algebraMap_eq,MvPolynomial.C_mul_X_pow_eq_monomial]

theorem separated_aeval_X_coeff_single (p : Polynomial R) (i : Fin n) (k : ℕ) :
    (Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p).coeff
      (Finsupp.single i k)=p.coeff k := by
  rw [separated_aeval_X_eq_sum,MvPolynomial.coeff_sum]
  by_cases hk : k∈p.support
  · simp only [MvPolynomial.coeff_monomial,(Finsupp.single_injective i).eq_iff,
      Finset.sum_ite_eq',hk,if_true]
  · simp only [MvPolynomial.coeff_monomial,(Finsupp.single_injective i).eq_iff,
      Finset.sum_ite_eq',hk,if_false,Polynomial.notMem_support_iff.mp hk]

/-- A monic univariate polynomial has precisely the highest weighted power
required in the main theorem after substitution into its own variable. -/
theorem highestPower_aeval_X_monic (r : Fin n → ℕ) (hr : ∀ i,0<r i)
    (p : Polynomial R) (hp : p.Monic) (i : Fin n) :
    HasHighestPower r (Polynomial.aeval (MvPolynomial.X i : PolynomialRing R n) p) i p.natDegree := by
  refine ⟨(separated_aeval_X_coeff_single p i p.natDegree).trans hp.coeff_natDegree,?_⟩
  intro e he hne
  have hc := MvPolynomial.mem_support_iff.mp he
  rw [separated_aeval_X_eq_sum,MvPolynomial.coeff_sum] at hc
  obtain ⟨j,hj,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have heq : e=Finsupp.single i j := by
    by_contra h
    apply hc
    rw [MvPolynomial.coeff_monomial,if_neg (Ne.symm h)]
  have hjle : j≤p.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
  have hjne : j≠p.natDegree := by
    intro h
    exact hne (heq.trans (congrArg (Finsupp.single i) h))
  have hjlt : j<p.natDegree := lt_of_le_of_ne hjle hjne
  rw [heq]
  have hw : monomialWeight r (Finsupp.single i j)=(j : ℚ)/(r i : ℚ) := by
    simp [monomialWeight,Finsupp.single_apply,ite_div]
  rw [hw]
  exact div_lt_div_of_pos_right (by exact_mod_cast hjlt) (by exact_mod_cast hr i)

end MonicEmbedding

namespace SeparatedPairedData

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
  (d : SeparatedPairedData F n)

theorem degree_balance (i : Fin n) :
    (d.a i).natDegree+(d.b i).natDegree=(d.phi i).natDegree*d.G.natDegree := by
  have h := congrArg Polynomial.natDegree (d.paired_product i)
  rw [(d.a_monic i).natDegree_mul (d.b_monic i),Polynomial.natDegree_comp] at h
  exact h.trans (Nat.mul_comm _ _)

/-- All assumptions of the general coupled paired theorem, proved directly
from the separated monic data.  The polynomial fields are unchanged. -/
def toPairedData (hn : 0<n) : PairedData (K := F) (n := n) where
  positive_n := hn
  s := d.G.natDegree
  positive_s := d.G_pos
  r i := (d.phi i).natDegree
  u i := (d.a i).natDegree
  v i := (d.b i).natDegree
  positive_r := d.phi_pos
  degree_split := d.degree_balance
  beta := d.beta
  allowed_weights := ⟨isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),d.beta_units⟩
  phi := d.phiPolynomial
  a := d.aPolynomial
  b := d.bPolynomial
  highest_phi i := highestPower_aeval_X_monic _ d.phi_pos _ (d.phi_monic i) i
  highest_a i := highestPower_aeval_X_monic _ d.phi_pos _ (d.a_monic i) i
  highest_b i := highestPower_aeval_X_monic _ d.phi_pos _ (d.b_monic i) i

/-- The closed global rank on the original separated superalgebra. -/
theorem globalSuper_finrank_closed (hn : 0<n) :
    Module.finrank F d.SuperQuotient=
      2^n*(∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n :=
  paired_finrank (d.toPairedData hn)

local instance FermionSeparatedGlobalFormulas_globalExteriorPaperOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

/-- The image of the original ambient total exterior degree, independent
of the separated-data bridge and of any proposed quotient basis. -/
def globalSuperExteriorTotalPart (k : ℕ) : Submodule F d.SuperQuotient :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := F))
    (fun z ↦ z.2.card) k).map d.superMk.toLinearMap

theorem globalSuperExteriorTotalPart_eq_paired (hn : 0<n) (k : ℕ) :
    d.globalSuperExteriorTotalPart k=pairedExteriorPiece (d.toPairedData hn) k := rfl

/-- Each coefficient of the global exterior polynomial is the dimension
of the original exterior-degree image. -/
theorem globalSuper_exterior_hilbert_coefficient (hn : 0<n) (k : ℕ) :
    Module.finrank F (d.globalSuperExteriorTotalPart k)=
      (Polynomial.C ((∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n)*
        (1+Polynomial.X)^n : Polynomial ℕ).coeff k := by
  rw [d.globalSuperExteriorTotalPart_eq_paired hn k]
  exact paired_exterior_hilbert_coefficient (d.toPairedData hn) k

end SeparatedPairedData

namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n)

local instance : Fintype d.O.SupportPoint := Fintype.ofFinite _

/-- Summing the actual local rank formula recovers the original global
rising factorial, for all root multiplicities and ramification orders. -/
theorem localRank_sum_closed (hn : 0<n) :
    (∑ rho : d.O.SupportPoint,
      2^n*(∏ i,d.O.ramificationOrder rho i)*
        ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
          ((d.localClusterFamily rho).s c).ascFactorial
            (Fintype.card (d.LocalFactorIndex rho c)))=
      2^n*(∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n :=
  d.globalSuper_finrank_sum.symm.trans (d.globalSuper_finrank_closed hn)

theorem localMultiplicity_sum_closed (hn : 0<n) :
    (∑ rho : d.O.SupportPoint,
      (∏ i,d.O.ramificationOrder rho i)*
        ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
          ((d.localClusterFamily rho).s c).ascFactorial
            (Fintype.card (d.LocalFactorIndex rho c)))=
      (∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n := by
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0<(2 : ℕ)) n)
  simpa only [Finset.mul_sum,Nat.mul_assoc] using d.localRank_sum_closed hn

/-- The sum of every actual local exterior coefficient is the corresponding
coefficient of the original global exterior quotient. -/
theorem localExteriorFinrank_sum (hn : 0<n) (k : ℕ) :
    (∑ rho : d.O.SupportPoint,Module.finrank F (d.localSuperExteriorTotalPart rho k))=
      Module.finrank F (d.globalSuperExteriorTotalPart k) := by
  rw [d.globalSuper_exterior_hilbert_coefficient hn k]
  simp_rw [d.localSuper_exterior_hilbert_coefficient,Polynomial.coeff_C_mul]
  rw [←Finset.sum_mul,d.localMultiplicity_sum_closed hn]

end SeparatedPairedData
end PaperVerification.Fermion
