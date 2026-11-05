module

public import PaperVerification.FermionLocalRank
public import PaperVerification.FermionLocalFactorBigraded
public import PaperVerification.FermionPairedBigradedBasis
public import PaperVerification.FermionFiniteGradedHilbert
public import PaperVerification.FermionBigradingTotal

/-!
# Exterior Hilbert coefficients of the actual local super quotient

The source degree pieces are the images of
the original exterior degree spaces after the actual scalar localization.
The already constructed local factorization is proved to carry those pieces
onto the independent natural total grading of its signed tensor target.
Factor bases and their Hilbert polynomials are derived from the original
paired basis theorem, with all factor hypotheses supplied by the root data.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

section Exterior

variable {A ι : Type*} [CommRing A] [Fintype ι] [LinearOrder (ι⊕ι)]

theorem exteriorTotalPart_eq_bigraded_iSup (k : ℕ) :
    exteriorTotalPart (A := A) (ι := ι) k=
      ⨆ g : {g : ℕ×ℕ // totalBidegree g=k},exteriorBigradedPart g.val := by
  have hd : exteriorWordDegree (fun _ : ι⊕ι ↦ (1 : ℕ))=
      fun T ↦ totalBidegree (exteriorWordDegree oddBidegree T) := by
    funext T
    exact (exteriorWordDegree_bidegree_total T).symm
  change basisDegreePart (Pi.basisFun A (ι⊕ι)).ExteriorAlgebra
    (exteriorWordDegree (fun _ : ι⊕ι ↦ (1 : ℕ))) k=_
  rw [hd]
  exact basisDegreePart_comp _ (exteriorWordDegree oddBidegree) totalBidegree k

end Exterior

namespace SeparatedPairedData

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)

local instance FermionLocalHilbert_originalOddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _

/-- The actual localized image of the original exterior-degree-k subspace.
Neither a factor isomorphism nor a proposed basis enters this definition. -/
def localSuperExteriorTotalPart (k : ℕ) : Submodule F (d.LocalSuper rho) :=
  ((exteriorTotalPart (A := d.O.LocalOrdinary rho) (ι := Fin n) k).map
    (d.localSuperExteriorLift rho).toLinearMap).restrictScalars F

theorem localSuperExteriorTotalPart_eq_bigraded_iSup (k : ℕ) :
    d.localSuperExteriorTotalPart rho k=
      ⨆ g : {g : ℕ×ℕ // totalBidegree g=k},
        (d.localSuperBigradedPart rho g.val).restrictScalars F := by
  unfold localSuperExteriorTotalPart
  rw [exteriorTotalPart_eq_bigraded_iSup,Submodule.map_iSup,
    Submodule.restrictScalars_iSup]
  rfl

/-- The actual factorization maps each pre-existing separate-degree piece
onto the independent signed tensor piece. -/
theorem localSuperTensorEquiv_map_bigradedPart (g : ℕ×ℕ) :
    ((d.localSuperBigradedPart rho g).restrictScalars F).map
        (d.localSuperTensorEquiv rho).toLinearMap=
      (d.localClusterFamily rho).tensorBigrading.part g := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (d.localSuperTensorEquiv_bigraded_iff rho g x).mpr hx
  · intro hy
    refine ⟨(d.localSuperTensorEquiv rho).symm y,?_,
      (d.localSuperTensorEquiv rho).apply_symm_apply y⟩
    exact (d.localSuperTensorEquiv_bigraded_iff rho g _).mp
      (by simpa only [AlgEquiv.apply_symm_apply] using hy)

/-- Coarsening the faithful bigraded factorization gives equality with the
natural total degree pieces, rather than transporting a grading. -/
theorem localSuperTensorEquiv_map_exteriorTotalPart (k : ℕ) :
    (d.localSuperExteriorTotalPart rho k).map
        (d.localSuperTensorEquiv rho).toLinearMap=
      (d.localClusterFamily rho).tensor.part k := by
  rw [d.localSuperExteriorTotalPart_eq_bigraded_iSup,Submodule.map_iSup]
  calc
    (⨆ g : {g : ℕ×ℕ // totalBidegree g=k},
      ((d.localSuperBigradedPart rho g.val).restrictScalars F).map
        (d.localSuperTensorEquiv rho).toLinearMap)=
      ⨆ g : {g : ℕ×ℕ // totalBidegree g=k},
        (d.localClusterFamily rho).tensorBigrading.part g.val :=
      iSup_congr fun g ↦ d.localSuperTensorEquiv_map_bigradedPart rho g.val
    _=(d.localClusterFamily rho).tensor.part k :=
      congrFun (d.localClusterFamily rho).tensorBigrading.totalPart_eq k

def localSuperExteriorPieceEquivTensor (k : ℕ) :
    d.localSuperExteriorTotalPart rho k ≃ₗ[F]
      (d.localClusterFamily rho).tensor.part k :=
  (d.localSuperTensorEquiv rho).toLinearEquiv.ofSubmodules
    (d.localSuperExteriorTotalPart rho k) ((d.localClusterFamily rho).tensor.part k)
    (d.localSuperTensorEquiv_map_exteriorTotalPart rho k)

section Factor

variable (c : Fin (Fintype.card (d.O.PointCluster rho)))

local instance FermionLocalHilbert_factorPaperOrder :
    LinearOrder (OddIndex (Fintype.card (d.LocalFactorIndex rho c))) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

set_option maxHeartbeats 1000000 in
/-- The untransported paired basis lies in its original separate-degree
piece. This specialization retains the paper's order on the exterior word. -/
theorem localFactorPairedBasis_bigraded
    (z : PairedPowerIndex (d.localFactorPairedData rho c).r
      (d.localFactorPairedData rho c).u (d.localFactorPairedData rho c).v
      (d.localFactorPairedData rho c).s) :
    pairedArbitraryRingBasis (d.localFactorPairedData rho c) z ∈
      d.localFactorPairedBigradedPart rho c (exteriorWordDegree oddBidegree z.1) := by
  let p : PairedData (K := F) (n := Fintype.card (d.LocalFactorIndex rho c)) :=
    d.localFactorPairedData rho c
  change pairedArbitraryRingBasis p z ∈
    d.localFactorPairedBigradedPart rho c (exteriorWordDegree oddBidegree z.1)
  rw [pairedArbitraryRingBasis_apply,pairedCoupledClasses,
    ← superMonomialBasis_apply (K := F) (z.2.val.val,z.1)]
  change ((pairedIdeal p.beta (fun i ↦ MvPolynomial.X i^p.r i)
      (fun i ↦ MvPolynomial.X i^p.u i) (fun i ↦ MvPolynomial.X i^p.v i)).ringCon.mkₐ F)
      (superMonomialBasis (K := F) (z.2.val.val,z.1))∈
    pairedPowerBigradedPart p.beta p.allowed_weights.2 p.r p.positive_r
      p.s p.positive_s p.u p.v p.degree_split (exteriorWordDegree oddBidegree z.1)
  exact pairedPowerBigraded_superMonomial_mem (F := F)
    (n := Fintype.card (d.LocalFactorIndex rho c)) p.beta p.allowed_weights.2
    p.r p.positive_r p.s p.positive_s p.u p.v p.degree_split (z.2.val.val,z.1)

/-- The original paired basis, pulled back only as a vector-space basis.
Its homogeneity for the independently defined factor grading is proved. -/
def localFactorHomogeneousBasis :
    NGradedAlgebra.FiniteHomogeneousBasis ((d.localClusterFamily rho).factor c) := by
  let p : PairedData (K := F) (n := Fintype.card (d.LocalFactorIndex rho c)) :=
    d.localFactorPairedData rho c
  let e : ((d.localClusterFamily rho).factor c).Carrier ≃ₐ[F]
      PairedQuotient p.beta p.phi p.a p.b :=
    (d.localFactorBigradedEquivPaired rho c).choose
  refine
    { Index := PairedPowerIndex p.r p.u p.v p.s
      finiteIndex := inferInstance
      basis := (pairedArbitraryRingBasis p).map e.symm.toLinearEquiv
      degree := fun (z : PairedPowerIndex p.r p.u p.v p.s) ↦ z.1.card
      homogeneous := ?_ }
  intro z
  let g := exteriorWordDegree oddBidegree z.1
  have hp : pairedArbitraryRingBasis p z∈d.localFactorPairedBigradedPart rho c g :=
    d.localFactorPairedBasis_bigraded rho c z
  have hb : e.symm (pairedArbitraryRingBasis p z)∈
      ((d.localClusterFamily rho).factorBigrading c).part g := by
    apply ((d.localFactorBigradedEquivPaired rho c).choose_spec g _).mp
    change e (e.symm (pairedArbitraryRingBasis p z))∈
      d.localFactorPairedBigradedPart rho c g
    exact (e.apply_symm_apply (pairedArbitraryRingBasis p z)).symm ▸ hp
  have ht := ((d.localClusterFamily rho).factorBigrading c).total g hb
  have hg : totalBidegree g=z.1.card := by
    dsimp only [g]
    rw [exteriorWordDegree_bidegree_total]
    simp only [exteriorWordDegree,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]
  simpa only [Module.Basis.map_apply,AlgEquiv.toLinearEquiv_apply,hg] using ht

theorem localFactorHomogeneousBasis_hilbertPolynomial :
    (d.localFactorHomogeneousBasis rho c).hilbertPolynomial=
      (Polynomial.C
        ((∏ j : Fin (Fintype.card (d.LocalFactorIndex rho c)),
          d.O.ramificationOrder rho (d.localFactorIndex rho c j))*
          ((d.localClusterFamily rho).s c).ascFactorial
            (Fintype.card (d.LocalFactorIndex rho c)))*
        (1+Polynomial.X)^Fintype.card (d.LocalFactorIndex rho c) : Polynomial ℕ) := by
  apply Polynomial.ext
  intro k
  rw [(d.localFactorHomogeneousBasis rho c).hilbertPolynomial_coeff,
    (d.localFactorHomogeneousBasis rho c).finrank_part]
  change Fintype.card (PairedExteriorIndex (d.localFactorPairedData rho c) k)=_
  exact paired_exterior_basis_card (d.localFactorPairedData rho c) k

end Factor

/-- Every coefficient of the printed local exterior Hilbert polynomial is
the dimension of the original localized exterior-degree image. -/
theorem localSuper_exterior_hilbert_coefficient (k : ℕ) :
    Module.finrank F (d.localSuperExteriorTotalPart rho k)=
      (Polynomial.C ((∏ i,d.O.ramificationOrder rho i)*
          ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
            ((d.localClusterFamily rho).s c).ascFactorial
              (Fintype.card (d.LocalFactorIndex rho c)))*
        (1+Polynomial.X)^n : Polynomial ℕ).coeff k := by
  rw [(d.localSuperExteriorPieceEquivTensor rho k).finrank_eq]
  change Module.finrank F ((NGradedAlgebra.tensorFin (d.localClusterFamily rho).factor).part k)=_
  rw [NGradedAlgebra.FiniteHomogeneousBasis.tensorFin_finrank_part
    (d.localClusterFamily rho).factor (d.localFactorHomogeneousBasis rho)]
  simp_rw [d.localFactorHomogeneousBasis_hilbertPolynomial rho]
  congr 1
  rw [Finset.prod_mul_distrib,←map_prod,Finset.prod_mul_distrib,
    d.localFactor_ramification_product rho,Finset.prod_pow_eq_pow_sum,
    d.localFactor_card_sum rho]

end SeparatedPairedData
end PaperVerification.Fermion
