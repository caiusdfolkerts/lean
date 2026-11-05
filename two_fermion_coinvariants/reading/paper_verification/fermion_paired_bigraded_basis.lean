module

public import PaperVerification.FermionSingleClusterBigraded
public import PaperVerification.FermionPairedExteriorPieces

/-!
# The actual paired basis is homogeneous for the original theta/xi grading

The paper basis and the cluster construction
can use different orders on the odd generators.  The argument below maps
actual exterior words into the independently defined quotient pieces; it
never identifies two differently ordered exterior bases by reflexivity.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct BigOperators

namespace PaperVerification.Fermion

namespace SeparatedPairedData

variable {F : Type*} [Field F] {n : ℕ} (d : SeparatedPairedData F n)

local instance FermionPairedBigradedBasis_paperOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

/-- Restriction of scalars retains the original quotient subspaces. -/
def globalSuperFieldBigradedPart (g : ℕ×ℕ) : Submodule F d.SuperQuotient :=
  (d.globalSuperBigradedPart g).restrictScalars F

def globalSuperFieldBigrading :
    GradedAlgebra (R := F) (A := d.SuperQuotient) d.globalSuperFieldBigradedPart := by
  letI := d.globalSuperBigrading
  exact restrictGradedAlgebra (R := F) (S := d.O.Ordinary)
    (C := d.SuperQuotient) d.globalSuperBigradedPart

theorem globalSuper_exteriorWord_bigraded (T : Finset (OddIndex n)) :
    d.superMk (Algebra.TensorProduct.includeRight
      ((Pi.basisFun F (OddIndex n)).ExteriorAlgebra T))∈
      d.globalSuperBigradedPart (exteriorWordDegree oddBidegree T) := by
  letI := d.globalSuperFieldBigrading
  let f : ExteriorAlgebra F (OddModule F n) →ₐ[F] d.SuperQuotient :=
    d.superMk.comp Algebra.TensorProduct.includeRight
  have ht (i : Fin n) : f (exteriorGenerator (Sum.inl i))=d.superMk (theta F n i) := by
    apply congrArg d.superMk
    apply congrArg (Algebra.TensorProduct.includeRight :
      ExteriorAlgebra F (OddModule F n) →ₐ[F] SuperRing F n)
    apply congrArg (ExteriorAlgebra.ι F)
    funext j
    by_cases h : j=Sum.inl i
    · subst j
      simp [exteriorGenerator,theta]
    · simp [exteriorGenerator,theta,Pi.single_apply,h,Ne.symm h]
  have hx (i : Fin n) : f (exteriorGenerator (Sum.inr i))=d.superMk (xi F n i) := by
    apply congrArg d.superMk
    apply congrArg (Algebra.TensorProduct.includeRight :
      ExteriorAlgebra F (OddModule F n) →ₐ[F] SuperRing F n)
    apply congrArg (ExteriorAlgebra.ι F)
    funext j
    by_cases h : j=Sum.inr i
    · subst j
      simp [exteriorGenerator,xi]
    · simp [exteriorGenerator,xi,Pi.single_apply,h,Ne.symm h]
  have hg (i : OddIndex n) : f (exteriorGenerator i)∈
      d.globalSuperFieldBigradedPart (oddBidegree i) := by
    cases i with
    | inl i =>
        -- The target pieces use the cluster order; the source words below
        -- retain the paper's order.  Generator homogeneity needs no
        -- identification between these two ordered exterior bases.
        letI : LinearOrder (Fin n ⊕ Fin n) := finiteIndexLinearOrder _
        rw [ht]
        change d.superMk (theta F n i) ∈
          (exteriorBigradedPart (A := d.O.Ordinary) (ι := Fin n) (1, 0)).map
            d.globalSuperExteriorLift.toLinearMap
        exact Submodule.mem_map.mpr ⟨clusterTheta (A := d.O.Ordinary) i,
          exteriorGenerator_weighted_mem (A := d.O.Ordinary)
            (ι := Fin n ⊕ Fin n) (Γ := ℕ × ℕ) oddBidegree (Sum.inl i),
          d.globalSuperExteriorLift_theta i⟩
    | inr i =>
        letI : LinearOrder (Fin n ⊕ Fin n) := finiteIndexLinearOrder _
        rw [hx]
        change d.superMk (xi F n i) ∈
          (exteriorBigradedPart (A := d.O.Ordinary) (ι := Fin n) (0, 1)).map
            d.globalSuperExteriorLift.toLinearMap
        exact Submodule.mem_map.mpr ⟨clusterXi (A := d.O.Ordinary) i,
          exteriorGenerator_weighted_mem (A := d.O.Ordinary)
            (ι := Fin n ⊕ Fin n) (Γ := ℕ × ℕ) oddBidegree (Sum.inr i),
          d.globalSuperExteriorLift_xi i⟩
  change f ((Pi.basisFun F (OddIndex n)).ExteriorAlgebra T) ∈
    d.globalSuperFieldBigradedPart (exteriorWordDegree oddBidegree T)
  exact exteriorWeighted_map_mem (A := F) (B := d.SuperQuotient)
    (ι := OddIndex n) (Γ := ℕ × ℕ) oddBidegree d.globalSuperFieldBigradedPart f hg
    (exteriorWeightedPart_basis (A := F) oddBidegree T)

/-- Polynomial coefficients have exterior degree zero through the actual
ordinary quotient action. -/
theorem globalSuper_polynomial_exteriorWord_bigraded
    (p : PolynomialRing F n) (T : Finset (OddIndex n)) :
    d.superMk (p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T)∈
      d.globalSuperBigradedPart (exteriorWordDegree oddBidegree T) := by
  have hword := d.globalSuper_exteriorWord_bigraded T
  have he : d.superMk (p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T)=
      (d.O.ordinaryMk p) • d.superMk (Algebra.TensorProduct.includeRight
        ((Pi.basisFun F (OddIndex n)).ExteriorAlgebra T)) := by
    rw [Algebra.smul_def]
    change d.superMk (p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T)=
      d.ordinaryToSuper (d.O.ordinaryMk p)*
        d.superMk (Algebra.TensorProduct.includeRight
          ((Pi.basisFun F (OddIndex n)).ExteriorAlgebra T))
    rw [d.ordinaryToSuper_mk]
    change d.superMk (p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T)=
      d.superMk ((Algebra.TensorProduct.includeLeft :
        PolynomialRing F n →ₐ[F] SuperRing F n) p)*
        d.superMk ((Algebra.TensorProduct.includeRight :
          ExteriorAlgebra F (OddModule F n) →ₐ[F] SuperRing F n)
          ((Pi.basisFun F (OddIndex n)).ExteriorAlgebra T))
    rw [←map_mul]
    congr 1
    simp only [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.tmul_mul_tmul,
      mul_one,one_mul]
  rw [he]
  exact (d.globalSuperBigradedPart _).smul_mem _ hword

theorem globalSuper_superMonomial_bigraded (z : SuperMonomialIndex n) :
    d.superMk (superMonomialBasis (K := F) z)∈
      d.globalSuperBigradedPart (exteriorWordDegree oddBidegree z.2) := by
  rw [superMonomialBasis_apply]
  exact d.globalSuper_polynomial_exteriorWord_bigraded _ _

end SeparatedPairedData

section Power

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
  (beta : Fin n → F)
  (hbeta : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i∈U,beta i))
  (r : Fin n → ℕ) (hr : ∀ i,0<r i) (s : ℕ) (hs : 0<s)
  (u v : Fin n → ℕ) (huv : ∀ i,u i+v i=r i*s)

local instance FermionPairedBigradedBasis_paperOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

theorem pairedPowerBigraded_superMonomial_mem (z : SuperMonomialIndex n) :
    ((pairedIdeal beta (fun i ↦ MvPolynomial.X i^r i)
      (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i)).ringCon.mkₐ F)
        (superMonomialBasis (K := F) z)∈
      pairedPowerBigradedPart beta hbeta r hr s hs u v huv
        (exteriorWordDegree oddBidegree z.2) := by
  let d := powerSeparatedData beta hbeta r hr s hs u v huv
  change _ ∈ ((d.globalSuperBigradedPart
    (exteriorWordDegree oddBidegree z.2)).restrictScalars F).map
      (pairedPowerOriginalEquiv beta hbeta r hr s hs u v huv).toLinearMap
  refine ⟨d.superMk (superMonomialBasis (K := F) z),
    d.globalSuper_superMonomial_bigraded z,?_⟩
  exact pairedPowerOriginalEquiv_mk beta hbeta r hr s hs u v huv _

end Power
end PaperVerification.Fermion
