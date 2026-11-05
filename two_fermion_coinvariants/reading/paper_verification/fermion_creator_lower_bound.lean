module

public import PaperVerification.FermionSpecialization
public import PaperVerification.FermionCreatorTriangularity
public import PaperVerification.FermionTriangularIndependence

/-!
# The creator argument in the paper's actual quotient

For each fixed exterior degree, the polynomial independence in the ordinary
quotient is transported to independence in the original two-fermion quotient.
The hypothesis is the precise ordinary diagonal-product independence that the
Newton colon box must supply; this file does not assert that box without proof.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct BigOperators
open Exterior

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}

local instance FermionCreatorLowerBound_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The faithful triangular creator lower bound, stated for classes in the
paper's literal two-sided quotient. The ordinary-independence hypothesis is
left explicit until the Newton-colon theorem is supplied. -/
theorem paired_fixedDegree_independent_of_ordinary_diagonal
    (f : PolynomialRing K n →ₐ[K] A) (β : Fin n → K)
    (φ a c : Fin n → PolynomialRing K n)
    (hordinary : ∀ j, moment (fun i ↦ f (φ i))
      (fun i ↦ algebraMap K A (β i) * f (a i) * f (c i)) j = 0)
    (k : ℕ) (D : Set.powersetCard (OddIndex n) k → Type*) [∀ s, Fintype (D s)]
    (p : (s : Set.powersetCard (OddIndex n) k) → D s → PolynomialRing K n)
    (hdiag : ∀ s, LinearIndependent K (fun e ↦ f (p s e) *
      ∏ i : Fin k, prefixCreatorDiagonal (fun j ↦ f (φ j))
        (fun j ↦ algebraMap K A (β j)) (fun j ↦ f (a j)) (fun j ↦ f (c j))
        (Set.powersetCard.ofFinEmbEquiv.symm s i))) :
    LinearIndependent K (fun se : Sigma D ↦
      (pairedIdeal β φ a c).ringCon.mkₐ K
        (p se.1 se.2 ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra se.1.val)) := by
  let b := Pi.basisFun A (OddIndex n)
  let q := ((pairedIdeal β φ a c).ringCon.mkₐ K).toLinearMap
  let w (s : Set.powersetCard (OddIndex n) k) : ExteriorAlgebra A (OddModule A n) :=
    prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun i ↦ f (a i)) (fun i ↦ f (c i)) k s
  let v (s : Set.powersetCard (OddIndex n) k) (e : D s) : SuperRing K n :=
    p s e ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra s.val
  let test (s : Set.powersetCard (OddIndex n) k) : SuperRing K n →ₗ[K] A :=
    (((coefficientPairing b).flip (w s)).restrictScalars K).comp
      (superSpecialization f).toLinearMap
  have htest (s t : Set.powersetCard (OddIndex n) k) (e : D t) :
      test s (v t e) = f (p t e) * (b.exteriorPower k).repr
        (prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
          (fun i ↦ f (a i)) (fun i ↦ f (c i)) k s) t := by
    change coefficientPairing b (superSpecialization f
      (p t e ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra t.val)) (w s) = _
    rw [superSpecialization_polynomial_wedge, map_smul, LinearMap.smul_apply,
      coefficientPairing_basis_left]
    change f (p t e) • b.ExteriorAlgebra.repr
      ((prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
        (fun i ↦ f (a i)) (fun i ↦ f (c i)) k s : ⋀[A]^k (OddModule A n)) :
          ExteriorAlgebra A (OddModule A n)) t.val = _
    rw [exteriorPower_coordinate_coe, smul_eq_mul]
  apply linearIndependent_map_of_triangular_test_maps q D v test
    (exteriorIndexWeight modeRank)
  · intro s z hz
    change test s z = 0
    change coefficientPairing b (superSpecialization f z) (w s) = 0
    apply paired_relation_pairing_zero f β φ a c hordinary z
    · exact (pairedIdeal β φ a c).ringCon.eq.mp hz
    · exact prefixCreatorWedge_isHarmonic b (fun i ↦ f (φ i))
        (fun i ↦ algebraMap K A (β i)) (fun i ↦ f (a i)) (fun i ↦ f (c i))
        hordinary k s
  · intro s t hst hweight e
    rw [htest, prefixCreatorWedge_coordinate_zero b _ _ _ _ k t s hst.symm hweight,
      mul_zero]
  · intro s
    have heq : (fun e ↦ test s (v s e)) =
        (fun e ↦ f (p s e) * ∏ i : Fin k,
          prefixCreatorDiagonal (fun j ↦ f (φ j)) (fun j ↦ algebraMap K A (β j))
            (fun j ↦ f (a j)) (fun j ↦ f (c j))
              (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
      funext e
      rw [htest, prefixCreatorWedge_coordinate_self]
    rw [heq]
    exact hdiag s

end PaperVerification.Fermion
