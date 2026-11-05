module

public import PaperVerification.FermionCreatorAllDegrees
public import PaperVerification.FermionStrictCreators

/-!
# Strict creator tests in the complete original quotient

Both creator colors contain a parameter factor, while the actual strict
relations contain the zeroth odd moments. The positive ordinary moments
suffice for every test vector to be harmonic. All exterior degrees and all
words are separated by the actual exterior-coordinate triangularity.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators TensorProduct
open Exterior

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}

local instance FermionStrictCreatorIndependence_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem strict_relation_pairing_zero
    (f : PolynomialRing K n →ₐ[K] A) (β : Fin n → K)
    (φ : Fin n → PolynomialRing K n)
    (hordinary : ∀ k, moment (fun i ↦ f (φ i))
      (fun i ↦ algebraMap K A (β i) * f (φ i)) k = 0)
    (z : SuperRing K n) (hz : z ∈ strictIdeal β φ)
    (w : ExteriorAlgebra A (OddModule A n))
    (hw : IsHarmonic (Pi.basisFun A (OddIndex n))
      (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun _ ↦ 1) (fun _ ↦ 1) w) :
    coefficientPairing (Pi.basisFun A (OddIndex n)) (superSpecialization f z) w = 0 := by
  have h := strictIdeal_le_harmonic_comap f β φ hordinary hz
  rw [TwoSidedIdeal.mem_comap,mem_harmonicOrthogonalIdeal] at h
  exact h w hw

/-- The full, all-degree creator separation theorem in the literal quotient.
Its only remaining mathematical input is polynomial independence of the
actual diagonal products; the Newton box theorem supplies that input. -/
theorem strict_independent_of_ordinary_diagonal
    (f : PolynomialRing K n →ₐ[K] A) (β : Fin n → K)
    (φ : Fin n → PolynomialRing K n)
    (hordinary : ∀ j, moment (fun i ↦ f (φ i))
      (fun i ↦ algebraMap K A (β i) * f (φ i)) j = 0)
    (D : Finset (OddIndex n) → Type*) [∀ S, Fintype (D S)]
    (p : (S : Finset (OddIndex n)) → D S → PolynomialRing K n)
    (hdiag : ∀ S, LinearIndependent K (fun e ↦ f (p S e) *
      ∏ j ∈ S, prefixCreatorDiagonal (fun i ↦ f (φ i))
        (fun i ↦ algebraMap K A (β i)) (fun i ↦ f (φ i)) (fun i ↦ f (φ i)) j)) :
    LinearIndependent K (fun se : Sigma D ↦
      (strictIdeal β φ).ringCon.mkₐ K
        (p se.1 se.2 ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra se.1)) := by
  classical
  let b := Pi.basisFun A (OddIndex n)
  let q := ((strictIdeal β φ).ringCon.mkₐ K).toLinearMap
  let w (S : Finset (OddIndex n)) : ExteriorAlgebra A (OddModule A n) :=
    prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun i ↦ f (φ i)) (fun i ↦ f (φ i)) S.card ⟨S,rfl⟩
  let v (S : Finset (OddIndex n)) (e : D S) : SuperRing K n :=
    p S e ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra S
  let test (S : Finset (OddIndex n)) : SuperRing K n →ₗ[K] A :=
    (((coefficientPairing b).flip (w S)).restrictScalars K).comp
      (superSpecialization f).toLinearMap
  have htest (S T : Finset (OddIndex n)) (e : D T) :
      test S (v T e) = f (p T e) * b.ExteriorAlgebra.repr (w S) T := by
    change coefficientPairing b (superSpecialization f
      (p T e ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T)) (w S) = _
    rw [superSpecialization_polynomial_wedge,map_smul,LinearMap.smul_apply,
      coefficientPairing_basis_left,smul_eq_mul]
  apply linearIndependent_map_of_triangular_test_maps q D v test creatorWordWeight
  · intro S z hz
    change coefficientPairing b (superSpecialization f z) (w S) = 0
    apply strict_relation_pairing_zero f β φ hordinary z
    · exact (strictIdeal β φ).ringCon.eq.mp hz
    · exact strict_prefixCreatorWedge_isHarmonic b _ _ hordinary S.card ⟨S,rfl⟩
  · intro S T hST hweight e
    rw [htest]
    suffices b.ExteriorAlgebra.repr (w S) T = 0 by rw [this,mul_zero]
    by_cases hcard : T.card = S.card
    · rw [show b.ExteriorAlgebra.repr (w S) T =
          (b.exteriorPower S.card).repr
            (prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
              (fun i ↦ f (φ i)) (fun i ↦ f (φ i)) S.card ⟨S,rfl⟩) ⟨T,hcard⟩ from
          exteriorPower_coordinate_coe b S.card ⟨T,hcard⟩ _]
      apply prefixCreatorWedge_coordinate_zero b _ _ _ _ S.card ⟨T,hcard⟩ ⟨S,rfl⟩
      · exact fun he ↦ hST (congrArg Subtype.val he).symm
      · simpa only [creatorWordWeight,exteriorIndexWeight_eq_sum] using hweight
    · exact exteriorPower_coordinate_coe_of_card_ne b S.card T hcard _
  · intro S
    have heq : (fun e ↦ test S (v S e)) =
        (fun e ↦ f (p S e) * ∏ j ∈ S,
          prefixCreatorDiagonal (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
            (fun i ↦ f (φ i)) (fun i ↦ f (φ i)) j) := by
      funext e
      rw [htest,show b.ExteriorAlgebra.repr (w S) S =
          (b.exteriorPower S.card).repr
            (prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
              (fun i ↦ f (φ i)) (fun i ↦ f (φ i)) S.card ⟨S,rfl⟩) ⟨S,rfl⟩ from
          exteriorPower_coordinate_coe b S.card ⟨S,rfl⟩ _,
        prefixCreatorWedge_coordinate_self,prod_exteriorEnumeration]
    rw [heq]
    exact hdiag S


end PaperVerification.Fermion
