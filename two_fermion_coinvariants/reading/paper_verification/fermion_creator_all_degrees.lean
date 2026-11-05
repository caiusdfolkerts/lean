module

public import PaperVerification.FermionCreatorLowerBound

/-!
# Triangular creation across every exterior degree

Different exterior degrees are separated by the actual exterior basis.
Within a degree, the proved triangular minors separate equal-weight and
higher-weight words. Thus a single finite triangular argument applies to
all exterior words simultaneously.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder J] [Fintype J]

theorem exteriorPower_coordinate_coe_of_card_ne
    (b : Module.Basis J R V) (k : ℕ) (U : Finset J) (hU : U.card ≠ k) (w : ⋀[R]^k V) :
    b.ExteriorAlgebra.repr (w : ExteriorAlgebra R V) U = 0 := by
  have h : (b.ExteriorAlgebra.coord U).comp (ExteriorAlgebra.exteriorPower R k V).subtype = 0 := by
    apply (b.exteriorPower k).ext
    intro t
    have ht : t.val ≠ U := by
      intro he
      exact hU (he ▸ t.property)
    simp only [LinearMap.comp_apply,Submodule.subtype_apply,Module.Basis.coord_apply,
      ← ExteriorAlgebra.basis_eq_coe_basis,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne ht.symm,LinearMap.zero_apply]
  simpa only [LinearMap.comp_apply,Submodule.subtype_apply,Module.Basis.coord_apply,LinearMap.zero_apply] using
    LinearMap.congr_fun h w

theorem prod_exteriorEnumeration {M : Type*} [CommMonoid M]
    (k : ℕ) (T : Set.powersetCard J k) (f : J → M) :
    (∏ i : Fin k, f (Set.powersetCard.ofFinEmbEquiv.symm T i)) = ∏ a ∈ T.val, f a := by
  classical
  let e := Set.powersetCard.ofFinEmbEquiv.symm T
  apply Finset.prod_bij (fun i _ ↦ e i)
  · intro i hi
    have hmem : e i ∈ Set.range e := ⟨i,rfl⟩
    rw [exteriorIndex_enum_range] at hmem
    exact hmem
  · intro i hi j hj he
    exact e.injective he
  · intro a ha
    have hmem : a ∈ Set.range e := by rw [exteriorIndex_enum_range]; exact ha
    obtain ⟨i,rfl⟩ := hmem
    exact ⟨i,Finset.mem_univ i,rfl⟩
  · intro i hi
    rfl

/-- The weight of an exterior index is the sum over its actual finite set,
independently of the proof used for its cardinality. -/
theorem exteriorIndexWeight_eq_sum (k : ℕ) (T : Set.powersetCard J k) (rank : J → ℕ) :
    exteriorIndexWeight rank T = ∑ a ∈ T.val, rank a := by
  classical
  let e := Set.powersetCard.ofFinEmbEquiv.symm T
  apply Finset.sum_bij (fun i _ ↦ e i)
  · intro i hi
    have hmem : e i ∈ Set.range e := ⟨i,rfl⟩
    rw [exteriorIndex_enum_range] at hmem
    exact hmem
  · intro i hi j hj he
    exact e.injective he
  · intro a ha
    have hmem : a ∈ Set.range e := by rw [exteriorIndex_enum_range]; exact ha
    obtain ⟨i,rfl⟩ := hmem
    exact ⟨i,Finset.mem_univ i,rfl⟩
  · intro i hi
    rfl

end PaperVerification.Fermion.Exterior

namespace PaperVerification.Fermion

open scoped TensorProduct BigOperators
open Exterior

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}

local instance FermionCreatorAllDegrees_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def creatorWordWeight (S : Finset (OddIndex n)) : ℕ :=
  exteriorIndexWeight modeRank (⟨S,rfl⟩ : Set.powersetCard (OddIndex n) S.card)

/-- The full, all-degree creator separation theorem in the literal quotient.
Its only remaining mathematical input is polynomial independence of the
actual diagonal products; the Newton box theorem supplies that input. -/
theorem paired_independent_of_ordinary_diagonal
    (f : PolynomialRing K n →ₐ[K] A) (β : Fin n → K)
    (φ a c : Fin n → PolynomialRing K n)
    (hordinary : ∀ j, moment (fun i ↦ f (φ i))
      (fun i ↦ algebraMap K A (β i) * f (a i) * f (c i)) j = 0)
    (D : Finset (OddIndex n) → Type*) [∀ S, Fintype (D S)]
    (p : (S : Finset (OddIndex n)) → D S → PolynomialRing K n)
    (hdiag : ∀ S, LinearIndependent K (fun e ↦ f (p S e) *
      ∏ j ∈ S, prefixCreatorDiagonal (fun i ↦ f (φ i))
        (fun i ↦ algebraMap K A (β i)) (fun i ↦ f (a i)) (fun i ↦ f (c i)) j)) :
    LinearIndependent K (fun se : Sigma D ↦
      (pairedIdeal β φ a c).ringCon.mkₐ K
        (p se.1 se.2 ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra se.1)) := by
  classical
  let b := Pi.basisFun A (OddIndex n)
  let q := ((pairedIdeal β φ a c).ringCon.mkₐ K).toLinearMap
  let w (S : Finset (OddIndex n)) : ExteriorAlgebra A (OddModule A n) :=
    prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun i ↦ f (a i)) (fun i ↦ f (c i)) S.card ⟨S,rfl⟩
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
    apply paired_relation_pairing_zero f β φ a c hordinary z
    · exact (pairedIdeal β φ a c).ringCon.eq.mp hz
    · exact prefixCreatorWedge_isHarmonic b _ _ _ _ hordinary S.card ⟨S,rfl⟩
  · intro S T hST hweight e
    rw [htest]
    suffices b.ExteriorAlgebra.repr (w S) T = 0 by rw [this,mul_zero]
    by_cases hcard : T.card = S.card
    · rw [show b.ExteriorAlgebra.repr (w S) T =
          (b.exteriorPower S.card).repr
            (prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
              (fun i ↦ f (a i)) (fun i ↦ f (c i)) S.card ⟨S,rfl⟩) ⟨T,hcard⟩ from
          exteriorPower_coordinate_coe b S.card ⟨T,hcard⟩ _]
      apply prefixCreatorWedge_coordinate_zero b _ _ _ _ S.card ⟨T,hcard⟩ ⟨S,rfl⟩
      · exact fun he ↦ hST (congrArg Subtype.val he).symm
      · simpa only [creatorWordWeight,exteriorIndexWeight_eq_sum] using hweight
    · exact exteriorPower_coordinate_coe_of_card_ne b S.card T hcard _
  · intro S
    have heq : (fun e ↦ test S (v S e)) =
        (fun e ↦ f (p S e) * ∏ j ∈ S,
          prefixCreatorDiagonal (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
            (fun i ↦ f (a i)) (fun i ↦ f (c i)) j) := by
      funext e
      rw [htest,show b.ExteriorAlgebra.repr (w S) S =
          (b.exteriorPower S.card).repr
            (prefixCreatorWedge b (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
              (fun i ↦ f (a i)) (fun i ↦ f (c i)) S.card ⟨S,rfl⟩) ⟨S,rfl⟩ from
          exteriorPower_coordinate_coe b S.card ⟨S,rfl⟩ _,
        prefixCreatorWedge_coordinate_self,prod_exteriorEnumeration]
    rw [heq]
    exact hdiag S

end PaperVerification.Fermion
