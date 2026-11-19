module

public import PaperVerification.AlternatingFormsOrbitCoefficientTransport
public import PaperVerification.AlternatingFormsEvenPaperWalks

/-!
# The generic Hilbert function of the actual even exterior quotient

The matching coordinates are a genuine reindexing of the standard basis.
Their literal wedge sums have exactly the block matrices used in the orbit
Jacobian calculation.  One nonzero parameter polynomial controls every
matching quotient degree; dominance and actual exterior transport then give
one principal open in the full space of pairs of exterior quadratic forms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix
open scoped BigOperators Classical

variable {K : Type*} [Field K]

def evenOrbitModeEquiv (k : ℕ) : EvenOrbitMode k ≃ (Fin k ⊕ Fin k) :=
  (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin k))).trans (Equiv.boolProdEquivSum (Fin k))

def evenOrbitMatchingBasis (k : ℕ) :
    Module.Basis (Fin k ⊕ Fin k) K (EvenOrbitMode k → K) :=
  (Pi.basisFun K (EvenOrbitMode k)).reindex (evenOrbitModeEquiv k)

@[simp] theorem evenOrbitMatchingBasis_inl (k : ℕ) (i : Fin k) :
    evenOrbitMatchingBasis (K := K) k (Sum.inl i) =
      Pi.basisFun K (EvenOrbitMode k) (0, i) := by
  rw [evenOrbitMatchingBasis, Module.Basis.reindex_apply]
  rfl

@[simp] theorem evenOrbitMatchingBasis_inr (k : ℕ) (i : Fin k) :
    evenOrbitMatchingBasis (K := K) k (Sum.inr i) =
      Pi.basisFun K (EvenOrbitMode k) (1, i) := by
  rw [evenOrbitMatchingBasis, Module.Basis.reindex_apply]
  rfl

theorem evenOrbitMatchingForm_matrix (k : ℕ) (a : Fin k → K) :
    orbitExteriorCoefficientMatrix
      (EvenSingletons.matchingForm (evenOrbitMatchingBasis (K := K) k) a) =
      evenOrbitSecond a := by
  ext u v
  rcases u with ⟨b, i⟩
  rcases v with ⟨c, j⟩
  fin_cases b <;> fin_cases c <;> by_cases hij : i = j <;>
    simp [EvenSingletons.matchingForm, orbitExteriorCoefficientMatrix,
      evenOrbitMatchingBasis_inl, evenOrbitMatchingBasis_inr,
      exteriorPair, orbitExteriorCoefficient_word, Pi.basisFun_apply,
      Pi.single_apply, evenOrbitSecond, evenOrbitJ, Matrix.blockDiagonal_apply,
      Finset.sum_neg_distrib, smul_eq_mul, hij, eq_comm]

/-- The polynomial congruence coordinates are coordinates of actual exterior
images of the two matching forms with the indicated coefficient vectors. -/
theorem evenOrbit_forms_eval (k : ℕ) (x : EvenOrbitParameter k → K) :
    orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k)
      (fun i => eval x (orbitPairPolynomialCoordinates (evenOrbitPolynomials (K := K) k) i)) =
      (exteriorPower.map 2
          (Matrix.toLin' (Matrix.of fun i j => x (Sum.inl (i, j))).transpose)
          (EvenSingletons.matchingForm (evenOrbitMatchingBasis (K := K) k)
            (fun i => x (Sum.inr (false, i)))),
       exteriorPower.map 2
          (Matrix.toLin' (Matrix.of fun i j => x (Sum.inl (i, j))).transpose)
          (EvenSingletons.matchingForm (evenOrbitMatchingBasis (K := K) k)
            (fun i => x (Sum.inr (true, i))))) := by
  change orbitFormsFromCoordinates (orbitSlotBasis (evenOrbitPairSlots k))
    (orbitPairCoefficientPoint (fun z => eval x (evenOrbitPolynomials (K := K) k z))) = _
  rw [orbitFormsFromCoordinates_pair_slots]
  apply Prod.ext
  · simp only [evenOrbitPolynomials_eval]
    rw [← evenOrbitMatchingForm_matrix]
    exact orbitSlotCoordinates_congruence (evenOrbitPairSlots k) _ _
  · simp only [evenOrbitPolynomials_eval]
    rw [← evenOrbitMatchingForm_matrix]
    exact orbitSlotCoordinates_congruence (evenOrbitPairSlots k) _ _

section CharacteristicZero

variable [CharZero K]

def evenOrbitMatchingOpen (k : ℕ) : MvPolynomial (EvenOrbitParameter k) K :=
  evenOrbitDeterminant k * rename Sum.inr
    (EvenSingletons.matchingGenericPolynomial (K := K) (ι := Fin k))

theorem evenOrbitMatchingOpen_ne_zero (k : ℕ) :
    evenOrbitMatchingOpen (K := K) k ≠ 0 := by
  apply mul_ne_zero (evenOrbitDeterminant_ne_zero k)
  rw [ne_eq, rename_eq_zero_iff_of_injective _ Sum.inr_injective]
  exact EvenSingletons.matchingGenericPolynomial_ne_zero

theorem evenOrbitMatchingOpen_eval (k : ℕ) (x : EvenOrbitParameter k → K) :
    eval x (evenOrbitMatchingOpen (K := K) k) =
      (Matrix.of fun i j => x (Sum.inl (i, j))).det *
        BooleanQuotient.pairParameterEvaluation
          (fun i => x (Sum.inr (false, i))) (fun i => x (Sum.inr (true, i)))
          (EvenSingletons.matchingGenericPolynomial (K := K) (ι := Fin k)) := by
  rw [evenOrbitMatchingOpen, map_mul, evenOrbitDeterminant_eval, eval_rename]
  congr 1
  have he : (fun z : Bool × Fin k => x (Sum.inr z)) =
      (fun z => if z.1 then x (Sum.inr (true, z.2)) else x (Sum.inr (false, z.2))) := by
    funext z
    rcases z with ⟨b, i⟩
    cases b <;> rfl
  change eval (fun z : Bool × Fin k => x (Sum.inr z)) _ = _
  rw [he]
  rfl

set_option maxHeartbeats 800000 in
theorem evenOrbit_parameter_hilbert (k : ℕ) (x : EvenOrbitParameter k → K)
    (hx : eval x (evenOrbitMatchingOpen (K := K) k) ≠ 0) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree
      (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k)
        (fun i => eval x (orbitPairPolynomialCoordinates (evenOrbitPolynomials (K := K) k) i))).1
      (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k)
        (fun i => eval x (orbitPairPolynomialCoordinates (evenOrbitPolynomials (K := K) k) i))).2 s) =
      EvenSingletons.blockWalkCount (Fin k) s := by
  rw [evenOrbitMatchingOpen_eval] at hx
  obtain ⟨hX, hmatching⟩ := mul_ne_zero_iff.mp hx
  rw [evenOrbit_forms_eval]
  let X : Matrix (EvenOrbitMode k) (EvenOrbitMode k) K :=
    Matrix.of fun i j => x (Sum.inl (i, j))
  let f : ⋀[K]^2 (EvenOrbitMode k → K) :=
    EvenSingletons.matchingForm (evenOrbitMatchingBasis (K := K) k)
      (fun i => x (Sum.inr (false, i)))
  let g : ⋀[K]^2 (EvenOrbitMode k → K) :=
    EvenSingletons.matchingForm (evenOrbitMatchingBasis (K := K) k)
      (fun i => x (Sum.inr (true, i)))
  have ht := (exteriorQuotientDegreeMapEquiv (orbitTransposeEquiv X hX) f g s).finrank_eq
  rw [orbitTransposeEquiv_toLinearMap] at ht
  exact ht.symm.trans (EvenSingletons.matchingGenericPolynomial_spec
    (evenOrbitMatchingBasis (K := K) k) _ _ hmatching s)

/-- Every degree of the actual even-dimensional exterior quotient has the
specified finite walk count on a single nonempty principal open in the full
coefficient space.  There are no generic-rank or normal-form hypotheses. -/
theorem even_actual_generic_hilbert (k : ℕ) :
    ∃ Q : MvPolynomial (EvenOrbitSlot k ⊕ EvenOrbitSlot k) K, Q ≠ 0 ∧
      ∀ y : (EvenOrbitSlot k ⊕ EvenOrbitSlot k) → K, eval y Q ≠ 0 → ∀ s : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) y).1
          (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) y).2 s) =
          EvenSingletons.blockWalkCount (Fin k) s := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  let p := orbitPairPolynomialCoordinates (evenOrbitPolynomials (K := K) k)
  let G := evenOrbitMatchingOpen (K := K) k
  have hG : G ≠ 0 := evenOrbitMatchingOpen_ne_zero k
  obtain ⟨x₀, hx₀⟩ : ∃ x : EvenOrbitParameter k → K, eval x G ≠ 0 := by
    by_contra hn
    apply hG
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    by_contra hx
    exact hn ⟨x, hx⟩
  let base : (EvenOrbitSlot k ⊕ EvenOrbitSlot k) → K := fun i => eval x₀ (p i)
  have hJ := jacobian_surjective_reindex (evenOrbitPolynomials (K := K) k)
    (evenOrbitBasePoint (fun i => (i.val : K)))
    (Equiv.boolProdEquivSum (EvenOrbitSlot k)).symm
    (evenOrbit_jacobian_surjective _ (evenOrbit_natPoint_injective k))
  have hb (s : ℕ) :
      Module.finrank K (ExteriorQuotientDegree
        (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) base).1
        (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) base).2 s) =
        EvenSingletons.blockWalkCount (Fin k) s :=
    evenOrbit_parameter_hilbert k x₀ hx₀ s
  obtain ⟨Q, hbase, hQ⟩ := exteriorHilbert_principal_certificate_of_dominant
    (evenOrbitExteriorBasis (K := K) k) p (evenOrbitBasePoint (fun i => (i.val : K)))
    hJ G hG base (fun x hx s =>
      (evenOrbit_parameter_hilbert k x hx s).trans (hb s).symm)
  refine ⟨Q, ?_, fun y hy s => (hQ y hy s).trans (hb s)⟩
  intro hz
  exact hbase (by rw [hz, map_zero])

/-- The walk formula and the full vanishing range, simultaneously on one
principal open, for every even dimension (including dimension zero). -/
theorem even_actual_generic_paperHilbert (k : ℕ) :
    ∃ Q : MvPolynomial (EvenOrbitSlot k ⊕ EvenOrbitSlot k) K, Q ≠ 0 ∧
      ∀ y : (EvenOrbitSlot k ⊕ EvenOrbitSlot k) → K, eval y Q ≠ 0 →
        (∀ s : ℕ, s ≤ k →
          Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) y).1
            (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) y).2 s) =
              StripWalks.paperWalkCount (2*k) s) ∧
        (∀ s : ℕ, k < s →
          Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) y).1
            (orbitFormsFromCoordinates (evenOrbitExteriorBasis (K := K) k) y).2 s) = 0) := by
  obtain ⟨Q, hQ, h⟩ := even_actual_generic_hilbert (K := K) k
  refine ⟨Q, hQ, ?_⟩
  intro y hy
  constructor
  · intro s hs
    rw [h y hy s, EvenSingletons.blockWalkCount_eq_paperWalkCount k s hs]
  · intro s hs
    rw [h y hy s, EvenSingletons.blockWalkCount_eq_zero (by simpa using hs)]

end CharacteristicZero

end PaperVerification.AlternatingForms
