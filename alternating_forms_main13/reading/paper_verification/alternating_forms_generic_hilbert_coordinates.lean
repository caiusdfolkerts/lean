module

public import PaperVerification.AlternatingFormsEvenActualGeneric
public import PaperVerification.AlternatingFormsOddActualGeneric
public import PaperVerification.AlternatingFormsPathDeterminant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi

/-!
# Generic exterior Hilbert certificates in arbitrary vector spaces

Every displayed coordinate system is a basis of the actual second exterior
power.  Replacing the vector space by a linearly equivalent one transports
that basis, the original two generated ideals, and every quotient degree.
The parameter polynomial is unchanged because the coefficient vectors are
unchanged in these corresponding bases.  The dimension-one boundary is
handled for every pair of forms, since its second exterior power is zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators Classical

variable {K M N I : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [Fintype I] [DecidableEq I]

/-- The coefficient points parametrize every actual pair of two-forms
uniquely.  This supplies the explicit equivalence behind the generic
coefficient-space formulation. -/
def orbitPairCoordinateEquiv (b₂ : Module.Basis I K (⋀[K]^2 M)) :
    ((I ⊕ I) → K) ≃ₗ[K] ((⋀[K]^2 M) × (⋀[K]^2 M)) :=
  (LinearEquiv.sumArrowLequivProdArrow I I K K).trans
    (b₂.equivFun.symm.prodCongr b₂.equivFun.symm)

@[simp] theorem orbitPairCoordinateEquiv_apply
    (b₂ : Module.Basis I K (⋀[K]^2 M)) (y : (I ⊕ I) → K) :
    orbitPairCoordinateEquiv b₂ y = orbitFormsFromCoordinates b₂ y := by
  apply Prod.ext <;>
    simp [orbitPairCoordinateEquiv, orbitFormsFromCoordinates,
      Module.Basis.equivFun_symm_apply]

theorem orbitFormsFromCoordinates_bijective (b₂ : Module.Basis I K (⋀[K]^2 M)) :
    Function.Bijective (orbitFormsFromCoordinates b₂) := by
  have he : orbitFormsFromCoordinates b₂ = fun y => orbitPairCoordinateEquiv b₂ y := by
    funext y
    exact (orbitPairCoordinateEquiv_apply b₂ y).symm
  rw [he]
  exact (orbitPairCoordinateEquiv b₂).bijective

theorem orbitFormsFromCoordinates_map (e : M ≃ₗ[K] N)
    (b₂ : Module.Basis I K (⋀[K]^2 M)) (y : (I ⊕ I) → K) :
    orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y =
      (exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).1,
       exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).2) := by
  simp only [orbitFormsFromCoordinates, Module.Basis.map_apply,
    orbitExteriorPowerEquiv_apply, map_sum, map_smul]

theorem orbitFormsFromCoordinates_map_finrank (e : M ≃ₗ[K] N)
    (b₂ : Module.Basis I K (⋀[K]^2 M)) (y : (I ⊕ I) → K) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree
      (orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y).1
      (orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y).2 s) =
    Module.finrank K (ExteriorQuotientDegree
      (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) := by
  rw [orbitFormsFromCoordinates_map]
  exact (exteriorQuotientDegreeMapEquiv e
    (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s).finrank_eq.symm

section CharacteristicZero

variable [CharZero K] [FiniteDimensional K M]

theorem exteriorQuotientDegree_zero_finrank (f g : ⋀[K]^2 M) :
    Module.finrank K (ExteriorQuotientDegree f g 0) = 1 := by
  have h := ((exteriorDegreeRelations f g 0).quotEquivOfEqBot
    (exteriorDegreeRelations_eq_bot f g (by decide))).finrank_eq
  exact h.trans (by rw [exteriorPower.finrank_eq, Nat.choose_zero_right])

/-- The full even-dimensional formula in any vector space of that dimension.
The nonzero polynomial is on all coefficients in an actual exterior basis. -/
theorem even_generic_paperHilbert_in_vector_space (k : ℕ)
    (hdim : Module.finrank K M = 2*k) :
    ∃ b₂ : Module.Basis (EvenOrbitSlot k) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (EvenOrbitSlot k ⊕ EvenOrbitSlot k) K, Q ≠ 0 ∧
        ∀ y : (EvenOrbitSlot k ⊕ EvenOrbitSlot k) → K, eval y Q ≠ 0 →
          (∀ s : ℕ, s ≤ k →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
                StripWalks.paperWalkCount (2*k) s) ∧
          (∀ s : ℕ, k < s →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  let e : (EvenOrbitMode k → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [EvenOrbitMode, Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_fin] using hdim.symm)
  obtain ⟨Q, hQ, h⟩ := even_actual_generic_paperHilbert (K := K) k
  refine ⟨(evenOrbitExteriorBasis k).map (orbitExteriorPowerEquiv e 2), Q, hQ, ?_⟩
  intro y hy
  obtain ⟨hlow, hhigh⟩ := h y hy
  constructor
  · intro s hs
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hlow s hs
  · intro s hs
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hhigh s hs

/-- The full odd-dimensional formula for dimensions at least three in every
vector space, with every natural exterior degree retained. -/
theorem odd_generic_paperHilbert_in_vector_space (t : ℕ)
    (hdim : Module.finrank K M = 2*(t+1)+1) :
    ∃ b₂ : Module.Basis (OddOrbitSlot t) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
        ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 →
          (∀ s : ℕ, Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
              StripWalks.paperWalkCount (2*(t+1)+1) s) ∧
          (∀ s : ℕ, t+2 < s →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  let e : (OddOrbitMode t → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, hdim]
    omega)
  obtain ⟨Q, hQ, h⟩ := odd_actual_generic_paperHilbert (K := K) t
  refine ⟨(oddOrbitExteriorBasis t).map (orbitExteriorPowerEquiv e 2), Q, hQ, ?_⟩
  intro y hy
  obtain ⟨hall, hhigh⟩ := h y hy
  constructor
  · intro s
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hall s
  · intro s hs
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hhigh s hs

theorem one_dimensional_coordinate_paperHilbert
    (f g : ⋀[K]^2 (Fin 1 → K)) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree f g s) = StripWalks.paperWalkCount 1 s := by
  letI : Subsingleton (⋀[K]^2 (Fin 1 → K)) := Module.finrank_zero_iff.mp (by
    rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
    decide)
  have hf : f = oddPathFirstQuadratic (Pi.basisFun K (Fin (2*0+1))) :=
    Subsingleton.elim _ _
  have hg : g = oddPathSecondQuadratic (Pi.basisFun K (Fin (2*0+1))) :=
    Subsingleton.elim _ _
  rw [hf, hg]
  exact oddExteriorQuotientDegree_finrank_eq_paperWalkCount 0 s

/-- The dimension-one case holds for all pairs, including the only pair of
zero quadratic forms, so no odd-dimensional boundary is omitted. -/
theorem one_dimensional_paperHilbert (hdim : Module.finrank K M = 1)
    (f g : ⋀[K]^2 M) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree f g s) = StripWalks.paperWalkCount 1 s := by
  let e : M ≃ₗ[K] (Fin 1 → K) := LinearEquiv.ofFinrankEq _ _ (by
    rw [hdim, Module.finrank_fin_fun])
  exact (exteriorQuotientDegreeMapEquiv e f g s).finrank_eq.trans
    (one_dimensional_coordinate_paperHilbert _ _ s)

/-- The actual quotient walk formula for every dimension in an arbitrary
vector space.  The existential coordinate index is finite and its vectors
are a genuine basis of the complete second exterior power.  Thus the
nonzero polynomial cuts out a principal open in the full space of pairs,
not in a restricted family.  The binomial determinant identity is a
separate combinatorial correspondence. -/
theorem generic_exterior_walk_hilbert (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            (∀ s : ℕ, s ≤ (n+1)/2 →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
                  StripWalks.paperWalkCount n s) ∧
            (∀ s : ℕ, (n+1)/2 < s →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2*k ∨ n = 2*k+1 := ⟨n/2, by omega⟩
  rcases hk with rfl | rfl
  · obtain ⟨b₂, Q, hQ, h⟩ := even_generic_paperHilbert_in_vector_space k hdim
    refine ⟨EvenOrbitSlot k, inferInstance, b₂, Q, hQ, ?_⟩
    intro y hy
    simpa only [show (2*k+1)/2 = k by omega] using h y hy
  · cases k with
    | zero =>
        let b₂ := Module.finBasis K (⋀[K]^2 M)
        refine ⟨Fin (Module.finrank K (⋀[K]^2 M)), inferInstance, b₂, 1,
          one_ne_zero, ?_⟩
        intro y hy
        constructor
        · intro s hs
          exact one_dimensional_paperHilbert hdim _ _ s
        · intro s hs
          rw [one_dimensional_paperHilbert hdim]
          exact paperWalkCount_odd_above_cutoff 0 s (by omega)
    | succ t =>
        obtain ⟨b₂, Q, hQ, h⟩ := odd_generic_paperHilbert_in_vector_space t hdim
        refine ⟨OddOrbitSlot t, inferInstance, b₂, Q, hQ, ?_⟩
        intro y hy
        obtain ⟨hall, hhigh⟩ := h y hy
        refine ⟨fun s _ => hall s, ?_⟩
        intro s hs
        exact hhigh s (by omega)

/-- The full coefficient statement of Theorem 1.1: the constant coefficient
is one, each positive coefficient in the entire printed range is both the
actual strip-walk number and the printed binomial determinant, and every
higher coefficient is zero.  One nonempty principal open controls all
degrees simultaneously in the full space of pairs of exterior forms. -/
theorem paper_theorem_1_1 (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 0) = 1 ∧
            (∀ s : ℕ, 1 ≤ s → s ≤ (n+1)/2 →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
                  StripWalks.paperWalkCount n s ∧
              (Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) : ℤ) =
                  (PathDeterminant.paperMatrix (n+2-2*s) s).det) ∧
            (∀ s : ℕ, (n+1)/2 < s →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨ι, fin, h⟩ := generic_exterior_walk_hilbert (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, ?_, ?_⟩
  · by_contra hn
    apply hQ
    apply MvPolynomial.funext
    intro y
    rw [map_zero]
    by_contra hy
    exact hn ⟨y, hy⟩
  · intro y hy
    obtain ⟨hlow, hhigh⟩ := h y hy
    refine ⟨exteriorQuotientDegree_zero_finrank _ _, ?_, hhigh⟩
    intro s hspos hs
    refine ⟨hlow s hs, ?_⟩
    rw [hlow s hs]
    exact PathDeterminant.paperWalkCount_determinant n s (by omega)

end CharacteristicZero

end PaperVerification.AlternatingForms
