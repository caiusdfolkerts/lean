module

public import Recovery.Unimodular.FlagKoszul.HomogeneousWords
public import Recovery.Unimodular.FlagKoszul.CoefficientModuleBar
public import Recovery.Unimodular.KoszulSupport.PaperVerification.WeightedBarDegrees

/-!
# Total-degree preservation of the actual coefficient bar differential

The front term is genuine module multiplication. The internal terms are the
actual positive-basis multiplication coefficients from the augmented algebra.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul.CoefficientDegree

open HomogeneousWords

variable {K A I J M : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

/-- Extension of scalar word coefficients to a fixed module coefficient. -/
def scalarLift (m : M) : (List I →₀ K) →ₗ[K] (List I →₀ M) :=
  Finsupp.linearCombination K (fun L => Finsupp.single L m)

@[simp] theorem scalarLift_single (m : M) (L : List I) (c : K) :
    scalarLift m (Finsupp.single L c) = c • Finsupp.single L m :=
  Finsupp.linearCombination_single _ _ _

@[simp] theorem scalarLift_apply (m : M) (z : List I →₀ K) (L : List I) :
    scalarLift m z L = z L • m := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply, zero_smul]
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw, add_smul]
  | single T c =>
    by_cases h : T = L <;> simp [scalarLift_single, Finsupp.single_apply, h]

theorem evaluate_lift (m : M) (z : List I →₀ K) :
    CoefficientModuleBar.evaluate (PaperVerification.NoncommutativeBar.lift (A := A) z) m =
      scalarLift m z := by
  ext L
  simp only [CoefficientModuleBar.evaluate_apply,
    PaperVerification.NoncommutativeBar.lift_apply, scalarLift_apply,
    IsScalarTower.algebraMap_smul]

variable (B : Module.Basis (Option I) K A)

/-- Exact formula for the coefficient differential on a word generator. -/
theorem differential_cons (i : I) (L : List I) (m : M) :
    CoefficientModuleBar.differential B (Finsupp.single (i :: L) m) =
      Finsupp.single L (B (some i) • m) -
        scalarLift m (PaperVerification.ReducedBarBasis.differentialBasis B (i :: L)) := by
  rw [CoefficientModuleBar.differential_single]
  change CoefficientModuleBar.evaluate
    (PaperVerification.NoncommutativeBar.front B (Finsupp.single (i :: L) 1) -
      PaperVerification.NoncommutativeBar.internal B (Finsupp.single (i :: L) 1)) m = _
  rw [PaperVerification.NoncommutativeBar.front_single,
    PaperVerification.NoncommutativeBar.internal_single, one_smul, one_smul,
    map_sub, LinearMap.sub_apply]
  change CoefficientModuleBar.evaluate (Finsupp.single L (B (some i))) m - _ = _
  rw [CoefficientModuleBar.evaluate_single, evaluate_lift]

theorem differential_nil (m : M) :
    CoefficientModuleBar.differential B (Finsupp.single [] m) = 0 := by
  rw [CoefficientModuleBar.differential_single]
  change CoefficientModuleBar.evaluate
    (PaperVerification.NoncommutativeBar.front B (Finsupp.single [] 1) -
      PaperVerification.NoncommutativeBar.internal B (Finsupp.single [] 1)) m = 0
  simp only [PaperVerification.NoncommutativeBar.front_single,
    PaperVerification.NoncommutativeBar.frontBasis,
    PaperVerification.NoncommutativeBar.internal_single,
    PaperVerification.ReducedBarBasis.differentialBasis, map_zero, smul_zero,
    sub_zero, LinearMap.zero_apply]

variable (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)

theorem differential_zero_length {N : ℕ} {z : List I →₀ M}
    (hz : z ∈ piece D δ d 0 N) : CoefficientModuleBar.differential B z = 0 := by
  apply piece_induction D δ d (fun z => CoefficientModuleBar.differential B z = 0)
    (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero]) ?_ z hz
  intro L j c hL hj
  have hnil : L = [] := List.length_eq_zero_iff.mp hL
  rw [hnil, LinearMap.map_smul_of_tower, differential_nil, smul_zero]

 theorem scalarLift_basis_mem_piece (j : J) {r N : ℕ} (z : List I →₀ K)
    (hz : ∀ L, z L ≠ 0 → L.length = r ∧ wordDegree δ L = N) :
    scalarLift (D j) z ∈ piece D δ d r (d j + N) := by
  classical
  rw [scalarLift, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro L hL
  have h := hz L (Finsupp.mem_support_iff.mp hL)
  exact (piece D δ d r (d j + N)).smul_mem _
    (single_basis_mem_piece D δ d L j h.1 (by rw [h.2]))

/-- Homogeneity follows from the genuine coefficient action and genuine
positive-basis multiplication; no differential preservation is assumed. -/
theorem differential_mem_piece
    (hproduct : ∀ a b c,
      PaperVerification.AugmentedAlgebraBasis.productCoefficients B a b c ≠ 0 →
      δ c = δ a + δ b)
    (haction : ∀ i j k, D.repr (B (some i) • D j) k ≠ 0 → d k = δ i + d j)
    {r N : ℕ} {z : List I →₀ M} (hz : z ∈ piece D δ d (r + 1) N) :
    CoefficientModuleBar.differential B z ∈ piece D δ d r N := by
  apply linearMap_mem_piece_of_basis D D δ d d
    ((CoefficientModuleBar.differential B).restrictScalars K) ?_ hz
  intro L j hL hj
  cases L with
  | nil => simp only [List.length_nil] at hL; omega
  | cons i L =>
    change CoefficientModuleBar.differential B (Finsupp.single (i :: L) (D j)) ∈ _
    rw [differential_cons]
    apply Submodule.sub_mem
    · intro T k hk
      classical
      by_cases hTL : T = L
      · subst T
        have hact : D.repr (B (some i) • D j) k ≠ 0 := by simpa using hk
        have hd := haction i j k hact
        simp only [List.length_cons] at hL
        simp only [wordDegree_cons] at hj
        exact ⟨by omega, by omega⟩
      · exact (hk (by simp [Finsupp.single_apply, hTL, Ne.symm hTL])).elim
    · have hmem := scalarLift_basis_mem_piece D δ d j
        (PaperVerification.ReducedBarBasis.differentialBasis B (i :: L))
        (r := r) (N := wordDegree δ (i :: L)) (by
          intro T hT
          have hlen := PaperVerification.NoncommutativeBar.reducedDifferentialBasis_mem_lengthPiece B (i :: L)
          have hdeg := PaperVerification.WeightedBar.differentialBasis_mem_degreePiece B δ hproduct (i :: L)
          have hT' := Finsupp.mem_support_iff.mpr hT
          have hl := hlen hT'
          have hd := hdeg hT'
          exact ⟨by simpa only [Set.mem_setOf_eq, hL, Nat.add_sub_cancel] using hl, hd⟩)
      simpa only [hj] using hmem

#print axioms differential_cons
#print axioms differential_mem_piece

end Unimodular.FlagKoszul.CoefficientDegree
