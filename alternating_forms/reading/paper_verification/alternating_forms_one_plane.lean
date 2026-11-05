module

public import PaperVerification.AlternatingFormsIntervalPlucker
public import PaperVerification.AlternatingFormsChart
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring.Basic
public import PaperVerification.WeightedInitialGeneralFiber
public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic

/-!
# The one-plane boundary of the odd degeneration theorem

Every alternating form vanishes on a one-dimensional subspace. The generic
one-row minor map is an actual polynomial-ring isomorphism, so its kernel and
every weighted initial ideal are zero. The Rees construction therefore gives
the literal trivial flat family, and the empty set is its quadratic Gröbner basis.

This file reconstructs the lost boundary source; it is not yet a checked theorem
of this run.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.AlternatingForms

open MvPolynomial PaperVerification.WeightedInitialFiber

variable {K : Type*} [Field K] {n : ℕ}

/-- The unique one-entry increasing column with the prescribed entry. -/
def onePlaneIndex (i : Fin n) : PluckerIndex 1 n :=
  ⟨fun _ ↦ i, fun a b hab ↦ by
    have h : a = b := Subsingleton.elim _ _
    exact (not_lt_of_ge h.ge hab).elim⟩

@[simp]
theorem onePlaneIndex_entry (i : Fin n) (a : Fin 1) :
    (onePlaneIndex i).val a = i := rfl

@[simp]
theorem onePlaneIndex_eta (I : PluckerIndex 1 n) :
    onePlaneIndex (I.val 0) = I := by
  apply Subtype.ext
  funext a
  have h : a = 0 := Subsingleton.elim _ _
  rw [h]
  rfl

/-- A single-row determinant is the corresponding independent matrix entry. -/
@[simp]
theorem onePlane_genericMinor (I : PluckerIndex 1 n) :
    genericPluckerMinor (K := K) I = X (0, I.val 0) := by
  simp only [genericPluckerMinor, Matrix.det_fin_one, Matrix.of_apply]

/-- The inverse of the literal generic one-row minor map. -/
def onePlaneGenericInverse :
    MvPolynomial (Fin 1 × Fin n) K →ₐ[K] MvPolynomial (PluckerIndex 1 n) K :=
  aeval fun ij ↦ X (onePlaneIndex ij.2)

theorem onePlaneGenericInverse_comp :
    (onePlaneGenericInverse (K := K) (n := n)).comp genericPluckerMap =
      AlgHom.id K _ := by
  ext I
  simp [genericPluckerMap, onePlaneGenericInverse]

theorem onePlaneGenericMap_comp :
    (genericPluckerMap (K := K) (s := 1) (n := n)).comp onePlaneGenericInverse =
      AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp [genericPluckerMap, onePlaneGenericInverse]

def onePlaneGenericMapEquiv :
    MvPolynomial (PluckerIndex 1 n) K ≃ₐ[K] MvPolynomial (Fin 1 × Fin n) K :=
  AlgEquiv.ofAlgHom genericPluckerMap onePlaneGenericInverse
    onePlaneGenericMap_comp onePlaneGenericInverse_comp

/-- There are no polynomial relations among the one-row minors. -/
theorem onePlane_matrixPluckerIdeal :
    matrixPluckerIdeal (K := K) (s := 1) (n := n) = ⊥ := by
  change RingHom.ker
    (genericPluckerMap (K := K) (s := 1) (n := n)).toRingHom = ⊥
  apply (RingHom.injective_iff_ker_eq_bot _).mp
  exact (onePlaneGenericMapEquiv (K := K) (n := n)).injective

def onePlanePluckerRingEquiv :
    (MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) ≃ₐ[K]
      MvPolynomial (Fin 1 × Fin n) K :=
  (Ideal.quotientEquivAlgOfEq K onePlane_matrixPluckerIdeal).trans
    ((AlgEquiv.quotientBot K _).trans onePlaneGenericMapEquiv)

/-- Literal alternating row evaluation vanishes on any two multiples of
one vector, over every commutative coefficient algebra. -/
theorem onePlane_row_isotropic {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (u : Fin n → R) (a b : R) :
    (∑ ij : StrictPairs n, f ij •
      ((a * u ij.val.1) * (b * u ij.val.2) -
        (a * u ij.val.2) * (b * u ij.val.1))) = 0 := by
  apply Finset.sum_eq_zero
  intro ij _
  have h : (a * u ij.val.1) * (b * u ij.val.2) =
      (a * u ij.val.2) * (b * u ij.val.1) := by ring
  rw [h, sub_self, smul_zero]

theorem onePlane_initialIdeal (w : PluckerIndex 1 n → ℕ) :
    initialIdeal (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w =
      matrixPluckerIdeal := by
  rw [onePlane_matrixPluckerIdeal]
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  have hp' : p = 0 := Ideal.mem_bot.mp hp
  rw [hp']
  simp [initialForm]

/-- The one-plane family, with its original polynomial presentation. -/
theorem onePlane_flat_family (w : PluckerIndex 1 n → ℕ) :
    Module.Flat (Polynomial K)
      (reesAlgebra (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w) ∧
    Nonempty (ZeroFiber (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w ≃ₐ[K]
      MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) ∧
    ∀ c : K, c ≠ 0 →
      Nonempty (ParameterFiber (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w c ≃ₐ[K]
        MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) := by
  refine ⟨inferInstance, ?_, fun c hc ↦ ⟨nonzeroFiberEquiv _ _ c hc⟩⟩
  exact ⟨(initialQuotientEquiv _ _).symm.trans
    (Ideal.quotientEquivAlgOfEq K (onePlane_initialIdeal w))⟩

/-- The empty set is a finite homogeneous-quadratic Gröbner basis of the
actual one-row Plücker kernel. -/
theorem onePlane_quadratic_groebner (m : MonomialOrder (PluckerIndex 1 n)) :
    (∅ : Set (MvPolynomial (PluckerIndex 1 n) K)).Finite ∧
    (∀ p ∈ (∅ : Set (MvPolynomial (PluckerIndex 1 n) K)), p.IsHomogeneous 2) ∧
    m.IsGroebnerBasis ∅ (matrixPluckerIdeal (K := K) (s := 1) (n := n)) := by
  refine ⟨Set.finite_empty, by simp, ?_⟩
  rw [onePlane_matrixPluckerIdeal, MonomialOrder.isGroebnerBasis_iff]
  constructor
  · exact Set.empty_subset _
  · simp [MonomialOrder.leadingTerm_zero]

end PaperVerification.AlternatingForms
