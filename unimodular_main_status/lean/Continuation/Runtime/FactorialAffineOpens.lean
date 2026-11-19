module

public import Mathlib.AlgebraicGeometry.StructureSheaf
import all Mathlib.AlgebraicGeometry.StructureSheaf

public import Continuation.Runtime.NormalAffineComplements
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Affine opens of a noetherian factorial affine scheme are principal

The complement has finitely many codimension-one components by the Hartogs
argument. Each corresponding prime ideal is principal in a UFD. The product
of their generators cuts out exactly that complement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R]

/-- Normality of every actual local ring of the spectrum of a UFD. -/
theorem factorial_spec_stalk_isIntegrallyClosed
    (x : Spec (CommRingCat.of R)) :
    IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk x) := by
  letI : IsIntegrallyClosed R := UniqueFactorizationMonoid.instIsIntegrallyClosed
  letI : x.asIdeal.IsPrime := x.isPrime
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  letI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  exact isIntegrallyClosed_of_isLocalization
    ((Spec (CommRingCat.of R)).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors

/-- Every nonempty affine open in the spectrum of a noetherian UFD is the
principal open of an actual nonzero ring element. -/
theorem exists_nonzero_basicOpen_eq_of_factorial
    (U : (Spec (CommRingCat.of R)).Opens) (hU : IsAffineOpen U) [Nonempty U] :
    ∃ f : R, f ≠ 0 ∧ U = PrimeSpectrum.basicOpen f := by
  classical
  let X := Spec (CommRingCat.of R)
  let Q := {x : X // Order.coheight x = 1 ∧ x ∉ U}
  letI : Finite Q := (finite_codimensionOne_complement U).to_subtype
  letI : Fintype Q := Fintype.ofFinite Q
  have hnormal : ∀ (V : X.Opens), IsAffineOpen V → Nonempty V →
      IsIntegrallyClosed Γ(X,V) := by
    intro V hV hne
    letI := hne
    exact affineOpen_isIntegrallyClosed_of_stalks
      (factorial_spec_stalk_isIntegrallyClosed R) V hV
  have hcompl := affineOpen_complement_eq_codimensionOne_closures hnormal U hU
  have hprincipal (q : Q) : ∃ f : R, q.val.asIdeal = Ideal.span {f} := by
    letI : q.val.asIdeal.IsPrime := q.val.isPrime
    have hheight : q.val.asIdeal.height = 1 :=
      (idealHeight_eq_coheight (CommRingCat.of R) q.val).trans q.property.1
    exact (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight).principal
  choose f hf using hprincipal
  have hfzero (q : Q) : f q ≠ 0 := by
    intro hzero
    have hheight : q.val.asIdeal.height = 1 :=
      (idealHeight_eq_coheight (CommRingCat.of R) q.val).trans q.property.1
    apply q.val.asIdeal.ne_bot_of_height_eq_one hheight
    simpa only [hzero, Ideal.span_singleton_zero] using hf q
  refine ⟨∏ q, f q, Finset.prod_ne_zero_iff.mpr (fun q _ => hfzero q), ?_⟩
  apply Opens.ext
  apply compl_injective
  rw [hcompl]
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff]
  change (∃ q : Q, x ∈ closure {q.val}) ↔ ¬ (∏ q, f q) ∉ x.asIdeal
  letI : x.asIdeal.IsPrime := x.isPrime
  simp only [Set.mem_iUnion, Set.mem_compl_iff, PrimeSpectrum.mem_basicOpen, not_not,
    PrimeSpectrum.closure_singleton, hf, PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
    Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and]
  apply exists_congr
  intro q
  rw [show closure ({q.val} : Set X) = PrimeSpectrum.zeroLocus q.val.asIdeal from PrimeSpectrum.closure_singleton q.val]
  change q.val.asIdeal ≤ x.asIdeal ↔ f q ∈ x.asIdeal
  rw [hf]
  simp only [Ideal.span_le, Set.singleton_subset_iff]
  rfl

end PaperVerification.ToricSchemes
