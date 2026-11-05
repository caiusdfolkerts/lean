module

public import Mathlib.AlgebraicGeometry.StructureSheaf
import all Mathlib.AlgebraicGeometry.StructureSheaf

public import Continuation.Runtime.NormalAffineComplements
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Affine opens containing a principal torus open

In a normal noetherian affine domain, suppose the distinguished open is
obtained by inverting a finite product of prime elements. Every affine
open containing it is obtained by inverting a subproduct. The proof uses
Hartogs at the actual height-one points and needs no factorization of
arbitrary elements of the ring.

Applied to polynomial coordinates over a Laurent ring, this is the
reverse direction of the smooth-cone face-localization theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators Classical

namespace PaperVerification.ToricSchemes

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]

/-- The actual stalks of a normal affine domain are integrally closed. -/
theorem normal_spec_stalk_isIntegrallyClosed (x : Spec (CommRingCat.of R)) :
    IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk x) := by
  letI : x.asIdeal.IsPrime := x.isPrime
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  letI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  exact isIntegrallyClosed_of_isLocalization
    ((Spec (CommRingCat.of R)).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors

/-- No further affine open containing the distinguished principal open
can occur: it is exactly a principal open of some of the same primes. -/
theorem affineOpen_eq_basicOpen_subproduct {ι : Type*} [Fintype ι]
    (p : ι → R) (hp : ∀ i, Prime (p i))
    (U : (Spec (CommRingCat.of R)).Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hT : PrimeSpectrum.basicOpen (∏ i, p i) ≤ U) :
    ∃ J : Finset ι, U = PrimeSpectrum.basicOpen (∏ i ∈ J, p i) := by
  let X := Spec (CommRingCat.of R)
  let q : ι → X := fun i =>
    ⟨Ideal.span {p i}, (Ideal.span_singleton_prime (hp i).ne_zero).mpr (hp i)⟩
  let J : Finset ι := Finset.univ.filter (fun i => q i ∉ U)
  let g : R := ∏ i ∈ J, p i
  let W : X.Opens := PrimeSpectrum.basicOpen g
  have hW : IsAffineOpen W :=
    IsAffine.of_isIso (basicOpenIsoSpecAway (R := CommRingCat.of R) g).hom
  have hWmem (x : X) : x ∈ W ↔ ∀ i ∈ J, p i ∉ x.asIdeal := by
    change (∏ i ∈ J, p i) ∉ x.asIdeal ↔ _
    simp only [Ideal.IsPrime.prod_mem_iff,
      not_exists, not_and]
  have hUleW : U ≤ W := by
    intro x hx
    apply (hWmem x).mpr
    intro i hi hpi
    have hqx : q i ⤳ x := by
      apply specializes_iff_mem_closure.mpr
      rw [PrimeSpectrum.closure_singleton]
      change Ideal.span {p i} ≤ x.asIdeal
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpi)
    exact (Finset.mem_filter.mp hi).2 (hqx.mem_open U.isOpen hx)
  letI : Nonempty W := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨⟨x.val, hUleW x.property⟩⟩
  letI : IsIntegrallyClosed Γ(X,W) :=
    affineOpen_isIntegrallyClosed_of_stalks
      (normal_spec_stalk_isIntegrallyClosed R) W hW
  have hcodim : ∀ x ∈ W, Order.coheight x = 1 → x ∈ U := by
    intro x hx hh
    by_contra hxU
    have hxT : x ∉ PrimeSpectrum.basicOpen (∏ i, p i) := fun h => hxU (hT h)
    have hprod : (∏ i, p i) ∈ x.asIdeal := by
      change ¬ (∏ i, p i) ∉ x.asIdeal at hxT
      exact Classical.not_not.mp hxT
    obtain ⟨i, hi, hpi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
    have heq : x.asIdeal = Ideal.span {p i} :=
      Ideal.eq_span_singleton_of_height_eq_one
        ((idealHeight_eq_coheight (CommRingCat.of R) x).trans hh) hpi (hp i)
    have hxq : x = q i := PrimeSpectrum.ext heq
    have hiJ : i ∈ J := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun h => hxU (hxq.symm ▸ h)⟩
    exact (hWmem x).mp hx i hiJ hpi
  exact ⟨J, normal_affineOpen_eq_of_contains_codimensionOne hW hU hUleW hcodim⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineOpen_eq_basicOpen_subproduct
