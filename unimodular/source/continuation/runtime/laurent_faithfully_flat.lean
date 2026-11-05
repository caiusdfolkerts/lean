module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Faithfully flat Laurent principal opens

A Laurent polynomial with a unit coefficient stays nonzero after reduction
modulo every prime of its coefficient ring.  Its principal open therefore
meets every fibre of the Laurent extension.  Since a monoid algebra is free
and localization is flat, this principal open is faithfully flat over the
coefficient ring.

The argument uses prime ideals and coefficient reduction, so it also applies
over finite fields.  No supply of rational points is assumed.
-/

@[expose] public noncomputable section

universe u v

namespace PaperVerification.ToricSchemes

variable {R : Type u} [CommRing R]
    {M : Type v} [AddCommMonoid M] [UniqueSums M]

/-- A principal open in a Laurent extension whose defining polynomial has
one unit coefficient surjects onto the spectrum of its coefficient ring. -/
theorem laurentAway_comap_surjective_of_isUnit_coeff
    (f : AddMonoidAlgebra R M) (m : M) (hm : IsUnit (f.coeff m)) :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
  intro p
  letI : p.asIdeal.IsPrime := p.isPrime
  let A := AddMonoidAlgebra R M
  let B := Localization.Away f
  let ρ : A →+* AddMonoidAlgebra (R ⧸ p.asIdeal) M :=
    AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk p.asIdeal)
  let q : Ideal A := RingHom.ker ρ
  have hq : q.IsPrime := RingHom.ker_isPrime ρ
  letI : q.IsPrime := hq
  have hqf : f ∉ q := by
    intro hf
    change ρ f = 0 at hf
    have hc : Ideal.Quotient.mk p.asIdeal (f.coeff m) = 0 := by
      exact (AddMonoidAlgebra.coeff_mapRingHom
        (Ideal.Quotient.mk p.asIdeal) f m).symm.trans
        (congrArg (fun a : AddMonoidAlgebra (R ⧸ p.asIdeal) M => a.coeff m) hf)
    exact (hm.map (Ideal.Quotient.mk p.asIdeal)).ne_zero hc
  have hdisj : Disjoint (Submonoid.powers f : Set A) (q : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hqf
  have hqR : Ideal.comap (algebraMap R A) q = p.asIdeal := by
    ext r
    change ρ (algebraMap R A r) = 0 ↔ r ∈ p.asIdeal
    simp [ρ, A, AddMonoidAlgebra.coe_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
  let q' : Ideal B := q.map (algebraMap A B)
  have hq' : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) B q hq hdisj
  refine ⟨⟨q', hq'⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R B) q' = p.asIdeal
  rw [IsScalarTower.algebraMap_eq R A B, ← Ideal.comap_comap]
  change Ideal.comap (algebraMap R A)
    ((q.map (algebraMap A B)).under A) = p.asIdeal
  rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) B hq hdisj]
  exact hqR

/-- The actual localization algebra is faithfully flat, not merely nonzero
on field-valued test points. -/
theorem laurentAway_faithfullyFlat_of_isUnit_coeff
    (f : AddMonoidAlgebra R M) (m : M) (hm : IsUnit (f.coeff m)) :
    Module.FaithfullyFlat R (Localization.Away f) := by
  letI : Module.Free R (AddMonoidAlgebra R M) :=
    Module.Free.of_basis (AddMonoidAlgebra.basis M R)
  exact Module.FaithfullyFlat.of_comap_surjective
    (laurentAway_comap_surjective_of_isUnit_coeff f m hm)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.laurentAway_comap_surjective_of_isUnit_coeff
#print axioms PaperVerification.ToricSchemes.laurentAway_faithfullyFlat_of_isUnit_coeff
