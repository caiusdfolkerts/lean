module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Formal smoothness descends to an algebra retract

A lifting problem for a retract is composed with the retraction, solved
for the larger smooth algebra, and restricted along the section. This is
used for the pointed factor of a smooth affine monoid algebra.
-/

@[expose] public section

universe u v

namespace PaperVerification.ToricCharacters

variable {R : Type u} {A B : Type v} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]

/-- Formal smoothness of the larger algebra supplies genuine lifts for
every square-zero extension of the retract. -/
theorem formallySmooth_of_algebra_retract [Algebra.FormallySmooth R B]
    (i : A →ₐ[R] B) (r : B →ₐ[R] A) (hri : r.comp i = AlgHom.id R A) :
    Algebra.FormallySmooth R A := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro C _ _ I hI f
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R B I hI (f.comp r)
  refine ⟨g.comp i, ?_⟩
  calc
    (Ideal.Quotient.mkₐ R I).comp (g.comp i) =
        ((Ideal.Quotient.mkₐ R I).comp g).comp i := (AlgHom.comp_assoc _ _ _).symm
    _ = (f.comp r).comp i := congrArg (fun h => h.comp i) hg
    _ = f.comp (r.comp i) := AlgHom.comp_assoc _ _ _
    _ = f := by rw [hri, AlgHom.comp_id]

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.formallySmooth_of_algebra_retract
