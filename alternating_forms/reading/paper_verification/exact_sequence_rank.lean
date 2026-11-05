import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Dimension bounds at the middle of an exact sequence

The maps need only be exact at the middle term. In particular, the right map
need not be surjective. This is the form needed for the long exact sequence of
an actual pair of topological spaces.
-/

namespace PaperVerification.ExactSequenceRank

noncomputable section

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/-- Finiteness of the two outside terms implies finiteness of the middle. -/
theorem finite_middle (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h : LinearMap.range f = LinearMap.ker g)
    [Module.Finite K A] [Module.Finite K C] : Module.Finite K B := by
  apply Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
  · apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, h]
  · exact g.surjective_rangeRestrict

/-- The actual rank of the middle term is bounded by the sum of the
outside ranks, with no surjectivity assumption on either map. -/
theorem finrank_middle_le (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h : LinearMap.range f = LinearMap.ker g)
    [Module.Finite K A] [Module.Finite K C] :
    Module.finrank K B ≤ Module.finrank K A + Module.finrank K C := by
  letI := finite_middle f g h
  rw [← g.finrank_range_add_finrank_ker, ← h]
  exact (Nat.add_le_add (LinearMap.range g).finrank_le f.finrank_range_le).trans_eq
    (Nat.add_comm _ _)

/-- Zero outside terms force the actual middle vector space to vanish. -/
theorem subsingleton_middle (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h : LinearMap.range f = LinearMap.ker g)
    [Subsingleton A] [Subsingleton C] : Subsingleton B := by
  have hf : f = 0 := Subsingleton.elim _ _
  have hg : g = 0 := Subsingleton.elim _ _
  have hb : (⊥ : Submodule K B) = ⊤ := by
    simpa only [hf, hg, LinearMap.range_zero, LinearMap.ker_zero] using h
  have hzero (x : B) : x = 0 := by
    apply (Submodule.mem_bot K).mp
    rw [hb]
    trivial
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end
end PaperVerification.ExactSequenceRank
