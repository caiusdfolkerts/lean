import CommAlg.KoszulComplex.MonomialBasis
import Mathlib.RingTheory.FiniteLength

/-! # Actual ideal quotients with finitely many missing monomials have finite length -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Strands
open Classical CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The actual module quotient J/(I∩J), written without choosing a complement. -/
abbrev idealDifferenceQuotient (B C : Family V) :=
  (monomialIdeal k C) ⧸ Submodule.comap (monomialIdeal k C).subtype (monomialIdeal k B)

theorem idealDifferenceQuotient_finite (B C : Family V)
    (hholes : {a : Exponent V | Contains C a ∧ ¬Contains B a}.Finite) :
    Module.Finite k (idealDifferenceQuotient (k := k) B C) := by
  let J := monomialIdeal k C
  let N : Submodule (MvPolynomial V k) J := Submodule.comap J.subtype (monomialIdeal k B)
  let Q := J ⧸ N
  let H := {a : Exponent V // Contains C a ∧ ¬Contains B a}
  letI : Fintype H := hholes.fintype
  let q : J →ₗ[k] Q := N.mkQ.restrictScalars k
  let hvec : H → Q := fun a => q (monomialBasis C ⟨a.val, a.property.1⟩)
  let f : (H →₀ k) →ₗ[k] Q := Finsupp.linearCombination k hvec
  have hbas (a : {a : Exponent V // Contains C a}) :
      q (monomialBasis C a) ∈ LinearMap.range f := by
    by_cases ha : Contains B a.val
    · have hz : q (monomialBasis C a) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero N).mpr
        change (monomialBasis C a).val ∈ monomialIdeal k B
        rw [monomialBasis_val, monomial_mem_iff]
        exact ha
      rw [hz]
      exact Submodule.zero_mem _
    · let a' : H := ⟨a.val, a.property, ha⟩
      refine ⟨Finsupp.single a' 1, ?_⟩
      simp only [f, Finsupp.linearCombination_single, one_smul]
      rfl
  have hspan (x : J) : q x ∈ LinearMap.range f := by
    have hx : x ∈ Submodule.span k (Set.range (monomialBasis (k := k) C)) := by
      rw [(monomialBasis (k := k) C).span_eq]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hbas a
    | zero => simpa using (Submodule.zero_mem (LinearMap.range f))
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
    | smul c x hx ih => simpa using Submodule.smul_mem _ c ih
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := N.mkQ_surjective z
    obtain ⟨y, hy⟩ := hspan x
    exact ⟨y, hy.trans hx⟩
  exact Module.Finite.of_surjective f hf

theorem idealDifferenceQuotient_finiteLength (B C : Family V)
    (hholes : {a : Exponent V | Contains C a ∧ ¬Contains B a}.Finite) :
    IsFiniteLength (MvPolynomial V k) (idealDifferenceQuotient (k := k) B C) := by
  letI := idealDifferenceQuotient_finite (k := k) B C hholes
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

end Characterizations.Strands
