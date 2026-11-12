module

public import ToricPower.WeightedDerivedCoverLift
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Finite homological fiber support for the full covering lift

The hypothesis concerns the nonzero homology of the original entire
character diagram. Cochains may have infinitely many nonzero weights;
the comparison does not truncate them.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (R : Type) [CommRing R]

private theorem extendNat_acyclic
    (K : CochainComplex (ModuleCat.{0} R) ℕ) (acyclic : K.Acyclic) :
    (K.extend ComplexShape.embeddingUpNat).Acyclic := by
  intro q
  by_cases present : ∃ p : ℕ, (p : ℤ) = q
  · obtain ⟨p,hp⟩ := present
    exact (K.extend_exactAt_iff ComplexShape.embeddingUpNat hp).mpr (acyclic p)
  · exact K.extend_exactAt ComplexShape.embeddingUpNat q (by
      intro p hp
      exact present ⟨p,hp⟩)

/-- Finiteness of actual homology on every original covering fiber. -/
theorem weightedCoverLiftComplex_finite_support
    (F : WeightedIncidenceObject A ⥤ CochainComplex (ModuleCat.{0} R) ℕ)
    (finite : {w : WeightedIncidenceObject A | ∃ p : ℕ,
      Nontrivial ((F.obj w).homology p)}.Finite)
    (q : ℤ) (c : IncidenceObject A) :
    {m : (universalWeightFunctor A).obj c | ¬ IsZero
      (((weightedCoverLiftComplex A R F).homology q).obj
        ((universalWeightFunctor A).elementsMk c m))}.Finite := by
  have injective : Function.Injective (fun m : Fin n → ℤ => (c,m)) :=
    fun _ _ h => congrArg Prod.snd h
  apply (Set.Finite.preimage injective.injOn finite).subset
  intro m nonzero
  by_contra outside
  have acyclic : (F.obj (c,m)).Acyclic := by
    intro p
    rw [HomologicalComplex.exactAt_iff_isZero_homology,ModuleCat.isZero_iff_subsingleton]
    apply not_nontrivial_iff_subsingleton.mp
    exact fun hp => outside ⟨p,hp⟩
  let K := weightedCoverLiftComplex A R F
  let ev := (evaluation (universalWeightFunctor A).Elements (ModuleCat.{0} R)).obj
    ((universalWeightFunctor A).elementsMk c m)
  have acyclicEvaluated : ((ev.mapHomologicalComplex (.up ℤ)).obj K).Acyclic :=
    extendNat_acyclic R (F.obj (c,m)) acyclic
  have zero : IsZero (((ev.mapHomologicalComplex (.up ℤ)).obj K).homology q) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (acyclicEvaluated q)
  exact nonzero (((K.sc q).mapHomologyIso ev).isZero_iff.mp zero)

end ToricPower.IntegralArrangement

end
