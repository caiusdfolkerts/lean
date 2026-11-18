module

public import ToricPower.ArrangementUniversalCover
public import ToricPower.ArrangementLocalSupport
public import ToricPower.CellularLocalMorse
public import ToricPower.ElementPullbackBaseChange

/-!
# A maximal support cell in the fixed finite fundamental domain

A periodic coefficient complex has a maximal nonzero cell among the
actual normalized quotient cells. Its canonical zero-weight lift is
maximal among all universal cells. This makes the later shrinking
threshold independent of the arbitrary target complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- The fixed zero-weight lift of an original normalized cell. -/
def normalizedUniversalCell (c : IncidenceObject A) : UniversalIncidenceObject A :=
  weightedIncidenceCellEquiv A (c,0)

@[simp]
theorem universalCoverProjection_normalized (c : IncidenceObject A) :
    (universalCoverProjection A).obj (normalizedUniversalCell A c) = c := by
  change ((weightedIncidenceCellEquiv A).symm ((weightedIncidenceCellEquiv A) (c,0))).1 = c
  rw [Equiv.symm_apply_apply]

@[simp]
theorem normalizedUniversalCell_dimension (c : IncidenceObject A) :
    (normalizedUniversalCell A c).1 = c.1 := rfl

@[simp]
theorem universalCoverProjection_dimension (c : UniversalIncidenceObject A) :
    ((universalCoverProjection A).obj c).1 = c.1 := rfl

variable (k : Type) [Field k]

/-- Literal pullback of an arbitrary complex to the universal cover. -/
abbrev universalPeriodicComplex (K : CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} k) ℤ) :
    CochainComplex (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) ℤ :=
  ((ElementPushdown.baseRestriction (universalCoverProjection A)
    (D := ModuleCat.{0} k)).mapHomologicalComplex (.up ℤ)).obj K

def normalizedPeriodicEvaluationIso
    (K : CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} k) ℤ) (c : IncidenceObject A) :
    ((universalPeriodicComplex A k K).asFunctor.obj (normalizedUniversalCell A c)) ≅
      K.asFunctor.obj c :=
  K.asFunctor.mapIso (eqToIso (universalCoverProjection_normalized A c))

/-- A nonzero full diagram complex has a nonzero actual coefficient. -/
theorem exists_nonacyclic_coefficient
    (K : CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} k) ℤ) (nonzero : ¬ K.Acyclic) :
    ∃ c, ¬ (K.asFunctor.obj c).Acyclic := by
  by_contra! vanishes
  exact nonzero (diagramComplex_acyclic_of_evaluation K vanishes)

/-- The chosen representative lies in the fixed finite domain; its
maximality concerns every translated universal cell and every degree. -/
theorem exists_normalized_maximal_support
    (K : CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} k) ℤ) (nonzero : ¬ K.Acyclic) :
    ∃ c : IncidenceObject A,
      ¬ ((universalPeriodicComplex A k K).asFunctor.obj (normalizedUniversalCell A c)).Acyclic ∧
      ∀ d : UniversalIncidenceObject A,
        ¬ ((universalPeriodicComplex A k K).asFunctor.obj d).Acyclic →
          d.1 ≤ (normalizedUniversalCell A c).1 := by
  classical
  let P : ℕ → Prop := fun q =>
    ∃ c : IncidenceObject A, ¬ (K.asFunctor.obj c).Acyclic ∧ c.1 = q
  obtain ⟨c₀,hc₀⟩ := exists_nonacyclic_coefficient A k K nonzero
  have highest : P (Nat.findGreatest P n) :=
    Nat.findGreatest_spec (cell_dimension_le A c₀.2.val) ⟨c₀,hc₀,rfl⟩
  obtain ⟨c,hc,dim⟩ := highest
  refine ⟨c,?_,?_⟩
  · intro zero
    apply hc
    intro q
    exact (exactAt_iff_of_quasiIsoAt (normalizedPeriodicEvaluationIso A k K c).hom q).mp
      (zero q)
  · intro d hd
    change ¬ (K.asFunctor.obj ((universalCoverProjection A).obj d)).Acyclic at hd
    rw [normalizedUniversalCell_dimension,dim]
    exact Nat.le_findGreatest (cell_dimension_le A d.2)
      ⟨(universalCoverProjection A).obj d,hd,rfl⟩

end ToricPower.IntegralArrangement

end
