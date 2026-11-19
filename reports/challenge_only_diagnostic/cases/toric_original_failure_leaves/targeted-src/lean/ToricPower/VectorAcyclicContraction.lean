module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Contraction of arbitrary acyclic vector-space complexes

The cycle sequences of an acyclic vector-space complex are short exact.
Their actual projective splittings supply an explicit contracting
homotopy. The argument places no lower or upper bound on the degrees
and no finiteness condition on any coefficient vector space.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.Cellular

universe u

variable (k : Type u) [Field k]

/-- The cycle inclusion followed by the next cycle-valued differential
is zero, as follows after cancelling its actual monic cycle inclusion. -/
theorem vector_iCycles_toCycles (K : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    K.iCycles i ≫ K.toCycles i (i+1) = 0 := by
  apply (cancel_mono (K.iCycles (i+1))).mp
  simp only [Category.assoc, toCycles_i, iCycles_d, zero_comp]

/-- The literal short cycle sequence. -/
def vectorCycleSequence (K : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i (i+1)) (vector_iCycles_toCycles k K i)

/-- Exactness and surjectivity of that cycle sequence are proved from
acyclicity of the original complex and actual kernel universal properties. -/
theorem vectorCycleSequence_shortExact
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) (i : ℤ) :
    (vectorCycleSequence k K i).ShortExact := by
  have hprev : (ComplexShape.up ℤ).prev (i+1) = i := by simp
  have hnext : (ComplexShape.up ℤ).next (i+1) = i+1+1 := by simp
  have hshort := (K.exactAt_iff' i (i+1) (i+1+1) hprev hnext).mp (hK (i+1))
  letI : Epi ((K.sc' i (i+1) (i+1+1)).toCycles) := hshort.epi_toCycles
  have hfactor := K.toCycles_cyclesIsoSc'_hom i (i+1) (i+1+1) hprev hnext
  letI : Epi (K.toCycles i (i+1) ≫
      (K.cyclesIsoSc' i (i+1) (i+1+1) hprev hnext).hom) := by
    rw [hfactor]
    infer_instance
  letI : Epi (K.toCycles i (i+1)) :=
    (epi_comp_iff_of_isIso (K.toCycles i (i+1))
      (K.cyclesIsoSc' i (i+1) (i+1+1) hprev hnext).hom).mp inferInstance
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ShortComplex.exact_of_f_is_kernel
    exact isKernelOfComp (K.iCycles (i+1)) (K.d i (i+1))
      (K.cyclesIsKernel i (i+1) (by simp)) (vector_iCycles_toCycles k K i)
      (K.toCycles_i i (i+1))
  · change Mono (K.iCycles i)
    infer_instance
  · change Epi (K.toCycles i (i+1))
    infer_instance

/-- Every cycle sequence has an actual splitting, since its final
cycle vector space has an actual basis and is projective. -/
def vectorCycleSplitting
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) (i : ℤ) :
    (vectorCycleSequence k K i).Splitting := by
  letI : Projective (K.cycles (i+1)) :=
    ModuleCat.projective_of_free (Module.Basis.ofVectorSpace k (K.cycles (i+1)))
  exact (vectorCycleSequence_shortExact k K hK i).splittingOfProjective

/-- The degree `-1` component is the cycle retraction followed by the
preceding chosen cycle section. -/
def vectorContractingComponent
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) (i j : ℤ) :
    K.X i ⟶ K.X j :=
  if h : i = j+1 then
    (vectorCycleSplitting k K hK i).r ≫
      eqToHom (by
        change K.cycles i = K.cycles (j+1)
        exact congrArg (fun n : ℤ => K.cycles n) h) ≫ (vectorCycleSplitting k K hK j).s
  else 0

@[simp]
theorem vectorContractingComponent_succ
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) (i : ℤ) :
    vectorContractingComponent k K hK (i+1) i =
      (vectorCycleSplitting k K hK (i+1)).r ≫ (vectorCycleSplitting k K hK i).s := by
  simp only [vectorContractingComponent, dite_true, eqToHom_refl,
    Category.id_comp]

/-- The displayed choices give a genuine contracting homotopy of the
identity, including in the unbounded case. -/
def vectorAcyclicContraction
    (K : CochainComplex (ModuleCat.{u} k) ℤ) (hK : K.Acyclic) :
    Homotopy (𝟙 K) 0 where
  hom := vectorContractingComponent k K hK
  zero i j h := by
    unfold vectorContractingComponent
    apply dite_eq_right
    intro hij
    exact h hij.symm
  comm i := by
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j+1 := ⟨i-1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (j+1) (j+1+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel j (j+1) from rfl)]
    simp only [vectorContractingComponent_succ, id_f, zero_f, add_zero]
    rw [← K.toCycles_i (j+1) (j+1+1), ← K.toCycles_i j (j+1)]
    have hfirst : K.toCycles (j+1) (j+1+1) ≫ K.iCycles (j+1+1) ≫
        (vectorCycleSplitting k K hK (j+1+1)).r ≫
        (vectorCycleSplitting k K hK (j+1)).s =
      K.toCycles (j+1) (j+1+1) ≫ (vectorCycleSplitting k K hK (j+1)).s := by
      have h := congrArg (fun q => K.toCycles (j+1) (j+1+1) ≫ q ≫
          (vectorCycleSplitting k K hK (j+1)).s)
          (vectorCycleSplitting k K hK (j+1+1)).f_r
      simp only [vectorCycleSequence, Category.assoc, Category.comp_id, Category.id_comp] at h
      exact h
    have hsecond : (vectorCycleSplitting k K hK (j+1)).r ≫
        (vectorCycleSplitting k K hK j).s ≫ K.toCycles j (j+1) ≫ K.iCycles (j+1) =
      (vectorCycleSplitting k K hK (j+1)).r ≫ K.iCycles (j+1) := by
      simpa only [vectorCycleSequence, Category.assoc, Category.id_comp] using
        congrArg (fun q => (vectorCycleSplitting k K hK (j+1)).r ≫ q ≫ K.iCycles (j+1))
          (vectorCycleSplitting k K hK j).s_g
    simp only [Category.assoc, hfirst, hsecond]
    have h := (vectorCycleSplitting k K hK (j+1)).id.symm
    simp only [vectorCycleSequence] at h
    exact h.trans (add_comm _ _)

/-- Every unbounded complex of vector spaces is K-projective: compose
an arbitrary map with the explicit contraction of its acyclic target. -/
instance vectorComplex_isKProjective (K : CochainComplex (ModuleCat.{u} k) ℤ) :
    K.IsKProjective where
  nonempty_homotopy_zero {L} f hL := by
    exact ⟨by simpa only [Category.comp_id, comp_zero] using
      (vectorAcyclicContraction k L hL).compLeft f⟩

end ToricPower.Cellular

end
