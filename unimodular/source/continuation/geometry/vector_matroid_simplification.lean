module

public import Recovery.Unimodular.ProductVectorMatroid
public import Matroid.Simple

set_option autoImplicit false

@[expose] public section

noncomputable section
open Set
open scoped Matroid

namespace Unimodular.MatroidSimplification

/-- Surjectively repeating the labels of an ordinary matroid preserves its
simplification up to actual matroid isomorphism. Labels sent outside the
ground are allowed: they become loops. -/
noncomputable def comapOnSimplificationIso {α β : Type*} (M : Matroid β)
    (E : Set α) (f : α → β) (hsurj : Set.SurjOn f E M.E) :
    (M.comapOn E f).simplification ≂ M.simplification := by
  classical
  let Q := M.comapOn E f
  let S := Q.simplification
  have hS : S.IsSimplification Q := Q.simplification_isSimplification
  have hSE : S.E ⊆ E := hS.isRestriction.subset
  have hnonloop (x : α) (hx : x ∈ S.E) : M.IsNonloop (f x) := by
    have h := hS.isNonloop_of_mem hx
    change ((M.comap f) ↾ E).IsNonloop x at h
    exact Matroid.comap_isNonloop_iff.mp (Matroid.restrict_isNonloop_iff.mp h).1
  have hf : Set.InjOn f S.E := by
    intro x hx y hy hxy
    apply hS.eq_of_parallel hx hy
    change (M.comapOn E f).Parallel x y
    apply Matroid.comapOn_parallel_iff.mpr
    refine ⟨?_, hSE hx, hSE hy⟩
    rw [← hxy]
    exact (hnonloop x hx).parallel_self
  have hmap : S.map f hf = M ↾ (f '' S.E) := by
    refine Matroid.ext_indep ?_ ?_
    · simp
    intro I hI
    rw [Matroid.map_indep_iff, Matroid.restrict_indep_iff]
    constructor
    · rintro ⟨J, hJ, rfl⟩
      have hJQ := (hS.isRestriction.indep_iff.mp hJ).1
      change (M.comapOn E f).Indep J at hJQ
      exact ⟨(Matroid.comapOn_indep_iff.mp hJQ).1,
        Set.image_mono hJ.subset_ground⟩
    · rintro ⟨hI, hIR⟩
      obtain ⟨J, hJS, hbij⟩ := Set.SurjOn.exists_bijOn_subset hIR
      refine ⟨J, hS.isRestriction.indep_iff.mpr ⟨?_, hJS⟩, hbij.image_eq.symm⟩
      change (M.comapOn E f).Indep J
      exact Matroid.comapOn_indep_iff.mpr
        ⟨by rwa [hbij.image_eq], hbij.injOn, hJS.trans hSE⟩
  have hrestriction : S.map f hf ≤r M := by
    refine ⟨f '' S.E, ?_, hmap⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hnonloop x hx).mem_ground
  have hsimplifies : (S.map f hf).Simplifies M := by
    refine ⟨hrestriction, ?_⟩
    intro y hy
    obtain ⟨x, hxE, hxy⟩ := hsurj hy.mem_ground
    have hx : Q.IsNonloop x := by
      change ((M.comap f) ↾ E).IsNonloop x
      exact Matroid.restrict_isNonloop_iff.mpr
        ⟨Matroid.comap_isNonloop_iff.mpr (hxy.symm ▸ hy), hxE⟩
    obtain ⟨z, hz, hxz⟩ := hS.simplifies.exists_of_isNonloop hx
    refine ⟨f z, ?_, ?_⟩
    · change f z ∈ f '' S.E
      exact ⟨z, hz, rfl⟩
    · have hparallel := (Matroid.comapOn_parallel_iff.mp hxz).1
      simpa only [hxy] using hparallel
  have hSM : (S.map f hf).IsSimplification M :=
    (hS.simple.map hf).isSimplification_of_simplifies hsimplifies
  exact (Matroid.isoMap S f hf).trans (hSM.iso M.simplification_isSimplification)

end Unimodular.MatroidSimplification

namespace Unimodular.VectorMatroid

variable {K α β V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Composition of a represented family is the ordinary comap on the full
original label set, including repeated columns and zero vectors. -/
theorem onSet_comp_eq_comapOn_image (v : β → V) (f : α → β) (E : Set α) :
    onSet (K := K) (v ∘ f) E = (onSet (K := K) v (f '' E)).comapOn E f := by
  refine Matroid.ext_indep ?_ ?_
  · simp
  intro I hI
  rw [onSet_indep, Matroid.comapOn_indep_iff, onSet_indep]
  constructor
  · rintro ⟨hIE, hli⟩
    refine ⟨⟨Set.image_mono hIE, hli.image_of_comp f v⟩, ?_, hIE⟩
    intro x hx y hy hxy
    apply hli.injOn hx hy
    change v (f x) = v (f y)
    rw [hxy]
  · rintro ⟨⟨_, hli⟩, hf, hIE⟩
    exact ⟨hIE, hli.comp_of_image hf⟩

/-- Passing from a vector family to its set of values preserves its actual
ordinary simplification. No injectivity or nonzero assumption is supplied. -/
noncomputable def simplificationIsoImage (v : β → V) (f : α → β) (E : Set α) :
    (onSet (K := K) (v ∘ f) E).simplification ≂
      (onSet (K := K) v (f '' E)).simplification := by
  rw [onSet_comp_eq_comapOn_image]
  exact MatroidSimplification.comapOnSimplificationIso _ E f
    (by rintro y ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩)

/-- Zero represented vectors are exactly loops, on the actual stated ground. -/
theorem onSet_isLoop_iff (v : β → V) {E : Set β} {e : β} (he : e ∈ E) :
    (onSet (K := K) v E).IsLoop e ↔ v e = 0 := by
  rw [← Matroid.singleton_not_indep (show e ∈ (onSet (K := K) v E).E from he),
    onSet_indep, Set.singleton_subset_iff, and_iff_right he,
    linearIndepOn_singleton_iff, not_not]

/-- Discarding precisely the zero columns and all repeated vector values
preserves the full ordinary simplification, including the empty case. -/
noncomputable def simplificationIsoNonzeroImage (v : β → V) (f : α → β) (E : Set α) :
    (onSet (K := K) (v ∘ f) E).simplification ≂
      (onSet (K := K) v {y | y ∈ f '' E ∧ v y ≠ 0}).simplification := by
  let Q := onSet (K := K) v (f '' E)
  let D : Set β := (f '' E) ∩ {y | v y = 0}
  have hD : D ⊆ Q.loops := by
    intro y hy
    exact (onSet_isLoop_iff v hy.1).mpr hy.2
  have hdelete : Q ＼ D = onSet (K := K) v {y | y ∈ f '' E ∧ v y ≠ 0} := by
    dsimp only [Q]
    rw [delete_onSet]
    apply congrArg (onSet (K := K) v)
    ext y
    constructor
    · rintro ⟨hy, hn⟩
      exact ⟨hy, fun hz => hn ⟨hy, hz⟩⟩
    · rintro ⟨hy, hn⟩
      exact ⟨hy, fun hz => hn hz.2⟩
  have hs : Q.simplification =
      (onSet (K := K) v {y | y ∈ f '' E ∧ v y ≠ 0}).simplification := by
    rw [← hdelete]
    exact (Q.simplification_delete_eq_of_subset_loops hD).symm
  exact (simplificationIsoImage v f E).trans (Matroid.Iso.ofEq hs)

end Unimodular.VectorMatroid

#print axioms Unimodular.MatroidSimplification.comapOnSimplificationIso
#print axioms Unimodular.VectorMatroid.onSet_comp_eq_comapOn_image
#print axioms Unimodular.VectorMatroid.simplificationIsoNonzeroImage
