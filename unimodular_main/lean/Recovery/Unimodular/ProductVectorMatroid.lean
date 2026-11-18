module

public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Combinatorics.Matroid.Minor.Order
public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

noncomputable section

open Set
open scoped Matroid

namespace Unimodular.VectorMatroid

variable {K α V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Finite linear-independence augmentation, proved from dimensions of the actual spans. -/
theorem linearIndepOn_finset_augment (v : α → V) {I J : Finset α}
    (hI : LinearIndepOn K v (I : Set α)) (hJ : LinearIndepOn K v (J : Set α))
    (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K v (insert e (I : Set α)) := by
  classical
  have hex : ∃ e ∈ J, v e ∉ Submodule.span K (v '' (I : Set α)) := by
    by_contra hn
    have hspan : Submodule.span K (v '' (J : Set α)) ≤
        Submodule.span K (v '' (I : Set α)) := by
      apply Submodule.span_le.2
      rintro _ ⟨e, he, rfl⟩
      by_contra he'
      exact hn ⟨e, he, he'⟩
    letI : FiniteDimensional K (Submodule.span K (v '' (I : Set α))) :=
      FiniteDimensional.span_of_finite K (I.finite_toSet.image v)
    have hdimI : Module.finrank K (Submodule.span K (v '' (I : Set α))) = I.card := by
      rw [Set.image_eq_range]
      simpa only [Finset.coe_sort_coe, Fintype.card_coe] using
        (finrank_span_eq_card hI)
    have hdimJ : Module.finrank K (Submodule.span K (v '' (J : Set α))) = J.card := by
      rw [Set.image_eq_range]
      simpa only [Finset.coe_sort_coe, Fintype.card_coe] using
        (finrank_span_eq_card hJ)
    have hle := Submodule.finrank_mono hspan
    rw [hdimI, hdimJ] at hle
    exact (Nat.not_le_of_lt hcard) hle
  obtain ⟨e, heJ, he⟩ := hex
  refine ⟨e, heJ, ?_, hI.insert he⟩
  intro heI
  exact he (Submodule.subset_span ⟨e, heI, rfl⟩)

/-- The standard vector matroid on a specified ground set. Independence means literal
linear independence of the labelled vectors; loops and parallel labels are retained. -/
def onSet (v : α → V) (E : Set α) : Matroid α := by
  classical
  exact (IndepMatroid.ofFinset E
    (fun I => (I : Set α) ⊆ E ∧ LinearIndepOn K v (I : Set α))
    (by simp)
    (fun _ _ h hIJ => ⟨(Finset.coe_subset.2 hIJ).trans h.1,
      h.2.mono (Finset.coe_subset.2 hIJ)⟩)
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI, hli⟩ := linearIndepOn_finset_augment v hI.2 hJ.2 hcard
      refine ⟨e, heJ, heI, ?_⟩
      exact ⟨by simpa only [Finset.coe_insert] using Set.insert_subset (hJ.1 heJ) hI.1,
        by simpa only [Finset.coe_insert] using hli⟩)
    (fun _ h => h.1)).matroid

@[simp] theorem onSet_ground (v : α → V) (E : Set α) :
    (onSet (K := K) v E).E = E := rfl

/-- Full independent-set semantics, including infinite sets. This is the link between
Mathlib's ordinary matroid object and linear algebra, not a restricted-size surrogate. -/
@[simp] theorem onSet_indep (v : α → V) (E I : Set α) :
    (onSet (K := K) v E).Indep I ↔ I ⊆ E ∧ LinearIndepOn K v I := by
  classical
  change (∀ J : Finset α, (J : Set α) ⊆ I →
    (J : Set α) ⊆ E ∧ LinearIndepOn K v (J : Set α)) ↔ _
  constructor
  · intro h
    refine ⟨?_, linearIndepOn_of_finite I ?_⟩
    · intro e he
      exact (h {e} (by simpa using he)).1 (by simp)
    · intro J hJI hJ
      simpa only [Set.Finite.coe_toFinset] using
        (h hJ.toFinset (by simpa only [Set.Finite.coe_toFinset] using hJI)).2
  · rintro ⟨hIE, hli⟩ J hJI
    exact ⟨hJI.trans hIE, hli.mono hJI⟩

/-- A vector family with every label in the ground set. -/
def ofFamily (v : α → V) : Matroid α := onSet (K := K) v Set.univ

@[simp] theorem ofFamily_ground (v : α → V) : (ofFamily (K := K) v).E = Set.univ := rfl

@[simp] theorem ofFamily_indep (v : α → V) (I : Set α) :
    (ofFamily (K := K) v).Indep I ↔ LinearIndepOn K v I := by
  simp [ofFamily]

/-- Relabelled families have the same matroid exactly when all their independent
sets agree. Quantification is over every subset of the ground-label type. -/
theorem ofFamily_eq_iff (v : α → V) (w : α → W) :
    ofFamily (K := K) v = ofFamily (K := K) w ↔
      ∀ I : Set α, LinearIndepOn K v I ↔ LinearIndepOn K w I := by
  constructor
  · intro h I
    rw [← ofFamily_indep, h, ofFamily_indep]
  · intro h
    exact Matroid.ext_indep rfl (fun I _ => by simpa using h I)

/-- An injective relabeling of a represented family is the same actual matroid
as the corresponding family on the image ground set. -/
theorem ofFamily_mapEmbedding_eq_onSet {β : Type*}
    (v : α → V) (w : β → V) (f : α ↪ β) (h : ∀ a, w (f a) = v a) :
    (ofFamily (K := K) v).mapEmbedding f = onSet (K := K) w (Set.range f) := by
  apply Matroid.ext_indep (by simp)
  intro I hI
  have hIR : I ⊆ Set.range f := by simpa using hI
  have he : w ∘ f = v := funext h
  rw [Matroid.mapEmbedding_indep_iff, ofFamily_indep, onSet_indep]
  constructor
  · rintro ⟨hli, _⟩
    refine ⟨hIR, ?_⟩
    have hc : LinearIndepOn K (w ∘ f) (f ⁻¹' I) := by rwa [he]
    have hi := hc.image_of_comp f w
    rwa [Set.image_preimage_eq_of_subset hIR] at hi
  · rintro ⟨_, hli⟩
    refine ⟨?_, hIR⟩
    have hi : LinearIndepOn K w (f '' (f ⁻¹' I)) := by
      rwa [Set.image_preimage_eq_of_subset hIR]
    have hc := hi.comp_of_image f.injective.injOn
    rwa [he] at hc

/-- Restricting a represented matroid to a genuine subset of its ground set
is exactly restriction of its labelled vector family. -/
theorem restrict_onSet (v : α → V) {E R : Set α} (hR : R ⊆ E) :
    (onSet (K := K) v E) ↾ R = onSet (K := K) v R := by
  apply Matroid.ext_indep (by simp)
  intro I hI
  rw [Matroid.restrict_indep_iff, onSet_indep, onSet_indep]
  exact ⟨fun h => ⟨h.2, h.1.2⟩,
    fun h => ⟨⟨h.1.trans hR, h.2⟩, h.1⟩⟩

/-- Ordinary matroid deletion agrees with removal of labels from the vector family. -/
theorem delete_onSet (v : α → V) (E D : Set α) :
    (onSet (K := K) v E) ＼ D = onSet (K := K) v (E \ D) := by
  exact restrict_onSet v Set.sdiff_subset

/-- A matroid basis of a subset spans exactly the same vector subspace as that subset. -/
theorem isBasis_span_eq (v : α → V) {E B C : Set α}
    (hB : (onSet (K := K) v E).IsBasis B C) :
    Submodule.span K (v '' B) = Submodule.span K (v '' C) := by
  apply le_antisymm (Submodule.span_mono (Set.image_mono hB.subset))
  apply Submodule.span_le.2
  rintro _ ⟨e, he, rfl⟩
  by_contra hn
  have hli := ((onSet_indep v E B).1 hB.indep).2
  have hi : (onSet (K := K) v E).Indep (insert e B) :=
    (onSet_indep v E _).2
      ⟨Set.insert_subset (hB.subset_ground he) hB.indep.subset_ground, hli.insert hn⟩
  exact hn (Submodule.subset_span ⟨e, hB.mem_of_insert_indep he hi, rfl⟩)

/-- Linear independence after a linear map is precisely original independence
and trivial intersection of its span with the actual kernel. -/
theorem linearIndepOn_map_iff (v : α → V) (q : V →ₗ[K] W) (I : Set α) :
    LinearIndepOn K (q ∘ v) I ↔ LinearIndepOn K v I ∧
      Disjoint (Submodule.span K (v '' I)) (LinearMap.ker q) := by
  constructor
  · intro h
    refine ⟨h.of_comp q, ?_⟩
    simpa only [Set.image_eq_range] using
      (Submodule.range_ker_disjoint (show LinearIndependent K
        (q ∘ (fun i : I => v i.val)) from h))
  · rintro ⟨h, hd⟩
    exact h.map_injOn q (LinearMap.injOn_of_disjoint_ker le_rfl hd)

/-- Matroid contraction is exactly projection by the span of the contracted
vectors. Surjectivity is deliberately unnecessary: an injective enlargement
of the quotient ambient space does not change any independent subset. -/
theorem contract_onSet (v : α → V) {E C : Set α} (hC : C ⊆ E)
    (q : V →ₗ[K] W) (hker : LinearMap.ker q = Submodule.span K (v '' C)) :
    (onSet (K := K) v E) ／ C = onSet (K := K) (q ∘ v) (E \ C) := by
  obtain ⟨B, hB⟩ := (onSet (K := K) v E).exists_isBasis C hC
  have hspan := isBasis_span_eq v hB
  have hBli := ((onSet_indep v E B).1 hB.indep).2
  apply Matroid.ext_indep (by simp)
  intro I hI
  change I ⊆ E \ C at hI
  have hIE : I ⊆ E := hI.trans Set.sdiff_subset
  have hIC : Disjoint I C := Set.disjoint_left.2 (fun e heI heC => (hI heI).2 heC)
  have hIB : Disjoint I B := hIC.mono_right hB.subset
  have hground : I ∪ B ⊆ E := Set.union_subset hIE hB.indep.subset_ground
  rw [hB.contract_indep_iff, onSet_indep, onSet_indep]
  simp only [hground, hIC.symm, hI, true_and, and_true]
  rw [linearIndepOn_union_iff hIB, linearIndepOn_map_iff, hker, ← hspan]
  simp only [hBli, true_and]

/-- Specializing the quotient map itself gives the standard quotient-space
representation of a matroid contraction, including dependent contracted sets. -/
theorem contract_eq_quotient (v : α → V) {E C : Set α} (hC : C ⊆ E) :
    (onSet (K := K) v E) ／ C =
      onSet (K := K) ((Submodule.span K (v '' C)).mkQ ∘ v) (E \ C) :=
  contract_onSet v hC _ (Submodule.ker_mkQ _)

/-- An exact kernel-and-image certificate identifies the relabelled target with
an ordinary contraction followed by deletion. All labels of the target are retained. -/
theorem mapEmbedding_eq_minor {β : Type*} (v : α → V) (w : β → W)
    {E C : Set α} (hC : C ⊆ E) (f : β ↪ α) (hR : Set.range f ⊆ E \ C)
    (q : V →ₗ[K] W) (hker : LinearMap.ker q = Submodule.span K (v '' C))
    (hf : ∀ j, q (v (f j)) = w j) :
    (ofFamily (K := K) w).mapEmbedding f =
      (onSet (K := K) v E) ／ C ＼ ((E \ C) \ Set.range f) := by
  rw [contract_onSet v hC q hker, delete_onSet, Set.sdiff_sdiff_cancel_left hR]
  exact ofFamily_mapEmbedding_eq_onSet w (q ∘ v) f hf

/-- The same certificate proves Mathlib's standard matroid minor relation. -/
theorem mapEmbedding_isMinor_of_kernel_image {β : Type*} (v : α → V) (w : β → W)
    {E C : Set α} (hC : C ⊆ E) (f : β ↪ α) (hR : Set.range f ⊆ E \ C)
    (q : V →ₗ[K] W) (hker : LinearMap.ker q = Submodule.span K (v '' C))
    (hf : ∀ j, q (v (f j)) = w j) :
    (ofFamily (K := K) w).mapEmbedding f ≤m onSet (K := K) v E :=
  ⟨C, (E \ C) \ Set.range f, mapEmbedding_eq_minor v w hC f hR q hker hf⟩

/-- A zero vector is exactly a loop of the represented matroid. -/
@[simp] theorem ofFamily_isLoop_iff (v : α → V) (e : α) :
    (ofFamily (K := K) v).IsLoop e ↔ v e = 0 := by
  rw [← Matroid.singleton_not_indep (by simp), ofFamily_indep,
    linearIndepOn_singleton_iff, not_not]

end Unimodular.VectorMatroid

end

#print axioms Unimodular.VectorMatroid.onSet_indep
#print axioms Unimodular.VectorMatroid.ofFamily_indep
#print axioms Unimodular.VectorMatroid.ofFamily_eq_iff
#print axioms Unimodular.VectorMatroid.ofFamily_mapEmbedding_eq_onSet
#print axioms Unimodular.VectorMatroid.isBasis_span_eq
#print axioms Unimodular.VectorMatroid.contract_onSet
#print axioms Unimodular.VectorMatroid.mapEmbedding_isMinor_of_kernel_image
#print axioms Unimodular.VectorMatroid.ofFamily_isLoop_iff
#check "UNIMODULAR_PRODUCT_VECTOR_MATROID_EOF_V1"
