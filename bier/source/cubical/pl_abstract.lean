import cubical.pl_barycentric

/-!
# Abstract simplicial graphs and links

These bridges retain the original vertex labels.  A topological statement
about standard realizations therefore yields rigidity of the original
combinatorial graph, including after passage through a barycentric
subdivision.
-/

noncomputable section

namespace Cubical.PL

open Set Geometry
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def standardVertex (i : ι) : ι → ℝ := Pi.single i 1

theorem standardVertex_injective : Function.Injective (standardVertex : ι → ι → ℝ) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp [standardVertex, Pi.single_apply, hij, Ne.symm hij] at hh

theorem image_mem_standardRealization_iff (P : PreAbstractSimplicialComplex ι)
    (s : Finset ι) :
    s.image standardVertex ∈ (standardRealization P).faces ↔ s ∈ P.faces := by
  classical
  constructor
  · rintro ⟨t, ht, heq⟩
    have : t = s := Finset.image_injective standardVertex_injective heq
    simpa [this] using ht
  · intro hs
    exact ⟨s, hs, rfl⟩

def abstractEdgeGraph (P : PreAbstractSimplicialComplex ι) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ {i, j} ∈ P.faces
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def standardVertexEquiv (P : PreAbstractSimplicialComplex ι)
    (hP : ∀ i, {i} ∈ P.faces) : ι ≃ (standardRealization P).vertices := by
  classical
  let f : ι → (standardRealization P).vertices := fun i => ⟨standardVertex i, by
    change {standardVertex i} ∈ (standardRealization P).faces
    exact ⟨{i}, hP i, by simp [standardVertex]⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    exact standardVertex_injective (congrArg Subtype.val hij)
  · intro x
    obtain ⟨s, hs, heq⟩ := x.property
    obtain ⟨i, hi⟩ := (P.isRelLowerSet_faces hs).1
    have hix : standardVertex i = x.val := by
      have hh := congrArg (fun t : Finset (ι → ℝ) => standardVertex i ∈ t) heq
      exact Finset.mem_singleton.mp (hh.mp (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    exact ⟨i, Subtype.ext hix⟩

@[simp]
theorem standardVertexEquiv_apply (P : PreAbstractSimplicialComplex ι)
    (hP : ∀ i, {i} ∈ P.faces) (i : ι) :
    (standardVertexEquiv P hP i).val = standardVertex i := rfl

def standardEdgeGraphIso (P : PreAbstractSimplicialComplex ι)
    (hP : ∀ i, {i} ∈ P.faces) :
    abstractEdgeGraph P ≃g
      DifferentialGeometry.Topology.SimplicialComplex.edgeGraph (standardRealization P) where
  __ := standardVertexEquiv P hP
  map_rel_iff' := by
    intro i j
    simp only [DifferentialGeometry.Topology.SimplicialComplex.edgeGraph_adj,
      standardVertexEquiv_apply, (standardVertexEquiv P hP).injective.ne_iff,
      abstractEdgeGraph]
    have hface := image_mem_standardRealization_iff P {i, j}
    apply and_congr_right
    intro _
    convert hface using 1
    apply Iff.of_eq
    apply congrArg (fun t => t ∈ (standardRealization P).faces)
    ext x
    simp

theorem abstractEdgeGraph_genericallyRigid (P : PreAbstractSimplicialComplex ι)
    (hvertices : ∀ i, {i} ∈ P.faces) {n : ℕ} (hn : 1 ≤ n)
    (hP : IsPLSphere (n + 1) (standardRealization P).space) :
    Cubical.Rigidity.GenericallyRigid (abstractEdgeGraph P)
      (EuclideanSpace ℝ (Fin (n + 2))) := by
  letI : Finite (standardRealization P).faces := (standardRealization_finite_faces P).to_subtype
  exact (sphere_edgeGraph_genericallyRigid (standardRealization P) hn hP).of_iso
    (standardEdgeGraphIso P hvertices).symm

theorem abstractEdgeGraph_genericallyRigid_of_barycentric_sphere
    (P : PreAbstractSimplicialComplex ι) (hvertices : ∀ i, {i} ∈ P.faces)
    {n : ℕ} (hn : 1 ≤ n)
    (hP : IsPLSphere (n + 1) (standardRealization (abstractBarycentric P)).space) :
    Cubical.Rigidity.GenericallyRigid (abstractEdgeGraph P)
      (EuclideanSpace ℝ (Fin (n + 2))) :=
  abstractEdgeGraph_genericallyRigid P hvertices hn
    ((isPLSphere_barycentric_iff P (n + 1)).mp hP)

open DifferentialGeometry.Topology.SimplicialComplex in
theorem standardRealization_link_singleton (P : PreAbstractSimplicialComplex ι) (i : ι) :
    standardRealization (link P {i}) = geometricLink (standardRealization P) {standardVertex i} := by
  classical
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [mem_geometricLink_singleton]
    refine ⟨Finset.image_nonempty.mpr hs.1, ?_, ?_⟩
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have hji' : j = i := standardVertex_injective hji
      exact (Finset.disjoint_singleton_left.mp hs.2.1) (hji' ▸ hj)
    · have hface : insert i s ∈ P.faces := by
        convert hs.2.2 using 1
        apply Iff.of_eq
        apply congrArg (fun t : Finset ι => t ∈ P.faces)
        ext j
        simp
      have himage := (image_mem_standardRealization_iff P (insert i s)).mpr hface
      convert himage using 1 <;> congr 1 <;> ext x <;> simp [standardVertex]
  · intro ht
    have hle := geometricLink_le (standardRealization P) {standardVertex i} ht
    obtain ⟨s, hs, rfl⟩ := hle
    rw [mem_geometricLink_singleton] at ht
    refine ⟨s, ?_, rfl⟩
    refine ⟨Finset.image_nonempty.mp ht.1, ?_, ?_⟩
    · apply Finset.disjoint_singleton_left.mpr
      intro hi
      exact ht.2.1 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · rw [Finset.singleton_union]
      apply (image_mem_standardRealization_iff P (insert i s)).mp
      convert ht.2.2 using 1 <;> congr 1 <;> ext x <;> simp [standardVertex]

open DifferentialGeometry.Topology.SimplicialComplex in
theorem isPLSphere_abstract_vertex_link (P : PreAbstractSimplicialComplex ι)
    {n : ℕ} (hP : IsPLSphere (n + 1) (standardRealization P).space)
    {i : ι} (hi : {i} ∈ P.faces) :
    IsPLSphere n (standardRealization (link P {i})).space := by
  classical
  letI : Finite (standardRealization P).faces := (standardRealization_finite_faces P).to_subtype
  rw [standardRealization_link_singleton]
  apply isPLSphere_geometricLink_of_isPLSphere (standardRealization P) hP
  exact ⟨{i}, hi, by simp [standardVertex]⟩

end Cubical.PL
