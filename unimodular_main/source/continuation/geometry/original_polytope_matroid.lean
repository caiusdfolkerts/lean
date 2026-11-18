module

public import Continuation.Geometry.OriginalPolytopeCorners
public import Continuation.Geometry.OriginalPolytopeReflexivity
public import Unimodular.SeriesParallelPrincipal

/-!
# Theorem 1.2 on the original lattice and its ordinary matroid minors

The input is the intrinsic original-lattice geometric presentation. Its
normal matroid is represented by the actual real extensions of its integral
primitive facet normals. All coordinates, geometric comparisons and label
maps are derived before applying the existing combinatorial theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open PaperVerification.OriginalLatticeCharts
open scoped Classical Matroid

namespace Unimodular.VectorMatroid

/-- Injective linear transport preserves the whole represented on-set
matroid, including every subset of the original ground labels. -/
theorem onSet_comp_injective {K α A B : Type*} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (v : α → A) (f : A →ₗ[K] B) (hf : Function.Injective f) (E : Set α) :
    onSet (K := K) (f ∘ v) E = onSet (K := K) v E := by
  apply Matroid.ext_indep (M₁ := onSet (K := K) (f ∘ v) E) (M₂ := onSet (K := K) v E) rfl
  intro I _
  rw [onSet_indep, onSet_indep]
  apply and_congr Iff.rfl
  change LinearIndependent K (f ∘ (fun a : I => v a.val)) ↔
    LinearIndependent K (fun a : I => v a.val)
  exact f.linearIndependent_iff (LinearMap.ker_eq_bot.mpr hf)

/-- Simultaneous invertible changes of labels and representing vectors
produce exactly the relabelled ordinary matroid. -/
theorem onSet_mapEquiv_linearEquiv {K α β A B : Type*} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (v : α → A) (w : β → B) (E : Set α)
    (e : α ≃ β) (f : A ≃ₗ[K] B) (hcomp : ∀ a, w (e a) = f (v a)) :
    (onSet (K := K) v E).mapEquiv e = onSet (K := K) w (e '' E) := by
  apply Matroid.ext_indep (by simp)
  intro I hIE
  have hsubset : I ⊆ e '' E := by simpa using hIE
  have hlinear (S : Set α) :
      LinearIndepOn K (f ∘ v) S ↔ LinearIndepOn K v S := by
    change LinearIndependent K (f.toLinearMap ∘ (fun a : S => v a.val)) ↔
      LinearIndependent K (fun a : S => v a.val)
    exact f.toLinearMap.linearIndependent_iff (LinearMap.ker_eq_bot.mpr f.injective)
  have he : w ∘ e = f ∘ v := funext hcomp
  rw [Matroid.mapEquiv_indep_iff, onSet_indep, onSet_indep]
  constructor
  · rintro ⟨_, hli⟩
    refine ⟨hsubset, ?_⟩
    have hc : LinearIndepOn K (w ∘ e) (e.symm '' I) := by
      rw [he]
      exact (hlinear _).mpr hli
    have h := hc.image_of_comp e w
    simpa only [e.image_symm_image] using h
  · rintro ⟨hsub, hli⟩
    refine ⟨?_, ?_⟩
    · rintro a ⟨x, hx, rfl⟩
      obtain ⟨a, ha, he⟩ := hsub hx
      rw [← he, e.symm_apply_apply]
      exact ha
    · have h' : LinearIndepOn K w (e '' (e.symm '' I)) := by
        simpa only [e.image_symm_image] using hli
      have hc := h'.comp_of_image e.injective.injOn
      rw [he] at hc
      exact (hlinear _).mp hc

end Unimodular.VectorMatroid

universe u v

namespace Unimodular.OriginalSmoothReflexivePresentation

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {ι : N →+ V} (P : OriginalSmoothReflexivePresentation n ι)

/-- The actual primitive-normal matroid on the original integral dual.
The ground set is defined by supporting inequalities and genuine facets. -/
def normalMatroid : Matroid (N →+ ℤ) :=
  VectorMatroid.onSet (K := ℝ) (fun m : N →+ ℤ => P.lattice.realCharacter m)
    P.geometricFacetNormals

@[simp] theorem normalMatroid_ground : P.normalMatroid.E = P.geometricFacetNormals := rfl

variable (b : Module.Basis (Fin n) ℤ N)

/-- Keeping every original normal label, changing real coordinates preserves
the literal matroid, not merely its rank or its full-size determinants. -/
theorem normalMatroid_in_coordinates :
    VectorMatroid.onSet (K := ℝ)
      (fun m : N →+ ℤ => embed (characterCoordinates b m)) P.geometricFacetNormals =
        P.normalMatroid := by
  have he : (fun m : N →+ ℤ => embed (characterCoordinates b m)) =
      (realCharacterCoordinates b P.lattice).toLinearMap ∘
        (fun m : N →+ ℤ => P.lattice.realCharacter m) := by
    funext m
    exact (realCharacterCoordinates_lattice b P.lattice m).symm
  rw [he]
  exact VectorMatroid.onSet_comp_injective _ _
    (realCharacterCoordinates b P.lattice).injective P.geometricFacetNormals

/-- Exact normal-matroid relabelling by the integral dual-basis equivalence. -/
theorem normalMatroid_coordinates :
    P.normalMatroid.mapEquiv (characterCoordinates b).toEquiv =
      VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n)
        (P.coordinatePresentation b).geometricFacetNormals := by
  calc
    P.normalMatroid.mapEquiv (characterCoordinates b).toEquiv =
        VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n)
          (characterCoordinates b '' P.geometricFacetNormals) :=
      VectorMatroid.onSet_mapEquiv_linearEquiv
        (fun m : N →+ ℤ => P.lattice.realCharacter m) embed P.geometricFacetNormals
        (characterCoordinates b).toEquiv (realCharacterCoordinates b P.lattice)
        (fun m => (realCharacterCoordinates_lattice b P.lattice m).symm)
    _ = _ := by rw [P.geometricFacetNormals_coordinate_image]

theorem normalMatroid_coordinates_list :
    P.normalMatroid.mapEquiv (characterCoordinates b).toEquiv =
      VectorMatroid.onSet (K := ℝ) (embed : Lattice n → Ambient n)
        ((P.coordinatePresentation b).normals : Set (Lattice n)) := by
  rw [P.normalMatroid_coordinates,
    (P.coordinatePresentation b).geometricFacetNormals_eq_normals]

/-- The normal matroid on the original labels is independent of the chosen
integral coordinate basis. -/
theorem normalMatroid_coordinate_basis_independent
    (c : Module.Basis (Fin n) ℤ N) :
    VectorMatroid.onSet (K := ℝ)
        (fun m : N →+ ℤ => embed (characterCoordinates b m)) P.geometricFacetNormals =
      VectorMatroid.onSet (K := ℝ)
        (fun m : N →+ ℤ => embed (characterCoordinates c m)) P.geometricFacetNormals :=
  (P.normalMatroid_in_coordinates b).trans (P.normalMatroid_in_coordinates c).symm

/-- Corollary 6.2 in the original integral dual: every real-independent
full selection of the actual geometric normals is an integral basis. -/
theorem deeplyMonotone_facetNormals_uniform (hP : P.DeeplyMonotone)
    (a : Fin n → {m // m ∈ P.geometricFacetNormals})
    (ha : LinearIndependent ℝ (fun i => P.lattice.realCharacter (a i).val)) :
    ∃ c : Module.Basis (Fin n) ℤ (N →+ ℤ), ∀ i, c i = (a i).val := by
  let b := P.coordinateBasis
  let a' : Fin n → {u // u ∈ (P.coordinatePresentation b).geometricFacetNormals} :=
    fun i => ⟨characterCoordinates b (a i).val,
      (P.geometricFacetNormals_coordinate_iff b (a i).val).mpr (a i).property⟩
  have ha' : LinearIndependent ℝ (fun i => embed (a' i).val) := by
    have h : LinearIndependent ℝ
        ((realCharacterCoordinates b P.lattice).toLinearMap ∘
          (fun i => P.lattice.realCharacter (a i).val)) :=
      ((realCharacterCoordinates b P.lattice).toLinearMap.linearIndependent_iff
        (LinearMap.ker_eq_bot.mpr (realCharacterCoordinates b P.lattice).injective)).mpr ha
    have he : ((realCharacterCoordinates b P.lattice).toLinearMap ∘
        (fun i => P.lattice.realCharacter (a i).val)) = (fun i => embed (a' i).val) := by
      funext i
      exact realCharacterCoordinates_lattice b P.lattice (a i).val
    rw [he] at h
    exact h
  obtain ⟨c, hc⟩ := (P.coordinatePresentation b).corollary_6_2
    ((P.coordinate_deeplyMonotone_iff b).mpr hP) a' ha'
  refine ⟨c.map (characterCoordinates b).symm, ?_⟩
  intro i
  change (characterCoordinates b).symm (c i) = (a i).val
  rw [hc i]
  exact (characterCoordinates b).symm_apply_apply (a i).val

/-- Theorem 1.2, necessity, for a deeply monotone polytope in its original
arbitrary integral lattice. A basis is chosen from finite freeness inside
the proof; the conclusion uses the original primitive geometric normals. -/
theorem deeplyMonotone_normalMatroid_seriesParallel (hP : P.DeeplyMonotone) :
    SeriesParallel.GroundSeriesParallel P.normalMatroid := by
  let b := P.coordinateBasis
  have hcoordinate := SeriesParallel.deeplyMonotone_normalMatroid_seriesParallel
    (P.coordinatePresentation b) ((P.coordinate_deeplyMonotone_iff b).mpr hP)
  apply SeriesParallel.GroundSeriesParallel.of_mapEmbedding
    (characterCoordinates b).toEquiv.toEmbedding
  change SeriesParallel.GroundSeriesParallel
    (P.normalMatroid.mapEquiv (characterCoordinates b).toEquiv)
  rw [P.normalMatroid_coordinates_list b]
  exact hcoordinate

/-- Every actual deletion/contraction minor on the original dual-lattice
ground type belongs to the same ordinary series--parallel class. -/
theorem deeplyMonotone_normalMatroid_all_minors_seriesParallel
    (hP : P.DeeplyMonotone) {M : Matroid (N →+ ℤ)}
    (hM : M ≤m P.normalMatroid) : SeriesParallel.GroundSeriesParallel M :=
  (P.deeplyMonotone_normalMatroid_seriesParallel hP).minor hM

/-- The ordinary-minor conclusion also retains arbitrary original element
labels when an injective label map exhibits the minor in the normal matroid. -/
theorem deeplyMonotone_normalMatroid_minor_of_embedding (hP : P.DeeplyMonotone)
    {E : Type*} {M : Matroid E} (f : E ↪ (N →+ ℤ))
    (hM : M.mapEmbedding f ≤m P.normalMatroid) : SeriesParallel.GroundSeriesParallel M :=
  SeriesParallel.GroundSeriesParallel.of_mapEmbedding f
    (P.deeplyMonotone_normalMatroid_all_minors_seriesParallel hP hM)

/-- The positive-rank form of Theorem 1.2 on the original lattice. Both
conclusions concern the actual original primitive geometric normals. -/
theorem theorem_1_2_original_lattice (_hn : 1 ≤ n) (hP : P.DeeplyMonotone) :
    SeriesParallel.GroundSeriesParallel P.normalMatroid ∧
      ∀ M : Matroid (N →+ ℤ), M ≤m P.normalMatroid →
        SeriesParallel.GroundSeriesParallel M :=
  ⟨P.deeplyMonotone_normalMatroid_seriesParallel hP,
    fun _ hM => P.deeplyMonotone_normalMatroid_all_minors_seriesParallel hP hM⟩

/-- The same necessity result written with the exact original finite normal
list, whose equality with the geometric normal set has already been proved. -/
theorem deeplyMonotone_listedNormals_seriesParallel (hP : P.DeeplyMonotone) :
    SeriesParallel.GroundSeriesParallel
      (VectorMatroid.onSet (K := ℝ)
        (fun m : N →+ ℤ => P.lattice.realCharacter m) (P.normals : Set (N →+ ℤ))) := by
  have h := P.deeplyMonotone_normalMatroid_seriesParallel hP
  change SeriesParallel.GroundSeriesParallel
    (VectorMatroid.onSet (K := ℝ)
      (fun m : N →+ ℤ => P.lattice.realCharacter m) P.geometricFacetNormals) at h
  rwa [P.geometricFacetNormals_eq_normals] at h

end Unimodular.OriginalSmoothReflexivePresentation

#print axioms Unimodular.OriginalSmoothReflexivePresentation.coordinate_deeplyMonotone_iff
#print axioms Unimodular.OriginalSmoothReflexivePresentation.normalMatroid_coordinates
#print axioms Unimodular.OriginalSmoothReflexivePresentation.deeplyMonotone_normalMatroid_seriesParallel
#print axioms Unimodular.OriginalSmoothReflexivePresentation.deeplyMonotone_normalMatroid_all_minors_seriesParallel

#print axioms Unimodular.OriginalSmoothReflexivePresentation.deeplyMonotone_facetNormals_uniform
#print axioms Unimodular.OriginalSmoothReflexivePresentation.theorem_1_2_original_lattice
