module

public import Continuation.CycleBounds.FanStrata
public import Continuation.SeriesParallel.All

@[expose] public section

/-!
# The fan-scheme consequence of Corollary 6.9

The conclusion is for the genuine glued scheme of the supplied fan. A separate
classification of an independently supplied abstract toric variety is not
assumed here. The original fan need not be identified in advance with the normal
fan of the polytope. Its ray inequalities define the reflected anticanonical polytope.
Terminality of the uniformly unimodular normal hull then proves that every ray
is one of the polytope's facet normals. Restriction preserves the series-parallel
matroid conclusion, so the full all-curves bound applies to the original fan.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matroid
open Set

namespace Unimodular.CycleBounds
open SeriesParallel
attribute [local instance] Classical.propDecidable

/-- The integral incidence embedding associated with an actual lattice basis. -/
def basisIncidenceMap {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Lattice n →ₗ[ℤ] (Option (Fin n) → ℤ) :=
  b.constr ℤ (fun i ↦ Pi.single (some i) 1 - Pi.single none 1)

theorem basisIncidenceMap_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (i : Fin n) : basisIncidenceMap b (b i) = Pi.single (some i) 1 - Pi.single none 1 :=
  b.constr_basis ℤ _ i

theorem basisIncidenceMap_vertex {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (p : Option (Fin n)) :
    basisIncidenceMap b (basisVertex b p) = Pi.single p 1 - Pi.single none 1 := by
  cases p with
  | none => simp [basisVertex]
  | some i => exact basisIncidenceMap_basis b i

theorem basisIncidenceMap_coordinate {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (x : Lattice n) (j : Fin n) : basisIncidenceMap b x (some j) = b.repr x j := by
  conv_lhs => rw [← b.sum_repr x, map_sum]
  simp only [map_smul, basisIncidenceMap_basis, Finset.sum_apply, Pi.smul_apply,
    Pi.sub_apply, Pi.single_apply, Option.some.injEq, Option.some_ne_none,
    if_false, sub_zero, smul_eq_mul]
  simp

theorem basisIncidenceMap_injective {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) : Function.Injective (basisIncidenceMap b) := by
  intro x y h
  apply b.repr.injective
  ext j
  simpa only [basisIncidenceMap_coordinate] using congrFun h (some j)

/-- Every original ray belongs to the exact normal set of a deeply monotone
anticanonical polytope. This discharges possible redundant-ray concerns. -/
theorem rays_subset_deeplyMonotone_normals {n : ℕ}
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (P : SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    (hcarrier : P.carrier = {x : Ambient n | ∀ u ∈ F.rays, pairing x u ≤ 1}) :
    (F.rays : Set (Lattice n)) ⊆ P.normals := by
  classical
  let U : Set (Lattice n) := insert 0 (P.normals : Set (Lattice n))
  have hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U ↦ u.val) := by
    apply (uniform_iff_real_independent_is_basis (fun u : U ↦ u.val)).mpr
    intro a ha
    have hi (i : Fin n) : (a i).val ∈ P.normals := by
      rcases (a i).property with hz | hn
      · exfalso
        exact ha.ne_zero i (by simp [hz, embed])
      · exact hn
    let a' : Fin n → {u // u ∈ P.normals} := fun i ↦ ⟨(a i).val, hi i⟩
    exact P.deeplyMonotone_facetNormals_uniform hP a' ha
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  let b := P.basis ⟨v, hv⟩
  have hspan : Submodule.span ℝ (embed '' U) = ⊤ := by
    apply top_unique
    intro x _
    rw [← sum_basis_realCoordinates b x]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨b i, Set.mem_insert_of_mem _ (P.basis_mem ⟨v, hv⟩ i), rfl⟩)
  intro u hu
  have hpolar : embed u ∈ realPolar P.carrier := by
    intro x hx
    change pairing x u ≤ 1
    rw [hcarrier] at hx
    exact hx u hu
  rw [P.realPolar_eq_convexHull_normals] at hpolar
  have hpolar' : embed u ∈ convexHull ℝ (embed '' U) := hpolar
  rcases LatticeHull.latticePoint_convexHull_eq_zero_or_mem U hU hspan u hpolar' with hz | hm
  · exact False.elim (F.ray_ne_zero hu hz)
  · rcases hm with hz | hm
    · exact False.elim (F.ray_ne_zero hu hz)
    · exact hm

/-- The all-ray integral incidence and literal no-K4 conclusion for the original
fan, obtained from the actual deeply monotone anticanonical polytope. -/
theorem anticanonical_integral_incidence_no_K4 {n : ℕ}
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (P : SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    (hcarrier : P.carrier = {x : Ambient n | ∀ u ∈ F.rays, pairing x u ≤ 1}) :
    ∃ (G : IncidenceGraph (Option (Fin n)) F.rays), G.edges = Set.univ ∧
      ¬G.HasK4Minor ∧ ∃ δ : Lattice n →ₗ[ℤ] (Option (Fin n) → ℤ),
        Function.Injective δ ∧ ∀ u : F.rays,
          δ u.val = Pi.single (G.source u) 1 - Pi.single (G.target u) 1 := by
  classical
  have hsub := rays_subset_deeplyMonotone_normals F P hP hcarrier
  obtain ⟨b, s, t, hvec, _⟩ := deeplyMonotone_integrally_graphic_no_K4 P hP
  let f : F.rays → {u // u ∈ P.normals} := fun u ↦ ⟨u.val, hsub u.property⟩
  let G : IncidenceGraph (Option (Fin n)) F.rays :=
    IncidenceGraph.ofIncidence (s ∘ f) (t ∘ f)
  let δ := basisIncidenceMap b
  have hδ (u : F.rays) : δ u.val = Pi.single (G.source u) 1 - Pi.single (G.target u) 1 := by
    rw [show u.val = basisVertex b (s (f u)) - basisVertex b (t (f u)) from hvec (f u),
      map_sub, basisIncidenceMap_vertex, basisIncidenceMap_vertex]
    change (Pi.single (s (f u)) 1 - Pi.single none 1) -
      (Pi.single (t (f u)) 1 - Pi.single none 1) = _
    abel
  have hSP : GroundSeriesParallel (VectorMatroid.ofFamily (K := ℝ)
      (fun u : F.rays ↦ embed u.val)) := by
    let j : F.rays ↪ Lattice n := ⟨Subtype.val, Subtype.val_injective⟩
    apply GroundSeriesParallel.of_mapEmbedding j
    have heq := VectorMatroid.ofFamily_mapEmbedding_eq_onSet (K := ℝ)
      (fun u : F.rays ↦ embed u.val) embed j (fun _ ↦ rfl)
    have hr : Set.range j = (F.rays : Set (Lattice n)) := by ext u; simp [j]
    rw [heq, hr]
    apply deeplyMonotone_normalMatroid_all_minors_seriesParallel P hP
    refine ⟨∅, (P.normals : Set (Lattice n)) \ (F.rays : Set (Lattice n)), ?_⟩
    rw [Matroid.contract_empty, VectorMatroid.delete_onSet, Set.sdiff_sdiff_cancel_left hsub]
  have hcol : G.column = realExtension δ ∘ (fun u : F.rays ↦ embed u.val) := by
    funext u
    rw [Function.comp_apply]
    change _ = realExtension δ (fun i ↦ (u.val i : ℝ))
    rw [realExtension_intCast, hδ]
    ext a
    simp [IncidenceGraph.column, IncidenceGraph.vertex, Pi.single_apply] <;>
      split_ifs <;> norm_num
  have hmatroid : G.cycleMatroid = VectorMatroid.ofFamily (K := ℝ)
      (fun u : F.rays ↦ embed u.val) := by
    change VectorMatroid.ofFamily (K := ℝ) G.column = _
    rw [hcol]
    exact VectorMatroid.ofFamily_comp_injective _ (realExtension δ)
      (realExtension_injective δ (basisIncidenceMap_injective b))
  refine ⟨G, rfl, ?_, δ, basisIncidenceMap_injective b, hδ⟩
  apply IncidenceGraph.no_K4_minor_of_seriesParallel
  rwa [hmatroid]

end Unimodular.CycleBounds
