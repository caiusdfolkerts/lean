import differential_geometry.topology.piecewise_linear.general_position
import differential_geometry.topology.piecewise_linear.manifold_connectivity
import differential_geometry.topology.simplicial_complex.edge_graph
import cubical.indexed_pseudomanifold
import cubical.simplicial_ridge_count
import cubical.fogelsanger

/-!
# Genuine finite simplicial PL spheres are generically rigid

Here `IsPLSphere` means a piecewise affine homeomorphism, with piecewise
affine inverse, from the ordinary boundary of a standard simplex. Its
links, purity and dual connectivity are proved geometric theorems.
Those theorems give an actual minimal simplicial cycle over `𝔽₂`, to
which the independently proved Fogelsanger theorem applies.
-/

noncomputable section

namespace Cubical.PL

open Set Cubical.Simplicial
open DifferentialGeometry.Topology.PiecewiseLinear
attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- All top-dimensional geometric simplices, with their original
geometric vertex sets. -/
abbrev TopFacet (K : Geometry.SimplicialComplex ℝ E) (d : ℕ) :=
  {s : Finset E // s ∈ K.faces ∧ s.card = d + 1}

instance topFacetFinite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (d : ℕ) :
    Finite (TopFacet K d) :=
  ((Set.toFinite K.faces).subset (fun _ h => h.1)).to_subtype

noncomputable instance topFacetFintype (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (d : ℕ) : Fintype (TopFacet K d) := Fintype.ofFinite _

/-- The geometric dimension bound identifies codimension-one links
with their two coface vertices. -/
theorem sphere_ridge_cofaces (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsPLSphere (n + 1) K.space) {r : Finset E}
    (hr : r ∈ K.faces) (hcard : r.card = n + 1) :
    ∃ a b, a ≠ b ∧ {w | w ∉ r ∧ insert w r ∈ K.faces} = {a, b} := by
  classical
  have hlink := isPLSphere_geometricLink_faces_of_isPLSphere K hK hr hcard (le_refl n)
  rw [Nat.sub_self] at hlink
  have hbound : ∀ u ∈ K.faces, r ⊆ u → u.card ≤ r.card + 1 := by
    intro u hu _
    rw [hcard]
    exact card_le_of_isPLSphere K hK hu
  rw [geometricLink_space_eq_coface_vertices_of_card_le K r hbound] at hlink
  exact isPLSphere_zero_iff.mp hlink

/-- Exactly two top simplices meet every ridge of a finite PL sphere. -/
theorem sphere_ridgePairing (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsPLSphere (n + 1) K.space) :
    RidgePairing (fun f : TopFacet K (n + 1) => f.val) := by
  classical
  intro i r hri
  have hrc : r.card = n + 1 := by
    have h := simplexBoundary_card hri
    change r.card + 1 = i.val.card at h
    have hc := i.property.2
    omega
  have hrK : r ∈ K.faces := K.down_closed i.property.1 (simplexBoundary_subset hri)
    (Finset.card_pos.mp (by omega))
  obtain ⟨a, b, hab, hcofaces⟩ := sphere_ridge_cofaces K hK hrK hrc
  have ha : a ∉ r ∧ insert a r ∈ K.faces := by
    have : a ∈ ({w | w ∉ r ∧ insert w r ∈ K.faces} : Set E) := by
      rw [hcofaces]
      exact Set.mem_insert _ _
    exact this
  have hb : b ∉ r ∧ insert b r ∈ K.faces := by
    have : b ∈ ({w | w ∉ r ∧ insert w r ∈ K.faces} : Set E) := by
      rw [hcofaces]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact this
  let fa : TopFacet K (n + 1) := ⟨insert a r, ha.2, by rw [Finset.card_insert_of_notMem ha.1, hrc]⟩
  let fb : TopFacet K (n + 1) := ⟨insert b r, hb.2, by rw [Finset.card_insert_of_notMem hb.1, hrc]⟩
  have hfab : fa ≠ fb := by
    intro heq
    have heq' : insert a r = insert b r := congrArg Subtype.val heq
    have hm : a ∈ insert b r := by rw [← heq']; simp
    exact (Finset.mem_insert.mp hm).elim hab ha.1
  have hocc : ∀ k : TopFacet K (n + 1),
      r ∈ Cubical.Simplicial.simplexBoundary k.val ↔ k = fa ∨ k = fb := by
    intro k
    constructor
    · intro hrk
      obtain ⟨w, hw, hwr⟩ := Finset.mem_image.mp hrk
      have hwr' : insert w r = k.val := by rw [← hwr, Finset.insert_erase hw]
      have hwm : w ∈ ({x | x ∉ r ∧ insert x r ∈ K.faces} : Set E) :=
        ⟨by rw [← hwr]; exact Finset.notMem_erase _ _, hwr'.symm ▸ k.property.1⟩
      rw [hcofaces] at hwm
      rcases hwm with hwa | hwb
      · exact Or.inl (Subtype.ext (hwr'.symm.trans (by rw [hwa])))
      · exact Or.inr (Subtype.ext (hwr'.symm.trans (by rw [hwb])))
    · rintro (rfl | rfl)
      · exact mem_simplexBoundary_iff.mpr ⟨Finset.subset_insert _ _, by
          change r.card + 1 = (insert a r).card
          rw [Finset.card_insert_of_notMem ha.1]⟩
      · exact mem_simplexBoundary_iff.mpr ⟨Finset.subset_insert _ _, by
          change r.card + 1 = (insert b r).card
          rw [Finset.card_insert_of_notMem hb.1]⟩
  rcases (hocc i).mp hri with rfl | rfl
  · exact ⟨fb, hfab, hocc⟩
  · exact ⟨fa, hfab.symm, fun k => (hocc k).trans or_comm⟩

/-- The combinatorial ridge graph is the geometric dual graph. -/
theorem indexedFacetGraph_eq_dualGraph (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (n : ℕ) :
    indexedFacetGraph (fun f : TopFacet K (n + 1) => f.val) = dualGraph (n + 1) K := by
  classical
  ext f g
  change (f ≠ g ∧ ∃ r, r ∈ Cubical.Simplicial.simplexBoundary f.val ∧
    r ∈ Cubical.Simplicial.simplexBoundary g.val) ↔
    f ≠ g ∧ ∃ r ∈ K.faces, r.card = n + 1 ∧ r ⊆ f.val ∧ r ⊆ g.val
  constructor
  · rintro ⟨hfg, r, hrf, hrg⟩
    have hc : r.card = n + 1 := by
      have := simplexBoundary_card hrf
      have := f.property.2
      omega
    exact ⟨hfg, r, K.down_closed f.property.1 (simplexBoundary_subset hrf)
      (Finset.card_pos.mp (by omega)), hc, simplexBoundary_subset hrf,
      simplexBoundary_subset hrg⟩
  · rintro ⟨hfg, r, _, hc, hrf, hrg⟩
    exact ⟨hfg, r,
      mem_simplexBoundary_iff.mpr ⟨hrf, by rw [hc, f.property.2]⟩,
      mem_simplexBoundary_iff.mpr ⟨hrg, by rw [hc, g.property.2]⟩⟩

/-- Every finite geometric triangulation of a genuine PL sphere has
connected top-dimensional ridge adjacency. -/
theorem sphere_indexedFacetGraph_connected (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {n : ℕ} (hK : IsPLSphere (n + 1) K.space) :
    (indexedFacetGraph (fun f : TopFacet K (n + 1) => f.val)).Connected := by
  classical
  rw [indexedFacetGraph_eq_dualGraph]
  obtain ⟨x, hx⟩ := hK.nonempty
  obtain ⟨r, hr, _⟩ := K.mem_space_iff.mp hx
  obtain ⟨s, hs, _, hsc⟩ := exists_face_superset_card_eq_of_isPLSphere K hK hr
  letI : Nonempty (TopFacet K (n + 1)) := ⟨⟨s, hs, hsc⟩⟩
  exact ⟨hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary.dualGraph_preconnected
    hK.isConnected.isPreconnected⟩

/-- A finite triangulation of a PL sphere is a genuine minimal
augmented simplicial cycle over `𝔽₂`. -/
theorem sphere_facetCircuit (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsPLSphere (n + 1) K.space) :
    IsFacetCircuit (fun f : TopFacet K (n + 1) => f.val) Finset.univ := by
  classical
  exact facetCircuit_of_ridgePairing_connected (sphere_ridgePairing K hK)
    (sphere_indexedFacetGraph_connected K hK)

/-- **Generic rigidity of finite simplicial PL spheres.** The only
topological hypothesis is an actual piecewise affine homeomorphism from
the standard sphere. The spatial dimension is one greater than the
sphere dimension, in the full range at least three. -/
theorem sphere_genericallyRigid (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hn : 1 ≤ n) (hK : IsPLSphere (n + 1) K.space) :
    Cubical.Rigidity.GenericallyRigid
      (supportGraph (fun f : TopFacet K (n + 1) => f.val) Finset.univ)
      (EuclideanSpace ℝ (Fin (n + 2))) := by
  classical
  apply (sphere_facetCircuit K hK).genericallyRigid (by omega)
    (fun f _ => f.property.2)
  simp

/-- Every original geometric vertex lies in a top-dimensional simplex,
and the finite family introduces no additional vertices. -/
theorem mem_sphere_vertices_iff (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsPLSphere (n + 1) K.space) (v : E) :
    v ∈ vertices (fun f : TopFacet K (n + 1) => f.val) Finset.univ ↔ v ∈ K.vertices := by
  classical
  constructor
  · intro hv
    obtain ⟨f, _, hvf⟩ := (mem_vertices _ _ v).mp hv
    exact K.down_closed f.property.1 (Finset.singleton_subset_iff.mpr hvf)
      (Finset.singleton_nonempty v)
  · intro hv
    obtain ⟨s, hs, hvs, hsc⟩ := exists_face_superset_card_eq_of_isPLSphere K hK hv
    exact (mem_vertices _ _ v).mpr ⟨⟨s, hs, hsc⟩, Finset.mem_univ _,
      hvs (Finset.mem_singleton_self v)⟩

/-- The support graph of the minimal circuit is exactly the original
geometric edge graph of the triangulation. -/
def sphereEdgeGraphIso (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hK : IsPLSphere (n + 1) K.space) :
    supportGraph (fun f : TopFacet K (n + 1) => f.val) Finset.univ ≃g
      DifferentialGeometry.Topology.SimplicialComplex.edgeGraph K where
  toEquiv := Equiv.subtypeEquivRight (mem_sphere_vertices_iff K hK)
  map_rel_iff' := by
    intro a b
    change ((⟨a.val, _⟩ : K.vertices) ≠ ⟨b.val, _⟩ ∧ {a.val, b.val} ∈ K.faces) ↔
      a.val ≠ b.val ∧ ∃ f : TopFacet K (n + 1), f ∈ Finset.univ ∧
        a.val ∈ f.val ∧ b.val ∈ f.val
    constructor
    · rintro ⟨hne, hab⟩
      obtain ⟨s, hs, hsub, hsc⟩ := exists_face_superset_card_eq_of_isPLSphere K hK hab
      exact ⟨fun h => hne (Subtype.ext h), ⟨s, hs, hsc⟩, Finset.mem_univ _,
        hsub (Finset.mem_insert_self _ _), hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
    · rintro ⟨hne, f, _, haf, hbf⟩
      exact ⟨fun h => hne (congrArg (fun v : K.vertices => v.val) h),
        K.down_closed f.property.1
          (Finset.insert_subset_iff.mpr ⟨haf, Finset.singleton_subset_iff.mpr hbf⟩) (by simp)⟩

/-- Generic rigidity of the genuine geometric graph of a finite
simplicial PL sphere of dimension at least two. -/
theorem sphere_edgeGraph_genericallyRigid (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {n : ℕ} (hn : 1 ≤ n) (hK : IsPLSphere (n + 1) K.space) :
    Cubical.Rigidity.GenericallyRigid
      (DifferentialGeometry.Topology.SimplicialComplex.edgeGraph K)
      (EuclideanSpace ℝ (Fin (n + 2))) :=
  (sphere_genericallyRigid K hn hK).of_iso (sphereEdgeGraphIso K hK)

end Cubical.PL
