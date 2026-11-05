module

public import PaperVerification.ToricSemigroupPolytopes
public import PaperVerification.ToricNormalChartOverlaps

@[expose] public section

/-!
# The actual normal fan retaining specified vertex character bases

The normal fan is constructed from any specified primitive edge bases at
the actual vertices. This retains exactly the bases recovered from the
smooth affine semigroup charts, so subsequent scheme identifications use
literal coordinate-ring equalities, without an unproved choice-of-basis
dictionary.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} (P : LatticePolytope n)

theorem exists_normal_fan_with_chosen_vertex_bases {J : Type*} [Fintype J]
    (v : J → Lattice n) (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : J → Fin n → ℕ)
    (hvertices : Set.range (fun j=>embed n (v j))=P.carrier.extremePoints ℝ)
    (hedges : ∀ j i,0<lengths j i ∧
      P.IsEdge (embed n (v j)) (embed n (v j+(lengths j i : ℤ) • b j i)))
    (horthant : ∀ j x,x∈P.carrier → ∀ i,
      0≤(integralBasisReal (b j)).repr (x-embed n (v j)) i) :
    ∃ «Σ» : SmoothCompleteFan n,
      «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      (∀ j,Finset.univ.image (integralDualBasis (b j))∈«Σ».cones) ∧
      (∀ t∈«Σ».cones,∃ j,t⊆Finset.univ.image (integralDualBasis (b j))) ∧
      (∀ j,P.normalCone (embed n (v j))=
        (latticeRayCone (Finset.univ.image (integralDualBasis (b j))) : Set (Ambient n))) := by
  let d : J → Module.Basis (Fin n) ℤ (Lattice n) := fun j=>integralDualBasis (b j)
  have hv (j : J) : embed n (v j)∈P.carrier :=
    ((hvertices ▸ Set.mem_range_self j) : embed n (v j)∈P.carrier.extremePoints ℝ).1
  have hnormal (j : J) : P.normalCone (embed n (v j))=
      (latticeRayCone (Finset.univ.image (d j)) : Set (Ambient n)) :=
    P.normalCone_eq_latticeRayCone (v j) (b j) (lengths j) (hedges j) (horthant j)
  have hinter (j l : J) :
      latticeRayCone (Finset.univ.image (d j)) ⊓
          latticeRayCone (Finset.univ.image (d l))=
        latticeRayCone ((Finset.univ.image (d j))∩(Finset.univ.image (d l))) :=
    P.normalCone_basis_common_rays (v j) (v l) (hv j) (hv l)
      (b j) (b l) (lengths j) (lengths l) (hedges j) (hedges l)
      (horthant j) (horthant l)
  have hcover (u : Ambient n) : ∃ j,u∈latticeRayCone (Finset.univ.image (d j)) := by
    let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
    obtain ⟨x,hx,hmin⟩ := P.exists_minimizing_vertex f
    obtain ⟨j,rfl⟩ := hvertices.symm ▸ hx
    refine ⟨j,?_⟩
    change u∈(latticeRayCone (Finset.univ.image (d j)) : Set (Ambient n))
    rw [← hnormal j]
    intro y hy
    change 0≤f (y-embed n (v j))
    rw [map_sub]
    exact sub_nonneg.mpr (hmin y hy)
  let «Σ» := fanOfBasisFamily d hinter hcover
  have hs (j : J) : Finset.univ.image (d j)∈«Σ».cones :=
    (mem_basisFamilyCones d _).mpr ⟨j,Finset.Subset.refl _⟩
  refine ⟨«Σ»,?_,fanOfBasisFamily_isPure d hinter hcover,hs,
    fun t ht=>(mem_basisFamilyCones d t).mp ht,hnormal⟩
  ext C
  constructor
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨j,hj⟩ := (mem_basisFamilyCones d s).mp hs
    let I := basisRayIndices (d j) s
    have hI : I.image (d j)=s := image_basisRayIndices (d j) s hj
    have h := P.subbasis_mem_normalFan (v j) (hv j) (b j) (lengths j)
      (hedges j) (horthant j) I
    change (latticeRayCone (I.image (d j)) : Set (Ambient n))∈P.normalFan at h
    simpa only [hI] using h
  · rintro ⟨x,hx,rfl⟩
    have hhull : x∈convexHull ℝ (Set.range (fun j=>embed n (v j))) := by
      rw [hvertices,P.hull_vertices]
      exact hx
    obtain ⟨p,hp,hpsum,hpm⟩ :=
      PaperVerification.Toric.exists_probability_of_mem_convexHull_range
        (fun j=>embed n (v j)) hhull
    let K := Finset.univ.filter (fun j : J=>0<p j)
    have hK : K.Nonempty := by
      have hpos : 0<∑ j,p j := by rw [hpsum];norm_num
      obtain ⟨j,hj,hpj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _=>hp j)).mp hpos
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hpj⟩⟩
    obtain ⟨s,hs',hspec⟩ := «Σ».exists_cone_finite_intersection K
      (fun j=>Finset.univ.image (d j)) hK (fun j hj=>hs j)
    refine ⟨s,hs',?_⟩
    ext u
    rw [← hpm,P.mem_normalCone_convex_average (fun j=>embed n (v j)) p hv hp hpsum u]
    change (∀ i,0<p i → u∈P.normalCone (embed n (v i))) ↔ u∈latticeRayCone s
    rw [hspec u]
    simp only [hnormal,K,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Iff.rfl

end PaperVerification.ToricGeometry.LatticePolytope

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

set_option maxHeartbeats 2000000 in
/-- Reconstruction retaining the actual affine-chart semigroups and the
literal vertex normal cones required for scheme gluing. -/
theorem exists_polytope_fan_of_vertex_semigroups {ι : Type*}
    [Fintype ι] [Nonempty ι] {n : ℕ} (a : ι → Lattice n)
    (hlocal : ∀ j : vertexWeightIndices a,
      ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
        differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ) :
    ∃ (P : LatticePolytope n) («Σ» : SmoothCompleteFan n)
      (s : vertexWeightIndices a → Finset (Lattice n)),
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth ∧
      «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      (∀ j,s j∈«Σ».cones) ∧ (∀ t∈«Σ».cones,∃ j,t⊆s j) ∧
      (∀ j,dualConeMonoid (s j)=differenceWeightMonoid a j.val) ∧
      (∀ j,P.normalCone (embed n (a j.val))=(latticeRayCone (s j) : Set (Ambient n))) := by
  obtain ⟨P,hP,hPs⟩ := exists_smooth_polytope_of_vertex_semigroups a hlocal
  choose b hb using hlocal
  have hvertices : Set.range (fun j : vertexWeightIndices a=>embed n (a j.val))=
      P.carrier.extremePoints ℝ := by rw [hP];exact range_vertexWeightIndices a
  have horthant (j : vertexWeightIndices a) (x : Ambient n) (hx : x∈P.carrier) :
      ∀ i,0≤(integralBasisReal (b j)).repr (x-embed n (a j.val)) i :=
    hull_orthant_of_difference_basis a j.val (b j) (hb j) x (hP ▸ hx)
  have hv (j : vertexWeightIndices a) : a j.val∈P.generators := by
    have hex : embed n (a j.val)∈P.carrier.extremePoints ℝ :=
      hvertices ▸ Set.mem_range_self j
    obtain ⟨z,hz,he⟩ := P.extreme_integral hex
    exact (embed_injective n he) ▸ hz
  have haxis (j : vertexWeightIndices a) (i : Fin n) :
      ∃ ε : ℝ,0<ε ∧ embed n (a j.val)+ε • integralBasisReal (b j) i∈P.carrier := by
    have hbi : b j i∈differenceWeightMonoid a j.val := by
      rw [hb j]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num
    simpa only [hP,integralBasisReal_apply] using
      positive_axis_point_of_differenceMonoid a j.val (b j i) hbi ((b j).ne_zero i)
  choose lengths hlengths using fun j i=>P.coordinateRayFace_eq_integral_edge
    (a j.val) (hv j) (b j) (horthant j) i (haxis j i)
  have hedges (j : vertexWeightIndices a) (i : Fin n) :
      0<lengths j i ∧ P.IsEdge (embed n (a j.val))
        (embed n (a j.val+(lengths j i : ℤ) • b j i)) :=
    ⟨(hlengths j i).1,(hlengths j i).2.1⟩
  obtain ⟨«Σ»,«hΣ»,hpure,hs,hcover,hnormal⟩ := P.exists_normal_fan_with_chosen_vertex_bases
    (fun j : vertexWeightIndices a=>a j.val) b lengths hvertices hedges horthant
  refine ⟨P,«Σ»,fun j=>Finset.univ.image (integralDualBasis (b j)),
    hP,hPs,«hΣ»,hpure,hs,hcover,?_,hnormal⟩
  intro j
  rw [dualConeMonoid_basis_eq,integralDualBasis_involutive,← hb j]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.exists_polytope_fan_of_vertex_semigroups
