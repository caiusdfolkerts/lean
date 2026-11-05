module

public import PaperVerification.ToricMonomialFanIso
public import PaperVerification.ToricIntrinsicAffineCharts
public import PaperVerification.ToricFanAction

@[expose] public section

/-!
# Ordinary smoothness reconstructs the actual fan of a monomial Proj

Smoothness is the ordinary scheme-morphism predicate over the field.
The torus is required to be the actual open character torus. These
geometric conditions imply the unimodular semigroup charts used in the
preceding construction, and hence yield an actual scheme isomorphism
over the original field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open scoped Classical

variable {ι : Type*} {n : ℕ} (a : ι → Lattice n) (k : Type u) [Field k]

/-- The canonical structure map of the genuine monomial Proj. -/
def monomialProjectiveToSpec :
    monomialProjectiveScheme a k⟶Spec (CommRingCat.of k) :=
  Proj.toSpecZero (homogeneousWeightGrading a k)≫
    Spec.map (CommRingCat.ofHom (homogeneousWeightZeroMap a k))

set_option maxHeartbeats 2000000 in
theorem monomialCoordinateChartMap_toSpec (j : ι) :
    monomialCoordinateChartMap a k j≫monomialProjectiveToSpec a k=
      Spec.map (CommRingCat.ofHom
        (algebraMap k (monoidChartAlgebra k (differenceWeightMonoid a j)))) := by
  unfold monomialCoordinateChartMap monomialProjectiveToSpec
  erw [Category.assoc,← Category.assoc (Proj.awayι _ _ _ _),Proj.awayι_toSpecZero,
    ← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (homogeneousWeightChartEquiv a k j).commutes r

set_option maxHeartbeats 2000000 in
theorem monomialTorusChart_toSpec (j : ι) :
    monomialTorusChart a k j≫monomialProjectiveToSpec a k=
      Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Lattice n)))) := by
  erw [← monomialCoordinateChartMap_torus a k j,Category.assoc,
    monomialCoordinateChartMap_toSpec a k j,← Spec.map_comp]
  congr 1

instance monomialProjective_isOver :
    (monomialProjectiveScheme a k).Over (Spec (CommRingCat.of k)) where
  hom := monomialProjectiveToSpec a k

instance monomialCoordinateChartMap_isOver (j : ι) :
    (monomialCoordinateChartMap a k j).IsOver (Spec (CommRingCat.of k)) where
  comp_over := monomialCoordinateChartMap_toSpec a k j

theorem monomialCoordinateChart_smooth
    [Smooth (monomialProjectiveToSpec a k)] (j : ι) :
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap k (monoidChartAlgebra k (differenceWeightMonoid a j))))) := by
  letI : IsOpenImmersion (monomialCoordinateChartMap a k j) :=
    monomialCoordinateChartMap_isOpenImmersion a k j
  have h : Smooth (monomialCoordinateChartMap a k j≫monomialProjectiveToSpec a k) :=
    inferInstance
  exact (monomialCoordinateChartMap_toSpec a k j) ▸ h

theorem monomialCoordinateChart_torus_isOpenImmersion (j₀ j : ι)
    [IsOpenImmersion (monomialTorusChart a k j₀)] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (monoidChartAlgebra k (differenceWeightMonoid a j)).val.toRingHom)) := by
  haveI : IsOpenImmersion (monomialTorusChart a k j) := by
    rw [monomialTorusChart_independent a k j j₀]
    infer_instance
  let f := Spec.map (CommRingCat.ofHom
    (monoidChartAlgebra k (differenceWeightMonoid a j)).val.toRingHom)
  letI : IsOpenImmersion (monomialCoordinateChartMap a k j) :=
    monomialCoordinateChartMap_isOpenImmersion a k j
  haveI : IsOpenImmersion (f≫monomialCoordinateChartMap a k j) :=
    (monomialCoordinateChartMap_torus a k j).symm ▸
      (inferInstance : IsOpenImmersion (monomialTorusChart a k j))
  exact IsOpenImmersion.of_comp f (monomialCoordinateChartMap a k j)

theorem smooth_monomial_vertex_semigroup [Fintype ι]
    [Smooth (monomialProjectiveToSpec a k)] (j₀ : ι)
    [IsOpenImmersion (monomialTorusChart a k j₀)]
    (j : vertexWeightIndices a) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ := by
  letI := monomialCoordinateChart_smooth a k j.val
  letI := monomialCoordinateChart_torus_isOpenImmersion a k j₀ j.val
  exact pointed_semigroup_basis_of_smooth_open_torus k (differenceWeightMonoid a j.val)
    (differenceWeightMonoid_pointed_at_vertex a j.val (Finset.mem_filter.mp j.property).2)

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}
    («Σ» : SmoothCompleteFan n) (P : LatticePolytope n)
    (a : ι → Lattice n) (k : Type u) [Field k]
    (s : vertexWeightIndices a → Finset (Lattice n))
    (hdual : ∀ j,dualConeMonoid (s j)=differenceWeightMonoid a j.val)

set_option maxHeartbeats 2000000 in
theorem monomialFanChart_toSpec (j : vertexWeightIndices a) :
    monomialFanChart a k s hdual j≫monomialProjectiveToSpec a k=
      Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k (dualConeMonoid (s j))))) := by
  erw [monomialFanChart,Category.assoc,monomialCoordinateChartMap_toSpec a k j.val]
  exact monoidChartEqIso_toSpec k (hdual j)

theorem monomialNormalFanIso_toSpec
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) :
    («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom≫
        monomialProjectiveToSpec a k=«Σ».fanSchemeStructureMap k := by
  apply colimit.hom_ext
  intro t
  change «Σ».fanChartMap k t≫_ = «Σ».fanChartMap k t≫_
  have hbase : «Σ».fanChartMap k t ≫ «Σ».fanSchemeStructureMap k =
      coneChart k t.val ↘ Spec (CommRingCat.of k) :=
    comp_over («Σ».fanChartMap k t) (Spec (CommRingCat.of k))
  rw [hbase]
  obtain ⟨j,htj⟩ := hcover t.val t.property
  have hchart : «Σ».fanChartMap k ⟨s j,hs j⟩≫
      («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom≫
        monomialProjectiveToSpec a k=coneChart k (s j) ↘ Spec (CommRingCat.of k) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f : coneChart k (s j)⟶monomialProjectiveScheme a k =>
        f≫monomialProjectiveToSpec a k)
          («Σ».monomialNormalFanIso_chart P a k s hdual hs hcover hv hnormal j)).trans
        (monomialFanChart_toSpec a k s hdual j))
  rw [← «Σ».fanChartMap_naturality k (s := t) (t := ⟨s j,hs j⟩) htj,
    Category.assoc,hchart]
  exact comp_over (coneChartFaceMap k htj) (Spec (CommRingCat.of k))

end PaperVerification.ToricGeometry.SmoothCompleteFan

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

/-- Faithful reconstruction for an ordinary smooth monomial projective
scheme with its actual open character torus. -/
theorem exists_smooth_normal_fan_of_monomial_projective {ι : Type*}
    [Fintype ι] {n : ℕ} (a : ι → Lattice n) (k : Type u) [Field k]
    [Smooth (monomialProjectiveToSpec a k)] (j₀ : ι)
    [IsOpenImmersion (monomialTorusChart a k j₀)] :
    ∃ (P : LatticePolytope n) («Σ» : SmoothCompleteFan n)
      (e : «Σ».fanScheme k≅monomialProjectiveScheme a k),
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth ∧
      «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      e.hom≫monomialProjectiveToSpec a k=«Σ».fanSchemeStructureMap k ∧
      (∀ j : ι,«Σ».splitTorusOpenMap k≫e.hom=monomialTorusChart a k j) := by
  letI : Nonempty ι := ⟨j₀⟩
  have hlocal := smooth_monomial_vertex_semigroup a k j₀
  obtain ⟨P,«Σ»,s,hP,hPs,«hΣ»,hpure,hs,hcover,hdual,hnormal⟩ :=
    exists_polytope_fan_of_vertex_semigroups a hlocal
  have hv (j : vertexWeightIndices a) : embed n (a j.val)∈P.carrier := by
    rw [hP]
    exact subset_convexHull ℝ _ (Set.mem_range_self j.val)
  let e := «Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal
  refine ⟨P,«Σ»,e,hP,hPs,«hΣ»,hpure,
    «Σ».monomialNormalFanIso_toSpec P a k s hdual hs hcover hv hnormal,?_⟩
  intro j
  obtain ⟨i,hi⟩ := hcover ∅ «Σ».empty_mem
  rw [«Σ».monomialNormalFanIso_torus P a k s hdual hs hcover hv hnormal i,
    monomialTorusChart_independent a k i.val j]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.exists_smooth_normal_fan_of_monomial_projective
