module

public import PaperVerification.ToricChosenVertexFans
public import PaperVerification.ToricFanSchemeChartIso
public import PaperVerification.ToricProjectiveMonomialMaps
public import PaperVerification.ToricFanCharacters

@[expose] public section

/-!
# The genuine monomial Proj is the scheme of its recovered normal fan

The affine coordinate rings, open immersions, torus restrictions, and
common-face overlaps are identified explicitly. The conclusion is an
isomorphism of actual schemes, obtained from their actual affine charts.
No fan presentation is included in the hypotheses on the monomial Proj.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory
open scoped Classical

section IndependentUniverses

variable (k : Type u) [CommRing k] {G : Type*} [AddCommGroup G]

def monoidChartEqIso {S T : AddSubmonoid G} (h : S=T) :
    monoidChartScheme k S≅monoidChartScheme k T :=
  eqToIso (congrArg (monoidChartScheme k) h)

theorem monoidChartEqIso_torus {S T : AddSubmonoid G} (h : S=T) :
    Spec.map (CommRingCat.ofHom (monoidChartAlgebra k S).val.toRingHom)≫
        (monoidChartEqIso k h).hom=
      Spec.map (CommRingCat.ofHom (monoidChartAlgebra k T).val.toRingHom) := by
  subst T
  exact Category.comp_id _

theorem monoidChartEqIso_preimage_character {S T : AddSubmonoid G} (h : S=T)
    (z : G) (hzS : z∈S) (hzT : z∈T) :
    (monoidChartEqIso k h).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (chartCharacter k T z hzT)=
      PrimeSpectrum.basicOpen (chartCharacter k S z hzS) := by
  subst T
  rfl

end IndependentUniverses

section ToSpec

variable (k : Type (max u v)) [CommRing k] {G : Type v} [AddCommGroup G]

theorem monoidChartEqIso_toSpec {S T : AddSubmonoid G} (h : S=T) :
    (monoidChartEqIso k h).hom≫
        Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k T)))=
      Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k S))) := by
  subst T
  exact Category.id_comp _

end ToSpec

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} (k : Type u) [CommRing k]

theorem coneChart_zeroFace_eq_torus (s : Finset (Lattice n)) :
    coneChartFaceMap k (Finset.empty_subset s)=
      (zeroConeChartIso k n).hom≫
        Spec.map (CommRingCat.ofHom (monoidChartAlgebra k (dualConeMonoid s)).val.toRingHom) := by
  change Spec.map _=Spec.map _≫Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  apply Subtype.ext
  change (f : AddMonoidAlgebra k (Lattice n))=
    zeroConeChartAlgEquiv k n
      ((zeroConeChartAlgEquiv k n).symm (f : AddMonoidAlgebra k (Lattice n)))
  exact ((zeroConeChartAlgEquiv k n).apply_symm_apply
    (f : AddMonoidAlgebra k (Lattice n))).symm

end PaperVerification.ToricGeometry

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}
    («Σ» : SmoothCompleteFan n) (P : LatticePolytope n)
    (a : ι → Lattice n) (k : Type u) [Field k]
    (s : vertexWeightIndices a → Finset (Lattice n))
    (hdual : ∀ j,dualConeMonoid (s j)=differenceWeightMonoid a j.val)

local instance monomialNormalFan_target_isSeparated :
    (monomialProjectiveScheme a k).IsSeparated :=
  inferInstanceAs ((Proj (homogeneousWeightGrading a k)).IsSeparated)

def monomialFanChart (j : vertexWeightIndices a) :
    coneChart k (s j)⟶monomialProjectiveScheme a k :=
  (monoidChartEqIso k (hdual j)).hom≫monomialCoordinateChartMap a k j.val

instance monomialFanChart_isOpenImmersion (j : vertexWeightIndices a) :
    IsOpenImmersion (monomialFanChart a k s hdual j) := by
  unfold monomialFanChart
  letI : IsOpenImmersion (monomialCoordinateChartMap a k j.val) :=
    monomialCoordinateChartMap_isOpenImmersion a k j.val
  exact IsOpenImmersion.comp _ _

set_option maxHeartbeats 2000000 in
theorem monomialFanChart_torus (j : vertexWeightIndices a) :
    coneChartFaceMap k (Finset.empty_subset (s j))≫monomialFanChart a k s hdual j=
      (zeroConeChartIso k n).hom≫monomialTorusChart a k j.val := by
  erw [monomialFanChart,coneChart_zeroFace_eq_torus k (s j),Category.assoc,
    ← Category.assoc (Spec.map (CommRingCat.ofHom
      (monoidChartAlgebra k (dualConeMonoid (s j))).val.toRingHom)),
    monoidChartEqIso_torus k (hdual j),monomialCoordinateChartMap_torus a k j.val]

theorem monomialFanChart_torus_agree (i j : vertexWeightIndices a) :
    coneChartFaceMap k (Finset.empty_subset (s i))≫monomialFanChart a k s hdual i=
      coneChartFaceMap k (Finset.empty_subset (s j))≫monomialFanChart a k s hdual j := by
  rw [monomialFanChart_torus,monomialFanChart_torus,monomialTorusChart_independent a k i.val j.val]

theorem monomialFanChart_opensRange (j : vertexWeightIndices a) :
    (monomialFanChart a k s hdual j).opensRange=
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j.val) := by
  change ((monoidChartEqIso k (hdual j)).hom≫
    monomialCoordinateChartMap a k j.val).opensRange=_
  erw [Scheme.Hom.opensRange_comp_of_isIso,monomialCoordinateChartMap_opensRange]

set_option maxHeartbeats 2000000 in
theorem monomialFanChart_preimage_range (i j : vertexWeightIndices a)
    (hz : a j.val-a i.val∈dualConeMonoid (s i)) :
    (monomialFanChart a k s hdual i) ⁻¹'
        Set.range (monomialFanChart a k s hdual j)=
      ((PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid (s i))
        (a j.val-a i.val) hz)).carrier : Set (coneChart k (s i))) := by
  let e : coneChart k (s i)≅monoidChartScheme k (differenceWeightMonoid a i.val) :=
    monoidChartEqIso k (hdual i)
  let f : monoidChartScheme k (differenceWeightMonoid a i.val)⟶
      monomialProjectiveScheme a k := monomialCoordinateChartMap a k i.val
  let U : (monomialProjectiveScheme a k).Opens :=
    Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j.val)
  have h₁ := congrArg (fun V : (monomialProjectiveScheme a k).Opens =>
    (e.hom≫f) ⁻¹ᵁ V) (monomialFanChart_opensRange a k s hdual j)
  have h₃ := congrArg
    (fun V : (monoidChartScheme k (differenceWeightMonoid a i.val)).Opens => e.hom ⁻¹ᵁ V)
    (monomialCoordinateChartMap_preimage_basicOpen a k i.val j.val)
  have h₄ := monoidChartEqIso_preimage_character k (hdual i)
    (a j.val-a i.val) hz (AddSubmonoid.subset_closure (Set.mem_range_self j.val))
  have ho : (e.hom≫f) ⁻¹ᵁ (monomialFanChart a k s hdual j).opensRange=
      PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid (s i))
        (a j.val-a i.val) hz) :=
    h₁.trans ((Scheme.Hom.comp_preimage e.hom f U).trans (h₃.trans h₄))
  exact congrArg (fun V : (coneChart k (s i)).Opens => V.carrier) ho

theorem monomialFanChart_cover (y : monomialProjectiveScheme a k) :
    ∃ j x,monomialFanChart a k s hdual j x=y := by
  have hy : y∈⨆ j : vertexWeightIndices a,
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j.val) := by
    rw [monomialProjective_vertex_cover]
    trivial
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  rw [← monomialFanChart_opensRange a k s hdual j] at hj
  obtain ⟨x,hx⟩ := hj
  exact ⟨j,x,hx⟩

/-- The normal fan chart scheme is the actual monomial projective
scheme, with its specified character torus unchanged. -/
def monomialNormalFanIso
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) :
    «Σ».fanScheme k≅monomialProjectiveScheme a k := by
  let f := monomialFanChart a k s hdual
  have hT := monomialFanChart_torus_agree a k s hdual
  refine «Σ».chartFamilyIso k s hs hcover f hT ?_
    (monomialFanChart_cover a k s hdual)
  intro i j
  rw [monomialFanChart_preimage_range a k s hdual i j
    («Σ».vertex_difference_mem_dualCone P (a i.val) (a j.val) (hv j) (s i) (hnormal i))]
  exact «Σ».normal_chart_intersection_range P k (a i.val) (a j.val) (hv i) (hv j)
    (s i) (s j) (hs i) (hs j) (hnormal i) (hnormal j)

theorem monomialNormalFanIso_chart
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) (j : vertexWeightIndices a) :
    «Σ».fanChartMap k ⟨s j,hs j⟩≫
        («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom=
      monomialFanChart a k s hdual j :=
  «Σ».familyChart_chartFamilyDesc k s hs hcover (monomialFanChart a k s hdual)
    (monomialFanChart_torus_agree a k s hdual) j

theorem monomialNormalFanIso_torus
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) (j : vertexWeightIndices a) :
    «Σ».splitTorusOpenMap k≫
        («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom=
      monomialTorusChart a k j.val := by
  rw [splitTorusOpenMap,Category.assoc]
  have hnat := «Σ».fanChartMap_naturality k
    (s := «Σ».zeroConeIndex) (t := ⟨s j,hs j⟩)
    (Finset.empty_subset (s j) : «Σ».zeroConeIndex.val⊆(⟨s j,hs j⟩ : «Σ».ConeIndex).val)
  change (zeroConeChartIso k n).inv≫(«Σ».fanChartMap k «Σ».zeroConeIndex≫_)=_
  rw [← hnat,Category.assoc,monomialNormalFanIso_chart,monomialFanChart_torus]
  simp only [← Category.assoc,Iso.inv_hom_id,Category.id_comp]

end PaperVerification.ToricGeometry.SmoothCompleteFan

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

/-- Actual scheme reconstruction from the local semigroup result. The
local bases themselves are mathematical conclusions of smoothness in
`pointed_semigroup_basis_of_smooth_open_torus`, not a fan hypothesis on
the original projective scheme. -/
theorem exists_fanSchemeIso_of_vertex_semigroups {ι : Type*}
    [Fintype ι] [Nonempty ι] {n : ℕ} (a : ι → Lattice n)
    (k : Type u) [Field k]
    (hlocal : ∀ j : vertexWeightIndices a,
      ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
        differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ) :
    ∃ (P : LatticePolytope n) («Σ» : SmoothCompleteFan n)
      (e : «Σ».fanScheme k≅monomialProjectiveScheme a k),
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth ∧
      «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      (∀ j : vertexWeightIndices a,
        «Σ».splitTorusOpenMap k≫e.hom=monomialTorusChart a k j.val) := by
  obtain ⟨P,«Σ»,s,hP,hPs,«hΣ»,hpure,hs,hcover,hdual,hnormal⟩ :=
    exists_polytope_fan_of_vertex_semigroups a hlocal
  have hv (j : vertexWeightIndices a) : embed n (a j.val)∈P.carrier := by
    rw [hP]
    exact subset_convexHull ℝ _ (Set.mem_range_self j.val)
  exact ⟨P,«Σ»,«Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal,
    hP,hPs,«hΣ»,hpure,fun j=>«Σ».monomialNormalFanIso_torus P a k s hdual hs hcover hv hnormal j⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.exists_fanSchemeIso_of_vertex_semigroups
