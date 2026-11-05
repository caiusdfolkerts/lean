module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import paper_verification.toric002
public import paper_verification.toric010
public import paper_verification.toric016
public import paper_verification.toric017
public import paper_verification.toric018
public import paper_verification.toric019
public import paper_verification.toric022
public import paper_verification.toric023
public import paper_verification.toric025
public import paper_verification.toric029
public import paper_verification.toric040

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricNormalChartOverlaps
section Source_ToricNormalChartOverlaps

-- original header: module

-- original header: public import PaperVerification.ToricChartOpenImmersions
-- original header: public import PaperVerification.ToricNormalConeFaces
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Lean.Elab.Tactic.Omega

-- original header: @[expose] public section

/-!
# A weight difference cuts out the actual common normal-cone chart

For two lattice points supporting actual fan cones, their difference is
nonnegative on the first cone and zero precisely on its common rays with
the second. Inverting this literal character therefore gives exactly the
common-face chart. This identifies actual projective chart overlaps with
actual fan gluing overlaps.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {n : ℕ}

def characterZeroFace (s : Finset (Lattice n)) (z : Lattice n) : Finset (Lattice n) :=
  s.filter (fun u=>integerPairing u z=0)

theorem characterZeroFace_subset (s : Finset (Lattice n)) (z : Lattice n) :
    characterZeroFace s z⊆s := Finset.filter_subset _ _

theorem negative_character_mem_zeroFace (s : Finset (Lattice n)) (z : Lattice n) :
    -z∈dualConeMonoid (characterZeroFace s z) := by
  intro u hu
  have hz := (Finset.mem_filter.mp hu).2
  simp only [integerPairing,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
  change 0≤-integerPairing u z
  rw [hz,neg_zero]

theorem character_clears_zeroFace (s : Finset (Lattice n)) (z : Lattice n)
    (hz : z∈dualConeMonoid s) (m : Lattice n)
    (hm : m∈dualConeMonoid (characterZeroFace s z)) :
    ∃ N : ℕ,m+N • z∈dualConeMonoid s := by
  let N := s.sup (fun u=>(-integerPairing u m).toNat)
  refine ⟨N,?_⟩
  intro u hu
  have he : integerPairing u (m+N • z)=
      integerPairing u m+(N : ℤ)*integerPairing u z := by
    simp [integerPairing,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,
      mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm]
  rw [he]
  by_cases hzero : integerPairing u z=0
  · rw [hzero,mul_zero,add_zero]
    exact hm u (Finset.mem_filter.mpr ⟨hu,hzero⟩)
  · have hpos : 1≤ integerPairing u z := by have := hz u hu;omega
    have hle : (-integerPairing u m).toNat≤N :=
      Finset.le_sup (f := fun u => (-integerPairing u m).toNat) hu
    have hleZ : (((-integerPairing u m).toNat : ℕ) : ℤ)≤(N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-integerPairing u m)
    have hN : (0 : ℤ)≤N := Int.natCast_nonneg _
    nlinarith

theorem characterZeroFace_isLocalizationMap (k : Type*) [CommSemiring k]
    (s : Finset (Lattice n)) (z : Lattice n) (hz : z∈dualConeMonoid s) :
    (Submonoid.powers (chartCharacter k (dualConeMonoid s) z hz)).IsLocalizationMap
      (monoidChartInclusion k (dualConeMonoid_antitone (characterZeroFace_subset s z))) :=
  monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone (characterZeroFace_subset s z)) z hz
    (negative_character_mem_zeroFace s z) (character_clears_zeroFace s z hz)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (P : LatticePolytope n)

include «Σ» in
theorem vertex_difference_mem_dualCone (v w : Lattice n)
    (hw : embed n w∈P.carrier) (s : Finset (Lattice n))
    (hs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n))) :
    w-v∈dualConeMonoid s := by
  intro u hu
  have hucone : embed n u∈P.normalCone (embed n v) :=
    hs.symm ▸ latticeRayCone_generator s hu
  have h := hucone (embed n w) hw
  change 0≤∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)) at h
  change 0≤∑ i,u i*(w i-v i)
  exact_mod_cast h

theorem normal_cone_common_rays_eq_characterZeroFace
    (v w : Lattice n) (hv : embed n v∈P.carrier) (hw : embed n w∈P.carrier)
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (ht : t∈«Σ».cones)
    (hvs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n)))
    (hwt : P.normalCone (embed n w)=(latticeRayCone t : Set (Ambient n))) :
    s∩t=characterZeroFace s (w-v) := by
  ext u
  simp only [Finset.mem_inter,characterZeroFace,Finset.mem_filter]
  constructor
  · rintro ⟨hus,hut⟩
    refine ⟨hus,?_⟩
    have hu : embed n u∈P.normalCone (embed n v)∩P.normalCone (embed n w) :=
      ⟨hvs.symm ▸ latticeRayCone_generator s hus,hwt.symm ▸ latticeRayCone_generator t hut⟩
    have hzero := ((P.mem_normalCone_inter_iff _ _ hv hw _).mp hu).2
    change (∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)))=0 at hzero
    change (∑ i,u i*(w i-v i))=0
    exact_mod_cast hzero
  · rintro ⟨hus,hzero⟩
    refine ⟨hus,?_⟩
    have hur : u∈«Σ».rays := («Σ».mem_rays_iff u).mpr ⟨s,hs,hus⟩
    apply («Σ».ray_mem_cone_iff ht hur).mp
    change embed n u∈(latticeRayCone t : Set (Ambient n))
    rw [← hwt]
    apply ((P.mem_normalCone_inter_iff _ _ hv hw _).mpr
      ⟨hvs.symm ▸ latticeRayCone_generator s hus,?_⟩).2
    change (∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)))=0
    change (∑ i,u i*(w i-v i))=0 at hzero
    exact_mod_cast hzero

/-- The common-face inclusion has exactly the principal open image
defined by the actual difference of the two vertex weights. -/
theorem normal_chart_intersection_range (k : Type*) [CommRing k]
    (v w : Lattice n) (hv : embed n v∈P.carrier) (hw : embed n w∈P.carrier)
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (ht : t∈«Σ».cones)
    (hvs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n)))
    (hwt : P.normalCone (embed n w)=(latticeRayCone t : Set (Ambient n))) :
    Set.range (coneChartFaceMap k (Finset.inter_subset_left : s∩t⊆s))=
      ((PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) (w-v)
        («Σ».vertex_difference_mem_dualCone P v w hw s hvs))).carrier :
          Set (coneChart k s)) := by
  have hz := «Σ».vertex_difference_mem_dualCone P v w hw s hvs
  have heq := «Σ».normal_cone_common_rays_eq_characterZeroFace P v w hv hw s t hs ht hvs hwt
  have hloc_transport (q : Finset (Lattice n))
      (hq : q=characterZeroFace s (w-v)) (hqs : q⊆s) :
      (Submonoid.powers (chartCharacter k (dualConeMonoid s) (w-v) hz)).IsLocalizationMap
        (monoidChartInclusion k (dualConeMonoid_antitone hqs)) := by
    subst q
    exact characterZeroFace_isLocalizationMap k s (w-v) hz
  have hloc := hloc_transport (s∩t) heq Finset.inter_subset_left
  letI : IsOpenImmersion (monoidChartSpecMap k
      (dualConeMonoid_antitone (Finset.inter_subset_left : s∩t⊆s))) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone (Finset.inter_subset_left : s∩t⊆s)) (w-v) hz hloc
  exact congrArg (fun U : TopologicalSpace.Opens
      (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s))) => U.carrier)
    (monoidChartSpecMap_opensRange_of_isLocalizationMap k _ (w-v) hz hloc)

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normal_chart_intersection_range
end
end Source_ToricNormalChartOverlaps
-- END ORIGINAL PaperVerification.ToricNormalChartOverlaps


-- BEGIN ORIGINAL PaperVerification.ToricSemigroupPolytopes
section Source_ToricSemigroupPolytopes

-- original header: module

-- original header: public import PaperVerification.ToricSmoothPointedSemigroup
-- original header: public import PaperVerification.ToricProjectiveVertexCover
-- original header: public import PaperVerification.ToricOrthantEdges
-- original header: public import PaperVerification.ToricFaceInheritance
-- original header: public import PaperVerification.ToricFanConstruction
-- original header: public import Mathlib.Algebra.Group.Submonoid.Finsupp
-- original header: public import Mathlib.Tactic.Module

-- original header: @[expose] public section

/-!
# Primitive affine semigroup charts reconstruct the actual smooth polytope

The input semigroups are the additive closures of literal weight
differences. Their basis descriptions give supporting orthants and
positive points on every coordinate ray of the actual convex hull.
Every incident edge is then proved to be a coordinate edge using its
actual minimal face. This supplies the ordinary polytope smoothness
predicate and its complete normal fan, without inserting an edge or
fan correspondence as an assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricCharacters PaperVerification.ToricExchange
open PaperVerification.ToricVertexCone
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

theorem positive_axis_point_of_differenceMonoid (a : ι → Lattice n) (j : ι)
    (z : Lattice n) (hz : z∈differenceWeightMonoid a j) (hz0 : z≠0) :
    ∃ ε : ℝ,0<ε ∧ embed n (a j)+ε • embed n z∈
      convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
  obtain ⟨c,hc⟩ := AddSubmonoid.exists_of_mem_closure_range
    (fun i=>a i-a j) z hz
  let N : ℕ := ∑ i,c i
  have hN : 0<N := by
    by_contra h
    have hzero : N=0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    have hci : ∀ i,c i=0 := fun i=>
      (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    exact hz0 (by simpa [hci] using hc)
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  let w : ι → ℝ := fun i=>(c i : ℝ)/(N : ℝ)
  have hw0 (i : ι) : 0≤w i := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hw1 : ∑ i,w i=1 := by
    simp only [w,← Finset.sum_div,← Nat.cast_sum,show ∑ i,c i=N from rfl]
    exact div_self hNR.ne'
  have hcR : embed n z=∑ i,(c i : ℝ) • (embed n (a i)-embed n (a j)) := by
    simpa only [map_sum,map_nsmul,map_sub,Nat.cast_smul_eq_nsmul] using congrArg (embed n) hc
  have hcomb : ∑ i,w i • embed n (a i)=
      embed n (a j)+(N : ℝ)⁻¹ • embed n z := by
    have hNcast : ∑ i,(c i : ℝ)=(N : ℝ) := by simp [N]
    rw [hcR,Finset.smul_sum]
    simp only [smul_sub,Finset.sum_sub_distrib,smul_smul]
    rw [← Finset.sum_smul]
    have hsum : ∑ i,(N : ℝ)⁻¹*(c i : ℝ)=1 := by
      rw [← Finset.mul_sum,hNcast,inv_mul_cancel₀ hNR.ne']
    rw [hsum,one_smul]
    simp only [w,div_eq_mul_inv,mul_comm]
    module
  refine ⟨(N : ℝ)⁻¹,inv_pos.mpr hNR,?_⟩
  rw [← hcomb]
  exact mem_convexHull_of_exists_fintype w (fun i=>embed n (a i)) hw0 hw1
    (fun i=>Set.mem_range_self i) rfl

theorem affineSpan_eq_top_of_difference_basis (a : ι → Lattice n) (j : ι)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hb : ∀ i,b i∈differenceWeightMonoid a j) :
    affineSpan ℝ (convexHull ℝ (Set.range (fun i=>embed n (a i))))=⊤ := by
  let P := convexHull ℝ (Set.range (fun i=>embed n (a i)))
  let A := affineSpan ℝ P
  have hv : embed n (a j)∈A :=
    subset_affineSpan ℝ _ (subset_convexHull ℝ _ (Set.mem_range_self j))
  have hdir (i : Fin n) : integralBasisReal b i∈A.direction := by
    obtain ⟨ε,hε,hpoint⟩ := positive_axis_point_of_differenceMonoid a j (b i) (hb i)
      (b.ne_zero i)
    have h := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hpoint) hv
    have h' : ε • integralBasisReal b i∈A.direction := by
      simpa only [vsub_eq_sub,add_sub_cancel_left,integralBasisReal_apply] using h
    simpa only [smul_smul,inv_mul_cancel₀ hε.ne',one_smul] using
      A.direction.smul_mem ε⁻¹ h'
  have hall (x : Ambient n) : x∈A.direction := by
    rw [← (integralBasisReal b).sum_repr x]
    exact Submodule.sum_mem _ (fun i hi=>A.direction.smul_mem _ (hdir i))
  apply top_unique
  intro x hx
  simpa only [vadd_eq_add,sub_add_cancel] using
    AffineSubspace.vadd_mem_of_mem_direction (hall (x-embed n (a j))) hv

theorem hull_orthant_of_difference_basis (a : ι → Lattice n) (j : ι)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hS : differenceWeightMonoid a j=coordinateConeMonoid b Finset.univ) :
    ∀ x∈convexHull ℝ (Set.range (fun i=>embed n (a i))),∀ l,
      0≤(integralBasisReal b).repr (x-embed n (a j)) l := by
  intro x hx l
  let f := (integralBasisReal b).coord l
  have hgen (i : ι) : f (embed n (a j))≤f (embed n (a i)) := by
    have hi : a i-a j∈coordinateConeMonoid b Finset.univ := hS ▸
      AddSubmonoid.subset_closure (Set.mem_range_self i)
    have hcoord : 0≤b.repr (a i-a j) l := hi l (Finset.mem_univ l)
    have hreal : 0≤(integralBasisReal b).repr
        (embed n (a i)-embed n (a j)) l := by
      rw [← map_sub,integralBasisReal_repr]
      exact_mod_cast hcoord
    simpa only [f,Module.Basis.coord_apply,map_sub,Finsupp.sub_apply,sub_nonneg] using hreal
  have hbound : f (embed n (a j))≤f x :=
    convexHull_min (by rintro _ ⟨i,rfl⟩;exact hgen i)
      ((convex_Ici (f (embed n (a j)))).linear_preimage f) hx
  simpa only [f,Module.Basis.coord_apply,map_sub,Finsupp.sub_apply,sub_nonneg] using hbound

namespace LatticePolytope

variable (P : LatticePolytope n)

/-- Orthant coordinates plus genuine positive feasible axis points
exhaust all incident edges of an actual polytope. -/
theorem edge_has_coordinate_direction_of_orthant_axes (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (horthant : ∀ x∈P.carrier,∀ j,0≤b.repr (x-v) j)
    (haxes : ∀ i,∃ ε : ℝ,0<ε ∧ v+ε • b i∈P.carrier)
    (w : Ambient n) (hedge : P.IsEdge v w) :
    ∃ i,w∈P.coordinateRayFace v b i := by
  obtain ⟨κ,hκ,H,hPH⟩ := P.hasFiniteHalfspaces
  letI := hκ
  obtain ⟨hv,hw⟩ := P.edge_endpoints_extreme hedge
  have hpositive : ∃ i,0<b.repr (w-v) i := by
    by_contra hn
    push_neg at hn
    apply hedge.1
    apply b.ext_elem
    intro i
    have hz := le_antisymm (hn i) (horthant w hw.1 i)
    have he : b.repr w i=b.repr v i := by
      simpa only [map_sub,Finsupp.sub_apply,sub_eq_zero] using hz
    exact he.symm
  obtain ⟨i,hi⟩ := hpositive
  choose ε hε hεP using haxes
  have hvF : v∈H.face (H.jointZeros v w) := by
    exact ⟨hPH ▸ hv.1,fun k hk=>hk.1⟩
  have hwF : w∈H.face (H.jointZeros v w) := by
    exact ⟨hPH ▸ hw.1,fun k hk=>hk.2⟩
  have hzF := positive_coordinate_endpoint_mem_face H (H.jointZeros v w)
    b v hvF ε hε (fun j=>hPH ▸ hεP j)
    (fun x hx=>horthant x (hPH.symm ▸ hx)) w hwF i hi
  have hmin := H.jointFace_minimal (hPH ▸ hv.1) (hPH ▸ hw.1)
    (convex_segment v w) (by simpa only [← hPH] using hedge.2)
    (left_mem_segment ℝ v w) (right_mem_segment ℝ v w)
  obtain ⟨r,t,hr,ht,hrt,hline⟩ := hmin hzF
  have hcoords (j : Fin n) :
      ε i*(if i=j then 1 else 0)=t*b.repr (w-v) j := by
    have he := congrArg (fun x=>b.repr x j) hline
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
      Module.Basis.repr_self_apply,smul_eq_mul] at he
    simp only [map_sub,Finsupp.sub_apply]
    have hrtj := congrArg (fun s : ℝ=>s * (b.repr v) j) hrt
    nlinarith only [he,hrtj]
  have htne : t≠0 := by
    intro h
    exact (hε i).ne' (by simpa [h] using hcoords i)
  refine ⟨i,hw.1,?_⟩
  intro j hji
  have h := hcoords j
  rw [if_neg (Ne.symm hji),mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left htne

theorem smooth_of_vertex_orthants_and_axes
    (hlocal : ∀ v∈P.carrier.extremePoints ℝ,
      ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)),
        vZ∈P.generators ∧ embed n vZ=v ∧
        (∀ x∈P.carrier,∀ i,0≤(integralBasisReal b).repr (x-v) i) ∧
        (∀ i,∃ ε : ℝ,0<ε ∧ v+ε • integralBasisReal b i∈P.carrier)) : P.Smooth := by
  intro v hv
  obtain ⟨vZ,b,hvZ,rfl,horthant,haxes⟩ := hlocal v hv
  choose lengths hlengths using fun i=>P.coordinateRayFace_eq_integral_edge
    vZ hvZ b horthant i (haxes i)
  refine ⟨vZ,b,lengths,rfl,fun i=>⟨(hlengths i).1,(hlengths i).2.1⟩,?_⟩
  intro w hw
  obtain ⟨i,hi⟩ := P.edge_has_coordinate_direction_of_orthant_axes
    (embed n vZ) (integralBasisReal b) horthant haxes w hw
  have hwseg := (hlengths i).2.2 ▸ hi
  have hverts := P.edge_endpoints_extreme hw
  have hend := (P.edge_endpoints_extreme (hlengths i).2.1).2.1
  rcases (mem_extremePoints_iff_forall_segment.mp hverts.2).2
    _ hverts.1.1 _ hend hwseg with hvw|hew
  · exact (hw.1 hvw).elim
  · exact ⟨i,hew.symm⟩

end LatticePolytope

/-- Literal basis semigroups at all actual vertex charts reconstruct the
actual finite convex hull as a smooth full-dimensional lattice polytope. -/
theorem exists_smooth_polytope_of_vertex_semigroups [Nonempty ι]
    (a : ι → Lattice n)
    (hlocal : ∀ j : vertexWeightIndices a,
      ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
        differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ) :
    ∃ P : LatticePolytope n,
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth := by
  have hverts : (vertexWeightIndices a : Set ι).Nonempty := by
    by_contra h
    have hempty : vertexWeightIndices a=∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi=>h ⟨i,hi⟩)
    have hH := hull_vertexWeightIndices a
    have hzero : convexHull ℝ (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val)))=∅ := by
      haveI : IsEmpty (vertexWeightIndices a) := ⟨fun i=>by simpa [hempty] using i.property⟩
      simp only [Set.range_eq_empty,convexHull_empty]
    have hmem := subset_convexHull ℝ (Set.range (fun i=>embed n (a i)))
      (Set.mem_range_self (Classical.arbitrary ι))
    rw [← hH,hzero] at hmem
    exact hmem
  obtain ⟨j,hj⟩ := hverts
  obtain ⟨b,hb⟩ := hlocal ⟨j,hj⟩
  have hfull : affineSpan ℝ
      (convexHull ℝ (Set.range (fun i=>embed n (a i))))=⊤ :=
    affineSpan_eq_top_of_difference_basis a j b (fun i=>by
      rw [hb]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num)
  let P : LatticePolytope n :=
    { generators := Finset.univ.image a
      nonempty := ⟨a j,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩
      fullDimensional := by
        simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ,← Set.range_comp'] using hfull }
  have hcarrier : P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
    simp only [P,LatticePolytope.carrier,Finset.coe_image,Finset.coe_univ,
      Set.image_univ,← Set.range_comp']
  refine ⟨P,hcarrier,P.smooth_of_vertex_orthants_and_axes ?_⟩
  intro v hv
  rw [hcarrier] at hv
  obtain ⟨j,rfl⟩ := extremePoints_convexHull_subset hv
  have hj : j∈vertexWeightIndices a := Finset.mem_filter.mpr ⟨Finset.mem_univ j,hv⟩
  obtain ⟨b,hb⟩ := hlocal ⟨j,hj⟩
  refine ⟨a j,b,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩,rfl,?_,?_⟩
  · simpa only [hcarrier] using hull_orthant_of_difference_basis a j b hb
  · intro i
    have hbi : b i∈differenceWeightMonoid a j := by
      rw [hb]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num
    simpa only [hcarrier,integralBasisReal_apply] using
      positive_axis_point_of_differenceMonoid a j (b i) hbi (b.ne_zero i)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.exists_smooth_polytope_of_vertex_semigroups
end
end Source_ToricSemigroupPolytopes
-- END ORIGINAL PaperVerification.ToricSemigroupPolytopes


-- BEGIN ORIGINAL PaperVerification.ToricChosenVertexFans
section Source_ToricChosenVertexFans

-- original header: module

-- original header: public import PaperVerification.ToricSemigroupPolytopes
-- original header: public import PaperVerification.ToricNormalChartOverlaps

-- original header: @[expose] public section

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
end
end Source_ToricChosenVertexFans
-- END ORIGINAL PaperVerification.ToricChosenVertexFans


-- BEGIN ORIGINAL PaperVerification.ToricFanSchemeChartIso
section Source_ToricFanSchemeChartIso

-- original header: module

-- original header: public import PaperVerification.ToricFanSchemeIntegral
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Separated
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

-- original header: @[expose] public section

/-!
# An actual scheme isomorphism from compatible affine fan charts

The hypotheses below concern literal open immersions of the already
constructed cone schemes. Agreement is tested on the actual dense torus,
and overlap ranges are required to equal the actual common-face chart.
The resulting map is constructed by the genuine fan colimit. Its point
injectivity, open-immersion property, and surjectivity are proved, giving
an actual scheme isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem coneChart_zeroFace_isDominant (s : «Σ».ConeIndex) :
    IsDominant (coneChartFaceMap k (Finset.empty_subset s.val)) := by
  refine ⟨?_⟩
  intro x
  have hg : «Σ».fanChartGenericPoint k s∈
      Set.range (coneChartFaceMap k (Finset.empty_subset s.val)) := by
    exact ⟨«Σ».fanChartGenericPoint k «Σ».zeroConeIndex,
      «Σ».fanChartGenericPoint_faceMap k
        (s := «Σ».zeroConeIndex) (t := s) (Finset.empty_subset s.val)⟩
  have hsub : ({«Σ».fanChartGenericPoint k s} : Set (coneChart k s.val))⊆
      Set.range (coneChartFaceMap k (Finset.empty_subset s.val)) :=
    Set.singleton_subset_iff.mpr hg
  have hcl := closure_mono hsub
  rw [(«Σ».fanChartGenericPoint_isGenericPoint k s).def] at hcl
  exact hcl (Set.mem_univ x)

section ChartFamily

variable {J : Type*} (s : J → Finset (Lattice n)) (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    {Y : Scheme.{u}} [Y.IsSeparated]
    (f : ∀ j,coneChart k (s j)⟶Y)
    [∀ j,IsOpenImmersion (f j)]
    (hT : ∀ i j,
      coneChartFaceMap k (Finset.empty_subset (s i))≫f i=
        coneChartFaceMap k (Finset.empty_subset (s j))≫f j)

include hs hT in
theorem chartFamily_commonFace_agree (i j : J) :
    coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i)≫f i=
      coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j)≫f j := by
  let t : «Σ».ConeIndex := ⟨s i∩s j,«Σ».downward (s i) (hs i) _ Finset.inter_subset_left⟩
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  simpa only [← Category.assoc,coneChartFaceMap_comp] using hT i j

def chartFamilyChoice (t : «Σ».ConeIndex) : J :=
  Classical.choose (hcover t.val t.property)

theorem chartFamilyChoice_subset (t : «Σ».ConeIndex) :
    t.val⊆s («Σ».chartFamilyChoice s hcover t) :=
  Classical.choose_spec (hcover t.val t.property)

def chartFamilyMap (t : «Σ».ConeIndex) : coneChart k t.val⟶Y :=
  coneChartFaceMap k («Σ».chartFamilyChoice_subset s hcover t)≫
    f («Σ».chartFamilyChoice s hcover t)

include hs hT in
theorem chartFamilyMap_torus (t : «Σ».ConeIndex) (j : J) :
    coneChartFaceMap k (Finset.empty_subset t.val)≫
      «Σ».chartFamilyMap k s hcover f t=
        coneChartFaceMap k (Finset.empty_subset (s j))≫f j := by
  simpa only [chartFamilyMap,← Category.assoc,coneChartFaceMap_comp] using
    hT («Σ».chartFamilyChoice s hcover t) j

include hs hT in
theorem chartFamilyMap_naturality {t q : «Σ».ConeIndex} (htq : t.val⊆q.val) :
    coneChartFaceMap k htq≫«Σ».chartFamilyMap k s hcover f q=
      «Σ».chartFamilyMap k s hcover f t := by
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  rw [← Category.assoc,coneChartFaceMap_comp,
    «Σ».chartFamilyMap_torus k s hs hcover f hT q («Σ».chartFamilyChoice s hcover t)]
  unfold chartFamilyMap
  rw [← Category.assoc,coneChartFaceMap_comp]

def chartFamilyCocone : Cocone («Σ».coneDiagram k) where
  pt := Y
  «ι» := {
    app := «Σ».chartFamilyMap k s hcover f
    naturality := by
      intro t q h
      change coneChartFaceMap k (leOfHom h)≫«Σ».chartFamilyMap k s hcover f q=
        «Σ».chartFamilyMap k s hcover f t≫𝟙 Y
      exact («Σ».chartFamilyMap_naturality k s hs hcover f hT (leOfHom h)).trans
        (Category.comp_id _).symm }

def chartFamilyDesc : «Σ».fanScheme k⟶Y :=
  colimit.desc («Σ».coneDiagram k) («Σ».chartFamilyCocone k s hs hcover f hT)

@[reassoc] theorem fanChartMap_chartFamilyDesc (t : «Σ».ConeIndex) :
    «Σ».fanChartMap k t≫«Σ».chartFamilyDesc k s hs hcover f hT=
      «Σ».chartFamilyMap k s hcover f t :=
  colimit.ι_desc («Σ».chartFamilyCocone k s hs hcover f hT) t

@[reassoc] theorem familyChart_chartFamilyDesc (j : J) :
    «Σ».fanChartMap k ⟨s j,hs j⟩≫«Σ».chartFamilyDesc k s hs hcover f hT=f j := by
  rw [«Σ».fanChartMap_chartFamilyDesc]
  let t : «Σ».ConeIndex := ⟨s j,hs j⟩
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  exact «Σ».chartFamilyMap_torus k s hs hcover f hT t j

include hcover in
theorem familyCharts_cover_fanScheme (x : «Σ».fanScheme k) :
    ∃ j y,«Σ».fanChartMap k ⟨s j,hs j⟩ y=x := by
  obtain ⟨t,y,rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  let j := «Σ».chartFamilyChoice s hcover t
  let ht := «Σ».chartFamilyChoice_subset s hcover t
  refine ⟨j,coneChartFaceMap k ht y,?_⟩
  exact congrArg (fun g : coneChart k t.val⟶«Σ».fanScheme k => g y)
    («Σ».fanChartMap_naturality k (s := t) (t := ⟨s j,hs j⟩) ht)

theorem chartFamilyDesc_injective
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j)) :
    Function.Injective («Σ».chartFamilyDesc k s hs hcover f hT) := by
  intro x y hxy
  obtain ⟨i,xi,rfl⟩ := «Σ».familyCharts_cover_fanScheme k s hs hcover x
  obtain ⟨j,yj,rfl⟩ := «Σ».familyCharts_cover_fanScheme k s hs hcover y
  have h : f i xi=f j yj := by
    simpa only [← Scheme.Hom.comp_apply,«Σ».familyChart_chartFamilyDesc] using hxy
  have hxi : xi∈Set.range
      (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i)) := by
    rw [hoverlap]
    exact ⟨yj,h.symm⟩
  obtain ⟨z,hzi⟩ := hxi
  have hzj : coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j) z=yj := by
    apply (f j).isOpenEmbedding.injective
    calc
      f j (coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j) z)=
          f i (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i) z) :=
        congrArg (fun g=>g z) («Σ».chartFamily_commonFace_agree k s hs f hT i j).symm
      _ = f j yj := by rw [hzi,h]
  exact («Σ».fanChartMap_eq_iff k ⟨s i,hs i⟩ ⟨s j,hs j⟩ xi yj).mpr ⟨z,hzi,hzj⟩

theorem chartFamilyDesc_isOpenImmersion
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j)) :
    IsOpenImmersion («Σ».chartFamilyDesc k s hs hcover f hT) := by
  apply IsOpenImmersion.of_openCover_source _ («Σ».fanSchemeOpenCover k)
    («Σ».chartFamilyDesc_injective k s hs hcover f hT hoverlap)
  intro t
  change IsOpenImmersion («Σ».fanChartMap k t≫_)
  rw [«Σ».fanChartMap_chartFamilyDesc]
  unfold chartFamilyMap
  letI := «Σ».coneChartFaceMap_isOpenImmersion k _ _
    (hs («Σ».chartFamilyChoice s hcover t)) («Σ».chartFamilyChoice_subset s hcover t)
  infer_instance

theorem chartFamilyDesc_surjective (hY : ∀ y : Y,∃ j x,f j x=y) :
    Function.Surjective («Σ».chartFamilyDesc k s hs hcover f hT) := by
  intro y
  obtain ⟨j,x,rfl⟩ := hY y
  refine ⟨«Σ».fanChartMap k ⟨s j,hs j⟩ x,?_⟩
  rw [← Scheme.Hom.comp_apply,«Σ».familyChart_chartFamilyDesc]

/-- The actual fan colimit is isomorphic to the separated target once
its literal chart maps have the proved common-face overlaps and cover. -/
def chartFamilyIso
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j))
    (hY : ∀ y : Y,∃ j x,f j x=y) : «Σ».fanScheme k≅Y := by
  let F := «Σ».chartFamilyDesc k s hs hcover f hT
  letI : IsOpenImmersion F := «Σ».chartFamilyDesc_isOpenImmersion k s hs hcover f hT hoverlap
  letI : Surjective F := ⟨«Σ».chartFamilyDesc_surjective k s hs hcover f hT hY⟩
  letI : IsIso F := (isIso_iff_isOpenImmersion_and_surjective F).mpr ⟨inferInstance,inferInstance⟩
  exact asIso F

end ChartFamily

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartFamilyIso
end
end Source_ToricFanSchemeChartIso
-- END ORIGINAL PaperVerification.ToricFanSchemeChartIso


-- BEGIN ORIGINAL PaperVerification.ToricMonomialFanIso
section Source_ToricMonomialFanIso

-- original header: module

-- original header: public import PaperVerification.ToricChosenVertexFans
-- original header: public import PaperVerification.ToricFanSchemeChartIso
-- original header: public import PaperVerification.ToricProjectiveMonomialMaps
-- original header: public import PaperVerification.ToricFanCharacters

-- original header: @[expose] public section

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
end
end Source_ToricMonomialFanIso
-- END ORIGINAL PaperVerification.ToricMonomialFanIso


-- BEGIN ORIGINAL PaperVerification.ToricSmoothMonomialFan
section Source_ToricSmoothMonomialFan

-- original header: module

-- original header: public import PaperVerification.ToricMonomialFanIso
-- original header: public import PaperVerification.ToricIntrinsicAffineCharts
-- original header: public import PaperVerification.ToricFanAction

-- original header: @[expose] public section

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
end
end Source_ToricSmoothMonomialFan
-- END ORIGINAL PaperVerification.ToricSmoothMonomialFan


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicFanClassification
section Source_ToricIntrinsicFanClassification

-- original header: module

-- original header: public import PaperVerification.ToricMonomialImageComparison
-- original header: public import PaperVerification.ToricIntrinsicProjectiveEmbedding
-- original header: public import PaperVerification.ToricSmoothMonomialFan

-- original header: @[expose] public section

/-!
# Fan reconstruction from an intrinsic smooth projective toric scheme

The hypotheses are the ordinary smooth and proper structural morphisms,
an actual dense equivariant open split torus, and an actual ample Cartier
sheaf. Character sections are obtained from the proved section coaction.
Their genuine projective closed immersion is identified with the genuine
monomial Proj by equality of kernel ideal sheaves. Ordinary smoothness
then reconstructs unimodular affine semigroups and the complete normal
fan. The result is an actual scheme isomorphism preserving the field and
the original torus; no fan classification is assumed as a premise.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance : IsDomain (AddMonoidAlgebra k (Fin n→ℤ)) :=
  torusCoordinateRing_isDomain k n

/-- Intrinsic geometric hypotheses yield an actual complete smooth fan
and an actual scheme isomorphism over the original field. -/
theorem exists_smooth_complete_fan
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ (P : LatticePolytope n) («Σ» : SmoothCompleteFan n)
      (e : «Σ».fanScheme k≅X.left),
      P.Smooth ∧ «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      e.hom≫X.hom=«Σ».fanSchemeStructureMap k ∧
      «Σ».splitTorusOpenMap k≫e.hom=T.torus.left := by
  obtain ⟨C,F,s,hvalue,hcover,hclosed⟩ := T.exists_character_projective_embedding D hD
  let a : ULift.{u} F→Lattice n := fun m => m.down.val
  have hF : Nonempty (ULift.{u} F) := by
    have hη : genericPoint X.left∈⨆ i : ULift.{u} F,C.nonvanishingOpen (s i) := by
      rw [hcover]; trivial
    obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hη
    exact ⟨i⟩
  let i₀ : ULift.{u} F := Classical.choice hF
  letI : IsClosedImmersion (C.sectionProjectiveMap k s hcover) := hclosed
  let e₀ : X.left≅monomialProjectiveScheme a k :=
    C.characterMonomialImageIso k T.torus.left a s hvalue T.dense hcover i₀
  let j : Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n))) ⟶ X.left :=
    T.torus.left
  letI : IsOpenImmersion j := T.open_immersion
  have htorus : T.torus.left≫e₀.hom=monomialTorusChart a k i₀ :=
    C.characterMonomialImageIso_torus k T.torus.left a s hvalue T.dense hcover i₀
  letI : IsDominant T.torus.left := ⟨T.dense⟩
  have hbase : e₀.hom≫monomialProjectiveToSpec a k=X.hom := by
    apply ext_of_isDominant T.torus.left
    rw [← Category.assoc,htorus]
    change monomialTorusChart a k i₀ ≫ monomialProjectiveToSpec a k = j ≫ X.hom
    exact (monomialTorusChart_toSpec a k i₀).trans T.torus.w.symm
  have hbase' : monomialProjectiveToSpec a k=e₀.inv≫X.hom := by
    rw [← hbase]
    simp
  letI : Smooth (monomialProjectiveToSpec a k) := by
    rw [hbase']
    infer_instance
  letI : IsOpenImmersion (monomialTorusChart a k i₀) := by
    rw [← htorus]
    change IsOpenImmersion (j ≫ e₀.hom)
    infer_instance
  obtain ⟨P,«Σ»,e₁,hP,hPs,«hΣ»,hpure,hbase₁,htorus₁⟩ :=
    exists_smooth_normal_fan_of_monomial_projective a k i₀
  refine ⟨P,«Σ»,e₁.trans e₀.symm,hPs,«hΣ»,hpure,?_,?_⟩
  · simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc]
    rw [← hbase',hbase₁]
  · simp only [Iso.trans_hom,Iso.symm_hom,← Category.assoc]
    rw [htorus₁ i₀,← htorus]
    change (j ≫ e₀.hom) ≫ e₀.inv = j
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_smooth_complete_fan
end
end Source_ToricIntrinsicFanClassification
-- END ORIGINAL PaperVerification.ToricIntrinsicFanClassification


-- BEGIN ORIGINAL PaperVerification.ToricOrbitChartQuotient
section Source_ToricOrbitChartQuotient

-- original header: module

-- original header: public import PaperVerification.ToricCartierCharacterModules
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

-- original header: @[expose] public section

/-!
# Actual closed orbit charts

A face of an additive semigroup gives a genuine quotient of its semigroup
algebra: characters outside the face map to zero, and characters on the face
remain their actual basis characters. The quotient map has an explicit right
inverse as a linear map (indeed an algebra map), so it induces an actual
closed immersion of affine schemes. Applied to a cone, the face consists
of characters vanishing on the specified cone rays.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped Classical

variable {M : Type*} [AddCommMonoid M]

/-- The intrinsic additive face condition. -/
def IsAdditiveFace (F : AddSubmonoid M) : Prop :=
  ∀ m p : M, m+p∈F → m∈F ∧ p∈F

theorem additiveFace_add_iff (F : AddSubmonoid M) (hF : IsAdditiveFace F)
    (m p : M) : m+p∈F ↔ m∈F ∧ p∈F :=
  ⟨hF m p,fun h => F.add_mem h.1 h.2⟩

variable (k : Type*) [CommRing k]

def additiveFaceCharacter (F : AddSubmonoid M) (hF : IsAdditiveFace F) :
    Multiplicative M →* AddMonoidAlgebra k F where
  toFun m := if hm : m.toAdd∈F then single ⟨m.toAdd,hm⟩ 1 else 0
  map_one' := by simp only [toAdd_one,dif_pos F.zero_mem]; rfl
  map_mul' m p := by
    change (if h : m.toAdd+p.toAdd∈F then single (⟨m.toAdd+p.toAdd,h⟩ : F) (1 : k) else 0) = _
    by_cases hm : m.toAdd∈F <;> by_cases hp : p.toAdd∈F
    · rw [dif_pos (F.add_mem hm hp),dif_pos hm,dif_pos hp,single_mul_single,one_mul]
      rfl
    · rw [dif_neg (fun h => hp (hF _ _ h).2),dif_pos hm,dif_neg hp,mul_zero]
    · rw [dif_neg (fun h => hm (hF _ _ h).1),dif_neg hm,dif_pos hp,zero_mul]
    · rw [dif_neg (fun h => hm (hF _ _ h).1),dif_neg hm,dif_neg hp,zero_mul]

/-- The literal quotient map on semigroup algebras. -/
def additiveFaceRetraction (F : AddSubmonoid M) (hF : IsAdditiveFace F) :
    AddMonoidAlgebra k M →ₐ[k] AddMonoidAlgebra k F :=
  AddMonoidAlgebra.lift k (AddMonoidAlgebra k F) M (additiveFaceCharacter k F hF)

@[simp] theorem additiveFaceRetraction_single_of_mem
    (F : AddSubmonoid M) (hF : IsAdditiveFace F) (m : M) (hm : m∈F) (a : k) :
    additiveFaceRetraction k F hF (single m a) = single ⟨m,hm⟩ a := by
  simp [additiveFaceRetraction,additiveFaceCharacter,hm,smul_single]

@[simp] theorem additiveFaceRetraction_single_of_not_mem
    (F : AddSubmonoid M) (hF : IsAdditiveFace F) (m : M) (hm : m∉F) (a : k) :
    additiveFaceRetraction k F hF (single m a) = 0 := by
  simp [additiveFaceRetraction,additiveFaceCharacter,hm]

theorem additiveFaceRetraction_surjective (F : AddSubmonoid M)
    (hF : IsAdditiveFace F) : Function.Surjective (additiveFaceRetraction k F hF) := by
  intro f
  induction f using AddMonoidAlgebra.induction_on with
  | of m =>
      refine ⟨single m.val 1,?_⟩
      exact additiveFaceRetraction_single_of_mem k F hF m.val m.property 1
  | add f g hf hg =>
      obtain ⟨f',hf'⟩ := hf
      obtain ⟨g',hg'⟩ := hg
      exact ⟨f'+g',by rw [map_add,hf',hg']⟩
  | smul a f hf =>
      obtain ⟨f',hf'⟩ := hf
      exact ⟨a • f',by rw [map_smul,hf']⟩

/-- An actual closed immersion, obtained from a surjective ring map. -/
theorem additiveFace_isClosedImmersion (F : AddSubmonoid M)
    (hF : IsAdditiveFace F) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (additiveFaceRetraction k F hF).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (additiveFaceRetraction_surjective k F hF)

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped Classical

variable {n : ℕ}

/-- The actual semigroup face cut out by vanishing on a subcone. It is
defined inside the original dual semigroup, so every other ray pairing
retains its nonnegativity condition. -/
def orbitCharacterFace (s t : Finset (Lattice n)) : AddSubmonoid (dualConeMonoid s) where
  carrier := {m | ∀ u∈t,integerPairing u m.val=0}
  zero_mem' := by intro u hu; simp [integerPairing]
  add_mem' := by
    intro m p hm hp u hu
    rw [show ((m+p : dualConeMonoid s) : Lattice n)=m.val+p.val from rfl,
      integerPairing_add,hm u hu,hp u hu,zero_add]

theorem orbitCharacterFace_isAdditiveFace (s t : Finset (Lattice n)) (hts : t⊆s) :
    IsAdditiveFace (orbitCharacterFace s t) := by
  intro m p h
  constructor
  · intro u hu
    have hm := m.property u (hts hu)
    have hp := p.property u (hts hu)
    have hh := h u hu
    change integerPairing u (m.val+p.val)=0 at hh
    rw [integerPairing_add] at hh
    omega
  · intro u hu
    have hm := m.property u (hts hu)
    have hp := p.property u (hts hu)
    have hh := h u hu
    change integerPairing u (m.val+p.val)=0 at hh
    rw [integerPairing_add] at hh
    omega

variable (k : Type*) [CommRing k]

/-- The orbit-closure chart as the spectrum of its actual semigroup face. -/
def orbitClosureChart (s t : Finset (Lattice n)) : Scheme :=
  Spec (CommRingCat.of (AddMonoidAlgebra k (orbitCharacterFace s t)))

/-- Quotienting the actual chart ring by the characters positive on the
subcone. This is a morphism of actual affine schemes. -/
def orbitClosureChartMap (s t : Finset (Lattice n)) (hts : t⊆s) :
    orbitClosureChart k s t ⟶
      Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s))) :=
  Spec.map (CommRingCat.ofHom
    ((additiveFaceRetraction k (orbitCharacterFace s t)
      (orbitCharacterFace_isAdditiveFace s t hts)).comp
        (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.toAlgHom).toRingHom)

instance orbitClosureChartMap_isClosedImmersion (s t : Finset (Lattice n)) (hts : t⊆s) :
    IsClosedImmersion (orbitClosureChartMap k s t hts) := by
  apply IsClosedImmersion.spec_of_surjective
  exact (additiveFaceRetraction_surjective k (orbitCharacterFace s t)
    (orbitCharacterFace_isAdditiveFace s t hts)).comp
      (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.surjective

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricCharacters.additiveFaceRetraction_surjective
#print axioms PaperVerification.ToricGeometry.orbitClosureChartMap_isClosedImmersion
end
end Source_ToricOrbitChartQuotient
-- END ORIGINAL PaperVerification.ToricOrbitChartQuotient


-- BEGIN ORIGINAL PaperVerification.ToricOrbitQuotientCoordinates
section Source_ToricOrbitQuotientCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricOrbitChartQuotient
-- original header: public import PaperVerification.ToricQuotientFaceCoordinates
-- original header: public import PaperVerification.ToricChartLocalization

-- original header: @[expose] public section

/-!
# The orbit chart is the actual chart of the quotient star

Vanishing on a smooth cone gives the saturated character lattice dual to
the quotient of the normal lattice. The coordinate maps are integral, and
the pairing identity identifies the two actual nonnegative semigroups.
Consequently the orbit quotient is a surjective map of the literal chart
algebras, rather than an assumed description of an orbit closure.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {n : ℕ}

theorem integerPairing_basis_eq_dualCoordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (m : Lattice n) :
    integerPairing (b i) m = (integralDualBasis b).repr m i := by
  simp only [integerPairing,integralDualBasis_repr,mul_comm]

theorem embed_faceTangentLattice
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) :
    embed n (faceTangentLattice b I z) =
      faceTangentReal b I (embed (n-I.card) z) := by
  simp only [faceTangentLattice,faceTangentReal,selectedBasisMap_apply,
    map_sum,embed_int_smul,integralBasisReal_apply]
  rfl

theorem integerPairing_faceTangentLattice
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (u : Lattice n) (z : Lattice (n-I.card)) :
    integerPairing u (faceTangentLattice b I z) =
      integerPairing (coneQuotientLattice b I u) z := by
  have h := faceTangentReal_pairing b I (embed n u) (embed (n-I.card) z)
  rw [← embed_faceTangentLattice,coneQuotient_compatible,
    SmoothCompleteFan.normalRay_pairing_lattice,
    SmoothCompleteFan.normalRay_pairing_lattice] at h
  exact_mod_cast h

def faceCharacterProjection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Lattice n →ₗ[ℤ] Lattice (n-I.card) where
  toFun m j := (integralDualBasis b).repr m (complementaryEmbedding I j)
  map_add' m p := by ext j; simp
  map_smul' a m := by
    ext j
    exact congrArg (fun z : Fin n →₀ ℤ => z (complementaryEmbedding I j))
      ((integralDualBasis b).repr.map_smul a m)

@[simp] theorem faceCharacterProjection_tangent
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) :
    faceCharacterProjection b I (faceTangentLattice b I z) = z := by
  ext j
  exact selectedBasisMap_coordinate (integralDualBasis b) (complementaryEmbedding I) z j

theorem faceTangentLattice_annihilates
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) (u : Lattice n) (hu : u∈I.image b) :
    integerPairing u (faceTangentLattice b I z)=0 := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  rw [integerPairing_basis_eq_dualCoordinate]
  apply selectedBasisMap_coordinate_eq_zero
  simpa only [mem_range_complementaryEmbedding_iff,not_not] using hi

theorem faceTangentLattice_projection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (m : Lattice n) (hm : ∀ u∈I.image b,integerPairing u m=0) :
    faceTangentLattice b I (faceCharacterProjection b I m)=m := by
  apply selectedBasisMap_repr_restrict
  intro i hi
  have hiI : i∈I := by
    simpa only [mem_range_complementaryEmbedding_iff,not_not] using hi
  rw [← integerPairing_basis_eq_dualCoordinate]
  exact hm (b i) (Finset.mem_image.mpr ⟨i,hiI,rfl⟩)

def orbitQuotientCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) : Finset (Lattice (n-I.card)) :=
  (s \ I.image b).image (coneQuotientLattice b I)

theorem faceCharacterProjection_mem_quotientDualCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n))
    (m : orbitCharacterFace s (I.image b)) :
    faceCharacterProjection b I m.val.val ∈ dualConeMonoid (orbitQuotientCone b I s) := by
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  rw [← integerPairing_faceTangentLattice,
    faceTangentLattice_projection b I m.val.val m.property]
  exact m.val.property u (Finset.mem_sdiff.mp hu).1

theorem faceTangentLattice_mem_dualCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (z : dualConeMonoid (orbitQuotientCone b I s)) :
    faceTangentLattice b I z.val ∈ dualConeMonoid s := by
  intro u hu
  by_cases huI : u∈I.image b
  · rw [faceTangentLattice_annihilates b I z.val u huI]
  · rw [integerPairing_faceTangentLattice]
    exact z.property _ (Finset.mem_image.mpr
      ⟨u,Finset.mem_sdiff.mpr ⟨hu,huI⟩,rfl⟩)

/-- The actual saturated semigroup equivalence. It uses no fan
classification, geometry, or positivity hypothesis beyond the semigroups. -/
def orbitQuotientSemigroupEquiv
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    orbitCharacterFace s (I.image b) ≃+ dualConeMonoid (orbitQuotientCone b I s) where
  toFun m := ⟨faceCharacterProjection b I m.val.val,
    faceCharacterProjection_mem_quotientDualCone b I s m⟩
  invFun z := ⟨⟨faceTangentLattice b I z.val,faceTangentLattice_mem_dualCone b I s z⟩,
    faceTangentLattice_annihilates b I z.val⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    exact faceTangentLattice_projection b I m.val.val m.property
  right_inv z := Subtype.ext (faceCharacterProjection_tangent b I z.val)
  map_add' m p := Subtype.ext ((faceCharacterProjection b I).map_add m.val.val p.val.val)

variable (k : Type*) [CommRing k]

def orbitQuotientAlgebraMap
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    monoidChartAlgebra k (dualConeMonoid s) →ₐ[k]
      monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I s)) :=
  (monoidChartAlgebraEquiv k _).toAlgHom.comp
    ((AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)).toAlgHom.comp
      ((additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b) hIs)).comp
          (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.toAlgHom))

theorem orbitQuotientAlgebraMap_surjective
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    Function.Surjective (orbitQuotientAlgebraMap k b I s hIs) :=
  (monoidChartAlgebraEquiv k _).surjective.comp
    ((AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)).surjective.comp
      ((additiveFaceRetraction_surjective k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b) hIs)).comp
          (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.surjective))

theorem orbitQuotientChartMap_isClosedImmersion
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (orbitQuotientAlgebraMap k b I s hIs).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (orbitQuotientAlgebraMap_surjective k b I s hIs)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.orbitQuotientSemigroupEquiv
#print axioms PaperVerification.ToricGeometry.orbitQuotientChartMap_isClosedImmersion
end
end Source_ToricOrbitQuotientCoordinates
-- END ORIGINAL PaperVerification.ToricOrbitQuotientCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricOrbitStarIndex
section Source_ToricOrbitStarIndex

-- original header: module

-- original header: public import PaperVerification.ToricOrbitQuotientCoordinates
-- original header: public import PaperVerification.ToricFanScheme
-- original header: public import Mathlib.CategoryTheory.Limits.Final

-- original header: @[expose] public section

/-! # The actual cone index of an orbit closure and its quotient fan -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

abbrev OrbitConeIndex :=
  {s : Finset (Lattice n) // s∈«Σ».cones ∧ I.image b⊆s}

def orbitConeQuotientIndex (s : «Σ».OrbitConeIndex b I) :
    («Σ».completeQuotientStarFan b I hF).ConeIndex :=
  ⟨orbitQuotientCone b I s.val,(«Σ».mem_quotientStarCones b I _).mpr
    ⟨s.val,s.property.1,s.property.2,rfl⟩⟩

theorem orbitQuotientCone_subset_iff (s t : «Σ».OrbitConeIndex b I) :
    orbitQuotientCone b I s.val ⊆ orbitQuotientCone b I t.val ↔ s.val⊆t.val := by
  constructor
  · intro h u hu
    by_cases huI : u∈I.image b
    · exact t.property.2 huI
    · have hup : coneQuotientLattice b I u∈orbitQuotientCone b I t.val :=
        h (Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨hu,huI⟩,rfl⟩)
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hup
      have huv := «Σ».coneQuotient_injective_star_rays b I s.property.1 t.property.1
        s.property.2 t.property.2 (Finset.mem_sdiff.mpr ⟨hu,huI⟩) hv hvu.symm
      exact huv.symm ▸ (Finset.mem_sdiff.mp hv).1
  · intro h
    exact Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) h)

theorem orbitConeQuotientIndex_injective :
    Function.Injective («Σ».orbitConeQuotientIndex b I hF) := by
  intro s t h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  apply Finset.Subset.antisymm
  · apply («Σ».orbitQuotientCone_subset_iff b I s t).mp
    exact he.le
  · apply («Σ».orbitQuotientCone_subset_iff b I t s).mp
    exact he.symm.le

theorem orbitConeQuotientIndex_surjective :
    Function.Surjective («Σ».orbitConeQuotientIndex b I hF) := by
  intro t
  obtain ⟨s,hs,hIs,ht⟩ := («Σ».mem_quotientStarCones b I t.val).mp t.property
  exact ⟨⟨s,hs,hIs⟩,Subtype.ext ht.symm⟩

/-- This is an order isomorphism of the actual cone sets. In particular it
records all face inclusions, not merely a bijection of maximal cones. -/
def orbitConeOrderIso :
    «Σ».OrbitConeIndex b I ≃o («Σ».completeQuotientStarFan b I hF).ConeIndex where
  toEquiv := Equiv.ofBijective («Σ».orbitConeQuotientIndex b I hF)
    ⟨«Σ».orbitConeQuotientIndex_injective b I hF,
      «Σ».orbitConeQuotientIndex_surjective b I hF⟩
  map_rel_iff' := by
    intro s t
    exact «Σ».orbitQuotientCone_subset_iff b I s t

@[simp] theorem orbitConeOrderIso_apply (s : «Σ».OrbitConeIndex b I) :
    («Σ».orbitConeOrderIso b I hF s).val = orbitQuotientCone b I s.val := rfl

variable (k : Type*) [CommRing k]

/-- The quotient fan's actual affine chart diagram, indexed instead by
the original cones containing the orbit cone. -/
def orbitChartDiagram : «Σ».OrbitConeIndex b I ⥤ Scheme :=
  («Σ».orbitConeOrderIso b I hF).equivalence.functor ⋙
    («Σ».completeQuotientStarFan b I hF).coneDiagram k

instance orbitChartDiagram_hasColimit : HasColimit («Σ».orbitChartDiagram b I hF k) := by
  exact inferInstanceAs (HasColimit
    ((«Σ».orbitConeOrderIso b I hF).equivalence.functor ⋙
      («Σ».completeQuotientStarFan b I hF).coneDiagram k))

def orbitChartColimit : Scheme := colimit («Σ».orbitChartDiagram b I hF k)

/-- Reindexing changes no glued scheme. The isomorphism follows from the
actual categorical colimit and an equivalence of its indexing categories. -/
def orbitChartColimitIsoFan :
    «Σ».orbitChartColimit b I hF k ≅ («Σ».completeQuotientStarFan b I hF).fanScheme k :=
  Functor.Final.colimitIso («Σ».orbitConeOrderIso b I hF).equivalence.functor
    ((«Σ».completeQuotientStarFan b I hF).coneDiagram k)

@[reassoc (attr := simp)] theorem orbitChartColimitIsoFan_ι
    (s : «Σ».OrbitConeIndex b I) :
    colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫
      («Σ».orbitChartColimitIsoFan b I hF k).hom =
        («Σ».completeQuotientStarFan b I hF).fanChartMap k
          («Σ».orbitConeQuotientIndex b I hF s) :=
  Functor.Final.ι_colimitIso_hom _ _ s

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitConeOrderIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitChartColimitIsoFan
end
end Source_ToricOrbitStarIndex
-- END ORIGINAL PaperVerification.ToricOrbitStarIndex


-- BEGIN ORIGINAL PaperVerification.ToricOrbitChartMaps
section Source_ToricOrbitChartMaps

-- original header: module

-- original header: public import PaperVerification.ToricOrbitStarIndex

-- original header: @[expose] public section

/-! # Naturality and gluing of actual orbit chart quotient morphisms -/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped Classical

variable (k : Type*) [CommRing k] {M : Type*} [AddCommGroup M]

@[simp] theorem monoidChartAlgebraEquiv_single_character
    (S : AddSubmonoid M) (m : S) :
    monoidChartAlgebraEquiv k S (single m 1) = chartCharacter k S m.val m.property :=
  Subtype.ext (monoidChartMap_single k S m 1)

@[simp] theorem monoidChartAlgebraEquiv_symm_character
    (S : AddSubmonoid M) (m : M) (hm : m∈S) :
    (monoidChartAlgebraEquiv k S).symm (chartCharacter k S m hm) = single ⟨m,hm⟩ 1 := by
  apply (monoidChartAlgebraEquiv k S).injective
  simp only [AlgEquiv.apply_symm_apply,monoidChartAlgebraEquiv_single_character]

theorem chartAlgHom_ext_characters (S : AddSubmonoid M)
    {A : Type*} [Semiring A] [Algebra k A]
    (F G : monoidChartAlgebra k S →ₐ[k] A)
    (h : ∀ m (hm : m∈S),F (chartCharacter k S m hm)=G (chartCharacter k S m hm)) :
    F=G := by
  ext f
  obtain ⟨g,rfl⟩ := (monoidChartAlgebraEquiv k S).surjective f
  induction g using AddMonoidAlgebra.induction_on with
  | of m =>
      simpa only [AddMonoidAlgebra.of_apply,toAdd_ofAdd,monoidChartAlgebraEquiv_single_character] using
        h m.val m.property
  | add f g hf hg => simp only [map_add,hf,hg]
  | smul a f hf => simp only [map_smul,hf]

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} (k : Type*) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

theorem orbitQuotientAlgebraMap_character
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) (m : Lattice n)
    (hm : m∈dualConeMonoid s) :
    ((orbitQuotientAlgebraMap k b I s hIs (chartCharacter k (dualConeMonoid s) m hm) :
        monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I s))) :
          AddMonoidAlgebra k (Lattice (n-I.card))) =
      if h : ∀ u∈I.image b,integerPairing u m=0
      then single (faceCharacterProjection b I m) 1 else 0 := by
  simp only [orbitQuotientAlgebraMap,AlgHom.comp_apply,AlgEquiv.coe_algHom,
    monoidChartAlgebraEquiv_symm_character]
  by_cases h : ∀ u∈I.image b,integerPairing u m=0
  · have hmem : (⟨m,hm⟩ : dualConeMonoid s)∈orbitCharacterFace s (I.image b) := h
    rw [additiveFaceRetraction_single_of_mem k _ _ _ hmem,
      AddMonoidAlgebra.domCongr_single,dif_pos h]
    exact monoidChartMap_single k _ _ 1
  · have hmem : (⟨m,hm⟩ : dualConeMonoid s)∉orbitCharacterFace s (I.image b) := h
    rw [additiveFaceRetraction_single_of_not_mem k _ _ _ hmem,map_zero,map_zero,dif_neg h]
    rfl

theorem orbitQuotientCone_mono {s t : Finset (Lattice n)} (hts : t⊆s) :
    orbitQuotientCone b I t ⊆ orbitQuotientCone b I s :=
  Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) hts)

/-- Restriction along an actual cone face commutes with killing the
characters positive on the orbit cone. -/
theorem orbitQuotientAlgebraMap_naturality
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t) :
    (orbitQuotientAlgebraMap k b I t hIt).comp
        (monoidChartInclusion k (dualConeMonoid_antitone hts)) =
      (monoidChartInclusion k (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))).comp
        (orbitQuotientAlgebraMap k b I s (hIt.trans hts)) := by
  apply chartAlgHom_ext_characters
  intro m hm
  apply Subtype.ext
  simp only [AlgHom.comp_apply,monoidChartInclusion_character,
    monoidChartInclusion_coe,orbitQuotientAlgebraMap_character]

def orbitQuotientChartMap (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    coneChart k (orbitQuotientCone b I s) ⟶ coneChart k s :=
  Spec.map (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I s hIs).toRingHom)

instance orbitQuotientChartMap_closed (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    IsClosedImmersion (orbitQuotientChartMap k b I s hIs) :=
  orbitQuotientChartMap_isClosedImmersion k b I s hIs

set_option maxHeartbeats 2000000 in
@[reassoc] theorem orbitQuotientChartMap_naturality
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t) :
    coneChartFaceMap k (orbitQuotientCone_mono b I hts) ≫
        orbitQuotientChartMap k b I s (hIt.trans hts) =
      orbitQuotientChartMap k b I t hIt ≫ coneChartFaceMap k hts := by
  exact (Spec.map_comp
    (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I s (hIt.trans hts)).toRingHom)
    (CommRingCat.ofHom (monoidChartInclusion k
      (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))).toRingHom)).symm.trans
    ((congrArg (fun f : monoidChartAlgebra k (dualConeMonoid s) →ₐ[k]
        monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I t)) =>
          Spec.map (CommRingCat.ofHom f.toRingHom))
      (orbitQuotientAlgebraMap_naturality k b I hts hIt).symm).trans
      (Spec.map_comp
        (CommRingCat.ofHom (monoidChartInclusion k (dualConeMonoid_antitone hts)).toRingHom)
        (CommRingCat.ofHom (orbitQuotientAlgebraMap k b I t hIt).toRingHom)))

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (hF : I.image b∈«Σ».cones)

/-- The actual quotient charts map compatibly into the actual fan scheme. -/
def orbitClosureCocone : Cocone («Σ».orbitChartDiagram b I hF k) where
  pt := «Σ».fanScheme k
  ι :=
    { app s := orbitQuotientChartMap k b I s.val s.property.2 ≫
        «Σ».fanChartMap k ⟨s.val,s.property.1⟩
      naturality := by
        intro s t f
        change coneChartFaceMap k (orbitQuotientCone_mono b I (leOfHom f)) ≫
          (orbitQuotientChartMap k b I t.val t.property.2 ≫
            «Σ».fanChartMap k ⟨t.val,t.property.1⟩) =
          (orbitQuotientChartMap k b I s.val s.property.2 ≫
            «Σ».fanChartMap k ⟨s.val,s.property.1⟩) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc,
          orbitQuotientChartMap_naturality k b I (leOfHom f) s.property.2,
          Category.assoc]
        exact congrArg
          (fun q => orbitQuotientChartMap k b I s.val s.property.2 ≫ q)
          («Σ».fanChartMap_naturality k
            (s := ⟨s.val, s.property.1⟩) (t := ⟨t.val, t.property.1⟩)
            (leOfHom f)) }

/-- The global morphism from the actual quotient-star scheme. Closedness
and its identification with the invariant orbit closure are proved using
the actual local quotient squares; they are not included in this definition. -/
def orbitClosureMap :
    («Σ».completeQuotientStarFan b I hF).fanScheme k ⟶ «Σ».fanScheme k :=
  («Σ».orbitChartColimitIsoFan b I hF k).inv ≫
    colimit.desc («Σ».orbitChartDiagram b I hF k) («Σ».orbitClosureCocone k b I hF)

@[reassoc (attr := simp)] theorem orbitClosureMap_chart
    (s : «Σ».OrbitConeIndex b I) :
    («Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s) ≫ «Σ».orbitClosureMap k b I hF =
      orbitQuotientChartMap k b I s.val s.property.2 ≫
        «Σ».fanChartMap k ⟨s.val,s.property.1⟩ := by
  rw [← «Σ».orbitChartColimitIsoFan_ι b I hF k s]
  change (colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫
      («Σ».orbitChartColimitIsoFan b I hF k).hom) ≫
    («Σ».orbitChartColimitIsoFan b I hF k).inv ≫
      colimit.desc («Σ».orbitChartDiagram b I hF k) («Σ».orbitClosureCocone k b I hF) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫ q)
      (Iso.hom_inv_id_assoc («Σ».orbitChartColimitIsoFan b I hF k)
        (colimit.desc («Σ».orbitChartDiagram b I hF k)
          («Σ».orbitClosureCocone k b I hF)))).trans
      (colimit.ι_desc («Σ».orbitClosureCocone k b I hF) s))

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.orbitQuotientAlgebraMap_naturality
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_chart
end
end Source_ToricOrbitChartMaps
-- END ORIGINAL PaperVerification.ToricOrbitChartMaps


-- BEGIN ORIGINAL PaperVerification.ToricOrbitFacePullbacks
section Source_ToricOrbitFacePullbacks

-- original header: module

-- original header: public import PaperVerification.ToricOrbitChartMaps

-- original header: @[expose] public section

/-!
# Actual pullback squares for orbit charts

The denominator removing a smooth cone face has pairing zero on the
retained rays and pairing one on the removed rays. If the orbit cone is
retained, the denominator descends to precisely the quotient-star face
denominator. If an orbit ray is removed, that denominator is killed by
the orbit quotient, so the preimage of the face chart is empty.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical BigOperators

variable {n : ℕ}

theorem integerPairing_neg (u m : Lattice n) :
    integerPairing u (-m) = -integerPairing u m := by
  simp [integerPairing]

theorem integerPairing_nsmul (u m : Lattice n) (N : ℕ) :
    integerPairing u (N • m) = (N : ℤ) * integerPairing u m := by
  simp only [integerPairing,Pi.smul_apply,nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

theorem exists_face_character_denominator_exact
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (hts : t⊆s) :
    ∃ v : Lattice n, v∈dualConeMonoid s ∧ -v∈dualConeMonoid t ∧
      (∀ u∈s,integerPairing u v=if u∈t then 0 else 1) ∧
      (∀ m∈dualConeMonoid t,∃ N : ℕ,m+N • v∈dualConeMonoid s) := by
  obtain ⟨b,J,rfl⟩ := «Σ».smooth s hs
  let I := basisRayIndices b t
  have hI : I.image b=t := image_basisRayIndices b t
    (hts.trans (Finset.image_subset_image (Finset.subset_univ J)))
  have hIJ : I⊆J := by
    intro i hi
    have hbi : b i∈t := hI ▸ Finset.mem_image.mpr ⟨i,hi,rfl⟩
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp (hts hbi)
    exact b.injective hji ▸ hj
  let v := faceDenominatorExponent (integralDualBasis b) I J
  refine ⟨v,?_,?_,?_,?_⟩
  · rw [dualConeMonoid_basis_eq]
    exact faceDenominatorExponent_mem (integralDualBasis b) I J
  · rw [← hI,dualConeMonoid_basis_eq]
    exact neg_faceDenominatorExponent_mem (integralDualBasis b) I J
  · intro u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate,faceDenominatorExponent_repr]
    have hbit : b i∈t ↔ i∈I := by simp [I,basisRayIndices]
    by_cases hiI : i∈I
    · simp [hiI,hbit.mpr hiI]
    · have hnot : b i∉t := fun h => hiI (hbit.mp h)
      simp [hi,hiI,hnot]
  · intro m hm
    rw [← hI,dualConeMonoid_basis_eq] at hm
    obtain ⟨N,hN⟩ := faceDenominatorExponent_clears (integralDualBasis b) hIJ m hm
    exact ⟨N,(dualConeMonoid_basis_eq b J).symm ▸ hN⟩

end SmoothCompleteFan

variable (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

theorem projected_face_denominator
    {s t : Finset (Lattice n)} (hts : t⊆s) (hIt : I.image b⊆t)
    (v : Lattice n) (hv : v∈dualConeMonoid s) (hnv : -v∈dualConeMonoid t)
    (hzero : ∀ u∈I.image b,integerPairing u v=0)
    (hclear : ∀ m∈dualConeMonoid t,∃ N : ℕ,m+N • v∈dualConeMonoid s) :
    faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I s) ∧
      -faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I t) ∧
      ∀ m∈dualConeMonoid (orbitQuotientCone b I t),∃ N : ℕ,
        m+N • faceCharacterProjection b I v∈dualConeMonoid (orbitQuotientCone b I s) := by
  refine ⟨faceCharacterProjection_mem_quotientDualCone b I s ⟨⟨v,hv⟩,hzero⟩,?_,?_⟩
  · have hzneg : ∀ u∈I.image b,integerPairing u (-v)=0 := by
      intro u hu
      rw [integerPairing_neg,hzero u hu,neg_zero]
    simpa only [map_neg] using
      faceCharacterProjection_mem_quotientDualCone b I t ⟨⟨-v,hnv⟩,hzneg⟩
  · intro m hm
    have hlift := faceTangentLattice_mem_dualCone b I t ⟨m,hm⟩
    obtain ⟨N,hN⟩ := hclear (faceTangentLattice b I m) hlift
    have hz : ∀ u∈I.image b,
        integerPairing u (faceTangentLattice b I m+N • v)=0 := by
      intro u hu
      rw [integerPairing_add,faceTangentLattice_annihilates b I m u hu,
        integerPairing_nsmul,hzero u hu,mul_zero,zero_add]
    have hproj := faceCharacterProjection_mem_quotientDualCone b I s
      ⟨⟨faceTangentLattice b I m+N • v,hN⟩,hz⟩
    exact ⟨N,by simpa only [map_add,map_nsmul,faceCharacterProjection_tangent] using hproj⟩

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (k : Type*) [CommRing k]

theorem orbitQuotientChart_face_isPullback
    {s t : Finset (Lattice n)} (hs : s∈«Σ».cones) (hts : t⊆s)
    (hIt : I.image b⊆t) :
    IsPullback (orbitQuotientChartMap k b I t hIt)
      (coneChartFaceMap k (orbitQuotientCone_mono b I hts))
      (coneChartFaceMap k hts)
      (orbitQuotientChartMap k b I s (hIt.trans hts)) := by
  obtain ⟨v,hv,hnv,hpair,hclear⟩ :=
    «Σ».exists_face_character_denominator_exact s t hs hts
  have hzero : ∀ u∈I.image b,integerPairing u v=0 := by
    intro u hu
    rw [hpair u (hts (hIt hu)),if_pos (hIt hu)]
  obtain ⟨hp,hnp,hpclear⟩ := projected_face_denominator b I hts hIt v hv hnv hzero hclear
  let hloc := monoidChartInclusion_isLocalizationMap k (dualConeMonoid_antitone hts)
    v hv hnv hclear
  let hploc := monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
    (faceCharacterProjection b I v) hp hnp hpclear
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
    (faceCharacterProjection b I v) hp hploc
  letI : IsOpenImmersion (coneChartFaceMap k hts) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone hts) v hv hloc
  letI : IsOpenImmersion (coneChartFaceMap k (orbitQuotientCone_mono b I hts)) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
      (faceCharacterProjection b I v) hp hploc
  apply IsOpenImmersion.isPullback
  · exact orbitQuotientChartMap_naturality k b I hts hIt
  · rw [show (coneChartFaceMap k hts).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) from
      monoidChartSpecMap_opensRange_of_isLocalizationMap k
        (dualConeMonoid_antitone hts) v hv hloc]
    rw [show (coneChartFaceMap k (orbitQuotientCone_mono b I hts)).opensRange =
        PrimeSpectrum.basicOpen (chartCharacter k
          (dualConeMonoid (orbitQuotientCone b I s)) (faceCharacterProjection b I v) hp) from
      monoidChartSpecMap_opensRange_of_isLocalizationMap k
        (dualConeMonoid_antitone (orbitQuotientCone_mono b I hts))
        (faceCharacterProjection b I v) hp hploc]
    change PrimeSpectrum.basicOpen
        (orbitQuotientAlgebraMap k b I s (hIt.trans hts)
          (chartCharacter k (dualConeMonoid s) v hv)) =
      PrimeSpectrum.basicOpen (chartCharacter k
        (dualConeMonoid (orbitQuotientCone b I s)) (faceCharacterProjection b I v) hp)
    apply congrArg PrimeSpectrum.basicOpen
    apply Subtype.ext
    rw [orbitQuotientAlgebraMap_character,dif_pos hzero]
    rfl

/-- A cone face omitting an orbit ray has empty preimage in the orbit
chart. This is proved by the literal denominator being mapped to zero. -/
theorem orbitQuotientChart_preimage_face_empty
    {s t : Finset (Lattice n)} (hs : s∈«Σ».cones) (hts : t⊆s)
    (hIs : I.image b⊆s) (hnot : ¬I.image b⊆t) :
    (orbitQuotientChartMap k b I s hIs) ⁻¹ᵁ
      ((coneChartFaceMap k hts).opensRange
        (H := «Σ».coneChartFaceMap_isOpenImmersion k s t hs hts)) = ⊥ := by
  letI : IsOpenImmersion (coneChartFaceMap k hts) :=
    «Σ».coneChartFaceMap_isOpenImmersion k s t hs hts
  obtain ⟨v,hv,hnv,hpair,hclear⟩ :=
    «Σ».exists_face_character_denominator_exact s t hs hts
  have hnonzero : ¬∀ u∈I.image b,integerPairing u v=0 := by
    intro h
    apply hnot
    intro u hu
    by_contra hut
    have he := hpair u (hIs hu)
    rw [if_neg hut,h u hu] at he
    norm_num at he
  let hloc := monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hnv hclear
  letI := monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
    (dualConeMonoid_antitone hts) v hv hloc
  rw [show (coneChartFaceMap k hts).opensRange =
      PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) v hv) from
    monoidChartSpecMap_opensRange_of_isLocalizationMap k
      (dualConeMonoid_antitone hts) v hv hloc]
  change PrimeSpectrum.basicOpen (orbitQuotientAlgebraMap k b I s hIs
    (chartCharacter k (dualConeMonoid s) v hv)) = ⊥
  have hmap : orbitQuotientAlgebraMap k b I s hIs
      (chartCharacter k (dualConeMonoid s) v hv)=0 := by
    apply Subtype.ext
    rw [orbitQuotientAlgebraMap_character,dif_neg hnonzero]
    rfl
  rw [hmap,PrimeSpectrum.basicOpen_zero]

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitQuotientChart_face_isPullback
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitQuotientChart_preimage_face_empty
end
end Source_ToricOrbitFacePullbacks
-- END ORIGINAL PaperVerification.ToricOrbitFacePullbacks


-- BEGIN ORIGINAL PaperVerification.ToricOrbitClosedImmersion
section Source_ToricOrbitClosedImmersion

-- original header: module

-- original header: public import PaperVerification.ToricOrbitFacePullbacks
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

-- original header: @[expose] public section

/-!
# The quotient-star scheme is an actual closed subscheme

The global map constructed from the actual semigroup quotient maps is a
closed immersion. Its pullback over a cone containing the orbit cone is
exactly the corresponding quotient chart, as a scheme-theoretic pullback.
Its preimage over every other cone is empty. These facts are proved from
the real fan intersection identity and the explicit localizations.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

theorem orbitChart_jointly_surjective
    (x : («Σ».completeQuotientStarFan b I hF).fanScheme k) :
    ∃ (s : «Σ».OrbitConeIndex b I) (y : coneChart k (orbitQuotientCone b I s.val)),
      («Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s) y=x := by
  obtain ⟨t,y,hy⟩ := («Σ».completeQuotientStarFan b I hF).fanChartMap_jointly_surjective k x
  obtain ⟨s,hs⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
  subst t
  exact ⟨s,y,hy⟩

theorem orbitClosureMap_preimage_chart_empty (t : «Σ».ConeIndex)
    (hnot : ¬I.image b⊆t.val) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ («Σ».fanChartMap k t).opensRange = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨s,y,rfl⟩ := «Σ».orbitChart_jointly_surjective k b I hF x
  obtain ⟨z,hz⟩ := hx
  have heq : «Σ».fanChartMap k ⟨s.val,s.property.1⟩
        (orbitQuotientChartMap k b I s.val s.property.2 y) = «Σ».fanChartMap k t z := by
    rw [← Scheme.Hom.comp_apply]
    rw [← «Σ».orbitClosureMap_chart k b I hF s]
    exact hz.symm
  obtain ⟨w,hws,hwt⟩ := («Σ».fanChartMap_eq_iff k
    ⟨s.val,s.property.1⟩ t _ z).mp heq
  letI : IsOpenImmersion
      (coneChartFaceMap k (Finset.inter_subset_left : s.val ∩ t.val ⊆ s.val)) :=
    «Σ».coneChartFaceMap_isOpenImmersion k s.val (s.val ∩ t.val)
      s.property.1 Finset.inter_subset_left
  have hface : orbitQuotientChartMap k b I s.val s.property.2 y∈
      (coneChartFaceMap k (Finset.inter_subset_left : s.val∩t.val⊆s.val)).opensRange :=
    ⟨w,hws⟩
  have hnotInter : ¬I.image b⊆s.val∩t.val := fun h => hnot
    (h.trans Finset.inter_subset_right)
  have hempty := «Σ».orbitQuotientChart_preimage_face_empty b I k s.property.1
    (Finset.inter_subset_left : s.val∩t.val⊆s.val) s.property.2 hnotInter
  have hy : y∈(orbitQuotientChartMap k b I s.val s.property.2) ⁻¹ᵁ
      (coneChartFaceMap k (Finset.inter_subset_left : s.val∩t.val⊆s.val)).opensRange := hface
  rw [hempty] at hy
  exact hy

theorem orbitClosureMap_preimage_chart (t : «Σ».OrbitConeIndex b I) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
        («Σ».fanChartMap k ⟨t.val,t.property.1⟩).opensRange =
      ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF t)).opensRange := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  ext x
  constructor
  · intro hx
    obtain ⟨s,y,rfl⟩ := «Σ».orbitChart_jointly_surjective k b I hF x
    obtain ⟨z,hz⟩ := hx
    have heq : «Σ».fanChartMap k ⟨s.val,s.property.1⟩
          (orbitQuotientChartMap k b I s.val s.property.2 y) =
        «Σ».fanChartMap k ⟨t.val,t.property.1⟩ z := by
      rw [← Scheme.Hom.comp_apply,← «Σ».orbitClosureMap_chart k b I hF s]
      exact hz.symm
    obtain ⟨w,hws,hwt⟩ := («Σ».fanChartMap_eq_iff k
      ⟨s.val,s.property.1⟩ ⟨t.val,t.property.1⟩ _ z).mp heq
    let u : «Σ».OrbitConeIndex b I :=
      ⟨s.val∩t.val,«Σ».downward s.val s.property.1 _ Finset.inter_subset_left,
        Finset.subset_inter s.property.2 t.property.2⟩
    have H := «Σ».orbitQuotientChart_face_isPullback b I k s.property.1
      (Finset.inter_subset_left : u.val⊆s.val) u.property.2
    letI := «Σ».coneChartFaceMap_isOpenImmersion k s.val u.val
      s.property.1 Finset.inter_subset_left
    have hy : y∈Set.range (pullback.snd
        (coneChartFaceMap k (Finset.inter_subset_left : u.val⊆s.val))
        (orbitQuotientChartMap k b I s.val s.property.2)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact ⟨w,hws⟩
    obtain ⟨p,hp⟩ := hy
    let r := H.isoPullback.inv p
    have hr : coneChartFaceMap k
        (orbitQuotientCone_mono b I (Finset.inter_subset_left : u.val⊆s.val)) r = y :=
      (congrArg (fun f => f p) H.isoPullback_inv_snd).trans hp
    refine ⟨coneChartFaceMap k
      (orbitQuotientCone_mono b I (Finset.inter_subset_right : u.val⊆t.val)) r,?_⟩
    have htmap := Γ.fanChartMap_naturality k
      (s := «Σ».orbitConeQuotientIndex b I hF u)
      (t := «Σ».orbitConeQuotientIndex b I hF t)
      (orbitQuotientCone_mono b I (Finset.inter_subset_right : u.val ⊆ t.val))
    have hsmap := Γ.fanChartMap_naturality k
      (s := «Σ».orbitConeQuotientIndex b I hF u)
      (t := «Σ».orbitConeQuotientIndex b I hF s)
      (orbitQuotientCone_mono b I (Finset.inter_subset_left : u.val ⊆ s.val))
    exact (congrArg (fun f => f r) htmap).trans
      ((congrArg (fun f => f r) hsmap).symm.trans
        (congrArg (Γ.fanChartMap k («Σ».orbitConeQuotientIndex b I hF s)) hr))
  · rintro ⟨y,rfl⟩
    refine ⟨orbitQuotientChartMap k b I t.val t.property.2 y,?_⟩
    exact (congrArg (fun f => f y) («Σ».orbitClosureMap_chart k b I hF t)).symm

/-- The quotient chart is the actual scheme-theoretic pullback of the
corresponding ambient chart. -/
theorem orbitClosureMap_chart_isPullback (t : «Σ».OrbitConeIndex b I) :
    IsPullback (orbitQuotientChartMap k b I t.val t.property.2)
      ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF t))
      («Σ».fanChartMap k ⟨t.val,t.property.1⟩) («Σ».orbitClosureMap k b I hF) := by
  exact @IsOpenImmersion.isPullback
    (coneChart k (orbitQuotientCone b I t.val)) (coneChart k t.val)
    ((«Σ».completeQuotientStarFan b I hF).fanScheme k) («Σ».fanScheme k)
    (orbitQuotientChartMap k b I t.val t.property.2)
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
      («Σ».orbitConeQuotientIndex b I hF t))
    («Σ».fanChartMap k ⟨t.val,t.property.1⟩) («Σ».orbitClosureMap k b I hF)
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap_isOpenImmersion k
      («Σ».orbitConeQuotientIndex b I hF t))
    («Σ».fanChartMap_isOpenImmersion k ⟨t.val,t.property.1⟩)
    («Σ».orbitClosureMap_chart k b I hF t)
    («Σ».orbitClosureMap_preimage_chart k b I hF t)

/-- Closedness is checked on the actual ambient affine open cover. -/
instance orbitClosureMap_isClosedImmersion :
    IsClosedImmersion («Σ».orbitClosureMap k b I hF) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    («Σ».fanSchemeOpenCover k)]
  intro t
  let t₀ : «Σ».ConeIndex := t
  letI : IsOpenImmersion («Σ».fanChartMap k t₀) :=
    «Σ».fanChartMap_isOpenImmersion k t₀
  change IsClosedImmersion
    (pullback.snd («Σ».orbitClosureMap k b I hF) («Σ».fanChartMap k t₀))
  by_cases hIt : I.image b ⊆ t₀.val
  · let t' : «Σ».OrbitConeIndex b I := ⟨t₀.val, t₀.property, hIt⟩
    have H := «Σ».orbitClosureMap_chart_isPullback k b I hF t'
    have hc : IsClosedImmersion
        (H.flip.isoPullback.inv ≫ orbitQuotientChartMap k b I t'.val t'.property.2) :=
      inferInstance
    exact Eq.mp (congrArg (fun f => IsClosedImmersion f) H.flip.isoPullback_inv_snd) hc
  · letI : IsEmpty ↥(pullback («Σ».orbitClosureMap k b I hF)
        («Σ».fanChartMap k t₀) : Scheme) := by
      apply Scheme.isEmpty_pullback
      apply Set.disjoint_left.mpr
      rintro x ⟨y,rfl⟩ hx
      have hy : y∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
          («Σ».fanChartMap k t₀).opensRange := hx
      rw [«Σ».orbitClosureMap_preimage_chart_empty k b I hF t₀ hIt] at hy
      exact hy
    infer_instance

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_isClosedImmersion
end
end Source_ToricOrbitClosedImmersion
-- END ORIGINAL PaperVerification.ToricOrbitClosedImmersion


-- BEGIN ORIGINAL PaperVerification.ToricOrbitCartierCoefficients
section Source_ToricOrbitCartierCoefficients

-- original header: module

-- original header: public import PaperVerification.ToricOrbitClosedImmersion
-- original header: public import PaperVerification.ToricQuotientFaceSupport
-- original header: public import PaperVerification.ToricFanIntegralCoefficients
-- original header: public import PaperVerification.ToricPrincipalChartModules

-- original header: @[expose] public section

/-!
# Cartier equations on an actual quotient-star orbit closure

A common integral character is used to normalize all local generators
along the orbit cone. The normalized characters lie in its actual
annihilator lattice. Their projections are proved to be the Cartier
characters of the quotient fan, and actual transition units are mapped
by the previously constructed surjective chart homomorphisms.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

def orbitRestrictionCoefficients (a : Lattice n→ℤ) (m₀ : Lattice n) :
    Lattice (n-I.card)→ℤ := fun u =>
  if hu : u∈(«Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u,hu⟩)+
      integerPairing («Σ».starRayLift b I hF ⟨u,hu⟩) m₀
  else 0

theorem orbitRestrictionCoefficients_projected (a : Lattice n→ℤ) (m₀ : Lattice n)
    {s : Finset (Lattice n)} (hs : s∈«Σ».cones) (hIs : I.image b⊆s)
    {u : Lattice n} (hu : u∈s\I.image b) :
    «Σ».orbitRestrictionCoefficients b I hF a m₀ (coneQuotientLattice b I u) =
      a u+integerPairing u m₀ := by
  have hp := «Σ».projected_starRay_mem b I hF hs hIs hu
  simp only [orbitRestrictionCoefficients,dif_pos hp]
  rw [«Σ».starRayLift_projected b I hF hs hIs hu]

def orbitFullConeIndex (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    («Σ».completeQuotientStarFan b I hF).fullCones :=
  ⟨orbitQuotientCone b I s.val,Finset.mem_filter.mpr ⟨
    («Σ».mem_quotientStarCones b I _).mpr ⟨s.val,«Σ».fullCones_mem s,hIs,rfl⟩,by
      have himage : (orbitQuotientCone b I s.val).card=(s.val\I.image b).card := by
        apply Finset.card_image_of_injOn
        intro v hv w hw he
        exact «Σ».coneQuotient_injective_star_rays b I
          («Σ».fullCones_mem s) («Σ».fullCones_mem s) hIs hIs hv hw he
      rw [himage,Finset.card_sdiff_of_subset hIs,
        Finset.card_image_of_injective I b.injective,«Σ».fullCones_card]⟩⟩

theorem orbit_normalized_character_annihilates (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    ∀ u∈I.image b,integerPairing u («Σ».cartierLatticePoint a s-m₀)=0 := by
  intro u hu
  rw [integerPairing_sub,«Σ».cartierLatticePoint_pairing a s u (hIs hu),hm₀ u hu,sub_self]

/-- Projected local equations are uniquely the actual Cartier equations
of the quotient fan. -/
theorem orbit_cartierLatticePoint (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    faceCharacterProjection b I («Σ».cartierLatticePoint a s-m₀) =
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀)
        («Σ».orbitFullConeIndex b I hF s hIs) := by
  apply («Σ».completeQuotientStarFan b I hF).eq_cartierLatticePoint_of_pairings
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  rw [← integerPairing_faceTangentLattice,
    faceTangentLattice_projection b I _
      («Σ».orbit_normalized_character_annihilates b I a m₀ hm₀ s hIs),
    integerPairing_sub,
    «Σ».cartierLatticePoint_pairing a s u (Finset.mem_sdiff.mp hu).1,
    «Σ».orbitRestrictionCoefficients_projected b I hF a m₀ («Σ».fullCones_mem s) hIs hu]
  ring

theorem orbit_cartier_difference (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val) :
    faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) =
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) («Σ».orbitFullConeIndex b I hF s hIs) -
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) («Σ».orbitFullConeIndex b I hF t hIt) := by
  rw [← «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ s hIs,
    ← «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ t hIt,← map_sub]
  congr 1
  abel

theorem orbitQuotientCone_inter (s t : «Σ».OrbitConeIndex b I) :
    orbitQuotientCone b I (s.val∩t.val) =
      orbitQuotientCone b I s.val∩orbitQuotientCone b I t.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_sdiff.mp hu with ⟨hut,huI⟩
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hut).1,huI⟩,rfl⟩,
      Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hut).2,huI⟩,rfl⟩⟩
  · intro hv
    obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).1
    obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).2
    have huw := «Σ».coneQuotient_injective_star_rays b I s.property.1 t.property.1
      s.property.2 t.property.2 hu hw (huv.trans hwv.symm)
    subst w
    exact Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1,(Finset.mem_sdiff.mp hw).1⟩,
        (Finset.mem_sdiff.mp hu).2⟩,huv⟩

variable (k : Type*) [CommRing k]

/-- The exact regular transition character is sent to its projected
character by the actual closed-immersion chart algebra homomorphism. -/
theorem orbit_cartierTransition_character (a : Lattice n→ℤ)
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val) :
    ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
      («Σ».cartierTransitionUnit k a s t :
        monoidChartAlgebra k (dualConeMonoid (s.val∩t.val)))) :
          AddMonoidAlgebra k (Lattice (n-I.card))) =
      AddMonoidAlgebra.single
        (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) 1 := by
  have hz : ∀ u∈I.image b,
      integerPairing u («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)=0 := by
    intro u hu
    rw [integerPairing_sub,«Σ».cartierLatticePoint_pairing a s u (hIs hu),
      «Σ».cartierLatticePoint_pairing a t u (hIt hu),sub_self]
  change ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
    (chartCharacter k (dualConeMonoid (s.val∩t.val))
      («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)
      («Σ».cartier_difference_mem_overlap a s t).1)) :
        AddMonoidAlgebra k (Lattice (n-I.card))) = _
  rw [orbitQuotientAlgebraMap_character,dif_pos hz]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_cartierLatticePoint
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_cartierTransition_character
end
end Source_ToricOrbitCartierCoefficients
-- END ORIGINAL PaperVerification.ToricOrbitCartierCoefficients


-- BEGIN ORIGINAL PaperVerification.ToricOrbitCartierRestriction
section Source_ToricOrbitCartierRestriction

-- original header: module

-- original header: public import PaperVerification.ToricFanCartierCocycle

-- original header: public import PaperVerification.ToricOrbitCartierCoefficients
-- original header: public import PaperVerification.ToricDominantCartierPullback
-- original header: public import PaperVerification.ToricAffinePullbackSections

-- original header: @[expose] public section

/-!
# Actual restriction of a Cartier sheaf to an orbit closure

The normalized local characters define an actual fractional sheaf on the
quotient-star scheme. The original transition functions are regular on
their overlaps and are pulled through the actual affine quotient maps.
The independent local-frame universal property then identifies this
fractional sheaf with Mathlib's ordinary module-sheaf pullback.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fanChartMap_inter_opensRange (s t : «Σ».ConeIndex) :
    («Σ».fanChartMap k
      ⟨s.val∩t.val,«Σ».downward s.val s.property _ Finset.inter_subset_left⟩).opensRange =
      («Σ».fanChartMap k s).opensRange⊓(«Σ».fanChartMap k t).opensRange := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    constructor
    · refine ⟨coneChartFaceMap k Finset.inter_subset_left z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_left)
    · refine ⟨coneChartFaceMap k Finset.inter_subset_right z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_right)
  · rintro ⟨⟨ys,hys⟩,⟨yt,hyt⟩⟩
    obtain ⟨z,hzs,hzt⟩ := («Σ».fanChartMap_eq_iff k s t ys yt).mp (hys.trans hyt.symm)
    refine ⟨z,?_⟩
    rw [← «Σ».fanChartMap_naturality k Finset.inter_subset_left]
    change «Σ».fanChartMap k s (coneChartFaceMap k Finset.inter_subset_left z)=x
    rw [hzs,hys]

variable (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

theorem orbit_preimage_fullChart_forces (s : «Σ».fullCones)
    (x : («Σ».completeQuotientStarFan b I hF).fanScheme k)
    (hx : x∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k s) :
    I.image b⊆s.val := by
  by_contra hn
  have he := «Σ».orbitClosureMap_preimage_chart_empty k b I hF («Σ».fullConeIndex s) hn
  change x∈(«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ
    («Σ».fanChartMap k («Σ».fullConeIndex s)).opensRange at hx
  rw [he] at hx
  exact hx

theorem orbit_preimage_fullChart (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k s =
      («Σ».completeQuotientStarFan b I hF).fullChartOpen k
        («Σ».orbitFullConeIndex b I hF s hIs) :=
  «Σ».orbitClosureMap_preimage_chart k b I hF
    ⟨s.val,«Σ».fullCones_mem s,hIs⟩

variable (hpure : «Σ».IsPure) (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)

/-- Empty preimages cause no problem: arbitrary generators there have
no effect on the actual sheaf. On every nonempty preimage the generator
is the projected normalized ambient character. -/
def orbitRestrictionCocycle :
    RationalCartierCocycle ((«Σ».completeQuotientStarFan b I hF).fanScheme k) where
  index := ULift.{u} «Σ».fullCones
  openSet i := («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ «Σ».fullChartOpen k i.down
  covers x := by
    obtain ⟨s,hs⟩ := «Σ».fullChartOpen_cover k hpure («Σ».orbitClosureMap k b I hF x)
    exact ⟨⟨s⟩,hs⟩
  generator i := («Σ».completeQuotientStarFan b I hF).rationalCharacter k
    (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀))
  transition i j x hi hj := by
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down x hi
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down x hj
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ i.down hIi,
      «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ j.down hIj]
    apply («Σ».completeQuotientStarFan b I hF).cartier_rational_transition_regular k
      («Σ».orbitRestrictionCoefficients b I hF a m₀)
      («Σ».orbitFullConeIndex b I hF i.down hIi)
      («Σ».orbitFullConeIndex b I hF j.down hIj) x
    · rwa [← «Σ».orbit_preimage_fullChart k b I hF i.down hIi]
    · rwa [← «Σ».orbit_preimage_fullChart k b I hF j.down hIj]

theorem orbitRestrictionCocycle_equivalent :
    («Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀).toCartierData.Equivalent
      ((«Σ».completeQuotientStarFan b I hF).fanCartierData k
        («Σ».completeQuotientStarFan_isPure hpure b I hF)
        («Σ».orbitRestrictionCoefficients b I hF a m₀)) := by
  let C := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  let Γ := «Σ».completeQuotientStarFan b I hF
  let E := Γ.fanCartierCocycle k («Σ».completeQuotientStarFan_isPure hpure b I hF)
    («Σ».orbitRestrictionCoefficients b I hF a m₀)
  apply C.equivalent_of_generatorRatios E
  · intro i j x hi hj
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down x hi
    change ((Γ.rationalCharacter k
      (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀)) :
        (Γ.fanScheme k).functionField) /
      (Γ.rationalCharacter k (Γ.cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) j.down) :
          (Γ.fanScheme k).functionField))∈_
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ i.down hIi]
    apply Γ.cartier_rational_transition_regular k _ _ _ x _ hj
    rwa [← «Σ».orbit_preimage_fullChart k b I hF i.down hIi]
  · intro i j x hi hj
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down x hj
    change ((Γ.rationalCharacter k (Γ.cartierLatticePoint
      («Σ».orbitRestrictionCoefficients b I hF a m₀) i.down) :
        (Γ.fanScheme k).functionField) /
      (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a j.down-m₀)) :
          (Γ.fanScheme k).functionField))∈_
    rw [«Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ j.down hIj]
    apply Γ.cartier_rational_transition_regular k _ _ _ x hi
    rwa [← «Σ».orbit_preimage_fullChart k b I hF j.down hIj]

/-- The actual pullback of any regular representative of an ambient
transition function has exactly the projected transition character. -/
theorem orbit_regularTransition_pullback
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val)
    (V : («Σ».fanScheme k).Opens) [Nonempty V]
    [Nonempty ((«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ V)]
    (hVs : V≤«Σ».fullChartOpen k s) (hVt : V≤«Σ».fullChartOpen k t)
    (c : Γ(«Σ».fanScheme k,V))
    (hc : («Σ».fanScheme k).germToFunctionField V c =
      («Σ».rationalCharacter k («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) :
        («Σ».fanScheme k).functionField)) :
    ((«Σ».completeQuotientStarFan b I hF).fanScheme k).germToFunctionField
      ((«Σ».orbitClosureMap k b I hF) ⁻¹ᵁ V) ((«Σ».orbitClosureMap k b I hF).app V c) =
      ((«Σ».completeQuotientStarFan b I hF).rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) :
          ((«Σ».completeQuotientStarFan b I hF).fanScheme k).functionField) := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  let q : «Σ».OrbitConeIndex b I :=
    ⟨s.val∩t.val,«Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left,
      Finset.subset_inter hIs hIt⟩
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid q.val))
  let S := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I q.val)))
  let j : Spec R ⟶ «Σ».fanScheme k := «Σ».fanChartMap k ⟨q.val,q.property.1⟩
  let l : Spec S ⟶ Γ.fanScheme k := Γ.fanChartMap k («Σ».orbitConeQuotientIndex b I hF q)
  letI : IsOpenImmersion j := «Σ».fanChartMap_isOpenImmersion k ⟨q.val,q.property.1⟩
  letI : IsOpenImmersion l := Γ.fanChartMap_isOpenImmersion k
    («Σ».orbitConeQuotientIndex b I hF q)
  let φ : R ⟶ S := CommRingCat.ofHom
    (orbitQuotientAlgebraMap k b I q.val q.property.2).toRingHom
  let d : R := «Σ».cartierTransitionUnit k a s t
  have hpre : («Σ».orbitClosureMap k b I hF) ⁻¹ᵁ (j ''ᵁ ⊤)=l ''ᵁ ⊤ := by
    rw [j.image_top_eq_opensRange,l.image_top_eq_opensRange]
    exact «Σ».orbitClosureMap_preimage_chart k b I hF q
  have hV : V≤j ''ᵁ ⊤ := by
    have h := «Σ».fanChartMap_inter_opensRange k («Σ».fullConeIndex s) («Σ».fullConeIndex t)
    change j.opensRange = «Σ».fullChartOpen k s ⊓ «Σ».fullChartOpen k t at h
    rw [Scheme.Hom.image_top_eq_opensRange,h]
    exact le_inf hVs hVt
  have hd : («Σ».fanScheme k).germToFunctionField V c=affineOpenCoordinateMap R j d := by
    rw [hc]
    exact («Σ».chartRationalMap_character k ⟨q.val,q.property.1⟩
      («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)
      («Σ».cartier_difference_mem_overlap a s t).1).symm
  rw [affineChartSection_pullback_value R S j l («Σ».orbitClosureMap k b I hF) φ
    («Σ».orbitClosureMap_chart k b I hF q) hpre V hV c d hd]
  have hm : faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)∈
      dualConeMonoid (orbitQuotientCone b I q.val) := by
    have h := (φ d).property
    rw [mem_monoidChartAlgebra] at h
    apply h
    change faceCharacterProjection b I
        («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) ∈
      ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
        («Σ».cartierTransitionUnit k a s t) : AddMonoidAlgebra k (Lattice (n-I.card)))).coeff.support
    rw [«Σ».orbit_cartierTransition_character b I k a s t hIs hIt]
    simp
  have hd' : φ d=chartCharacter k (dualConeMonoid (orbitQuotientCone b I q.val))
      (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) hm := by
    apply Subtype.ext
    exact «Σ».orbit_cartierTransition_character b I k a s t hIs hIt
  rw [hd']
  exact Γ.chartRationalMap_character k («Σ».orbitConeQuotientIndex b I hF q) _ hm

theorem orbitRestriction_frames_compatible :
    let C := «Σ».fanCartierCocycle k hpure a
    let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
    ModuleFrameGluing.Compatible
      (N := (Scheme.Modules.pushforward («Σ».orbitClosureMap k b I hF)).obj B.sheaf)
      C.openSet C.localFrame
      (fun i=>ModuleFrame.generator (B.localFrame i) (B.openSet i) le_rfl) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  let Γ := «Σ».completeQuotientStarFan b I hF
  let f := «Σ».orbitClosureMap k b I hF
  change ModuleFrameGluing.Compatible
    (N := (Scheme.Modules.pushforward f).obj B.sheaf)
    C.openSet C.localFrame
    (fun i=>ModuleFrame.generator (B.localFrame i) (B.openSet i) le_rfl)
  intro i j V hi hj
  let W := f ⁻¹ᵁ V
  by_cases hW : Nonempty W
  · letI := hW
    let bi : B.index := i
    let bj : B.index := j
    have hWi : W≤B.openSet bi := f.preimage_mono hi
    have hWj : W≤B.openSet bj := f.preimage_mono hj
    let y : W := Classical.choice hW
    letI : Nonempty V := ⟨⟨f y.val,y.property⟩⟩
    letI : Nonempty (B.openSet bi) := ⟨⟨y.val,hi y.property⟩⟩
    letI : Nonempty (B.openSet bj) := ⟨⟨y.val,hj y.property⟩⟩
    have hIi := «Σ».orbit_preimage_fullChart_forces k b I hF i.down y.val (hi y.property)
    have hIj := «Σ».orbit_preimage_fullChart_forces k b I hF j.down y.val (hj y.property)
    let c : Γ(«Σ».fanScheme k,V) := ModuleFrame.coordinates (C.localFrame j) V hj
      (ModuleFrame.generator (C.localFrame i) V hi)
    let d : Γ(Γ.fanScheme k,W) := f.app V c
    have hc₀ : («Σ».fanScheme k).germToFunctionField V c =
        (C.generator i : («Σ».fanScheme k).functionField) /
          (C.generator j : («Σ».fanScheme k).functionField) := by
      calc
        _ = rationalValue («Σ».fanScheme k) V
            (ModuleFrame.generator (C.localFrame i) V hi).val /
              (C.generator j : («Σ».fanScheme k).functionField) :=
          C.localCoordinates_value j V hj (ModuleFrame.generator (C.localFrame i) V hi)
        _ = C.toCartierData.sectionValue V (ModuleFrame.generator (C.localFrame i) V hi) /
            (C.generator j : («Σ».fanScheme k).functionField) :=
          congrArg (fun z : («Σ».fanScheme k).functionField =>
            z / (C.generator j : («Σ».fanScheme k).functionField))
            (C.toCartierData_sectionValue V (ModuleFrame.generator (C.localFrame i) V hi)).symm
        _ = _ := congrArg (fun z : («Σ».fanScheme k).functionField =>
          z / (C.generator j : («Σ».fanScheme k).functionField))
          (C.localFrame_generator_value i V hi)
    have hc : («Σ».fanScheme k).germToFunctionField V c =
        («Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down-
          «Σ».cartierLatticePoint a j.down) : («Σ».fanScheme k).functionField) := by
      simpa only [C,fanCartierCocycle,«Σ».rationalCharacter_sub k,
        Units.val_div_eq_div_val] using hc₀
    have hpc := «Σ».orbit_regularTransition_pullback k b I hF a
      i.down j.down hIi hIj V hi hj c hc
    have hmul : (B.generator bi : (Γ.fanScheme k).functionField) =
        (Γ.fanScheme k).germToFunctionField W d *
          (B.generator bj : (Γ.fanScheme k).functionField) := by
      change (B.generator bi : (Γ.fanScheme k).functionField) =
        (Γ.fanScheme k).germToFunctionField W (f.app V c) * _
      rw [hpc]
      change (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-m₀)) :
          (Γ.fanScheme k).functionField) =
        (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a i.down-
          «Σ».cartierLatticePoint a j.down)) : (Γ.fanScheme k).functionField) *
        (Γ.rationalCharacter k
        (faceCharacterProjection b I («Σ».cartierLatticePoint a j.down-m₀)) :
          (Γ.fanScheme k).functionField)
      rw [← Units.val_mul,← Γ.rationalCharacter_add k,← map_add (faceCharacterProjection b I)]
      congr 3
      abel
    apply B.toCartierData.sectionValue_injective W
    change B.toCartierData.sectionValue W
      (moduleRes B.sheaf hWi
        (ModuleFrame.generator (B.localFrame bi) (B.openSet bi) le_rfl)) =
      B.toCartierData.sectionValue W (d • moduleRes B.sheaf hWj
        (ModuleFrame.generator (B.localFrame bj) (B.openSet bj) le_rfl))
    calc
      _ = B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bi) W hWi) :=
        congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W s)
          (ModuleFrame.generator_res (B.localFrame bi) le_rfl hWi)
      _ = (B.generator bi : (Γ.fanScheme k).functionField) :=
        B.localFrame_generator_value bi W hWi
      _ = (Γ.fanScheme k).germToFunctionField W d *
          (B.generator bj : (Γ.fanScheme k).functionField) := hmul
      _ = (Γ.fanScheme k).germToFunctionField W d *
          B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bj) W hWj) :=
        congrArg (fun z : (Γ.fanScheme k).functionField =>
          (Γ.fanScheme k).germToFunctionField W d * z)
          (B.localFrame_generator_value bj W hWj).symm
      _ = B.toCartierData.sectionValue W
          (d • ModuleFrame.generator (B.localFrame bj) W hWj) :=
        (B.toCartierData.sectionValue_smul W d
          (ModuleFrame.generator (B.localFrame bj) W hWj)).symm
      _ = _ := congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W (d • s))
        (ModuleFrame.generator_res (B.localFrame bj) le_rfl hWj).symm
  · have hb : W=⊥ := by
      apply le_antisymm
      · intro y hy
        exact False.elim (hW ⟨⟨y,hy⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty B.sheaf W hb
    change (_ : Γ(B.sheaf,W)) = _
    exact Subsingleton.elim _ _

/-- The actual ambient line bundle restricts to the actual fan Cartier
sheaf with the computed quotient-ray coefficients. -/
def orbitCartierPullbackIso :
    (Scheme.Modules.pullback («Σ».orbitClosureMap k b I hF)).obj
      («Σ».fanCartierData k hpure a).sheaf ≅
        ((«Σ».completeQuotientStarFan b I hF).fanCartierData k
          («Σ».completeQuotientStarFan_isPure hpure b I hF)
          («Σ».orbitRestrictionCoefficients b I hF a m₀)).sheaf := by
  let C := «Σ».fanCartierCocycle k hpure a
  let B := «Σ».orbitRestrictionCocycle k b I hF hpure a m₀ hm₀
  exact pullbackIso_of_compatible_frames («Σ».orbitClosureMap k b I hF)
    C.openSet C.covers C.localFrame B.localFrame
    («Σ».orbitRestriction_frames_compatible k b I hF hpure a m₀ hm₀) ≪≫
      («Σ».orbitRestrictionCocycle_equivalent k b I hF hpure a m₀ hm₀).choose

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitRestrictionCocycle_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_regularTransition_pullback
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitCartierPullbackIso
end
end Source_ToricOrbitCartierRestriction
-- END ORIGINAL PaperVerification.ToricOrbitCartierRestriction


-- BEGIN ORIGINAL PaperVerification.ToricCartierFrameIsomorphisms
section Source_ToricCartierFrameIsomorphisms

-- original header: module

-- original header: public import PaperVerification.ToricCartierOrders
-- original header: public import PaperVerification.ToricModuleFrameGluing

-- original header: @[expose] public section

/-!
# Local Cartier frames under an actual line-bundle isomorphism

An isomorphism of the underlying module sheaves need not preserve their
fractional embeddings. It does, however, preserve the regular change of
coordinates between two transported frames. This distinction is used
when proving that degree depends only on the actual line bundle.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes

namespace ModuleFrame

variable {X : Scheme.{u}} {M N : X.Modules} (F : M ≅ N)
    {U : X.Opens} (e : ModuleFrame N U)

def precompose : ModuleFrame M U :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso F ≪≫ e

@[simp] theorem precompose_coordinates (V : X.Opens) (hV : V≤U)
    (s : Γ(M,V)) :
    (e.precompose F).coordinates V hV s = e.coordinates V hV (F.hom.app V s) := rfl

@[simp] theorem precompose_generator (V : X.Opens) (hV : V≤U) :
    F.hom.app V ((e.precompose F).generator V hV) = e.generator V hV := by
  apply (e.coordinates V hV).injective
  rw [← precompose_coordinates,coordinates_generator,coordinates_generator]

end ModuleFrame

namespace CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)
    (F : D.sheaf ≅ E.sheaf)

/-- Ratios of transported rational generators agree, even though the
individual generators need not have the same rational value. -/
theorem precompose_frameRatio {U V : X.Opens} [Nonempty U] [Nonempty V]
    (e : E.Frame U) (q : E.Frame V) :
    D.frameRationalGenerator (ModuleFrame.precompose F e) /
      D.frameRationalGenerator (ModuleFrame.precompose F q) =
        E.frameRationalGenerator e / E.frameRationalGenerator q := by
  let W := U⊓V
  letI : Nonempty W := ⟨⟨genericPoint X,genericPoint_mem_open X U,
    genericPoint_mem_open X V⟩⟩
  let c := (ModuleFrame.precompose F q).coordinates W inf_le_right
    ((ModuleFrame.precompose F e).generator W inf_le_left)
  have hD : (ModuleFrame.precompose F e).generator W inf_le_left =
      c • (ModuleFrame.precompose F q).generator W inf_le_right :=
    (ModuleFrame.precompose F q).section_eq W inf_le_right _
  have hE := congrArg (F.hom.app W) hD
  rw [ModuleFrame.precompose_generator,Scheme.Modules.Hom.app_smul,
    ModuleFrame.precompose_generator] at hE
  have hDv := congrArg (D.sectionValue W) hD
  have hEv := congrArg (E.sectionValue W) hE
  change D.sectionValue W (D.frameGenerator (ModuleFrame.precompose F e) W inf_le_left) =
    D.sectionValue W (c • D.frameGenerator (ModuleFrame.precompose F q) W inf_le_right) at hDv
  change E.sectionValue W (E.frameGenerator e W inf_le_left) =
    E.sectionValue W (c • E.frameGenerator q W inf_le_right) at hEv
  rw [D.sectionValue_frameGenerator,D.sectionValue_smul,D.sectionValue_frameGenerator] at hDv
  rw [E.sectionValue_frameGenerator,E.sectionValue_smul,E.sectionValue_frameGenerator] at hEv
  calc
    D.frameRationalGenerator (ModuleFrame.precompose F e) /
        D.frameRationalGenerator (ModuleFrame.precompose F q) = X.germToFunctionField W c := by
      rw [hDv,mul_div_cancel_right₀ _ (D.frameRationalGenerator_ne_zero _)]
    _ = E.frameRationalGenerator e / E.frameRationalGenerator q := by
      rw [hEv,mul_div_cancel_right₀ _ (E.frameRationalGenerator_ne_zero _)]

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.precompose_frameRatio
end
end Source_ToricCartierFrameIsomorphisms
-- END ORIGINAL PaperVerification.ToricCartierFrameIsomorphisms


-- BEGIN ORIGINAL PaperVerification.ToricCocycleOrders
section Source_ToricCocycleOrders

-- original header: module

-- original header: public import PaperVerification.ToricCartierOrders

-- original header: @[expose] public section

/-!
# The local equations compute actual Cartier orders

The fractional sheaf reconstructed from a rational Cartier cocycle has
the specified local rational generators. This connects its intrinsic
Weil coefficients to the input equations through the actual sheaf frames.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

theorem localFrame_frameLinearEquiv (i : C.index) (V : X.Opens)
    (hV : V≤C.openSet i) :
    C.toCartierData.frameLinearEquiv (C.localFrame i) V hV =
      C.localCoordinates i V hV := rfl

/-- The sheaf construction recovers the literal rational generator,
including its multiplicative scalar. -/
theorem localFrame_rationalGenerator (i : C.index) [Nonempty (C.openSet i)] :
    C.toCartierData.frameRationalGenerator (C.localFrame i) =
      (C.generator i : X.functionField) := by
  let U := C.openSet i
  let s := C.toCartierData.frameGenerator (C.localFrame i) U le_rfl
  have hs : C.localCoordinates i U le_rfl s = 1 := by
    rw [← C.localFrame_frameLinearEquiv]
    exact LinearEquiv.apply_symm_apply _ _
  have h := C.localCoordinates_value i U le_rfl s
  rw [hs,map_one] at h
  change rationalValue X U s.val = (C.generator i : X.functionField)
  exact (div_eq_one_iff_eq (Units.ne_zero _)).mp h.symm

variable [IsLocallyNoetherian X]

/-- The sign is fixed by taking local generators of `O(D)`, rather than
local equations of `D`. -/
theorem weilCoefficient_eq (i : C.index) {x : X} (hx : x∈C.openSet i) :
    C.toCartierData.weilCoefficient x = -X.ord (C.generator i : X.functionField) x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hx⟩⟩
  rw [C.toCartierData.weilCoefficient_eq_neg_frameOrder (C.localFrame i) hx,
    C.localFrame_rationalGenerator]

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.weilCoefficient_eq
end
end Source_ToricCocycleOrders
-- END ORIGINAL PaperVerification.ToricCocycleOrders


-- BEGIN ORIGINAL PaperVerification.ToricCoordinateOrders
section Source_ToricCoordinateOrders

-- original header: module

-- original header: public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
-- original header: public import Mathlib.RingTheory.Localization.AtPrime.Basic
-- original header: public import Mathlib.RingTheory.Localization.Submodule
-- original header: public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
-- original header: public import Mathlib.RingTheory.Polynomial.Basic
-- original header: public import Mathlib.Algebra.MvPolynomial.Division

-- original header: @[expose] public section

/-!
# Actual orders along coordinate boundary primes

The local ring is the literal localization at the principal coordinate
prime. Its DVR structure, its uniformizer, and the units in the other
coordinate directions are proved. The order is Mathlib's order of
vanishing defined from module length and its fraction-field extension,
rather than a newly defined exponent function.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open IsLocalRing
open scoped BigOperators Classical nonZeroDivisors

section PrincipalPrime

variable (R S : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime S P] [IsLocalRing S] [IsDomain S]

theorem maximalIdeal_eq_span_of_principalPrime (p : R) (hP : P = Ideal.span {p}) :
    maximalIdeal S = Ideal.span {algebraMap R S p} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P S, hP,
    Ideal.map_span, Set.image_singleton]

/-- A Noetherian domain localized at a nonzero principal prime is a DVR.
The conclusion is proved from the actual principal maximal ideal. -/
theorem principalPrimeLocalization_isDiscreteValuationRing
    (p : R) (hp : p ≠ 0) (hP : P = Ideal.span {p}) :
    IsDiscreteValuationRing S := by
  letI : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing P.primeCompl S inferInstance
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hp' : algebraMap R S p ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hp
  have hmax := maximalIdeal_eq_span_of_principalPrime R S P p hP
  have hnot : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    rw [hmax, Ideal.span_singleton_eq_bot]
    exact hp'
  have hprincipal : (maximalIdeal S).IsPrincipal := by
    rw [hmax]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE S hnot).out 5 1).mp hprincipal

theorem principalPrimeLocalization_generator_irreducible
    (p : R) (hp : p ≠ 0) (hP : P = Ideal.span {p}) :
    Irreducible (algebraMap R S p) := by
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact (map_ne_zero_iff _
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).mpr hp
  · exact maximalIdeal_eq_span_of_principalPrime R S P p hP

end PrincipalPrime

variable (k : Type*) [Field k] {n : ℕ}

/-- The actual prime ideal defining the i-th coordinate boundary. -/
def coordinatePrime (i : Fin n) : Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span {MvPolynomial.X i}

instance coordinatePrime_isPrime (i : Fin n) : (coordinatePrime k i).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (MvPolynomial.X_prime (R := k) (i := i))

abbrev coordinateBoundaryLocalRing (i : Fin n) :=
  Localization.AtPrime (coordinatePrime k i)

instance coordinateBoundaryLocalRing_isDomain (i : Fin n) :
    IsDomain (coordinateBoundaryLocalRing k i) :=
  IsLocalization.isDomain_of_atPrime _ (coordinatePrime k i)

instance coordinateBoundaryLocalRing_isDiscreteValuationRing (i : Fin n) :
    IsDiscreteValuationRing (coordinateBoundaryLocalRing k i) :=
  principalPrimeLocalization_isDiscreteValuationRing
    (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i)
    (coordinatePrime k i) (MvPolynomial.X i) (MvPolynomial.X_ne_zero i) rfl

def coordinateBoundaryParameter (i j : Fin n) : coordinateBoundaryLocalRing k i :=
  algebraMap (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i) (MvPolynomial.X j)

theorem coordinateBoundaryParameter_irreducible (i : Fin n) :
    Irreducible (coordinateBoundaryParameter k i i) :=
  principalPrimeLocalization_generator_irreducible
    (MvPolynomial (Fin n) k) (coordinateBoundaryLocalRing k i)
    (coordinatePrime k i) (MvPolynomial.X i) (MvPolynomial.X_ne_zero i) rfl

theorem coordinateBoundaryParameter_isUnit (i j : Fin n) (hij : i ≠ j) :
    IsUnit (coordinateBoundaryParameter k i j) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (S := coordinateBoundaryLocalRing k i) (I := coordinatePrime k i)
      (MvPolynomial.X j)).mpr
  change MvPolynomial.X j ∉ Ideal.span {MvPolynomial.X i}
  rw [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X]
  exact hij

variable (i : Fin n) (K : Type*) [Field K]
    [Algebra (coordinateBoundaryLocalRing k i) K]
    [IsFractionRing (coordinateBoundaryLocalRing k i) K]

/-- The literal order of the coordinate defining the boundary is one. -/
theorem ordFrac_X_i :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i i)) = WithZero.exp (1 : ℤ) :=
  Ring.ordFrac_irreducible (coordinateBoundaryParameter_irreducible k i)

theorem ordFrac_X_other (j : Fin n) (hij : i ≠ j) :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) = 1 :=
  Ring.ordFrac_of_isUnit (coordinateBoundaryParameter_isUnit k i j hij)

theorem ordFrac_coordinate_product :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (∏ j : Fin n, algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) = WithZero.exp (1 : ℤ) := by
  rw [map_prod]
  rw [Finset.prod_eq_single i]
  · exact ordFrac_X_i k i K
  · intro j hj hji
    exact ordFrac_X_other k i K j hji.symm
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The coefficient of a logarithmic volume relative to a regular
coordinate volume has the genuine order -1 at every boundary prime. -/
theorem ordFrac_inverse_coordinate_product :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      ((∏ j : Fin n, algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j))⁻¹) = WithZero.exp (-1 : ℤ) := by
  rw [map_inv₀, ordFrac_coordinate_product, WithZero.inv_exp]

/-- The familiar exponent formula is a consequence of actual DVR order,
and holds for all integral character exponents. -/
theorem ordFrac_coordinate_character (m : Fin n → ℤ) :
    Ring.ordFrac (coordinateBoundaryLocalRing k i)
      (∏ j : Fin n, (algebraMap (coordinateBoundaryLocalRing k i) K
        (coordinateBoundaryParameter k i j)) ^ m j) = WithZero.exp (m i) := by
  rw [map_prod]
  simp_rw [map_zpow₀]
  rw [Finset.prod_eq_single i]
  · rw [ordFrac_X_i, ← WithZero.exp_zsmul]
    simp
  · intro j hj hji
    rw [ordFrac_X_other k i K j hji.symm, one_zpow]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.principalPrimeLocalization_isDiscreteValuationRing
#print axioms PaperVerification.ToricSchemes.ordFrac_inverse_coordinate_product

end
end Source_ToricCoordinateOrders
-- END ORIGINAL PaperVerification.ToricCoordinateOrders


-- BEGIN ORIGINAL PaperVerification.ToricAffineBoundaryOrders
section Source_ToricAffineBoundaryOrders

-- original header: module

-- original header: public import PaperVerification.ToricCoordinateOrders
-- original header: public import PaperVerification.ToricFunctionFieldBridge
-- original header: public import Mathlib.AlgebraicGeometry.OrderOfVanishing

-- original header: @[expose] public section

/-!
# From an actual affine boundary prime to scheme order

The stalk equivalence below is composed from the actual affine stalk
localization and the actual open-immersion stalk map. Its compatibility
with the coordinate-ring embedding in the generic stalk is proved.
Principal prime uniformizers therefore compute the scheme's ordinary
order function at the corresponding actual point.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical nonZeroDivisors

variable (R : CommRingCat.{u}) [IsDomain R] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec R ⟶ X) [IsOpenImmersion j]

local instance affineOpenStalkMap_isIso (p : PrimeSpectrum R) : IsIso (j.stalkMap p) :=
  (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion j)).2
    (show Spec R from p)

/-- The genuine affine localization isomorphism followed by the inverse
of the genuine open-immersion map on local rings. -/
def affineOpenStalkEquiv (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk (j p) :=
  ((Spec.stalkIso R p).symm ≪≫ (asIso (j.stalkMap p)).symm).commRingCatIsoToRingEquiv

@[simp] theorem affineOpenStalkEquiv_stalkMap (p : PrimeSpectrum R)
    (r : Localization.AtPrime p.asIdeal) :
    j.stalkMap p (affineOpenStalkEquiv R j p r) = (Spec.stalkIso R p).inv r := by
  change (asIso (j.stalkMap p)).hom
    ((asIso (j.stalkMap p)).inv ((Spec.stalkIso R p).inv r)) =
      (Spec.stalkIso R p).inv r
  exact Iso.inv_hom_id_apply (asIso (j.stalkMap p)) _

theorem affineOpenStalkEquiv_algebraMap (p : PrimeSpectrum R) (r : R) :
    affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r) =
      X.presheaf.germ (j ''ᵁ (⊤ : (Spec R).Opens)) (j p) ⟨p, trivial, rfl⟩
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)) := by
  apply (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv.injective
  change j.stalkMap p
      (affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
    j.stalkMap p (X.presheaf.germ (j ''ᵁ (⊤ : (Spec R).Opens)) (j p) ⟨p,trivial,rfl⟩
      ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)))
  erw [affineOpenStalkEquiv_stalkMap, j.germ_stalkMap_apply]
  have hsec := congrArg (fun f => f ((Scheme.ΓSpecIso R).inv r)) (j.appIso_inv_app ⊤)
  erw [hsec]
  erw [(Spec R).presheaf.germ_res_apply
    (eqToHom (Scheme.Hom.preimage_image_eq j ⊤))]
  exact congrArg (fun f => f r) (Spec.algebraMap_stalkIso_inv (R := R) (x := p))

/-- The two routes to the actual generic stalk agree exactly. -/
theorem affineOpenStalkEquiv_functionField (p : PrimeSpectrum R) (r : R) :
    algebraMap (X.presheaf.stalk (j p)) X.functionField
        (affineOpenStalkEquiv R j p (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
      affineOpenCoordinateMap R j r := by
  letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) := openImmersion_image_nonempty j ⊤
  rw [affineOpenStalkEquiv_algebraMap]
  exact (X.algebraMap_germ_eq_germToFunctionField
    (U := j ''ᵁ (⊤ : (Spec R).Opens)) (x := j p) ⟨p,trivial,rfl⟩
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))).trans
    (openImmersionRegularToFunctionField_eq_germ_image j ⊤
      ((Scheme.ΓSpecIso R).inv r)).symm

theorem affineOpenCoordinateMap_injective : Function.Injective (affineOpenCoordinateMap R j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

/-- A DVR on the literal affine localization transports to the actual
scheme stalk; no regularity axiom is added to that stalk. -/
theorem affineOpen_stalk_isDiscreteValuationRing (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] :
    IsDiscreteValuationRing (X.presheaf.stalk (j p)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (affineOpenStalkEquiv R j p)

theorem affineOpen_coheight_eq_one (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] :
    Order.coheight (j p) = 1 := by
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk (j p))
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_eq_coe.mp h

variable [IsNoetherianRing R] [IsLocallyNoetherian X]

/-- Exact scheme order of a nonzero principal prime generator on an
actual affine open chart. -/
theorem affineOpen_order_principalPrime (p : PrimeSpectrum R)
    (r : R) (hr : r ≠ 0) (hp : p.asIdeal = Ideal.span {r}) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 1 := by
  letI : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
    principalPrimeLocalization_isDiscreteValuationRing R
      (Localization.AtPrime p.asIdeal) p.asIdeal r hr hp
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have hcodim := affineOpen_coheight_eq_one R j p
  have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr
  rw [X.ord_eq_iff hcodim hr']
  change Ring.ordFrac (X.presheaf.stalk (j p)) (affineOpenCoordinateMap R j r) =
    WithZero.exp (1 : ℤ)
  rw [← affineOpenStalkEquiv_functionField R j p r]
  apply Ring.ordFrac_irreducible
  exact (principalPrimeLocalization_generator_irreducible R
    (Localization.AtPrime p.asIdeal) p.asIdeal r hr hp).map
      (affineOpenStalkEquiv R j p).toMulEquiv

/-- An element outside the actual affine prime is a local unit, so its
scheme order is zero at the corresponding point. -/
theorem affineOpen_order_of_not_mem (p : PrimeSpectrum R)
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] (r : R) (hr : r ∉ p.asIdeal) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 0 := by
  letI := affineOpen_stalk_isDiscreteValuationRing R j p
  have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (S := Localization.AtPrime p.asIdeal) (I := p.asIdeal) r).mpr hr
  have hcodim := affineOpen_coheight_eq_one R j p
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr0
  rw [X.ord_eq_iff hcodim hr']
  change Ring.ordFrac (X.presheaf.stalk (j p)) (affineOpenCoordinateMap R j r) =
    WithZero.exp (0 : ℤ)
  rw [← affineOpenStalkEquiv_functionField R j p r]
  have hu' : IsUnit ((affineOpenStalkEquiv R j p)
      (algebraMap R (Localization.AtPrime p.asIdeal) r)) :=
    hu.map (affineOpenStalkEquiv R j p).toRingHom
  simpa only [WithZero.exp_zero] using Ring.ordFrac_of_isUnit hu'

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineOpen_order_principalPrime

end
end Source_ToricAffineBoundaryOrders
-- END ORIGINAL PaperVerification.ToricAffineBoundaryOrders


-- BEGIN ORIGINAL PaperVerification.ToricRationalPointDegrees
section Source_ToricRationalPointDegrees

-- original header: module

-- original header: public import Mathlib.AlgebraicGeometry.ResidueField
-- original header: public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

-- original header: @[expose] public section

/-!
# Residue degree at an actual rational point

A section of a scheme morphism induces inverse maps on residue fields
at its image. The proof uses the actual maps on local residue fields.
In particular, the two coordinate boundary points of an invariant
projective line contribute residue degree one over the ground field.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme.{u}}

/-- A section is an isomorphism on the residue field at every point of
its image, regardless of whether the base field is algebraically closed. -/
theorem residueFieldMap_bijective_of_section
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    Function.Bijective (f.residueFieldMap (s y)) := by
  have hpoint : f (s y)=y := congrArg (fun g : Y ⟶ Y => g y) hs
  have hcomp : f.residueFieldMap (s y) ≫ s.residueFieldMap y =
      (Y.residueFieldCongr hpoint).hom := by
    rw [← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr hs,
      Scheme.residueFieldMap_id]
    exact Category.comp_id ((Y.residueFieldCongr hpoint).hom)
  refine ⟨(f.residueFieldMap (s y)).hom.injective,?_⟩
  intro z
  obtain ⟨a,ha⟩ := (Y.residueFieldCongr hpoint).commRingCatIsoToRingEquiv.surjective
    (s.residueFieldMap y z)
  refine ⟨a,(s.residueFieldMap y).hom.injective ?_⟩
  exact (congrArg (fun g => g a) hcomp).trans ha

/-- Degree one is computed from Mathlib's literal residue extension. -/
theorem residueDegree_of_section
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    f.residueDegree (s y) = 1 := by
  letI := (f.residueFieldMap (s y)).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (residueFieldMap_bijective_of_section f s hs y)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.residueDegree_of_section
end
end Source_ToricRationalPointDegrees
-- END ORIGINAL PaperVerification.ToricRationalPointDegrees


