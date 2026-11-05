module

public import Continuation.Runtime.CartierDegreeComparison
public import Continuation.Divisor.FanoClosure

/-!
# Ordinary nefness implies the actual invariant-wall inequalities

The test curve is the original orbit-closure curve in the original fan
scheme. Its properness is proved from the two-ray fan's strict support,
and its ordinary line-bundle degree is identified with the previously
computed wall slack. No alternate toric scheme is introduced.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical

/-- The usual two-ray fan has strict integral unit support on all three cones. -/
theorem projectiveLine_strict_unit_support :
    projectiveLineFan.IsStrictSupport (fun _ => 1) := by
  intro s hs
  rcases (mem_projectiveLineFan_cones s).mp hs with rfl | rfl | rfl
  · refine ⟨0, ?_, ?_⟩
    · simp
    · intro v hv hn
      norm_num
  · refine ⟨LinearMap.proj (0 : Fin 1), ?_, ?_⟩
    · intro v hv
      have h := Finset.mem_singleton.mp hv
      subst v
      norm_num [embed, projectiveLineRay]
    · intro v hv hn
      rw [projectiveLineFan_rays] at hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (hn (Finset.mem_singleton_self _)).elim
      · have h := Finset.mem_singleton.mp hv
        subst v
        norm_num [embed, projectiveLineRay]
  · refine ⟨-(LinearMap.proj (0 : Fin 1)), ?_, ?_⟩
    · intro v hv
      have h := Finset.mem_singleton.mp hv
      subst v
      norm_num [embed, projectiveLineRay]
    · intro v hv hn
      rw [projectiveLineFan_rays] at hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · norm_num [embed, projectiveLineRay]
      · exact (hn hv).elim

variable (k : Type u) [Field k]

/-- Properness of the actual two-chart line over its original field. -/
instance projectiveLineStructureMap_isProper :
    IsProper (projectiveLineFan.fanSchemeStructureMap k) := by
  let D := Unimodular.Projectivity.strictSupportVertexData
    projectiveLineFan (fun _ => 1)
    (show projectiveLineFan.IsStrictSupport (fun _ => ((1 : ℤ) : ℝ)) by
      simpa using projectiveLine_strict_unit_support)
  exact D.fanScheme_isProper k

/-- The previously computed two-chart degree equals the ordinary curve degree. -/
theorem projectiveLineHasDegree_ordinary
    {M : (projectiveLineScheme k).Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (projectiveLineScheme k) M]
    {r : ℤ} (hr : ProjectiveLineHasDegree k M r) :
    Intersection.lineBundleDegree (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_topologicalKrullDim k).le M = r := by
  obtain ⟨a, ⟨e⟩, ha⟩ := hr
  let D := projectiveLineCartierData k a
  letI : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible _ D.sheaf :=
    (Unimodular.NefBig.cartierInvertibleSheaf D).property
  rw [Intersection.lineBundleDegree_eq_of_iso
    (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLine_topologicalKrullDim k).le e]
  rw [D.lineBundleDegree_eq_original k
    (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLine_topologicalKrullDim k).le
    (projectiveLine_weilCoefficient_locallyFinite k a)]
  exact (projectiveLineCartier_degree k a).trans ha

namespace SmoothCompleteFan

variable {d : ℕ} (Γ : SmoothCompleteFan d) (hd : d = 1)

include hd in
/-- Every original rank-one complete smooth fan has a proper structural map. -/
theorem oneDimensional_structureMap_isProper :
    IsProper (Γ.fanSchemeStructureMap k) := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  infer_instance

include hd in
theorem oneDimensional_dimension : topologicalKrullDim (Γ.fanScheme k) = 1 := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  exact projectiveLine_topologicalKrullDim k

/-- Identification of ordinary degree on the original rank-one fan scheme. -/
theorem oneDimensionalHasDegree_ordinary {M : (Γ.fanScheme k).Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (Γ.fanScheme k) M]
    {r : ℤ} (hr : Γ.OneDimensionalHasDegree hd k M r) :
    letI : IsProper (Γ.fanSchemeStructureMap k) :=
      Γ.oneDimensional_structureMap_isProper k hd
    Intersection.lineBundleDegree (Γ.fanSchemeStructureMap k)
      (Γ.oneDimensional_dimension k hd).le M = r := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  have h : ProjectiveLineHasDegree k
      ((Scheme.Modules.pullback (𝟙 (projectiveLineScheme k))).obj M) r := hr
  exact projectiveLineHasDegree_ordinary k
    ((projectiveLineHasDegree_iso k
      ((Scheme.Modules.pullbackId (projectiveLineScheme k)).app M) r).mp h)

variable {n : ℕ} (F : SmoothCompleteFan n)

local instance fanCartierOrdinaryInvertible (a : Lattice n → ℤ) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (F.fanScheme k)
      (F.fanCartierData k F.isPure a).sheaf :=
  (Unimodular.NefBig.cartierInvertibleSheaf (F.fanCartierData k F.isPure a)).property

/-- The actual wall curve is a valid ordinary proper integral test curve. -/
def ordinaryWallCurve (s : F.fullCones) (j : Fin n) :
    IntegralCurve k (F.fanScheme k) where
  carrier := F.wallCurve s j k
  ι := F.wallCurveInclusion s j k
  isClosedImmersion := inferInstance
  isIntegral := inferInstance
  isProper := by
    have h := (F.wallCurveFan s j).oneDimensional_structureMap_isProper k
      (F.wallIndices_codimension s j)
    have he := comp_over (F.wallCurveInclusion s j k) (Spec (CommRingCat.of k))
    change F.wallCurveInclusion s j k ≫ F.fanSchemeStructureMap k =
      (F.wallCurveFan s j).fanSchemeStructureMap k at he
    change IsProper (F.wallCurveInclusion s j k ≫ F.fanSchemeStructureMap k)
    rwa [he]
  dim_eq_one := F.wallCurve_dimension s j k

/-- Ordinary nefness of the actual fan Cartier sheaf forces every wall slack
to be nonnegative, with no extra projectivity hypothesis on the ambient fan. -/
theorem integerWallSlack_nonneg_of_geometric_nef
    (a : Lattice n → ℤ)
    (hnef : AlgebraicGeometry.IsNef (baseField := k)
      (F.fanCartierData k F.isPure a).sheaf)
    (s : F.fullCones) (j : Fin n) (t : F.fullCones) (w : Lattice n)
    (ht : t.val = insert w ((F.wallIndices s j).image (F.fullConeBasis s)))
    (hwj : (F.fullConeBasis s).repr w j = -1) :
    0 ≤ F.integerWallSlack a s w := by
  let C := F.ordinaryWallCurve k s j
  letI : IsProper (F.wallCurveInclusion s j k ≫ F.fanSchemeStructureMap k) :=
    C.isProper
  have hn := hnef C
  have hd := F.wallCurve_fanCartier_hasDegree s j k F.isPure a t w ht hwj
  have he := (F.wallCurveFan s j).oneDimensionalHasDegree_ordinary k
    (F.wallIndices_codimension s j) hd
  have hbase := comp_over (F.wallCurveInclusion s j k) (Spec (CommRingCat.of k))
  change F.wallCurveInclusion s j k ≫ F.fanSchemeStructureMap k =
    (F.wallCurveFan s j).fanSchemeStructureMap k at hbase
  change 0 ≤ Intersection.lineBundleDegree
    (F.wallCurveInclusion s j k ≫ F.fanSchemeStructureMap k)
    C.dim_eq_one.le
    ((Scheme.Modules.pullback (F.wallCurveInclusion s j k)).obj
      (F.fanCartierData k F.isPure a).sheaf) at hn
  have hdegree : Intersection.lineBundleDegree
      (F.wallCurveInclusion s j k ≫ F.fanSchemeStructureMap k)
      C.dim_eq_one.le
      ((Scheme.Modules.pullback (F.wallCurveInclusion s j k)).obj
        (F.fanCartierData k F.isPure a).sheaf) = F.integerWallSlack a s w := by
    simpa only [hbase] using he
  rwa [hdegree] at hn

#print axioms oneDimensionalHasDegree_ordinary
#print axioms integerWallSlack_nonneg_of_geometric_nef

end SmoothCompleteFan
end PaperVerification.ToricGeometry
