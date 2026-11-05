module

public import PaperVerification.ToricCartierChartValues
public import PaperVerification.ToricFanSectionValues
public import PaperVerification.ToricChartPicard

@[expose] public section

/-!
# Arbitrary Cartier frames on the actual fan scheme

An arbitrary invertible fractional sheaf is normalized on the dense torus.
Triviality of the genuine Picard group of each affine smooth chart supplies
an actual frame. Its rational generator is proved to be an actual unit of
the Laurent algebra, because both it and its inverse are regular on the
torus. No invariant-divisor presentation is assumed.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance splitTorus_integral : IsIntegral (ToricGeometry.splitTorus k n) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

local instance splitTorusOpenMap_schemes_isOpenImmersion : IsOpenImmersion
    (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
      «Σ».splitTorusOpenMap k) :=
  «Σ».splitTorusOpenMap_isOpenImmersion k

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility of the literal Laurent-ring inclusion with the actual
open torus's regular-function map into the genuine function field. -/
theorem torusRationalMap_eq_openImmersion (f : AddMonoidAlgebra k (Lattice n)) :
    «Σ».torusRationalMap k f =
      openImmersionGlobalToFunctionField («Σ».splitTorusOpenMap k)
        ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (Lattice n)))).inv f) := by
  letI : IsIntegral (coneChart k (∅ : Finset (Lattice n))) :=
    «Σ».coneChart_isIntegral k «Σ».zeroConeIndex
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid (∅ : Finset (Lattice n))))
  let S := CommRingCat.of (AddMonoidAlgebra k (Lattice n))
  let e := zeroConeChartAlgEquiv k n
  let g := (zeroConeChartIso k n).inv
  let a : Γ(coneChart k (∅ : Finset (Lattice n)),⊤) :=
    (Scheme.ΓSpecIso R).inv (e.symm f)
  have hsec : g.appTop a =
      (Scheme.ΓSpecIso S).inv f := by
    change @Eq (Γ(Spec S,⊤)) (g.appTop a) ((Scheme.ΓSpecIso S).inv f)
    have h := congrArg (fun h=>h (e.symm f))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e.toRingHom))
    change (Scheme.ΓSpecIso S).inv (e (e.symm f)) =
      g.appTop a at h
    exact h.symm.trans (congrArg (Scheme.ΓSpecIso S).inv (e.apply_symm_apply f))
  change openImmersionGlobalToFunctionField («Σ».torusOpenMap k) a =
    openImmersionGlobalToFunctionField (g ≫ «Σ».torusOpenMap k)
      ((Scheme.ΓSpecIso S).inv f)
  calc
    _ = openImmersionGlobalToFunctionField (g ≫ «Σ».torusOpenMap k) (g.appTop a) :=
      (openImmersionGlobalToFunctionField_restrict g («Σ».torusOpenMap k) a).symm
    _ = _ := congrArg (openImmersionGlobalToFunctionField (g ≫ «Σ».torusOpenMap k)) hsec

theorem torusOpen_le_chartOpen (s : «Σ».ConeIndex) :
    («Σ».splitTorusOpenMap k).opensRange ≤ («Σ».fanChartMap k s).opensRange := by
  rintro x ⟨y,rfl⟩
  refine ⟨coneChartFaceMap k (Finset.empty_subset s.val)
    ((zeroConeChartIso k n).inv y),?_⟩
  change (coneChartFaceMap k (Finset.empty_subset s.val) ≫ «Σ».fanChartMap k s)
      ((zeroConeChartIso k n).inv y) = _
  rw [«Σ».torusOpenMap_chart]
  rfl

/-- The actual normalized Cartier presentation for an arbitrary divisor. -/
def normalizedCartier (D : CartierData («Σ».fanScheme k)) : CartierData («Σ».fanScheme k) :=
  torusNormalizedCartier k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D

theorem normalizedCartier_linearlyEquivalent (D : CartierData («Σ».fanScheme k)) :
    («Σ».normalizedCartier k D).LinearlyEquivalent D :=
  torusNormalizedCartier_linearlyEquivalent k n («Σ».fanScheme k)
    («Σ».splitTorusOpenMap k) D

theorem normalizedCartier_isAmple_iff (D : CartierData («Σ».fanScheme k)) :
    («Σ».normalizedCartier k D).IsAmple ↔ D.IsAmple :=
  torusNormalizedCartier_isAmple_iff k n («Σ».fanScheme k)
    («Σ».splitTorusOpenMap k) D

set_option backward.isDefEq.respectTransparency.types false in
/-- Normalization makes the actual fractional section image equal to the
ordinary ring of regular functions on the torus image. -/
theorem normalizedCartier_torus_range (D : CartierData («Σ».fanScheme k)) :
    let W := («Σ».splitTorusOpenMap k) ''ᵁ (⊤ : (ToricGeometry.splitTorus k n).Opens)
    letI : Nonempty W := openImmersion_image_nonempty («Σ».splitTorusOpenMap k) ⊤
    ((«Σ».normalizedCartier k D).sectionValueRange W : Set («Σ».fanScheme k).functionField) =
      Set.range ((«Σ».fanScheme k).germToFunctionField W) := by
  let j := «Σ».splitTorusOpenMap k
  letI : IsOpenImmersion j := «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : IsOpenImmersion
      (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from j) :=
    «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : Nonempty (⊤ : (ToricSchemes.splitTorus k (Fin n → ℤ)).Opens) := by
    change Nonempty (⊤ : (ToricGeometry.splitTorus k n).Opens)
    infer_instance
  let W := j ''ᵁ (⊤ : (ToricGeometry.splitTorus k n).Opens)
  letI : Nonempty W := openImmersion_image_nonempty j ⊤
  change Set.range ((«Σ».normalizedCartier k D).sectionValue W) = _
  rw [← («Σ».normalizedCartier k D).alongSectionValue_range j ⊤]
  trans Set.range (openImmersionRegularToFunctionField j ⊤)
  · exact torusNormalizedCartier_range k n («Σ».fanScheme k) j D ⊤
  ext r
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(j.appIso ⊤).inv a,
      (openImmersionRegularToFunctionField_eq_germ_image j ⊤ a).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨(j.appIso ⊤).hom a,?_⟩
    rw [openImmersionRegularToFunctionField_eq_germ_image]
    simp
    rfl

/-- The frame is an actual sheaf isomorphism produced by affine Picard
triviality, applied to the arbitrary normalized Cartier sheaf. -/
def normalizedChartFrame (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) :
    («Σ».normalizedCartier k D).sheaf.restrict («Σ».fanChartMap k s) ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf := by
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))) ⟶
        «Σ».fanScheme k from «Σ».fanChartMap k s) :=
    «Σ».fanChartMap_isOpenImmersion k s
  exact «Σ».chartInvertibleSheafIso k s.val s.property
    ((«Σ».normalizedCartier k D).sheaf.restrict («Σ».fanChartMap k s))
    (isInvertibleModule_restrict («Σ».fanChartMap k s) («Σ».normalizedCartier k D).locallyFree)

def normalizedChartGenerator (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) :
    («Σ».fanScheme k).functionField := by
  letI := «Σ».coneChart_isIntegral k s
  exact («Σ».normalizedCartier k D).chartFrameRationalGenerator
    («Σ».fanChartMap k s) («Σ».normalizedChartFrame k D s)

theorem normalizedChartGenerator_ne_zero (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) : «Σ».normalizedChartGenerator k D s ≠ 0 := by
  letI := «Σ».coneChart_isIntegral k s
  exact («Σ».normalizedCartier k D).chartFrameRationalGenerator_ne_zero
    («Σ».fanChartMap k s) («Σ».normalizedChartFrame k D s)

/-- Every chosen genuine chart generator is a genuine Laurent unit.
In particular this is stronger than being a nonzero rational function. -/
theorem exists_normalizedChartLaurentUnit (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) :
    ∃ v : (AddMonoidAlgebra k (Lattice n))ˣ,
      «Σ».torusRationalMap k (v : AddMonoidAlgebra k (Lattice n)) =
        «Σ».normalizedChartGenerator k D s := by
  letI := «Σ».coneChart_isIntegral k s
  let j := «Σ».splitTorusOpenMap k
  let W := j ''ᵁ (⊤ : (ToricGeometry.splitTorus k n).Opens)
  letI : Nonempty W := openImmersion_image_nonempty j ⊤
  have hW : W≤(«Σ».fanChartMap k s).opensRange := by
    rw [show W=j ''ᵁ ⊤ from rfl,j.image_top_eq_opensRange]
    exact «Σ».torusOpen_le_chartOpen k s
  obtain ⟨a,ha⟩ := («Σ».normalizedCartier k D).chartFrameGenerator_isUnit_of_range
    («Σ».fanChartMap k s) («Σ».normalizedChartFrame k D s) W hW
    («Σ».normalizedCartier_torus_range k D)
  let S := CommRingCat.of (AddMonoidAlgebra k (Lattice n))
  let φ : Γ(«Σ».fanScheme k,W) →+* AddMonoidAlgebra k (Lattice n) :=
    (Scheme.ΓSpecIso S).hom.hom.comp (j.appIso ⊤).hom.hom
  refine ⟨Units.map φ a,?_⟩
  rw [Units.coe_map,«Σ».torusRationalMap_eq_openImmersion]
  change openImmersionGlobalToFunctionField j
    ((Scheme.ΓSpecIso S).inv (φ a))=«Σ».normalizedChartGenerator k D s
  rw [show (Scheme.ΓSpecIso S).inv (φ a)=(j.appIso ⊤).hom a by
    change (Scheme.ΓSpecIso S).inv ((Scheme.ΓSpecIso S).hom ((j.appIso ⊤).hom a)) = _
    exact (Scheme.ΓSpecIso S).hom_inv_id_apply _]
  rw [openImmersionRegularToFunctionField_eq_germ_image]
  simpa only [normalizedChartGenerator,Iso.hom_inv_id_apply] using ha

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normalizedCartier_linearlyEquivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_normalizedChartLaurentUnit
