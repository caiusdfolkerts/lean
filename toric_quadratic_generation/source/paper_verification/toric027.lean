module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import paper_verification.toric005
public import paper_verification.toric009
public import paper_verification.toric010
public import paper_verification.toric013
public import paper_verification.toric017
public import paper_verification.toric018
public import paper_verification.toric022
public import paper_verification.toric023
public import paper_verification.toric024
public import paper_verification.toric025
public import paper_verification.toric026
public import paper_verification.toric038
public import paper_verification.toric042

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLineFan
section Source_ToricProjectiveLineFan

-- original header: module

-- original header: public import PaperVerification.ToricFanNoetherian
-- original header: public import PaperVerification.ToricFanConstruction
-- original header: public import Mathlib.Algebra.Polynomial.AlgebraMap

-- original header: @[expose] public section

/-!
# The actual two-chart projective line

The complete rank-one fan has the primitive rays `1` and `-1`. Its scheme
is the actual gluing of the two affine polynomial charts along their common
Laurent chart. The algebra equivalences below identify the coordinate on
each affine chart with the corresponding primitive character.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

def projectiveLineRay (negative : Bool) : Lattice 1 :=
  fun _ => if negative then -1 else 1

def projectiveLineBasis (negative : Bool) : Module.Basis (Fin 1) ℤ (Lattice 1) :=
  if negative then (Pi.basisFun ℤ (Fin 1)).map (LinearEquiv.neg ℤ)
  else Pi.basisFun ℤ (Fin 1)

theorem projectiveLineBasis_apply (negative : Bool) (i : Fin 1) :
    projectiveLineBasis negative i = projectiveLineRay negative := by
  cases negative <;> ext j <;>
    simp [projectiveLineBasis,projectiveLineRay,Pi.basisFun_apply,
      Subsingleton.elim i j]

theorem projectiveLineBasis_rays (negative : Bool) :
    Finset.univ.image (projectiveLineBasis negative) = {projectiveLineRay negative} := by
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩
    exact projectiveLineBasis_apply negative i
  · rintro rfl
    exact ⟨0,projectiveLineBasis_apply negative 0⟩

theorem projectiveLineRay_ne : projectiveLineRay false ≠ projectiveLineRay true := by
  intro h
  have hh := congrFun h (0 : Fin 1)
  norm_num [projectiveLineRay] at hh

theorem mem_finiteRayCone_singleton_iff {E : Type*} [AddCommGroup E]
    [Module ℝ E] (v x : E) :
    x∈finiteRayCone {v} ↔ ∃ a : ℝ, 0≤a ∧ a • v=x := by
  constructor
  · rintro ⟨c,hc,hx⟩
    exact ⟨c v,hc v (Finset.mem_singleton_self v),by simpa only [Finset.sum_singleton] using hx⟩
  · rintro ⟨a,ha,hx⟩
    exact ⟨fun _ => a,fun _ _ => ha,by simpa only [Finset.sum_singleton] using hx⟩

theorem mem_projectiveLineCone (negative : Bool) (x : Ambient 1) :
    x∈latticeRayCone {projectiveLineRay negative} ↔
      0≤(if negative then -x 0 else x 0) := by
  rw [latticeRayCone,Finset.image_singleton,mem_finiteRayCone_singleton_iff]
  cases negative
  · constructor
    · rintro ⟨a,ha,hx⟩
      have h := congrFun hx (0 : Fin 1)
      have ha0 : a=x 0 := by simpa [embed,projectiveLineRay] using h
      simpa only [ha0, Bool.false_eq_true, ite_false] using ha
    · intro hx
      refine ⟨x 0,hx,?_⟩
      ext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      simp [embed,projectiveLineRay,hi]
  · constructor
    · rintro ⟨a,ha,hx⟩
      have h := congrFun hx (0 : Fin 1)
      simp [embed,projectiveLineRay] at h
      change 0≤-x 0
      linarith
    · intro hx
      refine ⟨-x 0,hx,?_⟩
      ext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      simp [embed,projectiveLineRay,hi]

theorem projectiveLineCone_inter :
    latticeRayCone {projectiveLineRay false} ⊓
      latticeRayCone {projectiveLineRay true} = ⊥ := by
  ext x
  simp only [Submodule.mem_inf,mem_projectiveLineCone,Bool.false_eq_true,
    if_false,if_true,Submodule.mem_bot]
  constructor
  · intro h
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simp only [hi,Pi.zero_apply]
    linarith [h.1,h.2]
  · rintro rfl
    simp

theorem projectiveLineBasis_inter (a b : Bool) :
    latticeRayCone (Finset.univ.image (projectiveLineBasis a)) ⊓
      latticeRayCone (Finset.univ.image (projectiveLineBasis b)) =
        latticeRayCone ((Finset.univ.image (projectiveLineBasis a)) ∩
          (Finset.univ.image (projectiveLineBasis b))) := by
  rw [projectiveLineBasis_rays,projectiveLineBasis_rays]
  cases a <;> cases b
  · simp
  · have h : ({projectiveLineRay false} : Finset (Lattice 1)) ∩
        {projectiveLineRay true} = ∅ := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
      rintro ⟨rfl,hv⟩
      exact projectiveLineRay_ne hv
    rw [h,latticeRayCone_empty,projectiveLineCone_inter]
  · rw [inf_comm,Finset.inter_comm]
    have h : ({projectiveLineRay false} : Finset (Lattice 1)) ∩
        {projectiveLineRay true} = ∅ := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
      rintro ⟨rfl,hv⟩
      exact projectiveLineRay_ne hv
    rw [h,latticeRayCone_empty,projectiveLineCone_inter]
  · simp

theorem projectiveLineBasis_cover (x : Ambient 1) :
    ∃ negative : Bool,
      x∈latticeRayCone (Finset.univ.image (projectiveLineBasis negative)) := by
  by_cases hx : 0≤x 0
  · exact ⟨false,by simpa only [projectiveLineBasis_rays,mem_projectiveLineCone,
      Bool.false_eq_true,ite_false] using hx⟩
  · exact ⟨true,by simpa only [projectiveLineBasis_rays,mem_projectiveLineCone,
      ite_true] using
      neg_nonneg.mpr (le_of_not_ge hx)⟩

/-- The fan is proved smooth and complete by its actual real cones. -/
def projectiveLineFan : SmoothCompleteFan 1 :=
  fanOfBasisFamily projectiveLineBasis projectiveLineBasis_inter projectiveLineBasis_cover

theorem projectiveLineFan_isPure : projectiveLineFan.IsPure :=
  fanOfBasisFamily_isPure projectiveLineBasis projectiveLineBasis_inter projectiveLineBasis_cover

theorem projectiveLineRayCone_mem (negative : Bool) :
    {projectiveLineRay negative} ∈ projectiveLineFan.cones := by
  apply (mem_basisFamilyCones projectiveLineBasis _).mpr
  exact ⟨negative,by simpa only [projectiveLineBasis_rays] using
    (Finset.Subset.refl {projectiveLineRay negative})⟩

theorem mem_projectiveLineFan_cones (s : Finset (Lattice 1)) :
    s∈projectiveLineFan.cones ↔
      s=∅ ∨ s={projectiveLineRay false} ∨ s={projectiveLineRay true} := by
  rw [show projectiveLineFan.cones=basisFamilyCones projectiveLineBasis from rfl,
    mem_basisFamilyCones]
  simp only [projectiveLineBasis_rays,Finset.subset_singleton_iff]
  constructor
  · rintro ⟨b,h⟩
    rcases h with h|h
    · exact Or.inl h
    · cases b
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rintro (h|h|h)
    · exact ⟨false,Or.inl h⟩
    · exact ⟨false,Or.inr h⟩
    · exact ⟨true,Or.inr h⟩

theorem mem_projectiveLineDualCone (negative : Bool) (m : Lattice 1) :
    m∈dualConeMonoid {projectiveLineRay negative} ↔
      0≤(if negative then -m 0 else m 0) := by
  change (∀ u∈({projectiveLineRay negative} : Finset (Lattice 1)),
    0≤ integerPairing u m) ↔ _
  cases negative <;> simp [integerPairing,projectiveLineRay]

/-- Exact natural-number coordinates on the actual dual semigroup. -/
def projectiveLineSemigroupEquiv (negative : Bool) :
    dualConeMonoid {projectiveLineRay negative} ≃+ ℕ where
  toFun m := (if negative then -m.val 0 else m.val 0).toNat
  invFun a := ⟨fun _ => if negative then -(a : ℤ) else a,by
    rw [mem_projectiveLineDualCone]
    cases negative <;> simp⟩
  left_inv m := by
    apply Subtype.ext
    have hm := (mem_projectiveLineDualCone negative m.val).mp m.property
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    cases negative <;> simp only [hi,if_false,if_true] at hm ⊢
    · exact Int.toNat_of_nonneg hm
    · rw [Int.toNat_of_nonneg hm,neg_neg]
  right_inv a := by cases negative <;> simp
  map_add' m p := by
    have hm := (mem_projectiveLineDualCone negative m.val).mp m.property
    have hp := (mem_projectiveLineDualCone negative p.val).mp p.property
    cases negative
    · exact Int.toNat_add hm hp
    · change (-(m.val 0 + p.val 0)).toNat = (-m.val 0).toNat + (-p.val 0).toNat
      rw [neg_add]
      exact Int.toNat_add (by simpa using hm) (by simpa using hp)

variable (k : Type*) [Field k]

/-- Each affine chart is the actual affine line. -/
def projectiveLineChartRingEquiv (negative : Bool) :
    monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative}) ≃ₐ[k]
      Polynomial k :=
  (monoidChartAlgebraEquiv k _).symm.trans
    ((AddMonoidAlgebra.domCongr k k (projectiveLineSemigroupEquiv negative)).trans
      (Polynomial.toFinsuppIsoAlg k).symm)

/-- The usual two affine lines with inverted transition coordinate, as an
actual scheme obtained by the already verified common-face gluing. -/
abbrev projectiveLineScheme : Scheme := projectiveLineFan.fanScheme k

def projectiveLineChart (negative : Bool) :
    coneChart k {projectiveLineRay negative} ⟶ projectiveLineScheme k :=
  projectiveLineFan.fanChartMap k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩

instance projectiveLineChart_isOpenImmersion (negative : Bool) :
    IsOpenImmersion (projectiveLineChart k negative) :=
  projectiveLineFan.fanChartMap_isOpenImmersion k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩

instance projectiveLineScheme_isIntegral : IsIntegral (projectiveLineScheme k) :=
  inferInstanceAs (IsIntegral (projectiveLineFan.fanScheme k))

instance projectiveLineScheme_isNoetherian : IsNoetherian (projectiveLineScheme k) :=
  inferInstanceAs (IsNoetherian (projectiveLineFan.fanScheme k))

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineBasis_inter
#print axioms PaperVerification.ToricGeometry.projectiveLineChartRingEquiv
end
end Source_ToricProjectiveLineFan
-- END ORIGINAL PaperVerification.ToricProjectiveLineFan


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLineOrders
section Source_ToricProjectiveLineOrders

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineFan
-- original header: public import PaperVerification.ToricPolynomialBoundary
-- original header: public import PaperVerification.ToricOrbitChartMaps
-- original header: public import PaperVerification.ToricFanAction

-- original header: @[expose] public section

/-!
# Character orders on the actual two-chart projective line

Each smooth rank-one chart is identified with `Spec k[X]`, and its
primitive character is identified with the literal coordinate `X`.
Orders are consequently computed in the actual scheme local rings.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} [IsIntegral X]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]

/-- Actual affine coordinate maps commute with restriction along a
specified affine open morphism. -/
theorem affineOpenCoordinateMap_comp (r : R) :
    affineOpenCoordinateMap S (Spec.map φ ≫ j) (φ r) =
      affineOpenCoordinateMap R j r := by
  have hsec : (Scheme.ΓSpecIso S).inv (φ r) =
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) :=
    congrArg (fun g => g r) (Scheme.ΓSpecIso_inv_naturality φ)
  change openImmersionGlobalToFunctionField (Spec.map φ ≫ j)
      ((Scheme.ΓSpecIso S).inv (φ r)) =
    openImmersionGlobalToFunctionField j ((Scheme.ΓSpecIso R).inv r)
  rw [hsec]
  exact openImmersionGlobalToFunctionField_restrict
    (Spec.map φ) j ((Scheme.ΓSpecIso R).inv r)

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open scoped Classical

variable (k : Type u) [Field k]

/-- The actual affine-line chart map, including the algebra equivalence
which determines its coordinate. -/
def projectiveLinePolynomialChart (negative : Bool) :
    Spec (.of (Polynomial k)) ⟶ projectiveLineScheme k :=
  Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom ≫
    projectiveLineChart k negative

instance projectiveLinePolynomialChart_isOpenImmersion (negative : Bool) :
    IsOpenImmersion (projectiveLinePolynomialChart k negative) := by
  let s : projectiveLineFan.ConeIndex :=
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩
  let R : CommRingCat := .of (monoidChartAlgebra k (dualConeMonoid s.val))
  let S : CommRingCat := .of (Polynomial k)
  let j : Spec R ⟶ projectiveLineScheme k := projectiveLineFan.fanChartMap k s
  let φ : R ⟶ S :=
    (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom
  letI : IsOpenImmersion j := projectiveLineFan.fanChartMap_isOpenImmersion k s
  letI : IsOpenImmersion (Spec.map φ) := by
    dsimp [φ]
    infer_instance
  change IsOpenImmersion (Spec.map φ ≫ j)
  exact IsOpenImmersion.comp (Spec.map φ) j

def projectiveLineBoundaryPoint (negative : Bool) : projectiveLineScheme k :=
  projectiveLinePolynomialChart k negative (polynomialOrigin k)

/-- The primitive character of either one-dimensional cone is its
ordinary polynomial coordinate. -/
theorem projectiveLineChartRingEquiv_primitive (negative : Bool) :
    projectiveLineChartRingEquiv k negative
      (chartCharacter k (dualConeMonoid {projectiveLineRay negative})
        (projectiveLineRay negative) (by
          rw [mem_projectiveLineDualCone]
          cases negative <;> norm_num [projectiveLineRay])) = Polynomial.X := by
  apply (Polynomial.toFinsuppIsoAlg k).injective
  simp only [projectiveLineChartRingEquiv,AlgEquiv.trans_apply,
    monoidChartAlgebraEquiv_symm_character,AlgEquiv.apply_symm_apply,
    AddMonoidAlgebra.domCongr_single]
  cases negative <;>
    simp [projectiveLineSemigroupEquiv,projectiveLineRay,
      Polynomial.toFinsuppIsoAlg]

theorem projectiveLine_coordinate_rationalCharacter (negative : Bool) :
    affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative) Polynomial.X =
        (projectiveLineFan.rationalCharacter k (projectiveLineRay negative) :
          (projectiveLineScheme k).functionField) := by
  let s : projectiveLineFan.ConeIndex :=
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩
  let R : CommRingCat := .of (monoidChartAlgebra k (dualConeMonoid s.val))
  let S : CommRingCat := .of (Polynomial k)
  let j : Spec R ⟶ projectiveLineScheme k := projectiveLineFan.fanChartMap k s
  let φ : R ⟶ S :=
    (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom
  letI : IsOpenImmersion j := projectiveLineFan.fanChartMap_isOpenImmersion k s
  letI : IsOpenImmersion (Spec.map φ) := by
    dsimp [φ]
    infer_instance
  have hm : projectiveLineRay negative∈dualConeMonoid s.val := by
    rw [mem_projectiveLineDualCone]
    cases negative <;> norm_num [projectiveLineRay]
  let r := chartCharacter k (dualConeMonoid s.val) (projectiveLineRay negative) hm
  rw [← projectiveLineChartRingEquiv_primitive k negative]
  exact (affineOpenCoordinateMap_comp R S j φ r).trans
      (projectiveLineFan.chartRationalMap_character k s
        (projectiveLineRay negative) hm)

theorem projectiveLine_character_as_power (negative : Bool) (m : Lattice 1) :
    projectiveLineFan.rationalCharacter k m =
      (projectiveLineFan.rationalCharacter k (projectiveLineRay negative)) ^
        (if negative then -m 0 else m 0) := by
  have hm : m = (if negative then -m 0 else m 0) • projectiveLineRay negative := by
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    cases negative <;> simp [projectiveLineRay,hi]
  nth_rw 1 [hm]
  exact (projectiveLineFan.rationalCharacterHom k).map_zpow
    (Multiplicative.ofAdd (projectiveLineRay negative)) _

/-- All character orders on each actual affine chart, for every integer
character and every actual scheme point. -/
theorem projectiveLine_character_order (negative : Bool) (m : Lattice 1)
    (p : PrimeSpectrum (Polynomial k)) :
    (projectiveLineScheme k).ord
      (projectiveLineFan.rationalCharacter k m : (projectiveLineScheme k).functionField)
      (projectiveLinePolynomialChart k negative p) =
      if p=polynomialOrigin k then (if negative then -m 0 else m 0) else 0 := by
  rw [projectiveLine_character_as_power k negative m,Units.val_zpow_eq_zpow_val,
    ← projectiveLine_coordinate_rationalCharacter k negative]
  exact affineLine_coordinate_zpow_order k
    (projectiveLinePolynomialChart k negative) _ p

theorem projectiveLine_character_order_boundary (negative : Bool) (m : Lattice 1) :
    (projectiveLineScheme k).ord
      (projectiveLineFan.rationalCharacter k m : (projectiveLineScheme k).functionField)
      (projectiveLineBoundaryPoint k negative) = if negative then -m 0 else m 0 := by
  simpa only [projectiveLineBoundaryPoint,if_pos rfl,ite_true] using
    projectiveLine_character_order k negative m (polynomialOrigin k)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_character_order
end
end Source_ToricProjectiveLineOrders
-- END ORIGINAL PaperVerification.ToricProjectiveLineOrders


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLineDegree
section Source_ToricProjectiveLineDegree

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineOrders
-- original header: public import PaperVerification.ToricCocycleOrders
-- original header: public import PaperVerification.ToricFanCartierCocycle

-- original header: @[expose] public section

/-!
# The actual divisor degree on the rank-one fan

For a Cartier divisor specified by integral coefficients at the two rays,
the actual Weil cycle is supported at the two actual rational boundary
points. Its coefficients are the two specified integers. Both residue
degrees are proved to be one, so Mathlib's cycle degree is their sum.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open scoped Classical

def projectiveLineFullCone (negative : Bool) : projectiveLineFan.fullCones :=
  ⟨{projectiveLineRay negative},Finset.mem_filter.mpr
    ⟨projectiveLineRayCone_mem negative,Finset.card_singleton _⟩⟩

theorem projectiveLineFullCone_surjective :
    Function.Surjective projectiveLineFullCone := by
  intro s
  rcases (mem_projectiveLineFan_cones s.val).mp (projectiveLineFan.fullCones_mem s)
    with h|h|h
  · have hc := projectiveLineFan.fullCones_card s
    simp only [h,Finset.card_empty] at hc
    omega
  · exact ⟨false,Subtype.ext h.symm⟩
  · exact ⟨true,Subtype.ext h.symm⟩

variable (k : Type u) [Field k]

theorem projectiveLinePolynomialChart_jointly_surjective (x : projectiveLineScheme k) :
    ∃ (negative : Bool) (p : PrimeSpectrum (Polynomial k)),
      projectiveLinePolynomialChart k negative p=x := by
  obtain ⟨s,y,hy⟩ := projectiveLineFan.fullChartOpen_cover k
    projectiveLineFan_isPure x
  obtain ⟨negative,rfl⟩ := projectiveLineFullCone_surjective s
  obtain ⟨p,hp⟩ :=
    (Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom).homeomorph.surjective y
  refine ⟨negative,p,?_⟩
  have hy' : projectiveLineChart k negative y = x := hy
  change projectiveLineChart k negative
    ((Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom) p) = x
  exact (congrArg (projectiveLineChart k negative) hp).trans hy'

theorem projectiveLineBoundaryPoint_ne :
    projectiveLineBoundaryPoint k false ≠ projectiveLineBoundaryPoint k true := by
  intro h
  have hh := congrArg (fun x => (projectiveLineScheme k).ord
    (projectiveLineFan.rationalCharacter k (projectiveLineRay false) :
      (projectiveLineScheme k).functionField) x) h
  rw [projectiveLine_character_order_boundary,projectiveLine_character_order_boundary] at hh
  norm_num [projectiveLineRay] at hh

/-- Each boundary point is an actual rational point over the field. -/
def projectiveLineBoundarySection (negative : Bool) :
    Spec (.of k) ⟶ projectiveLineScheme k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    projectiveLinePolynomialChart k negative

theorem projectiveLineBoundarySection_isSection (negative : Bool) :
    projectiveLineBoundarySection k negative ≫
      projectiveLineFan.fanSchemeStructureMap k = 𝟙 (Spec (.of k)) := by
  let s := projectiveLineFan.fullConeIndex (projectiveLineFullCone negative)
  have hj : projectiveLineFan.fanChartMap k s ≫
      projectiveLineFan.fanSchemeStructureMap k =
        Spec.map (CommRingCat.ofHom (algebraMap k
          (monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative})))) :=
    comp_over (projectiveLineFan.fanChartMap k s) (Spec (.of k))
  unfold projectiveLineBoundarySection projectiveLinePolynomialChart projectiveLineChart
  erw [Category.assoc,Category.assoc,hj,← Spec.map_comp,← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  change Polynomial.eval 0
    (projectiveLineChartRingEquiv k negative (algebraMap k _ a)) = a
  rw [AlgEquiv.commutes]
  simp

theorem projectiveLineBoundarySection_apply (negative : Bool) :
    projectiveLineBoundarySection k negative (⊥ : PrimeSpectrum k) =
      projectiveLineBoundaryPoint k negative := by
  change projectiveLinePolynomialChart k negative
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
      (⊥ : PrimeSpectrum k)) = _
  congr 1

theorem projectiveLineBoundaryPoint_residueDegree (negative : Bool) :
    (projectiveLineFan.fanSchemeStructureMap k).residueDegree
      (projectiveLineBoundaryPoint k negative) = 1 := by
  rw [← projectiveLineBoundarySection_apply k negative]
  exact residueDegree_of_section (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLineBoundarySection k negative)
    (projectiveLineBoundarySection_isSection k negative) (⊥ : PrimeSpectrum k)

def projectiveLineCartierData (a : Lattice 1→ℤ) : CartierData (projectiveLineScheme k) :=
  projectiveLineFan.fanCartierData k projectiveLineFan_isPure a

theorem projectiveLine_weilCoefficient_chart (a : Lattice 1→ℤ) (negative : Bool)
    (p : PrimeSpectrum (Polynomial k)) :
    (projectiveLineCartierData k a).weilCoefficient
      (projectiveLinePolynomialChart k negative p) =
        if p=polynomialOrigin k then a (projectiveLineRay negative) else 0 := by
  let C := projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a
  let s := projectiveLineFullCone negative
  have hx : projectiveLinePolynomialChart k negative p∈C.openSet ⟨s⟩ :=
    ⟨Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom p,rfl⟩
  change C.toCartierData.weilCoefficient (projectiveLinePolynomialChart k negative p) = _
  erw [C.weilCoefficient_eq ⟨s⟩ hx]
  change -(projectiveLineScheme k).ord
    (projectiveLineFan.rationalCharacter k
      (projectiveLineFan.cartierLatticePoint a s) : (projectiveLineScheme k).functionField)
      (projectiveLinePolynomialChart k negative p) = _
  rw [projectiveLine_character_order]
  have hp := projectiveLineFan.cartierLatticePoint_pairing a s
    (projectiveLineRay negative) (Finset.mem_singleton_self _)
  have hv : (if negative then -(projectiveLineFan.cartierLatticePoint a s) 0
      else (projectiveLineFan.cartierLatticePoint a s) 0) =
        -a (projectiveLineRay negative) := by
    cases negative <;> simpa only [integerPairing,Fin.sum_univ_one,
      projectiveLineRay,Bool.false_eq_true,ite_true,ite_false,neg_one_mul,one_mul] using hp
  rw [hv]
  split_ifs <;> simp

theorem projectiveLine_weilCoefficient_boundary (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).weilCoefficient (projectiveLineBoundaryPoint k negative) =
      a (projectiveLineRay negative) := by
  simpa only [projectiveLineBoundaryPoint,if_pos rfl,ite_true] using
    projectiveLine_weilCoefficient_chart k a negative (polynomialOrigin k)

theorem projectiveLine_weilCoefficient_support (a : Lattice 1→ℤ) :
    Function.support (projectiveLineCartierData k a).weilCoefficient ⊆
      ({projectiveLineBoundaryPoint k false,projectiveLineBoundaryPoint k true} :
        Finset (projectiveLineScheme k)) := by
  intro x hx
  obtain ⟨negative,p,rfl⟩ := projectiveLinePolynomialChart_jointly_surjective k x
  have hp : p=polynomialOrigin k := by
    by_contra hp
    exact hx (by rw [projectiveLine_weilCoefficient_chart,if_neg hp])
  subst p
  cases negative <;> simp [projectiveLineBoundaryPoint]

theorem projectiveLine_weilCoefficient_locallyFinite (a : Lattice 1→ℤ) :
    LocallyFiniteSupport (projectiveLineCartierData k a).weilCoefficient :=
  (projectiveLineCartierData k a).locallyFiniteSupport_weilCoefficient_of_finite
    ((Finset.finite_toSet _).subset (projectiveLine_weilCoefficient_support k a))

/-- The actual divisor degree, computed using actual local orders and
actual residue-field extensions. -/
theorem projectiveLineCartier_degree (a : Lattice 1→ℤ) :
    (projectiveLineCartierData k a).degree
      (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k a) =
        a (projectiveLineRay false)+a (projectiveLineRay true) := by
  rw [(projectiveLineCartierData k a).degree_eq_sum_of_support_subset
    (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLine_weilCoefficient_locallyFinite k a)
    {projectiveLineBoundaryPoint k false,projectiveLineBoundaryPoint k true}
    (projectiveLine_weilCoefficient_support k a)]
  simp [projectiveLineBoundaryPoint_ne,projectiveLineBoundaryPoint_residueDegree,
    projectiveLine_weilCoefficient_boundary]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_degree
end
end Source_ToricProjectiveLineDegree
-- END ORIGINAL PaperVerification.ToricProjectiveLineDegree


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLineUnits
section Source_ToricProjectiveLineUnits

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineDegree
-- original header: public import PaperVerification.ToricAffinePullbackSections
-- original header: public import PaperVerification.ToricFanRegularCharacters
-- original header: public import Mathlib.Algebra.Polynomial.Degree.Units

-- original header: @[expose] public section

/-!
# Units on the actual affine-line charts

Every regular unit on either affine-line chart is an actual nonzero
constant, by the polynomial-unit theorem. Its rational value therefore
has zero order at every point of the complete curve, including the point
outside that chart. This is the key input for degree invariance under
an arbitrary isomorphism of line bundles.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

theorem projectiveLinePolynomialChart_image (negative : Bool) :
    (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens) =
      projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative) := by
  ext x
  change (∃ p : PrimeSpectrum (Polynomial k),p∈(⊤ : (Spec (.of (Polynomial k))).Opens) ∧
    projectiveLinePolynomialChart k negative p=x) ↔
      ∃ q,projectiveLineChart k negative q=x
  constructor
  · rintro ⟨p,hp,hpx⟩
    exact ⟨Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom p,hpx⟩
  · rintro ⟨q,hq⟩
    obtain ⟨p,hp⟩ :=
      (Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom).homeomorph.surjective q
    refine ⟨p,trivial,?_⟩
    change projectiveLineChart k negative
      ((Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom) p) = x
    exact (congrArg (projectiveLineChart k negative) hp).trans hq

theorem projectiveLine_constant_coordinate (negative : Bool) (c : k) :
    affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative) (Polynomial.C c) =
        projectiveLineFan.rationalScalar k c := by
  let R := monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative})
  let j : Spec (.of R) ⟶ projectiveLineScheme k := projectiveLineChart k negative
  letI : IsOpenImmersion j := projectiveLineChart_isOpenImmersion k negative
  have h : affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative)
      (projectiveLineChartRingEquiv k negative (algebraMap k R c)) =
      affineOpenCoordinateMap (.of R) j (algebraMap k R c) :=
    affineOpenCoordinateMap_comp (.of R) (.of (Polynomial k)) j
      (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom _
  rw [(projectiveLineChartRingEquiv k negative).commutes] at h
  exact h.trans (projectiveLineFan.chartRationalMap_eq_torusRationalMap k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩ _)

theorem projectiveLine_rationalScalar_order (c : kˣ) (x : projectiveLineScheme k) :
    (projectiveLineScheme k).ord (projectiveLineFan.rationalScalar k (c : k)) x=0 := by
  have hc : projectiveLineFan.rationalScalar k (c : k)≠0 :=
    Units.ne_zero (projectiveLineFan.rationalScalarUnit k c)
  obtain ⟨a,ha⟩ := (regular_unit_iff_stalkwise (projectiveLineScheme k) ⊤
    (projectiveLineFan.rationalScalar k (c : k)) hc).mpr (by
      constructor
      · intro y hy
        exact projectiveLineFan.rationalScalar_mem_regularAt k (c : k) y
      · intro y hy
        exact (map_inv₀ (projectiveLineFan.rationalScalar k) (c : k)) ▸
          projectiveLineFan.rationalScalar_mem_regularAt k ((c : k)⁻¹) y)
  rw [← ha]
  exact (projectiveLineScheme k).ord_of_isUnit a.isUnit (show x∈(⊤ : (projectiveLineScheme k).Opens) from trivial)

theorem projectiveLine_polynomialChartUnit_scalar (negative : Bool)
    (u : Γ(projectiveLineScheme k,
      (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens))ˣ) :
    letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
    ∃ c : kˣ,(projectiveLineScheme k).germToFunctionField
      ((projectiveLinePolynomialChart k negative) ''ᵁ ⊤) (u : Γ(projectiveLineScheme k,_)) =
        projectiveLineFan.rationalScalar k (c : k) := by
  let j := projectiveLinePolynomialChart k negative
  let R := CommRingCat.of (Polynomial k)
  let U := j ''ᵁ (⊤ : (Spec R).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  let e : Γ(projectiveLineScheme k,U) ≃+* Polynomial k :=
    ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have he : IsUnit (e (u : Γ(projectiveLineScheme k,U))) := u.isUnit.map e
  obtain ⟨r,hr,hp⟩ := Polynomial.isUnit_iff.mp he
  obtain ⟨c,hc⟩ := hr
  refine ⟨c,?_⟩
  have hu : (u : Γ(projectiveLineScheme k,U)) =
      affineChartSection R j (e (u : Γ(projectiveLineScheme k,U))) := by
    change (u : Γ(projectiveLineScheme k,U)) = e.symm (e (u : Γ(projectiveLineScheme k,U)))
    exact (e.symm_apply_apply _).symm
  rw [hu,affineChartSection_germ,← hp,← hc]
  exact projectiveLine_constant_coordinate k negative (c : k)

theorem projectiveLine_polynomialChartUnit_order (negative : Bool)
    (u : Γ(projectiveLineScheme k,
      (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens))ˣ)
    (x : projectiveLineScheme k) :
    letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
    (projectiveLineScheme k).ord
      ((projectiveLineScheme k).germToFunctionField
        ((projectiveLinePolynomialChart k negative) ''ᵁ ⊤) (u : Γ(projectiveLineScheme k,_))) x=0 := by
  letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
  obtain ⟨c,hc⟩ := projectiveLine_polynomialChartUnit_scalar k negative u
  rw [hc]
  exact projectiveLine_rationalScalar_order k c x

theorem projectiveLine_fullChartUnit_order (negative : Bool)
    [Nonempty (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))]
    (u : Γ(projectiveLineScheme k,
      projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))ˣ)
    (x : projectiveLineScheme k) :
    (projectiveLineScheme k).ord
      ((projectiveLineScheme k).germToFunctionField
        (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))
        (u : Γ(projectiveLineScheme k,_))) x=0 := by
  let j := projectiveLinePolynomialChart k negative
  let U := j ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  let φ := (projectiveLineScheme k).presheaf.map
    (eqToHom (projectiveLinePolynomialChart_image k negative)).op
  have h := projectiveLine_polynomialChartUnit_order k negative (Units.map φ.hom u) x
  change (projectiveLineScheme k).ord
    ((projectiveLineScheme k).germToFunctionField U
      ((projectiveLineScheme k).presheaf.map
        (eqToHom (projectiveLinePolynomialChart_image k negative)).op
          (u : Γ(projectiveLineScheme k,_)))) x = 0 at h
  have hr := germToFunctionField_restrict (projectiveLineScheme k)
    (eqToHom (projectiveLinePolynomialChart_image k negative))
      (u : Γ(projectiveLineScheme k,_))
  exact (congrArg (fun r => (projectiveLineScheme k).ord r x) hr).symm.trans h

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_fullChartUnit_order
end
end Source_ToricProjectiveLineUnits
-- END ORIGINAL PaperVerification.ToricProjectiveLineUnits


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLinePicardDegree
section Source_ToricProjectiveLinePicardDegree

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineUnits
-- original header: public import PaperVerification.ToricCartierFrameIsomorphisms
-- original header: public import PaperVerification.ToricArbitraryCartierFan

-- original header: @[expose] public section

/-!
# Degree of the actual line bundle on the rank-one fan

An arbitrary isomorphism of the two Cartier sheaves preserves the sum of
their ray coefficients. The proof compares their genuine local frames:
the changes on the two affine-line charts are polynomial units, and the
remaining transition ratio is measured by actual local order. Thus the
degree is a property of the actual line bundle, not of a chosen fractional
embedding. Every Cartier sheaf has such a fan presentation by the proved
arbitrary-Cartier classification.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

theorem projectiveLine_cartierPoint_coordinate (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineFan.cartierLatticePoint a (projectiveLineFullCone negative)) 0 =
      if negative then a (projectiveLineRay true) else -a (projectiveLineRay false) := by
  have h := projectiveLineFan.cartierLatticePoint_pairing a
    (projectiveLineFullCone negative) (projectiveLineRay negative)
      (Finset.mem_singleton_self _)
  cases negative <;> simp only [integerPairing,Fin.sum_univ_one,
    projectiveLineRay,Bool.false_eq_true,ite_true,ite_false,neg_one_mul,one_mul] at h ⊢ <;> omega

instance projectiveLine_fullChart_nonempty (negative : Bool) :
    Nonempty (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative)) := by
  rw [← projectiveLinePolynomialChart_image k negative]
  exact openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤

def projectiveLineCartierFrame (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).Frame
      (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative)) :=
  (projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).localFrame
    ⟨projectiveLineFullCone negative⟩

theorem projectiveLineCartierFrame_generator (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).frameRationalGenerator
      (projectiveLineCartierFrame k a negative) =
        (projectiveLineFan.rationalCharacter k
          (projectiveLineFan.cartierLatticePoint a (projectiveLineFullCone negative)) :
            (projectiveLineScheme k).functionField) := by
  letI : Nonempty ((projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).openSet
      ⟨projectiveLineFullCone negative⟩) := projectiveLine_fullChart_nonempty k negative
  exact (projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a).localFrame_rationalGenerator
    ⟨projectiveLineFullCone negative⟩

theorem projectiveLineCartierFrame_order (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineScheme k).ord
      ((projectiveLineCartierData k a).frameRationalGenerator
        (projectiveLineCartierFrame k a negative)) (projectiveLineBoundaryPoint k false) =
      if negative then a (projectiveLineRay true) else -a (projectiveLineRay false) := by
  rw [projectiveLineCartierFrame_generator,projectiveLine_character_order_boundary]
  exact projectiveLine_cartierPoint_coordinate a negative

/-- Degree invariance is proved for every genuine sheaf isomorphism,
without requiring compatibility with the rational embeddings. -/
theorem projectiveLine_coefficientSum_eq_of_sheafIso
    (a b : Lattice 1→ℤ)
    (F : (projectiveLineCartierData k a).sheaf ≅ (projectiveLineCartierData k b).sheaf) :
    a (projectiveLineRay false)+a (projectiveLineRay true) =
      b (projectiveLineRay false)+b (projectiveLineRay true) := by
  let X := projectiveLineScheme k
  let D := projectiveLineCartierData k a
  let E := projectiveLineCartierData k b
  let x := projectiveLineBoundaryPoint k false
  let e (negative : Bool) := projectiveLineCartierFrame k a negative
  let q (negative : Bool) := projectiveLineCartierFrame k b negative
  have hsame (negative : Bool) :
      X.ord (D.frameRationalGenerator (e negative)) x =
        X.ord (D.frameRationalGenerator (ModuleFrame.precompose F (q negative))) x := by
    obtain ⟨u,hu⟩ := D.exists_frameTransitionUnit
      (e negative) (ModuleFrame.precompose F (q negative)) le_rfl le_rfl
    have hzero := projectiveLine_fullChartUnit_order k negative u x
    rw [hu,rationalOrder_div (D.frameRationalGenerator_ne_zero _)
      (D.frameRationalGenerator_ne_zero _)] at hzero
    omega
  have hratio := D.precompose_frameRatio E F (q false) (q true)
  have hord := congrArg (fun r : X.functionField=>X.ord r x) hratio
  rw [rationalOrder_div (D.frameRationalGenerator_ne_zero _)
      (D.frameRationalGenerator_ne_zero _),
    rationalOrder_div (E.frameRationalGenerator_ne_zero _)
      (E.frameRationalGenerator_ne_zero _),← hsame false,← hsame true] at hord
  change X.ord (D.frameRationalGenerator (projectiveLineCartierFrame k a false)) x -
      X.ord (D.frameRationalGenerator (projectiveLineCartierFrame k a true)) x =
    X.ord (E.frameRationalGenerator (projectiveLineCartierFrame k b false)) x -
      X.ord (E.frameRationalGenerator (projectiveLineCartierFrame k b true)) x at hord
  rw [projectiveLineCartierFrame_order,projectiveLineCartierFrame_order,
    projectiveLineCartierFrame_order,projectiveLineCartierFrame_order] at hord
  simp only [Bool.false_eq_true,if_false,if_true] at hord
  omega

theorem projectiveLineCartier_degree_iso
    (a b : Lattice 1→ℤ)
    (F : (projectiveLineCartierData k a).sheaf ≅ (projectiveLineCartierData k b).sheaf) :
    (projectiveLineCartierData k a).degree (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k a) =
    (projectiveLineCartierData k b).degree (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k b) := by
  rw [projectiveLineCartier_degree,projectiveLineCartier_degree]
  exact projectiveLine_coefficientSum_eq_of_sheafIso k a b F

/-- Degree via the actual integral fan Cartier presentations. Existence
for arbitrary Cartier sheaves and uniqueness are proved below. Each such
presentation has exactly this Mathlib Weil-cycle degree. -/
def ProjectiveLineHasDegree (M : (projectiveLineScheme k).Modules) (d : ℤ) : Prop :=
  ∃ a : Lattice 1→ℤ, Nonempty (M ≅ (projectiveLineCartierData k a).sheaf) ∧
    a (projectiveLineRay false)+a (projectiveLineRay true)=d

theorem projectiveLineHasDegree_unique {M : (projectiveLineScheme k).Modules}
    {d e : ℤ} (hd : ProjectiveLineHasDegree k M d) (he : ProjectiveLineHasDegree k M e) : d=e := by
  obtain ⟨a,⟨Fa⟩,ha⟩ := hd
  obtain ⟨b,⟨Fb⟩,hb⟩ := he
  rw [← ha,← hb]
  exact projectiveLine_coefficientSum_eq_of_sheafIso k a b (Fa.symm ≪≫ Fb)

theorem projectiveLineHasDegree_iso {M N : (projectiveLineScheme k).Modules}
    (F : M ≅ N) (d : ℤ) : ProjectiveLineHasDegree k M d ↔ ProjectiveLineHasDegree k N d := by
  constructor
  · rintro ⟨a,⟨G⟩,ha⟩
    exact ⟨a,⟨F.symm ≪≫ G⟩,ha⟩
  · rintro ⟨a,⟨G⟩,ha⟩
    exact ⟨a,⟨F ≪≫ G⟩,ha⟩

theorem projectiveLineCartier_hasDegree (a : Lattice 1→ℤ) :
    ProjectiveLineHasDegree k (projectiveLineCartierData k a).sheaf
      (a (projectiveLineRay false)+a (projectiveLineRay true)) :=
  ⟨a,⟨Iso.refl _⟩,rfl⟩

/-- Every arbitrary actual Cartier sheaf has a unique degree; no
character presentation or equivariance is assumed of the input. -/
theorem projectiveLineCartier_existsUnique_degree (D : CartierData (projectiveLineScheme k)) :
    ∃! d : ℤ,ProjectiveLineHasDegree k D.sheaf d := by
  let a := projectiveLineFan.cartierCoefficients k projectiveLineFan_isPure D
  let d := a (projectiveLineRay false)+a (projectiveLineRay true)
  have hd : ProjectiveLineHasDegree k D.sheaf d :=
    ⟨a,projectiveLineFan.cartierData_linearlyEquivalent_fanCartier k projectiveLineFan_isPure D,rfl⟩
  exact ⟨d,hd,fun e he=>projectiveLineHasDegree_unique k he hd⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_coefficientSum_eq_of_sheafIso
#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_existsUnique_degree
end
end Source_ToricProjectiveLinePicardDegree
-- END ORIGINAL PaperVerification.ToricProjectiveLinePicardDegree


-- BEGIN ORIGINAL PaperVerification.ToricRankOneFans
section Source_ToricRankOneFans

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineDegree
-- original header: public import Mathlib.Algebra.Group.Int.Units

-- original header: @[expose] public section

/-!
# Every smooth complete rank-one fan is the two-ray fan

A basis of the rank-one integral lattice has generator `1` or `-1`.
Smoothness restricts each cone to one of these rays or the zero cone,
and completeness forces both rays. The result is an equality of the
actual fans and hence an isomorphism of their actual glued schemes.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

theorem rankOneBasis_generator (b : Module.Basis (Fin 1) ℤ (Lattice 1)) :
    b 0=projectiveLineRay false ∨ b 0=projectiveLineRay true := by
  have hsum := b.sum_repr (projectiveLineRay false)
  have hmul : b 0 0 * b.repr (projectiveLineRay false) 0=1 := by
    have h := congrFun hsum (0 : Fin 1)
    simpa [Fin.sum_univ_one,projectiveLineRay,mul_comm] using h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h|h
  · left
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simpa [projectiveLineRay,hi] using h
  · right
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simpa [projectiveLineRay,hi] using h

namespace SmoothCompleteFan

theorem eq_of_cones_eq {d : ℕ} {«Σ» Γ : SmoothCompleteFan d}
    (h : «Σ».cones=Γ.cones) : «Σ»=Γ := by
  cases «Σ»
  cases Γ
  cases h
  rfl

variable («Σ» : SmoothCompleteFan 1)

theorem rankOne_cone_cases {s : Finset (Lattice 1)} (hs : s∈«Σ».cones) :
    s=∅ ∨ s={projectiveLineRay false} ∨ s={projectiveLineRay true} := by
  obtain ⟨b,I,rfl⟩ := «Σ».smooth s hs
  have hI : I⊆{(0 : Fin 1)} := by
    intro i hi
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  rcases Finset.subset_singleton_iff.mp hI with h|h
  · exact Or.inl (by rw [h,Finset.image_empty])
  · rw [h,Finset.image_singleton]
    rcases rankOneBasis_generator b with hb|hb
    · exact Or.inr (Or.inl (congrArg singleton hb))
    · exact Or.inr (Or.inr (congrArg singleton hb))

theorem rankOne_ray_mem (negative : Bool) :
    {projectiveLineRay negative}∈«Σ».cones := by
  obtain ⟨s,hs,hx⟩ := «Σ».complete (embed 1 (projectiveLineRay negative))
  rcases «Σ».rankOne_cone_cases hs with h|h|h
  · rw [h,latticeRayCone_empty] at hx
    have hz : embed 1 (projectiveLineRay negative)=0 := hx
    have h0 := congrFun hz (0 : Fin 1)
    cases negative <;> norm_num [embed,projectiveLineRay] at h0
  · rw [h,mem_projectiveLineCone] at hx
    cases negative
    · simpa only [h] using hs
    · norm_num [embed,projectiveLineRay] at hx
  · rw [h,mem_projectiveLineCone] at hx
    cases negative
    · norm_num [embed,projectiveLineRay] at hx
    · simpa only [h] using hs

/-- There is no extra classification hypothesis in dimension one. -/
theorem rankOne_eq_projectiveLine : «Σ»=projectiveLineFan := by
  apply eq_of_cones_eq
  ext s
  rw [mem_projectiveLineFan_cones]
  constructor
  · exact «Σ».rankOne_cone_cases
  · rintro (rfl|rfl|rfl)
    · exact «Σ».empty_mem
    · exact «Σ».rankOne_ray_mem false
    · exact «Σ».rankOne_ray_mem true

variable (k : Type u) [Field k]

def rankOneSchemeIso : «Σ».fanScheme k ≅ projectiveLineScheme k :=
  eqToIso (congrArg (fun Γ : SmoothCompleteFan 1 => Γ.fanScheme k)
    «Σ».rankOne_eq_projectiveLine)

end SmoothCompleteFan

/-- The rank condition is an equality of ordinary lattice dimensions,
not a replacement definition of a curve. -/
def oneDimensionalFanSchemeIso {d : ℕ} («Σ» : SmoothCompleteFan d)
    (hd : d=1) (k : Type u) [Field k] :
    «Σ».fanScheme k ≅ projectiveLineScheme k := by
  subst d
  exact «Σ».rankOneSchemeIso k

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rankOne_eq_projectiveLine
end
end Source_ToricRankOneFans
-- END ORIGINAL PaperVerification.ToricRankOneFans


-- BEGIN ORIGINAL PaperVerification.ToricRankOneDegree
section Source_ToricRankOneDegree

-- original header: module

-- original header: public import PaperVerification.ToricRankOneFans
-- original header: public import PaperVerification.ToricProjectiveLinePicardDegree

-- original header: @[expose] public section

/-! # Actual line-bundle degrees on arbitrary rank-one complete fans -/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

theorem projectiveLineFan_rays :
    projectiveLineFan.rays={projectiveLineRay false,projectiveLineRay true} := by
  ext u
  rw [projectiveLineFan.mem_rays_iff]
  constructor
  · rintro ⟨s,hs,hu⟩
    rcases (mem_projectiveLineFan_cones s).mp hs with h|h|h
    · rw [h] at hu
      exact (Finset.notMem_empty u hu).elim
    · simp only [h,Finset.mem_singleton] at hu
      simp [hu]
    · simp only [h,Finset.mem_singleton] at hu
      simp [hu]
  · intro hu
    rcases Finset.mem_insert.mp hu with h|h
    · subst u
      exact ⟨{projectiveLineRay false},projectiveLineRayCone_mem false,
        Finset.mem_singleton_self _⟩
    · have h' := Finset.mem_singleton.mp h
      subst u
      exact ⟨{projectiveLineRay true},projectiveLineRayCone_mem true,
        Finset.mem_singleton_self _⟩

namespace SmoothCompleteFan

variable {d : ℕ} (Γ : SmoothCompleteFan d) (hd : d=1)

include hd in
theorem oneDimensional_rays :
    Γ.rays={(fun _=>1 : Lattice d),(fun _=>-1 : Lattice d)} := by
  subst d
  rw [Γ.rankOne_eq_projectiveLine,projectiveLineFan_rays]
  rfl

variable (k : Type u) [Field k]

/-- Transport through the constructed actual scheme isomorphism to the
two-chart line, using the actual module-sheaf pullback functor. -/
def OneDimensionalHasDegree (M : (Γ.fanScheme k).Modules) (degree : ℤ) : Prop :=
  ProjectiveLineHasDegree k
    ((Scheme.Modules.pullback (oneDimensionalFanSchemeIso Γ hd k).inv).obj M) degree

theorem oneDimensionalHasDegree_unique {M : (Γ.fanScheme k).Modules}
    {r s : ℤ} (hr : Γ.OneDimensionalHasDegree hd k M r)
    (hs : Γ.OneDimensionalHasDegree hd k M s) : r=s :=
  projectiveLineHasDegree_unique k hr hs

theorem oneDimensionalHasDegree_iso {M N : (Γ.fanScheme k).Modules}
    (F : M ≅ N) (r : ℤ) :
    Γ.OneDimensionalHasDegree hd k M r ↔ Γ.OneDimensionalHasDegree hd k N r :=
  projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullback (oneDimensionalFanSchemeIso Γ hd k).inv).mapIso F) r

/-- The degree of the actual fan Cartier sheaf is the sum over its actual
two primitive rays. This is derived from local orders and residue degrees. -/
theorem oneDimensionalFanCartier_hasDegree (hpure : Γ.IsPure) (a : Lattice d→ℤ) :
    Γ.OneDimensionalHasDegree hd k (Γ.fanCartierData k hpure a).sheaf
      (∑ v∈Γ.rays,a v) := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  have hiso : oneDimensionalFanSchemeIso projectiveLineFan rfl k=
      Iso.refl (projectiveLineScheme k) := by
    rfl
  unfold OneDimensionalHasDegree
  rw [hiso]
  apply (projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullbackId (projectiveLineScheme k)).app
      (projectiveLineCartierData k a).sheaf) _).mpr
  change ProjectiveLineHasDegree k (projectiveLineCartierData k a).sheaf
    (∑ v∈projectiveLineFan.rays,a v)
  have h := projectiveLineCartier_hasDegree k a
  simpa only [projectiveLineFan_rays,Finset.sum_pair projectiveLineRay_ne] using h

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.oneDimensionalFanCartier_hasDegree
end
end Source_ToricRankOneDegree
-- END ORIGINAL PaperVerification.ToricRankOneDegree


-- BEGIN ORIGINAL PaperVerification.ToricChartCoaction
section Source_ToricChartCoaction

-- original header: module

-- original header: public import PaperVerification.ToricChartActions
-- original header: public import PaperVerification.ToricOrbitChartMaps

-- original header: @[expose] public section

/-! # Actual affine coactions and their genuine scheme-morphism equations -/

noncomputable section

universe u v w

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped TensorProduct

section Categorical

variable {C : Type u} {D : Type v} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {T Q A B : C}

/-- Naturality of the tensorator turns an actual algebra coaction
identity into the corresponding action identity after a monoidal functor. -/
theorem map_coaction_intertwining (r : T ⟶ Q) (f : B ⟶ A)
    (a : T ⊗ A ⟶ A) (b : Q ⊗ B ⟶ B)
    (h : T ◁ f ≫ a = r ▷ B ≫ b ≫ f) :
    F.obj T ◁ F.map f ≫ (Functor.LaxMonoidal.μ F T A ≫ F.map a) =
      F.map r ▷ F.obj B ≫ (Functor.LaxMonoidal.μ F Q B ≫ F.map b) ≫ F.map f := by
  rw [← Category.assoc,Functor.LaxMonoidal.μ_natural_right,Category.assoc,
    ← F.map_comp,h,F.map_comp,F.map_comp]
  rw [← Category.assoc,← Functor.LaxMonoidal.μ_natural_left,Category.assoc,Category.assoc]

end Categorical

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).LaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal

section AffineMorphism

variable (k : Type u) [CommRing k]

/-- The actual morphism of affine schemes associated to a coaction. -/
def affineCoactionMorphism {T A : Type u} [CommRing T] [CommRing A]
    [Algebra k T] [Algebra k A] (d : A →ₐ[k] T ⊗[k] A) :
    ((Spec (CommRingCat.of T)).asOver (Spec (CommRingCat.of k))) ⊗
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))) ⟶
        (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) :=
  Functor.LaxMonoidal.μ (algSpec (CommRingCat.of k))
      (op (CommAlgCat.of k T)) (op (CommAlgCat.of k A)) ≫
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom d).op

end AffineMorphism

section Characters

variable (k : Type (max u v)) [CommRing k] {M : Type v} [AddCommGroup M]

/-- The coaction on the literal chart subalgebra, transported through its
proved semigroup-algebra equivalence. -/
def monoidChartCoaction (S : AddSubmonoid M) :
    monoidChartAlgebra k S →ₐ[k]
      AddMonoidAlgebra k M ⊗[k] monoidChartAlgebra k S :=
  (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M))
    (monoidChartAlgebraEquiv k S).toAlgHom).comp
      ((semigroupChartCoaction k S).comp (monoidChartAlgebraEquiv k S).symm.toAlgHom)

@[simp] theorem monoidChartCoaction_character (S : AddSubmonoid M) (m : M) (hm : m∈S) :
    monoidChartCoaction k S (chartCharacter k S m hm) =
      AddMonoidAlgebra.single m 1 ⊗ₜ[k] chartCharacter k S m hm := by
  simp only [monoidChartCoaction,AlgHom.comp_apply,AlgEquiv.coe_algHom,
    monoidChartAlgebraEquiv_symm_character,semigroupChartCoaction_single,
    Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
    monoidChartAlgebraEquiv_single_character]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem semigroupChart_action_coaction (S : AddSubmonoid M) :
    γ[splitTorusOver k M,semigroupChartOver k S] =
      affineCoactionMorphism k (semigroupChartCoaction k S) := by
  apply Over.OverMorphism.ext
  exact semigroupChart_action_spec k S

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transported chart action really is the spectrum of the displayed
coaction on its actual coordinate subalgebra. -/
theorem monoidChart_action_coaction (S : AddSubmonoid M) :
    γ[splitTorusOver k M,monoidChartSchemeOver k S] =
      affineCoactionMorphism k (monoidChartCoaction k S) := by
  let F := algSpec (CommRingCat.of k)
  letI : F.LaxMonoidal :=
    (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal
  let T : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k M))
  let A : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (monoidChartAlgebra k S))
  let B : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k S))
  let e : A ⟶ B := (CommAlgCat.ofHom (monoidChartAlgebraEquiv k S).toAlgHom).op
  let e' : B ⟶ A := (CommAlgCat.ofHom (monoidChartAlgebraEquiv k S).symm.toAlgHom).op
  change (F.obj T ◁ F.map e) ≫
    γ[splitTorusOver k M,semigroupChartOver k S] ≫ F.map e' = _
  rw [semigroupChart_action_coaction]
  change (F.obj T ◁ F.map e) ≫
    (Functor.LaxMonoidal.μ F T B ≫ F.map
      (CommAlgCat.ofHom (semigroupChartCoaction k S)).op) ≫ F.map e' =
    Functor.LaxMonoidal.μ F T A ≫ F.map (CommAlgCat.ofHom (monoidChartCoaction k S)).op
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc F T e,
    ← F.map_comp,← F.map_comp]
  rfl

end Characters

section AffineIntertwining

variable (k : Type u) [CommRing k]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A literal coaction equation gives a literal affine action equation. -/
theorem affineCoaction_intertwining
    {T Q A B : Type u} [CommRing T] [CommRing Q] [CommRing A] [CommRing B]
    [Algebra k T] [Algebra k Q] [Algebra k A] [Algebra k B]
    (r : Q →ₐ[k] T) (f : A →ₐ[k] B)
    (a : A →ₐ[k] T ⊗[k] A) (b : B →ₐ[k] Q ⊗[k] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id k T) f).comp a =
      (Algebra.TensorProduct.map r (AlgHom.id k B)).comp (b.comp f)) :
    (Spec (CommRingCat.of T)).asOver (Spec (CommRingCat.of k)) ◁
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ affineCoactionMorphism k a =
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom r).op ▷
        (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of k))) ≫
      affineCoactionMorphism k b ≫
        (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op := by
  unfold affineCoactionMorphism
  apply map_coaction_intertwining (algSpec (CommRingCat.of k))
    (CommAlgCat.ofHom r).op (CommAlgCat.ofHom f).op
    (CommAlgCat.ofHom a).op (CommAlgCat.ofHom b).op
  exact congrArg (fun z => (CommAlgCat.ofHom z).op) h

end AffineIntertwining

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.monoidChart_action_coaction
end
end Source_ToricChartCoaction
-- END ORIGINAL PaperVerification.ToricChartCoaction


-- BEGIN ORIGINAL PaperVerification.ToricOrbitActions
section Source_ToricOrbitActions

-- original header: module

-- original header: public import PaperVerification.ToricChartCoaction
-- original header: public import PaperVerification.ToricFanAction
-- original header: public import PaperVerification.ToricOrbitClosedImmersion

-- original header: @[expose] public section

/-!
# Genuine torus invariance of the actual orbit closed immersion

The quotient torus is acted on through the homomorphism induced by the
saturated inclusion of its character lattice. The chart quotient kills
exactly the characters positive on the orbit cone. Its displayed coaction
identity is transported to actual affine schemes and then glued along the
actual open cover. The resulting equivariance is an equality of morphisms
over Spec(k), including arbitrary test schemes.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped TensorProduct

variable {n : ℕ} (k : Type u) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

/-- The actual pullback of characters along the quotient-torus map. -/
def orbitTorusCharacterMap :
    AddMonoidAlgebra k (Lattice (n-I.card)) →ₐ[k] AddMonoidAlgebra k (Lattice n) :=
  (AddMonoidAlgebra.mapDomainBialgHom k
    (faceTangentLattice b I).toAddMonoidHom).toAlgHom

@[simp] theorem orbitTorusCharacterMap_single (m : Lattice (n-I.card)) (a : k) :
    orbitTorusCharacterMap k b I (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single (faceTangentLattice b I m) a :=
  AddMonoidAlgebra.mapDomainBialgHom_single (R := k) _ m a

/-- The quotient map of actual split group schemes. -/
def orbitTorusMapOver :
    ToricSchemes.splitTorusOver k (Lattice n) ⟶
      ToricSchemes.splitTorusOver k (Lattice (n-I.card)) :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitTorusCharacterMap k b I)).op

instance orbitTorusMapOver_isMonHom : IsMonHom (orbitTorusMapOver k b I) := by
  change IsMonHom (((bialgSpec (CommRingCat.of k)).map
    (CommBialgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k
      (faceTangentLattice b I).toAddMonoidHom)).op).hom)
  infer_instance

/-- The quotient of a chart commutes with the genuine character
coactions, including the characters sent to zero. -/
theorem orbitQuotientAlgebraMap_coaction
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    (Algebra.TensorProduct.map
        (AlgHom.id k (AddMonoidAlgebra k (Lattice n)))
        (orbitQuotientAlgebraMap k b I s hIs)).comp
      (monoidChartCoaction k (dualConeMonoid s)) =
    (Algebra.TensorProduct.map (orbitTorusCharacterMap k b I)
        (AlgHom.id k (monoidChartAlgebra k
          (dualConeMonoid (orbitQuotientCone b I s))))).comp
      ((monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))).comp
        (orbitQuotientAlgebraMap k b I s hIs)) := by
  classical
  apply chartAlgHom_ext_characters
  intro m hm
  by_cases hann : ∀ u∈I.image b,integerPairing u m=0
  · have hproj : faceCharacterProjection b I m∈
        dualConeMonoid (orbitQuotientCone b I s) :=
      faceCharacterProjection_mem_quotientDualCone b I s ⟨⟨m,hm⟩,hann⟩
    have hmap : orbitQuotientAlgebraMap k b I s hIs
        (chartCharacter k (dualConeMonoid s) m hm) =
          chartCharacter k (dualConeMonoid (orbitQuotientCone b I s))
            (faceCharacterProjection b I m) hproj := by
      apply Subtype.ext
      rw [orbitQuotientAlgebraMap_character,dif_pos hann]
      rfl
    simp only [AlgHom.comp_apply,monoidChartCoaction_character,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply,hmap,
      orbitTorusCharacterMap_single,faceTangentLattice_projection b I m hann]
  · have hmap : orbitQuotientAlgebraMap k b I s hIs
        (chartCharacter k (dualConeMonoid s) m hm) = 0 := by
      apply Subtype.ext
      rw [orbitQuotientAlgebraMap_character,dif_neg hann]
      rfl
    simp only [AlgHom.comp_apply,monoidChartCoaction_character,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply,hmap,map_zero,
      TensorProduct.tmul_zero]

instance orbitQuotientChartMap_isOver
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    (orbitQuotientChartMap k b I s hIs).IsOver (Spec (CommRingCat.of k)) := by
  exact ⟨((algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitQuotientAlgebraMap k b I s hIs)).op).w⟩

/-- The actual affine orbit chart map intertwines the two group-scheme
actions through the actual quotient-torus homomorphism. -/
theorem orbitQuotientChartMap_action
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    ToricSchemes.splitTorusOver k (Lattice n) ◁
        (orbitQuotientChartMap k b I s hIs).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),
        (coneChart k s).asOver (Spec (CommRingCat.of k))] =
    orbitTorusMapOver k b I ▷
        (coneChart k (orbitQuotientCone b I s)).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice (n-I.card)),
        (coneChart k (orbitQuotientCone b I s)).asOver (Spec (CommRingCat.of k))] ≫
        (orbitQuotientChartMap k b I s hIs).asOver (Spec (CommRingCat.of k)) := by
  let G := ToricSchemes.splitTorusOver k (Lattice n)
  let Q := ToricSchemes.splitTorusOver k (Lattice (n-I.card))
  let U := monoidChartSchemeOver k (dualConeMonoid (orbitQuotientCone b I s))
  let V := monoidChartSchemeOver k (dualConeMonoid s)
  let ρ : G ⟶ Q := orbitTorusMapOver k b I
  let q : U ⟶ V := (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitQuotientAlgebraMap k b I s hIs)).op
  change G ◁ q ≫ γ[G,V] = ρ ▷ U ≫ γ[Q,U] ≫ q
  have h₁ : G ◁ q ≫ γ[G,V] = G ◁ q ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid s)) :=
    congrArg (fun h : G ⊗ V ⟶ V => G ◁ q ≫ h)
      (monoidChart_action_coaction k (dualConeMonoid s))
  have h₂ : G ◁ q ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid s)) =
      ρ ▷ U ≫ affineCoactionMorphism k
        (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))) ≫ q :=
    affineCoaction_intertwining k (orbitTorusCharacterMap k b I)
      (orbitQuotientAlgebraMap k b I s hIs)
      (monoidChartCoaction k (dualConeMonoid s))
      (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s)))
      (orbitQuotientAlgebraMap_coaction k b I s hIs)
  have h₃ : ρ ▷ U ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))) ≫ q =
      ρ ▷ U ≫ γ[Q,U] ≫ q :=
    congrArg (fun h : Q ⊗ U ⟶ U => ρ ▷ U ≫ h ≫ q)
      (monoidChart_action_coaction k
        (dualConeMonoid (orbitQuotientCone b I s))).symm
  exact h₁.trans (h₂.trans h₃)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (hF : I.image b∈«Σ».cones)

instance orbitClosureMap_isOver :
    («Σ».orbitClosureMap k b I hF).IsOver (Spec (CommRingCat.of k)) where
  comp_over := by
    apply ((«Σ».completeQuotientStarFan b I hF).fanSchemeOpenCover k).hom_ext
    intro t
    obtain ⟨s,rfl⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
    let U := coneChart k (orbitQuotientCone b I s.val)
    let V := coneChart k s.val
    let Z := («Σ».completeQuotientStarFan b I hF).fanScheme k
    let j : U ⟶ Z := («Σ».completeQuotientStarFan b I hF).fanChartMap k
      («Σ».orbitConeQuotientIndex b I hF s)
    let i : V ⟶ «Σ».fanScheme k := «Σ».fanChartMap k ⟨s.val,s.property.1⟩
    let q : U ⟶ V := orbitQuotientChartMap k b I s.val s.property.2
    let f : Z ⟶ «Σ».fanScheme k := «Σ».orbitClosureMap k b I hF
    have hj : j ≫ f = q ≫ i := «Σ».orbitClosureMap_chart k b I hF s
    have hjbase : j ≫ (Z ↘ Spec (CommRingCat.of k)) =
        (U ↘ Spec (CommRingCat.of k)) :=
      comp_over ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s)) (Spec (CommRingCat.of k))
    have hibase : i ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) =
        (V ↘ Spec (CommRingCat.of k)) :=
      comp_over («Σ».fanChartMap k ⟨s.val,s.property.1⟩) (Spec (CommRingCat.of k))
    have hqbase : q ≫ (V ↘ Spec (CommRingCat.of k)) =
        (U ↘ Spec (CommRingCat.of k)) :=
      comp_over (orbitQuotientChartMap k b I s.val s.property.2) (Spec (CommRingCat.of k))
    change j ≫ (f ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) =
      j ≫ (Z ↘ Spec (CommRingCat.of k))
    calc
      _ = (j ≫ f) ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) :=
        (Category.assoc _ _ _).symm
      _ = (q ≫ i) ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) :=
        congrArg (fun h : U ⟶ «Σ».fanScheme k =>
          h ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) hj
      _ = q ≫ (i ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) :=
        Category.assoc _ _ _
      _ = q ≫ (V ↘ Spec (CommRingCat.of k)) :=
        congrArg (fun h : V ⟶ Spec (CommRingCat.of k) => q ≫ h) hibase
      _ = (U ↘ Spec (CommRingCat.of k)) := hqbase
      _ = _ := hjbase.symm

@[reassoc] theorem orbitClosureMap_chart_over (s : «Σ».OrbitConeIndex b I) :
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s)).asOver (Spec (CommRingCat.of k)) ≫
      («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) =
    (orbitQuotientChartMap k b I s.val s.property.2).asOver (Spec (CommRingCat.of k)) ≫
      («Σ».fanChartMap k ⟨s.val,s.property.1⟩).asOver (Spec (CommRingCat.of k)) := by
  apply Over.OverMorphism.ext
  exact «Σ».orbitClosureMap_chart k b I hF s

/-- The actual orbit closed immersion is equivariant. This statement
holds as an equality over Spec(k), not only on rational points. -/
theorem orbitClosureMap_action :
    ToricSchemes.splitTorusOver k (Lattice n) ◁
        («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),«Σ».fanSchemeOver k] =
    orbitTorusMapOver k b I ▷
        («Σ».completeQuotientStarFan b I hF).fanSchemeOver k ≫
      γ[ToricSchemes.splitTorusOver k (Lattice (n-I.card)),
        («Σ».completeQuotientStarFan b I hF).fanSchemeOver k] ≫
        («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  let G := ToricSchemes.splitTorusOver k (Lattice n)
  let Q := ToricSchemes.splitTorusOver k (Lattice (n-I.card))
  let X := Γ.fanSchemeOver k
  let Y := «Σ».fanSchemeOver k
  let ρ : G ⟶ Q := orbitTorusMapOver k b I
  let f : X ⟶ Y := («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k))
  apply tensorCover_hom_ext (Γ.fanSchemeOpenCover k) G Y
  intro t
  obtain ⟨s,rfl⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
  let U := monoidChartSchemeOver k
    (dualConeMonoid (orbitQuotientCone b I s.val))
  let V := monoidChartSchemeOver k (dualConeMonoid s.val)
  let j : U ⟶ X := (Γ.fanChartMap k
    («Σ».orbitConeQuotientIndex b I hF s)).asOver (Spec (CommRingCat.of k))
  let i : V ⟶ Y := («Σ».fanChartMap k ⟨s.val,s.property.1⟩).asOver
    (Spec (CommRingCat.of k))
  let q : U ⟶ V := (orbitQuotientChartMap k b I s.val s.property.2).asOver
    (Spec (CommRingCat.of k))
  letI : IsModHom G i := «Σ».fanChartMap_isModHom k ⟨s.val,s.property.1⟩
  letI : IsModHom Q j := Γ.fanChartMap_isModHom k
    («Σ».orbitConeQuotientIndex b I hF s)
  have hj : j ≫ f = q ≫ i := «Σ».orbitClosureMap_chart_over k b I hF s
  have hi_action : γ[G,V] ≫ i = G ◁ i ≫ γ[G,Y] :=
    IsModHom.smul_hom (A := G) (f := i)
  have hj_action : γ[Q,U] ≫ j = Q ◁ j ≫ γ[Q,X] :=
    IsModHom.smul_hom (A := Q) (f := j)
  have hq_action : G ◁ q ≫ γ[G,V] = ρ ▷ U ≫ γ[Q,U] ≫ q :=
    orbitQuotientChartMap_action k b I s.val s.property.2
  change G ◁ j ≫ (G ◁ f ≫ γ[G,Y]) =
    G ◁ j ≫ (ρ ▷ X ≫ γ[Q,X] ≫ f)
  calc
    _ = (G ◁ j ≫ G ◁ f) ≫ γ[G,Y] := (Category.assoc _ _ _).symm
    _ = G ◁ (j ≫ f) ≫ γ[G,Y] :=
      congrArg (fun h : G ⊗ U ⟶ G ⊗ Y => h ≫ γ[G,Y])
        (whiskerLeft_comp G j f).symm
    _ = G ◁ (q ≫ i) ≫ γ[G,Y] :=
      congrArg (fun h : U ⟶ Y => G ◁ h ≫ γ[G,Y]) hj
    _ = (G ◁ q ≫ G ◁ i) ≫ γ[G,Y] :=
      congrArg (fun h : G ⊗ U ⟶ G ⊗ Y => h ≫ γ[G,Y])
        (whiskerLeft_comp G q i)
    _ = G ◁ q ≫ (G ◁ i ≫ γ[G,Y]) := Category.assoc _ _ _
    _ = G ◁ q ≫ (γ[G,V] ≫ i) :=
      congrArg (fun h : G ⊗ V ⟶ Y => G ◁ q ≫ h) hi_action.symm
    _ = (G ◁ q ≫ γ[G,V]) ≫ i := (Category.assoc _ _ _).symm
    _ = (ρ ▷ U ≫ γ[Q,U] ≫ q) ≫ i :=
      congrArg (fun h : G ⊗ U ⟶ V => h ≫ i) hq_action
    _ = ρ ▷ U ≫ γ[Q,U] ≫ (q ≫ i) := by simp only [Category.assoc]
    _ = ρ ▷ U ≫ γ[Q,U] ≫ (j ≫ f) :=
      congrArg (fun h : U ⟶ Y => ρ ▷ U ≫ γ[Q,U] ≫ h) hj.symm
    _ = ρ ▷ U ≫ (γ[Q,U] ≫ j) ≫ f := by simp only [Category.assoc]
    _ = ρ ▷ U ≫ (Q ◁ j ≫ γ[Q,X]) ≫ f :=
      congrArg (fun h : Q ⊗ U ⟶ X => ρ ▷ U ≫ h ≫ f) hj_action
    _ = (ρ ▷ U ≫ Q ◁ j) ≫ γ[Q,X] ≫ f := by simp only [Category.assoc]
    _ = (G ◁ j ≫ ρ ▷ X) ≫ γ[Q,X] ≫ f :=
      congrArg (fun h : G ⊗ U ⟶ Q ⊗ X => h ≫ γ[Q,X] ≫ f)
        (whisker_exchange ρ j).symm
    _ = _ := by simp only [Category.assoc]

/-- The original torus acts on the quotient-star scheme through its
actual quotient homomorphism. Kept explicit to avoid competing instances
for the quotient torus's own action. -/
def orbitClosureSourceAction :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».completeQuotientStarFan b I hF).fanSchemeOver k) :=
  Mod.scalarRestriction (orbitTorusMapOver k b I)
    ((«Σ».completeQuotientStarFan b I hF).fanSchemeOver k)

/-- The already-proved closed immersion identifies an invariant closed
subscheme, with invariance witnessed by an actual group-scheme action. -/
theorem orbitClosureMap_equivariant :
    letI := «Σ».orbitClosureSourceAction k b I hF
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k))) := by
  letI := «Σ».orbitClosureSourceAction k b I hF
  constructor
  exact («Σ».orbitClosureMap_action k b I hF).symm

end SmoothCompleteFan
end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_action
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_equivariant
end
end Source_ToricOrbitActions
-- END ORIGINAL PaperVerification.ToricOrbitActions


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveLineDimension
section Source_ToricProjectiveLineDimension

-- original header: module

-- original header: public import PaperVerification.ToricRankOneFans
-- original header: public import Mathlib.RingTheory.KrullDimension.Polynomial
-- original header: public import Mathlib.RingTheory.KrullDimension.Field

-- original header: @[expose] public section

/-! # The actual Krull dimension of the two-chart projective line -/

noncomputable section

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes

variable (k : Type*) [Field k]

theorem projectiveLine_orderKrullDim : Order.krullDim (projectiveLineScheme k) = 1 := by
  apply le_antisymm
  · rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    obtain ⟨negative,p,rfl⟩ := projectiveLinePolynomialChart_jointly_surjective k x
    let R := CommRingCat.of (Polynomial k)
    let q : Spec R := p
    have hc : Order.coheight ((projectiveLinePolynomialChart k negative) q) =
        p.asIdeal.height :=
      (coheight_eq_of_isOpenImmersion (x := q)
        (projectiveLinePolynomialChart k negative)).trans
          (idealHeight_eq_coheight R q).symm
    have h := Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
    have hp : (p.asIdeal.height : WithBot ENat) ≤ 1 := by
      simpa only [Polynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field,zero_add] using h
    exact (congrArg (fun d : ENat => (d : WithBot ENat)) hc).trans_le hp
  · let p := polynomialOrigin k
    letI : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
      principalPrimeLocalization_isDiscreteValuationRing
        (Polynomial k) (Localization.AtPrime p.asIdeal) p.asIdeal
        Polynomial.X Polynomial.X_ne_zero (polynomialOrigin_ideal k)
    have hc := affineOpen_coheight_eq_one (.of (Polynomial k))
      (projectiveLinePolynomialChart k false) p
    have h := Order.coheight_le_krullDim
      (projectiveLinePolynomialChart k false p)
    simpa only [hc,WithBot.coe_one] using h

/-- The dimension is the usual dimension by chains of irreducible closed
subsets of the actual underlying topological space. -/
theorem projectiveLine_topologicalKrullDim :
    topologicalKrullDim (projectiveLineScheme k) = 1 := by
  change Order.krullDim (IrreducibleCloseds (projectiveLineScheme k)) = 1
  rw [Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := projectiveLineScheme k))]
  exact projectiveLine_orderKrullDim k

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_topologicalKrullDim
end
end Source_ToricProjectiveLineDimension
-- END ORIGINAL PaperVerification.ToricProjectiveLineDimension


-- BEGIN ORIGINAL PaperVerification.ToricWallCurves
section Source_ToricWallCurves

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveLineDimension
-- original header: public import PaperVerification.ToricOrbitActions
-- original header: public import PaperVerification.ToricOrbitCartierCoefficients

-- original header: @[expose] public section

/-!
# Actual invariant curves associated to fan walls

Deleting one primitive generator from a full smooth cone gives an
actual quotient-star scheme. Its map into the fan scheme is the
previously constructed closed immersion. The quotient has rank one,
so its scheme is isomorphic to the actual two-chart projective line
and has ordinary topological Krull dimension one.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open MonoidalCategory MonObj
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (s : «Σ».fullCones) (j : Fin n)

def wallIndices (_s : «Σ».fullCones) (j : Fin n) : Finset (Fin n) := Finset.univ.erase j

theorem wallIndices_codimension : n-(«Σ».wallIndices s j).card=1 := by
  simp only [wallIndices,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_fin]
  have hn := j.isLt
  omega

theorem wallCone_mem :
    («Σ».wallIndices s j).image («Σ».fullConeBasis s)∈«Σ».cones := by
  apply «Σ».downward s.val («Σ».fullCones_mem s)
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.erase_subset _ _)

def wallCurveFan : SmoothCompleteFan (n-(«Σ».wallIndices s j).card) :=
  «Σ».completeQuotientStarFan («Σ».fullConeBasis s) («Σ».wallIndices s j) («Σ».wallCone_mem s j)

variable (k : Type u) [Field k]

def wallCurve : Scheme.{u} := («Σ».wallCurveFan s j).fanScheme k

def wallCurveInclusion : «Σ».wallCurve s j k ⟶ «Σ».fanScheme k :=
  «Σ».orbitClosureMap k («Σ».fullConeBasis s) («Σ».wallIndices s j) («Σ».wallCone_mem s j)

instance wallCurveInclusion_isClosedImmersion :
    IsClosedImmersion («Σ».wallCurveInclusion s j k) := by
  exact «Σ».orbitClosureMap_isClosedImmersion k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)

instance wallCurve_isIntegral : IsIntegral («Σ».wallCurve s j k) :=
  inferInstanceAs (IsIntegral ((«Σ».wallCurveFan s j).fanScheme k))

instance wallCurve_isNoetherian : IsNoetherian («Σ».wallCurve s j k) :=
  inferInstanceAs (IsNoetherian ((«Σ».wallCurveFan s j).fanScheme k))

instance wallCurve_isOver : («Σ».wallCurve s j k).Over (Spec (.of k)) :=
  inferInstanceAs (((«Σ».wallCurveFan s j).fanScheme k).Over (Spec (.of k)))

instance wallCurveInclusion_isOver :
    («Σ».wallCurveInclusion s j k).IsOver (Spec (.of k)) :=
  inferInstanceAs ((«Σ».orbitClosureMap k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)).IsOver (Spec (.of k)))

def wallCurveProjectiveLineIso : «Σ».wallCurve s j k ≅ projectiveLineScheme k :=
  oneDimensionalFanSchemeIso («Σ».wallCurveFan s j) («Σ».wallIndices_codimension s j) k

theorem wallCurve_dimension : topologicalKrullDim («Σ».wallCurve s j k)=1 := by
  have h := IsHomeomorph.topologicalKrullDim_eq
    (fun x => («Σ».wallCurveProjectiveLineIso s j k).hom x)
    («Σ».wallCurveProjectiveLineIso s j k).hom.homeomorph.isHomeomorph
  exact h.trans (projectiveLine_topologicalKrullDim k)

/-- The actual group-scheme equivariance identity is inherited from the
closed orbit immersion; it is stronger than invariance of rational points. -/
theorem wallCurve_equivariant :
    letI : ModObj (PaperVerification.ToricSchemes.splitTorusOver k (Lattice n))
        ((«Σ».wallCurve s j k).asOver (Spec (.of k))) :=
      «Σ».orbitClosureSourceAction k («Σ».fullConeBasis s)
        («Σ».wallIndices s j) («Σ».wallCone_mem s j)
    IsModHom (PaperVerification.ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».wallCurveInclusion s j k).asOver (Spec (.of k))) :=
  «Σ».orbitClosureMap_equivariant k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_dimension
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_equivariant
end
end Source_ToricWallCurves
-- END ORIGINAL PaperVerification.ToricWallCurves


-- BEGIN ORIGINAL PaperVerification.ToricCompleteWalls
section Source_ToricCompleteWalls

-- original header: module

-- original header: public import PaperVerification.ToricQuotientStarCovering
-- original header: public import PaperVerification.ToricFanPolytopeConstruction
-- original header: public import PaperVerification.ToricWallUniqueness
-- original header: public import Mathlib.Algebra.Group.Int.Units

-- original header: @[expose] public section

/-!
# Genuine opposite full cones in a complete smooth fan

Completeness is used through a small negative transverse perturbation of
the sum of the wall rays. Purity extends the resulting cone. The integral
basis condition then forces the opposite ray's transverse coordinate to
be exactly minus one.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem basis_wall_card (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) :
    ((Finset.univ.erase j).image b).card=n-1 := by
  rw [Finset.card_image_of_injective _ b.injective,Finset.card_erase_of_mem (Finset.mem_univ j)]
  simp

theorem basis_wall_coord_zero (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (v : Lattice n) (hv : v∈(Finset.univ.erase j).image b) : b.repr v j=0 := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  simp only [Module.Basis.repr_self_apply,if_neg (Finset.mem_erase.mp hi).1]

/-- Smoothness makes the opposite transverse coefficient a unit in Z;
its sign therefore determines it exactly. -/
theorem opposite_wall_coord_eq_neg_one
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) (w : Lattice n)
    (hwcone : insert w ((Finset.univ.erase j).image b)∈«Σ».cones)
    (hwneg : b.repr w j<0) : b.repr w j = -1 := by
  let F := (Finset.univ.erase j).image b
  have hwF : w∉F := by
    intro hw
    rw [basis_wall_coord_zero b j w hw] at hwneg
    exact (lt_irrefl 0 hwneg)
  have hn : 0<n := by have h := j.isLt; omega
  have hcard : (insert w F).card=n := by
    rw [Finset.card_insert_of_notMem hwF,basis_wall_card b j]
    omega
  obtain ⟨c,hc⟩ := «Σ».full_cone_basis hwcone hcard
  obtain ⟨l,hl,hcl⟩ := Finset.mem_image.mp (hc ▸ Finset.mem_insert_self w F)
  have hzero (i : Fin n) (hil : i≠l) : b.repr (c i) j=0 := by
    have hci : c i∈insert w F := hc.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    rcases Finset.mem_insert.mp hci with hiw | hiF
    · exact (hil (c.injective (hiw.trans hcl.symm))).elim
    · exact basis_wall_coord_zero b j (c i) hiF
  have hprod : b.repr w j * c.repr (b j) l = 1 := by
    calc
      b.repr w j * c.repr (b j) l = ∑ i, c.repr (b j) i * b.repr (c i) j := by
        rw [Finset.sum_eq_single l]
        · rw [hcl,mul_comm]
        · intro i hi hil
          rw [hzero i hil,mul_zero]
        · intro hl
          exact (hl (Finset.mem_univ l)).elim
      _ = b.repr (∑ i,c.repr (b j) i • c i) j := by
        simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
      _ = 1 := by rw [c.sum_repr]; simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h | h
  · omega
  · exact h

/-- A negative coordinate of a cone vector must occur in one of the
actual generating rays. -/
theorem exists_ray_negative_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n)
    (s : Finset (Lattice n)) (x : Ambient n) (hx : x∈latticeRayCone s)
    (hxneg : (integralBasisReal b).repr x j<0) :
    ∃ w∈s,b.repr w j<0 := by
  by_contra hn
  push_neg at hn
  obtain ⟨c,hc,hcx⟩ := hx
  have hsum : 0≤∑ v∈s.image (embed n),c v * (integralBasisReal b).repr v j := by
    apply Finset.sum_nonneg
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact mul_nonneg (hc _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩))
      (by rw [integralBasisReal_repr]; exact_mod_cast hn w hw)
  have he := congrArg (fun y=>(integralBasisReal b).repr y j) hcx
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul] at he
  rw [he] at hsum
  exact (not_lt_of_ge hsum) hxneg

/-- An actual opposite full cone exists across every facet of every full
cone; all ray sets and the transverse integral coordinate are explicit. -/
theorem exists_full_opposite_wall (hpure : «Σ».IsPure) (s : «Σ».fullCones) (j : Fin n) :
    ∃ t : «Σ».fullCones, ∃ w : Lattice n,
      t.val=insert w ((Finset.univ.erase j).image («Σ».fullConeBasis s)) ∧
      («Σ».fullConeBasis s).repr w j = -1 ∧
      s.val∩t.val=(Finset.univ.erase j).image («Σ».fullConeBasis s) ∧
      w∈t.val ∧ w∉s.val := by
  let b := «Σ».fullConeBasis s
  let F := (Finset.univ.erase j).image b
  have hFs : F⊆s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.image_subset_image (Finset.erase_subset j _)
  have hF : F∈«Σ».cones := «Σ».downward s.val («Σ».fullCones_mem s) F hFs
  obtain ⟨ε,hε,q,hq,hFq,hx⟩ := «Σ».exists_small_perturbation_in_containing_cone hF
    (-embed n (b j))
  obtain ⟨t,ht,hqt,htcard⟩ := hpure q hq
  let t' : «Σ».fullCones := ⟨t,Finset.mem_filter.mpr ⟨ht,htcard⟩⟩
  have hFt : F⊆t := hFq.trans hqt
  have hx' : (∑ u∈F,embed n u)+ε • (-embed n (b j))∈latticeRayCone t :=
    latticeRayCone_mono hqt hx
  have hneg : (integralBasisReal b).repr
      ((∑ u∈F,embed n u)+ε • (-embed n (b j))) j<0 := by
    have hz : (integralBasisReal b).repr (∑ u∈F,embed n u) j=0 := by
      rw [map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro u hu
      rw [integralBasisReal_repr,basis_wall_coord_zero b j u hu,Int.cast_zero]
    simp only [map_add,map_smul,map_neg,Finsupp.add_apply,Finsupp.smul_apply,
      Finsupp.neg_apply,integralBasisReal_repr,Module.Basis.repr_self_apply,
      if_true,Int.cast_one,smul_eq_mul,hz,zero_add,mul_neg,mul_one]
    exact neg_neg_of_pos hε
  obtain ⟨w,hwt,hwneg⟩ := exists_ray_negative_coordinate b j t _ hx' hneg
  have hwF : w∉F := by
    intro hw
    rw [basis_wall_coord_zero b j w hw] at hwneg
    exact (lt_irrefl 0 hwneg)
  have hins : insert w F⊆t := Finset.insert_subset hwt hFt
  have hcard : (insert w F).card=n := by
    rw [Finset.card_insert_of_notMem hwF,basis_wall_card b j]
    have hn := j.isLt
    omega
  have htF : t=insert w F :=
    (Finset.eq_of_subset_of_card_le hins (by rw [hcard,htcard])).symm
  have hwcone : insert w F∈«Σ».cones := htF ▸ ht
  have hwj : b.repr w j = -1 := «Σ».opposite_wall_coord_eq_neg_one b j w hwcone hwneg
  have hws : w∉s.val := by
    intro hws
    obtain ⟨i,hi,hwi⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hws)
    rw [← hwi,Module.Basis.repr_self_apply] at hwneg
    split_ifs at hwneg <;> omega
  have hmeet : s.val∩t=F := by
    rw [htF]
    ext v
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hvs,rfl|hvF⟩
      · exact (hws hvs).elim
      · exact hvF
    · intro hvF
      exact ⟨hFs hvF,Or.inr hvF⟩
  exact ⟨t',w,htF,hwj,hmeet,hwt,hws⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.opposite_wall_coord_eq_neg_one
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_full_opposite_wall
end
end Source_ToricCompleteWalls
-- END ORIGINAL PaperVerification.ToricCompleteWalls


-- BEGIN ORIGINAL PaperVerification.ToricWallStrictSupport
section Source_ToricWallStrictSupport

-- original header: module

-- original header: public import PaperVerification.ToricCompleteWalls
-- original header: public import PaperVerification.ToricEdgeWallSupport

-- original header: @[expose] public section

/-!
# Positive genuine wall slacks imply strict support

For a fixed fan ray, minimize its pairing with the finitely many actual
Cartier points. A negative coordinate in the minimizing cone would allow
crossing the corresponding wall and strictly lowering that pairing. Thus
the minimum is attained on a cone containing the ray. This proves all
global support inequalities and their strictness without a local-to-global
convexity theorem or a cone-of-curves assertion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def wallSlack (a : Lattice n→ℝ) (s : «Σ».fullCones) (u : Lattice n) : ℝ :=
  a u + (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s)

/-- Slacks are tested only at the actual new ray of two adjacent full
cones in the given fan. -/
def HasPositiveWallSlacks (a : Lattice n→ℝ) : Prop :=
  ∀ s t : «Σ».fullCones,(s.val∩t.val).card=n-1 →
    ∀ u∈t.val,u∉s.val → 0<«Σ».wallSlack a s u

theorem eq_cartierPoint_of_active_pairings (a : Lattice n→ℝ) (s : «Σ».fullCones)
    (x : Ambient n)
    (hx : ∀ u∈s.val,(dotProductEquiv ℝ (Fin n) (embed n u)) x = -a u) :
    x=«Σ».cartierPoint a s := by
  apply («Σ».cartierBasis s).repr.injective
  ext i
  have hi : («Σ».activeRay s i : Lattice n)∈s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  calc
    («Σ».cartierBasis s).repr x i =
        (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i))) x :=
      («Σ».activeRay_dual s i x).symm
    _ = -a («Σ».activeRay s i) := hx _ hi
    _ = (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i)))
        («Σ».cartierPoint a s) := («Σ».cartierPoint_active a s i).symm
    _ = («Σ».cartierBasis s).repr («Σ».cartierPoint a s) i := «Σ».activeRay_dual s i _

/-- The actual displacement of Cartier points across a smooth wall is
the primitive dual direction multiplied by the literal wall slack. -/
theorem cartierPoint_across_wall (a : Lattice n→ℝ) (s t : «Σ».fullCones)
    (j : Fin n) (w : Lattice n)
    (ht : t.val=insert w ((Finset.univ.erase j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    «Σ».cartierPoint a t = «Σ».cartierPoint a s + «Σ».wallSlack a s w • «Σ».cartierBasis s j := by
  symm
  apply «Σ».eq_cartierPoint_of_active_pairings a t
  intro u hu
  rw [ht] at hu
  rcases Finset.mem_insert.mp hu with hu | hu
  · subst u
    rw [map_add,map_smul]
    change _ + «Σ».wallSlack a s w *
      (dotProductEquiv ℝ (Fin n) (embed n w))
        (integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) j) = _
    rw [pairing_integral_dual_basis,hwj]
    simp only [Int.cast_neg,Int.cast_one,wallSlack]
    ring
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    have his : «Σ».fullConeBasis s i∈s.val := by
      rw [«Σ».fullConeBasis_ray_set]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    rw [map_add,map_smul,«Σ».cartierPoint_support_eq_of_mem a s his]
    change -a _ + «Σ».wallSlack a s w *
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s i)))
        (integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) j) = _
    rw [pairing_integral_dual_basis,Module.Basis.repr_self_apply,
      if_neg (Finset.mem_erase.mp hi).1]
    simp

theorem exists_negative_coordinate_of_ray_not_mem_full (s : «Σ».fullCones)
    (u : Lattice n) (hu : u∈«Σ».rays) (hus : u∉s.val) :
    ∃ j : Fin n,(«Σ».fullConeBasis s).repr u j<0 := by
  by_contra hn
  push_neg at hn
  have hcone : embed n u∈latticeRayCone s.val := by
    rw [«Σ».fullConeBasis_ray_set s]
    apply (mem_latticeRayCone_basis_iff («Σ».fullConeBasis s) Finset.univ (embed n u)).mpr
    refine ⟨?_,?_⟩
    · intro j
      rw [integralBasisReal_repr]
      exact_mod_cast hn j
    · intro j hj
      exact (hj (Finset.mem_univ j)).elim
  exact hus ((«Σ».ray_mem_cone_iff («Σ».fullCones_mem s) hu).mp hcone)

/-- Any cone not containing the chosen fan ray has a genuine adjacent
cone with strictly smaller Cartier pairing against that ray. -/
theorem exists_smaller_cartier_pairing (hpure : «Σ».IsPure) (a : Lattice n→ℝ)
    (ha : «Σ».HasPositiveWallSlacks a) (s : «Σ».fullCones)
    (u : Lattice n) (hu : u∈«Σ».rays) (hus : u∉s.val) :
    ∃ t : «Σ».fullCones,
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a t) <
        (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨j,huj⟩ := «Σ».exists_negative_coordinate_of_ray_not_mem_full s u hu hus
  obtain ⟨t,w,ht,hwj,hmeet,hwt,hws⟩ := «Σ».exists_full_opposite_wall hpure s j
  have hcard : (s.val∩t.val).card=n-1 := by
    rw [hmeet,basis_wall_card]
  have hslack := ha s t hcard w hwt hws
  refine ⟨t,?_⟩
  rw [«Σ».cartierPoint_across_wall a s t j w ht hwj,map_add,map_smul]
  change _+«Σ».wallSlack a s w *
      (dotProductEquiv ℝ (Fin n) (embed n u))
        (integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) j) < _
  rw [pairing_integral_dual_basis]
  exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hslack (by exact_mod_cast huj))

theorem cartier_pairing_ge_of_positive_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ) (ha : «Σ».HasPositiveWallSlacks a)
    (u : Lattice n) (hu : u∈«Σ».rays) (s : «Σ».fullCones) :
    -a u≤(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨s₀,hs₀⟩ := «Σ».fullCones_nonempty hpure
  letI : Nonempty «Σ».fullCones := ⟨⟨s₀,hs₀⟩⟩
  obtain ⟨t,ht,hmin⟩ := (Finset.univ : Finset «Σ».fullCones).exists_min_image
    (fun t=>(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a t))
    Finset.univ_nonempty
  have hut : u∈t.val := by
    by_contra hut
    obtain ⟨q,hq⟩ := «Σ».exists_smaller_cartier_pairing hpure a ha t u hu hut
    exact (not_lt_of_ge (hmin q (Finset.mem_univ q))) hq
  have hvalue := «Σ».cartierPoint_support_eq_of_mem a t hut
  rw [← hvalue]
  exact hmin s (Finset.mem_univ s)

theorem cartier_pairing_gt_of_positive_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ) (ha : «Σ».HasPositiveWallSlacks a)
    (u : Lattice n) (hu : u∈«Σ».rays) (s : «Σ».fullCones) (hus : u∉s.val) :
    -a u<(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨t,ht⟩ := «Σ».exists_smaller_cartier_pairing hpure a ha s u hu hus
  exact («Σ».cartier_pairing_ge_of_positive_wallSlacks hpure a ha u hu t).trans_lt ht

/-- Full-cone strict inequalities imply strict support on every face.
A small linear perturbation makes the other rays of a containing full
cone strict, while preserving all already strict inactive inequalities. -/
theorem strictSupport_of_full_cartier_inequalities (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ)
    (ha : ∀ (s : «Σ».fullCones) (u : Lattice n),u∈«Σ».rays → u∉s.val →
      -a u<(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s)) :
    «Σ».IsStrictSupport a := by
  intro F hF
  obtain ⟨s,hs,hFs,hcard⟩ := hpure F hF
  let s' : «Σ».fullCones := ⟨s,Finset.mem_filter.mpr ⟨hs,hcard⟩⟩
  let b := «Σ».fullConeBasis s'
  let B := integralBasisReal b
  have hs_basis : s = Finset.univ.image b := «Σ».fullConeBasis_ray_set s'
  let ℓ : Ambient n→ₗ[ℝ]ℝ := -(dotProductEquiv ℝ (Fin n) («Σ».cartierPoint a s'))
  have hℓ (u : Lattice n) : ℓ (embed n u) =
      -(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s') := by
    change -(«Σ».cartierPoint a s' ⬝ᵥ embed n u) =
      -(embed n u ⬝ᵥ «Σ».cartierPoint a s')
    exact congrArg (fun r : ℝ => -r)
      (dotProduct_comm («Σ».cartierPoint a s') (embed n u))
  let I := Finset.univ.filter (fun i : Fin n=>b i∉F)
  let h : Ambient n→ₗ[ℝ]ℝ := ∑ i∈I,B.coord i
  have hh (j : Fin n) : h (embed n (b j)) = if b j∈F then 0 else 1 := by
    simp only [h,B,LinearMap.sum_apply,Module.Basis.coord_apply,integralBasisReal_repr,
      Module.Basis.repr_self_apply]
    by_cases hj : b j∈F <;> simp [I,hj]
  let J := «Σ».rays\s
  let f : Lattice n→ℝ := fun u=>a u-ℓ (embed n u)
  let g : Lattice n→ℝ := fun u=>h (embed n u)
  have hf (u : Lattice n) (hu : u∈J) : 0<f u := by
    obtain ⟨hur,hus⟩ := Finset.mem_sdiff.mp hu
    have ht := ha s' u hur hus
    dsimp [f]
    rw [hℓ]
    linarith
  obtain ⟨ε,hε,hsmall⟩ := finite_strict_perturbation J f g hf
  refine ⟨ℓ-ε • h,?_,?_⟩
  · intro u hu
    have hus := hFs hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hs_basis ▸ hus)
    rw [LinearMap.sub_apply,LinearMap.smul_apply,hℓ,hh,if_pos hu,
      «Σ».cartierPoint_support_eq_of_mem a s' (hFs hu)]
    simp
  · intro u hur huF
    by_cases hus : u∈s
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hs_basis ▸ hus)
      rw [LinearMap.sub_apply,LinearMap.smul_apply,hℓ,hh,if_neg huF,
        «Σ».cartierPoint_support_eq_of_mem a s' hus]
      simp only [neg_neg,smul_eq_mul,mul_one]
      linarith
    · have hz := hsmall u (Finset.mem_sdiff.mpr ⟨hur,hus⟩)
      dsimp [f,g] at hz
      change ℓ (embed n u)-ε*h (embed n u)<a u
      linarith

/-- Positive actual wall slacks suffice for the entire strict support
condition, including every lower-dimensional cone. -/
theorem strictSupport_of_positive_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℝ) (ha : «Σ».HasPositiveWallSlacks a) : «Σ».IsStrictSupport a :=
  «Σ».strictSupport_of_full_cartier_inequalities hpure a
    (fun s u hu hus=>«Σ».cartier_pairing_gt_of_positive_wallSlacks hpure a ha u hu s hus)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierPoint_across_wall
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.strictSupport_of_positive_wallSlacks
end
end Source_ToricWallStrictSupport
-- END ORIGINAL PaperVerification.ToricWallStrictSupport


-- BEGIN ORIGINAL PaperVerification.ToricWallPolytopeBounds
section Source_ToricWallPolytopeBounds

-- original header: module

-- original header: public import PaperVerification.ToricWallStrictSupport
-- original header: public import PaperVerification.ToricSupportAveragedEdges
-- original header: public import PaperVerification.ToricCartierCharacterModules

-- original header: @[expose] public section

/-!
# Actual polytopes and edge bounds from genuine wall degrees

The adjacent Cartier points differ by the primitive dual direction times
the wall slack. Their actual convex segment therefore contains every
initial segment up to a common slack bound. The proved classification of
all incident edges transfers this to all genuine polytope edges.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def integerWallSlack (a : Lattice n→ℤ) (s : «Σ».fullCones) (u : Lattice n) : ℤ :=
  a u+integerPairing u («Σ».cartierLatticePoint a s)

theorem integerWallSlack_cast (a : Lattice n→ℤ) (s : «Σ».fullCones) (u : Lattice n) :
    («Σ».integerWallSlack a s u : ℝ)=«Σ».wallSlack (fun v=>(a v:ℝ)) s u := by
  rw [wallSlack,← «Σ».embed_cartierLatticePoint a s,normalRay_pairing_lattice]
  simp only [integerWallSlack,integerPairing,Int.cast_add]

def HasWallSlacksAtLeast (a : Lattice n→ℤ) (bound : ℕ) : Prop :=
  ∀ s t : «Σ».fullCones,(s.val∩t.val).card=n-1 →
    ∀ u∈t.val,u∉s.val → (bound:ℤ)≤«Σ».integerWallSlack a s u

theorem positiveWallSlacks_of_bound (a : Lattice n→ℤ) (bound : ℕ)
    (hbound : 0<bound) (ha : «Σ».HasWallSlacksAtLeast a bound) :
    «Σ».HasPositiveWallSlacks (fun u=>(a u:ℝ)) := by
  intro s t hst u hut hus
  rw [← «Σ».integerWallSlack_cast]
  have hpos : (0:ℤ)<«Σ».integerWallSlack a s u :=
    lt_of_lt_of_le (by exact_mod_cast hbound) (ha s t hst u hut hus)
  exact_mod_cast hpos

theorem support_edgesAtLeast_of_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℤ) (ha : «Σ».IsStrictSupport (fun u=>(a u:ℝ))) (bound : ℕ)
    (hbound : «Σ».HasWallSlacksAtLeast a bound) :
    («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound := by
  apply «Σ».support_edgesAtLeast_of_axis_points hpure a ha bound
  intro s j
  obtain ⟨t,w,ht,hwj,hmeet,hwt,hws⟩ := «Σ».exists_full_opposite_wall hpure s j
  have hcard : (s.val∩t.val).card=n-1 := by rw [hmeet,basis_wall_card]
  let aR : Lattice n→ℝ := fun u=>(a u:ℝ)
  let L := «Σ».wallSlack aR s w
  have hL : (bound:ℝ)≤L := by
    change (bound:ℝ) ≤ «Σ».wallSlack (fun v => (a v : ℝ)) s w
    rw [← «Σ».integerWallSlack_cast a s w]
    exact_mod_cast hbound s t hcard w hwt hws
  have hLp : 0<L := by
    have hw : w∈«Σ».rays := «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem t) hwt
    have h := «Σ».cartierPoint_support_lt_of_not_mem ha s hw hws
    dsimp [L,wallSlack]
    linarith
  have hsv : «Σ».cartierPoint aR s∈«Σ».fanPolytope aR :=
    «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) s
  have htv : «Σ».cartierPoint aR t∈«Σ».fanPolytope aR :=
    «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) t
  let «λ» : ℝ := bound/L
  have «hλ0» : 0≤«λ» := div_nonneg (Nat.cast_nonneg _) hLp.le
  have «hλ1» : «λ»≤1 := (div_le_one hLp).mpr hL
  have «hλL» : «λ»*L=bound := div_mul_cancel₀ _ hLp.ne'
  have hseg : «Σ».cartierPoint aR s+(bound:ℝ) • «Σ».cartierBasis s j ∈
      segment ℝ («Σ».cartierPoint aR s) («Σ».cartierPoint aR t) := by
    refine ⟨1-«λ»,«λ»,sub_nonneg.mpr «hλ1»,«hλ0»,by ring,?_⟩
    rw [«Σ».cartierPoint_across_wall aR s t j w ht hwj,
      smul_add,smul_smul,«hλL»,sub_smul,one_smul]
    abel
  exact («Σ».convex_fanPolytope aR).segment_subset hsv htv hseg

/-- Positive lower bounds on all actual wall degrees construct the
entire genuine smooth lattice polytope with the prescribed fan and with
the same lower bound on every actual edge. -/
theorem exists_smooth_latticePolytope_of_positive_wall_bounds
    (hpure : «Σ».IsPure) (a : Lattice n→ℤ) (bound : ℕ) (hbound : 0<bound)
    (ha : «Σ».HasWallSlacksAtLeast a bound) :
    ∃ P : LatticePolytope n,
      P.carrier=«Σ».fanPolytope (fun u=>(a u:ℝ)) ∧
      P.Smooth ∧ P.normalFan=«Σ».realCones ∧ P.EdgesAtLeast bound := by
  let hs := «Σ».strictSupport_of_positive_wallSlacks hpure (fun u=>(a u:ℝ))
    («Σ».positiveWallSlacks_of_bound a bound hbound ha)
  exact ⟨«Σ».supportLatticePolytope hpure a hs,
    «Σ».supportLatticePolytope_carrier hpure a hs,
    «Σ».supportLatticePolytope_smooth hpure a hs,
    «Σ».supportLatticePolytope_normalFan hpure a hs,
    «Σ».support_edgesAtLeast_of_wallSlacks hpure a hs bound ha⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.support_edgesAtLeast_of_wallSlacks
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_smooth_latticePolytope_of_positive_wall_bounds
end
end Source_ToricWallPolytopeBounds
-- END ORIGINAL PaperVerification.ToricWallPolytopeBounds


-- BEGIN ORIGINAL PaperVerification.ToricWallCurveDegrees
section Source_ToricWallCurveDegrees

-- original header: module

-- original header: public import PaperVerification.ToricWallCurves
-- original header: public import PaperVerification.ToricRankOneDegree
-- original header: public import PaperVerification.ToricOrbitCartierRestriction
-- original header: public import PaperVerification.ToricWallPolytopeBounds

-- original header: @[expose] public section

/-!
# Actual invariant-curve degree equals integral wall slack

The orbit cone is the wall obtained by deleting one basis ray. The
quotient lattice has one coordinate. The original ray projects to `1`
and the opposite ray to `-1`; normalization at the original full cone
makes the first restricted coefficient zero and the second exactly the
integral wall slack. The genuine pullback-sheaf isomorphism and the
proved degree formula on the actual curve give the equality.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (s : «Σ».fullCones) (j : Fin n)

theorem wall_complementaryEmbedding
    (q : Fin (n-(«Σ».wallIndices s j).card)) :
    complementaryEmbedding («Σ».wallIndices s j) q=j := by
  have hnot : complementaryEmbedding («Σ».wallIndices s j) q∉«Σ».wallIndices s j :=
    (mem_range_complementaryEmbedding_iff _ _).mp ⟨q,rfl⟩
  by_contra hne
  exact hnot (Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩)

theorem wall_quotient_coordinate (v : Lattice n)
    (q : Fin (n-(«Σ».wallIndices s j).card)) :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j) v q =
      («Σ».fullConeBasis s).repr v j := by
  change («Σ».fullConeBasis s).repr v (complementaryEmbedding («Σ».wallIndices s j) q)=_
  rw [«Σ».wall_complementaryEmbedding]

theorem wallCone_subset_full :
    («Σ».wallIndices s j).image («Σ».fullConeBasis s)⊆s.val := by
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.erase_subset _ _)

theorem fullConeBasis_mem_sdiff_wall :
    «Σ».fullConeBasis s j∈s.val\(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
  · intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hij := («Σ».fullConeBasis s).injective he
    exact (Finset.mem_erase.mp hi).1 hij

theorem wall_quotient_positive :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».fullConeBasis s j) = (fun _=>1) := by
  ext q
  rw [«Σ».wall_quotient_coordinate]
  simp

theorem wall_quotient_negative (w : Lattice n)
    (hw : («Σ».fullConeBasis s).repr w j = -1) :
    coneQuotientLattice («Σ».fullConeBasis s) («Σ».wallIndices s j) w = (fun _=>-1) := by
  ext q
  rw [«Σ».wall_quotient_coordinate,hw]

theorem wall_positive_ne_negative :
    (fun _=>1 : Lattice (n-(«Σ».wallIndices s j).card))≠(fun _=>-1) := by
  intro h
  let q : Fin (n-(«Σ».wallIndices s j).card) :=
    ⟨0,by rw [«Σ».wallIndices_codimension]; omega⟩
  have hq := congrFun h q
  norm_num at hq

def wallRestrictionCoefficients (a : Lattice n→ℤ) :
    Lattice (n-(«Σ».wallIndices s j).card)→ℤ :=
  «Σ».orbitRestrictionCoefficients («Σ».fullConeBasis s) («Σ».wallIndices s j)
    («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s)

theorem wallRestriction_positive (a : Lattice n→ℤ) :
    «Σ».wallRestrictionCoefficients s j a (fun _=>1)=0 := by
  rw [wallRestrictionCoefficients,← «Σ».wall_quotient_positive s j,
    «Σ».orbitRestrictionCoefficients_projected («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s) («Σ».fullCones_mem s)
      («Σ».wallCone_subset_full s j) («Σ».fullConeBasis_mem_sdiff_wall s j),
    «Σ».cartierLatticePoint_pairing a s («Σ».fullConeBasis s j)
      (Finset.mem_sdiff.mp («Σ».fullConeBasis_mem_sdiff_wall s j)).1]
  ring

theorem wallRestriction_negative (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    «Σ».wallRestrictionCoefficients s j a (fun _=>-1)=«Σ».integerWallSlack a s w := by
  have hwF : w∉(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    intro hw
    have hzero := basis_wall_coord_zero («Σ».fullConeBasis s) j w hw
    omega
  have hFt : («Σ».wallIndices s j).image («Σ».fullConeBasis s)⊆t.val := by
    rw [ht]
    exact Finset.subset_insert _ _
  have hwt : w∈t.val\(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    rw [ht]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _,hwF⟩
  rw [wallRestrictionCoefficients,← «Σ».wall_quotient_negative s j w hwj,
    «Σ».orbitRestrictionCoefficients_projected («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j) a («Σ».cartierLatticePoint a s)
      («Σ».fullCones_mem t) hFt hwt]
  rfl

theorem wallRestriction_sum (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    (∑ u∈(«Σ».wallCurveFan s j).rays,«Σ».wallRestrictionCoefficients s j a u) =
      «Σ».integerWallSlack a s w := by
  rw [(«Σ».wallCurveFan s j).oneDimensional_rays («Σ».wallIndices_codimension s j),
    Finset.sum_pair («Σ».wall_positive_ne_negative s j),
    «Σ».wallRestriction_positive s j a,«Σ».wallRestriction_negative s j a t w ht hwj,zero_add]

variable (k : Type u) [Field k] (hpure : «Σ».IsPure)

/-- The bound in the paper is applied to the genuine restricted line
bundle on the actual invariant curve. Its degree is the wall slack. -/
theorem wallCurve_fanCartier_hasDegree (a : Lattice n→ℤ)
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj
        («Σ».fanCartierData k hpure a).sheaf) («Σ».integerWallSlack a s w) := by
  have hm : ∀ u∈(«Σ».wallIndices s j).image («Σ».fullConeBasis s),
      integerPairing u («Σ».cartierLatticePoint a s) = -a u := by
    intro u hu
    exact «Σ».cartierLatticePoint_pairing a s u («Σ».wallCone_subset_full s j hu)
  let F := «Σ».orbitCartierPullbackIso k («Σ».fullConeBasis s) («Σ».wallIndices s j)
    («Σ».wallCone_mem s j) hpure a («Σ».cartierLatticePoint a s) hm
  apply ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
    («Σ».wallIndices_codimension s j) k F _).mpr
  have h := («Σ».wallCurveFan s j).oneDimensionalFanCartier_hasDegree
    («Σ».wallIndices_codimension s j) k
    («Σ».completeQuotientStarFan_isPure hpure («Σ».fullConeBasis s) («Σ».wallIndices s j)
      («Σ».wallCone_mem s j)) («Σ».wallRestrictionCoefficients s j a)
  rwa [«Σ».wallRestriction_sum s j a t w ht hwj] at h

/-- An arbitrary Cartier sheaf is handled through its proved actual
isomorphism to the recovered invariant presentation. -/
theorem wallCurve_cartier_hasDegree (D : CartierData («Σ».fanScheme k))
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hwj : («Σ».fullConeBasis s).repr w j = -1) :
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf)
      («Σ».integerWallSlack («Σ».cartierCoefficients k hpure D) s w) := by
  let F := («Σ».cartierData_linearlyEquivalent_fanCartier k hpure D).some
  apply ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
    («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).mapIso F) _).mpr
  exact «Σ».wallCurve_fanCartier_hasDegree s j k hpure _ t w ht hwj

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_fanCartier_hasDegree
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_cartier_hasDegree
end
end Source_ToricWallCurveDegrees
-- END ORIGINAL PaperVerification.ToricWallCurveDegrees


-- BEGIN ORIGINAL PaperVerification.ToricDegreePolytopeBridge
section Source_ToricDegreePolytopeBridge

-- original header: module

-- original header: public import PaperVerification.ToricWallCurveDegrees

-- original header: @[expose] public section

/-!
# From actual invariant-curve degrees to actual polytope edge lengths

Every adjacent full-cone pair determines a deleted basis ray. The
quotient fan proves that the other transverse ray is `-1`; its degree is
therefore exactly the wall slack already computed by actual sheaf
restriction. Positive degree bounds consequently give the full smooth
lattice polytope and the same bound on every actual edge.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem adjacentWall_basisIndex (s t : «Σ».fullCones)
    (hst : (s.val∩t.val).card=n-1) (u : Lattice n) (hut : u∈t.val) (hus : u∉s.val) :
    ∃ j : Fin n,
      s.val∩t.val=(«Σ».wallIndices s j).image («Σ».fullConeBasis s) ∧
      t.val=insert u ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)) := by
  have hn : 0<n := by
    have h := Finset.card_pos.mpr (show t.val.Nonempty from ⟨u,hut⟩)
    rwa [«Σ».fullCones_card] at h
  have hcard : (s.val\t.val).card=1 := by
    have h := Finset.card_sdiff_add_card_inter s.val t.val
    rw [hst,«Σ».fullCones_card] at h
    omega
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hcard
  have hvst : v∈s.val\t.val := by rw [hv]; exact Finset.mem_singleton_self _
  have hvs := (Finset.mem_sdiff.mp hvst).1
  have hvt := (Finset.mem_sdiff.mp hvst).2
  obtain ⟨j,hj,hbj⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hvs)
  have hmeet : s.val∩t.val=(«Σ».wallIndices s j).image («Σ».fullConeBasis s) := by
    ext w
    constructor
    · intro hw
      obtain ⟨i,hi,hbi⟩ := Finset.mem_image.mp
        ((«Σ».fullConeBasis_ray_set s) ▸ (Finset.mem_inter.mp hw).1)
      have hij : i≠j := by
        intro he
        have hwv : w=v := hbi.symm.trans (he ▸ hbj)
        exact hvt (hwv ▸ (Finset.mem_inter.mp hw).2)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hij,hi⟩,hbi⟩
    · intro hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      have his : «Σ».fullConeBasis s i∈s.val := by
        rw [«Σ».fullConeBasis_ray_set]
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
      refine Finset.mem_inter.mpr ⟨his,?_⟩
      by_contra hit
      have hiv : «Σ».fullConeBasis s i=v :=
        Finset.mem_singleton.mp (hv ▸ Finset.mem_sdiff.mpr ⟨his,hit⟩)
      exact (Finset.mem_erase.mp hi).1
        ((«Σ».fullConeBasis s).injective (hiv.trans hbj.symm))
  have hsub : insert u (s.val∩t.val)⊆t.val :=
    Finset.insert_subset hut Finset.inter_subset_right
  have huinter : u∉s.val∩t.val := fun h=>hus (Finset.mem_inter.mp h).1
  have hc : (insert u (s.val∩t.val)).card=n := by
    rw [Finset.card_insert_of_notMem huinter,hst]
    omega
  have ht : t.val=insert u (s.val∩t.val) :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [«Σ».fullCones_card,hc])).symm
  exact ⟨j,hmeet,by rw [ht,hmeet]⟩

/-- In the quotient rank-one fan an extra ray cannot project to the
original positive ray: injectivity of the actual star-ray projection
would identify the two original rays. Hence its coordinate is `-1`. -/
theorem adjacentWall_transverse (s t : «Σ».fullCones) (j : Fin n)
    (u : Lattice n)
    (ht : t.val=insert u ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hus : u∉s.val) : («Σ».fullConeBasis s).repr u j = -1 := by
  let I := «Σ».wallIndices s j
  let b := «Σ».fullConeBasis s
  let Γ := «Σ».wallCurveFan s j
  have hFs : I.image b⊆s.val := «Σ».wallCone_subset_full s j
  have hFt : I.image b⊆t.val := by rw [ht]; exact Finset.subset_insert _ _
  have hu : u∈t.val\I.image b :=
    Finset.mem_sdiff.mpr ⟨by rw [ht]; exact Finset.mem_insert_self _ _,fun h=>hus (hFs h)⟩
  have hp := «Σ».projected_starRay_mem b I («Σ».wallCone_mem s j)
    («Σ».fullCones_mem t) hFt hu
  change coneQuotientLattice b I u ∈ Γ.rays at hp
  rw [Γ.oneDimensional_rays («Σ».wallIndices_codimension s j),
    Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with hp|hp
  · have hueq : u=b j := «Σ».coneQuotient_injective_star_rays b I
      («Σ».fullCones_mem t) («Σ».fullCones_mem s) hFt hFs hu
      («Σ».fullConeBasis_mem_sdiff_wall s j)
      (hp.trans («Σ».wall_quotient_positive s j).symm)
    apply (hus ?_).elim
    rw [hueq]
    exact (Finset.mem_sdiff.mp («Σ».fullConeBasis_mem_sdiff_wall s j)).1
  · let q : Fin (n-I.card) := ⟨0,by rw [«Σ».wallIndices_codimension]; omega⟩
    have hq := congrFun hp q
    rw [«Σ».wall_quotient_coordinate] at hq
    exact hq

variable (k : Type u) [Field k] (hpure : «Σ».IsPure)

/-- The degree condition on the actual invariant wall curves, expressed
using genuine sheaf pullback and the uniquely determined curve degree. -/
def CartierWallDegreesAtLeast (D : CartierData («Σ».fanScheme k)) (bound : ℕ) : Prop :=
  ∀ (s : «Σ».fullCones) (j : Fin n) (degree : ℤ),
    («Σ».wallCurveFan s j).OneDimensionalHasDegree («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf) degree →
        (bound : ℤ)≤degree

theorem cartierWallDegreesAtLeast_iso (D E : CartierData («Σ».fanScheme k))
    (F : D.sheaf ≅ E.sheaf) (bound : ℕ) :
    «Σ».CartierWallDegreesAtLeast k D bound ↔ «Σ».CartierWallDegreesAtLeast k E bound := by
  constructor
  · intro h s j d hd
    apply h s j d
    exact ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
      («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).mapIso F) d).mpr hd
  · intro h s j d hd
    apply h s j d
    exact ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iso
      («Σ».wallIndices_codimension s j) k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).mapIso F) d).mp hd

theorem cartierCoefficients_hasWallSlacksAtLeast
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ)
    (hD : «Σ».CartierWallDegreesAtLeast k D bound) :
    «Σ».HasWallSlacksAtLeast («Σ».cartierCoefficients k hpure D) bound := by
  intro s t hst u hut hus
  obtain ⟨j,hmeet,ht⟩ := «Σ».adjacentWall_basisIndex s t hst u hut hus
  exact hD s j _ («Σ».wallCurve_cartier_hasDegree s j k hpure D t u ht
    («Σ».adjacentWall_transverse s t j u ht hus))

/-- The recovered divisor polytope has exactly the original normal fan,
is smooth, and satisfies the same lower bound on every actual edge. -/
theorem exists_polytope_of_cartierCurveDegrees
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ) (hbound : 0<bound)
    (hD : «Σ».CartierWallDegreesAtLeast k D bound) :
    ∃ P : LatticePolytope n,
      P.carrier=«Σ».fanPolytope (fun u=>(«Σ».cartierCoefficients k hpure D u : ℝ)) ∧
      P.Smooth ∧ P.normalFan=«Σ».realCones ∧ P.EdgesAtLeast bound :=
  «Σ».exists_smooth_latticePolytope_of_positive_wall_bounds hpure
    («Σ».cartierCoefficients k hpure D) bound hbound
    («Σ».cartierCoefficients_hasWallSlacksAtLeast k hpure D bound hD)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierCoefficients_hasWallSlacksAtLeast
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_polytope_of_cartierCurveDegrees
end
end Source_ToricDegreePolytopeBridge
-- END ORIGINAL PaperVerification.ToricDegreePolytopeBridge


-- BEGIN ORIGINAL PaperVerification.ToricSectionTensorNaturality
section Source_ToricSectionTensorNaturality

-- original header: module

-- original header: public import PaperVerification.ToricCartierTensor
-- original header: public import PaperVerification.ToricCartierBaseSections

-- original header: @[expose] public section

/-!
# Actual section multiplication under arbitrary line-bundle isomorphisms

The tensor sheaf is the genuine sheafification of sectionwise tensor
products. Naturality of its sheafification unit proves compatibility on
pure sections. Consequently arbitrary isomorphisms of the two line
bundles induce a commuting square for their actual section multiplication,
without any compatibility assumption on fractional embeddings.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

variable {X : Scheme.{u}}

theorem tensorSheafIso_pure_sections {M M' N N' : X.Modules}
    (F : M ≅ M') (G : N ≅ N') (U : X.Opens)
    (s : Γ(M,U)) (t : Γ(N,U)) :
    (tensorSheafIso F G).hom.app U
      ((tensorSheafUnit M N).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
      (tensorSheafUnit M' N').app (op U)
        (F.hom.app U s ⊗ₜ[Γ(X,U)] G.hom.app U t) := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let h := ((SheafOfModules.forget _).map F.hom) ⊗ₘ
    ((SheafOfModules.forget _).map G.hom)
  have he := congrArg (fun a=>a.app (op U) (s ⊗ₜ[Γ(X,U)] t))
    (adj.unit.naturality h)
  exact he.symm

variable [IsIntegral X]

namespace CartierData

variable (D D' E E' : CartierData X)

theorem tensorSheafAddIso_pure_sections (U : X.Opens)
    (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.tensorSheafAddIso E).hom.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
        D.sectionProduct E U s t := by
  change (D.localCocycle.tensorSheafMulIso E.localCocycle).hom.app U
    ((tensorSheafIso D.presentationIso E.presentationIso).hom.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t))) = _
  rw [tensorSheafIso_pure_sections,RationalCartierCocycle.tensorSheafMulIso_pure_sections]
  rfl

def addSheafIso (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf) :
    (D.add E).sheaf ≅ (D'.add E').sheaf :=
  (D.tensorSheafAddIso E).symm ≪≫ tensorSheafIso F G ≪≫ D'.tensorSheafAddIso E'

theorem addSheafIso_sectionProduct
    (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf)
    (U : X.Opens) (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.addSheafIso D' E E' F G).hom.app U (D.sectionProduct E U s t) =
      D'.sectionProduct E' U (F.hom.app U s) (G.hom.app U t) := by
  rw [← D.tensorSheafAddIso_pure_sections E U s t]
  change (D'.tensorSheafAddIso E').hom.app U
    ((tensorSheafIso F G).hom.app U
      ((D.tensorSheafAddIso E).inv.app U
        ((D.tensorSheafAddIso E).hom.app U
          ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t))))) = _
  have he : (D.tensorSheafAddIso E).inv.app U
      ((D.tensorSheafAddIso E).hom.app U
        ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t))) =
      (tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t) := by
    exact congrArg (fun h=>h.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t)))
      (D.tensorSheafAddIso E).hom_inv_id
  rw [he,tensorSheafIso_pure_sections,tensorSheafAddIso_pure_sections]

end CartierData

namespace BaseSections

open scoped BaseSections

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]

def globalSectionsIso {M N : X.Modules} (F : M ≅ N) : Γ(M,⊤) ≃ₗ[k] Γ(N,⊤) := by
  let e : Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) :=
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso F)).toLinearEquiv
  exact e.restrictScalars k

@[simp] theorem globalSectionsIso_apply {M N : X.Modules} (F : M ≅ N) (s : Γ(M,⊤)) :
    globalSectionsIso k F s=F.hom.app ⊤ s := rfl

end BaseSections

namespace CartierData

open scoped BaseSections

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (D D' E E' : CartierData X)
    (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf)

theorem sectionMultiplicationOver_sheafIso :
    (BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)).toLinearMap.comp
      (D.sectionMultiplicationOver k E) =
    (D'.sectionMultiplicationOver k E').comp
      (TensorProduct.map (BaseSections.globalSectionsIso k F).toLinearMap
        (BaseSections.globalSectionsIso k G).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  change BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)
      (D.sectionProduct E ⊤ s t) =
    D'.sectionProduct E' ⊤ (BaseSections.globalSectionsIso k F s)
      (BaseSections.globalSectionsIso k G t)
  exact D.addSheafIso_sectionProduct D' E E' F G ⊤ s t

include F G in
/-- Surjectivity of the actual tensor multiplication is an invariant of
the actual line bundles, independently of fractional presentations. -/
theorem sectionMultiplicationOver_surjective_iff_sheafIso :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (D'.sectionMultiplicationOver k E') := by
  let es := TensorProduct.congr (BaseSections.globalSectionsIso k F)
    (BaseSections.globalSectionsIso k G)
  let et := BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)
  have he (z) : et (D.sectionMultiplicationOver k E z)=
      D'.sectionMultiplicationOver k E' (es z) :=
    congrArg (fun h=>h z) (D.sectionMultiplicationOver_sheafIso k D' E E' F G)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_sheafIso
end
end Source_ToricSectionTensorNaturality
-- END ORIGINAL PaperVerification.ToricSectionTensorNaturality


-- BEGIN ORIGINAL PaperVerification.ToricFanDivisorTheorems
section Source_ToricFanDivisorTheorems

-- original header: module

-- original header: public import PaperVerification.ToricDegreePolytopeBridge
-- original header: public import PaperVerification.ToricSectionTensorNaturality
-- original header: public import PaperVerification.ToricCanonicalDifferentialGluing
-- original header: public import PaperVerification.ToricFanSectionMultiplication
-- original header: public import PaperVerification.ToricMainTheorems

-- original header: @[expose] public section

/-!
# The mixed theorems for arbitrary Cartier divisors on the actual fan scheme

The inputs here are actual invertible fractional sheaves. The lower
bounds refer to the degrees of their actual restrictions to the invariant
wall curves. The recovered polytopes and their edge bounds are consequences
of those inputs. The adjoint section map is the actual base-field tensor
multiplication; its canonical factor comes from the local top differential
modules and their proved gluing.

The separate reconstruction of an intrinsic toric variety as a fan scheme
is needed to apply these statements to the manuscript's intrinsic inputs.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical Pointwise BaseSections

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]
    (hpure : «Σ».IsPure)

def divisorPolytope (D : CartierData («Σ».fanScheme k)) : Set (Ambient n) :=
  «Σ».fanPolytope (fun v => («Σ».cartierCoefficients k hpure D v : ℝ))

theorem cartierCoefficients_strictSupport_of_curveDegrees
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ) (hbound : 0 < bound)
    (hD : «Σ».CartierWallDegreesAtLeast k D bound) :
    «Σ».IsStrictSupport (fun v => («Σ».cartierCoefficients k hpure D v : ℝ)) :=
  «Σ».strictSupport_of_positive_wallSlacks hpure _
    («Σ».positiveWallSlacks_of_bound _ bound hbound
      («Σ».cartierCoefficients_hasWallSlacksAtLeast k hpure D bound hD))

/-- Dimension zero has no rays, so every support polytope is the actual
one-point ambient space. No positive lower bound is inserted in that case. -/
theorem divisorPolytope_dimension_zero (hn : n = 0)
    (D : CartierData («Σ».fanScheme k)) : «Σ».divisorPolytope k hpure D = Set.univ := by
  subst n
  ext x
  simp only [Set.mem_univ,iff_true]
  intro v hv
  exact («Σ».ray_ne_zero hv (Subsingleton.elim v 0)).elim

/-- The manuscript's prescribed quotient class, for arbitrary actual
Cartier divisors on the constructed smooth complete fan scheme. -/
theorem fanDivisor_prescribedParity
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D n)
    (hE : «Σ».CartierWallDegreesAtLeast k E n)
    (m : Lattice n)
    (hm : embed n m ∈ interior
      («Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a ∈ «Σ».divisorPolytope k hpure D ∧
      embed n b ∈ «Σ».divisorPolytope k hpure E ∧
      a + b = m ∧ parityClass n a = α := by
  by_cases hn : n = 0
  · subst n
    refine ⟨m,0,?_,?_,add_zero m,?_⟩
    · rw [«Σ».divisorPolytope_dimension_zero k hpure rfl D]
      exact Set.mem_univ _
    · rw [«Σ».divisorPolytope_dimension_zero k hpure rfl E]
      exact Set.mem_univ _
    · obtain ⟨r,hr⟩ := parityClass_surjective 0 α
      exact (congrArg (parityClass 0) (Subsingleton.elim m r)).trans hr
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨P,hP,hPs,hPf,hPb⟩ :=
      «Σ».exists_polytope_of_cartierCurveDegrees k hpure D n hnpos hD
    obtain ⟨Q,hQ,hQs,hQf,hQb⟩ :=
      «Σ».exists_polytope_of_cartierCurveDegrees k hpure E n hnpos hE
    have hPQ : P.SameNormalFan Q := hPf.trans hQf.symm
    have hm' : embed n m ∈ interior (P.minkowskiSum Q) := by
      simpa only [LatticePolytope.minkowskiSum,hP,hQ,divisorPolytope] using hm
    obtain ⟨a,b,ha,hb,hab,hα⟩ := toric_theorem_1_2_quotient_classes
      n P Q hPs hQs hPQ hPb hQb m hm' α
    exact ⟨a,b,by simpa only [hP,divisorPolytope] using ha,
      by simpa only [hQ,divisorPolytope] using hb,hab,hα⟩

/-- The full literal equality of lattice-point sets, with the interior
on the second summand and on the whole Minkowski sum. -/
theorem fanDivisor_adjointLatticePoints
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D (n+1))
    (hE : «Σ».CartierWallDegreesAtLeast k E (n+1)) :
    {m : Lattice n | embed n m ∈ «Σ».divisorPolytope k hpure D} +
      {m : Lattice n | embed n m ∈ interior («Σ».divisorPolytope k hpure E)} =
    {m : Lattice n | embed n m ∈ interior
      («Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E)} := by
  obtain ⟨P,hP,hPs,hPf,hPb⟩ :=
    «Σ».exists_polytope_of_cartierCurveDegrees k hpure D (n+1) (by omega) hD
  obtain ⟨Q,hQ,hQs,hQf,hQb⟩ :=
    «Σ».exists_polytope_of_cartierCurveDegrees k hpure E (n+1) (by omega) hE
  have hPQ : P.SameNormalFan Q := hPf.trans hQf.symm
  simpa only [LatticePolytope.minkowskiSum,hP,hQ,divisorPolytope] using
    toric_theorem_1_3_polytope_sets n P Q hPs hQs hPQ hPb hQb

theorem fanDivisor_adjointExponentSum
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D (n+1))
    (hE : «Σ».CartierWallDegreesAtLeast k E (n+1)) :
    «Σ».fanIntegralExponents
        («Σ».cartierCoefficients k hpure D +
          («Σ».cartierCoefficients k hpure E + fun _ => -1)) =
      «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D) +
        «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure E + fun _ => -1) := by
  let a := «Σ».cartierCoefficients k hpure D
  let b := «Σ».cartierCoefficients k hpure E
  have ha := «Σ».cartierCoefficients_strictSupport_of_curveDegrees k hpure D
    (n+1) (by omega) hD
  have hb := «Σ».cartierCoefficients_strictSupport_of_curveDegrees k hpure E
    (n+1) (by omega) hE
  have hsum : «Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E =
      «Σ».fanPolytope (fun v => ((a v+b v : ℤ) : ℝ)) := by
    change «Σ».fanPolytope (fun v => (a v : ℝ)) +
      «Σ».fanPolytope (fun v => (b v : ℝ)) = _
    calc
      _ = «Σ».fanPolytope ((fun v => (a v : ℝ)) + (fun v => (b v : ℝ))) :=
        («Σ».fanPolytope_add hpure (fun v => (a v : ℝ)) (fun v => (b v : ℝ))
          (IsStrictSupport.isNef «Σ» ha) (IsStrictSupport.isNef «Σ» hb)).symm
      _ = _ := congrArg «Σ».fanPolytope (funext (fun v =>
        (Int.cast_add (a v) (b v)).symm))
  have he := («Σ».fanDivisor_adjointLatticePoints k hpure D E hD hE).symm
  have hleft : {m : Lattice n | embed n m ∈ interior
        («Σ».divisorPolytope k hpure D + «Σ».divisorPolytope k hpure E)} =
      «Σ».fanIntegralExponents (a+(b+fun _ => -1)) := by
    ext m
    rw [Set.mem_setOf_eq,hsum,«Σ».lattice_mem_interior_iff_adjointSupport]
    simp only [fanIntegralExponents,Set.mem_setOf_eq,Pi.add_apply,sub_eq_add_neg,add_assoc]
  have hright : {m : Lattice n | embed n m ∈ interior («Σ».divisorPolytope k hpure E)} =
      «Σ».fanIntegralExponents (b+fun _ => -1) := by
    ext m
    change (embed n m ∈ interior («Σ».fanPolytope (fun v => (b v : ℝ)))) ↔ _
    rw [«Σ».lattice_mem_interior_iff_adjointSupport]
    simp only [fanIntegralExponents,Set.mem_setOf_eq,Pi.add_apply,sub_eq_add_neg]
  rw [hleft,hright] at he
  exact he

/-- Surjectivity of multiplication of the actual global sections of
`D` and `E + K`, where the canonical presentation is obtained by gluing
the actual local top Kähler differential modules. -/
theorem fanDivisor_adjointSectionMultiplication
    (D E : CartierData («Σ».fanScheme k))
    (hD : «Σ».CartierWallDegreesAtLeast k D (n+1))
    (hE : «Σ».CartierWallDegreesAtLeast k E (n+1))
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    Function.Surjective (D.sectionMultiplicationOver k
      (E.add («Σ».differentialVolumeData k hpure b₀))) := by
  let a := «Σ».cartierCoefficients k hpure D
  let b := «Σ».cartierCoefficients k hpure E
  let A := «Σ».fanCartierData k hpure a
  let B := «Σ».fanCartierData k hpure b
  let K := «Σ».differentialVolumeData k hpure b₀
  let K' := «Σ».fanCartierData k hpure (fun _ => -1)
  let F : D.sheaf ≅ A.sheaf :=
    («Σ».cartierData_linearlyEquivalent_fanCartier k hpure D).some
  let G : E.sheaf ≅ B.sheaf :=
    («Σ».cartierData_linearlyEquivalent_fanCartier k hpure E).some
  let H : K.sheaf ≅ K'.sheaf :=
    («Σ».differentialVolumeData_equivalent_canonical k hpure b₀).choose
  let J : (E.add K).sheaf ≅ («Σ».fanCartierData k hpure (b+fun _ => -1)).sheaf :=
    E.addSheafIso B K K' G H ≪≫
      («Σ».fanCartierData_add_equivalent k hpure b (fun _ => -1)).choose
  apply (D.sectionMultiplicationOver_surjective_iff_sheafIso k A
    (E.add K) («Σ».fanCartierData k hpure (b+fun _ => -1)) F J).mpr
  apply («Σ».fanSectionMultiplication_surjective_iff k hpure a (b+fun _ => -1)).mpr
  exact «Σ».fanDivisor_adjointExponentSum k hpure D E hD hE

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanDivisor_prescribedParity
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanDivisor_adjointLatticePoints
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanDivisor_adjointSectionMultiplication
end
end Source_ToricFanDivisorTheorems
-- END ORIGINAL PaperVerification.ToricFanDivisorTheorems


-- BEGIN ORIGINAL PaperVerification.ToricNormalizedCharacterShift
section Source_ToricNormalizedCharacterShift

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicSectionCharacters
-- original header: public import PaperVerification.ToricCartierChartValues
-- original header: public import PaperVerification.ToricLaurentUnits
-- original header: public import PaperVerification.ToricCartierSchemeIso
-- original header: public import PaperVerification.ToricDominantAffineCoordinates

-- original header: @[expose] public section

/-!
# The actual character shift caused by a second torus normalization

The exponent set is read from the Laurent values of genuine global
sections. A Cartier presentation whose local frames are units on the
torus has a Laurent-unit normalization factor. Its scalar and its
integral character exponent are retained explicitly. Consequently a
second normalization translates the exponent set by an actual lattice
vector; it does not silently identify two differently framed polytopes.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

namespace CartierData

/-- Unit frames characterize the ordinary fractional regular-function
module on every open contained in the specified open. -/
theorem sectionValueRange_eq_regular_of_unitFrames (E : CartierData X)
    {V : X.Opens} (hE : E.localCocycle.HasUnitFramesOn V)
    (U : X.Opens) [Nonempty U] (hU : U≤V) :
    (E.sectionValueRange U : Set X.functionField)=
      Set.range (X.germToFunctionField U) := by
  ext z
  change z ∈ E.sectionValueRange U ↔ z ∈ (X.germToFunctionField U).hom.range
  rw [E.mem_sectionValueRange_iff_localStalks,
    mem_regular_range_iff_stalkwise]
  constructor
  · intro h x hx
    obtain ⟨i,hi⟩ := E.localCocycle.covers x
    have hz := (regularAtSubring X x).mul_mem (h i x hx hi)
      (hE i x (hU hx) hi).1
    simpa only [div_mul_cancel₀ _ (E.localCocycle.generator i).ne_zero] using hz
  · intro h i x hx hi
    simpa only [div_eq_mul_inv] using
      (regularAtSubring X x).mul_mem (h x hx) (hE i x (hU hx) hi).2

theorem hasUnitFramesOn_dominantPullback (E : CartierData X)
    {V : X.Opens} (hE : E.localCocycle.HasUnitFramesOn V)
    (f : Y ⟶ X) [IsDominant f] :
    (E.dominantPullback f).localCocycle.HasUnitFramesOn (f ⁻¹ᵁ V) :=
  (E.localCocycle.hasUnitFramesOn_pullback V hE f).of_equivalent
    (E.dominantPullback f).localCocycle
    (E.dominantPullback f).equivalent_localCocycle

end CartierData

variable (k : Type u) [Field k] (n : ℕ)
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]

local instance : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

/-- The exponents of literal characters contained in the actual Laurent
image of the global-section space of a Cartier presentation. -/
def torusSectionExponents (E : CartierData X) : Set (Fin n→ℤ) :=
  characterExponents k (torusSectionCharacters k n X j E)

/-- An intrinsic exponent set: it is defined before choosing any fan,
projective embedding, affine invariant cover, or polytope description. -/
def intrinsicSectionExponents (D : CartierData X) : Set (Fin n→ℤ) :=
  characterExponents k (normalizedGlobalCharacters k n X j D)

theorem intrinsicSectionExponents_eq (D : CartierData X) :
    intrinsicSectionExponents k n X j D=
      torusSectionExponents k n X j (torusNormalizedCartier k n X j D) := by
  rw [intrinsicSectionExponents,normalizedGlobalCharacters_eq_torusSectionCharacters]
  rfl

/-- A genuine global torus frame of an already torus-trivial divisor
has an actual Laurent-unit rational value. -/
theorem torusCartierGenerator_laurentUnit (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    ∃ v : (AddMonoidAlgebra k (Fin n→ℤ))ˣ,
      openTorusRationalAlgHom k n X j (v : AddMonoidAlgebra k (Fin n→ℤ))=
        (torusCartierGenerator k n X j E : X.functionField) := by
  let W := j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)
  letI : Nonempty W := openImmersion_image_nonempty j ⊤
  have hW : W≤j.opensRange := by
    rw [show W=j ''ᵁ ⊤ from rfl,Scheme.Hom.image_top_eq_opensRange]
  obtain ⟨a,ha⟩ := E.chartFrameGenerator_isUnit_of_range j
    (torusCartierFrame k n X j E) W hW
    (E.sectionValueRange_eq_regular_of_unitFrames hE W hW)
  let A := CommRingCat.of (torusCoordinateRing k n)
  let φ : Γ(X,W) →+* AddMonoidAlgebra k (Fin n→ℤ) :=
    (Scheme.ΓSpecIso A).hom.hom.comp (j.appIso ⊤).hom.hom
  refine ⟨Units.map φ a,?_⟩
  rw [Units.coe_map,openTorusRationalAlgHom_value]
  change openImmersionGlobalToFunctionField j
    ((Scheme.ΓSpecIso A).inv (φ a))=_
  rw [show (Scheme.ΓSpecIso A).inv (φ a)=(j.appIso ⊤).hom a by
      exact (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.left_inv _,
    openImmersionRegularToFunctionField_eq_germ_image]
  simpa only [torusCartierGenerator,Units.val_mk0,Iso.hom_inv_id_apply] using ha

/-- Both the scalar and the integral character shift are obtained from
the genuine torus frame. No character-frame hypothesis is assumed. -/
theorem torusCartierGenerator_scalar_character (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    ∃ c : kˣ, ∃ m : Fin n→ℤ,
      (torusCartierGenerator k n X j E : X.functionField)=
        openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single m (c:k)) := by
  obtain ⟨v,hv⟩ := torusCartierGenerator_laurentUnit k n X j E hE
  obtain ⟨c,m,hm⟩ := laurent_unit_single k n v
  exact ⟨c,m,hv.symm.trans (congrArg (openTorusRationalAlgHom k n X j) hm)⟩

theorem mem_normalizedGlobalRange_iff (E : CartierData X) (z : X.functionField) :
    z∈((torusNormalizedCartier k n X j E).globalSectionValue k).range ↔
      (torusCartierGenerator k n X j E : X.functionField)*z∈
        (E.globalSectionValue k).range := by
  let q := torusCartierGenerator k n X j E
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨s,?_⟩
    change E.sectionValue ⊤ s=(q:X.functionField)*
      (E.scale q⁻¹).sectionValue ⊤ s
    simpa only [Units.val_inv_eq_inv_val,← mul_assoc,
      mul_inv_cancel₀ q.ne_zero,one_mul] using
      congrArg (fun r : X.functionField => (q : X.functionField) * r)
        (E.scale_sectionValue q⁻¹ ⊤ s).symm
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    change (E.scale q⁻¹).sectionValue ⊤ s=z
    change E.sectionValue ⊤ s = (q : X.functionField) * z at hs
    calc
      _ = ((q⁻¹ : X.functionFieldˣ) : X.functionField) * E.sectionValue ⊤ s :=
        E.scale_sectionValue q⁻¹ ⊤ s
      _ = z := by
        rw [Units.val_inv_eq_inv_val,hs,← mul_assoc,
          inv_mul_cancel₀ q.ne_zero,one_mul]

/-- Exact membership after normalization, retaining the full integral
translation and cancelling only the proved nonzero scalar. -/
theorem torusSectionExponents_normalize_iff (E : CartierData X)
    (c : kˣ) (v : Fin n→ℤ)
    (hq : (torusCartierGenerator k n X j E : X.functionField)=
      openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single v (c:k)))
    (m : Fin n→ℤ) :
    m∈torusSectionExponents k n X j E ↔
      m-v∈intrinsicSectionExponents k n X j E := by
  rw [intrinsicSectionExponents_eq]
  change openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single m (1:k))∈
      (E.globalSectionValue k).range ↔
    openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single (m-v) (1:k))∈
      ((torusNormalizedCartier k n X j E).globalSectionValue k).range
  rw [mem_normalizedGlobalRange_iff,hq,← map_mul,
    AddMonoidAlgebra.single_mul_single,mul_one,
    show v+(m-v)=m by abel]
  have hs : AddMonoidAlgebra.single m (c:k)=
      (c:k) • AddMonoidAlgebra.single m (1:k) := by
    simp only [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  rw [hs,map_smul]
  exact ((E.globalSectionValue k).range.smul_mem_iff c.ne_zero).symm

theorem torusSectionExponents_eq_translate (E : CartierData X)
    (c : kˣ) (v : Fin n→ℤ)
    (hq : (torusCartierGenerator k n X j E : X.functionField)=
      openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single v (c:k))) :
    torusSectionExponents k n X j E=
      (fun m=>v+m) '' intrinsicSectionExponents k n X j E := by
  ext m
  constructor
  · intro hm
    exact ⟨m-v,(torusSectionExponents_normalize_iff k n X j E c v hq m).mp hm,
      by abel⟩
  · rintro ⟨w,hw,rfl⟩
    apply (torusSectionExponents_normalize_iff k n X j E c v hq (v+w)).mpr
    simpa only [add_sub_cancel_left] using hw

end PaperVerification.ToricSchemes
end
end Source_ToricNormalizedCharacterShift
-- END ORIGINAL PaperVerification.ToricNormalizedCharacterShift


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicSectionPolytopes
section Source_ToricIntrinsicSectionPolytopes

-- original header: module

-- original header: public import PaperVerification.ToricNormalizedCharacterShift
-- original header: public import PaperVerification.ToricFanSectionCoordinates
-- original header: public import Mathlib.Analysis.Convex.Hull

-- original header: @[expose] public section

/-!
# Intrinsic section polytopes and the proved fan dictionary

The polytope is the real convex hull of the actual Laurent characters of
the torus-normalized global-section module. Its definition contains no
chosen fan. A torus-preserving scheme isomorphism and a second choice of
torus frame change this polytope by the explicitly exhibited integral
translation, and the remaining polytope is proved to be the actual fan
halfspace polytope.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)
    (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (jX : splitTorus k (Fin n→ℤ) ⟶ X)
    (jY : splitTorus k (Fin n→ℤ) ⟶ Y)
    [IsOpenImmersion jX] [IsOpenImmersion jY]
    [jX.IsOver (Spec (CommRingCat.of k))]
    [jY.IsOver (Spec (CommRingCat.of k))]
    (e : Y≅X) [e.hom.IsOver (Spec (CommRingCat.of k))]
    (he : jY≫e.hom=jX)

local instance : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

include he in
/-- A torus-preserving scheme isomorphism preserves the actual rational
Laurent characters, not merely an abstractly isomorphic character space. -/
theorem openTorusRationalAlgHom_schemeIso (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    dominantFunctionFieldMap e.hom (openTorusRationalAlgHom k n X jX f)=
      openTorusRationalAlgHom k n Y jY f := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  let jX' : Spec R ⟶ X := jX
  let jY' : Spec R ⟶ Y := jY
  letI : IsOpenImmersion jX' := ‹IsOpenImmersion jX›
  letI : IsOpenImmersion jY' := ‹IsOpenImmersion jY›
  exact dominantFunctionFieldMap_affineCoordinate R R jX' jY' e.hom (𝟙 R)
    (by rw [Spec.map_id,Category.id_comp]; exact he) f

include he in
theorem schemeIso_preimage_torusOpen :
    e.hom ⁻¹ᵁ jX.opensRange=jY.opensRange := by
  have hinj : Function.Injective e.hom := by
    intro y z h
    have hh := congrArg (fun x=>e.inv x) h
    have hcomp (w : Y) : e.inv (e.hom w)=w := by
      change (e.hom≫e.inv) w=w
      rw [e.hom_inv_id]
      rfl
    simpa only [hcomp] using hh
  ext y
  change e.hom y∈Set.range jX ↔ y∈Set.range jY
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t,hinj ?_⟩
    change (jY≫e.hom) t=e.hom y
    rw [he]
    exact ht
  · rintro ⟨t,rfl⟩
    refine ⟨t,?_⟩
    change jX t=(jY≫e.hom) t
    rw [he]

include he in
theorem torusSectionCharacters_schemeIso (D : CartierData X) :
    torusSectionCharacters k n Y jY (D.dominantPullback e.hom)=
      torusSectionCharacters k n X jX D := by
  ext f
  change openTorusRationalAlgHom k n Y jY f∈
      ((D.dominantPullback e.hom).globalSectionValue k).range ↔
    openTorusRationalAlgHom k n X jX f∈(D.globalSectionValue k).range
  rw [← openTorusRationalAlgHom_schemeIso k n X Y jX jY e he f]
  exact D.globalSectionRange_schemeIso_iff e _

include he in
theorem torusSectionExponents_schemeIso (D : CartierData X) :
    torusSectionExponents k n Y jY (D.dominantPullback e.hom)=
      torusSectionExponents k n X jX D := by
  unfold torusSectionExponents
  rw [torusSectionCharacters_schemeIso k n X Y jX jY e he D]

include he in
theorem normalizedPullback_unitFrames (D : CartierData X) :
    ((torusNormalizedCartier k n X jX D).dominantPullback e.hom).localCocycle.HasUnitFramesOn jY.opensRange := by
  have h := (torusNormalizedCartier k n X jX D).hasUnitFramesOn_dominantPullback
    (torusNormalizedCartier_unitFrames k n X jX D) e.hom
  rw [schemeIso_preimage_torusOpen k n X Y jX jY e he] at h
  exact h

include he in
/-- The exact intrinsic exponent shift under a genuine torus-preserving
scheme isomorphism. The divisor is pulled back as an actual Cartier sheaf. -/
theorem intrinsicSectionExponents_schemeIso_translate (D : CartierData X) :
    ∃ c : kˣ, ∃ v : Lattice n,
      let E := (torusNormalizedCartier k n X jX D).dominantPullback e.hom
      (torusCartierGenerator k n Y jY E : Y.functionField)=
          openTorusRationalAlgHom k n Y jY (AddMonoidAlgebra.single v (c:k)) ∧
      intrinsicSectionExponents k n X jX D=
        (fun m=>v+m) '' intrinsicSectionExponents k n Y jY E := by
  let E := (torusNormalizedCartier k n X jX D).dominantPullback e.hom
  obtain ⟨c,v,hv⟩ := torusCartierGenerator_scalar_character k n Y jY E
    (normalizedPullback_unitFrames k n X Y jX jY e he D)
  refine ⟨c,v,hv,?_⟩
  rw [intrinsicSectionExponents_eq,
    ← torusSectionExponents_schemeIso k n X Y jX jY e he,
    torusSectionExponents_eq_translate k n Y jY E c v hv]

/-- The intrinsic real section polytope, defined solely by actual global
sections and the original dense torus. -/
def intrinsicSectionPolytope (D : CartierData X) : Set (Ambient n) :=
  convexHull ℝ (embed n '' intrinsicSectionExponents k n X jX D)

theorem convexHull_embed_translate (v : Lattice n) (S : Set (Lattice n)) :
    convexHull ℝ (embed n '' ((fun m=>v+m) '' S))=
      (fun x : Ambient n=>embed n v+x) '' convexHull ℝ (embed n '' S) := by
  have h : embed n '' ((fun m=>v+m) '' S)=
      (fun x : Ambient n=>embed n v+x) '' (embed n '' S) := by
    rw [Set.image_image,Set.image_image]
    congr 1
    funext m
    exact map_add (embed n) v m
  rw [h]
  exact ((AffineEquiv.constVAdd ℝ (Ambient n) (embed n v)).toAffineMap.image_convexHull (embed n '' S)).symm

include he in
theorem intrinsicSectionPolytope_schemeIso_translate (D : CartierData X) :
    ∃ v : Lattice n,
      intrinsicSectionPolytope k n X jX D=
        (fun x : Ambient n=>embed n v+x) ''
          intrinsicSectionPolytope k n Y jY
            ((torusNormalizedCartier k n X jX D).dominantPullback e.hom) := by
  obtain ⟨c,v,hq,hv⟩ :=
    intrinsicSectionExponents_schemeIso_translate k n X Y jX jY e he D
  refine ⟨v,?_⟩
  unfold intrinsicSectionPolytope
  rw [hv,convexHull_embed_translate]

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricSchemes

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance intrinsicSection_splitTorus_isOpenImmersion : IsOpenImmersion
    (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
      «Σ».splitTorusOpenMap k) :=
  «Σ».splitTorusOpenMap_isOpenImmersion k

local instance intrinsicSection_splitTorus_isOver :
    (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
      «Σ».splitTorusOpenMap k).IsOver (Spec (CommRingCat.of k)) :=
  «Σ».splitTorusOpenMap_isOver k

theorem openTorusRationalAlgHom_eq_torusRationalAlgHom :
    openTorusRationalAlgHom k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k)=
      «Σ».torusRationalAlgHom k := by
  let j : ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k :=
    «Σ».splitTorusOpenMap k
  letI : IsOpenImmersion j := «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : j.IsOver (Spec (CommRingCat.of k)) := «Σ».splitTorusOpenMap_isOver k
  apply AlgHom.ext
  intro f
  exact (openTorusRationalAlgHom_value k n («Σ».fanScheme k) j f).trans
    («Σ».torusRationalMap_eq_openImmersion k f).symm

/-- The intrinsic normalized section exponents on the fan scheme are
exactly the actual lattice points of its recovered support polytope. -/
theorem intrinsicSectionExponents_eq_fanIntegralExponents (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    intrinsicSectionExponents k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D=
      «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D) := by
  let j : ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k :=
    «Σ».splitTorusOpenMap k
  letI : IsOpenImmersion j := «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : j.IsOver (Spec (CommRingCat.of k)) := «Σ».splitTorusOpenMap_isOver k
  refine (intrinsicSectionExponents_eq k n («Σ».fanScheme k) j D).trans ?_
  ext m
  change openTorusRationalAlgHom k n («Σ».fanScheme k) j
      (AddMonoidAlgebra.single m (1:k))∈
      Set.range ((«Σ».normalizedCartier k D).sectionValue ⊤) ↔ _
  have hj : openTorusRationalAlgHom k n («Σ».fanScheme k) j =
      «Σ».torusRationalAlgHom k := «Σ».openTorusRationalAlgHom_eq_torusRationalAlgHom k
  rw [hj]
  change «Σ».torusRationalMap k (AddMonoidAlgebra.single m (1:k))∈
      Set.range ((«Σ».normalizedCartier k D).sectionValue ⊤) ↔ _
  rw [«Σ».normalizedCartier_globalRange k hpure D]
  constructor
  · rintro ⟨f,hf,he⟩
    have hf' := («Σ».torusRationalMap_injective k) he
    rw [hf'] at hf
    exact (single_mem_characterModule k _ m).mp hf
  · intro hm
    exact ⟨AddMonoidAlgebra.single m 1,
      (single_mem_characterModule k _ m).mpr hm,rfl⟩

/-- For an integral nef support, the actual halfspace polytope is the
convex hull of all of its actual lattice points. Both inclusions are
proved; the integral Cartier vertices supply the reverse inclusion. -/
theorem convexHull_fanIntegralExponents (hpure : «Σ».IsPure)
    (a : Lattice n→ℤ) (ha : «Σ».IsNef (fun u=>(a u:ℝ))) :
    convexHull ℝ (embed n '' «Σ».fanIntegralExponents a)=
      «Σ».fanPolytope (fun u=>(a u:ℝ)) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨m,hm,rfl⟩
      exact hm
    · exact «Σ».convex_fanPolytope _
  · rw [«Σ».fanPolytope_eq_convexHull_cartier hpure _ ha]
    apply convexHull_mono
    rintro _ ⟨s,rfl⟩
    refine ⟨«Σ».cartierLatticePoint a s,?_,«Σ».embed_cartierLatticePoint a s⟩
    change embed n («Σ».cartierLatticePoint a s)∈«Σ».fanPolytope _
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_mem_of_nef ha s

theorem intrinsicSectionPolytope_eq_fanPolytope (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k))
    (hD : «Σ».IsNef (fun u=>(«Σ».cartierCoefficients k hpure D u:ℝ))) :
    intrinsicSectionPolytope k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D=
      «Σ».fanPolytope (fun u=>(«Σ».cartierCoefficients k hpure D u:ℝ)) := by
  unfold intrinsicSectionPolytope
  rw [«Σ».intrinsicSectionExponents_eq_fanIntegralExponents k hpure D]
  exact «Σ».convexHull_fanIntegralExponents hpure _ hD

/-- The intrinsic polytope and the intrinsic character set of an
arbitrary Cartier divisor are both the same integral translate of their
recovered fan counterparts. This comparison does not define either
intrinsic object using the fan. -/
theorem intrinsic_sections_fan_translate (hpure : «Σ».IsPure)
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : ToricSchemes.splitTorus k (Fin n→ℤ) ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]
    (e : «Σ».fanScheme k≅X) [e.hom.IsOver (Spec (CommRingCat.of k))]
    (he : «Σ».splitTorusOpenMap k≫e.hom=j) (D : CartierData X)
    (hD : «Σ».IsNef (fun u=>(«Σ».cartierCoefficients k hpure
      ((torusNormalizedCartier k n X j D).dominantPullback e.hom) u:ℝ))) :
    ∃ v : Lattice n,
      let E := (torusNormalizedCartier k n X j D).dominantPullback e.hom
      let a := «Σ».cartierCoefficients k hpure E
      intrinsicSectionExponents k n X j D=(fun m=>v+m) '' «Σ».fanIntegralExponents a ∧
      intrinsicSectionPolytope k n X j D=
        (fun x : Ambient n=>embed n v+x) '' «Σ».fanPolytope (fun u=>(a u:ℝ)) := by
  let E := (torusNormalizedCartier k n X j D).dominantPullback e.hom
  obtain ⟨c,v,hq,hv⟩ := intrinsicSectionExponents_schemeIso_translate
    k n X («Σ».fanScheme k) j («Σ».splitTorusOpenMap k) e he D
  rw [«Σ».intrinsicSectionExponents_eq_fanIntegralExponents k hpure E] at hv
  refine ⟨v,hv,?_⟩
  unfold intrinsicSectionPolytope
  rw [hv,convexHull_embed_translate,«Σ».convexHull_fanIntegralExponents hpure _ hD]

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricIntrinsicSectionPolytopes
-- END ORIGINAL PaperVerification.ToricIntrinsicSectionPolytopes


