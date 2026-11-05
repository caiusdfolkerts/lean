module

public import Continuation.CycleBounds.IncidenceRelabel
public import Continuation.CycleBounds.TorusStrata
public import Continuation.Geometry.OriginalLatticeGivenFan
public import Continuation.Geometry.OriginalLatticePolar

/-!
# Proposition 6.8 in the original integral lattice

The input is an arbitrary complete regular fan in an arbitrary integral
lattice. The chosen integral basis transports all cones, all primitive
rays, and the literal dual semigroup charts. The real-dual arrangement,
its integral translation lattice and its affine dimension are compared
explicitly. The final sheaf and every invariant curve live on the actual
colimit of the original character charts.

Projectivity is never assumed. The graph hypothesis permits parallel
edges and arbitrary orientations, and its graph minors are transported
through the exact bijection of ray labels.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes
open TauCeti.Toric Unimodular.CycleBounds Unimodular.SeriesParallel
open scoped Classical BigOperators CategoryTheory.MonObj

universe u v w

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
  {embedding : N →+ V} (Φ : Fan embedding) (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)

local notation "F" => geometricOriginalFan b Φ hcomplete hregular

include b hcomplete hregular

/-- The entire original primitive-ray set, with every sign retained. -/
abbrev OriginalRay := {z : N // Unimodular.ConeBases.IsRay Φ z}

/-- The inverse coordinate map on every primitive ray, not merely on
a selected maximal cone. -/
def originalRayEquiv : (F).rays ≃ OriginalRay Φ where
  toFun z := ⟨b.equivFun.symm z.val,
    (geometricOriginalFan_ray_iff b Φ hcomplete hregular _).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using z.property)⟩
  invFun z := ⟨b.equivFun z.val,
    (geometricOriginalFan_ray_iff b Φ hcomplete hregular _).mpr z.property⟩
  left_inv z := by
    apply Subtype.ext
    exact b.equivFun.apply_symm_apply z.val
  right_inv z := by
    apply Subtype.ext
    exact b.equivFun.symm_apply_apply z.val

/-- The original real functional, expressed in the scalar-extended basis. -/
def coordinateThomsenCovector (θ : Module.Dual ℝ V) : Module.Dual ℝ (Ambient n) :=
  dotProductEquiv ℝ (Fin n) (realCharacterCoordinates b Φ.lattice θ)

/-- The actual original evaluation pairing is preserved exactly. -/
theorem coordinateThomsenCovector_pairing (θ : Module.Dual ℝ V) (z : N) :
    coordinateThomsenCovector b Φ θ (embed n (b.equivFun z)) = θ (embedding z) := by
  have h := realCharacterCoordinates_pairing b Φ.lattice θ (embedding z)
  rw [realCoordinates_lattice] at h
  change dotProduct (realCharacterCoordinates b Φ.lattice θ)
    (embed n (b.equivFun z)) = _
  rw [dotProduct_comm]
  exact h

/-- The literal periodic arrangement cell in the original real dual. -/
def originalThomsenStratum (θ : Module.Dual ℝ V) : Set (Module.Dual ℝ V) :=
  {φ | ∀ z : OriginalRay Φ,
    if ∃ a : ℤ, θ (embedding z.val) = (a : ℝ) then φ (embedding z.val) = θ (embedding z.val)
    else (⌊θ (embedding z.val)⌋ : ℝ) < φ (embedding z.val) ∧ φ (embedding z.val) < (⌈θ (embedding z.val)⌉ : ℝ)}

/-- The ordinary affine-geometric dimension of the original cell. -/
def originalThomsenStratumDimension (θ : Module.Dual ℝ V) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (originalThomsenStratum Φ θ)).direction

theorem thomsenForms_originalPairing (θ : Module.Dual ℝ V) (z : (F).rays) :
    (F).thomsenForms z (realCharacterCoordinates b Φ.lattice θ) =
      θ (embedding (originalRayEquiv b Φ hcomplete hregular z).val) := by
  have h := realCharacterCoordinates_pairing b Φ.lattice θ
    (embedding (b.equivFun.symm z.val))
  rw [realCoordinates_lattice, LinearEquiv.apply_symm_apply] at h
  exact h

theorem mem_thomsenStratum_coordinates (θ φ : Module.Dual ℝ V) :
    realCharacterCoordinates b Φ.lattice φ ∈
      (F).thomsenStratum (coordinateThomsenCovector b Φ θ) ↔
      φ ∈ originalThomsenStratum Φ θ := by
  simp only [SmoothCompleteFan.thomsenStratum, coordinateThomsenCovector,
    LinearEquiv.symm_apply_apply, integerStratum, Set.mem_setOf_eq,
    thomsenForms_originalPairing, originalThomsenStratum]
  constructor
  · intro h z
    simpa only [Equiv.apply_symm_apply] using
      h ((originalRayEquiv b Φ hcomplete hregular).symm z)
  · intro h z
    exact h (originalRayEquiv b Φ hcomplete hregular z)

/-- The whole original cell is transported, not just its active subspace. -/
theorem originalThomsenStratum_coordinates (θ : Module.Dual ℝ V) :
    realCharacterCoordinates b Φ.lattice '' originalThomsenStratum Φ θ =
      (F).thomsenStratum (coordinateThomsenCovector b Φ θ) := by
  ext x
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (mem_thomsenStratum_coordinates b Φ hcomplete hregular θ φ).mpr hφ
  · intro hx
    refine ⟨(realCharacterCoordinates b Φ.lattice).symm x, ?_,
      (realCharacterCoordinates b Φ.lattice).apply_symm_apply x⟩
    apply (mem_thomsenStratum_coordinates b Φ hcomplete hregular θ _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hx

/-- The dimension in Proposition 6.8 is unchanged in the original lattice. -/
theorem originalThomsenStratumDimension_coordinates (θ : Module.Dual ℝ V) :
    originalThomsenStratumDimension Φ θ =
      (F).thomsenStratumDimension (coordinateThomsenCovector b Φ θ) := by
  let f := (realCharacterCoordinates b Φ.lattice).toLinearMap.toAffineMap
  have hm : (affineSpan ℝ (originalThomsenStratum Φ θ)).map f =
      affineSpan ℝ ((F).thomsenStratum (coordinateThomsenCovector b Φ θ)) := by
    rw [AffineSubspace.map_span]
    exact congrArg (affineSpan ℝ)
      (originalThomsenStratum_coordinates b Φ hcomplete hregular θ)
  unfold originalThomsenStratumDimension SmoothCompleteFan.thomsenStratumDimension
  rw [← hm, AffineSubspace.map_direction]
  exact ((realCharacterCoordinates b Φ.lattice).finrank_map_eq _).symm

/-- The original embedded character lattice is mapped onto the full
integer coordinate lattice, with no finite-index enlargement. -/
theorem originalCharacterLattice_coordinates :
    Φ.lattice.realCharacter.range.map
      (realCharacterCoordinates b Φ.lattice).toAddEquiv.toAddMonoidHom =
        (embed n).range := by
  ext x
  constructor
  · rintro ⟨φ, ⟨m, rfl⟩, rfl⟩
    exact ⟨characterCoordinates b m, (realCharacterCoordinates_lattice b Φ.lattice m).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨Φ.lattice.realCharacter ((characterCoordinates b).symm m),
      ⟨_, rfl⟩, ?_⟩
    change realCharacterCoordinates b Φ.lattice (Φ.lattice.realCharacter ((characterCoordinates b).symm m)) = _
    rw [realCharacterCoordinates_lattice, LinearEquiv.apply_symm_apply]

/-- The real character torus uses the actual dual lattice Hom(N,ℤ). -/
abbrev OriginalCharacterTorus := Module.Dual ℝ V ⧸ Φ.lattice.realCharacter.range

def originalCharacterTorusCoordinates : OriginalCharacterTorus Φ ≃+ CharacterTorus n :=
  QuotientAddGroup.congr _ _ (realCharacterCoordinates b Φ.lattice).toAddEquiv
    (originalCharacterLattice_coordinates b Φ hcomplete hregular)

def originalTorusStratum (θ : Module.Dual ℝ V) : Set (OriginalCharacterTorus Φ) :=
  QuotientAddGroup.mk' Φ.lattice.realCharacter.range '' originalThomsenStratum Φ θ

theorem originalTorusStratum_coordinates (θ : Module.Dual ℝ V) :
    originalCharacterTorusCoordinates b Φ hcomplete hregular '' originalTorusStratum Φ θ =
      (F).torusStratum (coordinateThomsenCovector b Φ θ) := by
  change originalCharacterTorusCoordinates b Φ hcomplete hregular ''
    (QuotientAddGroup.mk' Φ.lattice.realCharacter.range '' originalThomsenStratum Φ θ) =
      characterTorusProjection n ''
        (F).thomsenStratum (coordinateThomsenCovector b Φ θ)
  rw [← originalThomsenStratum_coordinates b Φ hcomplete hregular θ,
    Set.image_image, Set.image_image]
  rfl

/-- Every actual original torus stratum, indexed by its subset. -/
def OriginalTorusStratum := {S : Set (OriginalCharacterTorus Φ) //
  ∃ θ : Module.Dual ℝ V, S = originalTorusStratum Φ θ}

namespace OriginalTorusStratum

variable {Φ}

def representative (σ : OriginalTorusStratum Φ) : Module.Dual ℝ V := σ.property.choose

theorem carrier_eq (σ : OriginalTorusStratum Φ) :
    σ.val = originalTorusStratum Φ σ.representative := σ.property.choose_spec

def dimension (σ : OriginalTorusStratum Φ) : ℕ :=
  originalThomsenStratumDimension Φ σ.representative

end OriginalTorusStratum

theorem OriginalTorusStratum.dimension_eq (σ : OriginalTorusStratum Φ)
    (θ : Module.Dual ℝ V) (hθ : σ.val = originalTorusStratum Φ θ) :
    σ.dimension = originalThomsenStratumDimension Φ θ := by
  unfold OriginalTorusStratum.dimension
  rw [originalThomsenStratumDimension_coordinates b Φ hcomplete hregular,
    originalThomsenStratumDimension_coordinates b Φ hcomplete hregular]
  apply (F).thomsenStratumDimension_eq_of_torusStratum_eq
  rw [← originalTorusStratum_coordinates b Φ hcomplete hregular,
    ← originalTorusStratum_coordinates b Φ hcomplete hregular,
    ← σ.carrier_eq, ← hθ]
  all_goals first | exact b | exact hcomplete | exact hregular | exact n

variable (k : Type u) [Field k]

/-- The actual original semigroup-chart colimit, with its glued scalar map. -/
abbrev originalFanOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (originalSchemeStructureMap b Φ.lattice k F)

/-- The original action is the transport of the glued character action
through the proved isomorphism of the original semigroup diagrams. -/
instance originalFan_torusAction :
    ModObj (splitTorusOver k (Lattice n)) (originalFanOver b Φ hcomplete hregular k) := by
  letI : IsMonHom (Iso.refl (splitTorusOver k (Lattice n))).hom := by
    change IsMonHom (𝟙 (splitTorusOver k (Lattice n)))
    infer_instance
  exact ModObj.ofIso (Iso.refl (splitTorusOver k (Lattice n)))
    (givenFanGluingOverIso b Φ hcomplete hregular k).symm

instance givenFanGluingOverIso_isModHom :
    IsModHom (splitTorusOver k (Lattice n))
      (givenFanGluingOverIso b Φ hcomplete hregular k).hom where
  smul_hom := by
    change ((𝟙 _ ⊗ₘ (givenFanGluingOverIso b Φ hcomplete hregular k).hom) ≫
      γ[splitTorusOver k (Lattice n), (F).fanSchemeOver k] ≫
        (givenFanGluingOverIso b Φ hcomplete hregular k).inv) ≫
      (givenFanGluingOverIso b Φ hcomplete hregular k).hom = _
    simp

/-- The positive Thomsen sheaf on the literal original gluing. Its
coefficients on original rays are identified in the following theorem. -/
def originalPositiveThomsenSheaf (θ : Module.Dual ℝ V) :
    (originalFanOver b Φ hcomplete hregular k).left.Modules :=
  (Scheme.Modules.pullback (givenFanGluingOverIso b Φ hcomplete hregular k).hom.left).obj
    ((F).fanCartierData k (F).isPure
      ((F).thomsenCoefficients (coordinateThomsenCovector b Φ θ))).sheaf

theorem originalPositiveThomsen_coefficients (θ : Module.Dual ℝ V) (z : N) :
    (F).thomsenCoefficients (coordinateThomsenCovector b Φ θ) (b.equivFun z) =
      ⌈θ (embedding z)⌉ := by
  change ⌈coordinateThomsenCovector b Φ θ (embed n (b.equivFun z))⌉ = _
  rw [coordinateThomsenCovector_pairing b Φ hcomplete hregular]

/-- The original positive Thomsen sheaf is independent, up to actual sheaf
isomorphism, of every choice of a lift of its torus stratum. -/
theorem originalPositiveThomsenSheaf_same_stratum (θ φ : Module.Dual ℝ V)
    (h : originalTorusStratum Φ θ = originalTorusStratum Φ φ) :
    Nonempty (originalPositiveThomsenSheaf b Φ hcomplete hregular k θ ≅
      originalPositiveThomsenSheaf b Φ hcomplete hregular k φ) := by
  have hF : (F).torusStratum (coordinateThomsenCovector b Φ θ) =
      (F).torusStratum (coordinateThomsenCovector b Φ φ) := by
    rw [← originalTorusStratum_coordinates b Φ hcomplete hregular,
      ← originalTorusStratum_coordinates b Φ hcomplete hregular, h]
  obtain ⟨J⟩ := (F).thomsenCartier_same_torusStratum k
    (coordinateThomsenCovector b Φ θ) (coordinateThomsenCovector b Φ φ) hF
  exact ⟨(Scheme.Modules.pullback
    (givenFanGluingOverIso b Φ hcomplete hregular k).hom.left).mapIso J⟩

variable {W : Type w} [Fintype W]

/-- Proposition 6.8 in the full original lattice and on the original
character-chart gluing, for every original real character and every
actual invariant integral curve. -/
theorem proposition_6_8_original_lattice
    (G : IncidenceGraph W (OriginalRay Φ)) (hG : G.edges = Set.univ)
    (hK : ¬ G.HasK4Minor)
    (δ : N →ₗ[ℤ] (W → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ z : OriginalRay Φ,
      δ z.val = Pi.single (G.source z) 1 - Pi.single (G.target z) 1)
    (θ : Module.Dual ℝ V)
    (C : InvariantIntegralCurve k n (originalFanOver b Φ hcomplete hregular k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (originalPositiveThomsenSheaf b Φ hcomplete hregular k θ)) d ∧
      d ≤ (originalThomsenStratumDimension Φ θ : ℤ) := by
  let eRay := originalRayEquiv b Φ hcomplete hregular
  let G' := G.reindex eRay
  have hG' : G'.edges = Set.univ := by
    simp [G', IncidenceGraph.reindex, hG]
  have hK' : ¬ G'.HasK4Minor := by
    intro h
    exact hK ((G.hasK4Minor_reindex_iff eRay).mp h)
  let δ' : Lattice n →ₗ[ℤ] (W → ℤ) := δ.comp b.equivFun.symm.toLinearMap
  have hinj' : Function.Injective δ' := hinj.comp b.equivFun.symm.injective
  have hδ' (z : (F).rays) :
      δ' z.val = Pi.single (G'.source z) 1 - Pi.single (G'.target z) 1 :=
    hδ (eRay z)
  let e := givenFanGluingOverIso b Φ hcomplete hregular k
  obtain ⟨d, hd, hbound⟩ := (F).thomsen_invariantCurve_degree_bound k
    G' hG' hK' δ' hinj' hδ' (coordinateThomsenCovector b Φ θ) (C.mapIso e)
  let L := ((F).fanCartierData k (F).isPure
    ((F).thomsenCoefficients (coordinateThomsenCovector b Φ θ))).sheaf
  let E : (Scheme.Modules.pullback C.inclusion.left).obj
      (originalPositiveThomsenSheaf b Φ hcomplete hregular k θ) ≅
      (Scheme.Modules.pullback (C.mapIso e).inclusion.left).obj L :=
    (Scheme.Modules.pullbackComp C.inclusion.left e.hom.left).app L
  refine ⟨d, (rationalCurveHasDegree_iso k E d).mpr hd, ?_⟩
  rwa [originalThomsenStratumDimension_coordinates b Φ hcomplete hregular θ]

/-- The same bound quantified over actual strata of the original real
character torus, including every lower dimensional stratum. -/
theorem proposition_6_8_original_torusStrata
    (G : IncidenceGraph W (OriginalRay Φ)) (hG : G.edges = Set.univ)
    (hK : ¬ G.HasK4Minor)
    (δ : N →ₗ[ℤ] (W → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ z : OriginalRay Φ,
      δ z.val = Pi.single (G.source z) 1 - Pi.single (G.target z) 1)
    (σ : OriginalTorusStratum Φ)
    (C : InvariantIntegralCurve k n (originalFanOver b Φ hcomplete hregular k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (originalPositiveThomsenSheaf b Φ hcomplete hregular k σ.representative)) d ∧
      d ≤ (σ.dimension : ℤ) :=
  proposition_6_8_original_lattice b Φ hcomplete hregular k
    G hG hK δ hinj hδ σ.representative C

/-- The same conclusion for every lifted representative of each original
stratum, rather than only the representative selected in its definition. -/
theorem proposition_6_8_original_torusStrata_every_representative
    (G : IncidenceGraph W (OriginalRay Φ)) (hG : G.edges = Set.univ)
    (hK : ¬ G.HasK4Minor)
    (δ : N →ₗ[ℤ] (W → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ z : OriginalRay Φ,
      δ z.val = Pi.single (G.source z) 1 - Pi.single (G.target z) 1)
    (σ : OriginalTorusStratum Φ) (θ : Module.Dual ℝ V)
    (hθ : σ.val = originalTorusStratum Φ θ)
    (C : InvariantIntegralCurve k n (originalFanOver b Φ hcomplete hregular k)) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj
        (originalPositiveThomsenSheaf b Φ hcomplete hregular k θ)) d ∧
      d ≤ (σ.dimension : ℤ) := by
  rw [OriginalTorusStratum.dimension_eq b Φ hcomplete hregular σ θ hθ]
  exact proposition_6_8_original_lattice b Φ hcomplete hregular k
    G hG hK δ hinj hδ θ C

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalThomsenStratum_coordinates
#print axioms PaperVerification.OriginalLatticeCharts.originalThomsenStratumDimension_coordinates
#print axioms PaperVerification.OriginalLatticeCharts.originalTorusStratum_coordinates
#print axioms PaperVerification.OriginalLatticeCharts.proposition_6_8_original_lattice
#print axioms PaperVerification.OriginalLatticeCharts.proposition_6_8_original_torusStrata
