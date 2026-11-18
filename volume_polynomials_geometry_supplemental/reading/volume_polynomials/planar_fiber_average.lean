module

public import VolumePolynomials.ConvexFibers
public import VolumePolynomials.TripleMinkowskiFunctional
public import VolumePolynomials.MixedVolumeTransport
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! # Minkowski averaging in the literal product coordinates

`Plane` and `Space k` have the sup norm. We transport both factors through
the actual measure-preserving `WithLp 2` equivalences before applying the
inner-product averaging theorem. Thus all areas and uniform averages below
retain their original product-Lebesgue meaning. The zero-dimensional base
is treated separately by its actual Dirac volume.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

namespace MinkowskiFunctional

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def comp_mapBody (φ : MinkowskiFunctional F) (L : E →L[ℝ] F) :
    MinkowskiFunctional E where
  toFun K := φ (mapBody L K)
  continuous_toFun := φ.continuous_toFun.comp (continuous_mapBody L)
  monotone h := φ.monotone (Set.image_mono h)
  map_add K M := by rw [mapBody_add, φ.map_add]
  map_nonneg_smul r hr K := by rw [mapBody_smul, φ.map_nonneg_smul r hr]

@[simp] theorem comp_mapBody_apply (φ : MinkowskiFunctional F) (L : E →L[ℝ] F)
    (K : ConvexBody E) : φ.comp_mapBody L K = φ (mapBody L K) := rfl

end MinkowskiFunctional

theorem mapBody_equiv_symm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E ≃L[ℝ] F) (K : ConvexBody E) :
    mapBody T.symm.toContinuousLinearMap (mapBody T.toContinuousLinearMap K) = K := by
  first
  | apply ConvexBody.ext
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      have hyx : y = x := by
        change T.symm (T y) = x at hxy
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hxy
      exact hyx ▸ hy
    · intro hx
      exact ⟨T x, ⟨x, hx, rfl⟩, T.symm_apply_apply x⟩

theorem uniformAverage_image_measurePreserving {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T) (Z : Set E) (f : F → ℝ) :
    uniformAverage (T '' Z) f = uniformAverage Z (fun x => f (T x)) := by
  first
  | have hmeasure := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' Z)
    rw [Set.preimage_image_eq Z T.injective] at hmeasure
    have hreal : volume.real (T '' Z) = volume.real Z :=
      congrArg ENNReal.toReal hmeasure.symm
    rw [uniformAverage, uniformAverage,
      hT.setIntegral_image_emb T.toHomeomorph.measurableEmbedding f Z, hreal]

namespace ConvexFibers

section Equivalences

variable {E E' U U' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup U'] [NormedSpace ℝ U']

theorem projection_map_prodEquiv (T : E ≃L[ℝ] E') (S : U ≃L[ℝ] U')
    (F : ConvexBody (E × U)) :
    projection (mapBody (T.prodCongr S).toContinuousLinearMap F) = S '' projection F := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hpy⟩
      exact ⟨p.2, ⟨p, hp, rfl⟩, hpy⟩
    · rintro ⟨u, ⟨p, hp, hpu⟩, huy⟩
      exact ⟨(T p.1, S p.2), ⟨p, hp, rfl⟩, (congrArg S hpu).trans huy⟩

theorem fiberBody_map_prodEquiv (T : E ≃L[ℝ] E') (S : U ≃L[ℝ] U')
    (F : ConvexBody (E × U)) {y : U} (hy : y ∈ projection F) :
    fiberBody (mapBody (T.prodCongr S).toContinuousLinearMap F) (S y) =
      mapBody T.toContinuousLinearMap (fiberBody F y) := by
  first
  | have hy' : S y ∈ projection (mapBody (T.prodCongr S).toContinuousLinearMap F) := by
      first
      | rw [projection_map_prodEquiv]
        exact Set.mem_image_of_mem S hy
    apply ConvexBody.ext
    rw [coe_fiberBody _ hy', coe_mapBody, coe_fiberBody _ hy]
    ext x
    constructor
    · rintro ⟨⟨u, z⟩, huz, h⟩
      have hzy : z = y := S.injective (congrArg Prod.snd h)
      subst z
      exact ⟨u, huz, congrArg Prod.fst h⟩
    · rintro ⟨u, huy, hux⟩
      exact ⟨(u, y), huy, Prod.ext hux rfl⟩

end Equivalences

end ConvexFibers

namespace PlanarInteraction

open PlanarExtrusion ConvexFibers MinkowskiAverages

abbrev InnerPlane := WithLp 2 Plane
abbrev InnerBase (k : ℕ) := EuclideanSpace ℝ (Fin k)

def planeToInner : Plane ≃L[ℝ] InnerPlane :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm

def baseToInner (k : ℕ) : VolumePolynomials.Space k ≃L[ℝ] InnerBase k :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm

theorem planeToInner_preserving : MeasurePreserving planeToInner :=
  WithLp.volume_preserving_toLp ℝ ℝ

theorem baseToInner_preserving (k : ℕ) : MeasurePreserving (baseToInner k) :=
  PiLp.volume_preserving_toLp (Fin k)

def innerTotal {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    ConvexBody (InnerPlane × InnerBase k) :=
  mapBody (planeToInner.prodCongr (baseToInner k)).toContinuousLinearMap F

theorem innerTotal_projection {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k)) :
    projection (innerTotal F) = baseToInner k '' projection F :=
  projection_map_prodEquiv planeToInner (baseToInner k) F

theorem innerTotal_fiber {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k))
    {y : VolumePolynomials.Space k} (hy : y ∈ projection F) :
    fiberBody (innerTotal F) (baseToInner k y) =
      mapBody planeToInner.toContinuousLinearMap (fiberBody F y) :=
  fiberBody_map_prodEquiv planeToInner (baseToInner k) F hy

theorem innerTotal_area {k : ℕ} (F : ConvexBody (Plane × VolumePolynomials.Space k))
    {y : VolumePolynomials.Space k} (hy : y ∈ projection F) :
    volume.real (fiberBody (innerTotal F) (baseToInner k y) : Set InnerPlane) =
      volume.real (fiberBody F y : Set Plane) := by
  first
  | rw [innerTotal_fiber F hy]
    exact measureReal_image_measurePreserving volume volume planeToInner
      planeToInner_preserving _

theorem fiber_functional_integrable {k : ℕ}
    (F : ConvexBody (Plane × VolumePolynomials.Space k)) (φ : MinkowskiFunctional Plane) :
    IntegrableOn (fun y => φ (fiberBody F y)) (projection F) := by
  first
  | obtain ⟨R, hR⟩ := fibers_uniformly_bounded (innerTotal F)
    let ψ := φ.comp_mapBody planeToInner.symm.toContinuousLinearMap
    have h := functional_fiber_integrable (projection_compact (innerTotal F))
      (fiberBody_concave (innerTotal F)) hR ψ
    rw [innerTotal_projection] at h
    have hi := ((baseToInner_preserving k).integrableOn_image
      (baseToInner k).toHomeomorph.measurableEmbedding).mp h
    apply hi.congr_fun _ (projection_compact F).measurableSet
    intro y hy
    change φ (mapBody planeToInner.symm.toContinuousLinearMap
      (fiberBody (innerTotal F) (baseToInner k y))) = φ (fiberBody F y)
    rw [innerTotal_fiber F hy, mapBody_equiv_symm]

theorem projection_zero_base (F : ConvexBody (Plane × VolumePolynomials.Space 0)) :
    projection F = Set.univ := by
  first
  | apply Set.eq_univ_of_forall
    intro y
    obtain ⟨p, hp⟩ := F.nonempty
    refine ⟨p, hp, ?_⟩
    funext i
    exact Fin.elim0 i

theorem uniformAverage_zero_base (F : ConvexBody (Plane × VolumePolynomials.Space 0))
    (f : VolumePolynomials.Space 0 → ℝ) : uniformAverage (projection F) f = f 0 := by
  first
  | rw [projection_zero_base, uniformAverage, Measure.restrict_univ,
      Measure.volume_pi_eq_dirac (0 : VolumePolynomials.Space 0)]
    simp only [integral_dirac, measureReal_def, Measure.dirac_apply_of_mem (Set.mem_univ _),
      ENNReal.toReal_one, div_one]

/-- Lemma 6.1 in the literal coordinate spaces, including the exact
zero-dimensional case. The base dimension is unrestricted. -/
theorem planar_average_coordinates (k : ℕ)
    (F : ConvexBody (Plane × VolumePolynomials.Space k))
    (hvol : 0 < volume.real (projection F)) :
    ∃ A : ConvexBody Plane,
      (∀ φ : MinkowskiFunctional Plane,
        φ A = uniformAverage (projection F) (fun y => φ (fiberBody F y))) ∧
      uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)) /
        berwaldConstant k ≤ volume.real (A : Set Plane) ∧
      (k = 0 → volume.real (A : Set Plane) =
        uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane))) := by
  first
  | by_cases hk : k = 0
    · subst k
      refine ⟨fiberBody F 0, ?_, ?_, ?_⟩
      · intro φ
        rw [uniformAverage_zero_base]
      · rw [uniformAverage_zero_base]
        norm_num [berwaldConstant]
      · intro _
        rw [uniformAverage_zero_base]
    have hbase : 0 < finrank ℝ (InnerBase k) := by
      first
      | simpa only [InnerBase, finrank_euclideanSpace, Fintype.card_fin] using Nat.pos_of_ne_zero hk
    have hdim : finrank ℝ InnerPlane = 2 := by
      first
      | rw [(WithLp.linearEquiv 2 ℝ Plane).finrank_eq]
        exact PlanarCorner.plane_finrank
    have hvol' : 0 < volume.real (projection (innerTotal F)) := by
      first
      | rw [innerTotal_projection,
          measureReal_image_measurePreserving volume volume (baseToInner k) (baseToInner_preserving k)]
        exact hvol
    obtain ⟨A', hA', harea⟩ := planar_average_area hdim hbase (innerTotal F) hvol'
    let A := mapBody planeToInner.symm.toContinuousLinearMap A'
    have hAreaA : volume.real (A : Set Plane) = volume.real (A' : Set InnerPlane) :=
      measureReal_image_measurePreserving volume volume planeToInner.symm
        (MeasurePreserving.symm planeToInner.toHomeomorph.toMeasurableEquiv planeToInner_preserving) _
    have hmean : uniformAverage (projection (innerTotal F))
        (fun y => volume.real (fiberBody (innerTotal F) y : Set InnerPlane)) =
        uniformAverage (projection F) (fun y => volume.real (fiberBody F y : Set Plane)) := by
      first
      | rw [innerTotal_projection, uniformAverage_image_measurePreserving
          (baseToInner k) (baseToInner_preserving k)]
        unfold uniformAverage
        congr 1
        apply setIntegral_congr_fun (projection_compact F).measurableSet
        exact fun y hy => innerTotal_area F hy
    refine ⟨A, ?_, ?_, fun he => (hk he).elim⟩
    · intro φ
      have h := hA' (φ.comp_mapBody planeToInner.symm.toContinuousLinearMap)
      change φ A = uniformAverage (projection (innerTotal F))
        (fun y => φ (mapBody planeToInner.symm.toContinuousLinearMap (fiberBody (innerTotal F) y))) at h
      rw [innerTotal_projection, uniformAverage_image_measurePreserving
        (baseToInner k) (baseToInner_preserving k)] at h
      refine h.trans ?_
      unfold uniformAverage
      congr 1
      apply setIntegral_congr_fun (projection_compact F).measurableSet
      intro y hy
      change φ (mapBody planeToInner.symm.toContinuousLinearMap
        (fiberBody (innerTotal F) (baseToInner k y))) = φ (fiberBody F y)
      rw [innerTotal_fiber F hy, mapBody_equiv_symm]
    · rw [hAreaA]
      rw [hmean] at harea
      simpa only [InnerBase, finrank_euclideanSpace, Fintype.card_fin,
        div_eq_mul_inv, mul_comm] using harea

end PlanarInteraction
end VolumePolynomials
