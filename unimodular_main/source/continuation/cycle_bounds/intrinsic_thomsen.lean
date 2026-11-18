module

public import Continuation.CycleBounds.ActualAnticanonical
public import Continuation.Runtime.IntrinsicBoundaryCartier
public import Continuation.Runtime.IntrinsicFanPresentation
public import Continuation.Runtime.ProjectiveAmpleCartier
public import Recovery.Unimodular.IntrinsicToric.TorusEquivariance

/-!
# Corollary 6.9 on the independently specified toric variety

The periodic arrangement is defined directly from the character valuations
at the actual boundary prime divisors of the original scheme. Its strata
are subsets of the original real character torus, and their dimensions are
ordinary affine dimensions in a lifted chart. Reconstruction identifies
these sets with the fan arrangement, without changing a character or a
boundary valuation.

Every positive Thomsen divisor exists on the original scheme. Its sheaf
is compared with the genuine inverse pullback of the fan Cartier sheaf.
An arbitrary invariant integral curve is kept as the same curve scheme
while its inclusion is transported. The conclusion therefore concerns
every actual invariant curve of the original variety.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes
open Unimodular.CycleBounds Unimodular.NefBig
open scoped Classical

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
  {X : Over (Spec (CommRingCat.of k))}
  [ModObj (splitTorusOver k (Fin n → ℤ)) X]
  [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
  (T : SplitToricEmbedding k n X)

local instance intrinsicStratumNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- The literal periodic cell defined by all original boundary valuations. -/
def boundaryThomsenStratum (θ : Module.Dual ℝ (Ambient n)) : Set (Ambient n) :=
  integerStratum T.boundaryForm ((dotProductEquiv ℝ (Fin n)).symm θ)

/-- The usual affine dimension of that cell. -/
def boundaryThomsenStratumDimension (θ : Module.Dual ℝ (Ambient n)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (T.boundaryThomsenStratum θ)).direction

/-- The corresponding subset of the original real character torus. -/
def boundaryTorusStratum (θ : Module.Dual ℝ (Ambient n)) : Set (CharacterTorus n) :=
  characterTorusProjection n '' T.boundaryThomsenStratum θ

/-- All actual strata, indexed by their subsets of the character torus. -/
def BoundaryTorusStratum := {S : Set (CharacterTorus n) //
  ∃ θ : Module.Dual ℝ (Ambient n), S = T.boundaryTorusStratum θ}

namespace BoundaryTorusStratum

variable {T}

def representative (σ : T.BoundaryTorusStratum) : Module.Dual ℝ (Ambient n) :=
  σ.property.choose

theorem carrier_eq (σ : T.BoundaryTorusStratum) :
    σ.val = T.boundaryTorusStratum σ.representative := σ.property.choose_spec

def dimension (σ : T.BoundaryTorusStratum) : ℕ :=
  T.boundaryThomsenStratumDimension σ.representative

end BoundaryTorusStratum

section Presentation

variable (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X)
  (htorus : (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus)

include e htorus

/-- Quantification over the actual boundary valuations is precisely
quantification over every ray of the reconstructed fan. -/
theorem forall_boundaryValuation_iff_rays (P : Lattice n → Prop) :
    (∀ q : T.BoundaryPrime, P (T.boundaryValuation q)) ↔
      ∀ v : F.rays, P v.val := by
  have hr := T.completeBoundaryRaySet_presentation F e htorus
  constructor
  · intro h v
    have hv : v.val ∈ T.completeBoundaryRaySet := by
      rw [hr]
      exact v.property
    obtain ⟨q, hq⟩ := hv
    simpa only [hq] using h q
  · intro h q
    apply h ⟨T.boundaryValuation q, ?_⟩
    change T.boundaryValuation q ∈ (F.rays : Set _)
    rw [← hr]
    exact Set.mem_range_self q

/-- Equality of the whole lifted cells, including their open faces and
all lower dimensional strata. -/
theorem boundaryThomsenStratum_presentation (θ : Module.Dual ℝ (Ambient n)) :
    T.boundaryThomsenStratum θ = F.thomsenStratum θ := by
  ext x
  exact T.forall_boundaryValuation_iff_rays F e htorus (fun v =>
    if ∃ z : ℤ, dotProductEquiv ℝ (Fin n) (embed n v)
        ((dotProductEquiv ℝ (Fin n)).symm θ) = (z : ℝ) then
      dotProductEquiv ℝ (Fin n) (embed n v) x =
        dotProductEquiv ℝ (Fin n) (embed n v)
          ((dotProductEquiv ℝ (Fin n)).symm θ)
    else
      (⌊dotProductEquiv ℝ (Fin n) (embed n v)
        ((dotProductEquiv ℝ (Fin n)).symm θ)⌋ : ℝ) <
          dotProductEquiv ℝ (Fin n) (embed n v) x ∧
      dotProductEquiv ℝ (Fin n) (embed n v) x <
        (⌈dotProductEquiv ℝ (Fin n) (embed n v)
          ((dotProductEquiv ℝ (Fin n)).symm θ)⌉ : ℝ))

theorem boundaryThomsenStratumDimension_presentation
    (θ : Module.Dual ℝ (Ambient n)) :
    T.boundaryThomsenStratumDimension θ = F.thomsenStratumDimension θ := by
  unfold boundaryThomsenStratumDimension SmoothCompleteFan.thomsenStratumDimension
  rw [T.boundaryThomsenStratum_presentation F e htorus θ]

theorem boundaryTorusStratum_presentation (θ : Module.Dual ℝ (Ambient n)) :
    T.boundaryTorusStratum θ = F.torusStratum θ := by
  unfold boundaryTorusStratum SmoothCompleteFan.torusStratum
  rw [T.boundaryThomsenStratum_presentation F e htorus θ]

end Presentation

variable [X.left.IsProjectiveOver k]

/-- The geometric dimension is independent of every lifted representative
of an actual stratum in the character torus. -/
theorem boundaryThomsenStratumDimension_eq_of_torusStratum_eq
    (θ φ : Module.Dual ℝ (Ambient n))
    (h : T.boundaryTorusStratum θ = T.boundaryTorusStratum φ) :
    T.boundaryThomsenStratumDimension θ = T.boundaryThomsenStratumDimension φ := by
  obtain ⟨A, hA⟩ := exists_isAmpleModule_of_isProjectiveOver (X := X.left) k
  obtain ⟨F, e, ht⟩ := T.exists_fan_of_ordinaryAmple A.obj
    ((isInvertibleModule_iff_standard A.obj).mpr A.property) hA
  rw [T.boundaryThomsenStratumDimension_presentation F e ht θ,
    T.boundaryThomsenStratumDimension_presentation F e ht φ]
  apply F.thomsenStratumDimension_eq_of_torusStratum_eq θ φ
  rwa [T.boundaryTorusStratum_presentation F e ht θ,
    T.boundaryTorusStratum_presentation F e ht φ] at h

theorem BoundaryTorusStratum.dimension_eq (σ : T.BoundaryTorusStratum)
    (θ : Module.Dual ℝ (Ambient n)) (hθ : σ.val = T.boundaryTorusStratum θ) :
    σ.dimension = T.boundaryThomsenStratumDimension θ :=
  T.boundaryThomsenStratumDimension_eq_of_torusStratum_eq σ.representative θ
    (σ.carrier_eq.symm.trans hθ)

/-- The dimension is the dimension in an actual local quotient chart at
every point of the stratum. -/
theorem BoundaryTorusStratum.local_chart (σ : T.BoundaryTorusStratum)
    {p : CharacterTorus n} (hp : p ∈ σ.val) :
    ∃ (x : Ambient n) (U : Set (Ambient n)),
      characterTorusProjection n x = p ∧ IsOpen U ∧ x ∈ U ∧
      Topology.IsOpenEmbedding (U.domRestrict (characterTorusProjection n)) ∧
      (characterTorusProjection n ⁻¹' σ.val) ∩ U =
        T.boundaryThomsenStratum (dotProductEquiv ℝ (Fin n) x) ∩ U ∧
      Module.finrank ℝ (affineSpan ℝ
        (T.boundaryThomsenStratum (dotProductEquiv ℝ (Fin n) x) ∩ U)).direction =
          σ.dimension := by
  obtain ⟨A, hA⟩ := exists_isAmpleModule_of_isProjectiveOver (X := X.left) k
  obtain ⟨F, e, ht⟩ := T.exists_fan_of_ordinaryAmple A.obj
    ((isInvertibleModule_iff_standard A.obj).mpr A.property) hA
  have hτ : σ.val = F.torusStratum σ.representative :=
    σ.carrier_eq.trans (T.boundaryTorusStratum_presentation F e ht σ.representative)
  let τ : F.TorusStratum := ⟨σ.val, σ.representative, hτ⟩
  obtain ⟨x, U, hxp, hU, hx, hinj, hcell, hdim⟩ := τ.local_chart hp
  refine ⟨x, U, hxp, hU, hx, hinj, ?_, ?_⟩
  · simpa only [T.boundaryThomsenStratum_presentation F e ht] using hcell
  · rw [T.boundaryThomsenStratum_presentation F e ht]
    refine hdim.trans ?_
    rw [τ.dimension_eq σ.representative hτ]
    exact (T.boundaryThomsenStratumDimension_presentation F e ht σ.representative).symm

/-- The positive Thomsen divisor exists with its exact ceiling coefficients
at every original prime divisor; no Cartier existence witness is assumed. -/
theorem exists_positiveThomsenCartier (θ : Module.Dual ℝ (Ambient n)) :
    ∃ D : CartierData X.left,
      T.HasBoundaryCoefficients D (fun v => ⌈θ (embed n v)⌉) := by
  obtain ⟨A, hA⟩ := exists_isAmpleModule_of_isProjectiveOver (X := X.left) k
  obtain ⟨F, e, ht⟩ := T.exists_fan_of_ordinaryAmple A.obj
    ((isInvertibleModule_iff_standard A.obj).mpr A.property) hA
  exact T.exists_boundaryCartier_of_presentation F e ht _

/-- All lifts of a single torus stratum give isomorphic original positive
Thomsen sheaves. Thus the divisor representative in the final result does
not restrict or alter the class attached to the stratum. -/
theorem positiveThomsenSheaf_same_stratum
    (θ φ : Module.Dual ℝ (Ambient n))
    (h : T.boundaryTorusStratum θ = T.boundaryTorusStratum φ)
    (D E : CartierData X.left)
    (hD : T.HasBoundaryCoefficients D (fun v => ⌈θ (embed n v)⌉))
    (hE : T.HasBoundaryCoefficients E (fun v => ⌈φ (embed n v)⌉)) :
    Nonempty (D.sheaf ≅ E.sheaf) := by
  obtain ⟨A, hA⟩ := exists_isAmpleModule_of_isProjectiveOver (X := X.left) k
  obtain ⟨F, e, ht⟩ := T.exists_fan_of_ordinaryAmple A.obj
    ((isInvertibleModule_iff_standard A.obj).mpr A.property) hA
  have hF : F.torusStratum θ = F.torusStratum φ := by
    rwa [T.boundaryTorusStratum_presentation F e ht θ,
      T.boundaryTorusStratum_presentation F e ht φ] at h
  obtain ⟨J⟩ := F.thomsenCartier_same_torusStratum k θ φ hF
  exact ⟨T.boundaryCartierPresentationSheafIso F e ht D (F.thomsenCoefficients θ) hD ≪≫
    (Scheme.Modules.pullback e.inv.left).mapIso J ≪≫
    (T.boundaryCartierPresentationSheafIso F e ht E (F.thomsenCoefficients φ) hE).symm⟩

/-- Corollary 6.9 for every positive Thomsen Cartier representative on the
original variety and every independently supplied invariant integral curve. -/
theorem corollary_6_9_original_degree
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = T.unitBoundaryDivisorPolytope)
    (θ : Module.Dual ℝ (Ambient n))
    (D : CartierData X.left)
    (hD : T.HasBoundaryCoefficients D (fun v => ⌈θ (embed n v)⌉))
    (C : InvariantIntegralCurve k n X) :
    ∃ d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d ∧
      d ≤ (T.boundaryThomsenStratumDimension θ : ℤ) := by
  obtain ⟨A, hA⟩ := exists_isAmpleModule_of_isProjectiveOver (X := X.left) k
  obtain ⟨F, e, ht⟩ := T.exists_fan_of_ordinaryAmple A.obj
    ((isInvertibleModule_iff_standard A.obj).mpr A.property) hA
  letI : IsIntegral (F.fanSchemeOver k).left :=
    inferInstanceAs (IsIntegral (F.fanScheme k))
  letI : IsSeparated (F.fanSchemeOver k).hom := by
    rw [← e.hom.w]
    infer_instance
  letI : LocallyOfFiniteType (F.fanSchemeStructureMap k) :=
    (Unimodular.NefBig.fanScheme_finiteType F k).1
  letI : IsLocallyNoetherian (F.fanSchemeOver k).left :=
    LocallyOfFiniteType.isLocallyNoetherian (F.fanSchemeStructureMap k)
  let hinv := (F.intrinsicToricEmbedding k).torus_preserving_inverse T e ht
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) e.inv :=
    T.isModHom_of_torusPreserving (F.intrinsicToricEmbedding k) e.inv hinv
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) e.symm.hom := by
    change IsModHom (splitTorusOver k (Fin n → ℤ)) e.inv
    infer_instance
  have hQF : Q.carrier = F.fanPolytope (fun _ => (1 : ℝ)) :=
    hanti.trans (T.unitBoundaryDivisorPolytope_presentation F e ht)
  obtain ⟨d, hd, hbound⟩ :=
    F.corollary_6_9_anticanonical_degree k Q hQ hQF θ (C.mapIso e.symm)
  let E : (Scheme.Modules.pullback C.inclusion.left).obj D.sheaf ≅
      (Scheme.Modules.pullback (C.mapIso e.symm).inclusion.left).obj
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf :=
    (Scheme.Modules.pullback C.inclusion.left).mapIso
      (T.boundaryCartierPresentationSheafIso F e ht D
        (F.thomsenCoefficients θ) hD) ≪≫
      (Scheme.Modules.pullbackComp C.inclusion.left e.inv.left).app
        (F.fanCartierData k F.isPure (F.thomsenCoefficients θ)).sheaf
  refine ⟨d, (rationalCurveHasDegree_iso k E d).mpr hd, ?_⟩
  rwa [T.boundaryThomsenStratumDimension_presentation F e ht θ]

/-- The representative-free form of Corollary 6.9 quantifies the actual
strata in the original real torus, not a chosen fan or a chosen cell list. -/
theorem corollary_6_9_original_torusStrata
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = T.unitBoundaryDivisorPolytope)
    (σ : T.BoundaryTorusStratum) :
    ∃ D : CartierData X.left,
      T.HasBoundaryCoefficients D (fun v => ⌈σ.representative (embed n v)⌉) ∧
      ∀ C : InvariantIntegralCurve k n X,
        ∃ d : ℤ, RationalCurveHasDegree k
          ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d ∧
          d ≤ (σ.dimension : ℤ) := by
  obtain ⟨D, hD⟩ := T.exists_positiveThomsenCartier σ.representative
  refine ⟨D, hD, ?_⟩
  intro C
  exact T.corollary_6_9_original_degree Q hQ hanti σ.representative D hD C

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.boundaryThomsenStratum_presentation
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_positiveThomsenCartier
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.corollary_6_9_original_degree
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.corollary_6_9_original_torusStrata
