module

public import Continuation.Runtime.EquivarianceFromDenseTorus
public import Continuation.Runtime.IntrinsicBoundaryCartier
public import Continuation.Runtime.IntrinsicFanPresentation
public import Continuation.Divisor.AffineSectionAmpleness
public import Continuation.Runtime.NonvanishingPullback
public import Continuation.Geometry.NefIsoTransport
public import Continuation.Divisor.PositiveThomsenLiteral
public import Continuation.Divisor.StrictSupportAffineCover

/-!
# Proposition 6.3 on an independently specified complete toric variety

The positive Thomsen divisor is specified by the ceiling of each original
boundary valuation.  Its existence is derived from the unconditional fan
presentation of the original smooth complete toric scheme.  Equality of its
actual Weil coefficients proves independence from every Cartier representative
and every recovered fan presentation.

Nefness below is the ordinary degree condition on all proper integral closed
curves of the original scheme.  The Fano conclusion concerns the actual dual
of its top Kähler sheaf; its projective embedding and anticanonical polytope
are also transported to the original scheme and character lattice.

This is a source candidate. Its complete dependency chain still requires
native checking; the theorem names do not constitute a verification receipt.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes
open TauCeti.AlgebraicGeometry Unimodular.NefBig
open scoped Classical

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance originalThomsenLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- The literal Weil coefficients of the positive Thomsen divisor. The real
character is an arbitrary integral-linear functional on the original
cocharacter lattice. No fan or positivity certificate enters this definition. -/
def positiveBoundaryCoefficients (θ : Lattice n →ₗ[ℤ] ℝ) : X.left → ℤ :=
  T.boundaryCoefficient (Unimodular.Thomsen.positiveCoefficients θ)

theorem positiveBoundaryCoefficients_apply (θ : Lattice n →ₗ[ℤ] ℝ) (x : X.left) :
    T.positiveBoundaryCoefficients θ x =
      if Order.coheight x = 1 ∧ x ∈ T.boundary then
        ⌈θ (T.valuationVector x)⌉ else 0 := rfl

/-- Every prescribed integral invariant boundary divisor is Cartier on the
original smooth complete variety. A fan is constructed inside the proof. -/
theorem exists_complete_boundaryCartier (a : Lattice n → ℤ) :
    ∃ D : CartierData X.left, T.HasBoundaryCoefficients D a := by
  obtain ⟨F, e, ht, _, _⟩ := T.exists_equivariant_fan_of_complete
  exact T.exists_boundaryCartier_of_presentation F e ht a

/-- A Cartier representative of the independently specified positive Thomsen
divisor. Its actual Weil coefficients, rather than this choice, characterize it. -/
def positiveBoundaryCartier (θ : Lattice n →ₗ[ℤ] ℝ) : CartierData X.left :=
  (T.exists_complete_boundaryCartier (Unimodular.Thomsen.positiveCoefficients θ)).choose

theorem positiveBoundaryCartier_hasCoefficients (θ : Lattice n →ₗ[ℤ] ℝ) :
    T.HasBoundaryCoefficients (T.positiveBoundaryCartier θ)
      (Unimodular.Thomsen.positiveCoefficients θ) :=
  (T.exists_complete_boundaryCartier (Unimodular.Thomsen.positiveCoefficients θ)).choose_spec

theorem positiveBoundaryCartier_weilCoefficient (θ : Lattice n →ₗ[ℤ] ℝ) :
    (T.positiveBoundaryCartier θ).weilCoefficient = T.positiveBoundaryCoefficients θ :=
  T.positiveBoundaryCartier_hasCoefficients θ

/-- The ordinary positive Thomsen line bundle on the original scheme. -/
def positiveBoundaryLineBundle (θ : Lattice n →ₗ[ℤ] ℝ) : InvertibleSheaf X.left :=
  cartierInvertibleSheaf (T.positiveBoundaryCartier θ)

/-- Any actual Cartier divisor with the same original ceiling coefficients
has this same ordinary line bundle. -/
def positiveBoundaryLineBundle_iso_of_coefficients
    (θ : Lattice n →ₗ[ℤ] ℝ) (D : CartierData X.left)
    (hD : T.HasBoundaryCoefficients D (Unimodular.Thomsen.positiveCoefficients θ)) :
    D.sheaf ≅ (T.positiveBoundaryLineBundle θ).obj :=
  (HasBoundaryCoefficients.unique T hD (T.positiveBoundaryCartier_hasCoefficients θ)).choose

/-- Quantifying over the chosen representatives is exactly quantifying over
every original Cartier representative with the required boundary coefficients. -/
theorem all_positiveBoundary_nef_iff_all_representatives :
    (∀ θ : Lattice n →ₗ[ℤ] ℝ,
      IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj) ↔
    ∀ (θ : Lattice n →ₗ[ℤ] ℝ) (D : CartierData X.left),
      T.HasBoundaryCoefficients D (Unimodular.Thomsen.positiveCoefficients θ) →
      IsNef (baseField := k) (cartierInvertibleSheaf D).obj := by
  constructor
  · intro h θ D hD
    exact IsNef.of_iso (T.positiveBoundaryLineBundle_iso_of_coefficients θ D hD).symm
      (h θ)
  · intro h θ
    exact h θ (T.positiveBoundaryCartier θ) (T.positiveBoundaryCartier_hasCoefficients θ)

section Presentation

variable (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X)
    (ht : (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus)

/-- The original divisor sheaf is the genuine inverse pullback of the fan
divisor sheaf, with equality of all actual boundary coefficients proved. -/
def positiveBoundaryLineBundle_presentationIso (θ : Lattice n →ₗ[ℤ] ℝ) :
    (T.positiveBoundaryLineBundle θ).obj ≅
      ((InvertibleSheaf.pullback e.inv.left).obj
        (Unimodular.Thomsen.positiveThomsenLineBundle F k θ)).obj :=
  T.boundaryCartierPresentationSheafIso F e ht (T.positiveBoundaryCartier θ)
    (Unimodular.Thomsen.positiveCoefficients θ) (T.positiveBoundaryCartier_hasCoefficients θ)

include e ht in
/-- Ordinary nefness transports along the actual scheme isomorphism. The
same proper integral curve and its residue-weighted degree are used. -/
theorem positiveBoundaryLineBundle_isNef_iff (θ : Lattice n →ₗ[ℤ] ℝ) :
    IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj ↔
      IsNef (baseField := k) (Unimodular.Thomsen.positiveThomsenLineBundle F k θ).obj := by
  let E : X.left ≅ F.fanScheme k := (Over.forget _).mapIso e.symm
  letI : E.hom.IsOver (Spec (CommRingCat.of k)) := ⟨e.inv.w⟩
  exact (AlgebraicGeometry.isNef_iff_of_iso
    (T.positiveBoundaryLineBundle_presentationIso F e ht θ)).trans
      (isNef_pullback_schemeIso_iff k E
        (Unimodular.Thomsen.positiveThomsenLineBundle F k θ))

include e ht in
/-- The coordinate criterion agrees with original-variety nefness for
every actual torus-preserving fan presentation, not merely a chosen one. -/
theorem all_positiveBoundary_nef_iff_positiveCriterion :
    (∀ θ : Lattice n →ₗ[ℤ] ℝ,
      IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj) ↔
      Unimodular.ConeBases.PositiveCriterion
        (Unimodular.FanInterfaces.dictionaryToricFan F) := by
  constructor
  · intro h
    apply (Unimodular.Thomsen.proposition_6_3_positiveThomsen_iff F k).mp
    intro θ
    exact (T.positiveBoundaryLineBundle_isNef_iff F e ht θ).mp (h θ)
  · intro h θ
    apply (T.positiveBoundaryLineBundle_isNef_iff F e ht θ).mpr
    exact (Unimodular.Thomsen.proposition_6_3_positiveThomsen_iff F k).mpr h θ

include e ht in
/-- The negative-mass condition concerns every genuine normalized wall
relation of any actual presentation of the original variety. -/
theorem all_positiveBoundary_nef_iff_normalizedWalls :
    (∀ θ : Lattice n →ₗ[ℤ] ℝ,
      IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj) ↔
      F.AllNormalizedWallsNegativeMass :=
  (T.all_positiveBoundary_nef_iff_positiveCriterion F e ht).trans
    F.normalizedWallCriterion_iff_positiveCriterion.symm

include e in
/-- A strict integral support gives an ample unit-boundary sheaf after
transport to the unchanged original scheme. The last isomorphism identifies
it with the dual of the original top Kähler differential sheaf. -/
theorem originalAnticanonical_isAmple_of_strictSupport
    (ha : F.IsStrictSupport (fun _ => ((1 : ℤ) : ℝ))) :
    IsAmpleModule (topDifferentialSheaf k X.left n).dual := by
  let L := cocycleInvertibleSheaf (F.fanCartierCocycle k F.isPure (fun _ => (1 : ℤ)))
  let M := (InvertibleSheaf.pullback e.inv.left).obj L
  have hM : IsAmpleModule M.obj := by
    apply isAmpleModule_of_affine_nonvanishing_cover M
      (QuasiCompact.compactSpace_of_compactSpace X.hom)
    intro x
    obtain ⟨s, hx, hs⟩ := F.fanCartier_affine_nonvanishing_cover_of_strictSupport
      k (fun _ => (1 : ℤ)) ha (e.inv.left x)
    let t : Γ(M.obj, ⊤) := e.inv.left.pullbackSectionsLE L.obj ⊤ ⊤ (by simp) s
    have hopen : M.obj.nonvanishingLocus t = e.inv.left ⁻¹ᵁ L.obj.nonvanishingLocus s := by
      change ((Scheme.Modules.pullback e.inv.left).obj L.obj).nonvanishingLocus
        (e.inv.left.pullbackSectionsLE L.obj ⊤ ⊤ (by simp) s) = _
      rw [nonvanishingLocus_pullbackSectionsLE]
      simp only [top_inf_eq]
    refine ⟨t, ?_, ?_⟩
    · rw [hopen]
      exact hx
    · rw [hopen]
      exact hs.preimage e.inv.left
  let J : M.obj ≅ (topDifferentialSheaf k X.left n).dual :=
    (Scheme.Modules.pullback e.inv.left).mapIso (anticanonical_unitBoundaryIso F k).symm ≪≫
      fanAnticanonicalPullbackIso F k e.inv.left
  exact isAmpleModule_of_iso J hM

end Presentation

/-- Changing the representative in the real character torus by an integral
character changes the literal ceiling divisor by a principal divisor. This
is an isomorphism of the actual sheaves on the unchanged original variety. -/
def positiveBoundaryLineBundle_iso_of_integralTranslation
    (θ φ : Lattice n →ₗ[ℤ] ℝ) (m : Lattice n)
    (h : ∀ v, φ v = θ v + (integerPairing v m : ℝ)) :
    (T.positiveBoundaryLineBundle θ).obj ≅
      (T.positiveBoundaryLineBundle φ).obj := by
  apply Nonempty.some
  obtain ⟨F, e, ht, _, _⟩ := T.exists_equivariant_fan_of_complete
  have hF : (Unimodular.Thomsen.positiveThomsenLineBundle F k θ).obj ≅
      (Unimodular.Thomsen.positiveThomsenLineBundle F k φ).obj := by
    apply Nonempty.some
    apply F.fanCartierData_characterTranslation k F.isPure
      (Unimodular.Thomsen.positiveCoefficients θ)
      (Unimodular.Thomsen.positiveCoefficients φ) (-m)
    intro v hv
    change ⌈φ v⌉ = ⌈θ v⌉ - integerPairing v (-m)
    rw [h v, Int.ceil_add_intCast]
    simp only [integerPairing, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, sub_neg_eq_add]
  exact ⟨T.positiveBoundaryLineBundle_presentationIso F e ht θ ≪≫
    (Scheme.Modules.pullback e.inv.left).mapIso hF ≪≫
      (T.positiveBoundaryLineBundle_presentationIso F e ht φ).symm⟩

/-- Ordinary nefness is independent of the lift of the character-torus
point. Thus the all-real-character statement tests exactly its classes. -/
theorem positiveBoundaryLineBundle_isNef_iff_integralTranslation
    (θ φ : Lattice n →ₗ[ℤ] ℝ) (m : Lattice n)
    (h : ∀ v, φ v = θ v + (integerPairing v m : ℝ)) :
    IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj ↔
      IsNef (baseField := k) (T.positiveBoundaryLineBundle φ).obj :=
  AlgebraicGeometry.isNef_iff_of_iso
    (T.positiveBoundaryLineBundle_iso_of_integralTranslation θ φ m h)

/-- Proposition 6.3 for an independently specified smooth complete toric
variety. The fan and its torus-preserving isomorphism are conclusions; neither
projectivity nor an ample line bundle is assumed. -/
theorem proposition_6_3_original_criteria :
    ∃ (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X),
      (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus ∧
      ((∀ θ : Lattice n →ₗ[ℤ] ℝ,
        IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj) ↔
        Unimodular.ConeBases.PositiveCriterion
          (Unimodular.FanInterfaces.dictionaryToricFan F)) ∧
      ((∀ θ : Lattice n →ₗ[ℤ] ℝ,
        IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj) ↔
        F.AllNormalizedWallsNegativeMass) := by
  obtain ⟨F, e, ht, _, _⟩ := T.exists_equivariant_fan_of_complete
  exact ⟨F, e, ht, T.all_positiveBoundary_nef_iff_positiveCriterion F e ht,
    T.all_positiveBoundary_nef_iff_normalizedWalls F e ht⟩

/-- The Fano consequence is on the original scheme: its actual intrinsic
anticanonical sheaf is ample, its dimension is the torus rank, and an actual
closed immersion over the field into finite projective space is exhibited. -/
theorem positiveBoundary_nef_implies_original_fano
    (hn : ∀ θ : Lattice n →ₗ[ℤ] ℝ,
      IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj) :
    IsAmpleModule (topDifferentialSheaf k X.left n).dual ∧
      topologicalKrullDim X.left = n ∧
      ∃ (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X)
        (ha : F.IsStrictSupport (fun _ => ((1 : ℤ) : ℝ))),
        (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus ∧
        IsClosedImmersion (e.inv.left ≫
          Unimodular.Projectivity.strictSupportProjectiveEmbedding F (fun _ => 1) ha k) ∧
        (e.inv.left ≫
          Unimodular.Projectivity.strictSupportProjectiveEmbedding F (fun _ => 1) ha k) ≫
            Unimodular.Projectivity.polynomialProjectiveToSpec k
              (Unimodular.Projectivity.WeightIndex.{u} (F := F)) = X.hom := by
  obtain ⟨F, e, ht, _, _⟩ := T.exists_equivariant_fan_of_complete
  have hnF : ∀ θ : Lattice n →ₗ[ℤ] ℝ,
      IsNef (baseField := k) (Unimodular.Thomsen.positiveThomsenLineBundle F k θ).obj :=
    fun θ => (T.positiveBoundaryLineBundle_isNef_iff F e ht θ).mp (hn θ)
  obtain ⟨_, _, hdim, _, ha, hclosed, hbase⟩ :=
    Unimodular.Thomsen.positiveThomsen_nef_implies_smooth_projective_fano F k hnF
  letI : IsClosedImmersion
      (Unimodular.Projectivity.strictSupportProjectiveEmbedding F (fun _ => 1) ha k) := hclosed
  refine ⟨originalAnticanonical_isAmple_of_strictSupport F e ha, ?_, F, e, ha, ht,
    inferInstance, ?_⟩
  · exact e.inv.left.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans hdim
  · rw [Category.assoc, hbase]
    exact e.inv.w

/-- The deeply monotone polytope is the literal anticanonical section
polytope of the original scheme. Its outward normals are exactly the
negatives of all original boundary valuation vectors. -/
theorem positiveBoundary_nef_implies_original_deeplyMonotone
    (hn : ∀ θ : Lattice n →ₗ[ℤ] ℝ,
      IsNef (baseField := k) (T.positiveBoundaryLineBundle θ).obj) :
    ∃ Q : Unimodular.SmoothReflexivePresentation n,
      Q.carrier = T.unitBoundaryDivisorPolytope ∧ Q.DeeplyMonotone ∧
      (Q.normals : Set (Lattice n)) = Neg.neg '' T.completeBoundaryRaySet := by
  obtain ⟨F, e, ht, _, _⟩ := T.exists_equivariant_fan_of_complete
  have hnF : ∀ θ : Lattice n →ₗ[ℤ] ℝ,
      IsNef (baseField := k) (Unimodular.Thomsen.positiveThomsenLineBundle F k θ).obj :=
    fun θ => (T.positiveBoundaryLineBundle_isNef_iff F e ht θ).mp (hn θ)
  obtain ⟨Q, hQ, hdeep, hnormals⟩ :=
    Unimodular.Thomsen.positiveThomsen_nef_implies_literal_anticanonical_polytope F k hnF
  refine ⟨Q, hQ.trans (T.unitBoundaryDivisorPolytope_presentation F e ht).symm,
    hdeep, ?_⟩
  rw [hnormals, T.completeBoundaryRaySet_presentation F e ht]
  exact Finset.coe_image

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.positiveBoundaryCartier_weilCoefficient
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.all_positiveBoundary_nef_iff_all_representatives
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.proposition_6_3_original_criteria
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.positiveBoundary_nef_implies_original_fano
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.positiveBoundary_nef_implies_original_deeplyMonotone
