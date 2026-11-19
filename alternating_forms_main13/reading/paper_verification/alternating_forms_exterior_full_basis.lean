module

public import PaperVerification.AlternatingFormsDuality
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-! Integral exterior scalar extension. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def exteriorFullQuotientGrading (f g : ⋀[R]^2 M) :
    TauCeti.InternalGrading R
      (ExteriorAlgebra R M ⧸ (exteriorRelationIdeal f g).restrictScalars R) ℕ :=
  (TauCeti.InternalGrading.ofDecomposition (fun s : ℕ => ⋀[R]^s M)).quotient
    ((exteriorRelationIdeal f g).restrictScalars R)
    (by
      apply (TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff
        (fun s : ℕ => ⋀[R]^s M) ((exteriorRelationIdeal f g).restrictScalars R)).mpr
      exact exteriorRelationIdeal_homogeneous f g)

theorem exteriorFullQuotientGrading_piece (f g : ⋀[R]^2 M) (s : ℕ) :
    (exteriorFullQuotientGrading f g).piece s =
      (exteriorDegreeProjection f g s).range := by
  rw [exteriorFullQuotientGrading, TauCeti.InternalGrading.quotient_piece,
    TauCeti.InternalGrading.ofDecomposition_piece]
  change (⋀[R]^s M).map
      (((exteriorRelationIdeal f g).restrictScalars R).mkQ.restrictScalars R) =
    (((exteriorRelationIdeal f g).restrictScalars R).mkQ.comp
      (Submodule.subtype (⋀[R]^s M))).range
  rw [LinearMap.range_comp, Submodule.range_subtype]
  rfl

def exteriorQuotientDegreeEquivFullPiece (f g : ⋀[R]^2 M) (s : ℕ) :
    ExteriorQuotientDegree f g s ≃ₗ[R] (exteriorFullQuotientGrading f g).piece s :=
  (exteriorQuotientDegreeEquivImage f g s).trans
    (LinearEquiv.ofEq _ _ (exteriorFullQuotientGrading_piece f g s).symm)

@[simp] theorem exteriorQuotientDegreeEquivFullPiece_mk
    (f g : ⋀[R]^2 M) (s : ℕ) (x : ⋀[R]^s M) :
    ((exteriorQuotientDegreeEquivFullPiece f g s (Submodule.Quotient.mk x) :
      (exteriorFullQuotientGrading f g).piece s) :
        ExteriorAlgebra R M ⧸ (exteriorRelationIdeal f g).restrictScalars R) =
      Submodule.Quotient.mk (x : ExteriorAlgebra R M) := by
  rfl

/-- Assemble the full basis in the actual ring quotient by the relation
ideal.  The index records the degree and then the chosen basis index. -/
def exteriorFullBasisOfDegreeBases (f g : ⋀[R]^2 M) {ι : ℕ → Type*}
    (b : ∀ s, Module.Basis (ι s) R (ExteriorQuotientDegree f g s)) :
    Module.Basis (Σ s, ι s) R (ExteriorAlgebra R M ⧸ exteriorRelationIdeal f g) :=
  ((exteriorFullQuotientGrading f g).isInternal.collectedBasis
    (fun s => (b s).map (exteriorQuotientDegreeEquivFullPiece f g s))).map
      (Submodule.Quotient.restrictScalarsEquiv R (exteriorRelationIdeal f g))

theorem exteriorFullBasisOfDegreeBases_apply (f g : ⋀[R]^2 M) {ι : ℕ → Type*}
    (b : ∀ s, Module.Basis (ι s) R (ExteriorQuotientDegree f g s))
    (v : ∀ s, ι s → ⋀[R]^s M)
    (hb : ∀ s i, b s i=Submodule.Quotient.mk (v s i)) (s : ℕ) (i : ι s) :
    exteriorFullBasisOfDegreeBases f g b ⟨s,i⟩ =
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (v s i : ExteriorAlgebra R M) := by
  rw [exteriorFullBasisOfDegreeBases, Module.Basis.map_apply,
    DirectSum.IsInternal.collectedBasis_coe]
  change (Submodule.Quotient.restrictScalarsEquiv R (exteriorRelationIdeal f g))
    ((exteriorQuotientDegreeEquivFullPiece f g s (b s i) :
      (exteriorFullQuotientGrading f g).piece s) :
        ExteriorAlgebra R M ⧸ (exteriorRelationIdeal f g).restrictScalars R) = _
  rw [hb, exteriorQuotientDegreeEquivFullPiece_mk]
  rfl

end PaperVerification.AlternatingForms
