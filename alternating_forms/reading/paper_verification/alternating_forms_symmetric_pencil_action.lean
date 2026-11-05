module

public import PaperVerification.AlternatingFormsSymmetricPencil
public import PaperVerification.AlternatingFormsBigradedPieces
import Lean.Elab.Tactic.Omega

/-!
# The compatible group action on the original exterior quotient

The action is induced from the original vector space through the exterior
algebra functor.  Preservation of the generated ideal is proved from the
covariance of its two displayed generators.  Commutation with scaling the
`a`-span proves preservation of every original bidegree component.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.SymmetricPencil

section General

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem degreeRelations_map_le_of_span (f g : ⋀[K]^2 M) (L : M →ₗ[K] M)
    (hf : exteriorPower.map 2 L f ∈ Submodule.span K ({f,g} : Set (⋀[K]^2 M)))
    (hg : exteriorPower.map 2 L g ∈ Submodule.span K ({f,g} : Set (⋀[K]^2 M)))
    (s : ℕ) : exteriorDegreeRelations f g s ≤
      (exteriorDegreeRelations f g s).comap (exteriorPower.map s L) := by
  have h : exteriorRelationIdeal f g ≤
      (exteriorRelationIdeal f g).comap (ExteriorAlgebra.map L) := by
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · have hh := quadraticSpan_le_exteriorDegreeRelations f g hf
      change (exteriorPower.map 2 L f : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g at hh
      change ExteriorAlgebra.map L (f : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g
      rw [exteriorPower.coe_map] at hh
      exact hh
    · have hh := quadraticSpan_le_exteriorDegreeRelations f g hg
      change (exteriorPower.map 2 L g : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g at hh
      change ExteriorAlgebra.map L (g : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g
      rw [exteriorPower.coe_map] at hh
      exact hh
  intro x hx
  change exteriorPower.map s L x ∈ exteriorDegreeRelations f g s
  change (exteriorPower.map s L x : ExteriorAlgebra K M) ∈ exteriorRelationIdeal f g
  rw [exteriorPower.coe_map]
  exact h hx

end General

section OriginalAction

variable (K : Type) [Field K]

abbrev Coordinates (t : ℕ) := Fin (2*(t+1)+1) → K

def coordinateEquiv (t : ℕ) : Coordinates K t ≃ₗ[K] Model K t :=
  standardBasisEquiv (modelBasis K t)

/-- The actual original vector representation, obtained by the displayed
monomial-basis coordinate change. -/
def coordinateRepresentation (t : ℕ) :
    Representation K (GL (Fin 2) K) (Coordinates K t) where
  toFun g := (coordinateEquiv K t).symm.toLinearMap ∘ₗ
    modelRepresentation K t g ∘ₗ (coordinateEquiv K t).toLinearMap
  map_one' := by
    ext x
    simp only [map_one, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    ext x
    simp only [map_mul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.End.mul_apply, LinearEquiv.apply_symm_apply]

@[simp] theorem coordinateRepresentation_equiv (t : ℕ) (g : GL (Fin 2) K)
    (x : Coordinates K t) :
    coordinateEquiv K t (coordinateRepresentation K t g x) =
      modelRepresentation K t g (coordinateEquiv K t x) := by
  change coordinateEquiv K t ((coordinateEquiv K t).symm _) = _
  exact (coordinateEquiv K t).apply_symm_apply _

def coordinateRepresentationEquiv (t : ℕ) :
    (coordinateRepresentation K t).Equiv (modelRepresentation K t) :=
  .mk (coordinateEquiv K t) (fun g => by
    apply LinearMap.ext
    intro x
    exact coordinateRepresentation_equiv K t g x)

theorem coordinate_exterior_intertwining (t s : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map s (coordinateEquiv K t).toLinearMap ∘ₗ
        exteriorPower.map s (coordinateRepresentation K t g) =
      exteriorPower.map s (modelRepresentation K t g) ∘ₗ
        exteriorPower.map s (coordinateEquiv K t).toLinearMap := by
  rw [← exteriorPower.map_comp, ← exteriorPower.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact coordinateRepresentation_equiv K t g x

theorem pencil_decompose (t : ℕ) (u : Standard K) :
    pencil K t u = u 0 • (-oddPathFirstQuadratic (modelBasis K t)) +
      u 1 • oddPathSecondQuadratic (modelBasis K t) := by
  have hu : u = u 0 • Pi.basisFun K (Fin 2) 0 + u 1 • Pi.basisFun K (Fin 2) 1 := by
    simpa only [Fin.sum_univ_two, Pi.basisFun_repr] using
      ((Pi.basisFun K (Fin 2)).sum_repr u).symm
  conv_lhs => rw [hu]
  rw [map_add, map_smul, map_smul, pencil_zero_eq_path, pencil_one_eq_path]

theorem model_first_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (modelRepresentation K t g)
      (oddPathFirstQuadratic (modelBasis K t)) =
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 • oddPathFirstQuadratic (modelBasis K t) -
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 • oddPathSecondQuadratic (modelBasis K t) := by
  have h := pencil_equivariant K t g (Pi.basisFun K (Fin 2) 0)
  rw [pencil_zero_eq_path, Representation.exteriorPower_apply, map_neg,
    pencil_decompose] at h
  simp only [TauCeti.stdRep_apply_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] at h
  have hh := congrArg (fun x : ⋀[K]^2 (Model K t) => -x) h
  simpa only [neg_neg,neg_add,smul_neg,sub_eq_add_neg] using hh

theorem model_second_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (modelRepresentation K t g)
      (oddPathSecondQuadratic (modelBasis K t)) =
    -(g : Matrix (Fin 2) (Fin 2) K) 0 1 • oddPathFirstQuadratic (modelBasis K t) +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 • oddPathSecondQuadratic (modelBasis K t) := by
  have h := pencil_equivariant K t g (Pi.basisFun K (Fin 2) 1)
  rw [pencil_one_eq_path, Representation.exteriorPower_apply, pencil_decompose] at h
  simp only [TauCeti.stdRep_apply_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply,smul_neg] at h
  exact h.trans (congrArg
    (fun x : ⋀[K]^2 (Model K t) =>
      x+(g : Matrix (Fin 2) (Fin 2) K) 1 1 • oddPathSecondQuadratic (modelBasis K t))
    (neg_smul ((g : Matrix (Fin 2) (Fin 2) K) 0 1)
      (oddPathFirstQuadratic (modelBasis K t))).symm)

theorem coordinate_first_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (coordinateRepresentation K t g)
      (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) =
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 •
        oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) -
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 •
        oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) := by
  apply (exteriorPowerLinearEquiv (coordinateEquiv K t) 2).injective
  change exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _ =
    exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _
  rw [← LinearMap.comp_apply, coordinate_exterior_intertwining,
    LinearMap.comp_apply, map_sub, map_smul, map_smul]
  simpa only [coordinateEquiv, oddPathFirstQuadratic_standardBasisEquiv,
    oddPathSecondQuadratic_standardBasisEquiv] using model_first_covariance K t g

theorem coordinate_second_covariance (t : ℕ) (g : GL (Fin 2) K) :
    exteriorPower.map 2 (coordinateRepresentation K t g)
      (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) =
    -(g : Matrix (Fin 2) (Fin 2) K) 0 1 •
        oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 •
        oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))) := by
  apply (exteriorPowerLinearEquiv (coordinateEquiv K t) 2).injective
  change exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _ =
    exteriorPower.map 2 (coordinateEquiv K t).toLinearMap _
  rw [← LinearMap.comp_apply, coordinate_exterior_intertwining,
    LinearMap.comp_apply, map_add, map_smul, map_smul]
  simpa only [coordinateEquiv, oddPathFirstQuadratic_standardBasisEquiv,
    oddPathSecondQuadratic_standardBasisEquiv] using model_second_covariance K t g

theorem original_relations_invariant (t s : ℕ) (g : GL (Fin 2) K) :
    exteriorDegreeRelations
        (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))))
        (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) s ≤
      (exteriorDegreeRelations
        (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*(t+1)+1))))
        (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*(t+1)+1)))) s).comap
        (exteriorPower.map s (coordinateRepresentation K t g)) := by
  apply degreeRelations_map_le_of_span
  · rw [coordinate_first_covariance]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [coordinate_second_covariance]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The representation on the genuine quotient by both original quadrics. -/
def quotientRepresentation (t s : ℕ) :
    Representation K (GL (Fin 2) K) (OddExteriorQuotientDegree (K := K) (t+1) s) :=
  ((coordinateRepresentation K t).exteriorPower s).quotient _
    (by
      intro g
      simpa only [Representation.exteriorPower_apply] using original_relations_invariant K t s g)

@[simp] theorem quotientRepresentation_mk (t s : ℕ) (g : GL (Fin 2) K)
    (x : ⋀[K]^s (Coordinates K t)) :
    quotientRepresentation K t s g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (exteriorPower.map s (coordinateRepresentation K t g) x) := by
  simp only [quotientRepresentation,Representation.quotient_apply,Submodule.mapQ_apply,
    Representation.exteriorPower_apply]

def modelScaling (t : ℕ) (c : K) : Module.End K (Model K t) :=
  (c • LinearMap.id).prodMap LinearMap.id

theorem coordinateEquiv_scaling (t : ℕ) (c : K) :
    (coordinateEquiv K t).toLinearMap ∘ₗ Bidegree.oddScaling (t+1) c =
      modelScaling K t c ∘ₗ (coordinateEquiv K t).toLinearMap := by
  apply (Pi.basisFun K (Fin (2*(t+1)+1))).ext
  intro j
  obtain ⟨j, rfl⟩ := (TopInterlacing.abIndex (t+1)).surjective j
  cases j with
  | inl i =>
      have ha : Bidegree.aIndexDegree ((TopInterlacing.abIndex (t+1)) (Sum.inl i)) = 1 := by
        simp only [Bidegree.aIndexDegree, TopInterlacing.abIndex]
        have h : (2*i.val+1)%2=1 := by omega
        simp [h]
      simp only [LinearMap.comp_apply, Bidegree.oddScaling, Bidegree.basisScaling_basis,
        ha, pow_one, LinearEquiv.coe_coe, map_smul, coordinateEquiv,
        standardBasisEquiv_basisFun]
      have hi : (TopInterlacing.abIndex (t+1)) (Sum.inl i)=oddPathMiddle i := by
        apply Fin.ext
        rfl
      rw [hi]
      simp [modelBasis_middle,modelScaling]
  | inr i =>
      have ha : Bidegree.aIndexDegree ((TopInterlacing.abIndex (t+1)) (Sum.inr i)) = 0 := by
        simp only [Bidegree.aIndexDegree, TopInterlacing.abIndex]
        have h : (2*i.val)%2≠1 := by omega
        simp [h]
      simp only [LinearMap.comp_apply, Bidegree.oddScaling, Bidegree.basisScaling_basis,
        ha, pow_zero, one_smul, LinearEquiv.coe_coe, coordinateEquiv,
        standardBasisEquiv_basisFun]
      simp [modelBasis, modelScaling, Module.Basis.prod_apply]

theorem coordinate_scaling_commute (t : ℕ) (c : K) (g : GL (Fin 2) K) :
    Bidegree.oddScaling (t+1) c ∘ₗ coordinateRepresentation K t g =
      coordinateRepresentation K t g ∘ₗ Bidegree.oddScaling (t+1) c := by
  apply LinearMap.ext
  intro x
  apply (coordinateEquiv K t).injective
  have hs := LinearMap.congr_fun (coordinateEquiv_scaling K t c)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hs
  simp only [LinearMap.comp_apply]
  rw [hs, coordinateRepresentation_equiv, coordinateRepresentation_equiv, hs]
  change modelScaling K t c (modelRepresentation K t g _) =
    modelRepresentation K t g (modelScaling K t c _)
  simp [modelScaling, modelRepresentation, Representation.prod, map_smul]

theorem quotient_scaling_commute (t s : ℕ) (c : K) (g : GL (Fin 2) K) :
    Bidegree.quotientScaling (t+1) s c ∘ₗ quotientRepresentation K t s g =
      quotientRepresentation K t s g ∘ₗ Bidegree.quotientScaling (t+1) s c := by
  apply Submodule.quot_hom_ext
  intro x
  simp only [LinearMap.comp_apply, quotientRepresentation_mk,
    Bidegree.quotientScaling, Submodule.mapQ_apply]
  congr 1
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    coordinate_scaling_commute, exteriorPower.map_comp, LinearMap.comp_apply]

end OriginalAction

section BigradedAction

variable (K : Type) [Field K] [CharZero K]

theorem quotientScaling_piece (k s p : ℕ)
    (x : OddExteriorQuotientDegree (K := K) k s)
    (hx : x ∈ Bidegree.quotientASubdegree k s p) (c : K) :
    Bidegree.quotientScaling k s c x = c^p • x := by
  rw [Bidegree.quotientASubdegree_eq_basisPiece, BasisDegree.piece_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨I, hI, rfl⟩ := hx
      rw [Bidegree.quotientScaling_goodBasis, hI]
  | zero => rw [map_zero,smul_zero]
  | add x y hx hy hx' hy' => rw [map_add,hx',hy',smul_add]
  | smul a x hx hx' => rw [map_smul,hx',smul_comm]

theorem bigradedPiece_invariant (t p q : ℕ) (g : GL (Fin 2) K) :
    Bidegree.actualBigradedPiece (K := K) (t+1) p q ≤
      (Bidegree.actualBigradedPiece (K := K) (t+1) p q).comap
        (quotientRepresentation K t (p+q) g) := by
  intro x hx
  change quotientRepresentation K t (p+q) g x ∈ Bidegree.quotientASubdegree _ _ _
  rw [Bidegree.quotientASubdegree_eq_basisPiece, BasisDegree.mem_piece]
  intro I hI
  apply Bidegree.eigenvector_coordinate_zero (oddExteriorBasis (t+1) (p+q))
    (Bidegree.quotientScaling (t+1) (p+q) (2 : K))
    (fun J => (2 : K)^Bidegree.goodADegree J)
    (Bidegree.quotientScaling_goodBasis (t+1) (p+q) 2) ((2 : K)^p)
    (quotientRepresentation K t (p+q) g x) ?_ I
    (fun h => hI (Bidegree.two_pow_injective h))
  rw [← LinearMap.comp_apply, quotient_scaling_commute, LinearMap.comp_apply,
    quotientScaling_piece K (t+1) (p+q) p x hx 2, map_smul]

/-- The compatible action on the paper's original `(p,q)` quotient piece.
Its carrier remains the independently defined image of the original words. -/
def bigradedRepresentation (t p q : ℕ) :
    Representation K (GL (Fin 2) K)
      (Bidegree.actualBigradedPiece (K := K) (t+1) p q) :=
  (quotientRepresentation K t (p+q)).subrepresentation _
    (bigradedPiece_invariant K t p q)

end BigradedAction
end PaperVerification.AlternatingForms.SymmetricPencil
