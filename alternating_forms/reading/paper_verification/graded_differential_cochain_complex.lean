module

public import PaperVerification.SquareZeroHomologyGrading
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Actual cochain cohomology of a graded square-zero differential

A homogeneous differential of degree one defines an ordinary integer-indexed
cochain complex with term `G.piece q` in degree `q`. Its categorical homology
is canonically equivalent to the degree-`q` piece of the inherited global
kernel/image quotient. The boundary comparison uses homogeneous projection
of a genuine boundary preimage, so no degreewise exactness is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.GradedDifferentialCochainComplex

open CategoryTheory
open SquareZeroHomologyConjugacy SquareZeroHomologyGrading

variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]
  (G : TauCeti.InternalGrading R A) (D : A →ₗ[R] A)
  (hD : D.comp D = 0)
  (hd : TauCeti.LinearMap.IsHomogeneous D G.piece G.piece 1)

/-- The original differential restricted to two consecutive pieces. -/
def pieceMap (p q : ℤ) (hpq : p + 1 = q) : G.piece p →ₗ[R] G.piece q :=
  (D.comp (G.piece p).subtype).codRestrict _ (fun x ↦ by
    change D x.val ∈ G.piece q
    simpa only [hpq] using hd x.property)

@[simp] theorem pieceMap_apply_val (p q : ℤ) (hpq : p + 1 = q) (x : G.piece p) :
    (pieceMap G D hd p q hpq x).val = D x.val := rfl

include hD in
/-- Consecutive restrictions retain the original square-zero identity. -/
theorem pieceMap_comp (p q r : ℤ) (hpq : p + 1 = q) (hqr : q + 1 = r) :
    (pieceMap G D hd q r hqr).comp (pieceMap G D hd p q hpq) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun hD x.val

/-- The honest integer-indexed cochain complex of original homogeneous
pieces and the original restricted differential. -/
def cochainComplex : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (G.piece q))
    (fun q ↦ ModuleCat.ofHom (pieceMap G D hd q (q + 1) rfl))
    (fun q ↦ ModuleCat.hom_ext (pieceMap_comp G D hD hd q (q + 1) (q + 1 + 1) rfl rfl))

/-- The three original homogeneous pieces around one cohomological degree. -/
def degreeShortComplex (q : ℤ) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (pieceMap G D hd (q - 1) q (sub_add_cancel q 1))
    (pieceMap G D hd q (q + 1) rfl)
    (pieceMap_comp G D hD hd (q - 1) q (q + 1) (sub_add_cancel q 1) rfl)

/-- A degreewise cycle is an actual global cycle with the same underlying
element of the original module. -/
def cycleEmbedding (q : ℤ) :
    LinearMap.ker (pieceMap G D hd q (q + 1) rfl) →ₗ[R] LinearMap.ker D where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Sending a homogeneous cycle to its original global homology class. -/
def cycleComparison (q : ℤ) :
    LinearMap.ker (pieceMap G D hd q (q + 1) rfl) →ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  (((LinearMap.range (complex D hD).moduleCatToCycles).mkQ).comp
    (cycleEmbedding G D hd q)).codRestrict _ (fun x ↦
      mk_mem_homologyGrading G D hD hd x.val.property)

/-- Every homogeneous global homology class has a homogeneous cycle
representative, and therefore comes from the degreewise complex. -/
theorem cycleComparison_surjective (q : ℤ) :
    Function.Surjective (cycleComparison G D hD hd q) := by
  intro z
  obtain ⟨x, hx, hclass⟩ := (mem_homologyGrading_iff G D hD hd).1 z.property
  refine ⟨⟨⟨x.val, hx⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    exact x.property
  · apply Subtype.ext
    exact hclass

/-- Global and degreewise boundaries agree. In the forward implication,
project a global boundary preimage to degree `q - 1`. -/
theorem cycleComparison_ker (q : ℤ) :
    LinearMap.ker (cycleComparison G D hD hd q) =
      LinearMap.range (degreeShortComplex G D hD hd q).moduleCatToCycles := by
  ext x
  constructor
  · intro hx
    change cycleComparison G D hD hd q x = 0 at hx
    have hz := congrArg Subtype.val hx
    change (Submodule.Quotient.mk (cycleEmbedding G D hd q x) :
      LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) = 0 at hz
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hz
    have ha' : D a = x.val.val := congrArg Subtype.val ha
    refine ⟨DirectSum.decompose G.piece a (q - 1), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hp := hd.map_decompose (q - 1) a
    rw [sub_add_cancel, ha', DirectSum.decompose_of_mem_same G.piece x.val.property] at hp
    exact hp
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a.val, rfl⟩

/-- The explicit kernel/image quotient of the degreewise complex is the
actual homogeneous component of the global kernel/image quotient. -/
def quotientHomologyEquiv (q : ℤ) :
    (LinearMap.ker (pieceMap G D hd q (q + 1) rfl) ⧸
      LinearMap.range (degreeShortComplex G D hD hd q).moduleCatToCycles) ≃ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  (Submodule.quotEquivOfEq _ _ (cycleComparison_ker G D hD hd q).symm).trans
    ((cycleComparison G D hD hd q).quotKerEquivOfSurjective
      (cycleComparison_surjective G D hD hd q))

/-- The degreewise quotient comparison sends each cycle to its original
homology class. -/
@[simp] theorem quotientHomologyEquiv_mk (q : ℤ)
    (x : LinearMap.ker (pieceMap G D hd q (q + 1) rfl)) :
    quotientHomologyEquiv G D hD hd q (Submodule.Quotient.mk x) =
      cycleComparison G D hD hd q x := by
  rfl

/-- The actual categorical homology of the degreewise short complex. -/
def shortComplexHomologyEquiv (q : ℤ) :
    (degreeShortComplex G D hD hd q).homology ≃ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  (degreeShortComplex G D hD hd q).moduleCatHomologyIso.toLinearEquiv.trans
    (quotientHomologyEquiv G D hD hd q)

/-- Reindexing a homogeneous submodule changes no underlying element. -/
theorem eqToHom_piece_val {p q : ℤ} (hpq : p = q) (x : G.piece p) :
    ((eqToHom (congrArg (fun r ↦ ModuleCat.of R (G.piece r)) hpq)) x : G.piece q).val =
      x.val := by
  subst q
  rfl

/-- The restricted three-term complex is the corresponding part of the
actual integer-indexed cochain complex. -/
def cochainShortComplexIso (q : ℤ) :
    (cochainComplex G D hD hd).sc' (q - 1) q (q + 1) ≅
      degreeShortComplex G D hD hd q := by
  dsimp only [cochainComplex, degreeShortComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor',
    ShortComplex.moduleCatMk]
  refine ShortComplex.isoMk
    (Iso.refl (ModuleCat.of R (G.piece (q - 1))))
    (Iso.refl (ModuleCat.of R (G.piece q)))
    (Iso.refl (ModuleCat.of R (G.piece (q + 1)))) ?_ ?_
  · simp only [Category.comp_id, Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [CochainComplex.of.d, pieceMap]
    exact (eqToHom_piece_val G (sub_add_cancel q 1)
      (pieceMap G D hd (q - 1) (q - 1 + 1) rfl x)).symm
  · simp [CochainComplex.of_d]

/-- Actual cochain cohomology in every integer degree is the corresponding
piece of the inherited global kernel/image quotient. -/
def cochainHomologyEquiv (q : ℤ) :
    (cochainComplex G D hD hd).homology q ≃ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  ((cochainComplex G D hD hd).homologyIsoSc' (q - 1) q (q + 1)
    ((ComplexShape.up ℤ).prev_eq' (by exact sub_add_cancel q 1))
    ((ComplexShape.up ℤ).next_eq' rfl)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (cochainShortComplexIso G D hD hd q)).toLinearEquiv.trans
      (shortComplexHomologyEquiv G D hD hd q))

end PaperVerification.GradedDifferentialCochainComplex
