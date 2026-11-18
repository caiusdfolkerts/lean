module

public import ToricPower.CartierMeetDerivedCech
public import ToricPower.AffineSectionsColimits
public import ToricPower.ComplexDiagramEquivalence
public import ToricPower.LinearHomComplexCoproducts
public import ToricPower.ProjectiveCochainBounds
public import ToricPower.FiniteDiagramSyzygies
public import ToricPower.FiniteDiagramCoproductCompact
public import ToricPower.CoproductCompactFunctor
public import ToricPower.CechPosetContraction

/-!
# Arbitrary coproducts in the actual finite Cartier Čech complex

Affine sections and inverse Cartier tensoring preserve actual small
colimits. The constant-chart resolution has finitely many finite
projective terms. Its signed Hom functor therefore preserves arbitrary
coproducts of unrestricted coefficient complexes, with every label map.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite CochainComplex

namespace ToricPower

section Postcompose

universe u v u' v' w z
variable {L : Type*} [Category* L]
  {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
  {ι : Type*} {shape : ComplexShape ι}
  {J : Type w} [Category.{z} J]
  [HasColimitsOfShape J A] [HasColimitsOfShape J D]

instance complexDiagramPostcompose_preservesColimitsOfShape
    (F : HomologicalComplex A shape ⥤ HomologicalComplex D shape)
    [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J (complexDiagramPostcompose (L := L) F) := by
  change PreservesColimitsOfShape J
    ((complexDiagramEquivalence (L := L) (C := A) shape).functor ⋙
      (Functor.whiskeringRight L _ _).obj F ⋙
        (complexDiagramEquivalence (L := L) (C := D) shape).inverse)
  infer_instance

end Postcompose

section Sections

variable (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))]
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)
  (affine : ∀ b, IsAffineOpen (opens.obj b))

include affine in
theorem quasicoherentMeetSections_preservesColimits :
    PreservesColimitsOfSize.{0,0} (FiniteCech.quasicoherentMeetSections k X opens) := by
  apply preservesColimits_of_evaluation
  intro b
  rw [FiniteCech.quasicoherentMeetSections_evaluation]
  exact affineBaseSections_preservesColimits k X (opens.obj b.unop) (affine _)

variable [IsIntegral X] {L : Type} [Category.{0} L]
  (labels : Lᵒᵖ ⥤ CartierSources X)

include affine in
theorem cartierMeetSectionsDiagram_preservesColimits :
    PreservesColimitsOfSize.{0,0} (cartierMeetSectionsDiagram k X labels opens) := by
  letI := quasicoherentMeetSections_preservesColimits k X opens affine
  apply preservesColimits_of_evaluation
  intro l
  rw [cartierMeetSectionsDiagram_evaluation]
  infer_instance

end Sections

namespace FiniteCech

variable (k : Type) [Field k] {B : Type} [SemilatticeInf B] [Fintype B]

/-- The actual chart-resolution terms are finite-dimensional at every chart. -/
theorem finiteTupleResolution_term_finite (m : ℕ) (b : Bᵒᵖ) :
    FiniteDimensional k (((finiteTupleResolution k (B := B)).complex.X m).obj b) := by
  letI (c : Bᵒᵖ) : FiniteDimensional k (((tupleAugmented k (B := B)).right).obj c) := by
    change FiniteDimensional k (PUnit →₀ k)
    infer_instance
  exact Cellular.diagramProjectiveTerm_finite k (tupleAugmented k).right m b

theorem finiteTupleCochain_finiteSupport (q : ℤ)
    (outside : q ∉ Finset.Icc (-(Fintype.card B : ℤ)) 0) :
    IsZero ((projectiveCochain (finiteTupleResolution k (B := B))).X q) := by
  let P := finiteTupleResolution k (B := B)
  letI := projectiveCochain_isStrictlyGE P (Fintype.card B)
    (finiteTupleResolution_isZero_of_card_lt k)
  by_cases low : q < -(Fintype.card B : ℤ)
  · exact (projectiveCochain P).isZero_of_isStrictlyGE (-(Fintype.card B : ℤ)) q low
  · have high : 0 < q := by
      simp only [Finset.mem_Icc] at outside
      omega
    exact (projectiveCochain P).isZero_of_isStrictlyLE 0 q high

theorem finiteTupleCochain_term_compact (q : ℤ)
    (inside : q ∈ Finset.Icc (-(Fintype.card B : ℤ)) 0) :
    CompactExtraction.CoproductCompact
      ((projectiveCochain (finiteTupleResolution k (B := B))).X q) := by
  have nonpositive : q ≤ 0 := (Finset.mem_Icc.mp inside).2
  let m : ℕ := (-q).toNat
  let P := finiteTupleResolution k (B := B)
  let e := P.complex.extendXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f m = q by dsimp [m]; omega)
  letI (b : Bᵒᵖ) : FiniteDimensional k ((P.complex.X m).obj b) :=
    finiteTupleResolution_term_finite k m b
  exact CompactExtraction.coproductCompact_of_iso e.symm
    (CompactExtraction.finiteDiagram_coproductCompact k (P.complex.X m))

theorem finiteTupleHomComplex_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (linearHomComplexFunctor k (projectiveCochain (finiteTupleResolution k (B := B)))) :=
  linearHomComplexFunctor_preservesCoproducts k
    (projectiveCochain (finiteTupleResolution k (B := B)))
    (Finset.Icc (-(Fintype.card B : ℤ)) 0)
    (finiteTupleCochain_finiteSupport k) (finiteTupleCochain_term_compact k) I

end FiniteCech

variable (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))] [IsIntegral X]
  {L : Type} [Category.{0} L] (labels : Lᵒᵖ ⥤ CartierSources X)
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)
  (affine : ∀ b, IsAffineOpen (opens.obj b))

include affine in
/-- This is the actual full complex functor used by unbounded Cartier
Čech descent, before localization. -/
theorem cartierFiniteMeetComplex_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (diagramProjectiveCoefficientComplexFunctor k
        (cartierMeetSectionsDiagram k X labels opens) (FiniteCech.finiteTupleResolution k)) := by
  letI : Fintype B := Fintype.ofFinite B
  letI := cartierMeetSectionsDiagram_preservesColimits k X opens affine labels
  letI := FiniteCech.finiteTupleHomComplex_preservesCoproducts k (B := B) I
  unfold diagramProjectiveCoefficientComplexFunctor
  infer_instance

end ToricPower
end
