module
public import Mathlib

/-! Multiplication on the weight-graded relative Koszul complexes. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open scoped BigOperators DirectSum
universe u v w
open Classical Finset MvPolynomial CategoryTheory
set_option backward.isDefEq.respectTransparency false
section
open Category Limits Module ExteriorAlgebra
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)
noncomputable def koszulComplex.dAlternating (n : ℕ) : M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M := AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))
noncomputable def koszulComplex.d (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M := exteriorPower.alternatingMapLinearEquiv (koszulComplex.dAlternating φ n)
lemma koszulComplex.d_comp_eq_zero (n : ℕ) : koszulComplex.d φ n ∘ₗ koszulComplex.d φ (n + 1) = 0 := by sorry
noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ := ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulComplex.d φ n))
    (fun n ↦ by rw [← ModuleCat.ofHom_comp, koszulComplex.d_comp_eq_zero, ModuleCat.ofHom_zero])
end
namespace CommAlg.Koszul
open TensorProduct
variable {R : Type u} {V : Type} [CommRing R] [Fintype V] [LinearOrder V]
abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ℕ := (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj
  M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex (Fintype.linearCombination R x))
def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)
def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  let δ : (familyCoefficientComplex.{u} x M).X (i + 1) →ₗ[R]
      (familyCoefficientComplex.{u} x M).X i := ((familyCoefficientComplex.{u} x M).d (i + 1) i).hom
  (coefficientCoordinates.{u} x M i).toLinearMap.comp
    (δ.comp (coefficientCoordinates.{u} x M (i + 1)).symm.toLinearMap)
end CommAlg.Koszul
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop := ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
def faceVertices (p : P) : Finset P := univ.filter fun a => IsAtom a ∧ a ≤ p
@[simp] theorem mem_faceVertices {p a : P} :
    a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by sorry
theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by sorry
theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P) (hsu : s ⊆ faceVertices p) : ∃! x : Set.Iic p, faceVertices x.val = s := by sorry
def faceRank (p : P) : ℕ := (faceVertices p).card
end
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
structure ModuleDiagram where
  obj : P → Type w
  [addCommGroup : ∀ p, AddCommGroup (obj p)]
  [module : ∀ p, Module K (obj p)]
  res : ∀ {p q}, q ≤ p → obj p →ₗ[K] obj q
  res_refl : ∀ p x, res (le_refl p) x = x
  res_comp : ∀ {p q r} (hqp : q ≤ p) (hrq : r ≤ q) x, res hrq (res hqp x) = res (hrq.trans hqp) x
attribute [instance] ModuleDiagram.addCommGroup ModuleDiagram.module
end FourPapers.Universal
namespace FourPapers.Universal.ModuleDiagram
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable (D : ModuleDiagram K P)
def sections : Submodule K (∀ p, D.obj p) where
  carrier := {x | ∀ p q (h : q ≤ p), D.res h (x p) = x q}
  zero_mem' := by intros; simp
  add_mem' := by
    intro x y hx hy p q h
    simpa using congrArg₂ (· + ·) (hx p q h) (hy p q h)
  smul_mem' := by
    intro c x hx p q h
    simpa using congrArg (c • ·) (hx p q h)
end FourPapers.Universal.ModuleDiagram
namespace FourPapers.Universal
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
structure CoherentEquiv (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p ≃ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x, E.res h (component p x) = component q (D.res h x)
end FourPapers.Universal
namespace FourPapers.Universal.CoherentEquiv
variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]
variable {K P}
variable {D E F : ModuleDiagram K P}
def symm (e : CoherentEquiv D E) : CoherentEquiv E D where
  component p := (e.component p).symm
  naturality p q h x := by
    apply (e.component q).injective
    simpa using (e.naturality p q h ((e.component p).symm x)).symm
def trans (e : CoherentEquiv D E) (f : CoherentEquiv E F) : CoherentEquiv D F where
  component p := (e.component p).trans (f.component p)
  naturality p q h x := by
    change F.res h (f.component p (e.component p x)) = f.component q (e.component q (D.res h x))
    rw [f.naturality, e.naturality]
def sectionEquiv (e : CoherentEquiv D E) : D.sections ≃ₗ[K] E.sections where
  toFun x := ⟨fun p => e.component p (x.val p), by
    intro p q h
    rw [e.naturality, x.property p q h]⟩
  invFun x := ⟨fun p => (e.component p).symm (x.val p), by
    intro p q h
    change D.res h (e.symm.component p (x.val p)) = e.symm.component q (x.val q)
    exact (e.symm.naturality p q h (x.val p)).trans
      (congrArg (e.symm.component q) (x.property p q h))⟩
  left_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).symm_apply_apply (x.val p)
  right_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).apply_symm_apply (x.val p)
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (e.component p) (x.val p) (y.val p)
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (e.component p) c (x.val p)
end FourPapers.Universal.CoherentEquiv
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
section
variable (K : Type*) [CommRing K]
abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}
def faceVertexInclusion {p q : P} (hqp : q ≤ p) : FaceVertex q ↪ FaceVertex p where
  toFun a := ⟨a.val, a.property.1, a.property.2.trans hqp⟩
  inj' _ _ h := Subtype.ext (congrArg (fun a : FaceVertex p => a.val) h)
abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K
def polynomialRestriction {p q : P} (hqp : q ≤ p) :
    PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0
theorem polynomialRestriction_refl (p : P) : polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by sorry
theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) : (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) = polynomialRestriction K
  (hrq.trans hqp) := by sorry
abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f
def polynomialParameter (p : P) (i : ℕ) : PolynomialStalk K p := MvPolynomial.esymm (FaceVertex p) K i
end
abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}
def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w) : P := ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
  (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val
def IsMinimalCommonUpper (p q w : P) : Prop := p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w
def minimalCommonUppers (p q : P) : Finset P := univ.filter (IsMinimalCommonUpper p q)
variable (K : Type*) [CommRing K]
abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K
def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩
def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) := {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w), f = faceSymbol K p * faceSymbol K q -
  faceSymbol K (faceMeetBelow hs p q w hpw hqw) * ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨ (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧ f = faceSymbol K p * faceSymbol K q)}
def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) := Ideal.span (faceRelations K hs)
abbrev FaceRing (hs : IsSimplicialPoset P) := FacePolynomial (P := P) K ⧸ faceIdeal K hs
def barycentricIdeal : Ideal (FacePolynomial (P := P) K) := Ideal.span {f | ∃ p q : NonzeroFace P, ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}
abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K
def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs := Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
def barycentricGenerator (p : P) : BarycentricRing (P := P) K := Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs := ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K := ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p
def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) : MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs := MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)
def barycentricParameterAction (d : ℕ) : MvPolynomial (Fin d) K →ₐ[K] BarycentricRing (P := P) K := MvPolynomial.aeval fun i => barycentricRankParameter K (i.val + 1)
end
section
variable {V : Type*} [Fintype V]
def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K]
def stalkVertexSet (p q : P) : Finset (FaceVertex p) := univ.filter fun a => a.val ≤ q
@[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by sorry
def faceProduct (p q : P) : PolynomialStalk K p := ∏ a ∈ stalkVertexSet p q, X a
def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0
def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r := MvPolynomial.aeval fun p => faceValue K r p.val
theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P) {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) : faceEvaluation K r f = 0 := by sorry
def faceRingEvaluation (hs : IsSimplicialPoset P) (r : P) :
    FaceRing K hs →ₐ[K] PolynomialStalk K r := Ideal.Quotient.liftₐ (faceIdeal K hs) (faceEvaluation K r) (by
    change faceIdeal K hs ≤ RingHom.ker (faceEvaluation K r).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    exact faceEvaluation_relation K hs r hf)
end
section
variable {V K : Type*} [CommRing K]
def IsDivisorClosed (P : (V →₀ ℕ) → Prop) : Prop := ∀ ⦃a b⦄, a ≤ b → P b → P a
def forbiddenIdeal (P : (V →₀ ℕ) → Prop) : Ideal (MvPolynomial V K) := Ideal.span ((fun a : V →₀ ℕ => MvPolynomial.monomial a (1 : K)) '' {a | ¬ P a})
abbrev MonomialQuotient (P : (V →₀ ℕ) → Prop) := MvPolynomial V K ⧸ forbiddenIdeal P
def standardCoefficients (P : (V →₀ ℕ) → Prop) : MvPolynomial V K →ₗ[K] ({a // P a} →₀ K) := (Finsupp.lsubtypeDomain {a | P a}).comp (MvPolynomial.basisMonomials V
  K).repr.toLinearMap
lemma standardCoefficients_surjective (P : (V →₀ ℕ) → Prop) : Function.Surjective (standardCoefficients (K := K) P) := by sorry
lemma standardCoefficients_ker (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) : LinearMap.ker (standardCoefficients (K := K) P) = (forbiddenIdeal P).restrictScalars K := by
  sorry
def standardMonomialEquiv (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) : MonomialQuotient (K := K) P ≃ₗ[K] ({a // P a} →₀ K) := (Submodule.quotEquivOfEq _ _
  (standardCoefficients_ker (K := K) P hP).symm).trans ((standardCoefficients (K := K) P).quotKerEquivOfSurjective (standardCoefficients_surjective (K := K) P))
def standardMonomialBasis (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) : Module.Basis {a // P a} K (MonomialQuotient (K := K) P) := (Finsupp.basisSingleOne).map
  (standardMonomialEquiv P hP).symm
end
section
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}
def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop := ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val
theorem isChainExponent_divisorClosed : IsDivisorClosed (IsChainExponent (V := V)) := by sorry
abbrev BooleanBarycentricRing (V K : Type*) [Fintype V] [DecidableEq V] [CommRing K] := MonomialQuotient (K := K) (IsChainExponent (V := V))
def booleanChainBasis : Module.Basis {a : BooleanFace V →₀ ℕ // IsChainExponent a} K (BooleanBarycentricRing V K) := standardMonomialBasis IsChainExponent
  isChainExponent_divisorClosed
def faceVariable (F : BooleanFace V) : BooleanBarycentricRing V K := Ideal.Quotient.mk (forbiddenIdeal (K := K) IsChainExponent) (MvPolynomial.X F)
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) : Set.Iic p := (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose
theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P) (s : Finset (FaceVertex p)) : stalkVertexSet p (subfaceOfVertexSet hs p s).val = s := by sorry
def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) :
    BooleanFace (FaceVertex p) ↪ NonzeroFace P where
  toFun F := ⟨(subfaceOfVertexSet hs p F.val).val, by
    intro hbot
    have he := stalkVertexSet_subfaceOfVertexSet hs p F.val
    rw [hbot, stalkVertexSet_bot] at he
    exact F.property.ne_empty he.symm⟩
  inj' F G h := by
    apply Subtype.ext
    have he : (subfaceOfVertexSet hs p F.val).val = (subfaceOfVertexSet hs p G.val).val := congrArg (fun z : NonzeroFace P => z.val) h
    have hv := congrArg (stalkVertexSet p) he
    simpa only [stalkVertexSet_subfaceOfVertexSet] using hv
theorem booleanFaceInclusion_le (hs : IsSimplicialPoset P) (p : P) (F : BooleanFace (FaceVertex p)) : (booleanFaceInclusion hs p F).val ≤ p := by sorry
section
variable (K : Type*) [CommRing K]
def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop := ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val
theorem barycentricAllowed_divisorClosed : IsDivisorClosed (BarycentricAllowed (P := P)) := by sorry
theorem barycentricIdeal_eq_forbiddenIdeal : barycentricIdeal (P := P) K = forbiddenIdeal (K := K) (BarycentricAllowed (P := P)) := by sorry
end
abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] := {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}
def standardCarrier (a : StandardFaceIndex P) : P :=
  if h : a.val.support.Nonempty then
    (Finset.exists_max_image a.val.support (fun p : NonzeroFace P => faceRank p.val) h).choose.val
  else ⊥
theorem standardCarrier_le_iff (hs : IsSimplicialPoset P) (a : StandardFaceIndex P) (p : P) : standardCarrier a ≤ p ↔ ∀ q ∈ a.val.support, q.val ≤ p := by sorry
theorem booleanFaceInclusion_range_iff (hs : IsSimplicialPoset P) (p : P) (q : NonzeroFace P) : q ∈ Set.range (booleanFaceInclusion hs p) ↔ q.val ≤ p := by sorry
theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) : BarycentricAllowed
  (a.mapDomain (booleanFaceInclusion hs p)) := by sorry
theorem chainExponent_comap_booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) {a : NonzeroFace P →₀ ℕ} (ha : BarycentricAllowed a) : IsChainExponent (a.comapDomain
  (booleanFaceInclusion hs p) (booleanFaceInclusion hs p).injective.injOn) := by sorry
abbrev StandardInside (p : P) := {a : StandardFaceIndex P // standardCarrier a ≤ p}
def standardInsideEquiv (hs : IsSimplicialPoset P) (p : P) :
    {a : BooleanFace (FaceVertex p) →₀ ℕ // IsChainExponent a} ≃ StandardInside p where
  toFun a := ⟨⟨a.val.mapDomain (booleanFaceInclusion hs p), standardExponent_map_booleanFaceInclusion hs p a.property⟩, by
      apply (standardCarrier_le_iff hs _ p).mpr
      intro q hq
      rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
      exact booleanFaceInclusion_le hs p F⟩
  invFun a := ⟨a.val.val.comapDomain (booleanFaceInclusion hs p)
    (booleanFaceInclusion hs p).injective.injOn, chainExponent_comap_booleanFaceInclusion hs p a.val.property⟩
  left_inv a := Subtype.ext
    (Finsupp.comapDomain_mapDomain _ (booleanFaceInclusion hs p).injective a.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.mapDomain_comapDomain _ (booleanFaceInclusion hs p).injective
    intro q hq
    exact (booleanFaceInclusion_range_iff hs p q).mpr
      ((standardCarrier_le_iff hs a.val p).mp a.property q hq)
end
section
variable {V W K : Type*} [CommRing K]
theorem killCompl_mem_forbiddenIdeal (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q) (allowed : ∀ a, Q a → P
  (a.mapDomain e)) {f : MvPolynomial W K} (hf : f ∈ forbiddenIdeal P) : MvPolynomial.killCompl e.injective f ∈ forbiddenIdeal Q := by sorry
def monomialRestriction
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e)) :
    MonomialQuotient (K := K) P →ₐ[K] MonomialQuotient (K := K) Q := Ideal.Quotient.liftₐ (forbiddenIdeal P)
    ((Ideal.Quotient.mkₐ K (forbiddenIdeal Q)).comp
      (MvPolynomial.killCompl e.injective)) (by
        intro f hf
        change Ideal.Quotient.mk (forbiddenIdeal Q)
          (MvPolynomial.killCompl e.injective f) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (killCompl_mem_forbiddenIdeal e P Q hP hQ allowed hf))
end
section
variable {U V W K : Type*}
  [Fintype U] [Fintype V] [Fintype W]
  [DecidableEq U] [DecidableEq V] [DecidableEq W] [CommRing K]
def booleanFaceEmbedding (e : V ↪ W) : BooleanFace V ↪ BooleanFace W where
  toFun F := ⟨F.val.map e, F.property.map (f := e)⟩
  inj' F G h := Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))
theorem isChainExponent_map_booleanFaceEmbedding (e : V ↪ W) {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) : IsChainExponent (a.mapDomain (booleanFaceEmbedding e)) := by
  sorry
def booleanRestriction (e : V ↪ W) : BooleanBarycentricRing W K →ₐ[K] BooleanBarycentricRing V K := monomialRestriction (booleanFaceEmbedding e) IsChainExponent
  IsChainExponent isChainExponent_divisorClosed isChainExponent_divisorClosed (fun _ ha => isChainExponent_map_booleanFaceEmbedding e ha)
theorem booleanRestriction_refl : booleanRestriction (K := K) (Function.Embedding.refl V) = AlgHom.id K (BooleanBarycentricRing V K) := by sorry
theorem booleanRestriction_comp (e : U ↪ V) (f : V ↪ W) : (booleanRestriction (K := K) e).comp (booleanRestriction f) = booleanRestriction (e.trans f) := by sorry
def booleanRankParameter (r : ℕ) : BooleanBarycentricRing V K := ∑ F : BooleanFace V, if F.val.card = r then faceVariable F else 0
end
section
variable {P I : Type*} [Preorder P] (K : Type*) [CommRing K] (carrier : I → P)
def coefficientStalk (p : P) : Submodule K (I →₀ K) := Finsupp.supported K K {i | carrier i ≤ p}
def coefficientRestriction {p q : P} (_hqp : q ≤ p) : coefficientStalk K carrier p →ₗ[K] coefficientStalk K carrier q := (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp
  (coefficientStalk K carrier p).subtype
@[simp] theorem coefficientRestriction_apply {p q : P} (hqp : q ≤ p)
    (x : coefficientStalk K carrier p) (i : I) :
    (coefficientRestriction K carrier hqp x).val i = if carrier i ≤ q then x.val i else 0 := by sorry
abbrev coefficientDiagram : ModuleDiagram K P where
  obj p := coefficientStalk K carrier p
  res h := coefficientRestriction K carrier h
  res_refl p x := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ p
    · simp [hi]
    · have hx := (Finsupp.mem_supported' K x.val).mp x.property i hi
      simp [hi, hx]
  res_comp := by
    intro p q r hqp hrq x
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ r
    · have hiq := hi.trans hrq
      simp [hi, hiq]
    · simp [hi]
def coefficientSection : (I →₀ K) →ₗ[K] (coefficientDiagram K carrier).sections where
  toFun x := ⟨fun p => Finsupp.restrictDom K K {i | carrier i ≤ p} x, by
    intro p q hqp
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change (if carrier i ≤ q then (if carrier i ≤ p then x i else 0) else 0) = (if carrier i ≤ q then x i else 0)
    by_cases hi : carrier i ≤ q
    · have hip := hi.trans hqp
      simp [hi, hip]
    · simp [hi]⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (Finsupp.restrictDom K K {i | carrier i ≤ p}) x y
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (Finsupp.restrictDom K K {i | carrier i ≤ p}) c x
def coefficientAtCarrier (x : (coefficientDiagram K carrier).sections) (i : I) : K := (x.val (carrier i)).val i
variable [Fintype P]
def coefficientAssembly (x : (coefficientDiagram K carrier).sections) : I →₀ K :=
  Finsupp.onFinset (Finset.univ.biUnion fun p => (x.val p).val.support)
    (coefficientAtCarrier K carrier x) (by
      intro i hi
      apply Finset.mem_biUnion.mpr
      exact ⟨carrier i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hi⟩)
theorem coefficientAssembly_section (x : I →₀ K) : coefficientAssembly K carrier (coefficientSection K carrier x) = x := by sorry
theorem coefficientSection_assembly (x : (coefficientDiagram K carrier).sections) : coefficientSection K carrier (coefficientAssembly K carrier x) = x := by sorry
def coefficientSectionEquiv : (I →₀ K) ≃ₗ[K] (coefficientDiagram K carrier).sections where
  toFun := coefficientSection K carrier
  invFun := coefficientAssembly K carrier
  left_inv := coefficientAssembly_section K carrier
  right_inv := coefficientSection_assembly K carrier
  map_add' := (coefficientSection K carrier).map_add
  map_smul' := (coefficientSection K carrier).map_smul
def sectionsFromCoherentCoefficients (D : ModuleDiagram K P) (e : CoherentEquiv D (coefficientDiagram K carrier)) : D.sections ≃ₗ[K] (I →₀ K) := e.sectionEquiv.trans
  (coefficientSectionEquiv K carrier).symm
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
section
variable (K : Type*) [CommRing K]
@[simp] theorem faceVertexInclusion_refl (p : P) :
    faceVertexInclusion (le_refl p) = Function.Embedding.refl (FaceVertex p) := by sorry
@[simp] theorem faceVertexInclusion_trans {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (faceVertexInclusion hrq).trans (faceVertexInclusion hqp) = faceVertexInclusion (hrq.trans hqp) := by sorry
abbrev BarycentricStalk (p : P) := BooleanBarycentricRing (FaceVertex p) K
abbrev barycentricDiagram : ModuleDiagram K P where
  obj p := BarycentricStalk K p
  res h := (booleanRestriction (K := K) (faceVertexInclusion h)).toLinearMap
  res_refl p x := by
    change booleanRestriction (K := K) (faceVertexInclusion (le_refl p)) x = x
    rw [faceVertexInclusion_refl, booleanRestriction_refl]
    rfl
  res_comp hqp hrq x := by
    change booleanRestriction (K := K) (faceVertexInclusion hrq)
      (booleanRestriction (faceVertexInclusion hqp) x) = booleanRestriction (faceVertexInclusion (hrq.trans hqp)) x
    have h := DFunLike.congr_fun
      (booleanRestriction_comp (K := K) (faceVertexInclusion hrq) (faceVertexInclusion hqp)) x
    simpa only [AlgHom.comp_apply, faceVertexInclusion_trans] using h
variable (hs : IsSimplicialPoset P)
def barycentricStalkStandardBasis (p : P) : Module.Basis (StandardInside p) K (BarycentricStalk K p) := (booleanChainBasis (V := FaceVertex p) (K := K)).reindex
  (standardInsideEquiv hs p)
def barycentricStandardCoordinates (p : P) : BarycentricStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p := (barycentricStalkStandardBasis K hs p).repr.trans
  (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm
theorem barycentricStandardCoordinates_naturality {p q : P} (hqp : q ≤ p) (x : BarycentricStalk K p) : coefficientRestriction K standardCarrier hqp
  (barycentricStandardCoordinates K hs p x) = barycentricStandardCoordinates K hs q (booleanRestriction (K := K) (faceVertexInclusion hqp) x) := by sorry
def barycentricCoefficientEquiv :
    CoherentEquiv (barycentricDiagram (P := P) K)
      (coefficientDiagram K (standardCarrier (P := P))) where
  component := barycentricStandardCoordinates K hs
  naturality p q hqp x := barycentricStandardCoordinates_naturality K hs hqp x
def barycentricSectionCoordinates : (barycentricDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) := sectionsFromCoherentCoefficients K standardCarrier
  (barycentricDiagram K) (barycentricCoefficientEquiv K hs)
end
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def faceRingMonomial (a : NonzeroFace P →₀ ℕ) : FaceRing K hs := Ideal.Quotient.mk (faceIdeal K hs) (monomial a 1)
end
section
variable {V T K : Type*} [Fintype V] [DecidableEq V] [Fintype T] [CommRing K]
def subsetExponent (F : Finset V) : V →₀ ℕ := ∑ v ∈ F, Finsupp.single v 1
end
section
variable {V : Type*} [Fintype V] [LinearOrder V]
def chainVertexMap : (BooleanFace V →₀ ℕ) →ₗ[ℕ] (V →₀ ℕ) := Finsupp.linearCombination ℕ (fun F => subsetExponent F.val)
def vertexHeight (a : V →₀ ℕ) : ℕ := Finset.univ.sup (fun v => a v)
def exponentLayer (a : V →₀ ℕ) (k : Fin (vertexHeight a)) : BooleanFace V := ⟨Finset.univ.filter (fun v => k.val < a v), by
    obtain ⟨v, hv, hkv⟩ := Finset.lt_sup_iff.mp k.isLt
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hkv⟩⟩⟩
def layerExponent (a : V →₀ ℕ) : BooleanFace V →₀ ℕ := ∑ k : Fin (vertexHeight a), Finsupp.single (exponentLayer a k) 1
theorem layerExponent_isChain (a : V →₀ ℕ) : IsChainExponent (layerExponent a) := by sorry
theorem chainVertexMap_layerExponent (a : V →₀ ℕ) : chainVertexMap (layerExponent a) = a := by sorry
theorem chainVertexMap_chain_injective : Function.Injective (fun a : {a : BooleanFace V →₀ ℕ // IsChainExponent a} => chainVertexMap a.val) := by sorry
def chainVertexEquiv : {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃ (V →₀ ℕ) where
  toFun a := chainVertexMap a.val
  invFun a := ⟨layerExponent a, layerExponent_isChain a⟩
  left_inv a := chainVertexMap_chain_injective (chainVertexMap_layerExponent (chainVertexMap a.val))
  right_inv := chainVertexMap_layerExponent
variable {W : Type*} [Fintype W] [DecidableEq W]
def chainVertexEquivUnordered :
    {a : BooleanFace W →₀ ℕ // IsChainExponent a} ≃ (W →₀ ℕ) := by
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  exact chainVertexEquiv
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
section
variable (K : Type*) [CommRing K]
variable {K}
def standardVertexEquiv (hs : IsSimplicialPoset P) (p : P) : StandardInside p ≃ (FaceVertex p →₀ ℕ) := (standardInsideEquiv hs p).symm.trans chainVertexEquivUnordered
def polynomialStandardBasis (hs : IsSimplicialPoset P) (p : P) : Module.Basis (StandardInside p) K (PolynomialStalk K p) := (MvPolynomial.basisMonomials (FaceVertex p)
  K).reindex (standardVertexEquiv hs p).symm
end
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
theorem faceRingEvaluation_naturality {p q : P} (hqp : q ≤ p) (f : FaceRing K hs) : polynomialRestriction K hqp (faceRingEvaluation K hs p f) = faceRingEvaluation K hs q f :=
  by sorry
def faceRingSection : FaceRing K hs →ₗ[K] (polynomialDiagram (P := P) K).sections where
  toFun f := ⟨fun p => faceRingEvaluation K hs p f, fun p q hqp => faceRingEvaluation_naturality K hs hqp f⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    exact map_add (faceRingEvaluation K hs p) f g
  map_smul' c f := by
    apply Subtype.ext
    funext p
    exact map_smul (faceRingEvaluation K hs p) c f
@[simp] theorem faceRingSection_apply (f : FaceRing K hs) (p : P) :
    (faceRingSection K hs f).val p = faceRingEvaluation K hs p f := by sorry
def polynomialStandardCoordinates (p : P) : PolynomialStalk K p ≃ₗ[K] coefficientStalk K (standardCarrier (P := P)) p := (polynomialStandardBasis (K := K) hs p).repr.trans
  (Finsupp.supportedEquivFinsupp {a : StandardFaceIndex P | standardCarrier a ≤ p}).symm
theorem polynomialStandardCoordinates_naturality {p q : P} (hqp : q ≤ p) (f : PolynomialStalk K p) : coefficientRestriction K standardCarrier hqp
  (polynomialStandardCoordinates K hs p f) = polynomialStandardCoordinates K hs q (polynomialRestriction K hqp f) := by sorry
def polynomialCoefficientEquiv :
    CoherentEquiv (polynomialDiagram (P := P) K)
      (coefficientDiagram K (standardCarrier (P := P))) where
  component := polynomialStandardCoordinates K hs
  naturality p q hqp f := polynomialStandardCoordinates_naturality K hs hqp f
def polynomialSectionCoordinates : (polynomialDiagram (P := P) K).sections ≃ₗ[K] (StandardFaceIndex P →₀ K) := sectionsFromCoherentCoefficients K standardCarrier
  (polynomialDiagram K) (polynomialCoefficientEquiv K hs)
def standardFaceCombination : (StandardFaceIndex P →₀ K) →ₗ[K] FaceRing K hs := Finsupp.linearCombination K (fun a => faceRingMonomial K hs a.val)
theorem standardFaceCombination_surjective : Function.Surjective (standardFaceCombination K hs) := by sorry
theorem standardFaceCombination_coefficients (x : StandardFaceIndex P →₀ K) : polynomialSectionCoordinates K hs (faceRingSection K hs (standardFaceCombination K hs x)) = x :=
  by sorry
def standardFaceBasis : Module.Basis (StandardFaceIndex P) K (FaceRing K hs) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (standardFaceCombination K hs)
    ⟨by
      intro x y hxy
      have h := congrArg (fun f => polynomialSectionCoordinates K hs (faceRingSection K hs f)) hxy
      simpa only [standardFaceCombination_coefficients] using h, standardFaceCombination_surjective K hs⟩).symm
def faceRingSectionEquiv : FaceRing K hs ≃ₗ[K] (polynomialDiagram (P := P) K).sections := (standardFaceBasis K hs).repr.trans (polynomialSectionCoordinates K hs).symm
@[simp] theorem faceRingSectionEquiv_apply (f : FaceRing K hs) :
    faceRingSectionEquiv K hs f = faceRingSection K hs f := by sorry
end
section
variable {I K R S : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
structure ParameterEquiv (φ : MvPolynomial I K →ₐ[K] R)
    (ψ : MvPolynomial I K →ₐ[K] S) where
  toLinearEquiv : R ≃ₗ[K] S
  map_X_mul : ∀ i x, toLinearEquiv (φ (X i) * x) = ψ (X i) * toLinearEquiv x
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def standardRankWeight (d : ℕ) (a : StandardFaceIndex P) : ℤ := a.val.sum (fun F n => (n : ℤ) * rankWeight d (faceRank F.val))
def HasStandardLeading (d : ℕ) (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) : Prop := ∀ (a : StandardInside p) (b : StandardFaceIndex P),
    standardRankWeight d a.val ≤ standardRankWeight d b → (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).val b =
      if a.val = b then 1 else 0
def standardOrdinaryDegree (a : StandardFaceIndex P) : ℕ := a.val.sum (fun F n => n * faceRank F.val)
def HasStandardDegree (p : P) (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p) : Prop := ∀ (a : StandardInside p) (b : StandardFaceIndex P), standardOrdinaryDegree b ≠
  standardOrdinaryDegree a.val → (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).val b = 0
theorem exists_graded_coherent_parameter_comparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) : ∃ e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K), ∀ p
  : P, HasStandardLeading K hs d p (e.component p).toLinearMap ∧ (∀ i : ℕ, ∀ x : BarycentricStalk K p, e.component p (booleanRankParameter (i + 1) * x) = polynomialParameter K
  p (i + 1) * e.component p x) ∧ HasStandardDegree K hs p (e.component p).toLinearMap := by sorry
end
section
variable {V W K L : Type*} [CommRing K] [CommRing L] (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) (h : K →+* L)
def monomialCoefficientMap : MonomialQuotient (K := K) P →ₛₗ[h] MonomialQuotient (K := L) P := (standardMonomialEquiv (K := L) P hP).symm.toLinearMap.comp
  ((Finsupp.mapRange.linearMap h.toSemilinearMap).comp (standardMonomialEquiv (K := K) P hP).toLinearMap)
end
section
variable {I J K M N M' N' : Type*} [CommRing K]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
def integralLinearExtension (b : Module.Basis I ℤ M) (b' : Module.Basis I K M') (n : N →ₛₗ[Int.castRingHom K] N') (f : M →ₗ[ℤ] N) : M' →ₗ[K] N' := b'.constr K (fun i => n (f
  (b i)))
@[simp] theorem integralLinearExtension_basis
    (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (n : N →ₛₗ[Int.castRingHom K] N') (f : M →ₗ[ℤ] N) (i : I) :
    integralLinearExtension b b' n f (b' i) = n (f (b i)) := by sorry
theorem integralLinearExtension_commutes (b : Module.Basis I ℤ M) (b' : Module.Basis I K M') (m : M →ₛₗ[Int.castRingHom K] M') (n : N →ₛₗ[Int.castRingHom K] N') (hm : ∀ i, m
  (b i) = b' i) (f : M →ₗ[ℤ] N) (x : M) : integralLinearExtension b b' n f (m x) = n (f x) := by sorry
def integralEquivExtension
    (b : Module.Basis I ℤ M) (b' : Module.Basis I K M')
    (c : Module.Basis J ℤ N) (c' : Module.Basis J K N')
    (m : M →ₛₗ[Int.castRingHom K] M') (n : N →ₛₗ[Int.castRingHom K] N')
    (hm : ∀ i, m (b i) = b' i) (hn : ∀ j, n (c j) = c' j)
    (e : M ≃ₗ[ℤ] N) : M' ≃ₗ[K] N' := by
  let f := integralLinearExtension b b' n e.toLinearMap
  let g := integralLinearExtension c c' m e.symm.toLinearMap
  have hgf : g.comp f = LinearMap.id := by
    apply b'.ext
    intro i
    change g (f (b' i)) = b' i
    rw [integralLinearExtension_basis]
    rw [integralLinearExtension_commutes c c' n m hn]
    change m (e.symm (e (b i))) = b' i
    rw [LinearEquiv.symm_apply_apply]
    exact hm i
  have hfg : f.comp g = LinearMap.id := by
    apply c'.ext
    intro j
    change f (g (c' j)) = c' j
    rw [integralLinearExtension_basis]
    rw [integralLinearExtension_commutes b b' m n hm]
    change n (e (e.symm (c j))) = c' j
    rw [LinearEquiv.apply_symm_apply]
    exact hn j
  exact { f with
    invFun := g
    left_inv := fun x => DFunLike.congr_fun hgf x
    right_inv := fun x => DFunLike.congr_fun hfg x }
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def barycentricPresentationEquiv : BarycentricRing (P := P) K ≃ₐ[K] MonomialQuotient (K := K) (BarycentricAllowed (P := P)) := Ideal.quotientEquivAlgOfEq K
  (barycentricIdeal_eq_forbiddenIdeal K)
def barycentricMonomialEquiv : BarycentricRing (P := P) K ≃ₗ[K] (StandardFaceIndex P →₀ K) := (barycentricPresentationEquiv K).toLinearEquiv.trans (standardMonomialEquiv
  BarycentricAllowed barycentricAllowed_divisorClosed)
def barycentricRingEvaluation (p : P) : BarycentricRing (P := P) K →ₐ[K] BarycentricStalk K p := (monomialRestriction (booleanFaceInclusion hs p) BarycentricAllowed
  IsChainExponent barycentricAllowed_divisorClosed isChainExponent_divisorClosed (fun _ ha => standardExponent_map_booleanFaceInclusion hs p ha)).comp
  (barycentricPresentationEquiv K).toAlgHom
def barycentricRingSectionEquiv : BarycentricRing (P := P) K ≃ₗ[K] (barycentricDiagram (P := P) K).sections := (barycentricMonomialEquiv K).trans
  (barycentricSectionCoordinates K hs).symm
end
section
variable {V W K L : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W] [CommRing K] [CommRing L]
def booleanCoefficientChange (h : K →+* L) : BooleanBarycentricRing V K →ₛₗ[h] BooleanBarycentricRing V L := monomialCoefficientMap IsChainExponent
  isChainExponent_divisorClosed h
theorem booleanCoefficientChange_restriction (h : K →+* L) (e : V ↪ W) (x : BooleanBarycentricRing W K) : booleanCoefficientChange h (booleanRestriction e x) =
  booleanRestriction e (booleanCoefficientChange h x) := by sorry
def polynomialCoefficientChange (h : K →+* L) :
    MvPolynomial V K →ₛₗ[h] MvPolynomial V L where
  toFun := MvPolynomial.map h
  map_add' := (MvPolynomial.map h).map_add
  map_smul' c f := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (hs : IsSimplicialPoset P)
theorem booleanCoefficientChange_standardBasis (h : K →+* L) (p : P) (a : StandardInside p) : booleanCoefficientChange h (barycentricStalkStandardBasis K hs p a) =
  barycentricStalkStandardBasis L hs p a := by sorry
theorem polynomialCoefficientChange_standardBasis (h : K →+* L) (p : P) (a : StandardInside p) : polynomialCoefficientChange h (polynomialStandardBasis (K := K) hs p a) =
  polynomialStandardBasis (K := L) hs p a := by sorry
theorem polynomialCoefficientChange_restriction (h : K →+* L) {p q : P} (hqp : q ≤ p) (x : PolynomialStalk K p) : polynomialCoefficientChange h (polynomialRestriction K hqp x)
  = polynomialRestriction L hqp (polynomialCoefficientChange h x) := by sorry
end
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def integralStalkComparison (p : P) (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) : BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p := integralEquivExtension
  (barycentricStalkStandardBasis ℤ hs p) (barycentricStalkStandardBasis K hs p) (polynomialStandardBasis (K := ℤ) hs p) (polynomialStandardBasis (K := K) hs p)
  (booleanCoefficientChange (Int.castRingHom K)) (polynomialCoefficientChange (Int.castRingHom K)) (booleanCoefficientChange_standardBasis hs (Int.castRingHom K) p)
  (polynomialCoefficientChange_standardBasis hs (Int.castRingHom K) p) e
theorem integralStalkComparison_commutes (p : P) (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (x : BarycentricStalk ℤ p) : integralStalkComparison K hs p e
  (booleanCoefficientChange (Int.castRingHom K) x) = polynomialCoefficientChange (Int.castRingHom K) (e x) := by sorry
@[simp] theorem integralStalkComparison_basis (p : P)
    (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (a : StandardInside p) :
    integralStalkComparison K hs p e (barycentricStalkStandardBasis K hs p a) =
      polynomialCoefficientChange (Int.castRingHom K) (e (barycentricStalkStandardBasis ℤ hs p a)) := by sorry
def integralCoherentComparison
    (e : CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ)) :
    CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) where
  component p := integralStalkComparison K hs p (e.component p)
  naturality p q hqp x := by
    have hf : (polynomialRestriction K hqp).toLinearMap.comp
        (integralStalkComparison K hs p (e.component p)).toLinearMap = (integralStalkComparison K hs q (e.component q)).toLinearMap.comp
          (booleanRestriction (K := K) (faceVertexInclusion hqp)).toLinearMap := by
      apply (barycentricStalkStandardBasis K hs p).ext
      intro a
      change polynomialRestriction K hqp
        (integralStalkComparison K hs p (e.component p) (barycentricStalkStandardBasis K hs p a)) = integralStalkComparison K hs q (e.component q)
          (booleanRestriction (faceVertexInclusion hqp) (barycentricStalkStandardBasis K hs p a))
      rw [integralStalkComparison_basis, ← polynomialCoefficientChange_restriction (Int.castRingHom K) hqp]
      have hn := e.naturality p q hqp (barycentricStalkStandardBasis ℤ hs p a)
      change polynomialRestriction ℤ hqp (e.component p (barycentricStalkStandardBasis ℤ hs p a)) =
        e.component q (booleanRestriction (faceVertexInclusion hqp)
          (barycentricStalkStandardBasis ℤ hs p a)) at hn
      rw [hn, ← integralStalkComparison_commutes, booleanCoefficientChange_restriction, booleanCoefficientChange_standardBasis]
    exact DFunLike.congr_fun hf x
theorem integralStalkComparison_parameters (p : P) (e : BarycentricStalk ℤ p ≃ₗ[ℤ] PolynomialStalk ℤ p) (he : ∀ i : ℕ, ∀ x : BarycentricStalk ℤ p, e (booleanRankParameter (i +
  1) * x) = polynomialParameter ℤ p (i + 1) * e x) (i : ℕ) (x : BarycentricStalk K p) : integralStalkComparison K hs p e (booleanRankParameter (i + 1) * x) =
  polynomialParameter K p (i + 1) * integralStalkComparison K hs p e x := by sorry
theorem barycentricRingEvaluation_parameter (p : P) (i : ℕ) (hi : 0 < i) : barycentricRingEvaluation K hs p (barycentricRankParameter K i) = booleanRankParameter (V :=
  FaceVertex p) (K := K) i := by sorry
theorem faceRingEvaluation_parameter (p : P) (i : ℕ) (hi : 0 < i) : faceRingEvaluation K hs p (faceRankParameter K hs i) = polynomialParameter K p i := by sorry
def originalComparison (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)) : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs :=
  ((barycentricRingSectionEquiv K hs).trans e.sectionEquiv).trans (faceRingSectionEquiv K hs).symm
theorem originalComparison_evaluation (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)) (x : BarycentricRing (P := P) K) (p : P) : faceRingEvaluation K
  hs p (originalComparison K hs e x) = e.component p (barycentricRingEvaluation K hs p x) := by sorry
def originalParameterComparison (d : ℕ)
    (e : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K))
    (he : ∀ p : P, ∀ i : ℕ, ∀ x : BarycentricStalk K p, e.component p (booleanRankParameter (i + 1) * x) =
        polynomialParameter K p (i + 1) * e.component p x) :
    ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) where
  toLinearEquiv := originalComparison K hs e
  map_X_mul i x := by
    simp only [barycentricParameterAction, faceParameterAction, MvPolynomial.aeval_X]
    apply (faceRingSectionEquiv K hs).injective
    apply Subtype.ext
    funext p
    simp only [faceRingSectionEquiv_apply, faceRingSection_apply, originalComparison_evaluation, map_mul,
      barycentricRingEvaluation_parameter K hs p (i.val + 1) (Nat.succ_pos _), faceRingEvaluation_parameter K hs p (i.val + 1) (Nat.succ_pos _)]
    exact he p i.val (barycentricRingEvaluation K hs p x)
def universalIntegralComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) : CoherentEquiv (barycentricDiagram (P := P) ℤ) (polynomialDiagram ℤ) :=
  (exists_graded_coherent_parameter_comparison ℤ hs d hrank).choose
theorem universalIntegralComparison_spec (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) (p : P) : HasStandardLeading ℤ hs d p ((universalIntegralComparison hs d hrank).component
  p).toLinearMap ∧ (∀ i : ℕ, ∀ x : BarycentricStalk ℤ p, (universalIntegralComparison hs d hrank).component p (booleanRankParameter (i + 1) * x) = polynomialParameter ℤ p (i +
  1) * (universalIntegralComparison hs d hrank).component p x) ∧ HasStandardDegree ℤ hs p ((universalIntegralComparison hs d hrank).component p).toLinearMap := by sorry
def universalCoherentComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K) := integralCoherentComparison K
  hs (universalIntegralComparison hs d hrank)
def universalOriginalParameterComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) : ParameterEquiv (barycentricParameterAction (P := P) K d) (faceParameterAction K hs d) :=
  originalParameterComparison K hs d (universalCoherentComparison K hs d hrank) (fun p => integralStalkComparison_parameters K hs p ((universalIntegralComparison hs d
  hrank).component p) (universalIntegralComparison_spec hs d hrank p).2.1)
def barycentricGlobalStandardBasis : Module.Basis (StandardFaceIndex P) K (BarycentricRing (P := P) K) := Module.Basis.ofRepr (barycentricMonomialEquiv K)
def faceRestrictionIdeal (Q : Set P) : Ideal (FaceRing K hs) := Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = faceRingGenerator K hs p}
def barycentricRestrictionIdeal (Q : Set P) : Ideal (BarycentricRing (P := P) K) := Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = barycentricGenerator K p}
end FourPapers.Universal
namespace FourPapers.FilteredHomology
variable {K : Type*} [CommRing K]
structure Filtration (M : Type*) [AddCommGroup M] [Module K M] where
  level : ℕ → Submodule K M
  zero : level 0 = ⊥
  mono : Monotone level
  exhaustive : ∀ x : M, ∃ n, x ∈ level n
variable {X Y Z : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
def lowerInLevel (F : Filtration (K := K) X) (n : ℕ) : Submodule K (F.level (n + 1)) := (F.level n).comap (F.level (n + 1)).subtype
abbrev Grade (F : Filtration (K := K) X) (n : ℕ) := F.level (n + 1) ⧸ lowerInLevel F n
end FourPapers.FilteredHomology
namespace FourPapers.BasisGrading
variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
def Piece (b : Module.Basis I R M) (deg : I → A) (a : A) : Submodule R M := Submodule.span R (b '' {i | deg i = a})
end FourPapers.BasisGrading
namespace FourPapers.FilteredHomology
section
variable {K X Y Z X' Y' Z' : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup X'] [Module K X']
  [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']
def levelEquiv (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (e : X ≃ₗ[K] Y) (he : ∀ n x, e x ∈ G.level n ↔ x ∈ F.level n) (n : ℕ) :
    F.level n ≃ₗ[K] G.level n where
  toFun x := ⟨e x.val, (he n x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (he n (e.symm y.val)).mp
    (by simpa only [LinearEquiv.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' a x := Subtype.ext (e.map_smul a x.val)
theorem levelEquiv_lower (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (e : X ≃ₗ[K] Y) (he : ∀ n x, e x ∈ G.level n ↔ x ∈ F.level n) (n : ℕ) : (lowerInLevel F n).map
  (levelEquiv F G e he (n + 1)).toLinearMap = lowerInLevel G n := by sorry
def gradeEquiv (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (e : X ≃ₗ[K] Y) (he : ∀ n x, e x ∈ G.level n ↔ x ∈ F.level n) (n : ℕ) : Grade F n ≃ₗ[K] Grade G n :=
  Submodule.Quotient.equiv _ _ (levelEquiv F G e he (n + 1)) (levelEquiv_lower F G e he n)
end
variable {K X Y Z : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]
def submoduleFiltration (F : Filtration (K := K) X) (N : Submodule K X) :
    Filtration (K := K) N where
  level n := (F.level n).comap N.subtype
  zero := by simp only [F.zero, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr N.injective_subtype]
  mono := fun _ _ h => Submodule.comap_mono (F.mono h)
  exhaustive x := F.exhaustive x.val
end FourPapers.FilteredHomology
namespace FourPapers.Universal
section
open FourPapers.FilteredHomology
variable {K I J X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]
def basisFiltration (b : Module.Basis I K X) (w : I → ℕ) : Filtration (K := K) X where
  level n := Submodule.span K (b '' {i | w i < n})
  zero := by simp
  mono := by
    intro m n hmn
    apply Submodule.span_mono
    exact Set.image_mono (fun i hi => hi.trans_le hmn)
  exhaustive x := by
    refine ⟨(b.repr x).support.sup w + 1, ?_⟩
    rw [b.mem_span_image]
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup (f := w) hi)
end
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def koszulExteriorDegree {d i : ℕ} (s : Set.powersetCard (Fin d) i) : ℕ := ∑ j ∈ s.val, (j.val + 1)
def koszulExteriorWeight (d : ℕ) {i : ℕ} (s : Set.powersetCard (Fin d) i) : ℤ := ∑ j ∈ s.val, rankWeight d (j.val + 1)
abbrev OriginalKoszulIndex (P : Type*) [PartialOrder P] [OrderBot P] (d i : ℕ) := Σ _ : Set.powersetCard (Fin d) i, StandardFaceIndex P
def originalKoszulDegree {d i : ℕ} (a : OriginalKoszulIndex P d i) : ℕ := standardOrdinaryDegree a.2 + koszulExteriorDegree a.1
def originalKoszulWeight (d : ℕ) {i : ℕ} (a : OriginalKoszulIndex P d i) : ℤ := standardRankWeight d a.2 + koszulExteriorWeight d a.1
end
section
open CommAlg
section
variable {K B B' : Type u} {C : Type} [CommRing K] [CommRing B] [CommRing B']
  [Algebra K B] [Algebra K B'] [Fintype C] [LinearOrder C]
def parameterKoszulDifferential (γ : C → B) (i : ℕ) : (Set.powersetCard C (i + 1) →₀ B) →ₗ[K] (Set.powersetCard C i →₀ B) := (Koszul.coordinateDifferential γ (ModuleCat.of B
  B) i).restrictScalars K
theorem parameterKoszulDifferential_comp (γ : C → B) (i : ℕ) : (parameterKoszulDifferential (K := K) γ i).comp (parameterKoszulDifferential (K := K) γ (i + 1)) = 0 := by sorry
def parameterKoszulComplex (γ : C → B) : ChainComplex (ModuleCat.{u} K) ℕ := ChainComplex.of (fun i => ModuleCat.of K (Set.powersetCard C i →₀ B)) (fun i => ModuleCat.ofHom
  (parameterKoszulDifferential (K := K) γ i)) (fun i => ModuleCat.hom_ext (parameterKoszulDifferential_comp (K := K) γ i))
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
abbrev originalKoszulComplex : ChainComplex (ModuleCat.{u} K) ℕ := parameterKoszulComplex (K := K) (fun i : Fin d => faceRankParameter K hs (i.val + 1))
abbrev barycentricKoszulComplex : ChainComplex (ModuleCat.{u} K) ℕ := parameterKoszulComplex (K := K) (fun i : Fin d => barycentricRankParameter (P := P) K (i.val + 1))
end
open FourPapers.FilteredHomology
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
def originalKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ FaceRing K hs) := Finsupp.basis (fun _ => standardFaceBasis K hs)
def barycentricKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) := Finsupp.basis (fun _ =>
  barycentricGlobalStandardBasis K)
def originalKoszulFiltration (i : ℕ) : Filtration (K := K) (Set.powersetCard (Fin d) i →₀ FaceRing K hs) := basisFiltration (originalKoszulBasis K hs d i) (fun a =>
  (originalKoszulWeight d a).toNat)
def barycentricKoszulFiltration (i : ℕ) : Filtration (K := K) (Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) := basisFiltration (barycentricKoszulBasis (P := P) K
  d i) (fun a => (originalKoszulWeight d a).toNat)
def originalKoszulDegreePiece (i j : ℕ) := FourPapers.BasisGrading.Piece (originalKoszulBasis K hs d i) originalKoszulDegree j
def barycentricKoszulDegreePiece (i j : ℕ) := FourPapers.BasisGrading.Piece (barycentricKoszulBasis (P := P) K d i) originalKoszulDegree j
def originalKoszulCoefficientEquiv (hrank : ∀ p : P, faceRank p ≤ d) (i : ℕ) : (Set.powersetCard (Fin d) i →₀ BarycentricRing (P := P) K) ≃ₗ[K] (Set.powersetCard (Fin d) i →₀
  FaceRing K hs) := Finsupp.mapRange.linearEquiv (universalOriginalParameterComparison K hs d hrank).toLinearEquiv
end
section
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
def idealCoefficientSubmodule (S : Type*) (I : Ideal B) : Submodule K (S →₀ B) where
  carrier := {x | ∀ s, x s ∈ I}
  zero_mem' := fun _ => I.zero_mem
  add_mem' := fun hx hy s => I.add_mem (hx s) (hy s)
  smul_mem' := fun k x hx s => I.smul_of_tower_mem k (hx s)
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
def originalRelativeKoszulTerm (i : ℕ) : Submodule K ((originalKoszulComplex K hs d).X i) := idealCoefficientSubmodule _ (faceRestrictionIdeal K hs Q)
def barycentricRelativeKoszulTerm (i : ℕ) : Submodule K ((barycentricKoszulComplex (P := P) K d).X i) := idealCoefficientSubmodule _ (barycentricRestrictionIdeal K Q)
variable (hrank : ∀ p : P, faceRank p ≤ d)
def originalRelativeDegreeTerm (j i : ℕ) : Submodule K ((originalKoszulComplex K hs d).X i) := originalRelativeKoszulTerm K hs d Q i ⊓ originalKoszulDegreePiece K hs d i j
def barycentricRelativeDegreeTerm (j i : ℕ) : Submodule K ((barycentricKoszulComplex (P := P) K d).X i) := barycentricRelativeKoszulTerm (P := P) K d Q i ⊓
  barycentricKoszulDegreePiece (P := P) K d i j
def originalRelativeDegreeFiltration (j i : ℕ) := submoduleFiltration (originalKoszulFiltration K hs d i) (originalRelativeDegreeTerm K hs d Q j i)
def barycentricRelativeDegreeFiltration (j i : ℕ) := submoduleFiltration (barycentricKoszulFiltration (P := P) K d i) (barycentricRelativeDegreeTerm (P := P) K d Q j i)
section
include hQ
theorem originalKoszulCoefficientEquiv_relativeDegree (j i : ℕ) (x : (barycentricKoszulComplex (P := P) K d).X i) : originalKoszulCoefficientEquiv K hs d hrank i x ∈
  originalRelativeDegreeTerm K hs d Q j i ↔ x ∈ barycentricRelativeDegreeTerm (P := P) K d Q j i := by sorry
end
def relativeInternalCoefficientEquiv (j i : ℕ) :
    barycentricRelativeDegreeTerm (P := P) K d Q j i ≃ₗ[K] originalRelativeDegreeTerm K hs d Q j i where
  toFun x := ⟨originalKoszulCoefficientEquiv K hs d hrank i x.val,
    (originalKoszulCoefficientEquiv_relativeDegree K hs d Q hQ hrank j i x.val).mpr x.property⟩
  invFun y := ⟨(originalKoszulCoefficientEquiv K hs d hrank i).symm y.val, (originalKoszulCoefficientEquiv_relativeDegree K hs d Q hQ hrank j i _).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext ((originalKoszulCoefficientEquiv K hs d hrank i).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((originalKoszulCoefficientEquiv K hs d hrank i).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' a x := Subtype.ext (map_smul _ a x.val)
theorem relativeInternalCoefficientEquiv_filtered (j i n : ℕ) (x : barycentricRelativeDegreeTerm (P := P) K d Q j i) : relativeInternalCoefficientEquiv K hs d Q hQ hrank j i x
  ∈ (originalRelativeDegreeFiltration K hs d Q j i).level n ↔ x ∈ (barycentricRelativeDegreeFiltration (P := P) K d Q j i).level n := by sorry
end FourPapers.Universal
namespace FourPapers.FilteredHomology
variable {K X Y Z : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]
def PreservesPair (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (H : Filtration (K := K) Z) (p : X →ₗ[K] Y →ₗ[K] Z) : Prop := ∀ r s x y, x ∈ F.level (r + 1) → y ∈
  G.level (s + 1) → p x y ∈ H.level (r + s + 1)
variable (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
  (H : Filtration (K := K) Z) (p : X →ₗ[K] Y →ₗ[K] Z) (hp : PreservesPair F G H p)
def levelBilinearProduct (r s : ℕ) :
    F.level (r + 1) →ₗ[K] G.level (s + 1) →ₗ[K] H.level (r + s + 1) where
  toFun x :=
    { toFun := fun y => ⟨p x.val y.val, hp r s x.val y.val x.property y.property⟩
      map_add' y z := Subtype.ext (map_add (p x.val) y.val z.val)
      map_smul' c y := Subtype.ext (map_smul (p x.val) c y.val) }
  map_add' x z := by
    ext y
    exact LinearMap.congr_fun (map_add p x.val z.val) y.val
  map_smul' c x := by
    ext y
    exact LinearMap.congr_fun (map_smul p c x.val) y.val
def levelBilinearClass (r s : ℕ) : F.level (r + 1) →ₗ[K] G.level (s + 1) →ₗ[K] Grade H (r + s) := (levelBilinearProduct F G H p hp r s).compr₂ (lowerInLevel H (r + s)).mkQ
theorem levelBilinearClass_left_lower (r s : ℕ) : lowerInLevel F r ≤ LinearMap.ker (levelBilinearClass F G H p hp r s) := by sorry
theorem levelBilinearClass_right_lower (r s : ℕ) : lowerInLevel G s ≤ LinearMap.ker (levelBilinearClass F G H p hp r s).flip := by sorry
def gradeBilinearProduct (r s : ℕ) : Grade F r →ₗ[K] Grade G s →ₗ[K] Grade H (r + s) := (levelBilinearClass F G H p hp r s).liftQ₂ _ _ (levelBilinearClass_left_lower F G H p
  hp r s) (levelBilinearClass_right_lower F G H p hp r s)
end FourPapers.FilteredHomology
namespace FourPapers.Universal
section
open CliffordAlgebra
variable {K B C : Type*} [CommRing K] [CommRing B] [Algebra K B] [Fintype C]
abbrev CoefficientExterior (B C : Type*) [CommRing B] := ExteriorAlgebra B (C → B)
end
section
open CommAlg CliffordAlgebra
open FourPapers.FilteredHomology
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
  [Fintype C] [LinearOrder C]
def coefficientExteriorBasis : Module.Basis (Finset C) B (CoefficientExterior B C) := (Pi.basisFun B C).ExteriorAlgebra
def coefficientExteriorLift (i : ℕ) : (Set.powersetCard C i →₀ B) →ₗ[K] CoefficientExterior B C := ((coefficientExteriorBasis (B := B) (C := C)).repr.symm.toLinearMap.comp
  (Finsupp.lmapDomain B B Subtype.val)).restrictScalars K
def coefficientExteriorProjection (i : ℕ) : CoefficientExterior B C →ₗ[K] (Set.powersetCard C i →₀ B) := ((Finsupp.lsubtypeDomain {F : Finset C | F.card = i}).comp
  (coefficientExteriorBasis (B := B) (C := C)).repr.toLinearMap).restrictScalars K
end
set_option backward.isDefEq.respectTransparency.types false
open FourPapers.FilteredHomology
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
  [Fintype C] [LinearOrder C]
def coefficientKoszulProduct (i j : ℕ) : (Set.powersetCard C i →₀ B) →ₗ[K] (Set.powersetCard C j →₀ B) →ₗ[K] (Set.powersetCard C (i + j) →₀ B) := ((LinearMap.mul K
  (CoefficientExterior B C)).compl₁₂ (coefficientExteriorLift (K := K) i) (coefficientExteriorLift (K := K) j)).compr₂ (coefficientExteriorProjection (K := K) (i + j))
end FourPapers.Universal
namespace FourPapers.FilteredHomology
set_option backward.isDefEq.respectTransparency.types false
variable {K X Y Z : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]
def restrictedBilinearProduct (p : X →ₗ[K] Y →ₗ[K] Z)
    (N : Submodule K X) (M : Submodule K Y) (L : Submodule K Z)
    (hNML : ∀ x, x ∈ N → ∀ y, y ∈ M → p x y ∈ L) :
    N →ₗ[K] M →ₗ[K] L where
  toFun x :=
    { toFun := fun y => ⟨p x.val y.val, hNML x.val x.property y.val y.property⟩
      map_add' y z := Subtype.ext (map_add (p x.val) y.val z.val)
      map_smul' c y := Subtype.ext (map_smul (p x.val) c y.val) }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add p x.val z.val) y.val
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul p c x.val) y.val
end FourPapers.FilteredHomology
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency.types false
open FourPapers.FilteredHomology
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (hrank : ∀ p : P, faceRank p ≤ d)
theorem originalRelativeDegreeProduct_mem (j k i l : ℕ) (x : (originalKoszulComplex K hs d).X i) (y : (originalKoszulComplex K hs d).X l) (hx : x ∈ originalRelativeDegreeTerm
  K hs d Q j i) (hy : y ∈ originalRelativeDegreeTerm K hs d Q k l) : coefficientKoszulProduct (K := K) i l x y ∈ originalRelativeDegreeTerm K hs d Q (j + k) (i + l) := by
  sorry
theorem barycentricRelativeDegreeProduct_mem (j k i l : ℕ) (x : (barycentricKoszulComplex (P := P) K d).X i) (y : (barycentricKoszulComplex (P := P) K d).X l) (hx : x ∈
  barycentricRelativeDegreeTerm (P := P) K d Q j i) (hy : y ∈ barycentricRelativeDegreeTerm (P := P) K d Q k l) : coefficientKoszulProduct (K := K) i l x y ∈
  barycentricRelativeDegreeTerm (P := P) K d Q (j + k) (i + l) := by sorry
def originalRelativeInternalProduct (j k i l : ℕ) : originalRelativeDegreeTerm K hs d Q j i →ₗ[K] originalRelativeDegreeTerm K hs d Q k l →ₗ[K] originalRelativeDegreeTerm K hs
  d Q (j + k) (i + l) := restrictedBilinearProduct (coefficientKoszulProduct (K := K) i l) (originalRelativeDegreeTerm K hs d Q j i) (originalRelativeDegreeTerm K hs d Q k l)
  (originalRelativeDegreeTerm K hs d Q (j + k) (i + l)) (fun x hx y hy => originalRelativeDegreeProduct_mem K hs d Q j k i l x y hx hy)
def barycentricRelativeInternalProduct (j k i l : ℕ) : barycentricRelativeDegreeTerm (P := P) K d Q j i →ₗ[K] barycentricRelativeDegreeTerm (P := P) K d Q k l →ₗ[K]
  barycentricRelativeDegreeTerm (P := P) K d Q (j + k) (i + l) := restrictedBilinearProduct (coefficientKoszulProduct (K := K) i l) (barycentricRelativeDegreeTerm (P := P) K d
  Q j i) (barycentricRelativeDegreeTerm (P := P) K d Q k l) (barycentricRelativeDegreeTerm (P := P) K d Q (j + k) (i + l)) (fun x hx y hy =>
  barycentricRelativeDegreeProduct_mem K d Q j k i l x y hx hy)
section
include hrank
theorem originalRelativeInternalProduct_filtered (j k i l : ℕ) : PreservesPair (originalRelativeDegreeFiltration K hs d Q j i) (originalRelativeDegreeFiltration K hs d Q k l)
  (originalRelativeDegreeFiltration K hs d Q (j + k) (i + l)) (originalRelativeInternalProduct K hs d Q j k i l) := by sorry
theorem barycentricRelativeInternalProduct_filtered (j k i l : ℕ) : PreservesPair (barycentricRelativeDegreeFiltration (P := P) K d Q j i) (barycentricRelativeDegreeFiltration
  (P := P) K d Q k l) (barycentricRelativeDegreeFiltration (P := P) K d Q (j + k) (i + l)) (barycentricRelativeInternalProduct K d Q j k i l) := by sorry
end
def originalRelativeInternalGradeProduct (j k i l r s : ℕ) : Grade (originalRelativeDegreeFiltration K hs d Q j i) r →ₗ[K] Grade (originalRelativeDegreeFiltration K hs d Q k
  l) s →ₗ[K] Grade (originalRelativeDegreeFiltration K hs d Q (j + k) (i + l)) (r + s) := gradeBilinearProduct (originalRelativeDegreeFiltration K hs d Q j i)
  (originalRelativeDegreeFiltration K hs d Q k l) (originalRelativeDegreeFiltration K hs d Q (j + k) (i + l)) (originalRelativeInternalProduct K hs d Q j k i l)
  (originalRelativeInternalProduct_filtered K hs d Q hrank j k i l) r s
def barycentricRelativeInternalGradeProduct (j k i l r s : ℕ) : Grade (barycentricRelativeDegreeFiltration (P := P) K d Q j i) r →ₗ[K] Grade
  (barycentricRelativeDegreeFiltration (P := P) K d Q k l) s →ₗ[K] Grade (barycentricRelativeDegreeFiltration (P := P) K d Q (j + k) (i + l)) (r + s) := gradeBilinearProduct
  (barycentricRelativeDegreeFiltration (P := P) K d Q j i) (barycentricRelativeDegreeFiltration (P := P) K d Q k l) (barycentricRelativeDegreeFiltration (P := P) K d Q (j + k)
  (i + l)) (barycentricRelativeInternalProduct K d Q j k i l) (barycentricRelativeInternalProduct_filtered K d Q hrank j k i l) r s
def relativeInternalGradeCoefficientEquiv (j i n : ℕ) : Grade (barycentricRelativeDegreeFiltration (P := P) K d Q j i) n ≃ₗ[K] Grade (originalRelativeDegreeFiltration K hs d Q
  j i) n := gradeEquiv _ _ (relativeInternalCoefficientEquiv K hs d Q hQ hrank j i) (relativeInternalCoefficientEquiv_filtered K hs d Q hQ hrank j i) n
theorem relativeInternalGradeCoefficientEquiv_multiplicative (j k i l r s : ℕ) (x : Grade (barycentricRelativeDegreeFiltration (P := P) K d Q j i) r) (y : Grade
  (barycentricRelativeDegreeFiltration (P := P) K d Q k l) s) : relativeInternalGradeCoefficientEquiv K hs d Q hQ hrank (j + k) (i + l) (r + s)
  (barycentricRelativeInternalGradeProduct K d Q hrank j k i l r s x y) = originalRelativeInternalGradeProduct K hs d Q hrank j k i l r s
  (relativeInternalGradeCoefficientEquiv K hs d Q hQ hrank j i r x) (relativeInternalGradeCoefficientEquiv K hs d Q hQ hrank k l s y) := by sorry
end FourPapers.Universal
