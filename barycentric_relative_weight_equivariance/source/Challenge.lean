module
public import Mathlib

/-! Equivariant rank-selected cohomology of the relative weight filtration. -/

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
namespace CommAlg.Grading
variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
def restrictedBasis (b : Module.Basis I R M) (P : I → Prop) :
    Module.Basis {i // P i} R (Submodule.span R (b '' {i | P i})) :=
  (Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by congr 1; ext x; simp))
end CommAlg.Grading
namespace CommAlg.Simplicial
open CliffordAlgebra
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra
def Chains (K : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) := Submodule.span k (basis '' {s | K s ∧ s.card = i})
def Downward (K : Finset V → Prop) : Prop := ∀ ⦃s t⦄, t ⊆ s → K s → K t
abbrev boundary : Ambient V k →ₗ[k] Ambient V k := contractLeft (Q := (0 : QuadraticForm k (V → k))) (Fintype.linearCombination k (fun _ : V => (1 : k)))
lemma boundary_mem {K : Finset V → Prop} (hK : Downward K) {i : ℕ} {z : Ambient V k} (hz : z ∈ Chains K (i + 1)) : boundary z ∈ Chains K i := by sorry
end CommAlg.Simplicial
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
@[simp] theorem faceRank_bot : faceRank (⊥ : P) = 0 := by sorry
theorem faceRank_strictMono (hs : IsSimplicialPoset P) : StrictMono (faceRank : P → ℕ) := by sorry
theorem faceRank_eq_of_orderIso {Q : Type*} [PartialOrder Q] [OrderBot Q] [Fintype Q] (e : P ≃o Q) (p : P) : faceRank (e p) = faceRank p := by sorry
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
def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs := Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs := ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p
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
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}
def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop := ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val
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
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
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
def standardOrdinaryDegree (a : StandardFaceIndex P) : ℕ := a.val.sum (fun F n => n * faceRank F.val)
def faceRestrictionIdeal (Q : Set P) : Ideal (FaceRing K hs) := Ideal.span {x | ∃ p : P, p ∉ Q ∧ x = faceRingGenerator K hs p}
end
variable {V C : Type*} [Fintype V] [Fintype C]
structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)
attribute [class] ProperlyColoredComplex
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def rankColoredOrderComplex (hs : IsSimplicialPoset P) (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    ProperlyColoredComplex (NonzeroFace P) (Fin d) where
  face s := ∀ p ∈ s, ∀ q ∈ s, p.val ≤ q.val ∨ q.val ≤ p.val
  downward := by
    intro s t hst ht p hp q hq
    exact ht p (hst hp) q (hst hq)
  color p := ⟨faceRank p.val - 1, by
    have hpos : 0 < faceRank p.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr p.property)
    have hbound := hrank p.val
    omega⟩
  proper s hs' p hp q hq he := by
    have hpos (v : NonzeroFace P) : 0 < faceRank v.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr v.property)
    have hr : faceRank p.val = faceRank q.val := by
      have hh := congrArg Fin.val he
      have hp' := hpos p
      have hq' := hpos q
      dsimp at hh
      omega
    apply Subtype.ext
    rcases hs' p hp q hq with hpq | hqp
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hpq hn))) hr
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hqp (Ne.symm hn)))) hr.symm
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
def Preserves (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) : Prop := ∀ n x, x ∈ F.level n → f x ∈ G.level n
def lowerInLevel (F : Filtration (K := K) X) (n : ℕ) : Submodule K (F.level (n + 1)) := (F.level n).comap (F.level (n + 1)).subtype
abbrev Grade (F : Filtration (K := K) X) (n : ℕ) := F.level (n + 1) ⧸ lowerInLevel F n
def levelMap (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) (hf : Preserves F G f) (n : ℕ) : F.level n →ₗ[K] G.level n := (f.domRestrict
  _).codRestrict _ (fun x => hf n x.val x.property)
def gradeMap (F : Filtration (K := K) X) (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) (hf : Preserves F G f) (n : ℕ) : Grade F n →ₗ[K] Grade G n := Submodule.mapQ _ _ (levelMap
  F G f hf (n + 1)) (fun x hx => hf n x.val hx)
def boundaryMap (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) : X →ₗ[K] LinearMap.ker g := f.codRestrict _ (fun x => LinearMap.congr_fun hfg x)
abbrev Homology (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0) := LinearMap.ker g ⧸ LinearMap.range (boundaryMap f g hfg)
end FourPapers.FilteredHomology
namespace FourPapers.Universal
open CommAlg
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
def augmentedFaceBoundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Simplicial.Chains (k := K) Λ (i + 1) →ₗ[K] Simplicial.Chains (k := K) Λ i :=
  (Simplicial.boundary.domRestrict (Simplicial.Chains Λ (i + 1))).codRestrict _ (fun x => Simplicial.boundary_mem hΛ x.property)
def relativeFaceSubmodule (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Submodule K (Simplicial.Chains (k := K) Λ i) := (Simplicial.Chains Λ₀ i).comap (Simplicial.Chains Λ i).subtype
abbrev RelativeAugmentedChains (Λ Λ₀ : Finset V → Prop) (i : ℕ) := Simplicial.Chains (k := K) Λ i ⧸ relativeFaceSubmodule (K := K) Λ Λ₀ i
def relativeAugmentedBoundary (Λ Λ₀ : Finset V → Prop)
    (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) :
    RelativeAugmentedChains (K := K) Λ Λ₀ (i + 1) →ₗ[K] RelativeAugmentedChains (K := K) Λ Λ₀ i :=
  Submodule.mapQ _ _ (augmentedFaceBoundary Λ hΛ i) (by
    intro x hx
    exact Simplicial.boundary_mem hΛ₀ hx)
def relativeAugmentedCoboundary (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) : Module.Dual K (RelativeAugmentedChains (K := K)
  Λ Λ₀ i) →ₗ[K] Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ (i + 1)) := (relativeAugmentedBoundary Λ Λ₀ hΛ hΛ₀ i).dualMap
theorem relativeAugmentedCoboundary_square (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) : (relativeAugmentedCoboundary (K := K)
  Λ Λ₀ hΛ hΛ₀ (i + 1)).comp (relativeAugmentedCoboundary (K := K) Λ Λ₀ hΛ hΛ₀ i) = 0 := by sorry
def relativeAugmentedCochainComplex (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) : CochainComplex (ModuleCat.{max u v} K) ℕ :=
  CochainComplex.of (fun i => ModuleCat.of K (Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i))) (fun i => ModuleCat.ofHom (relativeAugmentedCoboundary Λ Λ₀ hΛ hΛ₀ i))
  (fun i => ModuleCat.hom_ext (relativeAugmentedCoboundary_square Λ Λ₀ hΛ hΛ₀ i))
def reducedRelativeCohomology (Λ Λ₀ : Finset V → Prop)
    (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (q : ℤ) :
    ModuleCat.{max u v} K :=
  if -1 ≤ q then (relativeAugmentedCochainComplex (K := K) Λ Λ₀ hΛ hΛ₀).homology (q + 1).toNat
  else ModuleCat.of K (ULift.{v} (Fin 0 → K))
def rankSelection {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Finset V → Prop := fun F => D.face F ∧ F.image D.color ⊆ S
theorem rankSelection_downward {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Simplicial.Downward (rankSelection D S) := by sorry
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
variable {C : Type*} [LinearOrder C] [DecidableEq C] {V : Type*} [Fintype V] (D : FourPapers.Universal.ProperlyColoredComplex V C)
def colorLinearOrder : LinearOrder V := LinearOrder.lift' (fun v => toLex (D.color v, (Fintype.equivFin V) v)) (by
    intro v w h
    apply (Fintype.equivFin V).injective
    exact congrArg (fun p => (ofLex p).2) h)
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal
open CommAlg
variable {K V : Type*} [CommRing K] [Fintype V] [LinearOrder V]
abbrev AugmentedFaceIndex (Λ : Finset V → Prop) (i : ℕ) := {F : Finset V // Λ F ∧ F.card = i}
abbrev RelativeFaceIndex (Λ Λ₀ : Finset V → Prop) (i : ℕ) := {F : Finset V // Λ F ∧ F.card = i ∧ ¬ Λ₀ F}
def augmentedChainBasis (Λ : Finset V → Prop) (i : ℕ) : Module.Basis (AugmentedFaceIndex Λ i) K (Simplicial.Chains (k := K) Λ i) := Grading.restrictedBasis Simplicial.basis
  (fun F => Λ F ∧ F.card = i)
def relativeFaceClass (Λ Λ₀ : Finset V → Prop) (i : ℕ) (F : AugmentedFaceIndex Λ i) : RelativeAugmentedChains (K := K) Λ Λ₀ i := Submodule.Quotient.mk (augmentedChainBasis Λ i
  F)
def relativeCochainCoordinates (Λ Λ₀ : Finset V → Prop) (i : ℕ) :
    Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i) →ₗ[K] (RelativeFaceIndex Λ Λ₀ i → K) where
  toFun f F := f (relativeFaceClass Λ Λ₀ i ⟨F.val, F.property.1, F.property.2.1⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem relativeCochainCoordinates_injective (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Function.Injective (relativeCochainCoordinates (K := K) Λ Λ₀ i) := by sorry
theorem relativeCochainCoordinates_surjective (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Function.Surjective (relativeCochainCoordinates (K := K) Λ Λ₀ i) := by sorry
def relativeCochainCoordinateEquiv (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i) ≃ₗ[K] (RelativeFaceIndex Λ Λ₀ i → K) :=
  LinearEquiv.ofBijective (relativeCochainCoordinates Λ Λ₀ i) ⟨relativeCochainCoordinates_injective Λ Λ₀ i, relativeCochainCoordinates_surjective Λ Λ₀ i⟩
end FourPapers.Universal
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
variable (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
  (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
  (a : X →ₗ[K] X') (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
  (hab : b.comp f = f'.comp a) (hbc : c.comp g = g'.comp b)
def inducedCycleMap : LinearMap.ker g →ₗ[K] LinearMap.ker g' := (b.domRestrict _).codRestrict _ (by
    intro y
    change g' (b y.val) = 0
    have hy : g y.val = 0 := y.property
    have h := LinearMap.congr_fun hbc y.val
    simpa only [LinearMap.comp_apply, hy, map_zero] using h.symm)
section
include hab
theorem inducedCycleMap_boundary (x : X) : inducedCycleMap g g' b c hbc (boundaryMap f g hfg x) = boundaryMap f' g' hfg' (a x) := by sorry
end
def inducedHomologyMap : Homology f g hfg →ₗ[K] Homology f' g' hfg' := Submodule.mapQ _ _ (inducedCycleMap g g' b c hbc) (by
    rintro z ⟨x, rfl⟩
    exact ⟨a x, (inducedCycleMap_boundary f g hfg f' g' hfg' a b c hab hbc x).symm⟩)
end
variable {K X Y Z : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]
def restrictedMap (f : X →ₗ[K] Y) (N : Submodule K X) (M : Submodule K Y) (hNM : ∀ x, x ∈ N → f x ∈ M) : N →ₗ[K] M := (f.domRestrict N).codRestrict M (fun x => hNM x.val
  x.property)
end FourPapers.FilteredHomology
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
section
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def nonzeroFaceOrderEquiv (e : P ≃o P) : NonzeroFace P ≃ NonzeroFace P where
  toFun p := ⟨e p.val, fun h => p.property (e.injective (h.trans e.map_bot.symm))⟩
  invFun p := ⟨e.symm p.val, fun h => p.property (e.symm.injective (h.trans e.symm.map_bot.symm))⟩
  left_inv p := Subtype.ext (e.symm_apply_apply p.val)
  right_inv p := Subtype.ext (e.apply_symm_apply p.val)
theorem faceRelations_rename (e : P ≃o P) {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) : MvPolynomial.rename (nonzeroFaceOrderEquiv e) f ∈ faceRelations K hs
  := by sorry
def faceRingOrderMap (e : P ≃o P) : FaceRing K hs →ₐ[K] FaceRing K hs := by
  let f := (Ideal.Quotient.mkₐ K (faceIdeal K hs)).comp
    (MvPolynomial.rename (nonzeroFaceOrderEquiv e))
  apply Ideal.Quotient.liftₐ (faceIdeal K hs) f
  have hh : faceIdeal K hs ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    change Ideal.Quotient.mk (faceIdeal K hs)
      (MvPolynomial.rename (nonzeroFaceOrderEquiv e) p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (faceRelations_rename K hs e hp))
  exact fun p hp => hh hp
theorem faceRingOrderMap_inverse (e : P ≃o P) (x : FaceRing K hs) : faceRingOrderMap K hs e.symm (faceRingOrderMap K hs e x) = x := by sorry
def faceRingOrderAut (e : P ≃o P) : FaceRing K hs ≃ₐ[K] FaceRing K hs := AlgEquiv.ofAlgHom (faceRingOrderMap K hs e) (faceRingOrderMap K hs e.symm)
    (by ext x; exact faceRingOrderMap_inverse K hs e.symm x)
    (by ext x; exact faceRingOrderMap_inverse K hs e x)
@[simp] theorem faceRingOrderAut_parameter (e : P ≃o P) (r : ℕ) :
    faceRingOrderAut K hs e (faceRankParameter K hs r) = faceRankParameter K hs r := by sorry
end
def koszulExteriorDegree {d i : ℕ} (s : Set.powersetCard (Fin d) i) : ℕ := ∑ j ∈ s.val, (j.val + 1)
abbrev OriginalKoszulIndex (P : Type*) [PartialOrder P] [OrderBot P] (d i : ℕ) := Σ _ : Set.powersetCard (Fin d) i, StandardFaceIndex P
def originalKoszulDegree {d i : ℕ} (a : OriginalKoszulIndex P d i) : ℕ := standardOrdinaryDegree a.2 + koszulExteriorDegree a.1
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
@[simp] theorem parameterKoszulComplex_d (γ : C → B) (i : ℕ) :
    (parameterKoszulComplex (K := K) γ).d (i + 1) i = ModuleCat.ofHom (parameterKoszulDifferential (K := K) γ i) := by sorry
theorem parameterKoszul_map_commutes (γ : C → B) (δ : C → B') (f : B →ₗ[K] B') (hf : ∀ j b, f (γ j * b) = δ j * f b) (i : ℕ) : (Finsupp.mapRange.linearMap f).comp
  (parameterKoszulDifferential (K := K) γ i) = (parameterKoszulDifferential (K := K) δ i).comp (Finsupp.mapRange.linearMap f) := by sorry
def parameterKoszulEquiv (γ : C → B) (δ : C → B')
    (e : B ≃ₗ[K] B') (he : ∀ j b, e (γ j * b) = δ j * e b) :
    parameterKoszulComplex (K := K) γ ≅ parameterKoszulComplex (K := K) δ := HomologicalComplex.Hom.isoOfComponents
    (fun _ => (Finsupp.mapRange.linearEquiv e).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [parameterKoszulComplex_d, parameterKoszulComplex_d]
      exact ModuleCat.hom_ext (parameterKoszul_map_commutes γ δ e.toLinearMap he j).symm)
end
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
abbrev originalKoszulComplex : ChainComplex (ModuleCat.{u} K) ℕ := parameterKoszulComplex (K := K) (fun i : Fin d => faceRankParameter K hs (i.val + 1))
end
open FourPapers.FilteredHomology
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
def originalKoszulBasis (i : ℕ) : Module.Basis (OriginalKoszulIndex P d i) K (Set.powersetCard (Fin d) i →₀ FaceRing K hs) := Finsupp.basis (fun _ => standardFaceBasis K hs)
def originalKoszulDegreePiece (i j : ℕ) := FourPapers.BasisGrading.Piece (originalKoszulBasis K hs d i) originalKoszulDegree j
def originalKoszulOrderAut (e : P ≃o P) : originalKoszulComplex K hs d ≅ originalKoszulComplex K hs d :=
  parameterKoszulEquiv _ _ (faceRingOrderAut K hs e).toLinearEquiv (by
    intro i x
    simp only [AlgEquiv.toLinearEquiv_apply, map_mul, faceRingOrderAut_parameter])
end
section
variable {K : Type u} [CommRing K]
abbrev complexIncoming (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) := (C.d (i + 1) i).hom
abbrev complexOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) := (C.d i (i - 1)).hom
theorem complexIncomingOutgoing (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) : (complexOutgoing C i).comp (complexIncoming C i) = 0 := by sorry
abbrev complexKernelHomology (C : ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ) := Homology (complexIncoming C i) (complexOutgoing C i) (complexIncomingOutgoing C i)
def submoduleComplex (C : ChainComplex (ModuleCat.{u} K) ℕ)
    (N : ∀ i, Submodule K (C.X i))
    (hN : ∀ i x, x ∈ N (i + 1) → complexIncoming C i x ∈ N i) :
    ChainComplex (ModuleCat.{u} K) ℕ := ChainComplex.of (fun i => ModuleCat.of K (N i))
    (fun i => ModuleCat.ofHom (restrictedMap (complexIncoming C i) _ _ (hN i))) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun f => f x.val) (C.d_comp_d (i + 2) (i + 1) i))
@[simp] theorem submoduleComplex_d (C : ChainComplex (ModuleCat.{u} K) ℕ)
    (N : ∀ i, Submodule K (C.X i))
    (hN : ∀ i x, x ∈ N (i + 1) → complexIncoming C i x ∈ N i) (i : ℕ) :
    (submoduleComplex C N hN).d (i + 1) i = ModuleCat.ofHom (restrictedMap (complexIncoming C i) _ _ (hN i)) := by sorry
end
section
variable {K B : Type u} {C : Type} [CommRing K] [CommRing B] [Algebra K B]
def idealCoefficientSubmodule (S : Type*) (I : Ideal B) : Submodule K (S →₀ B) where
  carrier := {x | ∀ s, x s ∈ I}
  zero_mem' := fun _ => I.zero_mem
  add_mem' := fun hx hy s => I.add_mem (hx s) (hy s)
  smul_mem' := fun k x hx s => I.smul_of_tower_mem k (hx s)
end
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
def originalRelativeKoszulTerm (i : ℕ) : Submodule K ((originalKoszulComplex K hs d).X i) := idealCoefficientSubmodule _ (faceRestrictionIdeal K hs Q)
variable (hrank : ∀ p : P, faceRank p ≤ d)
def originalRelativeDegreeTerm (j i : ℕ) : Submodule K ((originalKoszulComplex K hs d).X i) := originalRelativeKoszulTerm K hs d Q i ⊓ originalKoszulDegreePiece K hs d i j
section
include hrank
theorem originalRelativeDegreeTerm_preserved (j i : ℕ) (x : (originalKoszulComplex K hs d).X (i + 1)) (hx : x ∈ originalRelativeDegreeTerm K hs d Q j (i + 1)) :
  complexIncoming (originalKoszulComplex K hs d) i x ∈ originalRelativeDegreeTerm K hs d Q j i := by sorry
end
def originalRelativeDegreeComplex (j : ℕ) : ChainComplex (ModuleCat.{u} K) ℕ := submoduleComplex (originalKoszulComplex K hs d) (originalRelativeDegreeTerm K hs d Q j)
  (originalRelativeDegreeTerm_preserved K hs d Q hrank j)
abbrev originalRelativeInternalHomology (j i : ℕ) := complexKernelHomology (originalRelativeDegreeComplex K hs d Q hrank j) i
end
section
variable {K : Type u} [CommRing K]
variable {C D E : ChainComplex (ModuleCat.{u} K) ℕ}
def submoduleComplexMap
    (N : ∀ i, Submodule K (C.X i)) (M : ∀ i, Submodule K (D.X i))
    (hN : ∀ i x, x ∈ N (i + 1) → complexIncoming C i x ∈ N i)
    (hM : ∀ i x, x ∈ M (i + 1) → complexIncoming D i x ∈ M i)
    (f : C ⟶ D) (hf : ∀ i x, x ∈ N i → f.f i x ∈ M i) :
    submoduleComplex C N hN ⟶ submoduleComplex D M hM where
  f i := ModuleCat.ofHom (restrictedMap (f.f i).hom (N i) (M i) (hf i))
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [submoduleComplex_d, submoduleComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun q : C.X (j + 1) ⟶ D.X j => q x.val) (f.comm (j + 1) j)
def complexKernelHomologyMap (f : C ⟶ D) (i : ℕ) : complexKernelHomology C i →ₗ[K] complexKernelHomology D i := inducedHomologyMap _ _ (complexIncomingOutgoing C i) _ _
  (complexIncomingOutgoing D i) (f.f (i + 1)).hom (f.f i).hom (f.f (i - 1)).hom (congrArg (fun q => q.hom) (f.comm (i + 1) i)).symm (congrArg (fun q => q.hom) (f.comm i (i -
  1))).symm
end
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
section
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
variable (Q : Set P) (e : P ≃o P) (hstable : ∀ p, e p ∈ Q ↔ p ∈ Q)
include hstable
theorem originalKoszulOrderAut_relativeDegree (j i : ℕ) (x : (originalKoszulComplex K hs d).X i) (hx : x ∈ originalRelativeDegreeTerm K hs d Q j i) : (originalKoszulOrderAut K
  hs d e).hom.f i x ∈ originalRelativeDegreeTerm K hs d Q j i := by sorry
end
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (e : P ≃o P) (hstable : ∀ p, e p ∈ Q ↔ p ∈ Q)
def originalRelativeInternalOrderMap (j : ℕ) : originalRelativeDegreeComplex K hs d Q hrank j ⟶ originalRelativeDegreeComplex K hs d Q hrank j := submoduleComplexMap _ _
  (originalRelativeDegreeTerm_preserved K hs d Q hrank j) (originalRelativeDegreeTerm_preserved K hs d Q hrank j) (originalKoszulOrderAut K hs d e).hom
  (originalKoszulOrderAut_relativeDegree K hs d Q e hstable j)
def originalRelativeInternalHomologyAction (j i : ℕ) : Module.End K (originalRelativeInternalHomology K hs d Q hrank j i) := complexKernelHomologyMap
  (originalRelativeInternalOrderMap K hs d hrank Q e hstable j) i
end
section
variable (G : Type v) (P : Type u) [Group G] [PartialOrder P]
structure PosetGroupAction where
  orderIso : G → P ≃o P
  one : orderIso 1 = OrderIso.refl P
  mul : ∀ g h, orderIso (g * h) = (orderIso h).trans (orderIso g)
end
variable {P K : Type u} {G : Type v} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K] [Group G]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q) (a : PosetGroupAction G P) (hstable : ∀ g p, a.orderIso g p ∈ Q ↔ p ∈ Q)
def rankSubsetDegree {d : ℕ} (S : Finset (Fin d)) : ℕ := ∑ r ∈ S, (r.val + 1)
def rankSubsetWeight (d : ℕ) (S : Finset (Fin d)) : ℕ := (∑ r ∈ S, rankWeight d (r.val + 1)).toNat
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
set_option backward.isDefEq.respectTransparency.types false
variable {V C K : Type*} [Fintype V] [Fintype C] [CommRing K] (D : FourPapers.Universal.ProperlyColoredComplex V C)
structure Subcomplex where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  subface : ∀ s, face s → D.face s
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex
set_option backward.isDefEq.respectTransparency.types false
variable {V C K : Type*} [Fintype V] [Fintype C] [CommRing K] (D : FourPapers.Universal.ProperlyColoredComplex V C)
variable {D} (Q : D.Subcomplex)
def toColoredComplex : FourPapers.Universal.ProperlyColoredComplex V C where
  face := Q.face
  downward := Q.downward
  color := D.color
  proper s hs := D.proper s (Q.subface s hs)
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
def rankColoredSubcomplex (Q : Set P) : (rankColoredOrderComplex hs d hrank).Subcomplex where
  face s := (⊥ : P) ∈ Q ∧ (rankColoredOrderComplex hs d hrank).face s ∧ ∀ p ∈ s, p.val ∈ Q
  downward := by
    intro s t hst ht
    exact ⟨ht.1, (rankColoredOrderComplex hs d hrank).downward hst ht.2.1, fun p hp => ht.2.2 p (hst hp)⟩
  subface s hs := hs.2.1
end
set_option backward.isDefEq.respectTransparency.types false
open CommAlg
variable {K V : Type*} [CommRing K] [Fintype V] [LinearOrder V]
def relativeCochainBasis (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Module.Basis (RelativeFaceIndex Λ Λ₀ i) K (Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i)) := (Pi.basisFun
  K (RelativeFaceIndex Λ Λ₀ i)).map (relativeCochainCoordinateEquiv (K := K) Λ Λ₀ i).symm
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex
set_option backward.isDefEq.respectTransparency.types false
section
open CategoryTheory.Limits CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
variable [D : FourPapers.Universal.ProperlyColoredComplex V C] (Q : D.Subcomplex) (K)
local instance : DecidableEq C := Classical.decEq C
set_option synthInstance.checkSynthOrder false in
local instance relativeSquarefreeHomologyVertexOrder : LinearOrder V := D.colorLinearOrder
abbrev rankCochainComplex (S : Finset C) : CochainComplex (ModuleCat.{u} K) ℕ := relativeAugmentedCochainComplex (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex
  S) (rankSelection_downward D S) (rankSelection_downward Q.toColoredComplex S)
end
open CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
variable {D : FourPapers.Universal.ProperlyColoredComplex V C} (Q : D.Subcomplex)
structure ColorPairAutomorphism where
  vertex : Equiv.Perm V
  face_iff : ∀ F, D.face (F.image vertex) ↔ D.face F
  subface_iff : ∀ F, Q.face (F.image vertex) ↔ Q.face F
  color_eq : ∀ v, D.color (vertex v) = D.color v
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex.ColorPairAutomorphism
set_option backward.isDefEq.respectTransparency.types false
open CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
section
variable {D : FourPapers.Universal.ProperlyColoredComplex V C} (Q : D.Subcomplex)
variable {Q} (e : Q.ColorPairAutomorphism)
def symm : Q.ColorPairAutomorphism where
  vertex := e.vertex.symm
  face_iff F := by
    have h := e.face_iff (F.image e.vertex.symm)
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id, Finset.image_id'] using h.symm
  subface_iff F := by
    have h := e.subface_iff (F.image e.vertex.symm)
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id, Finset.image_id'] using h.symm
  color_eq v := by
    have h := e.color_eq (e.vertex.symm v)
    simpa only [Equiv.apply_symm_apply] using h.symm
end
variable [D : FourPapers.Universal.ProperlyColoredComplex V C] {Q : D.Subcomplex}
variable (e : Q.ColorPairAutomorphism) (K)
section
set_option synthInstance.checkSynthOrder false in
local instance relativeCochainAutomorphismsVertexOrder : LinearOrder V := D.colorLinearOrder
local instance relativeCochainAutomorphismsColorDecidableEq : DecidableEq C := Classical.decEq _
local instance relativeCochainAutomorphismsVertexDecidableEq : DecidableEq V := Classical.decEq _
lemma rankSelection_iff (S : Finset C) (F : Finset V) : rankSelection D S (F.image e.vertex) ↔ rankSelection D S F := by sorry
lemma relativeRankSelection_iff (S : Finset C) (F : Finset V) : rankSelection Q.toColoredComplex S (F.image e.vertex) ↔ rankSelection Q.toColoredComplex S F := by sorry
def cochainIndexEquiv (S : Finset C) (j : ℕ) :
    RelativeFaceIndex (rankSelection D S) (rankSelection Q.toColoredComplex S) j ≃
      RelativeFaceIndex (rankSelection D S) (rankSelection Q.toColoredComplex S) j where
  toFun F := ⟨F.val.image e.vertex, (e.rankSelection_iff S F.val).mpr F.property.1,
    (Finset.card_image_of_injective F.val e.vertex.injective).trans F.property.2.1,
    fun h => F.property.2.2 ((e.relativeRankSelection_iff S F.val).mp h)⟩
  invFun F := ⟨F.val.image e.vertex.symm, (e.symm.rankSelection_iff S F.val).mpr F.property.1,
    (Finset.card_image_of_injective F.val e.vertex.symm.injective).trans F.property.2.1,
    fun h => F.property.2.2 ((e.symm.relativeRankSelection_iff S F.val).mp h)⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id, Finset.image_id']
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id, Finset.image_id']
def cochainEquiv (S : Finset C) (j : ℕ) : (Q.rankCochainComplex K S).X j ≃ₗ[K] (Q.rankCochainComplex K S).X j := (relativeCochainBasis (K := K) (rankSelection D S)
  (rankSelection Q.toColoredComplex S) j).equiv (relativeCochainBasis (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex S) j) (e.cochainIndexEquiv S j)
theorem cochainEquiv_differential (S : Finset C) (j : ℕ) (f : (Q.rankCochainComplex K S).X j) : (Q.rankCochainComplex K S).d j (j + 1) (e.cochainEquiv K S j f) =
  e.cochainEquiv K S (j + 1) ((Q.rankCochainComplex K S).d j (j + 1) f) := by sorry
def cochainMap (S : Finset C) : Q.rankCochainComplex K S ⟶ Q.rankCochainComplex K S where
  f j := (e.cochainEquiv K S j).toModuleIso.hom
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact e.cochainEquiv_differential K S i
end
set_option synthInstance.checkSynthOrder false in
local instance relativeSquarefreeNaturalityVertexOrder : LinearOrder V := D.colorLinearOrder
local instance relativeSquarefreeNaturalityColorDecidableEq : DecidableEq C := Classical.decEq _
local instance relativeSquarefreeNaturalityVertexDecidableEq : DecidableEq V := Classical.decEq _
def reducedCohomologyMap (S : Finset C) (q : ℤ) :
    reducedRelativeCohomology (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex S)
      (rankSelection_downward D S) (rankSelection_downward Q.toColoredComplex S) q ⟶
    reducedRelativeCohomology (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex S)
      (rankSelection_downward D S) (rankSelection_downward Q.toColoredComplex S) q := by
  by_cases hq : -1 ≤ q
  · simp only [reducedRelativeCohomology, if_pos hq]
    exact HomologicalComplex.homologyMap (e.cochainMap K S) (q + 1).toNat
  · simp only [reducedRelativeCohomology, if_neg hq]
    exact 𝟙 _
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex.ColorPairAutomorphism
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency.types false
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (e : P ≃o P) (hstable : ∀ p, e p ∈ Q ↔ p ∈ Q)
local instance rankColoredNaturalNonzeroDecidableEq : DecidableEq (NonzeroFace P) := Classical.decEq _
lemma rankColored_face_order_iff (F : Finset (NonzeroFace P)) : (rankColoredOrderComplex hs d hrank).face (F.image (nonzeroFaceOrderEquiv e)) ↔ (rankColoredOrderComplex hs d
  hrank).face F := by sorry
def rankColoredPairOrderAut :
    (rankColoredSubcomplex hs d hrank Q).ColorPairAutomorphism where
  vertex := nonzeroFaceOrderEquiv e
  face_iff := rankColored_face_order_iff hs d hrank e
  subface_iff F := by
    constructor
    · rintro ⟨hb, hF, hQ⟩
      refine ⟨hb, (rankColored_face_order_iff hs d hrank e F).mp hF, ?_⟩
      intro p hp
      exact (hstable p.val).mp
        (hQ (nonzeroFaceOrderEquiv e p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    · rintro ⟨hb, hF, hQ⟩
      refine ⟨hb, (rankColored_face_order_iff hs d hrank e F).mpr hF, ?_⟩
      intro p hp
      obtain ⟨a, ha, hap⟩ := Finset.mem_image.mp hp
      rw [← hap]
      exact (hstable a.val).mpr (hQ a ha)
  color_eq p := by
    apply Fin.ext
    change faceRank (e p.val) - 1 = faceRank p.val - 1
    rw [faceRank_eq_of_orderIso]
end
section
open CommAlg FourPapers.FilteredHomology
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
abbrev rankSelectedRelativeCohomology (S : Finset (Fin d)) (i : ℕ) :=
  letI : LinearOrder (NonzeroFace P) := (rankColoredOrderComplex hs d hrank).colorLinearOrder
  letI : DecidableEq (Fin d) := Classical.decEq _
  letI : DecidableEq (NonzeroFace P) := Classical.decEq _
  reducedRelativeCohomology (K := K)
    (rankSelection (rankColoredOrderComplex hs d hrank) S)
    (rankSelection (rankColoredSubcomplex hs d hrank Q).toColoredComplex S)
    (rankSelection_downward (rankColoredOrderComplex hs d hrank) S)
    (rankSelection_downward (rankColoredSubcomplex hs d hrank Q).toColoredComplex S)
    ((S.card : ℤ) - i - 1)
end
open FourPapers.FilteredHomology
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
include hQ in
theorem palomarRelativeWeightEquivariance (j i : ℕ) : ∃ F : Filtration (K := K) (originalRelativeInternalHomology K hs d Q hrank j i), F.level (2*d*j+1) = ⊤ ∧ ∃ hF : ∀ (e : P
  ≃o P) (hsQ : ∀ p, e p ∈ Q ↔ p ∈ Q), Preserves F F (originalRelativeInternalHomologyAction K hs d hrank Q e hsQ j i), ∀ n, ∃ E : Grade F n ≃ₗ[K] (∀ S : {S : Finset (Fin d) //
  rankSubsetDegree S = j ∧ rankSubsetWeight d S = n}, rankSelectedRelativeCohomology K hs d hrank Q S.val i), ∀ (e : P ≃o P) (hsQ : ∀ p, e p ∈ Q ↔ p ∈ Q) x S, E (gradeMap F F
  (originalRelativeInternalHomologyAction K hs d hrank Q e hsQ j i) (hF e hsQ) n x) S = (rankColoredPairOrderAut hs d hrank Q e hsQ).reducedCohomologyMap (D :=
  rankColoredOrderComplex hs d hrank) K S.val ((S.val.card : ℤ)-i-1) (E x S) := by sorry
end FourPapers.Universal
