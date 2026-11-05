module

public import PaperVerification.AlternatingFormsIntegerGrading
public import PaperVerification.AlternatingFormsKoszulResolution
public import TauCeti.Algebra.Module.GradedModule.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Graded homology and the Euler identity for the two-form complex

The homology is the actual kernel modulo the actual image, equipped with
the grading inherited from the shifted exterior modules.  The dimension
identity is proved on each homogeneous component by rank-nullity.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

section GradedLinearAlgebra

variable {K A B : Type*} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]

theorem homogeneous_image_piece
    (G : TauCeti.InternalGrading K A) (H : TauCeti.InternalGrading K B)
    (f : A →ₗ[K] B)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece H.piece 0) (q : ℤ) :
    (G.piece q).map f = LinearMap.range f ⊓ H.piece q := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by simpa using hf.map_mem hx⟩
  · rintro y ⟨⟨x, hxy⟩, hy⟩
    refine ⟨(DirectSum.decompose G.piece x q : A),
      (DirectSum.decompose G.piece x q).property, ?_⟩
    have h := hf.map_decompose q x
    rw [add_zero, hxy, DirectSum.decompose_of_mem_same H.piece hy] at h
    exact h

/-- Rank-nullity after restriction to a genuine homogeneous component. -/
theorem homogeneous_piece_rank_nullity
    (G : TauCeti.InternalGrading K A) (H : TauCeti.InternalGrading K B)
    (f : A →ₗ[K] B)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece H.piece 0) (q : ℤ) :
    Module.finrank K (G.piece q) =
      Module.finrank K ((G.ker hf).piece q) +
        Module.finrank K (LinearMap.range f ⊓ H.piece q : Submodule K B) := by
  let P := G.piece q
  let fq := f.domRestrict P
  have hrange : LinearMap.range fq = LinearMap.range f ⊓ H.piece q := by
    change LinearMap.range (f.comp P.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact homogeneous_image_piece G H f hf q
  have hker : (LinearMap.ker fq).map P.subtype = LinearMap.ker f ⊓ P := by
    change (LinearMap.ker (f.comp P.subtype)).map P.subtype = _
    rw [LinearMap.ker_comp, Submodule.map_comap_subtype, inf_comm]
  have hpiece : Module.finrank K ((G.ker hf).piece q) =
      Module.finrank K (LinearMap.ker f ⊓ P : Submodule K A) := by
    rw [← Submodule.finrank_map_subtype_eq (LinearMap.ker f) ((G.ker hf).piece q)]
    have he : (G.ker hf).piece q=P.comap (LinearMap.ker f).subtype := by
      ext z
      exact TauCeti.InternalGrading.mem_ker_piece G hf
    rw [he]
    rw [Submodule.map_comap_subtype]
  have h := fq.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker fq), hker,
    ← hpiece] at h
  simpa only [P,add_comm] using h.symm

/-- A homogeneous quotient has exactly the expected component kernel;
arbitrary representatives are projected to the required degree. -/
theorem homogeneous_quotient_piece_dimension
    (G : TauCeti.InternalGrading K A) (U : Submodule K A)
    (hU : DirectSum.SetLike.IsHomogeneous G.piece U) (q : ℤ) :
    Module.finrank K (G.piece q) =
      Module.finrank K ((G.quotient U hU).piece q) +
        Module.finrank K (U ⊓ G.piece q : Submodule K A) := by
  let P := G.piece q
  let π := U.mkQ.domRestrict P
  have hrange : LinearMap.range π = (G.quotient U hU).piece q := by
    change LinearMap.range (U.mkQ.comp P.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
    simpa only [TauCeti.InternalGrading.quotient_piece,LinearMap.restrictScalars_self] using
      (show P.map U.mkQ = (G.piece q).map U.mkQ from rfl)
  have hker : (LinearMap.ker π).map P.subtype = U ⊓ P := by
    change (LinearMap.ker (U.mkQ.comp P.subtype)).map P.subtype = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.map_comap_subtype, inf_comm]
  have h := π.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker π), hker] at h
  exact h.symm

end GradedLinearAlgebra

section GradedShortComplex

variable {K A₂ A₁ A₀ : Type*} [Field K]
  [AddCommGroup A₂] [Module K A₂] [FiniteDimensional K A₂]
  [AddCommGroup A₁] [Module K A₁] [FiniteDimensional K A₁]
  [AddCommGroup A₀] [Module K A₀] [FiniteDimensional K A₀]

variable (G₂ : TauCeti.InternalGrading K A₂) (G₁ : TauCeti.InternalGrading K A₁)
  (G₀ : TauCeti.InternalGrading K A₀)
  (d₂ : A₂ →ₗ[K] A₁) (d₁ : A₁ →ₗ[K] A₀) (hd : d₁.comp d₂ = 0)
  (hd₂ : TauCeti.LinearMap.IsHomogeneous d₂ G₂.piece G₁.piece 0)
  (hd₁ : TauCeti.LinearMap.IsHomogeneous d₁ G₁.piece G₀.piece 0)

def shortComplexToCycles : A₂ →ₗ[K] LinearMap.ker d₁ :=
  d₂.codRestrict _ (fun a => by
    change d₁ (d₂ a) = 0
    exact LinearMap.congr_fun hd a)

include hd₂ in
theorem shortComplexToCycles_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (shortComplexToCycles d₂ d₁ hd)
      G₂.piece (G₁.ker hd₁).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [TauCeti.InternalGrading.mem_ker_piece]
  exact hd₂.map_mem ha

def shortComplexH₀Grading :
    TauCeti.InternalGrading K (A₀ ⧸ LinearMap.range d₁) :=
  G₀.quotient (LinearMap.range d₁) hd₁.isHomogeneous_range

def shortComplexH₁Grading : TauCeti.InternalGrading K
    (LinearMap.ker d₁ ⧸ LinearMap.range (shortComplexToCycles d₂ d₁ hd)) :=
  (G₁.ker hd₁).quotient (LinearMap.range (shortComplexToCycles d₂ d₁ hd))
    (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).isHomogeneous_range

def shortComplexH₂Grading : TauCeti.InternalGrading K
    (LinearMap.ker (shortComplexToCycles d₂ d₁ hd)) :=
  G₂.ker (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁)

/-- Euler characteristic in every integer degree, with all three homology
spaces defined by the displayed maps. -/
theorem shortComplex_homogeneous_euler (q : ℤ) :
    (Module.finrank K ((shortComplexH₀Grading G₁ G₀ d₁ hd₁).piece q) : ℤ) -
      Module.finrank K ((shortComplexH₁Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).piece q) +
      Module.finrank K ((shortComplexH₂Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).piece q) =
    (Module.finrank K (G₀.piece q) : ℤ) - Module.finrank K (G₁.piece q) +
      Module.finrank K (G₂.piece q) := by
  have h₀ := homogeneous_quotient_piece_dimension G₀ (LinearMap.range d₁)
    hd₁.isHomogeneous_range q
  have h₁ := homogeneous_piece_rank_nullity G₁ G₀ d₁ hd₁ q
  have h₂ := homogeneous_quotient_piece_dimension (G₁.ker hd₁)
    (LinearMap.range (shortComplexToCycles d₂ d₁ hd))
    (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).isHomogeneous_range q
  have h₃ := homogeneous_piece_rank_nullity G₂ (G₁.ker hd₁)
    (shortComplexToCycles d₂ d₁ hd)
    (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁) q
  change (Module.finrank K ((G₀.quotient _ _).piece q) : ℤ) -
      Module.finrank K (((G₁.ker hd₁).quotient _ _).piece q) +
      Module.finrank K ((G₂.ker _).piece q) = _
  omega

/-- The coefficientwise Euler identity is an equality of actual finite
Laurent-polynomial Hilbert series. -/
theorem shortComplex_hilbert_euler :
    finiteHilbertLaurent (shortComplexH₀Grading G₁ G₀ d₁ hd₁) -
      finiteHilbertLaurent (shortComplexH₁Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁) +
      finiteHilbertLaurent (shortComplexH₂Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁) =
    finiteHilbertLaurent G₀ - finiteHilbertLaurent G₁ + finiteHilbertLaurent G₂ := by
  ext q
  exact shortComplex_homogeneous_euler G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁ q

end GradedShortComplex

section ExteriorKoszul

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

def exteriorKoszulFirst (f g : ⋀[K]^2 M) :
    ExteriorAlgebra K M × ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M :=
  pairFirstDifferential (twoFormMultiplication f) (twoFormMultiplication g)

def exteriorKoszulSecond (f g : ⋀[K]^2 M) :
    ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M × ExteriorAlgebra K M :=
  pairSecondDifferential (twoFormMultiplication f) (twoFormMultiplication g)

theorem exteriorKoszul_comp (f g : ⋀[K]^2 M) :
    (exteriorKoszulFirst f g).comp (exteriorKoszulSecond f g) = 0 :=
  pairDifferentials_comp _ _ (twoFormMultiplication_commute f g)

def exteriorKoszulTerm₀Grading : TauCeti.InternalGrading K (ExteriorAlgebra K M) :=
  exteriorIntegerGrading

def exteriorKoszulTerm₁Grading :
    TauCeti.InternalGrading K (ExteriorAlgebra K M × ExteriorAlgebra K M) :=
  (exteriorIntegerGrading.prod exteriorIntegerGrading).shift (-2)

def exteriorKoszulTerm₂Grading : TauCeti.InternalGrading K (ExteriorAlgebra K M) :=
  exteriorIntegerGrading.shift (-4)

theorem exteriorKoszulFirst_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (exteriorKoszulFirst f g)
      exteriorKoszulTerm₁Grading.piece exteriorKoszulTerm₀Grading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorKoszulTerm₁Grading,TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece] at ha
  change a.1 ∈ exteriorIntegerGrading.piece (q + -2) ∧
    a.2 ∈ exteriorIntegerGrading.piece (q + -2) at ha
  have hf := (twoFormMultiplication_homogeneous f).map_mem ha.1
  have hg := (twoFormMultiplication_homogeneous g).map_mem ha.2
  have hq : q + -2 + 2 = q + 0 := by omega
  rw [hq] at hf hg
  exact Submodule.add_mem _ hf hg

theorem exteriorKoszulSecond_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (exteriorKoszulSecond f g)
      exteriorKoszulTerm₂Grading.piece exteriorKoszulTerm₁Grading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorKoszulTerm₂Grading,TauCeti.InternalGrading.shift_piece] at ha
  change a ∈ exteriorIntegerGrading.piece (q + -4) at ha
  have hf := (twoFormMultiplication_homogeneous f).map_mem ha
  have hg := (twoFormMultiplication_homogeneous g).map_mem ha
  rw [exteriorKoszulTerm₁Grading,TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change -((g : ExteriorAlgebra K M) * a) ∈ exteriorIntegerGrading.piece (q + 0 + -2) ∧
    (f : ExteriorAlgebra K M) * a ∈ exteriorIntegerGrading.piece (q + 0 + -2)
  have hq : q + -4 + 2 = q + 0 + -2 := by omega
  rw [hq] at hf hg
  exact ⟨Submodule.neg_mem _ hg, hf⟩

def exteriorKoszulH₀Grading (f g : ⋀[K]^2 M) :=
  shortComplexH₀Grading exteriorKoszulTerm₁Grading exteriorKoszulTerm₀Grading
    (exteriorKoszulFirst f g) (exteriorKoszulFirst_homogeneous f g)

def exteriorKoszulH₁Grading (f g : ⋀[K]^2 M) :=
  shortComplexH₁Grading exteriorKoszulTerm₂Grading exteriorKoszulTerm₁Grading
    exteriorKoszulTerm₀Grading (exteriorKoszulSecond f g) (exteriorKoszulFirst f g)
    (exteriorKoszul_comp f g) (exteriorKoszulSecond_homogeneous f g)
    (exteriorKoszulFirst_homogeneous f g)

def exteriorKoszulH₂Grading (f g : ⋀[K]^2 M) :=
  shortComplexH₂Grading exteriorKoszulTerm₂Grading exteriorKoszulTerm₁Grading
    exteriorKoszulTerm₀Grading (exteriorKoszulSecond f g) (exteriorKoszulFirst f g)
    (exteriorKoszul_comp f g) (exteriorKoszulSecond_homogeneous f g)
    (exteriorKoszulFirst_homogeneous f g)

/-- Euler characteristic for the literal two-form Koszul homology. -/
theorem exteriorKoszul_hilbert_euler (f g : ⋀[K]^2 M) :
    finiteHilbertLaurent (exteriorKoszulH₀Grading f g) -
      finiteHilbertLaurent (exteriorKoszulH₁Grading f g) +
      finiteHilbertLaurent (exteriorKoszulH₂Grading f g) =
    finiteHilbertLaurent (exteriorKoszulTerm₀Grading (K := K) (M := M)) -
      finiteHilbertLaurent (exteriorKoszulTerm₁Grading (K := K) (M := M)) +
      finiteHilbertLaurent (exteriorKoszulTerm₂Grading (K := K) (M := M)) :=
  shortComplex_hilbert_euler _ _ _ _ _ _ _ _

end ExteriorKoszul

end PaperVerification.AlternatingForms
