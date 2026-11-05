module

public import PaperVerification.FermionColorAction
public import PaperVerification.FermionExteriorWordMaps
public import PaperVerification.FermionStrictWeightRees
public import PaperVerification.FermionBlockInitialNormalForm

/-!
# Color preservation of the actual multiplicity filtration

The homogeneous pieces are spans of the original ordered exterior words.
They are not defined by transport along a color automorphism. Preservation
is proved first on the two generators at every index, then on exterior
products, then on polynomial-linear combinations, and finally on the
literal quotient-image filtration.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.ColorAction

open Exterior

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionColorFiltration_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem exterior_map_preserves_multiplicity (A : ColorMatrix R)
    {r : ℕ} {x : ExteriorAlgebra R (OddModule R n)}
    (hx : x ∈ exteriorWeightedPart multiplicityModeWeight r) :
    ExteriorAlgebra.map (linear A) x ∈ exteriorWeightedPart multiplicityModeWeight r := by
  letI := exteriorWeightedGrading (A := R) (multiplicityModeWeight (n := n))
  apply exteriorWeighted_map_mem multiplicityModeWeight
    (exteriorWeightedPart multiplicityModeWeight) (ExteriorAlgebra.map (linear A)) _ hx
  have htheta (i : Fin n) :
      ExteriorAlgebra.map (linear A) (exteriorGenerator (A := R) (Sum.inl i)) =
        A 0 0 • exteriorGenerator (Sum.inl i) +
          A 1 0 • exteriorGenerator (Sum.inr i) := by
    simp only [exteriorGenerator,ExteriorAlgebra.map_apply_ι]
    rw [← map_smul,← map_smul,← map_add]
    apply congrArg (ExteriorAlgebra.ι R)
    funext j
    cases j with
    | inl j =>
        by_cases h : j=i
        · subst j; simp [linear,Pi.single_apply]
        · simp [linear,Pi.single_apply,h,Ne.symm h]
    | inr j =>
        by_cases h : j=i
        · subst j; simp [linear,Pi.single_apply]
        · simp [linear,Pi.single_apply,h,Ne.symm h]
  have hxi (i : Fin n) :
      ExteriorAlgebra.map (linear A) (exteriorGenerator (A := R) (Sum.inr i)) =
        A 0 1 • exteriorGenerator (Sum.inl i) +
          A 1 1 • exteriorGenerator (Sum.inr i) := by
    simp only [exteriorGenerator,ExteriorAlgebra.map_apply_ι]
    rw [← map_smul,← map_smul,← map_add]
    apply congrArg (ExteriorAlgebra.ι R)
    funext j
    cases j with
    | inl j =>
        by_cases h : j=i
        · subst j; simp [linear,Pi.single_apply]
        · simp [linear,Pi.single_apply,h,Ne.symm h]
    | inr j =>
        by_cases h : j=i
        · subst j; simp [linear,Pi.single_apply]
        · simp [linear,Pi.single_apply,h,Ne.symm h]
  intro j
  cases j with
  | inl i =>
      rw [htheta]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem multiplicityModeWeight (.inl i)))
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem multiplicityModeWeight (.inr i)))
  | inr i =>
      rw [hxi]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem multiplicityModeWeight (.inl i)))
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem multiplicityModeWeight (.inr i)))

/-- The independently defined polynomial-linear multiplicity component. -/
def ambientPart (r : ℕ) : Submodule (PolynomialRing R n) (SuperRing R n) :=
  basisDegreePart (superPolynomialBasis (K := R)) multiplicityWordWeight r

theorem includeRight_mem_ambientPart {r : ℕ}
    {x : ExteriorAlgebra R (OddModule R n)}
    (hx : x ∈ exteriorWeightedPart multiplicityModeWeight r) :
    Algebra.TensorProduct.includeRight (A := PolynomialRing R n) x ∈ ambientPart r := by
  let L := (ambientPart (R := R) (n := n) r).restrictScalars R
  change Algebra.TensorProduct.includeRight x ∈ L
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨T,hT,rfl⟩ := hx
      have hb : superPolynomialBasis (K := R) T ∈ ambientPart r :=
        Submodule.subset_span ⟨T,hT,rfl⟩
      simpa only [L,Submodule.restrictScalars_mem,superPolynomialBasis_apply,
        Algebra.TensorProduct.includeRight_apply] using hb
  | zero => simpa only [map_zero] using L.zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using L.add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using L.smul_mem c ih

theorem ambient_basis_mem (A : ColorMatrix R) (T : Finset (OddIndex n)) :
    ambient A (superPolynomialBasis (K := R) T) ∈ ambientPart (multiplicityWordWeight T) := by
  rw [superPolynomialBasis_apply]
  change (1 : PolynomialRing R n) ⊗ₜ[R]
    ExteriorAlgebra.map (linear A) ((Pi.basisFun R (OddIndex n)).ExteriorAlgebra T) ∈ _
  exact includeRight_mem_ambientPart
    (exterior_map_preserves_multiplicity A (exteriorWeightedPart_basis multiplicityModeWeight T))

theorem ambient_preserves_part (A : ColorMatrix R) {r : ℕ} {x : SuperRing R n}
    (hx : x ∈ ambientPart r) : ambient A x ∈ ambientPart r := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨T,hT,rfl⟩ := hx
      change multiplicityWordWeight T=r at hT
      rw [←hT]
      exact ambient_basis_mem A T
  | zero => simpa only [map_zero] using (ambientPart r).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (ambientPart r).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (ambientPart r).smul_mem c ih

theorem ambientPart_le_homogeneousPiece (r : ℕ) :
    ambientPart (R := R) (n := n) r ≤
      BasisFiltered.homogeneousPiece (superPolynomialBasis (K := R))
        multiplicityWordWeight r := by
  apply Submodule.span_le.mpr
  rintro x ⟨T,hT,rfl⟩
  change multiplicityWordWeight T=r at hT
  change BasisFiltered.Homogeneous (superPolynomialBasis (K := R))
    multiplicityWordWeight r (superPolynomialBasis (K := R) T)
  rw [←hT]
  simpa only [one_smul] using
    BlockInitial.homogeneous_single (b := superPolynomialBasis (K := R))
      (weight := multiplicityWordWeight) T (1 : PolynomialRing R n)

theorem ambient_smul_basis_homogeneous (A : ColorMatrix R)
    (p : PolynomialRing R n) (T : Finset (OddIndex n)) :
    BasisFiltered.Homogeneous (superPolynomialBasis (K := R)) multiplicityWordWeight
      (multiplicityWordWeight T) (ambient A (p • superPolynomialBasis (K := R) T)) := by
  apply ambientPart_le_homogeneousPiece
  rw [map_smul]
  exact (ambientPart _).smul_mem p (ambient_basis_mem A T)

theorem ambientPart_le_lower {r d : ℕ} (hrd : r ≤ d) :
    ambientPart (R := R) (n := n) d ≤
      BlockInitial.lowerSubmodule (superPolynomialBasis (K := R)) multiplicityWordWeight r := by
  apply Submodule.span_le.mpr
  rintro x ⟨T,hT,rfl⟩
  change multiplicityWordWeight T=d at hT
  have h := BlockInitial.lowerBound_single
    (b := superPolynomialBasis (K := R)) (weight := multiplicityWordWeight) T 1
  intro U hU
  have ht : multiplicityWordWeight T ≤ multiplicityWordWeight U :=
    h U (by simpa only [one_smul] using hU)
  exact hrd.trans (hT ▸ ht)

theorem ambient_preserves_lower (A : ColorMatrix R) {r : ℕ} {x : SuperRing R n}
    (hx : BlockInitial.LowerBound (superPolynomialBasis (K := R)) multiplicityWordWeight r x) :
    BlockInitial.LowerBound (superPolynomialBasis (K := R)) multiplicityWordWeight r (ambient A x) := by
  let b := superPolynomialBasis (K := R) (n := n)
  let L := BlockInitial.lowerSubmodule b multiplicityWordWeight r
  change ambient A x ∈ L
  rw [←b.sum_repr x,map_sum]
  apply Submodule.sum_mem
  intro T hT
  rw [map_smul]
  by_cases hc : b.repr x T=0
  · rw [hc,zero_smul]
    exact L.zero_mem
  · exact L.smul_mem _ (ambientPart_le_lower (hx T hc) (ambient_basis_mem A T))

/-- The filtration is the image of the actual ambient lower-weight vectors. -/
def quotientFiltration (phi : Fin n → PolynomialRing R n) (r : ℕ) :
    Submodule R (StrictQuotient (fun _ => (1 : R)) phi) :=
  ((BlockInitial.lowerSubmodule (superPolynomialBasis (K := R)) multiplicityWordWeight r).restrictScalars
    R).map
      (((strictIdeal (fun _ => (1 : R)) phi).ringCon.mkₐ R).toLinearMap)

theorem quotientEquiv_preserves_filtration (g : Matrix.GeneralLinearGroup (Fin 2) R)
    (phi : Fin n → PolynomialRing R n) {r : ℕ}
    {z : StrictQuotient (fun _ => (1 : R)) phi}
    (hz : z ∈ quotientFiltration phi r) : quotientEquiv g phi z ∈ quotientFiltration phi r := by
  obtain ⟨x,hx,rfl⟩ := hz
  exact ⟨ambient g.val x,ambient_preserves_lower g.val hx,rfl⟩

theorem quotientEquiv_filtration_iff (g : Matrix.GeneralLinearGroup (Fin 2) R)
    (phi : Fin n → PolynomialRing R n) (r : ℕ)
    (z : StrictQuotient (fun _ => (1 : R)) phi) :
    quotientEquiv g phi z ∈ quotientFiltration phi r ↔ z ∈ quotientFiltration phi r := by
  constructor
  · intro h
    have hh := quotientEquiv_preserves_filtration g⁻¹ phi h
    have he : quotientEquiv g⁻¹ phi (quotientEquiv g phi z)=z := by
      have ha := congrArg (fun e : StrictQuotient (fun _ => (1 : R)) phi ≃ₐ[R]
          StrictQuotient (fun _ => (1 : R)) phi ↦ e z)
        (quotientEquiv_mul g⁻¹ g phi)
      simpa only [inv_mul_cancel,quotientEquiv_one,AlgEquiv.one_apply,AlgEquiv.mul_apply] using ha.symm
    rwa [he] at hh
  · exact quotientEquiv_preserves_filtration g phi

end PaperVerification.Fermion.ColorAction
