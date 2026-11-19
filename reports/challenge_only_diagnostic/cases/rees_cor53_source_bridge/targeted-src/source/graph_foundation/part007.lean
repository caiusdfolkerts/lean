module
public import graph_foundation.part006

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.BlockDegrees -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {K B : Type*} [CommRing K] {M : B → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] {J : B → Type*}

lemma dfinsupp_basis_degree_iff (b : ∀ i, Module.Basis (J i) K (M i))
    (degree : ∀ i, J i → ℕ) (n : ℕ) (x : Π₀ i, M i) :
    x ∈ basisDegreePiece (DFinsupp.basis b) (fun a => degree a.1 a.2) n ↔
      ∀ i, x i ∈ basisDegreePiece (b i) (degree i) n := by
  change x ∈ Submodule.span K ((DFinsupp.basis b) '' {a | degree a.1 a.2 = n}) ↔ _
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨i,j⟩,hij,rfl⟩ := hy
      intro r
      rw [dfinsuppBasis_apply]
      by_cases hir : i = r
      · subst r
        rw [DFinsupp.single_eq_same]
        change (b i) j ∈ Submodule.span K ((b i) '' {j | degree i j = n})
        exact Submodule.subset_span ⟨j,hij,rfl⟩
      · simp [hir, basisDegreePiece]
    | zero => intro i; exact (basisDegreePiece (b i) (degree i) n).zero_mem
    | add y z hy hz ihy ihz =>
      intro i
      exact (basisDegreePiece (b i) (degree i) n).add_mem (ihy i) (ihz i)
    | smul c y hy ih =>
      intro i
      exact (basisDegreePiece (b i) (degree i) n).smul_mem c (ih i)
  · intro hx
    rw [← (DFinsupp.basis b).linearCombination_repr x,
      Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨a, ?_, rfl⟩
    by_contra hn
    apply Finsupp.mem_support_iff.mp ha
    exact repr_zero_of_mem_basis_span (b a.1) {j | degree a.1 j = n} (hx a.1) hn

lemma blockMap_preserves_basis_degree (b : ∀ i, Module.Basis (J i) K (M i))
    (degree : ∀ i, J i → ℕ) (h : ∀ i, Module.End K (M i)) (n m : ℕ)
    (hh : ∀ i x, x ∈ basisDegreePiece (b i) (degree i) n →
      h i x ∈ basisDegreePiece (b i) (degree i) m)
    {x : Π₀ i, M i}
    (hx : x ∈ basisDegreePiece (DFinsupp.basis b) (fun a => degree a.1 a.2) n) :
    DFinsupp.mapRange.linearMap h x ∈
      basisDegreePiece (DFinsupp.basis b) (fun a => degree a.1 a.2) m := by
  apply (dfinsupp_basis_degree_iff b degree m _).mpr
  intro i
  exact hh i _ ((dfinsupp_basis_degree_iff b degree n x).mp hx i)

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.WeightFiltration -/
section

set_option autoImplicit false

/-!
# The exact coefficient filtration and triangular inverses

A filtration level is defined by the vanishing of actual coordinates in a module
basis. Unitriangular inverses preserve every level. This supplies the weight control
on the explicit contracting homotopies used to correct the first-power sections.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical Finset

variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]

def weightBelow (b : Module.Basis I K M) (rank : I → ℕ) (n : ℕ) : Submodule K M where
  carrier := {x | ∀ i, n ≤ rank i → b.repr x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi,hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

lemma weightBelow_mono (b : Module.Basis I K M) (rank : I → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    weightBelow b rank m ≤ weightBelow b rank n :=
  fun _ hx i hi => hx i (hmn.trans hi)

lemma basis_mem_weightBelow (b : Module.Basis I K M) (rank : I → ℕ) {i : I} {n : ℕ}
    (hi : rank i < n) : b i ∈ weightBelow b rank n := by
  intro j hj
  have hij : i ≠ j := fun h => Nat.not_lt_of_ge (h ▸ hj) hi
  simp [hij]

lemma weightBelow_zero (b : Module.Basis I K M) (rank : I → ℕ) : weightBelow b rank 0 = ⊥ := by
  apply le_antisymm
  · intro x hx
    apply (Submodule.mem_bot K).mpr
    apply b.repr.injective
    ext i
    simpa only [map_zero,Finsupp.zero_apply] using hx i (Nat.zero_le _)
  · exact bot_le

lemma map_mem_weightBelow_of_basis (b : Module.Basis I K M) (rank : I → ℕ)
    (f : M →ₗ[K] M) {n : ℕ}
    (hf : ∀ i, rank i < n → f (b i) ∈ weightBelow b rank n)
    {x : M} (hx : x ∈ weightBelow b rank n) : f x ∈ weightBelow b rank n := by
  rw [← b.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  apply Submodule.smul_mem
  apply hf
  by_contra h
  exact (Finsupp.mem_support_iff.mp hi) (hx i (Nat.le_of_not_gt h))

/-- At a maximal occupied weight a unitriangular map preserves the exact coordinate. -/
lemma triangular_max_coordinate (b : Module.Basis I K M) (rank : I → ℕ)
    (f : M →ₗ[K] M)
    (hdiag : ∀ i, b.repr (f (b i)) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (f (b i)) j = 0)
    (x : M) (i : I) (hi : i ∈ (b.repr x).support)
    (hmax : ∀ j ∈ (b.repr x).support, rank j ≤ rank i) :
    b.repr (f x) i = b.repr x i := by
  conv_lhs => rw [← b.linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [hdiag,mul_one]
  · intro j hj hji
    rw [htri j i hji (hmax j hj),mul_zero]
  · intro hni
    exact (hni hi).elim

/-- A genuine unitriangular automorphism has a filtration-preserving inverse. -/
theorem triangularInverse_preserves (b : Module.Basis I K M) (rank : I → ℕ)
    (f : M ≃ₗ[K] M)
    (hdiag : ∀ i, b.repr (f (b i)) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (f (b i)) j = 0)
    (n : ℕ) {y : M} (hy : y ∈ weightBelow b rank n) :
    f.symm y ∈ weightBelow b rank n := by
  let x := f.symm y
  intro j hj
  by_contra hjne
  have hjs : j ∈ (b.repr x).support := Finsupp.mem_support_iff.mpr hjne
  have hs : ((b.repr x).support.image rank).Nonempty :=
    ⟨rank j,Finset.mem_image.mpr ⟨j,hjs,rfl⟩⟩
  obtain ⟨i,hi,hir⟩ := Finset.mem_image.mp (Finset.max'_mem _ hs)
  have hmax : ∀ a ∈ (b.repr x).support, rank a ≤ rank i := by
    intro a ha
    rw [hir]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have hni : n ≤ rank i := hj.trans (hmax j hjs)
  have hc := triangular_max_coordinate b rank f.toLinearMap hdiag htri x i hi hmax
  have hfx : f x = y := f.apply_symm_apply y
  change b.repr (f x) i = b.repr x i at hc
  rw [hfx,hy i hni] at hc
  exact (Finsupp.mem_support_iff.mp hi) hc.symm

lemma perturbationInverse_preserves (b : Module.Basis I K M) (rank : I → ℕ)
    (d d₀ h : Module.End K M)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d - d₀) (h (b i))) j = 0)
    (n : ℕ) {y : M} (hy : y ∈ weightBelow b rank n) :
    (perturbationEquiv b rank d d₀ h hlower).symm y ∈ weightBelow b rank n := by
  apply triangularInverse_preserves b rank
  · intro i
    change b.repr ((perturbationEquiv b rank d d₀ h hlower).toLinearMap (b i)) i = 1
    rw [perturbationEquiv_toLinearMap]
    have hh := hlower i i le_rfl
    simp only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply] at hh
    simp [perturbationMap,hh]
  · intro i j hij hr
    change b.repr ((perturbationEquiv b rank d d₀ h hlower).toLinearMap (b i)) j = 0
    rw [perturbationEquiv_toLinearMap]
    have hh := hlower i j hr
    simp only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply] at hh
    simp [perturbationMap,hh,hij]
  · exact hy

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SectionWeightControl -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]

lemma preserves_weight_of_basis (b : Module.Basis I K M) (rank : I → ℕ)
    (h : Module.End K M)
    (hh : ∀ i j, rank i < rank j → b.repr (h (b i)) j = 0)
    (n : ℕ) {x : M} (hx : x ∈ weightBelow b rank n) : h x ∈ weightBelow b rank n := by
  apply map_mem_weightBelow_of_basis b rank h
  · intro i hi j hj
    exact hh i j (hi.trans_le hj)
  · exact hx

lemma partialPerturbation_preserves_weight (b : Module.Basis I K M) (rank : I → ℕ)
    (d d₀ h : Module.End K M)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d-d₀) (h (b i))) j = 0)
    (hh : ∀ i j, rank i < rank j → b.repr (h (b i)) j = 0)
    (n : ℕ) {x : M} (hx : x ∈ weightBelow b rank n) :
    (h * (perturbationEquiv b rank d d₀ h hlower).symm.toLinearMap) x ∈
      weightBelow b rank n := by
  exact preserves_weight_of_basis b rank h hh n
    (perturbationInverse_preserves b rank d d₀ h hlower n hx)

variable {N : Type*} [AddCommGroup N] [Module K N]

lemma correctedSection_lower_difference (b : Module.Basis I K M) (rank : I → ℕ)
    (d : Module.End K M) (dN : Module.End K N) (s : N →ₗ[K] M) (H : Module.End K M)
    (n : ℕ) (hH : ∀ x, x ∈ weightBelow b rank n → H x ∈ weightBelow b rank n)
    (y : N) (hdefect : sectionDefect d dN s y ∈ weightBelow b rank n) :
    correctedSection d dN s H y - s y ∈ weightBelow b rank n := by
  have he : correctedSection d dN s H y - s y = -H (sectionDefect d dN s y) := by
    simp only [correctedSection, LinearMap.sub_apply, LinearMap.comp_apply]
    abel
  rw [he]
  exact (weightBelow b rank n).neg_mem (hH _ hdefect)

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ActualFirstPowerSection -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma firstPowerTarget_maximalWeight
    {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) (w : AdmissibleChain n E 1 β) :
    finiteChainFactorWeight.{u} w.val ≤
      finiteChainFactorWeight.{u} (firstPowerTarget hβ).val := by
  let b : E := w.val.val 0
  have he : singletonChain b = w.val := singletonChain_eq w.val
  have hb : finiteRowExponent n b.val ≤ β := by
    simpa only [← he, singletonChain_shift] using w.property
  change finiteChainFactorWeight.{u} w.val ≤ finiteChainFactorWeight.{u} (singletonChain a)
  rw [← he, singletonChain_factorWeight, singletonChain_factorWeight]
  by_cases hba : b = a
  · simp [hba]
  · exact (proper_generator_weight_lt hβ hb hba).le

def firstPowerLowerHomotopy (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) (w : AdmissibleChain n E 1 β)
    (hw : w ≠ firstPowerTarget hβ) :
    Module.End k (TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val))) :=
  (properFirstPowerChainBlock_contractible (k := k) hE hβ w hw).choose

lemma firstPowerLowerHomotopy_contracts (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) (w : AdmissibleChain n E 1 β)
    (hw : w ≠ firstPowerTarget hβ) :
    quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (β-finiteChainShift n w.val) * firstPowerLowerHomotopy (k := k) hE hβ w hw +
    firstPowerLowerHomotopy (k := k) hE hβ w hw *
      quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val) = 1 :=
  (properFirstPowerChainBlock_contractible (k := k) hE hβ w hw).choose_spec.1

lemma firstPowerLowerHomotopy_raises (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) (w : AdmissibleChain n E 1 β)
    (hw : w ≠ firstPowerTarget hβ) (i : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (β-finiteChainShift n w.val)))
    (hx : x ∈ totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (β-finiteChainShift n w.val)) i) :
    firstPowerLowerHomotopy (k := k) hE hβ w hw x ∈
      totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val)) (i+1) :=
  (properFirstPowerChainBlock_contractible (k := k) hE hβ w hw).choose_spec.2 i x hx

/-- An actual chain section into the first-power ideal complex, in normal-form coordinates.
The differential is the literal signed face differential transported by `chainTotalEquiv`.
All contraction and triangularity hypotheses have been proved from the sublattice data. -/
theorem actualFirstPowerChainSection_exists (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) :
    ∃ F : TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
          (β-finiteChainShift n (firstPowerTarget hβ).val)) →ₗ[k]
        ChainTotalModule n E 1 β k,
      (DFinsupp.lapply (firstPowerTarget hβ)).comp F = LinearMap.id ∧
      (chainTotalOrdinaryDifferential hE 1 β k).comp F =
        F.comp (quotientTotalDifferential
          (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
          (β-finiteChainShift n (firstPowerTarget hβ).val)) := by
  let b := fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
    (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val))
  let rank := fun w : AdmissibleChain n E 1 β => finiteChainFactorWeight.{u} w.val
  let D := chainTotalOrdinaryDifferential hE 1 β k
  let dB := fun w : AdmissibleChain n E 1 β => quotientTotalDifferential (k := k)
    (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)
  let H := firstPowerLowerHomotopy (k := k) hE hβ
  have hlow : ∀ i j, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((D-blockSpecialDifferential dB) ((DFinsupp.basis b) i)) j = 0 :=
    chainTotalDifferential_strictLower hE 1 β k
  refine ⟨blockCorrectedSection b rank (firstPowerTarget hβ) D dB H hlow, ?_⟩
  exact blockCorrectedSection_is_chain b rank (firstPowerTarget hβ)
    (firstPowerTarget_maximalWeight hβ) D dB H
    (chainTotalOrdinaryDifferential_square_zero hE 1 β k)
    (fun w => quotientTotalDifferential_comp _ _)
    (firstPowerLowerHomotopy_contracts hE hβ) hlow

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MaximalBlockGeometry -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {K B : Type*} [CommRing K] {M : B → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] {J : B → Type*}

lemma blockSpecialDifferential_single (dB : ∀ i, Module.End K (M i))
    (a : B) (x : M a) :
    blockSpecialDifferential dB (DFinsupp.lsingle (R := K) (M := M) a x) = DFinsupp.lsingle (R := K) (M := M) a (dB a x) := by
  ext i
  by_cases hi : a = i
  · subst i; simp [blockSpecialDifferential]
  · simp [blockSpecialDifferential, hi]

lemma blockCorrectedSection_lower_basis
    (b : ∀ i, Module.Basis (J i) K (M i)) (rank : B → ℕ) (a : B)
    (d : Module.End K (Π₀ i, M i)) (dB : ∀ i, Module.End K (M i))
    (h : ∀ i, i ≠ a → Module.End K (M i))
    (hlower : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((d-blockSpecialDifferential dB) ((DFinsupp.basis b) i)) j = 0)
    (j : J a) :
    blockCorrectedSection b rank a d dB h hlower (b a j) -
      (DFinsupp.basis b) ⟨a,j⟩ ∈ weightBelow (DFinsupp.basis b) (fun i => rank i.1) (rank a) := by
  have hs : DFinsupp.lsingle (R := K) (M := M) a (b a j) = (DFinsupp.basis b) ⟨a,j⟩ :=
    (dfinsuppBasis_apply b a j).symm
  have hdef : sectionDefect d (dB a) (DFinsupp.lsingle (R := K) (M := M) a) (b a j) =
      (d-blockSpecialDifferential dB) ((DFinsupp.basis b) ⟨a,j⟩) := by
    change d (DFinsupp.lsingle (R := K) (M := M) a (b a j)) - DFinsupp.lsingle (R := K) (M := M) a (dB a (b a j)) = _
    rw [← blockSpecialDifferential_single dB, hs]
    rfl
  rw [← hs]
  apply correctedSection_lower_difference
  · intro x hx
    exact partialPerturbation_preserves_weight (DFinsupp.basis b) (fun i => rank i.1)
      d (blockSpecialDifferential dB) (blockPartialHomotopy a h)
      (blockPerturbationLower b rank a d dB h hlower)
      (blockMap_basis_weight b rank (fun i => if hi : i = a then 0 else h i hi))
      (rank a) hx
  · rw [hdef]
    exact fun i hi => hlower ⟨a,j⟩ i hi

lemma blockSingle_preserves_basis_degree
    (b : ∀ i, Module.Basis (J i) K (M i)) (degree : ∀ i, J i → ℕ)
    (a : B) (n : ℕ) {x : M a} (hx : x ∈ basisDegreePiece (b a) (degree a) n) :
    DFinsupp.lsingle (R := K) (M := M) a x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) n := by
  apply (dfinsupp_basis_degree_iff b degree n _).mpr
  intro i
  by_cases hai : a = i
  · subst i; simpa using hx
  · simp [hai, basisDegreePiece]

lemma blockCorrectedSection_preserves_degree
    (b : ∀ i, Module.Basis (J i) K (M i)) (rank : B → ℕ)
    (degree : ∀ i, J i → ℕ) (a : B)
    (d : Module.End K (Π₀ i, M i)) (dB : ∀ i, Module.End K (M i))
    (h : ∀ i, i ≠ a → Module.End K (M i))
    (hlower : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((d-blockSpecialDifferential dB) ((DFinsupp.basis b) i)) j = 0)
    (hd : ∀ n x, x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) (n+1) →
      d x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) n)
    (hdzero : ∀ x, x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) 0 → d x = 0)
    (hdB : ∀ i n x, x ∈ basisDegreePiece (b i) (degree i) (n+1) →
      dB i x ∈ basisDegreePiece (b i) (degree i) n)
    (hdBzero : ∀ i x, x ∈ basisDegreePiece (b i) (degree i) 0 → dB i x = 0)
    (hh : ∀ i (hi : i ≠ a) n x, x ∈ basisDegreePiece (b i) (degree i) n →
      h i hi x ∈ basisDegreePiece (b i) (degree i) (n+1))
    (n : ℕ) {x : M a} (hx : x ∈ basisDegreePiece (b a) (degree a) n) :
    blockCorrectedSection b rank a d dB h hlower x ∈
      basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) n := by
  have hd₀ : ∀ n x, x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) (n+1) →
      blockSpecialDifferential dB x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) n := by
    intro n x hx
    exact blockMap_preserves_basis_degree b degree dB (n+1) n (fun i => hdB i n) hx
  have hh₀ : ∀ n x, x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) n →
      blockPartialHomotopy a h x ∈ basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2) (n+1) := by
    intro n x hx
    apply blockMap_preserves_basis_degree b degree (fun i => if hi : i = a then 0 else h i hi) n (n+1) _ hx
    intro i y hy
    split_ifs with hi
    · exact (basisDegreePiece (b i) (degree i) (n+1)).zero_mem
    · exact hh i hi n y hy
  exact correctedSection_preserves_degree
    (basisDegreePiece (DFinsupp.basis b) (fun i => degree i.1 i.2))
    (basisDegreePiece (b a) (degree a)) d (dB a) (DFinsupp.lsingle (R := K) (M := M) a) _
    hd (hdB a) hdzero (hdBzero a)
    (fun n x hx => blockSingle_preserves_basis_degree b degree a n hx)
    (fun n x hx => partialPerturbation_raises (DFinsupp.basis b) (fun i => rank i.1)
      (fun i => degree i.1 i.2) d (blockSpecialDifferential dB) (blockPartialHomotopy a h)
      (blockPerturbationLower b rank a d dB h hlower) hd hd₀ hh₀ n hx) n hx

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BasisDegreeSupport -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]

lemma basisDegreePiece_differential_lowers (b : Module.Basis I K M) (degree : I → ℕ)
    (D : Module.End K M)
    (hD : ∀ i j, degree j + 1 ≠ degree i → b.repr (D (b i)) j = 0)
    (n : ℕ) {x : M} (hx : x ∈ basisDegreePiece b degree (n+1)) :
    D x ∈ basisDegreePiece b degree n := by
  have hle : basisDegreePiece b degree (n+1) ≤ (basisDegreePiece b degree n).comap D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change D (b i) ∈ basisDegreePiece b degree n
    rw [← b.linearCombination_repr (D (b i)), Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨j, ?_, rfl⟩
    change degree i = n+1 at hi
    by_contra hn
    change degree j ≠ n at hn
    exact (Finsupp.mem_support_iff.mp hj) (hD i j (by omega))
  exact hle hx

lemma basisDegreePiece_differential_zero (b : Module.Basis I K M) (degree : I → ℕ)
    (D : Module.End K M)
    (hD : ∀ i j, degree j + 1 ≠ degree i → b.repr (D (b i)) j = 0)
    {x : M} (hx : x ∈ basisDegreePiece b degree 0) : D x = 0 := by
  have hle : basisDegreePiece b degree 0 ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change D (b i) = 0
    apply b.repr.injective
    ext j
    change degree i = 0 at hi
    simpa only [map_zero, Finsupp.zero_apply] using hD i j (by omega)
  exact hle hx

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.TotalFaceDegrees -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma quotientFaceProjection_degree (B : Family V) (α : Exponent V) (i : ℕ)
    {x : Simplicial.Ambient V k} (hx : x ∈ Simplicial.Chains (fullKoszulFaces α) i) :
    quotientFaceProjection B α x ∈ Simplicial.Chains (quotientKoszulFaces B α) i := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s,⟨hs,hcard⟩,rfl⟩ := hy
    rw [quotientFaceProjection, relativeProjection_basis]
    split_ifs with hq
    · exact Simplicial.basis_mem hq hcard
    · exact Submodule.zero_mem _
  | zero => simpa using (Submodule.zero_mem (Simplicial.Chains (k := k) (quotientKoszulFaces B α) i))
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa using Submodule.smul_mem _ c ih

lemma quotientTotalDifferential_lowers (B : Family V) (α : Exponent V) (i : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hx : x ∈ totalFacePiece (quotientKoszulFaces B α) (i+1)) :
    quotientTotalDifferential B α x ∈ totalFacePiece (quotientKoszulFaces B α) i := by
  change quotientFaceProjection B α (Simplicial.boundary x.val) ∈
    Simplicial.Chains (quotientKoszulFaces B α) i
  apply quotientFaceProjection_degree
  apply Simplicial.boundary_mem (fullKoszulFaces_downward α)
  exact Simplicial.chains_mono (fun s hs => hs.1) (i+1)
    (show x.val ∈ Simplicial.Chains (quotientKoszulFaces B α) (i+1) from hx)

lemma quotientTotalDifferential_zero_degree (B : Family V) (α : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hx : x ∈ totalFacePiece (quotientKoszulFaces B α) 0) :
    quotientTotalDifferential B α x = 0 := by
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary x.val) = 0
  have hz : Simplicial.boundary x.val = 0 := Simplicial.boundary_zero_degree_zero
    (show x.val ∈ Simplicial.Chains (quotientKoszulFaces B α) 0 from hx)
  rw [hz, map_zero]

lemma totalFacePiece_eq_basisDegreePiece (P : Finset V → Prop) (i : ℕ) :
    totalFacePiece (k := k) P i = basisDegreePiece (totalFaceBasis P) (fun s => s.val.card) i :=
  totalFacePiece_eq_basis_span P i

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerSectionGeometry -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def firstPowerChainSection (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) :
    TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
          (β-finiteChainShift n (firstPowerTarget hβ).val)) →ₗ[k]
        ChainTotalModule n E 1 β k :=
  blockCorrectedSection
    (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)))
    (fun w => finiteChainFactorWeight.{u} w.val) (firstPowerTarget hβ)
    (chainTotalOrdinaryDifferential hE 1 β k)
    (fun w => quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (β-finiteChainShift n w.val))
    (firstPowerLowerHomotopy hE hβ) (chainTotalDifferential_strictLower hE 1 β k)

theorem firstPowerChainSection_is_chain (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val) :
    (DFinsupp.lapply (firstPowerTarget hβ)).comp (firstPowerChainSection (k := k) hE hβ) =
        LinearMap.id ∧
      (chainTotalOrdinaryDifferential hE 1 β k).comp (firstPowerChainSection (k := k) hE hβ) =
        (firstPowerChainSection (k := k) hE hβ).comp (quotientTotalDifferential (k := k)
          (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
          (β-finiteChainShift n (firstPowerTarget hβ).val)) := by
  exact blockCorrectedSection_is_chain (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)))
    (fun w : AdmissibleChain n E 1 β => finiteChainFactorWeight.{u} w.val) (firstPowerTarget hβ) (firstPowerTarget_maximalWeight hβ)
    (chainTotalOrdinaryDifferential hE 1 β k) (fun w : AdmissibleChain n E 1 β => quotientTotalDifferential (k := k)
      (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)) (firstPowerLowerHomotopy (k := k) hE hβ)
    (chainTotalOrdinaryDifferential_square_zero hE 1 β k)
    (fun w => quotientTotalDifferential_comp _ _) (firstPowerLowerHomotopy_contracts hE hβ)
    (chainTotalDifferential_strictLower hE 1 β k)

theorem firstPowerChainSection_lower_basis (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (s : {s // quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
      (β-finiteChainShift n (firstPowerTarget hβ).val) s}) :
    firstPowerChainSection (k := k) hE hβ (totalFaceBasis _ s) -
        chainTotalBasis n E 1 β k ⟨firstPowerTarget hβ,s⟩ ∈
      weightBelow (chainTotalBasis n E 1 β k)
        (fun i => finiteChainFactorWeight.{u} i.1.val)
        (finiteChainFactorWeight.{u} (firstPowerTarget hβ).val) := by
  exact blockCorrectedSection_lower_basis (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)))
    (fun w : AdmissibleChain n E 1 β => finiteChainFactorWeight.{u} w.val) (firstPowerTarget hβ) (chainTotalOrdinaryDifferential hE 1 β k) (fun w : AdmissibleChain n E 1 β => quotientTotalDifferential (k := k)
      (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)) (firstPowerLowerHomotopy (k := k) hE hβ)
    (chainTotalDifferential_strictLower hE 1 β k) s

theorem firstPowerChainSection_preserves_degree (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (i : ℕ)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
        (β-finiteChainShift n (firstPowerTarget hβ).val)))
    (hx : x ∈ basisDegreePiece (totalFaceBasis _)
      (fun s => s.val.card) i) :
    firstPowerChainSection (k := k) hE hβ x ∈
      basisDegreePiece (chainTotalBasis n E 1 β k) (fun s => s.2.val.card) i := by
  unfold firstPowerChainSection
  refine blockCorrectedSection_preserves_degree (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)))
    (fun w : AdmissibleChain n E 1 β => finiteChainFactorWeight.{u} w.val) (fun _ s => s.val.card) (firstPowerTarget hβ)
    (chainTotalOrdinaryDifferential hE 1 β k) (fun w : AdmissibleChain n E 1 β => quotientTotalDifferential (k := k)
      (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)) (firstPowerLowerHomotopy (k := k) hE hβ)
    (chainTotalDifferential_strictLower hE 1 β k) ?_ ?_ ?_ ?_ ?_ i hx
  · intro j y hy
    exact basisDegreePiece_differential_lowers (chainTotalBasis n E 1 β k)
      (fun s => s.2.val.card) _ (chainTotalOrdinaryDifferential_degreeSupport hE 1 β k) j hy
  · intro y hy
    exact basisDegreePiece_differential_zero (chainTotalBasis n E 1 β k)
      (fun s => s.2.val.card) _ (chainTotalOrdinaryDifferential_degreeSupport hE 1 β k) hy
  · intro w j y hy
    rw [← totalFacePiece_eq_basisDegreePiece] at hy ⊢
    exact quotientTotalDifferential_lowers _ _ j y hy
  · intro w y hy
    rw [← totalFacePiece_eq_basisDegreePiece] at hy
    exact quotientTotalDifferential_zero_degree _ _ y hy
  · intro w hw j y hy
    rw [← totalFacePiece_eq_basisDegreePiece] at hy ⊢
    exact firstPowerLowerHomotopy_raises hE hβ w hw j y hy
/-- Degree preservation in the actual exterior face pieces, before any homology is taken. -/
theorem firstPowerChainSection_preserves_face_degree (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (i : ℕ)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
        (β-finiteChainShift n (firstPowerTarget hβ).val)))
    (hx : x ∈ totalFacePiece
      (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
        (β-finiteChainShift n (firstPowerTarget hβ).val)) i)
    (w : AdmissibleChain n E 1 β) :
    firstPowerChainSection (k := k) hE hβ x w ∈
      totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val)) i := by
  rw [totalFacePiece_eq_basisDegreePiece] at hx ⊢
  exact (dfinsupp_basis_degree_iff (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val))) (fun _ s => s.val.card) i
    (firstPowerChainSection (k := k) hE hβ x)).mp
    (firstPowerChainSection_preserves_degree hE hβ i x hx) w

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ExteriorFaceProduct -/
section

set_option autoImplicit false
set_option maxHeartbeats 20000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def faceWedgeSign (F G : Finset V) (h : Disjoint F G) : ℤˣ :=
  (Set.powersetCard.permOfDisjoint
    (s := (⟨F,rfl⟩ : Set.powersetCard V F.card))
    (t := (⟨G,rfl⟩ : Set.powersetCard V G.card)) h).sign

lemma faceBasis_mul_of_disjoint (F G : Finset V) (h : Disjoint F G) :
    Simplicial.basis (k := k) F * Simplicial.basis G =
      faceWedgeSign F G h • Simplicial.basis (F∪G) := by
  simpa only [Simplicial.basis,faceWedgeSign,Set.powersetCard.coe_disjUnion,
    Finset.disjUnion_eq_union] using
    ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun k V)
      (⟨F,rfl⟩ : Set.powersetCard V F.card)
      (⟨G,rfl⟩ : Set.powersetCard V G.card) h

lemma faceBasis_mul_of_not_disjoint (F G : Finset V) (h : ¬Disjoint F G) :
    Simplicial.basis (k := k) F * Simplicial.basis G = 0 :=
  ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun k V)
    (⟨F,rfl⟩ : Set.powersetCard V F.card)
    (⟨G,rfl⟩ : Set.powersetCard V G.card) h

lemma faceSpan_mul_mem (P Q R : Finset V → Prop)
    (hPQ : ∀ F, P F → ∀ G, Q G → Disjoint F G → R (F∪G))
    {x y : Simplicial.Ambient V k}
    (hx : x∈basisSpan Simplicial.basis P) (hy : y∈basisSpan Simplicial.basis Q) :
    x*y∈basisSpan Simplicial.basis R := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F,hF,rfl⟩ := hx
    change P F at hF
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨G,hG,rfl⟩ := hy
      change Q G at hG
      by_cases hd : Disjoint F G
      · rw [faceBasis_mul_of_disjoint F G hd]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨F∪G,hPQ F hF G hG hd,rfl⟩)
      · rw [faceBasis_mul_of_not_disjoint F G hd]
        exact Submodule.zero_mem _
    | zero => simp
    | add y z hy hz ihy ihz =>
      simpa only [mul_add] using Submodule.add_mem _ ihy ihz
    | smul c y hy ih =>
      simpa only [mul_smul_comm] using Submodule.smul_mem _ c ih
  | zero => simp
  | add x z hx hz ihx ihz =>
    simpa only [add_mul] using Submodule.add_mem _ ihx ihz
  | smul c x hx ih =>
    simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ih

def totalFaceMulBilinear (P Q R : Finset V → Prop)
    (hPQ : ∀ F, P F → ∀ G, Q G → Disjoint F G → R (F∪G)) :
    TotalFaceModule (k := k) P →ₗ[k]
      TotalFaceModule (k := k) Q →ₗ[k] TotalFaceModule (k := k) R where
  toFun x :=
    { toFun := fun y => ⟨x.val*y.val,faceSpan_mul_mem P Q R hPQ x.property y.property⟩
      map_add' := fun y z => Subtype.ext (mul_add x.val y.val z.val)
      map_smul' := fun c y => Subtype.ext (mul_smul_comm c x.val y.val) }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (add_mul x.val z.val y.val)
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (smul_mul_assoc c x.val y.val)

def totalFaceMulTensor (P Q R : Finset V → Prop)
    (hPQ : ∀ F, P F → ∀ G, Q G → Disjoint F G → R (F∪G)) :
    (TotalFaceModule (k := k) P ⊗[k] TotalFaceModule (k := k) Q) →ₗ[k]
      TotalFaceModule (k := k) R :=
  TensorProduct.lift (totalFaceMulBilinear P Q R hPQ)

@[simp] lemma totalFaceMulTensor_tmul_val (P Q R : Finset V → Prop)
    (hPQ : ∀ F, P F → ∀ G, Q G → Disjoint F G → R (F∪G))
    (x : TotalFaceModule (k := k) P) (y : TotalFaceModule (k := k) Q) :
    (totalFaceMulTensor P Q R hPQ (x⊗ₜ[k]y)).val=x.val*y.val := rfl

lemma totalFaceMulTensor_degree (P Q R : Finset V → Prop)
    (hPQ : ∀ F, P F → ∀ G, Q G → Disjoint F G → R (F∪G))
    (i j : ℕ) (x : TotalFaceModule (k := k) P) (y : TotalFaceModule (k := k) Q)
    (hx : x∈totalFacePiece P i) (hy : y∈totalFacePiece Q j) :
    totalFaceMulTensor P Q R hPQ (x⊗ₜ[k]y) ∈ totalFacePiece R (i+j) := by
  change x.val*y.val ∈ Simplicial.Chains R (i+j)
  apply faceSpan_mul_mem (fun F => P F ∧ F.card=i) (fun G => Q G ∧ G.card=j)
    (fun H => R H ∧ H.card=i+j) _ hx hy
  intro F hF G hG hd
  exact ⟨hPQ F hF.1 G hG.1 hd,by rw [Finset.card_union_of_disjoint hd,hF.2,hG.2]⟩

lemma faceSpan_involute_mem (P : Finset V → Prop) {x : Simplicial.Ambient V k}
    (hx : x∈basisSpan Simplicial.basis P) :
    CliffordAlgebra.involute x∈basisSpan Simplicial.basis P := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F,hF,rfl⟩ := hx
    rw [Simplicial.basis,TauCeti.ExteriorAlgebra.involute_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨F,hF,rfl⟩)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def totalFaceInvolute (P : Finset V → Prop) : Module.End k (TotalFaceModule (k := k) P) :=
  (CliffordAlgebra.involute.toLinearMap.domRestrict (TotalFaceModule (k := k) P)).codRestrict _
    (fun x => faceSpan_involute_mem P x.property)

lemma idealTotalDifferential_mul (P Q R : Finset V → Prop)
    (hP : Simplicial.Downward P) (hQ : Simplicial.Downward Q) (hR : Simplicial.Downward R)
    (hPQ : ∀ F, P F → ∀ G, Q G → Disjoint F G → R (F∪G))
    (x : TotalFaceModule (k := k) P) (y : TotalFaceModule (k := k) Q) :
    idealTotalDifferential hR (totalFaceMulTensor P Q R hPQ (x⊗ₜ[k]y)) =
      totalFaceMulTensor P Q R hPQ ((idealTotalDifferential hP x)⊗ₜ[k]y) +
      totalFaceMulTensor P Q R hPQ ((totalFaceInvolute P x)⊗ₜ[k](idealTotalDifferential hQ y)) := by
  apply Subtype.ext
  exact CliffordAlgebra.contractLeft_mul _ x.val y.val

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FaceDegreeInvolute -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma totalFaceBasis_mem_degree (P : Finset V → Prop) (s : {s // P s}) :
    totalFaceBasis (k := k) P s ∈ totalFacePiece P s.val.card := by
  change (totalFaceBasis (k := k) P s).val ∈ Simplicial.Chains (k := k) P s.val.card
  rw [totalFaceBasis_val]
  exact Simplicial.basis_mem (k := k) s.property rfl

lemma involute_of_mem_face_degree (P : Finset V → Prop) (i : ℕ)
    {z : Simplicial.Ambient V k} (hz : z ∈ Simplicial.Chains P i) :
    CliffordAlgebra.involute z = (-1 : k)^i • z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,⟨hs,hcard⟩,rfl⟩ := hx
    simpa only [Simplicial.basis,hcard] using
      TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun k V) s
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy,smul_add]
  | smul c x hx ih =>
    rw [map_smul, ih]
    exact smul_comm c ((-1 : k)^i) x

lemma totalFaceInvolute_of_degree (P : Finset V → Prop) (i : ℕ)
    {x : TotalFaceModule (k := k) P} (hx : x ∈ totalFacePiece P i) :
    totalFaceInvolute P x = (-1 : k)^i • x := by
  apply Subtype.ext
  exact involute_of_mem_face_degree P i hx

/-- Every linear map that preserves the literal exterior degree commutes with
the grade involution, over every commutative ring, including characteristic two. -/
theorem totalFaceLinearMap_commutes_involute (P Q : Finset V → Prop)
    (F : TotalFaceModule (k := k) P →ₗ[k] TotalFaceModule (k := k) Q)
    (hF : ∀ i x, x ∈ totalFacePiece P i → F x ∈ totalFacePiece Q i) :
    (totalFaceInvolute Q).comp F = F.comp (totalFaceInvolute P) := by
  apply (totalFaceBasis P).ext
  intro s
  simp only [LinearMap.comp_apply]
  rw [totalFaceInvolute_of_degree Q s.val.card
      (hF _ _ (totalFaceBasis_mem_degree P s)),
    totalFaceInvolute_of_degree P s.val.card (totalFaceBasis_mem_degree P s),map_smul]

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerExteriorLift -/
section

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

theorem firstPowerSourceModule_eq {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) :
    TotalFaceModule (k := k)
        (quotientKoszulFaces (finitePredecessorFamily n E a.val)
          (β-finiteRowExponent n a.val)) =
      TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
          (β-finiteChainShift n (firstPowerTarget hβ).val)) := by
  simp only [firstPowerTarget,singletonChain_coefficient,singletonChain_shift]

/-- The identity on exterior elements, transporting the singleton-chain source
to the paper's literal predecessor quotient. -/
def firstPowerSourceCast {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) :
    TotalFaceModule (k := k)
        (quotientKoszulFaces (finitePredecessorFamily n E a.val)
          (β-finiteRowExponent n a.val)) →ₗ[k]
      TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
          (β-finiteChainShift n (firstPowerTarget hβ).val)) :=
  (LinearEquiv.ofEq _ _ (firstPowerSourceModule_eq (k := k) hβ)).toLinearMap

@[simp] lemma firstPowerSourceCast_val
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val))) :
    (firstPowerSourceCast (k := k) hβ x).val=x.val := by
  exact LinearEquiv.coe_ofEq_apply (firstPowerSourceModule_eq (k := k) hβ) x

lemma firstPowerSourceCast_differential
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val))) :
    quotientTotalDifferential
      (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
      (β-finiteChainShift n (firstPowerTarget hβ).val) (firstPowerSourceCast hβ x) =
    firstPowerSourceCast hβ
      (quotientTotalDifferential (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val) x) := by
  apply Subtype.ext
  change quotientFaceProjection _ _ (Simplicial.boundary x.val) =
    quotientFaceProjection _ _ (Simplicial.boundary x.val)
  simp only [firstPowerTarget,singletonChain_coefficient,singletonChain_shift]

/-- The corrected first-power section in the actual ideal Koszul face strand. -/
def firstPowerExteriorLift (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val) :
    TotalFaceModule (k := k)
        (quotientKoszulFaces (finitePredecessorFamily n E a.val)
          (β-finiteRowExponent n a.val)) →ₗ[k]
      TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β) :=
  (chainTotalEquiv hE 1 β k).toLinearMap.comp
    ((firstPowerChainSection hE hβ).comp (firstPowerSourceCast hβ))

theorem firstPowerExteriorLift_differential (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val))) :
    idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β)
      (firstPowerExteriorLift hE hβ x) =
    firstPowerExteriorLift hE hβ
      (quotientTotalDifferential (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val) x) := by
  have h := LinearMap.congr_fun (firstPowerChainSection_is_chain (k := k) hE hβ).2
    (firstPowerSourceCast hβ x)
  have hh := congrArg (chainTotalEquiv hE 1 β k) h
  simp only [LinearMap.comp_apply,chainTotalOrdinaryDifferential,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] at hh
  rw [firstPowerSourceCast_differential] at hh
  exact hh

lemma chainTotalEquiv_preserves_degree (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (i : ℕ)
    {x : ChainTotalModule n E m α k}
    (hx : x ∈ basisDegreePiece (chainTotalBasis n E m α k)
      (fun s => s.2.val.card) i) :
    chainTotalEquiv hE m α k x ∈
      totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i := by
  have hle : basisDegreePiece (chainTotalBasis n E m α k) (fun s => s.2.val.card) i ≤
      (totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i).comap
        (chainTotalEquiv hE m α k).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    change chainTotalEquiv hE m α k (chainTotalBasis n E m α k s) ∈
      totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i
    rw [chainTotalEquiv_basis]
    change (totalFaceBasis (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)
      (chainFaceEquiv hE α s)).val ∈
      Simplicial.Chains (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) i
    rw [totalFaceBasis_val]
    exact Simplicial.basis_mem (k := k) (chainFaceEquiv hE α s).property
      (by simpa only [chainFaceEquiv_val,Set.mem_setOf_eq] using hs)
  exact hle hx

theorem firstPowerExteriorLift_preserves_degree (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (i : ℕ)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val)))
    (hx : x ∈ totalFacePiece
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val)) i) :
    firstPowerExteriorLift hE hβ x ∈
      totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β) i := by
  have hxcast : firstPowerSourceCast (k := k) hβ x ∈ totalFacePiece
      (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
        (β-finiteChainShift n (firstPowerTarget hβ).val)) i := by
    change (firstPowerSourceCast (k := k) hβ x).val ∈ Simplicial.Chains (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
        (β-finiteChainShift n (firstPowerTarget hβ).val)) i
    rw [firstPowerSourceCast_val]
    change x.val ∈ Simplicial.Chains (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val)) i at hx
    simpa only [firstPowerTarget,singletonChain_coefficient,singletonChain_shift] using hx
  have hxcastBasis : firstPowerSourceCast (k := k) hβ x ∈
      basisDegreePiece (totalFaceBasis (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
          (β-finiteChainShift n (firstPowerTarget hβ).val))) (fun s => s.val.card) i := by
    rw [← totalFacePiece_eq_basisDegreePiece]
    exact hxcast
  have hsec : firstPowerChainSection (k := k) hE hβ (firstPowerSourceCast hβ x) ∈
      basisDegreePiece (chainTotalBasis n E 1 β k) (fun s => s.2.val.card) i :=
    firstPowerChainSection_preserves_degree (k := k) hE hβ i
      (firstPowerSourceCast (k := k) hβ x) hxcastBasis
  exact chainTotalEquiv_preserves_degree (k := k) hE 1 β i
    (x := firstPowerChainSection (k := k) hE hβ (firstPowerSourceCast hβ x)) hsec

theorem firstPowerExteriorLift_involute (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val) :
    (totalFaceInvolute
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β)).comp
        (firstPowerExteriorLift (k := k) hE hβ) =
    (firstPowerExteriorLift hE hβ).comp
      (totalFaceInvolute (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val))) :=
  totalFaceLinearMap_commutes_involute _ _ _
    (firstPowerExteriorLift_preserves_degree hE hβ)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.firstPowerExteriorLift_differential
#print axioms FourPapers.Sublattice.firstPowerExteriorLift_preserves_degree
#print axioms FourPapers.Sublattice.firstPowerExteriorLift_involute

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SeparatedFaceTensor -/
section

set_option autoImplicit false
set_option maxHeartbeats 40000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg
open scoped TensorProduct
universe u v

lemma finsetUnion_decidableEq {V : Type*} (D D' : DecidableEq V) (F G : Finset V) :
    @Union.union (Finset V) (@Finset.instUnion V D) F G = @Union.union (Finset V) (@Finset.instUnion V D') F G := by
  cases Subsingleton.elim D D'
  rfl

lemma integerUnit_cast_smul {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    (z : ℤˣ) (x : M) :
    (Units.map (Int.castRingHom k).toMonoidHom z) • x = z • x := by
  change ((z.val : k) • x) = z.val • x
  exact Int.cast_smul_eq_zsmul k z.val x

def signedBasisEquiv {I J k M N : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (b : Module.Basis I k M) (c : Module.Basis J k N)
    (e : I ≃ J) (ε : I → ℤˣ) : M ≃ₗ[k] N :=
  b.equiv ((c.reindex e.symm).unitsSMul
    (fun i => Units.map (Int.castRingHom k).toMonoidHom (ε i))) (Equiv.refl I)

lemma signedBasisEquiv_basis {I J k M N : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (b : Module.Basis I k M) (c : Module.Basis J k N)
    (e : I ≃ J) (ε : I → ℤˣ) (i : I) :
    signedBasisEquiv b c e ε (b i) = ε i • c (e i) := by
  simp only [signedBasisEquiv,Module.Basis.equiv_apply,Equiv.refl_apply,
    Module.Basis.unitsSMul_apply,Module.Basis.reindex_apply,Equiv.symm_symm,
    integerUnit_cast_smul]

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def splitFacePredicate (S : V → Prop) (P Q : Finset V → Prop) (F : Finset V) : Prop :=
  P (F.filter S) ∧ Q (F.filter (fun x => ¬ S x))

lemma face_filter_union_left (S : V → Prop) (F G : Finset V)
    (hF : ∀ x∈F, S x) (hG : ∀ x∈G, ¬S x) :
    (F∪G).filter S=F := by
  ext x
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hx,hS⟩
    rcases hx with hx | hx
    · exact hx
    · exact False.elim (hG x hx hS)
  · intro hx
    exact ⟨Or.inl hx,hF x hx⟩

lemma face_filter_union_right (S : V → Prop) (F G : Finset V)
    (hF : ∀ x∈F, S x) (hG : ∀ x∈G, ¬S x) :
    (F∪G).filter (fun x => ¬S x)=G := by
  ext x
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hx,hS⟩
    rcases hx with hx | hx
    · exact False.elim (hS (hF x hx))
    · exact hx
  · intro hx
    exact ⟨Or.inr hx,hG x hx⟩

def splitFaceIndexEquiv (S : V → Prop) (P Q : Finset V → Prop)
    (hP : ∀ F, P F → ∀ x∈F, S x) (hQ : ∀ G, Q G → ∀ x∈G, ¬S x) :
    ({F // P F} × {G // Q G}) ≃ {H // splitFacePredicate S P Q H} where
  toFun a := ⟨a.1.val∪a.2.val,by
    rw [splitFacePredicate,face_filter_union_left S _ _ (hP _ a.1.property) (hQ _ a.2.property),
      face_filter_union_right S _ _ (hP _ a.1.property) (hQ _ a.2.property)]
    exact ⟨a.1.property,a.2.property⟩⟩
  invFun H := (⟨H.val.filter S,H.property.1⟩,⟨H.val.filter (fun x => ¬S x),H.property.2⟩)
  left_inv a := by
    apply Prod.ext <;> apply Subtype.ext
    · exact face_filter_union_left S _ _ (hP _ a.1.property) (hQ _ a.2.property)
    · exact face_filter_union_right S _ _ (hP _ a.1.property) (hQ _ a.2.property)
  right_inv H := by
    apply Subtype.ext
    ext x
    by_cases hx : S x <;> simp [hx]

lemma splitFaces_disjoint (S : V → Prop) (P Q : Finset V → Prop)
    (hP : ∀ F, P F → ∀ x∈F, S x) (hQ : ∀ G, Q G → ∀ x∈G, ¬S x)
    (F : {F // P F}) (G : {G // Q G}) : Disjoint F.val G.val := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hQ _ G.property x hy (hP _ F.property x hx)

lemma splitFacePredicate_union (S : V → Prop) (P Q : Finset V → Prop)
    (hP : ∀ F, P F → ∀ x∈F, S x) (hQ : ∀ G, Q G → ∀ x∈G, ¬S x) :
    ∀ F, P F → ∀ G, Q G → Disjoint F G → splitFacePredicate S P Q (F∪G) := by
  intro F hF G hG _
  exact (splitFaceIndexEquiv S P Q hP hQ (⟨F,hF⟩,⟨G,hG⟩)).property

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SeparatedFaceDifferential -/
section

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Projection onto the indicated actual exterior face basis. -/
def faceProjection (P : Finset V → Prop) : Module.End k (Simplicial.Ambient V k) :=
  relativeProjection Simplicial.basis P (fun _ => False)

@[simp] lemma faceProjection_basis (P : Finset V → Prop) (F : Finset V) :
    faceProjection (k := k) P (Simplicial.basis F) =
      if P F then Simplicial.basis F else 0 := by
  simp [faceProjection]

lemma faceProjection_mem (P : Finset V → Prop) (x : Simplicial.Ambient V k) :
    faceProjection P x ∈ TotalFaceModule (k := k) P := by
  simpa only [and_true,not_false_eq_true,TotalFaceModule,faceProjection] using
    relativeProjection_mem (Simplicial.basis (k := k)) P (fun _ => False) x

lemma faceProjection_eq_self (P : Finset V → Prop) {x : Simplicial.Ambient V k}
    (hx : x ∈ TotalFaceModule (k := k) P) : faceProjection P x=x := by
  apply relativeProjection_eq_self
  simpa only [and_true,not_false_eq_true] using hx

lemma quotientFaceProjection_eq_faceProjection (B : Family V) (α : Exponent V) :
    quotientFaceProjection (k := k) B α = faceProjection (quotientKoszulFaces B α) := by
  simp only [quotientFaceProjection,faceProjection,relativeProjection,quotientKoszulFaces,
    not_false_eq_true,and_true]

def projectedTotalDifferential (P : Finset V → Prop) :
    Module.End k (TotalFaceModule (k := k) P) :=
  ((faceProjection P).comp (Simplicial.boundary.comp
    (TotalFaceModule (k := k) P).subtype)).codRestrict _ (fun x => faceProjection_mem _ _)

@[simp] lemma projectedTotalDifferential_val (P : Finset V → Prop)
    (x : TotalFaceModule (k := k) P) :
    (projectedTotalDifferential P x).val = faceProjection P (Simplicial.boundary x.val) := rfl

lemma quotientTotalDifferential_eq_projected (B : Family V) (α : Exponent V) :
    quotientTotalDifferential (k := k) B α =
      projectedTotalDifferential (quotientKoszulFaces B α) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [quotientTotalDifferential_val,projectedTotalDifferential_val,
    quotientFaceProjection_eq_faceProjection]

def facesOn (S : V → Prop) (F : Finset V) : Prop := ∀ x∈F, S x

lemma facesOn_downward (S : V → Prop) : Simplicial.Downward (facesOn S) :=
  fun _ _ h hF x hx => hF x (h hx)

lemma faceSpan_supported (S : V → Prop) (P : Finset V → Prop)
    (hP : ∀ F, P F → ∀ x∈F, S x) {x : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (k := k) P) : x∈TotalFaceModule (facesOn S) :=
  Submodule.span_mono (Set.image_mono (fun F hF => hP F hF)) hx

/-- Coordinate projection respects exterior multiplication on disjoint variable supports. -/
lemma faceProjection_mul_separated (S : V → Prop) (P Q : Finset V → Prop)
    {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (k := k) (facesOn S))
    (hy : y∈TotalFaceModule (k := k) (facesOn (fun z => ¬S z))) :
    faceProjection (splitFacePredicate S P Q) (x*y) =
      faceProjection P x * faceProjection Q y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F,hF,rfl⟩ := hx
    change facesOn S F at hF
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨G,hG,rfl⟩ := hy
      change facesOn (fun z => ¬S z) G at hG
      have hd : Disjoint F G := Finset.disjoint_left.mpr (fun z hz hz' => hG z hz' (hF z hz))
      rw [faceBasis_mul_of_disjoint F G hd]
      simp only [Units.smul_def,map_zsmul,faceProjection_basis,splitFacePredicate,
        face_filter_union_left S F G hF hG,face_filter_union_right S F G hF hG]
      by_cases hp : P F <;> by_cases hq : Q G <;>
        simp [hp,hq,faceBasis_mul_of_disjoint F G hd,Units.smul_def]
    | zero => simp
    | add y z hy hz ihy ihz => simp only [mul_add,map_add,ihy,ihz]
    | smul c y hy ih => simp only [mul_smul_comm,map_smul,ih]
  | zero => simp
  | add x z hx hz ihx ihz => simp only [add_mul,map_add,ihx,ihz]
  | smul c x hx ih => simp only [smul_mul_assoc,map_smul,ih]

/-- The literal exterior product is a chain map from the signed tensor differential,
including the projections defining the quotient differentials. -/
theorem projectedTotalDifferential_mul_separated
    (S : V → Prop) (P Q : Finset V → Prop)
    (hP : ∀ F, P F → ∀ x∈F, S x) (hQ : ∀ G, Q G → ∀ x∈G, ¬S x)
    (x : TotalFaceModule (k := k) P) (y : TotalFaceModule (k := k) Q) :
    projectedTotalDifferential (splitFacePredicate S P Q)
        (totalFaceMulTensor P Q (splitFacePredicate S P Q)
          (splitFacePredicate_union S P Q hP hQ) (x⊗ₜ[k]y)) =
      totalFaceMulTensor P Q (splitFacePredicate S P Q)
        (splitFacePredicate_union S P Q hP hQ) ((projectedTotalDifferential P x)⊗ₜ[k]y) +
      totalFaceMulTensor P Q (splitFacePredicate S P Q)
        (splitFacePredicate_union S P Q hP hQ)
        ((totalFaceInvolute P x)⊗ₜ[k](projectedTotalDifferential Q y)) := by
  have hx := faceSpan_supported S P hP x.property
  have hy := faceSpan_supported (fun z => ¬S z) Q hQ y.property
  have hdx := boundary_mem_basisSpan (facesOn_downward S) hx
  have hdy := boundary_mem_basisSpan (facesOn_downward (fun z => ¬S z)) hy
  have hix := faceSpan_involute_mem (facesOn S) hx
  apply Subtype.ext
  change faceProjection (splitFacePredicate S P Q) (Simplicial.boundary (x.val*y.val)) =
    faceProjection P (Simplicial.boundary x.val)*y.val +
      CliffordAlgebra.involute x.val*faceProjection Q (Simplicial.boundary y.val)
  rw [show Simplicial.boundary (x.val*y.val) =
      Simplicial.boundary x.val*y.val + CliffordAlgebra.involute x.val*Simplicial.boundary y.val
        from CliffordAlgebra.contractLeft_mul _ _ _,map_add,
    faceProjection_mul_separated S P Q hdx hy,
    faceProjection_mul_separated S P Q hix hdy,
    faceProjection_eq_self Q y.property,
    faceProjection_eq_self P (faceSpan_involute_mem P x.property)]

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteFaceTensor -/
section

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def faceListUnion : List (Finset V) → Finset V
  | [] => ∅
  | F::L => F∪faceListUnion L

@[simp] lemma mem_faceListUnion (L : List (Finset V)) (x : V) :
    x∈faceListUnion L ↔ ∃F∈L, x∈F := by
  induction L with
  | nil => simp [faceListUnion]
  | cons F L ih => simp [faceListUnion,ih,or_and_right,exists_or]

lemma disjoint_faceListUnion (F : Finset V) (L : List (Finset V))
    (h : ∀G∈L,Disjoint F G) : Disjoint F (faceListUnion L) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨G,hG,hxG⟩ := (mem_faceListUnion L x).mp hy
  exact Finset.disjoint_left.mp (h G hG) hx hxG

def faceListSign : (L : List (Finset V)) → L.Pairwise Disjoint → ℤˣ
  | [],_ => 1
  | F::L,h => faceListSign L (List.pairwise_cons.mp h).2 *
      faceWedgeSign F (faceListUnion L)
        (disjoint_faceListUnion F L (List.pairwise_cons.mp h).1)

lemma faceBasis_empty : Simplicial.basis (V := V) (k := k) ∅=1 := by
  simp [Simplicial.basis,Module.Basis.exteriorAlgebra_eq_prod_map_sort]

theorem faceBasis_list_product (L : List (Finset V)) (h : L.Pairwise Disjoint) :
    (L.map (Simplicial.basis (k := k))).prod =
      faceListSign L h • Simplicial.basis (faceListUnion L) := by
  induction L with
  | nil => simp [faceListUnion,faceListSign,faceBasis_empty]
  | cons F L ih =>
    rw [List.map_cons,List.prod_cons,ih (List.pairwise_cons.mp h).2]
    rw [mul_smul_comm,faceBasis_mul_of_disjoint F (faceListUnion L)
      (disjoint_faceListUnion F L (List.pairwise_cons.mp h).1),smul_smul]
    rfl

variable {m : ℕ}

def finiteFaceUnion (f : Fin m → Finset V) : Finset V := Finset.univ.biUnion f

@[simp] lemma mem_finiteFaceUnion (f : Fin m → Finset V) (x : V) :
    x∈finiteFaceUnion f ↔ ∃p,x∈f p := by
  simp [finiteFaceUnion]

lemma faceListUnion_ofFn (f : Fin m → Finset V) :
    faceListUnion (List.ofFn f)=finiteFaceUnion f := by
  ext x
  simp only [mem_faceListUnion,mem_finiteFaceUnion,List.mem_ofFn]
  constructor
  · rintro ⟨F,⟨p,rfl⟩,hp⟩
    exact ⟨p,hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨f p,⟨p,rfl⟩,hp⟩

def separatedFamilyFaces (S : Fin m → V → Prop) (P : Fin m → Finset V → Prop)
    (F : Finset V) : Prop :=
  (∀x∈F,∃p,S p x) ∧ ∀p,P p (F.filter (S p))

lemma finiteFaceUnion_filter (S : Fin m → V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (f : Fin m → Finset V) (hf : ∀p x,x∈f p → S p x) (p : Fin m) :
    (finiteFaceUnion f).filter (S p)=f p := by
  ext x
  simp only [Finset.mem_filter,mem_finiteFaceUnion]
  constructor
  · rintro ⟨⟨q,hq⟩,hp⟩
    have he : q=p := by
      by_contra hn
      exact hS q p hn x (hf q x hq) hp
    simpa only [he] using hq
  · intro hp
    exact ⟨⟨p,hp⟩,hf p x hp⟩

def finiteFaceIndexEquiv (S : Fin m → V → Prop) (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (hP : ∀p F,P p F → ∀x∈F,S p x) :
    (∀p,{F // P p F}) ≃ {F // separatedFamilyFaces S P F} where
  toFun f := ⟨finiteFaceUnion (fun p => (f p).val),by
    constructor
    · intro x hx
      obtain ⟨p,hp⟩ := (mem_finiteFaceUnion _ x).mp hx
      exact ⟨p,hP p _ (f p).property x hp⟩
    · intro p
      rw [finiteFaceUnion_filter S hS _ (fun q x hx => hP q _ (f q).property x hx)]
      exact (f p).property⟩
  invFun F p := ⟨F.val.filter (S p),F.property.2 p⟩
  left_inv f := by
    funext p
    apply Subtype.ext
    exact finiteFaceUnion_filter S hS _ (fun q x hx => hP q _ (f q).property x hx) p
  right_inv F := by
    apply Subtype.ext
    ext x
    simp only [mem_finiteFaceUnion,Finset.mem_filter]
    constructor
    · rintro ⟨p,hx,_⟩
      exact hx
    · intro hx
      obtain ⟨p,hp⟩ := F.property.1 x hx
      exact ⟨p,hx,hp⟩

lemma finiteFamily_faces_pairwise (S : Fin m → V → Prop) (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (hP : ∀p F,P p F → ∀x∈F,S p x) (f : ∀p,{F // P p F}) :
    (List.ofFn (fun p => (f p).val)).Pairwise Disjoint := by
  apply List.pairwise_ofFn.mpr
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hS p q (ne_of_lt hpq) x (hP p _ (f p).property x hx) (hP q _ (f q).property x hy)

def finiteFaceTensorEquiv (S : Fin m → V → Prop) (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (hP : ∀p F,P p F → ∀x∈F,S p x) :
    (⨂[k] p,TotalFaceModule (k := k) (P p)) ≃ₗ[k]
      TotalFaceModule (k := k) (separatedFamilyFaces S P) :=
  signedBasisEquiv (k := k) (Basis.piTensorProduct (fun p => totalFaceBasis (k := k) (P p)))
    (totalFaceBasis (k := k) (separatedFamilyFaces S P)) (finiteFaceIndexEquiv S P hS hP)
    (fun f => faceListSign _ (finiteFamily_faces_pairwise S P hS hP f))

/-- Actual ordered multiplication of the factors in the exterior algebra. -/
def finiteFaceProduct (P : Fin m → Finset V → Prop) :
    (⨂[k] p,TotalFaceModule (k := k) (P p)) →ₗ[k] Simplicial.Ambient V k :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebraFin k m (Simplicial.Ambient V k)).compLinearMap
    (fun p => (TotalFaceModule (k := k) (P p)).subtype))

theorem finiteFaceTensorEquiv_actual_product (S : Fin m → V → Prop)
    (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (hP : ∀p F,P p F → ∀x∈F,S p x) :
    (TotalFaceModule (k := k) (separatedFamilyFaces S P)).subtype.comp
        (finiteFaceTensorEquiv S P hS hP).toLinearMap = finiteFaceProduct P := by
  apply (Basis.piTensorProduct (fun p => totalFaceBasis (k := k) (P p))).ext
  intro f
  change ((finiteFaceTensorEquiv (k := k) S P hS hP)
    ((Basis.piTensorProduct (fun p => totalFaceBasis (k := k) (P p))) f)).val = _
  unfold finiteFaceTensorEquiv
  rw [signedBasisEquiv_basis,Basis.piTensorProduct_apply]
  simp only [Submodule.coe_smul_of_tower,totalFaceBasis_val,finiteFaceProduct,
    PiTensorProduct.lift.tprod,MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebraFin_apply,Submodule.subtype_apply]
  have h := faceBasis_list_product (k := k) _ (finiteFamily_faces_pairwise S P hS hP f)
  simpa only [List.map_ofFn,Function.comp_def,faceListUnion_ofFn,
    finiteFaceIndexEquiv,Equiv.coe_fn_mk] using h.symm

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.OrderedDGAProduct -/
section

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace FourPapers.Sublattice
open Classical
open scoped TensorProduct

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]

def orderedDerivativeTerm {m : ℕ} (D : Module.End K A) (σ : A →ₐ[K] A)
    (x : Fin m → A) (p : Fin m) : A :=
  (List.ofFn (fun q => if q<p then σ (x q) else if q=p then D (x q) else x q)).prod

/-- The signed Leibniz formula for every finite ordered product. -/
theorem orderedProduct_leibniz (D : Module.End K A) (σ : A →ₐ[K] A)
    (h1 : D 1=0) (hmul : ∀x y,D (x*y)=D x*y+σ x*D y)
    (m : ℕ) (x : Fin m → A) :
    D (List.ofFn x).prod = ∑p,orderedDerivativeTerm D σ x p := by
  induction m with
  | zero => simp [h1]
  | succ m ih =>
    rw [List.ofFn_succ,List.prod_cons,hmul,ih,Fin.sum_univ_succ]
    have hzero : orderedDerivativeTerm D σ x 0 =
        D (x 0)*(List.ofFn (fun q => x q.succ)).prod := by
      simp [orderedDerivativeTerm,List.ofFn_succ]
    have hsucc (p : Fin m) : orderedDerivativeTerm D σ x p.succ =
        σ (x 0)*orderedDerivativeTerm D σ (fun q => x q.succ) p := by
      simp [orderedDerivativeTerm,List.ofFn_succ]
    rw [hzero]
    simp_rw [hsucc]
    rw [Finset.mul_sum]

variable {m : ℕ} {M : Fin m → Type*}
  [∀p,AddCommGroup (M p)] [∀p,Module K (M p)]

def signedTensorFactor (d ι : ∀p,Module.End K (M p)) (p q : Fin m) :
    Module.End K (M q) := if q<p then ι q else if q=p then d q else LinearMap.id

def signedTensorDifferential (d ι : ∀p,Module.End K (M p)) :
    Module.End K (⨂[K] p,M p) :=
  ∑p,PiTensorProduct.map (signedTensorFactor d ι p)

def orderedLiftProduct (f : ∀p,M p →ₗ[K] A) : (⨂[K] p,M p) →ₗ[K] A :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebraFin K m A).compLinearMap f)

@[simp] lemma orderedLiftProduct_tprod (f : ∀p,M p →ₗ[K] A) (x : ∀p,M p) :
    orderedLiftProduct f (⨂ₜ[K] p,x p)=(List.ofFn (fun p => f p (x p))).prod := by
  simp only [orderedLiftProduct,PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebraFin_apply]

theorem orderedLiftProduct_is_chain (D : Module.End K A) (σ : A →ₐ[K] A)
    (h1 : D 1=0) (hmul : ∀x y,D (x*y)=D x*y+σ x*D y)
    (d ι : ∀p,Module.End K (M p)) (f : ∀p,M p →ₗ[K] A)
    (hd : ∀p x,D (f p x)=f p (d p x))
    (hι : ∀p x,σ (f p x)=f p (ι p x)) :
    D.comp (orderedLiftProduct f) =
      (orderedLiftProduct f).comp (signedTensorDifferential d ι) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,orderedLiftProduct_tprod,
    signedTensorDifferential,LinearMap.sum_apply,map_sum,PiTensorProduct.map_tprod]
  rw [orderedProduct_leibniz D σ h1 hmul]
  apply Finset.sum_congr rfl
  intro p _
  unfold orderedDerivativeTerm
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext q
  by_cases hqp : q<p
  · simp [signedTensorFactor,hqp,hι]
  · by_cases he : q=p
    · simp [signedTensorFactor,hqp,he,hd]
    · simp [signedTensorFactor,hqp,he]

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteFaceDifferential -/
section

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] {m : ℕ}

def faceProjectionTo (P Q : Finset V → Prop) :
    TotalFaceModule (k := k) P →ₗ[k] TotalFaceModule (k := k) Q :=
  ((faceProjection Q).domRestrict (TotalFaceModule (k := k) P)).codRestrict _
    (fun x => faceProjection_mem Q x.val)

@[simp] lemma faceProjectionTo_val (P Q : Finset V → Prop)
    (x : TotalFaceModule (k := k) P) :
    (faceProjectionTo P Q x).val=faceProjection Q x.val := rfl

lemma separatedFamilyFaces_union_iff (S : Fin m → V → Prop)
    (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (f : Fin m → Finset V) (hf : ∀p x,x∈f p → S p x) :
    separatedFamilyFaces S P (finiteFaceUnion f) ↔ ∀p,P p (f p) := by
  constructor
  · intro h p
    simpa only [finiteFaceUnion_filter S hS f hf] using h.2 p
  · intro h
    constructor
    · intro x hx
      obtain ⟨p,hp⟩ := (mem_finiteFaceUnion f x).mp hx
      exact ⟨p,hf p x hp⟩
    · intro p
      rw [finiteFaceUnion_filter S hS f hf]
      exact h p

theorem finiteFaceProjection_product_map (S : Fin m → V → Prop)
    (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x) :
    (faceProjection (separatedFamilyFaces S P)).comp
        (finiteFaceProduct (k := k) (fun p => facesOn (S p))) =
      (finiteFaceProduct P).comp
        (PiTensorProduct.map (fun p => faceProjectionTo (facesOn (S p)) (P p))) := by
  apply (Basis.piTensorProduct (fun p => totalFaceBasis (k := k) (facesOn (S p)))).ext
  intro f
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod,finiteFaceProduct,PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebraFin_apply,
    Submodule.subtype_apply,totalFaceBasis_val,faceProjectionTo_val]
  have hpair := finiteFamily_faces_pairwise S (fun p => facesOn (S p)) hS
    (fun _ _ h => h) f
  have hprod : (List.ofFn (fun p => Simplicial.basis (k := k) (f p).val)).prod =
      faceListSign _ hpair • Simplicial.basis (finiteFaceUnion (fun p => (f p).val)) := by
    simpa only [List.map_ofFn,Function.comp_def,faceListUnion_ofFn] using faceBasis_list_product _ hpair
  rw [hprod]
  simp only [Units.smul_def,map_zsmul,faceProjection_basis]
  have hr := separatedFamilyFaces_union_iff S P hS (fun p => (f p).val)
    (fun p x hx => (f p).property x hx)
  by_cases hall : ∀p,P p (f p).val
  · rw [if_pos (hr.mpr hall)]
    simp only [hall,ite_true]
    exact hprod.symm
  · rw [if_neg (fun h => hall (hr.mp h)),zsmul_zero]
    obtain ⟨p,hp⟩ := not_forall.mp hall
    symm
    apply List.prod_eq_zero
    exact List.mem_ofFn.mpr ⟨p,by simp only [if_neg hp]⟩

lemma finiteFaceProjection_product (S : Fin m → V → Prop)
    (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (x : Fin m → Simplicial.Ambient V k)
    (hx : ∀p,x p∈TotalFaceModule (k := k) (facesOn (S p))) :
    faceProjection (separatedFamilyFaces S P) (List.ofFn x).prod =
      (List.ofFn (fun p => faceProjection (P p) (x p))).prod := by
  have h := LinearMap.congr_fun (finiteFaceProjection_product_map (k := k) S P hS)
    (⨂ₜ[k] p,(⟨x p,hx p⟩ : TotalFaceModule (k := k) (facesOn (S p))))
  simpa only [LinearMap.comp_apply,finiteFaceProduct,PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebraFin_apply,
    PiTensorProduct.map_tprod,Submodule.subtype_apply,faceProjectionTo_val] using h

def finiteFaceTensorDifferential (P : Fin m → Finset V → Prop) :
    Module.End k (⨂[k] p,TotalFaceModule (k := k) (P p)) :=
  signedTensorDifferential (fun p => projectedTotalDifferential (P p))
    (fun p => totalFaceInvolute (P p))

/-- The full projected tensor differential agrees with the actual exterior boundary. -/
theorem finiteFaceProduct_differential (S : Fin m → V → Prop)
    (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (hP : ∀p F,P p F → ∀x∈F,S p x) :
    (faceProjection (separatedFamilyFaces S P)).comp
        (Simplicial.boundary.comp (finiteFaceProduct (k := k) P)) =
      (finiteFaceProduct P).comp (finiteFaceTensorDifferential P) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,finiteFaceProduct,PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebraFin_apply,
    Submodule.subtype_apply,finiteFaceTensorDifferential,signedTensorDifferential,
    LinearMap.sum_apply,map_sum,PiTensorProduct.map_tprod]
  rw [orderedProduct_leibniz Simplicial.boundary CliffordAlgebra.involute
    (CliffordAlgebra.contractLeft_one _ _) (CliffordAlgebra.contractLeft_mul _) m]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  unfold orderedDerivativeTerm
  let y : Fin m → Simplicial.Ambient V k :=
    fun q => if q<p then CliffordAlgebra.involute (x q).val
      else if q=p then Simplicial.boundary (x q).val else (x q).val
  have hy : ∀q,y q∈TotalFaceModule (k := k) (facesOn (S q)) := by
    intro q
    have hx := faceSpan_supported (S q) (P q) (hP q) (x q).property
    dsimp [y]
    split_ifs
    · exact faceSpan_involute_mem _ hx
    · exact boundary_mem_basisSpan (facesOn_downward _) hx
    · exact hx
  rw [finiteFaceProjection_product S P hS y hy]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext q
  by_cases hqp : q<p
  · simp only [y,hqp,ite_true,signedTensorFactor]
    exact faceProjection_eq_self (P q) (faceSpan_involute_mem (P q) (x q).property)
  · by_cases he : q=p
    · subst q
      simp only [y,lt_self_iff_false,ite_false,ite_true,signedTensorFactor,
        projectedTotalDifferential_val]
    · simp only [y,hqp,ite_false,he,signedTensorFactor,LinearMap.id_apply]
      exact faceProjection_eq_self (P q) (x q).property

theorem finiteFaceTensorEquiv_is_chain (S : Fin m → V → Prop)
    (P : Fin m → Finset V → Prop)
    (hS : ∀p q,p≠q → ∀x,S p x → ¬S q x)
    (hP : ∀p F,P p F → ∀x∈F,S p x) :
    (projectedTotalDifferential (separatedFamilyFaces S P)).comp
        (finiteFaceTensorEquiv (k := k) S P hS hP).toLinearMap =
      (finiteFaceTensorEquiv S P hS hP).toLinearMap.comp (finiteFaceTensorDifferential P) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have he := finiteFaceTensorEquiv_actual_product (k := k) S P hS hP
  have h := LinearMap.congr_fun (finiteFaceProduct_differential (k := k) S P hS hP) x
  simpa only [←he,LinearMap.comp_apply,Submodule.subtype_apply,
    LinearEquiv.coe_coe,projectedTotalDifferential_val] using h

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BlockFaceFactorization -/
section

set_option autoImplicit false
set_option maxHeartbeats 20000
noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

lemma contains_filter_iff_of_supported {V : Type u} [Fintype V] [DecidableEq V]
    (B : Family V) (p : V → Prop) [DecidablePred p]
    (hB : ∀ b∈B, ∀ x, b x≠0 → p x) (v : Exponent V) :
    Contains B (v.filter p) ↔ Contains B v := by
  constructor
  · rintro ⟨b,hb,hbv⟩
    refine ⟨b,hb,fun x => (hbv x).trans ?_⟩
    by_cases hp : p x <;> simp [Finsupp.filter_apply,hp]
  · rintro ⟨b,hb,hbv⟩
    refine ⟨b,hb,?_⟩
    intro x
    by_cases hx : b x=0
    · simp [hx]
    · simpa [Finsupp.filter_apply,hB b hb x hx] using hbv x

lemma filter_residual_face {V : Type u} [Fintype V] [LinearOrder V]
    [DecidableEq V] (p : V → Prop) [DecidablePred p]
    (v : Exponent V) (F : Finset V) :
    (v-faceExponent F).filter p = v.filter p-faceExponent (F.filter p) := by
  ext x
  by_cases hp : p x
  · by_cases hF : x∈F <;> simp [Finsupp.filter_apply,faceExponent_apply,hp,hF]
  · simp [Finsupp.filter_apply,faceExponent_apply,hp]

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

def finiteBlockFace (w : FiniteMultichain n E m) (p : Fin m)
    (F : Finset (FiniteVariable.{u} n)) : Finset (FiniteVariable.{u} n) :=
  F.filter (finiteCrosses w p)

@[simp] lemma mem_finiteBlockFace (w : FiniteMultichain n E m) (p : Fin m)
    (F : Finset (FiniteVariable.{u} n)) (x : FiniteVariable.{u} n) :
    x∈finiteBlockFace w p F ↔ x∈F ∧ finiteCrosses w p x := by
  simp only [finiteBlockFace,Finset.mem_filter]

lemma finiteBlockFace_pairwise_disjoint (w : FiniteMultichain n E m)
    (F : Finset (FiniteVariable.{u} n)) {p q : Fin m} (hpq : p≠q) :
    Disjoint (finiteBlockFace w p F) (finiteBlockFace w q F) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hpq (finiteCrosses_unique (mem_finiteBlockFace w p F x|>.mp hx).2
    (mem_finiteBlockFace w q F x|>.mp hy).2)

lemma finiteBlockDegree_residual_face (w : FiniteMultichain n E m) (p : Fin m)
    (v : Exponent (FiniteVariable.{u} n)) (F : Finset (FiniteVariable.{u} n)) :
    finiteBlockDegree w p (v-faceExponent F) =
      finiteBlockDegree w p v-faceExponent (finiteBlockFace w p F) :=
  filter_residual_face (finiteCrosses w p) v F

lemma finiteBlock_contains_degree (w : FiniteMultichain n E m) (p : Fin m)
    (v : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteBlockFamily w p) (finiteBlockDegree w p v) ↔
      Contains (finiteBlockFamily w p) v :=
  contains_filter_iff_of_supported (finiteBlockFamily w p) (finiteCrosses w p)
    (fun b hb x hx => finiteBlockFamily_variables w p hb x hx) v

theorem finiteChainCoefficient_contains_blockDegrees (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoefficientFamily n w) v ↔
      ∃ p, Contains (finitePredecessorFamily n E (w.val p).val) (finiteBlockDegree w p v) := by
  rw [finiteChainCoefficient_contains_blocks hE]
  apply exists_congr
  intro p
  rw [finitePredecessor_block_restriction hE w p _ (finiteBlockDegree_supported w p v),
    finiteBlock_contains_degree]

lemma finiteBlockFace_full (w : FiniteMultichain n E m) (p : Fin m)
    {v : Exponent (FiniteVariable.{u} n)} {F : Finset (FiniteVariable.{u} n)}
    (hF : fullKoszulFaces v F) :
    fullKoszulFaces (finiteBlockDegree w p v) (finiteBlockFace w p F) := by
  intro x
  by_cases hp : finiteCrosses w p x
  · have hh := hF x
    by_cases hx : x∈F <;>
      simpa [faceExponent_apply,finiteBlockDegree_apply,hp,hx] using hh
  · simp [faceExponent_apply,finiteBlockDegree_apply,hp]

theorem finiteChainQuotientFaces_blocks (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (F : Finset (FiniteVariable.{u} n)) :
    quotientKoszulFaces (finiteChainCoefficientFamily n w) v F ↔
      fullKoszulFaces v F ∧ ∀ p,
        quotientKoszulFaces (finitePredecessorFamily n E (w.val p).val)
          (finiteBlockDegree w p v) (finiteBlockFace w p F) := by
  constructor
  · intro hF
    refine ⟨hF.1,fun p => ⟨finiteBlockFace_full w p hF.1,?_⟩⟩
    intro hp
    apply hF.2
    apply (finiteChainCoefficient_contains_blockDegrees hE w _).mpr
    refine ⟨p,?_⟩
    simpa only [forbiddenKoszulFaces,finiteBlockDegree_residual_face] using hp
  · rintro ⟨hF,hblocks⟩
    refine ⟨hF,?_⟩
    intro hbad
    obtain ⟨p,hp⟩ := (finiteChainCoefficient_contains_blockDegrees hE w _).mp hbad
    apply (hblocks p).2
    simpa only [forbiddenKoszulFaces,finiteBlockDegree_residual_face] using hp

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CrossingBlockTensor -/
section

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

def facePredicateEquiv {V : Type u} [Fintype V] [LinearOrder V]
    (P Q : Finset V → Prop) (h : ∀F,P F↔Q F) :
    TotalFaceModule (k := k) P ≃ₗ[k] TotalFaceModule (k := k) Q where
  toFun x := ⟨x.val,Submodule.span_mono (Set.image_mono (fun F hF => (h F).mp hF)) x.property⟩
  invFun x := ⟨x.val,Submodule.span_mono (Set.image_mono (fun F hF => (h F).mpr hF)) x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma facePredicateEquiv_projected {V : Type u} [Fintype V] [LinearOrder V]
    (P Q : Finset V → Prop) (h : ∀F,P F↔Q F) :
    (projectedTotalDifferential Q).comp (facePredicateEquiv (k := k) P Q h).toLinearMap =
      (facePredicateEquiv P Q h).toLinearMap.comp (projectedTotalDifferential P) := by
  have he : P=Q := funext (fun F => propext (h F))
  subst Q
  rfl

def CrossingCovered (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) : Prop :=
  ∀x,v x≠0 → ∃p,finiteCrosses w p x

def crossingBlockFaces (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m) : Finset (FiniteVariable.{u} n) → Prop :=
  quotientKoszulFaces (finitePredecessorFamily n E (w.val p).val) (finiteBlockDegree w p v)

lemma crossingBlockFaces_supported (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (F : Finset (FiniteVariable.{u} n)) (hF : crossingBlockFaces w v p F)
    (x : FiniteVariable.{u} n) (hx : x∈F) : finiteCrosses w p x := by
  have he := hF.1 x
  have hne : finiteBlockDegree w p v x≠0 := by
    simpa only [faceExponent_apply,if_pos hx,Nat.one_le_iff_ne_zero] using he
  exact finiteBlockDegree_supported w p v x hne

theorem crossingBlockFaces_factorization (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) (F : Finset (FiniteVariable.{u} n)) :
    quotientKoszulFaces (finiteChainCoefficientFamily n w) v F ↔
      separatedFamilyFaces (finiteCrosses w) (crossingBlockFaces w v) F := by
  rw [finiteChainQuotientFaces_blocks hE w v F]
  constructor
  · rintro ⟨hF,hP⟩
    refine ⟨?_,hP⟩
    intro x hx
    apply hv x
    have he := hF x
    simpa only [faceExponent_apply,if_pos hx,Nat.one_le_iff_ne_zero] using he
  · rintro ⟨hcov,hP⟩
    refine ⟨?_,hP⟩
    intro x
    by_cases hx : x∈F
    · obtain ⟨p,hp⟩ := hcov x hx
      have he := (hP p).1 x
      simpa only [faceExponent_apply,Finset.mem_filter,hx,hp,and_self,ite_true,
        finiteBlockDegree_apply] using he
    · simp only [faceExponent_apply,if_neg hx,zero_le]

/-- The complete coefficient strand is a tensor product over all crossing steps. -/
def crossingBlockTensorEquiv (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) :
    (⨂[k] p,TotalFaceModule (k := k) (crossingBlockFaces w v p)) ≃ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w) v) :=
  (finiteFaceTensorEquiv (finiteCrosses w) (crossingBlockFaces w v)
    (fun p q hpq x hp hq => hpq (finiteCrosses_unique hp hq))
    (crossingBlockFaces_supported w v)).trans
    (facePredicateEquiv _ _ (fun F => (crossingBlockFaces_factorization hE w v hv F).symm))

theorem crossingBlockTensorEquiv_actual_product (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) :
    (TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w) v)).subtype.comp
      (crossingBlockTensorEquiv hE w v hv).toLinearMap = finiteFaceProduct (crossingBlockFaces w v) := by
  exact finiteFaceTensorEquiv_actual_product (finiteCrosses w) (crossingBlockFaces w v)
    (fun p q hpq x hp hq => hpq (finiteCrosses_unique hp hq))
    (crossingBlockFaces_supported w v)

theorem crossingBlockTensorEquiv_is_chain (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) :
    (quotientTotalDifferential (finiteChainCoefficientFamily n w) v).comp
        (crossingBlockTensorEquiv (k := k) hE w v hv).toLinearMap =
      (crossingBlockTensorEquiv hE w v hv).toLinearMap.comp
        (finiteFaceTensorDifferential (crossingBlockFaces w v)) := by
  rw [quotientTotalDifferential_eq_projected]
  let S := finiteCrosses w
  let P := crossingBlockFaces w v
  have hS : ∀p q,p≠q → ∀x,S p x → ¬S q x :=
    fun p q hpq x hp hq => hpq (finiteCrosses_unique hp hq)
  let e := finiteFaceTensorEquiv (k := k) S P hS (crossingBlockFaces_supported w v)
  let hPred := fun F => (crossingBlockFaces_factorization hE w v hv F).symm
  let c := facePredicateEquiv (k := k) (separatedFamilyFaces S P)
    (quotientKoszulFaces (finiteChainCoefficientFamily n w) v) hPred
  have hc := facePredicateEquiv_projected (k := k) _ _ hPred
  have he := finiteFaceTensorEquiv_is_chain (k := k) S P hS (crossingBlockFaces_supported w v)
  change (projectedTotalDifferential _).comp (c.toLinearMap.comp e.toLinearMap) =
    (c.toLinearMap.comp e.toLinearMap).comp _
  rw [←LinearMap.comp_assoc,hc,LinearMap.comp_assoc,he,←LinearMap.comp_assoc]

def crossingCoefficientFamily (w : FiniteMultichain n E m) : Family (FiniteVariable.{u} n) :=
  Finset.univ.biUnion (finiteBlockFamily w)

lemma crossingCoefficient_contains (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    Contains (crossingCoefficientFamily w) v ↔ Contains (finiteChainCoefficientFamily n w) v := by
  rw [finiteChainCoefficient_contains_blocks hE]
  simp only [Contains,crossingCoefficientFamily,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨b,⟨p,hp⟩,hb⟩
    exact ⟨p,b,hp,hb⟩
  · rintro ⟨p,b,hp,hb⟩
    exact ⟨b,⟨p,hp⟩,hb⟩

theorem uncoveredCrossingBlock_contractible (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (e : FiniteVariable.{u} n) (he : 0<v e) (hn : ∀p,¬finiteCrosses w p e) :
    ∃ H : Module.End k (TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w) v)),
      quotientTotalDifferential (finiteChainCoefficientFamily n w) v*H+
        H*quotientTotalDifferential (finiteChainCoefficientFamily n w) v=1 ∧
      ∀i x,x∈totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w) v) i →
        H x∈totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w) v) (i+1) := by
  have hu : UnusedVariable (crossingCoefficientFamily w) e := by
    intro b hb
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hb
    by_contra hne
    exact hn p (finiteBlockFamily_variables w p hp e hne)
  refine ⟨quotientTotalCreation (finiteChainCoefficientFamily n w) v e,?_,?_⟩
  · exact quotientTotalCreation_contracts_of_contains (crossingCoefficient_contains hE w) hu he
  · exact quotientTotalCreation_raises_of_contains (crossingCoefficient_contains hE w) hu he

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainProduct -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {r s : ℕ}

lemma finiteTargetExponent_add (a b : Exponent (FiniteVariable.{u} n)) (r s : ℕ) :
    finiteTargetExponent (a+b) (r+s) = finiteTargetExponent a r + finiteTargetExponent b s := by
  ext x
  cases x <;> simp

lemma finitePresentationWeight_add (c e : FiniteReesVariable.{u} E →₀ ℕ) :
    finitePresentationWeight (c+e) = finitePresentationWeight c + finitePresentationWeight e := by
  simp only [finitePresentationWeight, Finsupp.embDomain_add, map_add]

lemma chainIndexProduct_mem (a : FiniteChainStandardIndex.{u} n E r)
    (b : FiniteChainStandardIndex.{u} n E s) :
    Contains (exponentPowerFamily (finiteRowFamily n E) (r+s))
      (finiteChainIndexExponent a + finiteChainIndexExponent b) := by
  apply (finiteTarget_mem_rees_iff _ _).mp
  refine ⟨finiteChainPresentation a.1 a.2.val + finiteChainPresentation b.1 b.2.val, ?_⟩
  rw [map_add, finiteChainPresentation_image, finiteChainPresentation_image,
    finiteTargetExponent_add]
  rfl

/-- The product is defined by multiplication of actual monomials in the ordinary powers. -/
def chainIndexProduct (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s) :
    FiniteChainStandardIndex.{u} n E (r+s) :=
  (finiteChainPowerIndexEquiv hE (r+s)).symm
    ⟨finiteChainIndexExponent a + finiteChainIndexExponent b, chainIndexProduct_mem a b⟩

lemma chainIndexProduct_image (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s) :
    finiteChainIndexExponent (chainIndexProduct hE a b) =
      finiteChainIndexExponent a + finiteChainIndexExponent b :=
  congrArg Subtype.val ((finiteChainPowerIndexEquiv hE (r+s)).apply_symm_apply _)

lemma chainIndexProduct_presentation (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s) :
    finiteChainPresentation (chainIndexProduct hE a b).1 (chainIndexProduct hE a b).2.val =
      finiteReesNormalForm hE (finiteChainPresentation a.1 a.2.val +
        finiteChainPresentation b.1 b.2.val) := by
  apply finiteReesStandard_image_injective hE
    ((finiteChainPresentation_standard_iff hE _ _).mpr (chainIndexProduct hE a b).2.property)
    (finiteReesNormalForm_standard hE _)
  rw [finiteReesNormalForm_image, finiteChainPresentation_image, map_add,
    finiteChainPresentation_image, finiteChainPresentation_image]
  change finiteTargetExponent (finiteChainIndexExponent (chainIndexProduct hE a b)) (r+s) =
    finiteTargetExponent (finiteChainIndexExponent a) r +
      finiteTargetExponent (finiteChainIndexExponent b) s
  rw [chainIndexProduct_image, finiteTargetExponent_add]

lemma chainIndexProduct_weight_le (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s) :
    chainIndexWeight (chainIndexProduct hE a b) ≤ chainIndexWeight a + chainIndexWeight b := by
  unfold chainIndexWeight
  rw [chainIndexProduct_presentation]
  exact (finiteReesNormalForm_weight_le hE _).trans_eq (finitePresentationWeight_add _ _)

lemma chainIndexProduct_coefficient_degree (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s) :
    (chainIndexProduct hE a b).2.val.degree = a.2.val.degree + b.2.val.degree := by
  have he := congrArg Finsupp.degree (chainIndexProduct_image hE a b)
  simp only [map_add, finiteChainIndexExponent_degree, Nat.add_mul] at he
  omega

/-- Multiplication weakly lowers the sum of the two multichain weights. -/
theorem chainIndexProduct_factorWeight_le (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s) :
    finiteChainFactorWeight.{u} (chainIndexProduct hE a b).1 ≤
      finiteChainFactorWeight.{u} a.1 + finiteChainFactorWeight.{u} b.1 := by
  have hw := chainIndexProduct_weight_le hE a b
  rw [chainIndexWeight_eq, chainIndexWeight_eq, chainIndexWeight_eq,
    chainIndexProduct_coefficient_degree] at hw
  omega

theorem chainIndexProduct_factorWeight_lt_left (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s)
    (A B : ℕ) (ha : finiteChainFactorWeight.{u} a.1 < A)
    (hb : finiteChainFactorWeight.{u} b.1 ≤ B) :
    finiteChainFactorWeight.{u} (chainIndexProduct hE a b).1 < A+B := by
  have h := chainIndexProduct_factorWeight_le hE a b
  omega

theorem chainIndexProduct_factorWeight_lt_right (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E r) (b : FiniteChainStandardIndex.{u} n E s)
    (A B : ℕ) (ha : finiteChainFactorWeight.{u} a.1 ≤ A)
    (hb : finiteChainFactorWeight.{u} b.1 < B) :
    finiteChainFactorWeight.{u} (chainIndexProduct hE a b).1 < A+B := by
  have h := chainIndexProduct_factorWeight_le hE a b
  omega

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealFaceProduct -/
section

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {r s : ℕ}

lemma faceExponent_union_of_disjoint {V : Type*} [Fintype V] [LinearOrder V] [DecidableEq V]
    (F G : Finset V) (h : Disjoint F G) : faceExponent (F∪G)=faceExponent F+faceExponent G := by
  unfold faceExponent
  exact Finset.sum_union h

lemma residual_union_of_disjoint {V : Type*} [Fintype V] [LinearOrder V] [DecidableEq V]
    (α β : Exponent V) (F G : Finset V) (h : Disjoint F G)
    (hF : faceExponent F≤α) (hG : faceExponent G≤β) :
    α+β-faceExponent (F∪G)=(α-faceExponent F)+(β-faceExponent G) := by
  rw [faceExponent_union_of_disjoint F G h]
  ext x
  have hf := hF x
  have hg := hG x
  simp only [Finsupp.add_apply,Finsupp.tsub_apply]
  omega

lemma finitePower_contains_add (hE : finiteLatticeClosed n E)
    {α β : Exponent (FiniteVariable.{u} n)}
    (hα : Contains (exponentPowerFamily (finiteRowFamily n E) r) α)
    (hβ : Contains (exponentPowerFamily (finiteRowFamily n E) s) β) :
    Contains (exponentPowerFamily (finiteRowFamily n E) (r+s)) (α+β) := by
  let a := (finiteChainPowerIndexEquiv hE r).symm ⟨α,hα⟩
  let b := (finiteChainPowerIndexEquiv hE s).symm ⟨β,hβ⟩
  have ha : finiteChainIndexExponent a=α :=
    congrArg Subtype.val ((finiteChainPowerIndexEquiv hE r).apply_symm_apply _)
  have hb : finiteChainIndexExponent b=β :=
    congrArg Subtype.val ((finiteChainPowerIndexEquiv hE s).apply_symm_apply _)
  simpa only [ha,hb] using chainIndexProduct_mem a b

lemma idealPowerFaces_union (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) :
    ∀ F, koszulFaces (exponentPowerFamily (finiteRowFamily n E) r) α F →
      ∀ G, koszulFaces (exponentPowerFamily (finiteRowFamily n E) s) β G →
      Disjoint F G →
      koszulFaces (exponentPowerFamily (finiteRowFamily n E) (r+s)) (α+β) (F∪G) := by
  intro F hF G hG hFG
  refine ⟨?_,?_⟩
  · rw [faceExponent_union_of_disjoint F G hFG]
    exact add_le_add hF.1 hG.1
  · rw [residual_union_of_disjoint α β F G hFG hF.1 hG.1]
    exact finitePower_contains_add hE hF.2 hG.2

lemma idealPowerFaces_union_ordered (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) :
    ∀ F, koszulFaces (exponentPowerFamily (finiteRowFamily n E) r) α F →
      ∀ G, koszulFaces (exponentPowerFamily (finiteRowFamily n E) s) β G →
      Disjoint F G →
      koszulFaces (exponentPowerFamily (finiteRowFamily n E) (r+s)) (α+β)
        (@Union.union (Finset (FiniteVariable.{u} n))
          (@Finset.instUnion (FiniteVariable.{u} n)
            (inferInstance : LinearOrder (FiniteVariable.{u} n)).toDecidableEq) F G) := by
  intro F hF G hG hFG
  exact (finsetUnion_decidableEq (inferInstance : DecidableEq (FiniteVariable.{u} n))
    (inferInstance : LinearOrder (FiniteVariable.{u} n)).toDecidableEq F G) ▸
      idealPowerFaces_union hE α β F hF G hG hFG

/-- Literal multiplication in the Koszul differential graded algebra, in fixed fine degrees. -/
def idealPowerFaceMul (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) :
    (TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) r) α)
      ⊗[k] TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) s) β))
      →ₗ[k] TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) (r+s)) (α+β)) :=
  totalFaceMulTensor _ _ _ (idealPowerFaces_union_ordered hE α β)

theorem idealPowerFaceMul_is_chain (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n))
    (x : TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) r) α))
    (y : TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) s) β)) :
    idealTotalDifferential (koszulFaces_downward _ (α+β)) (idealPowerFaceMul hE α β (x⊗ₜ[k]y)) =
      idealPowerFaceMul hE α β ((idealTotalDifferential (koszulFaces_downward _ α) x)⊗ₜ[k]y) +
      idealPowerFaceMul hE α β
        ((totalFaceInvolute _ x)⊗ₜ[k](idealTotalDifferential (koszulFaces_downward _ β) y)) :=
  idealTotalDifferential_mul _ _ _ _ _ _ (idealPowerFaces_union_ordered hE α β) x y

def chainFaceProduct (hE : finiteLatticeClosed n E)
    {α β : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E r α) (b : ChainFaceIndex n E s β)
    (h : Disjoint a.2.val b.2.val) : ChainFaceIndex n E (r+s) (α+β) :=
  (chainFaceEquiv hE (α+β)).symm
    ⟨a.2.val∪b.2.val,idealPowerFaces_union hE α β _
      (chainFaceToActual a).property _ (chainFaceToActual b).property h⟩

@[simp] lemma chainFaceProduct_face (hE : finiteLatticeClosed n E)
    {α β : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E r α) (b : ChainFaceIndex n E s β)
    (h : Disjoint a.2.val b.2.val) :
    (chainFaceProduct hE a b h).2.val=a.2.val∪b.2.val :=
  congrArg Subtype.val ((chainFaceEquiv hE (α+β)).apply_symm_apply _)

lemma chainFaceProduct_standard (hE : finiteLatticeClosed n E)
    {α β : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E r α) (b : ChainFaceIndex n E s β)
    (h : Disjoint a.2.val b.2.val) :
    chainFaceStandardIndex (chainFaceProduct hE a b h) =
      chainIndexProduct hE (chainFaceStandardIndex a) (chainFaceStandardIndex b) := by
  apply finiteChainIndexExponent_injective hE
  rw [chainIndexProduct_image,chainFaceStandardIndex_exponent,
    chainFaceStandardIndex_exponent,chainFaceStandardIndex_exponent,chainFaceProduct_face]
  exact residual_union_of_disjoint α β a.2.val b.2.val h
    (chainFaceIndex_face_le a) (chainFaceIndex_face_le b)

theorem chainFaceProduct_factorWeight_le (hE : finiteLatticeClosed n E)
    {α β : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E r α) (b : ChainFaceIndex n E s β)
    (h : Disjoint a.2.val b.2.val) :
    finiteChainFactorWeight.{u} (chainFaceProduct hE a b h).1.val ≤
      finiteChainFactorWeight.{u} a.1.val+finiteChainFactorWeight.{u} b.1.val := by
  have hw := chainIndexProduct_factorWeight_le hE (chainFaceStandardIndex a) (chainFaceStandardIndex b)
  rw [← chainFaceProduct_standard hE a b h] at hw
  exact hw

/-- The genuine product, expressed in the standard multichain coordinates. -/
def chainTotalMul (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n)) :
    (ChainTotalModule n E r α k ⊗[k] ChainTotalModule n E s β k) →ₗ[k]
      ChainTotalModule n E (r+s) (α+β) k :=
  (chainTotalEquiv hE (r+s) (α+β) k).symm.toLinearMap.comp
    ((idealPowerFaceMul hE α β).comp
      (TensorProduct.map (chainTotalEquiv hE r α k).toLinearMap
        (chainTotalEquiv hE s β k).toLinearMap))

theorem chainTotalMul_basis (hE : finiteLatticeClosed n E)
    (α β : Exponent (FiniteVariable.{u} n))
    (a : ChainFaceIndex n E r α) (b : ChainFaceIndex n E s β)
    (h : Disjoint a.2.val b.2.val) :
    chainTotalMul hE α β ((chainTotalBasis n E r α k a)⊗ₜ[k](chainTotalBasis n E s β k b)) =
      faceWedgeSign a.2.val b.2.val h •
        chainTotalBasis n E (r+s) (α+β) k (chainFaceProduct hE a b h) := by
  apply (chainTotalEquiv hE (r+s) (α+β) k).injective
  simp only [chainTotalMul,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,TensorProduct.map_tmul,chainTotalEquiv_basis]
  apply Subtype.ext
  simp only [idealPowerFaceMul,totalFaceMulTensor_tmul_val,totalFaceBasis_val,
    map_zsmul_unit,chainTotalEquiv_basis,Submodule.coe_smul_of_tower,
    chainFaceEquiv_val,chainFaceProduct_face]
  have hu := finsetUnion_decidableEq
    (inferInstance : LinearOrder (FiniteVariable.{u} n)).toDecidableEq
    (inferInstance : DecidableEq (FiniteVariable.{u} n)) a.2.val b.2.val
  simpa only [hu] using faceBasis_mul_of_disjoint (k := k) a.2.val b.2.val h

lemma idealPowerFace_list_mul_mem (hE : finiteLatticeClosed n E) (m : ℕ)
    (β : Fin m → Exponent (FiniteVariable.{u} n))
    (x : Fin m → Simplicial.Ambient (FiniteVariable.{u} n) k)
    (hx : ∀p,x p∈TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) (β p))) :
    (List.ofFn x).prod∈TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) (∑p,β p)) := by
  induction m with
  | zero =>
    simp only [List.ofFn_zero,List.prod_nil,Fin.sum_univ_zero]
    have hf : koszulFaces (exponentPowerFamily (finiteRowFamily n E) 0) 0
        (∅ : Finset (FiniteVariable.{u} n)) := by
      constructor
      · simp only [faceExponent_empty,le_refl]
      · exact ⟨0,by simp [exponentPowerFamily],by simp⟩
    rw [←faceBasis_empty (V := FiniteVariable.{u} n) (k := k)]
    exact Submodule.subset_span ⟨∅,hf,rfl⟩
  | succ m ih =>
    rw [List.ofFn_succ,List.prod_cons,Fin.sum_univ_succ]
    have ht := ih (fun p => β p.succ) (fun p => x p.succ) (fun p => hx p.succ)
    have hm := faceSpan_mul_mem _ _ _
      (idealPowerFaces_union_ordered (r := 1) (s := m) hE (β 0) (∑p : Fin m,β p.succ)) (hx 0) ht
    simpa only [Nat.one_add] using hm

def idealPowerOrderedProduct (hE : finiteLatticeClosed n E) (m : ℕ)
    (β : Fin m → Exponent (FiniteVariable.{u} n)) :
    (⨂[k] p,TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) (β p))) →ₗ[k]
      TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) (∑p,β p)) :=
  let f : (⨂[k] p,TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) (β p))) →ₗ[k]
      Simplicial.Ambient (FiniteVariable.{u} n) k := PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebraFin k m (Simplicial.Ambient (FiniteVariable.{u} n) k)).compLinearMap
      (fun p => (TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) (β p))).subtype))
  f.codRestrict (TotalFaceModule (k := k)
    (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) (∑p,β p)))
    (fun t => by
      refine PiTensorProduct.induction_on (motive := fun z => f z ∈ TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) (∑p,β p))) t ?_ ?_
      · intro c x
        simp only [f,map_smul,PiTensorProduct.lift.tprod,MultilinearMap.compLinearMap_apply,
          MultilinearMap.mkPiAlgebraFin_apply,Submodule.subtype_apply]
        exact Submodule.smul_mem _ c
          (idealPowerFace_list_mul_mem hE m β (fun p => (x p).val) (fun p => (x p).property))
      · intro x y hx hy
        simpa only [map_add] using Submodule.add_mem _ hx hy)

@[simp] theorem idealPowerOrderedProduct_tprod_val (hE : finiteLatticeClosed n E) (m : ℕ)
    (β : Fin m → Exponent (FiniteVariable.{u} n))
    (x : ∀p,TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) (β p))) :
    (idealPowerOrderedProduct hE m β (⨂ₜ[k] p,x p)).val =
      (List.ofFn (fun p => (x p).val)).prod := by
  simp only [idealPowerOrderedProduct,LinearMap.codRestrict_apply,
    PiTensorProduct.lift.tprod,MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebraFin_apply,Submodule.subtype_apply]

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CrossingBlockLift -/
section

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

def crossingBlockFineDegree (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m) : Exponent (FiniteVariable.{u} n) :=
  finiteBlockDegree w p v+finiteRowExponent n (w.val p).val

lemma crossingBlockFineDegree_sum (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (hv : CrossingCovered w v) :
    (∑p,crossingBlockFineDegree w v p)=v+finiteChainShift n w := by
  simp only [crossingBlockFineDegree,Finset.sum_add_distrib,finiteBlockDegree_sum w v hv,
    finiteChainShift]

theorem crossingBlockSourceModule_eq (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m) :
    TotalFaceModule (k := k) (crossingBlockFaces w v p) =
      TotalFaceModule (k := k) (quotientKoszulFaces (finitePredecessorFamily n E (w.val p).val)
        (crossingBlockFineDegree w v p-finiteRowExponent n (w.val p).val)) := by
  rw [crossingBlockFineDegree,add_tsub_cancel_right]
  rfl

def crossingBlockSourceCast (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m) :
    TotalFaceModule (k := k) (crossingBlockFaces w v p) →ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces (finitePredecessorFamily n E (w.val p).val)
        (crossingBlockFineDegree w v p-finiteRowExponent n (w.val p).val)) :=
  (LinearEquiv.ofEq _ _ (crossingBlockSourceModule_eq (k := k) w v p)).toLinearMap

@[simp] lemma crossingBlockSourceCast_val (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (x : TotalFaceModule (k := k) (crossingBlockFaces w v p)) :
    (crossingBlockSourceCast (k := k) w v p x).val=x.val := by
  exact LinearEquiv.coe_ofEq_apply (crossingBlockSourceModule_eq (k := k) w v p) x

lemma crossingBlockSourceCast_differential (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (x : TotalFaceModule (k := k) (crossingBlockFaces w v p)) :
    quotientTotalDifferential (finitePredecessorFamily n E (w.val p).val)
        (crossingBlockFineDegree w v p-finiteRowExponent n (w.val p).val)
        (crossingBlockSourceCast w v p x) =
      crossingBlockSourceCast w v p
        (quotientTotalDifferential (finitePredecessorFamily n E (w.val p).val)
          (finiteBlockDegree w p v) x) := by
  apply Subtype.ext
  simp only [quotientTotalDifferential_val,crossingBlockSourceCast_val]
  change quotientFaceProjection (finitePredecessorFamily n E (w.val p).val)
      (crossingBlockFineDegree w v p-finiteRowExponent n (w.val p).val)
      (Simplicial.boundary x.val)=
    quotientFaceProjection (finitePredecessorFamily n E (w.val p).val)
      (finiteBlockDegree w p v) (Simplicial.boundary x.val)
  simp only [crossingBlockFineDegree,add_tsub_cancel_right]

lemma crossingBlockSourceCast_involute (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (x : TotalFaceModule (k := k) (crossingBlockFaces w v p)) :
    totalFaceInvolute _ (crossingBlockSourceCast (k := k) w v p x) =
      crossingBlockSourceCast w v p (totalFaceInvolute (crossingBlockFaces w v p) x) := by
  apply Subtype.ext
  change CliffordAlgebra.involute (crossingBlockSourceCast (k := k) w v p x).val =
    (crossingBlockSourceCast w v p (totalFaceInvolute (crossingBlockFaces w v p) x)).val
  rw [crossingBlockSourceCast_val,crossingBlockSourceCast_val]
  rfl

def crossingBlockLift (hE : finiteLatticeClosed n E) (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (p : Fin m) :
    TotalFaceModule (k := k) (crossingBlockFaces w v p) →ₗ[k]
      TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1)
        (crossingBlockFineDegree w v p)) :=
  (firstPowerExteriorLift (k := k) hE (β := crossingBlockFineDegree w v p)
    (a := w.val p) (rowMaximum_block w p v)).comp (crossingBlockSourceCast w v p)

@[simp] lemma crossingBlockLift_apply (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (x : TotalFaceModule (k := k) (crossingBlockFaces w v p)) :
    crossingBlockLift (k := k) hE w v p x =
      firstPowerExteriorLift (k := k) hE (β := crossingBlockFineDegree w v p)
        (a := w.val p) (rowMaximum_block w p v) (crossingBlockSourceCast w v p x) := rfl

lemma crossingBlockLift_differential (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (x : TotalFaceModule (k := k) (crossingBlockFaces w v p)) :
    idealTotalDifferential (koszulFaces_downward _ (crossingBlockFineDegree w v p))
        (crossingBlockLift hE w v p x) =
      crossingBlockLift hE w v p (projectedTotalDifferential (crossingBlockFaces w v p) x) := by
  rw [crossingBlockLift_apply,crossingBlockLift_apply]
  have h := firstPowerExteriorLift_differential (k := k) hE
    (β := crossingBlockFineDegree w v p) (a := w.val p) (rowMaximum_block w p v)
    (crossingBlockSourceCast w v p x)
  have hc := crossingBlockSourceCast_differential (k := k) w v p x
  have hp : quotientTotalDifferential (k := k)
      (finitePredecessorFamily n E (w.val p).val) (finiteBlockDegree w p v) x =
      projectedTotalDifferential (crossingBlockFaces w v p) x :=
    LinearMap.congr_fun (quotientTotalDifferential_eq_projected (k := k)
      (finitePredecessorFamily n E (w.val p).val) (finiteBlockDegree w p v)) x
  have hc' := hc.trans (congrArg (crossingBlockSourceCast (k := k) w v p) hp)
  exact h.trans (congrArg
    (firstPowerExteriorLift (k := k) hE (β := crossingBlockFineDegree w v p)
      (a := w.val p) (rowMaximum_block w p v)) hc')

lemma crossingBlockLift_involute (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) (p : Fin m)
    (x : TotalFaceModule (k := k) (crossingBlockFaces w v p)) :
    totalFaceInvolute _ (crossingBlockLift hE w v p x) =
      crossingBlockLift hE w v p (totalFaceInvolute (crossingBlockFaces w v p) x) := by
  rw [crossingBlockLift_apply,crossingBlockLift_apply]
  have h := LinearMap.congr_fun (firstPowerExteriorLift_involute (k := k) hE
    (β := crossingBlockFineDegree w v p) (a := w.val p) (rowMaximum_block w p v))
    (crossingBlockSourceCast w v p x)
  change totalFaceInvolute _
      (firstPowerExteriorLift (k := k) hE (β := crossingBlockFineDegree w v p)
        (a := w.val p) (rowMaximum_block w p v) (crossingBlockSourceCast w v p x)) =
    firstPowerExteriorLift (k := k) hE (β := crossingBlockFineDegree w v p)
      (a := w.val p) (rowMaximum_block w p v)
      (totalFaceInvolute _ (crossingBlockSourceCast w v p x)) at h
  exact h.trans (congrArg
    (firstPowerExteriorLift (k := k) hE (β := crossingBlockFineDegree w v p)
      (a := w.val p) (rowMaximum_block w p v))
    (crossingBlockSourceCast_involute (k := k) w v p x))

def crossingLiftTensorProduct (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    (⨂[k] p,TotalFaceModule (k := k) (crossingBlockFaces w v p)) →ₗ[k]
      TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m)
        (∑p,crossingBlockFineDegree w v p)) :=
  (idealPowerOrderedProduct hE m (crossingBlockFineDegree w v)).comp
    (PiTensorProduct.map (crossingBlockLift hE w v))

lemma crossingLiftTensorProduct_val (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    (TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m)
      (∑p,crossingBlockFineDegree w v p))).subtype.comp (crossingLiftTensorProduct hE w v) =
    orderedLiftProduct (fun p =>
      (TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1)
        (crossingBlockFineDegree w v p))).subtype.comp (crossingBlockLift hE w v p)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
    crossingLiftTensorProduct,PiTensorProduct.map_tprod,
    Submodule.subtype_apply,idealPowerOrderedProduct_tprod_val,orderedLiftProduct_tprod]

theorem crossingLiftTensorProduct_is_chain (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    (idealTotalDifferential (koszulFaces_downward _ (∑p,crossingBlockFineDegree w v p))).comp
        (crossingLiftTensorProduct (k := k) hE w v) =
      (crossingLiftTensorProduct hE w v).comp (finiteFaceTensorDifferential (crossingBlockFaces w v)) := by
  let f := fun p =>
    (TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1)
      (crossingBlockFineDegree w v p))).subtype.comp (crossingBlockLift hE w v p)
  have hd : ∀p x,Simplicial.boundary (f p x)=
      f p (projectedTotalDifferential (crossingBlockFaces w v p) x) := by
    intro p x
    exact congrArg Subtype.val (crossingBlockLift_differential hE w v p x)
  have hi : ∀p x,CliffordAlgebra.involute (f p x)=
      f p (totalFaceInvolute (crossingBlockFaces w v p) x) := by
    intro p x
    exact congrArg Subtype.val (crossingBlockLift_involute hE w v p x)
  have h := orderedLiftProduct_is_chain (K := k)
    (A := Simplicial.Ambient (FiniteVariable.{u} n) k)
    (M := fun p : Fin m => TotalFaceModule (k := k) (crossingBlockFaces w v p))
    Simplicial.boundary CliffordAlgebra.involute
    (CliffordAlgebra.contractLeft_one _ _) (CliffordAlgebra.contractLeft_mul _)
    (fun p => projectedTotalDifferential (crossingBlockFaces w v p))
    (fun p => totalFaceInvolute (crossingBlockFaces w v p)) f hd hi
  rw [←crossingLiftTensorProduct_val hE w v] at h
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun h x

def crossingWholeLift (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) :
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w) v) →ₗ[k]
      TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m)
        (∑p,crossingBlockFineDegree w v p)) :=
  (crossingLiftTensorProduct hE w v).comp (crossingBlockTensorEquiv hE w v hv).symm.toLinearMap

theorem crossingWholeLift_is_chain (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n))
    (hv : CrossingCovered w v) :
    (idealTotalDifferential (koszulFaces_downward _ (∑p,crossingBlockFineDegree w v p))).comp
        (crossingWholeLift (k := k) hE w v hv) =
      (crossingWholeLift hE w v hv).comp
        (quotientTotalDifferential (finiteChainCoefficientFamily n w) v) := by
  let e := crossingBlockTensorEquiv (k := k) hE w v hv
  have he := crossingBlockTensorEquiv_is_chain (k := k) hE w v hv
  apply LinearMap.ext
  intro x
  have hi : finiteFaceTensorDifferential (crossingBlockFaces w v) (e.symm x) =
      e.symm (quotientTotalDifferential (finiteChainCoefficientFamily n w) v x) := by
    apply e.injective
    have hh := LinearMap.congr_fun he (e.symm x)
    simpa only [e,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using hh.symm
  have h := LinearMap.congr_fun (crossingLiftTensorProduct_is_chain (k := k) hE w v) (e.symm x)
  rw [LinearMap.comp_apply,LinearMap.comp_apply,hi] at h
  exact h

end FourPapers.Sublattice

end
end


end
