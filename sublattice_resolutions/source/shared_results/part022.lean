module
public import graph_foundation.part014
public import shared_results.part021

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ActualMultiplicativeDegeneration -/
section

/-! # Multiplicative propagation stated using actual associated homology

The hypotheses compare the literal homology quotients of a component and
its actual associated component. The proof constructs leading-cycle lifts
from that equality, propagates them by multiplication of actual cycles,
and recovers the homology dimensions and algebra generation.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical FilteredHomology

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x,x∈F.level n→D.d x∈F.level n)
  (hp : ∀ n x,x∈F.level n→D.parity x∈F.level n)

theorem specialClasses_eq_selected (W : Submodule K A) :
    F.specialClasses D hd hp W =
      selectedHomologyClasses (F.associatedDGA D hd hp) (F.associatedPiece W) := by
  ext u
  constructor
  · rintro ⟨p,hcycle,hW,rfl⟩
    exact ⟨⟨F.leadingMap p,hcycle⟩,F.leading_mem_associatedPiece W p hW,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨p,hp',hW⟩ := (F.mem_associatedPiece_iff W x.val).mp hx
    refine ⟨p,?_,hW,?_⟩
    · rw [hp']
      exact x.property
    · apply congrArg (F.associatedDGA D hd hp).classMap
      exact Subtype.ext hp'.symm

variable [AddMonoid Γ] [DecidableEq Γ]
  (P : Γ → Submodule K A) [GradedAlgebra P]
  [∀ i,FiniteDimensional K (P i)]

/-- A version of the multiplicative principle whose dimension hypothesis
uses the literal original and associated homology groups. No lifting,
flatness or homology comparison is assumed in this statement. -/
theorem propagation_from_actual_components
    (hF : ∀ n,DirectSum.SetLike.IsHomogeneous P (F.level n))
    (hD : ∀ i x,x∈P i→D.d x∈P i)
    (W : Submodule K A) (hWh : DirectSum.SetLike.IsHomogeneous P W)
    (hWd : ∀ x∈W,D.d x∈W)
    (hfirst : ∀ i,
      Module.finrank K (Homology
        (componentDifferential D (P i⊓W) (fun x hx => ⟨hD i x hx.1,hWd x hx.2⟩))
        (componentDifferential D (P i⊓W) (fun x hx => ⟨hD i x hx.1,hWd x hx.2⟩))
        (componentDifferential_square D (P i⊓W) (fun x hx => ⟨hD i x hx.1,hWd x hx.2⟩))) =
      Module.finrank K (F.associatedComponentHomology D hd hp (P i⊓W) (P i⊓W) (P i⊓W)
        (fun x hx => ⟨hD i x hx.1,hWd x hx.2⟩)
        (fun x hx => ⟨hD i x hx.1,hWd x hx.2⟩)))
    (hgen : Algebra.adjoin K (selectedHomologyClasses (F.associatedDGA D hd hp)
      (F.associatedPiece W))=⊤) :
    F.LiftsCycles D ∧
      (∀ i, Module.finrank K (Homology (componentDifferential D (P i) (hD i))
        (componentDifferential D (P i) (hD i)) (componentDifferential_square D (P i) (hD i))) =
        Module.finrank K (F.associatedComponentHomology D hd hp (P i) (P i) (P i) (hD i) (hD i))) ∧
      Algebra.adjoin K (selectedHomologyClasses D W)=⊤ := by
  have hrelative : F.RelativeLiftsCycles D W :=
    F.relativeLiftsCycles_of_components D P W hF hWh hD (fun i =>
      (F.relativeLiftsCycles_iff_actualAssociated D hd hp (P i⊓W)
        (fun x hx => ⟨hD i x hx.1,hWd x hx.2⟩)).mpr (hfirst i))
  have hgen' : Algebra.adjoin K (F.specialClasses D hd hp W)=⊤ := by
    rw [F.specialClasses_eq_selected D hd hp W]
    exact hgen
  have hlift := F.liftsCycles_of_relative_generators D hd hp W hgen' hrelative
  refine ⟨hlift,?_,F.homology_generated_of_relative_generators D P hd hp hF hD W hWh
    hrelative hgen'⟩
  intro i
  exact (F.relativeLiftsCycles_iff_actualAssociated D hd hp (P i) (hD i)).mp
    (F.relativeLiftsCycles_of_homogeneous_projection D P hF hD hlift i)

end FourPapers.IntegerFiltered.MultiplicativeFiltration

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open FilteredHomology

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x,x∈F.level n→D.d x∈F.level n)
  (hp : ∀ n x,x∈F.level n→D.parity x∈F.level n)
  (W U Z : Submodule K A)
  [FiniteDimensional K W] [FiniteDimensional K U] [FiniteDimensional K Z]
  (hWU : ∀ x∈W,D.d x∈U) (hUZ : ∀ x∈U,D.d x∈Z)
  (L : ℤ)
  (hLW : (F.level (L-1)).comap W.subtype=⊥)
  (hLU : (F.level (L-1)).comap U.subtype=⊥)
  (hLZ : (F.level (L-1)).comap Z.subtype=⊥)
  (N : ℕ)
  (hNW : (F.componentFiltration W L hLW).level N=⊤)
  (hNU : (F.componentFiltration U L hLU).level N=⊤)
  (hNZ : (F.componentFiltration Z L hLZ).level N=⊤)

include hNW hNU hNZ in
/-- Leading-cycle lifts in the two adjacent actual maps give equality in
the individual three-term homology group, with no sum over homological
degrees in the conclusion. -/
theorem componentHomology_dimension_eq_actualAssociated
    (liftf : FilteredHomology.LiftsCycles (F.componentFiltration W L hLW) (F.componentFiltration U L hLU)
      (componentDifferentialBetween D W U hWU))
    (liftg : FilteredHomology.LiftsCycles (F.componentFiltration U L hLU) (F.componentFiltration Z L hLZ)
      (componentDifferentialBetween D U Z hUZ)) :
    Module.finrank K (Homology (componentDifferentialBetween D W U hWU)
      (componentDifferentialBetween D U Z hUZ) (componentDifferentialBetween_comp D W U Z hWU hUZ)) =
      Module.finrank K (F.associatedComponentHomology D hd hp W U Z hWU hUZ) := by
  rw [F.associatedComponentHomology_finrank D hd hp W U Z hWU hUZ
    L hLW hLU hLZ N hNW hNU hNZ]
  exact finrank_homology_eq_sum_graded
    (F.componentFiltration W L hLW) (F.componentFiltration U L hLU)
    (F.componentFiltration Z L hLZ)
    (componentDifferentialBetween D W U hWU) (componentDifferentialBetween D U Z hUZ)
    (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU)
    (F.componentDifferentialBetween_preserves D hd U Z hUZ L hLU hLZ)
    (componentDifferentialBetween_comp D W U Z hWU hUZ) N hNU liftf liftg

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredThreeTerm -/
section

/-! # Common finite bounds and homogeneous projection of actual cycle lifts -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical FilteredHomology

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A)
  (W U Z : Submodule K A)
  [FiniteDimensional K W] [FiniteDimensional K U] [FiniteDimensional K Z]

/-- Three actual finite-dimensional pieces admit one common finite weight
interval. The bounds are consequences of the original filtration. -/
theorem exists_three_component_bounds :
    ∃ (L : ℤ)
      (hLW : (F.level (L-1)).comap W.subtype=⊥)
      (hLU : (F.level (L-1)).comap U.subtype=⊥)
      (hLZ : (F.level (L-1)).comap Z.subtype=⊥) (N : ℕ),
      (F.componentFiltration W L hLW).level N=⊤ ∧
      (F.componentFiltration U L hLU).level N=⊤ ∧
      (F.componentFiltration Z L hLZ).level N=⊤ := by
  obtain ⟨lW,hlW⟩ := F.exists_component_lower_bound W
  obtain ⟨lU,hlU⟩ := F.exists_component_lower_bound U
  obtain ⟨lZ,hlZ⟩ := F.exists_component_lower_bound Z
  obtain ⟨uW,huW⟩ := F.exists_component_upper_bound W
  obtain ⟨uU,huU⟩ := F.exists_component_upper_bound U
  obtain ⟨uZ,huZ⟩ := F.exists_component_upper_bound Z
  let L : ℤ := min lW (min lU lZ)+1
  have hLW : (F.level (L-1)).comap W.subtype=⊥ := by
    apply bot_unique
    rw [← hlW]
    exact Submodule.comap_mono (F.mono (by dsimp [L]; omega))
  have hLU : (F.level (L-1)).comap U.subtype=⊥ := by
    apply bot_unique
    rw [← hlU]
    exact Submodule.comap_mono (F.mono (by dsimp [L]; omega))
  have hLZ : (F.level (L-1)).comap Z.subtype=⊥ := by
    apply bot_unique
    rw [← hlZ]
    exact Submodule.comap_mono (F.mono (by dsimp [L]; omega))
  obtain ⟨N,hN⟩ := exists_nat_ge (max uW (max uU uZ)-L+1)
  refine ⟨L,hLW,hLU,hLZ,N,?_,?_,?_⟩
  · apply top_unique
    intro a _
    have ha : a∈(F.level uW).comap W.subtype := by rw [huW]; trivial
    exact F.mono (by omega) ha
  · apply top_unique
    intro a _
    have ha : a∈(F.level uU).comap U.subtype := by rw [huU]; trivial
    exact F.mono (by omega) ha
  · apply top_unique
    intro a _
    have ha : a∈(F.level uZ).comap Z.subtype := by rw [huZ]; trivial
    exact F.mono (by omega) ha

variable (D : ParityDifferential K A)
  (hWU : ∀ x∈W,D.d x∈U)

/-- Project a genuine lifted cycle to its original homogeneous component.
The projection is specified by its actual action, left-inverse property,
weight preservation and differential commutation; it is not a cycle-lift
or homology-isomorphism hypothesis. -/
theorem componentDifferentialBetween_lifts_of_projection
    (hlift : F.LiftsCycles D)
    (πW : A →ₗ[K] W) (πU : A →ₗ[K] U)
    (hπW : ∀ a : W,πW a.val=a)
    (hπF : ∀ n x,x∈F.level n→(πW x).val∈F.level n)
    (hπD : ∀ x,D.d (πW x).val=(πU (D.d x)).val)
    (L : ℤ)
    (hLW : (F.level (L-1)).comap W.subtype=⊥)
    (hLU : (F.level (L-1)).comap U.subtype=⊥) :
    FilteredHomology.LiftsCycles (F.componentFiltration W L hLW) (F.componentFiltration U L hLU)
      (componentDifferentialBetween D W U hWU) := by
  intro n a ha hda
  have ha' : a.val∈F.level (L+(n:ℤ)) := by
    change a.val∈F.level (L+((n+1:ℕ):ℤ)-1) at ha
    have he : L+((n+1:ℕ):ℤ)-1=L+(n:ℤ) := by omega
    simpa only [he] using ha
  obtain ⟨z,hz,hdz,haz⟩ := hlift (L+(n:ℤ)) a.val ha' hda
  refine ⟨πW z,?_,?_,?_⟩
  · have h := hπF (L+(n:ℤ)) z hz
    change (πW z).val∈F.level (L+((n+1:ℕ):ℤ)-1)
    have he : L+((n+1:ℕ):ℤ)-1=L+(n:ℤ) := by omega
    simpa only [he] using h
  · apply Subtype.ext
    change D.d (πW z).val=0
    rw [hπD,hdz,map_zero]
    rfl
  · have h := hπF (L+(n:ℤ)-1) (a.val-z) haz
    rw [map_sub,hπW] at h
    exact h

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BigradedTensorKoszul -/
section

/-!
# The literal bigrading and homological grading of K(A)

The total degree of a coefficient in P_(r,m) tensored with e_F is
(r+|F|,m). Each variable has degree (1,0), so the actual Koszul differential
preserves this bigrading and lowers exterior degree by one. All homogeneous
pieces and projections below are submodules and maps on the original
tensor-exterior algebra, not replacement complexes.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BigradedTensorKoszul

open Classical CommAlg TensorExteriorKoszul FilteredTensorKoszul BigradedPolynomialAlgebra
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  (hX : ∀ v,algebraMap (MvPolynomial V K) A (MvPolynomial.X v)∈P (1,0))

abbrev Total := A ⊗[K] Simplicial.Ambient V K
abbrev Index := FullIndex P × Finset V

def basis : Module.Basis (Index (V:=V) P) K (Total (K:=K) (A:=A) (V:=V)) :=
  (fullBasis P).tensorProduct Simplicial.basis

def degree (a : Index (V:=V) P) : ℤ × ℕ := (a.1.1.1+(a.2.card:ℤ),a.1.1.2)

def fullDegree (a : Index (V:=V) P) : (ℤ × ℕ) × ℤ := (degree P a,(a.2.card:ℤ))

def piece (γ : ℤ × ℕ) : Submodule K (Total (K:=K) (A:=A) (V:=V)) :=
  Grading.Piece (basis P) (degree P) γ

def strand (γ : ℤ × ℕ) (p : ℤ) : Submodule K (Total (K:=K) (A:=A) (V:=V)) :=
  Grading.Piece (basis P) (fullDegree P) (γ,p)

@[simp] theorem basis_apply (a : FullIndex P) (s : Finset V) :
    basis P (a,s)=fullBasis P a ⊗ₜ[K] Simplicial.basis s := by
  simp only [basis,Module.Basis.tensorProduct_apply]

theorem basis_repr_coefficient (z : Total (K:=K) (A:=A) (V:=V))
    (a : FullIndex P) (s : Finset V) :
    (basis P).repr z (a,s)=(fullBasis P).repr (coefficient s z) a := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  | tmul x y =>
      rw [basis,Module.Basis.tensorProduct_repr_tmul_apply]
      change _=(fullBasis P).repr
        ((TensorProduct.equivFinsuppOfBasisRight Simplicial.basis) (x ⊗ₜ[K] y) s) a
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,map_smul,Finsupp.smul_apply]

theorem mem_piece (γ : ℤ × ℕ) (z : Total (K:=K) (A:=A) (V:=V)) :
    z∈piece P γ ↔ ∀ s,coefficient s z∈P (γ.1-(s.card:ℤ),γ.2) := by
  rw [piece,Grading.mem_piece]
  constructor
  · intro hz s
    rw [← fullBasis_piece P (γ.1-(s.card:ℤ),γ.2),Grading.mem_piece]
    intro a ha
    have hd := hz (a,s) (by rw [basis_repr_coefficient]; exact ha)
    apply Prod.ext
    · have h := congrArg Prod.fst hd
      change a.1.1+(s.card:ℤ)=γ.1 at h
      omega
    · simpa only [degree,fullDegree] using
        congrArg (fun g : ℤ × ℕ => g.2) hd
  · intro hz a ha
    rw [basis_repr_coefficient] at ha
    have hd := (Grading.mem_piece (fullBasis P) (fun a => a.1)
      (γ.1-(a.2.card:ℤ),γ.2) _).mp (by rw [fullBasis_piece]; exact hz a.2) a.1 ha
    unfold degree
    rw [hd]
    simp only [sub_add_cancel]

theorem piece_eq_coordinatePiece (γ : ℤ × ℕ) :
    piece (V:=V) P γ=coordinatePiece (fun s : Finset V => P (γ.1-(s.card:ℤ),γ.2)) := by
  ext z
  rw [mem_piece,mem_coordinatePiece]

theorem mem_strand (γ : ℤ × ℕ) (p : ℤ) (z : Total (K:=K) (A:=A) (V:=V)) :
    z∈strand P γ p ↔ ∀ s,coefficient s z∈
      (if (s.card:ℤ)=p then P (γ.1-(s.card:ℤ),γ.2) else ⊥) := by
  rw [strand,Grading.mem_piece]
  constructor
  · intro hz s
    by_cases hs : (s.card:ℤ)=p
    · rw [if_pos hs,← fullBasis_piece P (γ.1-(s.card:ℤ),γ.2),Grading.mem_piece]
      intro a ha
      have hd := congrArg Prod.fst (hz (a,s) (by rw [basis_repr_coefficient]; exact ha))
      apply Prod.ext
      · have h := congrArg Prod.fst hd
        change a.1.1+(s.card:ℤ)=γ.1 at h
        omega
      · simpa only [degree,fullDegree] using
          congrArg (fun g : ℤ × ℕ => g.2) hd
    · rw [if_neg hs,Submodule.mem_bot]
      apply (fullBasis P).repr.injective
      ext a
      simp only [map_zero,Finsupp.zero_apply]
      change (fullBasis P).repr (coefficient s z) a=0
      by_contra ha
      have hd := congrArg Prod.snd (hz (a,s) (by rw [basis_repr_coefficient]; exact ha))
      exact hs hd
  · intro hz a ha
    rw [basis_repr_coefficient] at ha
    have hp : (a.2.card:ℤ)=p := by
      by_contra hp
      have hh := hz a.2
      rw [if_neg hp,Submodule.mem_bot] at hh
      exact ha (by rw [hh,map_zero,Finsupp.zero_apply])
    have hh := hz a.2
    rw [if_pos hp,← fullBasis_piece P (γ.1-(a.2.card:ℤ),γ.2),Grading.mem_piece] at hh
    have hg := hh a.1 ha
    unfold fullDegree degree
    rw [hg,hp]
    simp only [sub_add_cancel]

theorem strand_eq_coordinatePiece (γ : ℤ × ℕ) (p : ℤ) :
    strand (V:=V) P γ p=coordinatePiece (fun s : Finset V =>
      if (s.card:ℤ)=p then P (γ.1-(s.card:ℤ),γ.2) else ⊥) := by
  ext z
  rw [mem_strand,mem_coordinatePiece]

instance piece_decomposition : DirectSum.Decomposition (piece (V:=V) P) :=
  basisGradingDecomposition (basis P) (degree P)

instance fullPiece_decomposition : DirectSum.Decomposition
    (fun g : (ℤ × ℕ) × ℤ => strand (V:=V) P g.1 g.2) :=
  basisGradingDecomposition (basis P) (fullDegree P)

theorem one_mem_piece : (1 : Total (K:=K) (A:=A) (V:=V))∈piece P 0 := by
  rw [piece_eq_coordinatePiece,Algebra.TensorProduct.one_def]
  have he : Simplicial.basis (V:=V) (k:=K) ∅=1 := by
    simp [Simplicial.basis,Module.Basis.exteriorAlgebra_eq_prod_map_sort]
  rw [← he]
  apply tmul_basis_mem_coordinatePiece
  change (1 : A) ∈ P (0,0)
  exact SetLike.one_mem_graded P

theorem mul_mem_piece (γ δ : ℤ × ℕ)
    (x y : Total (K:=K) (A:=A) (V:=V))
    (hx : x∈piece P γ) (hy : y∈piece P δ) : x*y∈piece P (γ+δ) := by
  rw [← sum_coefficients x,← sum_coefficients y,Finset.sum_mul]
  apply Submodule.sum_mem
  intro s _
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  intro t _
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hst : Disjoint s t
  · rw [Sublattice.faceBasis_mul_of_disjoint s t hst,TensorProduct.tmul_smul]
    apply (piece (V:=V) P (γ+δ)).smul_of_tower_mem
    rw [piece_eq_coordinatePiece]
    apply tmul_basis_mem_coordinatePiece
    have hm := SetLike.mul_mem_graded ((mem_piece P γ x).mp hx s)
      ((mem_piece P δ y).mp hy t)
    have he : (γ.1-(s.card:ℤ),γ.2)+(δ.1-(t.card:ℤ),δ.2)=
        ((γ+δ).1-((s∪t).card:ℤ),(γ+δ).2) := by
      rw [Finset.card_union_of_disjoint hst]
      apply Prod.ext
      · simp only [Prod.fst_add,Nat.cast_add]
        omega
      · rfl
    simpa only [he] using hm
  · rw [Sublattice.faceBasis_mul_of_not_disjoint s t hst,TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

/-- The actual tensor-exterior algebra has the paper's total bigrading. -/
instance piece_gradedAlgebra : GradedAlgebra (piece (V:=V) P) where
  __ := piece_decomposition P
  one_mem := one_mem_piece P
  mul_mem := by
    intro γ δ x y hx hy
    exact mul_mem_piece P γ δ x y hx hy

theorem piece_finite [∀ γ,Module.Finite K (P γ)] (γ : ℤ × ℕ) :
    Module.Finite K (piece (V:=V) P γ) := by
  rw [piece_eq_coordinatePiece]
  exact coordinatePiece_finite _

theorem strand_finite [∀ γ,Module.Finite K (P γ)] (γ : ℤ × ℕ) (p : ℤ) :
    Module.Finite K (strand (V:=V) P γ p) := by
  rw [strand_eq_coordinatePiece]
  letI : ∀ s : Finset V,Module.Finite K
      ↥(if (s.card:ℤ)=p then P (γ.1-(s.card:ℤ),γ.2) else (⊥ : Submodule K A)) := by
    intro s
    by_cases hs : (s.card : ℤ) = p
    · rw [if_pos hs]
      infer_instance
    · rw [if_neg hs]
      infer_instance
  exact coordinatePiece_finite _

def baseVariable (v : V) : A := algebraMap (MvPolynomial V K) A (MvPolynomial.X v)

abbrev D := TensorExteriorKoszul.parityDifferential (K:=K) (baseVariable (K:=K) (A:=A) (V:=V))

include hX in
theorem differential_piece (γ : ℤ × ℕ) (z : Total (K:=K) (A:=A) (V:=V))
    (hz : z∈piece P γ) : (D (K:=K) (A:=A) (V:=V)).d z∈piece P γ := by
  rw [← sum_coefficients z,map_sum]
  apply Submodule.sum_mem
  intro s _
  dsimp only [D,TensorExteriorKoszul.parityDifferential]
  rw [differential_tmul_exterior]
  apply Submodule.sum_mem
  intro v _
  apply (piece P γ).toAddSubgroup.zsmul_mem
  rw [piece_eq_coordinatePiece]
  apply tmul_basis_mem_coordinatePiece
  have hm := SetLike.mul_mem_graded (hX v.val) ((mem_piece P γ z).mp hz s)
  have hs := Finset.card_erase_of_mem v.property
  convert hm using 1 <;> try rfl
  apply congrArg P
  apply Prod.ext
  · simp only [Prod.fst_add]
    rw [hs]
    have hpos : 0<s.card := Finset.card_pos.mpr ⟨v.val,v.property⟩
    omega
  · simp only [Prod.snd_add,zero_add]

include hX in
theorem differential_strand (γ : ℤ × ℕ) (p : ℤ)
    (z : Total (K:=K) (A:=A) (V:=V)) (hz : z∈strand P γ p) :
    (D (K:=K) (A:=A) (V:=V)).d z∈strand P γ (p-1) := by
  rw [← sum_coefficients z,map_sum]
  apply Submodule.sum_mem
  intro s _
  by_cases hs : (s.card:ℤ)=p
  · dsimp only [D,TensorExteriorKoszul.parityDifferential]
    rw [differential_tmul_exterior]
    apply Submodule.sum_mem
    intro v _
    apply (strand P γ (p-1)).toAddSubgroup.zsmul_mem
    rw [strand_eq_coordinatePiece]
    apply tmul_basis_mem_coordinatePiece
    have hcard : ((s.erase v.val).card:ℤ)=p-1 := by
      rw [Finset.card_erase_of_mem v.property]
      have hpos : 0<s.card := Finset.card_pos.mpr ⟨v.val,v.property⟩
      omega
    rw [if_pos hcard]
    have hc := (mem_strand P γ p z).mp hz s
    rw [if_pos hs] at hc
    have hm := SetLike.mul_mem_graded (hX v.val) hc
    convert hm using 1 <;> try rfl
    apply congrArg P
    apply Prod.ext
    · simp only [Prod.fst_add]
      omega
    · simp only [Prod.snd_add,zero_add]
  · have hc := (mem_strand P γ p z).mp hz s
    rw [if_neg hs,Submodule.mem_bot] at hc
    rw [hc,TensorProduct.zero_tmul,map_zero]
    exact Submodule.zero_mem _

theorem strand_zero_negative (γ : ℤ × ℕ) (p : ℤ) (hp : p<0) :
    strand (V:=V) P γ p=⊥ := by
  rw [strand_eq_coordinatePiece]
  ext z
  rw [mem_coordinatePiece,Submodule.mem_bot]
  constructor
  · intro hz
    apply TensorExteriorKoszul.coordinates.injective
    ext s
    change coefficient s z=0
    have hs := hz s
    rw [if_neg (by omega),Submodule.mem_bot] at hs
    exact hs
  · intro hz
    subst z
    intro s
    simp only [map_zero]
    exact Submodule.zero_mem _

end FourPapers.BigradedTensorKoszul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BigradedTensorTor -/
section

/-!
# Actual polynomial Tor in the finite bigraded tensor strands

The comparison maps include the original auxiliary-degree module into A,
retain the original exterior basis with its signs, and preserve both the
internal degree and the homological degree. No comparison of homology is
assumed. The degree-zero outgoing differential is proved to vanish.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BigradedTensorTor

open Classical CommAlg CommAlg.Koszul BigradedPolynomialAlgebra
open FilteredTensorKoszul FilteredHomology
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  (hX : ∀ v,algebraMap (MvPolynomial V K) A (MvPolynomial.X v)∈P (1,0))

abbrev Coeff (m : ℕ) := auxiliaryModule (V:=V) P hX m
abbrev Coord (m p : ℕ) := PolynomialCoordinateTor.Coordinates (V:=V) (M:=Coeff P hX m) p
abbrev TorPiece (m : ℕ) (q : ℤ) (p : ℕ) :=
  GradedPolynomialModuleTor.piece (V:=V) (auxiliaryGrading P hX m) q p
abbrev Strand (m : ℕ) (q : ℤ) (p : ℕ) :=
  BigradedTensorKoszul.strand (V:=V) P (q,m) (p:ℤ)

def liftCoefficients (m p : ℕ) : Coord P hX m p →ₗ[K]
    BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V) :=
  (TensorExteriorKoszul.lift p).comp
    (Finsupp.mapRange.linearMap ((auxiliaryModule P hX m).subtype.restrictScalars K))

@[simp] theorem liftCoefficients_single (m p : ℕ)
    (s : Set.powersetCard V p) (a : Coeff P hX m) :
    liftCoefficients P hX m p (Finsupp.single s a)=a.val ⊗ₜ[K] Simplicial.basis s.val := by
  simp only [liftCoefficients,LinearMap.comp_apply,Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single,LinearMap.restrictScalars_apply,Submodule.subtype_apply,
    TensorExteriorKoszul.lift_single]

theorem coefficient_liftCoefficients (m p : ℕ) (x : Coord P hX m p) (s : Finset V) :
    coefficient s (liftCoefficients P hX m p x)=
      if hs : s ∈ Set.powersetCard V p then (x ⟨s,hs⟩).val else 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,Submodule.coe_zero]; split_ifs <;> rfl
  | add x y hx hy =>
      simp only [map_add,hx,hy,Finsupp.add_apply,Submodule.coe_add]
      split_ifs <;> simp only [add_zero]
  | single t a =>
      rw [liftCoefficients_single,coefficient_tmul_basis]
      by_cases hts : t.val=s
      · subst s
        rw [dif_pos t.property]
        simp only [if_pos rfl,if_true,Finsupp.single_eq_same]
      · by_cases hs : s ∈ Set.powersetCard V p
        · rw [dif_pos hs,Finsupp.single_eq_of_ne (by exact fun h => hts (congrArg Subtype.val h).symm)]
          simp only [hts,↓reduceIte,Submodule.coe_zero]
        · simp only [hs,↓reduceDIte,hts,↓reduceIte]

theorem liftCoefficients_mem (m : ℕ) (q : ℤ) (p : ℕ) (x : TorPiece P hX m q p) :
    liftCoefficients P hX m p x.val∈Strand (V:=V) P m q p := by
  rw [BigradedTensorKoszul.mem_strand]
  intro s
  rw [coefficient_liftCoefficients]
  by_cases hs : s ∈ Set.powersetCard V p
  · have hcard : s.card = p := hs
    rw [dif_pos hs,if_pos (by omega)]
    have h := (GradedPolynomialModuleTor.mem_piece
      (auxiliaryGrading P hX m) q p x.val).mp x.property ⟨s,hs⟩
    change (x.val ⟨s,hs⟩).val ∈ P (q-(p:ℤ),m) at h
    simpa only [hcard] using h
  · rw [dif_neg hs]
    exact Submodule.zero_mem _

def strandMap (m : ℕ) (q : ℤ) (p : ℕ) :
    TorPiece P hX m q p →ₗ[K] Strand (V:=V) P m q p :=
  ((liftCoefficients P hX m p).domRestrict (TorPiece P hX m q p)).codRestrict
    (Strand (V:=V) P m q p) (liftCoefficients_mem P hX m q p)

theorem strandMap_injective (m : ℕ) (q : ℤ) (p : ℕ) :
    Function.Injective (strandMap P hX m q p) := by
  intro x y h
  apply Subtype.ext
  apply Finsupp.ext
  intro s
  apply Subtype.ext
  have he := congrArg (fun z : Strand (V:=V) P m q p => coefficient s.val z.val) h
  simpa only [strandMap,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,
    coefficient_liftCoefficients,s.property,↓reduceDIte] using he

def strandInverseCoordinates (m : ℕ) (q : ℤ) (p : ℕ) (z : Strand (V:=V) P m q p) :
    Coord P hX m p :=
  Finsupp.equivFunOnFinite.symm (fun s : Set.powersetCard V p =>
    ⟨coefficient s.val z.val,Submodule.subset_span
      ⟨q-(p:ℤ),by
        have h := (BigradedTensorKoszul.mem_strand P (q,m) (p:ℤ) z.val).mp z.property s.val
        have hcard : s.val.card = p := s.property
        simpa only [hcard,if_pos rfl,if_true] using h⟩⟩)

theorem strandInverseCoordinates_mem (m : ℕ) (q : ℤ) (p : ℕ)
    (z : Strand (V:=V) P m q p) :
    strandInverseCoordinates P hX m q p z∈TorPiece P hX m q p := by
  rw [GradedPolynomialModuleTor.mem_piece]
  intro s
  change coefficient s.val z.val∈P (q-(p:ℤ),m)
  have h := (BigradedTensorKoszul.mem_strand P (q,m) (p:ℤ) z.val).mp z.property s.val
  have hcard : s.val.card = p := s.property
  simpa only [hcard,if_pos rfl,if_true] using h

theorem strandMap_surjective (m : ℕ) (q : ℤ) (p : ℕ) :
    Function.Surjective (strandMap (V:=V) P hX m q p) := by
  intro z
  refine ⟨⟨strandInverseCoordinates P hX m q p z,
    strandInverseCoordinates_mem P hX m q p z⟩,?_⟩
  apply Subtype.ext
  apply TensorExteriorKoszul.coordinates.injective
  ext s
  change coefficient s (liftCoefficients P hX m p _)=coefficient s z.val
  rw [coefficient_liftCoefficients]
  by_cases hs : s ∈ Set.powersetCard V p
  · rw [dif_pos hs]
    rfl
  · rw [dif_neg hs]
    have hcard : s.card ≠ p := hs
    have h := (BigradedTensorKoszul.mem_strand P (q,m) (p:ℤ) z.val).mp z.property s
    rw [if_neg (by omega),Submodule.mem_bot] at h
    exact h.symm

/-- Identity on the actual coefficient and exterior basis elements. -/
def strandEquiv (m : ℕ) (q : ℤ) (p : ℕ) :
    TorPiece P hX m q p ≃ₗ[K] Strand (V:=V) P m q p :=
  LinearEquiv.ofBijective (strandMap P hX m q p)
    ⟨strandMap_injective P hX m q p,strandMap_surjective P hX m q p⟩

theorem differential_liftCoefficients (m p : ℕ) (x : Coord P hX m (p+1)) :
    (BigradedTensorKoszul.D (K:=K) (A:=A) (V:=V)).d
      (liftCoefficients P hX m (p+1) x)=
      liftCoefficients P hX m p (PolynomialCoordinateTor.differential (K:=K) (V:=V) (M:=Coeff P hX m) p x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single s a =>
      rw [liftCoefficients_single]
      change TensorExteriorKoszul.differential
        (BigradedTensorKoszul.baseVariable (K:=K) (A:=A) (V:=V))
          (a.val ⊗ₜ[K] Simplicial.basis s.val)=_
      rw [differential_tmul_exterior]
      change _=liftCoefficients P hX m p
        (coordinateDifferential (MvPolynomial.X : V→MvPolynomial V K)
          (ModuleCat.of (MvPolynomial V K) (Coeff P hX m)) p (Finsupp.single s a))
      rw [coordinateDifferential_single,map_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [liftCoefficients_single]
      simp only [Units.smul_def]
      rw [TensorProduct.smul_tmul']
      change ((TauCeti.ExteriorAlgebra.basisEraseSign v.val s.val : ℤ) •
        (BigradedTensorKoszul.baseVariable (K:=K) (A:=A) (V:=V) v.val*a.val)) ⊗ₜ[K]
          Simplicial.basis (k:=K) (s.val.erase v.val)=
        ((MvPolynomial.X v.val : MvPolynomial V K) •
          ((TauCeti.ExteriorAlgebra.basisEraseSign v.val s.val : ℤ) • a.val)) ⊗ₜ[K]
          Simplicial.basis (k:=K) (s.val.erase v.val)
      rw [Algebra.smul_def (R:=MvPolynomial V K)]
      change ((TauCeti.ExteriorAlgebra.basisEraseSign v.val s.val : ℤ) •
        (BigradedTensorKoszul.baseVariable (K:=K) (A:=A) (V:=V) v.val*a.val)) ⊗ₜ[K]
          Simplicial.basis (k:=K) (s.val.erase v.val)=
        (BigradedTensorKoszul.baseVariable (K:=K) (A:=A) (V:=V) v.val*
          ((TauCeti.ExteriorAlgebra.basisEraseSign v.val s.val : ℤ) • a.val)) ⊗ₜ[K]
          Simplicial.basis (k:=K) (s.val.erase v.val)
      rw [Algebra.mul_smul_comm]

def differential (m : ℕ) (q : ℤ) (p : ℕ) :
    Strand (V:=V) P m q (p+1) →ₗ[K] Strand (V:=V) P m q p :=
  (((BigradedTensorKoszul.D (K:=K) (A:=A) (V:=V)).d).domRestrict
    (Strand (V:=V) P m q (p+1))).codRestrict (Strand (V:=V) P m q p) (by
      intro z
      change (BigradedTensorKoszul.D (K:=K) (A:=A) (V:=V)).d z.val ∈
        BigradedTensorKoszul.strand (V:=V) P (q,m) (p:ℤ)
      have h := BigradedTensorKoszul.differential_strand P hX (q,m) ((p+1:ℕ):ℤ)
        z.val z.property
      simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using h)

def previous (m : ℕ) (q : ℤ) : ∀ p : ℕ,
    Strand (V:=V) P m q p →ₗ[K] Strand (V:=V) P m q p.pred
  | 0 => 0
  | p+1 => differential P hX m q p

theorem previous_val (m : ℕ) (q : ℤ) (p : ℕ) (z : Strand (V:=V) P m q p) :
    (previous P hX m q p z).val=
      (BigradedTensorKoszul.D (K:=K) (A:=A) (V:=V)).d z.val := by
  cases p with
  | zero =>
      have h := BigradedTensorKoszul.differential_strand P hX (q,m) 0 z.val z.property
      have hz : (0 : ℤ)-1 = -1 := by omega
      rw [hz,BigradedTensorKoszul.strand_zero_negative P (q,m) (-1) (by omega),Submodule.mem_bot] at h
      exact h.symm
  | succ p => rfl

theorem previous_comp (m : ℕ) (q : ℤ) (p : ℕ) :
    (previous P hX m q p).comp (differential P hX m q p)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change (previous P hX m q p (differential P hX m q p z)).val = 0
  rw [previous_val]
  exact (BigradedTensorKoszul.D (K:=K) (A:=A) (V:=V)).square_zero z.val

abbrev Homology (m : ℕ) (q : ℤ) (p : ℕ) := FilteredHomology.Homology
  (differential (V:=V) P hX m q p) (previous P hX m q p) (previous_comp P hX m q p)

theorem strandEquiv_differential (m : ℕ) (q : ℤ) (p : ℕ)
    (z : TorPiece P hX m q (p+1)) :
    differential P hX m q p (strandEquiv P hX m q (p+1) z)=
      strandEquiv P hX m q p
        (GradedPolynomialModuleTor.differential (auxiliaryGrading P hX m)
          (auxiliaryGrading_X P hX m) q p z) :=
  Subtype.ext (differential_liftCoefficients P hX m p z.val)

theorem strandEquiv_previous (m : ℕ) (q : ℤ) (p : ℕ) (z : TorPiece P hX m q p) :
    previous P hX m q p (strandEquiv P hX m q p z)=
      strandEquiv P hX m q p.pred
        (GradedPolynomialModuleTor.previous (auxiliaryGrading P hX m)
          (auxiliaryGrading_X P hX m) q p z) := by
  cases p with
  | zero =>
      change (0 : Strand (V:=V) P m q 0) = strandEquiv P hX m q 0 0
      exact (strandEquiv P hX m q 0).toAddEquiv.map_zero.symm
  | succ p => exact strandEquiv_differential P hX m q p z

def cycleEquiv (m : ℕ) (q : ℤ) (p : ℕ) :
    LinearMap.ker (GradedPolynomialModuleTor.previous (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p) ≃ₗ[K] LinearMap.ker (previous P hX m q p) :=
  threeTermCyclesEquiv (R:=K)
    (Y:=TorPiece P hX m q p) (Z:=TorPiece P hX m q p.pred)
    (Y':=Strand (V:=V) P m q p) (Z':=Strand (V:=V) P m q p.pred)
    (GradedPolynomialModuleTor.previous (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p) (previous P hX m q p)
    (strandEquiv P hX m q p) (strandEquiv P hX m q p.pred)
    (fun z => (strandEquiv_previous P hX m q p z).symm)

theorem cycleEquiv_boundaries (m : ℕ) (q : ℤ) (p : ℕ) :
    (LinearMap.range (boundaryMap
      (GradedPolynomialModuleTor.differential (auxiliaryGrading P hX m)
        (auxiliaryGrading_X P hX m) q p)
      (GradedPolynomialModuleTor.previous (auxiliaryGrading P hX m)
        (auxiliaryGrading_X P hX m) q p)
      (GradedPolynomialModuleTor.previous_comp (auxiliaryGrading P hX m)
        (auxiliaryGrading_X P hX m) q p))).map
          (cycleEquiv P hX m q p).toLinearMap=
      LinearMap.range (boundaryMap (differential P hX m q p)
        (previous P hX m q p) (previous_comp P hX m q p)) :=
  threeTermCyclesEquiv_boundaries (R:=K)
    (X:=TorPiece P hX m q (p+1)) (Y:=TorPiece P hX m q p)
    (Z:=TorPiece P hX m q p.pred)
    (X':=Strand (V:=V) P m q (p+1)) (Y':=Strand (V:=V) P m q p)
    (Z':=Strand (V:=V) P m q p.pred)
    (GradedPolynomialModuleTor.differential (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p)
    (GradedPolynomialModuleTor.previous (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p)
    (GradedPolynomialModuleTor.previous_comp (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p)
    (differential P hX m q p) (previous P hX m q p) (previous_comp P hX m q p)
    (strandEquiv P hX m q (p+1)) (strandEquiv P hX m q p)
    (strandEquiv P hX m q p.pred)
    (fun z => (strandEquiv_differential P hX m q p z).symm)
    (fun z => (strandEquiv_previous P hX m q p z).symm)

/-- The finite actual tensor-strand homology computes the degree-q part
of the literal derived Tor of A_(*,m). -/
def homologyEquiv (m : ℕ) (q : ℤ) (p : ℕ) :
    GradedPolynomialModuleTor.Homology (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p ≃ₗ[K] Homology P hX m q p :=
  threeTermHomologyEquiv (R:=K)
    (X:=TorPiece P hX m q (p+1)) (Y:=TorPiece P hX m q p)
    (Z:=TorPiece P hX m q p.pred)
    (X':=Strand (V:=V) P m q (p+1)) (Y':=Strand (V:=V) P m q p)
    (Z':=Strand (V:=V) P m q p.pred)
    (GradedPolynomialModuleTor.differential (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p)
    (GradedPolynomialModuleTor.previous (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p)
    (GradedPolynomialModuleTor.previous_comp (auxiliaryGrading P hX m)
      (auxiliaryGrading_X P hX m) q p)
    (differential P hX m q p) (previous P hX m q p) (previous_comp P hX m q p)
    (strandEquiv P hX m q (p+1)) (strandEquiv P hX m q p)
    (strandEquiv P hX m q p.pred)
    (fun z => (strandEquiv_differential P hX m q p z).symm)
    (fun z => (strandEquiv_previous P hX m q p z).symm)

theorem bettiNumber_eq_finrank (m p : ℕ) (q : ℤ) :
    BigradedPolynomialAlgebra.bettiNumber P hX m p q=
      Module.finrank K (Homology P hX m q p) := by
  rw [BigradedPolynomialAlgebra.bettiNumber,GradedPolynomialModuleTor.bettiNumber_eq_finrank]
  exact (homologyEquiv P hX m q p).finrank_eq

end FourPapers.BigradedTensorTor

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BigradedTotalHomology -/
section

/-!
# Fixed-bidegree total homology and the individual genuine Tor groups

The homological decomposition is an actual direct-sum decomposition of the
finite (q,m) tensor component. Equality of every individual graded Betti
number therefore implies equality of the total square-zero homology used
by the multiplicative filtration argument. No total-homology dimension
equality is added as a hypothesis in place of the paper's Betti hypothesis.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BigradedTotalHomology

open Classical CommAlg FilteredHomology BigradedTensorKoszul
open GradedHomologyDecomposition IntegerFiltered IntegerFiltered.MultiplicativeFiltration

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  (hX : ∀ v,algebraMap (MvPolynomial V K) A (MvPolynomial.X v)∈P (1,0))

abbrev Component (γ : ℤ × ℕ) := piece (V:=V) P γ
abbrev ComponentIndex (γ : ℤ × ℕ) := {a : Index (V:=V) P // degree P a=γ}

instance componentAddCommGroup (γ : ℤ × ℕ) : AddCommGroup (Component (V:=V) P γ) :=
  Submodule.addCommGroup (R:=K) (M:=Total (K:=K) (A:=A) (V:=V)) (piece P γ)

instance componentModule (γ : ℤ × ℕ) : Module K (Component (V:=V) P γ) :=
  Submodule.module (R:=K) (M:=Total (K:=K) (A:=A) (V:=V)) (piece P γ)

def componentBasis (γ : ℤ × ℕ) : Module.Basis (ComponentIndex (V:=V) P γ) K (Component (V:=V) P γ) :=
  Grading.restrictedBasis (basis P) (fun a => degree P a=γ)

theorem componentBasis_repr (γ : ℤ × ℕ) (x : Component (V:=V) P γ)
    (a : ComponentIndex (V:=V) P γ) :
    (componentBasis (V:=V) P γ).repr x a=(basis (V:=V) P).repr x.val a.val :=
  restrictedBasis_repr (basis (V:=V) P) (fun a => degree P a=γ) x a

def homologicalPiece (γ : ℤ × ℕ) (p : ℤ) : Submodule K (Component (V:=V) P γ) :=
  Grading.Piece (componentBasis (V:=V) P γ) (fun a => (a.val.2.card:ℤ)) p

instance homologicalPieceAddCommGroup (γ : ℤ × ℕ) (p : ℤ) :
    AddCommGroup (homologicalPiece (V:=V) P γ p) :=
  Submodule.addCommGroup (R:=K) (M:=Component (V:=V) P γ) (homologicalPiece (V:=V) P γ p)

instance homologicalPieceModule (γ : ℤ × ℕ) (p : ℤ) :
    Module K (homologicalPiece (V:=V) P γ p) :=
  Submodule.module (R:=K) (M:=Component (V:=V) P γ) (homologicalPiece (V:=V) P γ p)

instance homologicalPiece_decomposition (γ : ℤ × ℕ) :
    DirectSum.Decomposition (homologicalPiece (V:=V) P γ) :=
  basisGradingDecomposition (componentBasis (V:=V) P γ) (fun a => (a.val.2.card:ℤ))

theorem strand_le_piece (γ : ℤ × ℕ) (p : ℤ) : strand (V:=V) P γ p≤piece P γ := by
  intro x hx
  rw [strand,Grading.mem_piece] at hx
  rw [piece,Grading.mem_piece]
  intro a ha
  exact congrArg Prod.fst (hx a ha)

theorem mem_homologicalPiece (γ : ℤ × ℕ) (p : ℤ) (x : Component (V:=V) P γ) :
    x∈homologicalPiece (V:=V) P γ p ↔ x.val∈strand P γ p := by
  rw [homologicalPiece,Grading.mem_piece,strand,Grading.mem_piece]
  constructor
  · intro h a ha
    have hγ : degree P a=γ := (Grading.mem_piece (basis P) (degree P) γ x.val).mp x.property a ha
    apply Prod.ext hγ
    exact h ⟨a,hγ⟩ (by
      rw [componentBasis_repr]
      exact ha)
  · intro h a ha
    have ha' : (basis P).repr x.val a.val≠0 := by
      rwa [componentBasis_repr] at ha
    exact congrArg Prod.snd (h a.val ha')

def strandEquivPiece (γ : ℤ × ℕ) (p : ℤ) :
    strand (V:=V) P γ p ≃ₗ[K] homologicalPiece (V:=V) P γ p where
  toFun x := ⟨⟨x.val,strand_le_piece P γ p x.property⟩,
    (mem_homologicalPiece (V:=V) P γ p _).mpr x.property⟩
  invFun x := ⟨x.val.val,(mem_homologicalPiece (V:=V) P γ p x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def d (γ : ℤ × ℕ) : Module.End K (Component (V:=V) P γ) :=
  componentDifferential (D (K:=K) (A:=A) (V:=V)) (piece P γ) (differential_piece P hX γ)

theorem d_comp (γ : ℤ × ℕ) : (d P hX γ).comp (d P hX γ)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (D (K:=K) (A:=A) (V:=V)).square_zero x.val

theorem d_homogeneous (γ : ℤ × ℕ) (p : ℤ) (x : Component (V:=V) P γ)
    (hx : x∈homologicalPiece (V:=V) P γ p) : d P hX γ x∈homologicalPiece (V:=V) P γ (p+(-1)) := by
  rw [mem_homologicalPiece] at hx ⊢
  change (D (K:=K) (A:=A) (V:=V)).d x.val ∈ strand (V:=V) P γ (p+(-1))
  simpa only [sub_eq_add_neg] using differential_strand P hX γ p x.val hx

abbrev TotalHomology (γ : ℤ × ℕ) := Homology (d (V:=V) P hX γ) (d P hX γ) (d_comp P hX γ)
abbrev HomologicalHomology (γ : ℤ × ℕ) (p : ℤ) :=
  DegreeHomology (homologicalPiece (V:=V) P γ) (d P hX γ) (d_comp P hX γ) p

instance homologicalHomologyAddCommGroup (γ : ℤ × ℕ) (p : ℤ) :
    AddCommGroup (HomologicalHomology (V:=V) P hX γ p) :=
  GradedHomologyDecomposition.degreeHomologyAddCommGroup
    (homologicalPiece (V:=V) P γ) (d P hX γ) (d_comp P hX γ) p

instance homologicalHomologyModule (γ : ℤ × ℕ) (p : ℤ) :
    Module K (HomologicalHomology (V:=V) P hX γ p) :=
  GradedHomologyDecomposition.degreeHomologyModule
    (homologicalPiece (V:=V) P γ) (d P hX γ) (d_comp P hX γ) p

def incoming (γ : ℤ × ℕ) (p : ℤ) :
    homologicalPiece (V:=V) P γ (p+1) →ₗ[K] homologicalPiece (V:=V) P γ p :=
  ((d P hX γ).domRestrict (homologicalPiece (V:=V) P γ (p+1))).codRestrict
    (homologicalPiece (V:=V) P γ p) (by
      intro x
      change d P hX γ x.val ∈ homologicalPiece (V:=V) P γ p
      simpa only [add_neg_cancel_right] using d_homogeneous P hX γ (p+1) x.val x.property)

theorem incoming_comp (γ : ℤ × ℕ) (p : ℤ) :
    ((d P hX γ).domRestrict (homologicalPiece (V:=V) P γ p)).comp (incoming P hX γ p)=0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (d_comp P hX γ) x.val

theorem incoming_is_boundary (γ : ℤ × ℕ) (p : ℤ)
    (x : homologicalPiece (V:=V) P γ (p+1)) :
    (incoming P hX γ p x).val∈LinearMap.range (d P hX γ) := ⟨x.val,rfl⟩

theorem boundary_homogeneous_preimage (γ : ℤ × ℕ) (p : ℤ)
    (x : Component (V:=V) P γ) (hx : d P hX γ x∈homologicalPiece (V:=V) P γ p) :
    ∃ y : homologicalPiece (V:=V) P γ (p+1),(incoming P hX γ p y).val=d P hX γ x := by
  refine ⟨DirectSum.decompose (homologicalPiece (V:=V) P γ) x (p+1),?_⟩
  change d P hX γ (DirectSum.decompose (homologicalPiece (V:=V) P γ) x (p+1)).val=_
  rw [GradedHomologyDecomposition.differential_projection (homologicalPiece (V:=V) P γ)
    (d P hX γ) (-1) (d_homogeneous P hX γ),add_neg_cancel_right,
    DirectSum.decompose_of_mem_same (homologicalPiece (V:=V) P γ) hx]

section IncomingComparison
attribute [local irreducible] d incoming homologicalPiece

set_option backward.isDefEq.respectTransparency true in
def incomingHomologyEquiv (γ : ℤ × ℕ) (p : ℤ) :
    FilteredHomology.Homology (K:=K)
      (X:=homologicalPiece (V:=V) P γ (p+1)) (Y:=homologicalPiece (V:=V) P γ p)
      (Z:=Component (V:=V) P γ) (incoming (V:=V) P hX γ p)
      ((d P hX γ).domRestrict (homologicalPiece (V:=V) P γ p)) (incoming_comp P hX γ p) ≃ₗ[K]
        HomologicalHomology P hX γ p :=
  degreeHomologyEquiv (K:=K) (M:=Component (V:=V) P γ) (I:=ℤ)
    (X:=homologicalPiece (V:=V) P γ (p+1))
    (P:=homologicalPiece (V:=V) P γ) (d:=d P hX γ) (hdd:=d_comp P hX γ) (i:=p)
    (f:=incoming P hX γ p) (hfd:=incoming_comp P hX γ p)
    (hf:=incoming_is_boundary P hX γ p)
    (hfill:=boundary_homogeneous_preimage P hX γ p)

end IncomingComparison

def strandInComponent (γ : ℤ × ℕ) (p : ℤ) :
    strand (V:=V) P γ p →ₗ[K] Component (V:=V) P γ :=
  (strand P γ p).inclusion (strand_le_piece P γ p)

theorem strandInComponent_injective (γ : ℤ × ℕ) (p : ℤ) :
    Function.Injective (strandInComponent (V:=V) P γ p) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Component (V:=V) P γ => z.val) h

/-- Every natural homological degree agrees with the actual Tor strand,
including p=0 with its zero outgoing differential. -/
def tensorHomologyEquiv (m : ℕ) (q : ℤ) (p : ℕ) :
    BigradedTensorTor.Homology (V:=V) P hX m q p ≃ₗ[K]
      HomologicalHomology P hX (q,m) (p:ℤ) := by
  let f : strand (V:=V) P (q,m) ((p+1:ℕ):ℤ) →ₗ[K]
      strand (V:=V) P (q,m) (p:ℤ) := BigradedTensorTor.differential P hX m q p
  let g : strand (V:=V) P (q,m) (p:ℤ) →ₗ[K]
      strand (V:=V) P (q,m) (p.pred:ℤ) := BigradedTensorTor.previous P hX m q p
  let hfg := BigradedTensorTor.previous_comp P hX m q p
  let j : strand (V:=V) P (q,m) (p.pred:ℤ) →ₗ[K] Component (V:=V) P (q,m) :=
    strandInComponent (V:=V) P (q,m) (p.pred:ℤ)
  let eX : strand (V:=V) P (q,m) ((p+1:ℕ):ℤ) ≃ₗ[K]
      homologicalPiece (V:=V) P (q,m) ((p:ℤ)+1) :=
    (strandEquivPiece P (q,m) ((p+1:ℕ):ℤ)).trans
    (LinearEquiv.ofEq _ _ (by simp only [Nat.cast_add,Nat.cast_one]))
  let eY : strand (V:=V) P (q,m) (p:ℤ) ≃ₗ[K]
      homologicalPiece (V:=V) P (q,m) (p:ℤ) := strandEquivPiece P (q,m) (p:ℤ)
  let H := homologyEquiv_postcompose (R:=K)
    (X:=strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)) (Y:=strand (V:=V) P (q,m) (p:ℤ))
    (Z:=strand (V:=V) P (q,m) (p.pred:ℤ)) (W:=Component (V:=V) P (q,m))
    f g hfg j (strandInComponent_injective P (q,m) (p.pred:ℤ))
  refine H.trans ((threeTermHomologyEquiv (R:=K)
    (X:=strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)) (Y:=strand (V:=V) P (q,m) (p:ℤ))
    (Z:=Component (V:=V) P (q,m))
    (X':=homologicalPiece (V:=V) P (q,m) ((p:ℤ)+1))
    (Y':=homologicalPiece (V:=V) P (q,m) (p:ℤ)) (Z':=Component (V:=V) P (q,m))
    f (j.comp g) (postcompose_comp_zero f g hfg j)
    (incoming P hX (q,m) (p:ℤ)) ((d P hX (q,m)).domRestrict (homologicalPiece (V:=V) P (q,m) (p:ℤ)))
    (incoming_comp P hX (q,m) (p:ℤ)) eX eY (LinearEquiv.refl K _) ?_ ?_).trans
      (incomingHomologyEquiv P hX (q,m) (p:ℤ)))
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro x
    apply Subtype.ext
    exact BigradedTensorTor.previous_val P hX m q p x

theorem bettiNumber_eq_homological_finrank (m p : ℕ) (q : ℤ) :
    BigradedPolynomialAlgebra.bettiNumber P hX m p q=
      Module.finrank K (HomologicalHomology P hX (q,m) (p:ℤ)) := by
  rw [BigradedTensorTor.bettiNumber_eq_finrank]
  exact (tensorHomologyEquiv P hX m q p).finrank_eq

theorem homological_negative (γ : ℤ × ℕ) (p : ℤ) (hp : p<0) :
    Subsingleton (HomologicalHomology (V:=V) P hX γ p) := by
  have hzero : ∀ x : degreeCycles (homologicalPiece (V:=V) P γ) (d P hX γ) p,x=0 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hx := (mem_homologicalPiece (V:=V) P γ p x.val.val).mp x.property
    rw [strand_zero_negative P γ p hp,Submodule.mem_bot] at hx
    exact hx
  letI : Subsingleton (degreeCycles (homologicalPiece (V:=V) P γ) (d P hX γ) p) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  infer_instance

instance component_finite [∀ γ,Module.Finite K (P γ)] (γ : ℤ × ℕ) :
    Module.Finite K (Component (V:=V) P γ) := piece_finite P γ

instance homologicalHomology_finite [∀ γ,Module.Finite K (P γ)] (γ : ℤ × ℕ) (p : ℤ) :
    Module.Finite K (HomologicalHomology (V:=V) P hX γ p) := by
  unfold HomologicalHomology DegreeHomology
  infer_instance

section Comparison
variable {B : Type u} [CommRing B] [Algebra K B] [Algebra (MvPolynomial V K) B]
  [IsScalarTower K (MvPolynomial V K) B]
  (Q : ℤ × ℕ → Submodule K B) [GradedAlgebra Q]
  (hY : ∀ v,algebraMap (MvPolynomial V K) B (MvPolynomial.X v)∈Q (1,0))
  [∀ γ,Module.Finite K (P γ)] [∀ γ,Module.Finite K (Q γ)]

/-- The paper's individual Betti equality implies the total finite
homology equality needed for the cycle-lifting criterion. -/
theorem total_finrank_eq_of_betti_eq (m : ℕ) (q : ℤ)
    (hβ : ∀ p,BigradedPolynomialAlgebra.bettiNumber P hX m p q=
      BigradedPolynomialAlgebra.bettiNumber Q hY m p q) :
    Module.finrank K (TotalHomology (V:=V) P hX (q,m))=
      Module.finrank K (TotalHomology Q hY (q,m)) := by
  apply GradedHomologyDecomposition.finrank_total_eq_of_degree_eq
    (homologicalPiece (V:=V) P (q,m)) (homologicalPiece Q (q,m))
    (d P hX (q,m)) (d Q hY (q,m)) (d_comp P hX (q,m)) (d_comp Q hY (q,m))
    (cycles_homogeneous _ _ (-1) (d_homogeneous P hX (q,m)))
    (boundaries_homogeneous _ _ (-1) (d_homogeneous P hX (q,m)))
    (cycles_homogeneous _ _ (-1) (d_homogeneous Q hY (q,m)))
    (boundaries_homogeneous _ _ (-1) (d_homogeneous Q hY (q,m)))
  intro p
  by_cases hp : 0≤p
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [← bettiNumber_eq_homological_finrank,← bettiNumber_eq_homological_finrank]
    exact hβ n
  · letI := homological_negative P hX (q,m) p (lt_of_not_ge hp)
    letI := homological_negative Q hY (q,m) p (lt_of_not_ge hp)
    simp only [Module.finrank_zero_of_subsingleton]

end Comparison
end FourPapers.BigradedTotalHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.AssociatedCoefficientGrading -/
section

/-! # The genuine homogeneous grading of the associated coefficient algebra

Homogeneous projections act coefficientwise on the actual Rees algebra and
preserve its strict ideal. Their induced maps separate the homogeneous
pieces of the quotient. This proves both direct-sum independence and
spanning for the submodules `associatedPiece (P i)`; neither is assumed.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical DirectSum
open scoped BigOperators

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A]
  [AddMonoid Γ] [DecidableEq Γ]
  (F : MultiplicativeFiltration K A) (P : Γ → Submodule K A)
  [GradedAlgebra P] (hF : ∀ n,SetLike.IsHomogeneous P (F.level n))

/-- The original homogeneous projection on every Laurent coefficient. -/
def reesHomogeneousProjection (i : Γ) : F.rees →ₗ[K] F.rees where
  toFun p := ⟨AddMonoidAlgebra.map (GradedAlgebra.proj P i).toAddMonoidHom p.val,
    fun n => hF n i (p.property n)⟩
  map_add' p q := by
    apply Subtype.ext
    exact AddMonoidAlgebra.map_add _ _ _
  map_smul' c p := by
    apply Subtype.ext
    ext n
    exact (GradedAlgebra.proj P i).map_smul c (p.val.coeff n)

@[simp] theorem reesHomogeneousProjection_coeff (i : Γ) (p : F.rees) (n : ℤ) :
    (F.reesHomogeneousProjection P hF i p).val.coeff n=
      GradedAlgebra.proj P i (p.val.coeff n) := rfl

theorem reesHomogeneousProjection_strict (i : Γ) (p : F.rees)
    (hp : p∈F.strictIdeal.asIdeal.restrictScalars K) :
    F.reesHomogeneousProjection P hF i p∈F.strictIdeal.asIdeal.restrictScalars K := by
  change p∈F.strictIdeal.asIdeal at hp
  change F.reesHomogeneousProjection P hF i p∈F.strictIdeal.asIdeal
  rw [TwoSidedIdeal.mem_asIdeal,F.mem_strictIdeal] at hp ⊢
  intro n
  exact hF (n-1) i (hp n)

/-- A homogeneous projection on the literal Rees quotient. -/
def associatedHomogeneousProjection (i : Γ) :
    F.AssociatedGraded →ₗ[K] F.AssociatedGraded :=
  Submodule.mapQ (F.strictIdeal.asIdeal.restrictScalars K)
    (F.strictIdeal.asIdeal.restrictScalars K) (F.reesHomogeneousProjection P hF i)
    (F.reesHomogeneousProjection_strict P hF i)

@[simp] theorem associatedHomogeneousProjection_leading (i : Γ) (p : F.rees) :
    F.associatedHomogeneousProjection P hF i (F.leadingMap p)=
      F.leadingMap (F.reesHomogeneousProjection P hF i p) := rfl

@[simp] theorem associatedHomogeneousProjection_symbol (i : Γ) (n : ℤ) (a : F.level n) :
    F.associatedHomogeneousProjection P hF i (F.symbol n a)=
      F.symbol n ⟨GradedAlgebra.proj P i a.val,hF n i a.property⟩ := by
  change F.leadingMap (F.reesHomogeneousProjection P hF i (F.monomial n a))=_
  apply congrArg F.leadingMap
  apply Subtype.ext
  exact AddMonoidAlgebra.map_single _ _ _

theorem associatedHomogeneousProjection_same (i : Γ) {x : F.AssociatedGraded}
    (hx : x∈F.associatedPiece (P i)) :
    F.associatedHomogeneousProjection P hF i x=x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n,a,ha,rfl⟩ := hx
      rw [F.associatedHomogeneousProjection_symbol]
      apply congrArg (F.symbol n)
      apply Subtype.ext
      exact DirectSum.decompose_of_mem_same P ha
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy]
  | smul c x hx ih => rw [map_smul,ih]

theorem associatedHomogeneousProjection_ne (i j : Γ) (hij : j≠i)
    {x : F.AssociatedGraded} (hx : x∈F.associatedPiece (P j)) :
    F.associatedHomogeneousProjection P hF i x=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n,a,ha,rfl⟩ := hx
      rw [F.associatedHomogeneousProjection_symbol]
      have he : (⟨GradedAlgebra.proj P i a.val,hF n i a.property⟩ : F.level n)=0 :=
        Subtype.ext (DirectSum.decompose_of_mem_ne P ha hij)
      rw [he,map_zero]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

theorem associatedHomogeneousProjection_coe (i : Γ)
    (z : ⨁ j,F.associatedPiece (P j)) :
    F.associatedHomogeneousProjection P hF i
      (DirectSum.coeLinearMap (fun j => F.associatedPiece (P j)) z)=(z i).val := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero,DirectSum.zero_apply,Submodule.coe_zero]
  | of j x =>
      rw [DirectSum.coeLinearMap_of]
      by_cases hji : j=i
      · subst j
        rw [DirectSum.of_eq_same]
        exact F.associatedHomogeneousProjection_same P hF i x.property
      · rw [DirectSum.of_eq_of_ne (β := fun j => F.associatedPiece (P j)) j i x (Ne.symm hji),Submodule.coe_zero]
        exact F.associatedHomogeneousProjection_ne P hF i j hji x.property
  | add x y hx hy =>
      simpa only [map_add,DirectSum.add_apply,Submodule.coe_add] using congrArg₂ (·+·) hx hy

include hF in
theorem associatedPiece_coe_injective : Function.Injective
    (DirectSum.coeLinearMap (fun i => F.associatedPiece (P i))) := by
  intro x y h
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  rw [← F.associatedHomogeneousProjection_coe P hF i x,
    ← F.associatedHomogeneousProjection_coe P hF i y,h]

include hF in
theorem associatedPiece_coe_surjective : Function.Surjective
    (DirectSum.coeLinearMap (fun i => F.associatedPiece (P i))) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro x hx
  clear hx
  induction x using F.associated_induction with
  | h0 => exact Submodule.zero_mem _
  | hadd x y hx hy => exact Submodule.add_mem _ hx hy
  | hsymbol n a =>
      let s := (DirectSum.decompose P a.val).support
      let b : Γ → F.level n := fun i =>
        ⟨(DirectSum.decompose P a.val i).val,hF n i a.property⟩
      have hb : (∑ i∈s,b i)=a := by
        apply Subtype.ext
        simpa only [Submodule.coe_sum,b,s] using DirectSum.sum_support_decompose P a.val
      rw [← hb,map_sum]
      apply Submodule.sum_mem
      intro i hi
      refine ⟨DirectSum.of (fun j => F.associatedPiece (P j)) i
        ⟨F.symbol n (b i),F.symbol_mem_associatedPiece (P i) n (b i)
          (DirectSum.decompose P a.val i).property⟩,?_⟩
      exact DirectSum.coeLinearMap_of _ _ _

include hF in
/-- The actual associated homogeneous submodules are an internal direct sum. -/
theorem associatedPiece_isInternal :
    DirectSum.IsInternal (fun i => F.associatedPiece (P i)) :=
  ⟨F.associatedPiece_coe_injective P hF,F.associatedPiece_coe_surjective P hF⟩

theorem associatedPiece_one : (1 : F.AssociatedGraded)∈F.associatedPiece (P 0) := by
  rw [← F.symbol_one]
  exact F.symbol_mem_associatedPiece (P 0) 0 _ (SetLike.one_mem_graded P)

theorem associatedPiece_mul (i j : Γ) {x y : F.AssociatedGraded}
    (hx : x∈F.associatedPiece (P i)) (hy : y∈F.associatedPiece (P j)) :
    x*y∈F.associatedPiece (P (i+j)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n,a,ha,rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨m,b,hb,rfl⟩ := hy
          rw [F.symbol_mul]
          exact F.symbol_mem_associatedPiece (P (i+j)) (n+m) _
            (SetLike.mul_mem_graded ha hb)
      | zero => simpa only [mul_zero] using (F.associatedPiece (P (i+j))).zero_mem
      | add y z hy hz ihy ihz =>
          simpa only [mul_add] using (F.associatedPiece (P (i+j))).add_mem ihy ihz
      | smul c y hy ih =>
          simpa only [mul_smul_comm] using (F.associatedPiece (P (i+j))).smul_mem c ih
  | zero => simpa only [zero_mul] using (F.associatedPiece (P (i+j))).zero_mem
  | add x z hx hz ihx ihz =>
      simpa only [add_mul] using (F.associatedPiece (P (i+j))).add_mem ihx ihz
  | smul c x hx ih =>
      simpa only [smul_mul_assoc] using (F.associatedPiece (P (i+j))).smul_mem c ih

/-- The grading is supplied with its proved decomposition, not just with
closure under products. -/
def associatedGradingAlgebra : GradedAlgebra (fun i => F.associatedPiece (P i)) := by
  letI : SetLike.GradedMonoid (fun i => F.associatedPiece (P i)) :=
    { one_mem := F.associatedPiece_one P
      mul_mem := by
        intro i j x y hx hy
        exact F.associatedPiece_mul P i j hx hy }
  exact (F.associatedPiece_isInternal P hF).gradedAlgebra

/-- Finite-dimensionality of a homogeneous component survives passage to
the actual associated algebra, using exhaustion and separation. -/
theorem associatedPiece_finite_of_finite (W : Submodule K A) [FiniteDimensional K W] :
    Module.Finite K (F.associatedPiece W) := by
  obtain ⟨L,hL,N,hN⟩ := F.exists_component_bounds W
  exact F.associatedPiece_finite W L hL N hN

theorem associatedVariable_mem (i : Γ) (n : ℤ) (a : A)
    (ha : a∈F.level n) (hPi : a∈P i) :
    F.symbol n ⟨a,ha⟩∈F.associatedPiece (P i) :=
  F.symbol_mem_associatedPiece (P i) n ⟨a,ha⟩ hPi

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.AssociatedPolynomialAlgebra -/
section

/-! # The polynomial action on the actual associated coefficient algebra -/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (F : MultiplicativeFiltration K A)

/-- These structures extend exactly the existing ring structures of the
same Rees subalgebra and ideal quotient. -/
instance (priority := 1200) reesCommRing : CommRing F.rees :=
  Subalgebra.toCommRing F.rees

end FourPapers.IntegerFiltered.MultiplicativeFiltration

namespace FourPapers.FilteredTensorKoszul

open IntegerFiltered

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V]
  (F : MultiplicativeFiltration K A) (w : V → ℤ)
  (x : V → A) (hx : ∀ v,x v∈F.level (w v))

/-- Variables act by their literal leading symbols. -/
def associatedPolynomialMap : MvPolynomial V K →ₐ[K] F.AssociatedGraded :=
  MvPolynomial.aeval (leadingVariable F w x hx)

def associatedPolynomialAlgebra : Algebra (MvPolynomial V K) F.AssociatedGraded :=
  (associatedPolynomialMap F w x hx).toAlgebra

theorem associatedPolynomialScalarTower :
    @IsScalarTower K (MvPolynomial V K) F.AssociatedGraded inferInstance
      (associatedPolynomialAlgebra F w x hx).toSMul inferInstance := by
  letI : Algebra (MvPolynomial V K) F.AssociatedGraded := associatedPolynomialAlgebra F w x hx
  exact IsScalarTower.of_algebraMap_eq (R:=K) (S:=MvPolynomial V K) (A:=F.AssociatedGraded)
    (fun c => ((associatedPolynomialMap F w x hx).commutes c).symm)

/-- The actual associated quotient, with the chosen polynomial action
recorded in the type. Its ring and coefficient-algebra structures are
definitionally those of `F.AssociatedGraded`. -/
def AssociatedPolynomialCarrier (w' : V → ℤ) (x' : V → A)
    (_hx' : ∀ v, x' v ∈ F.level (w' v)) : Type u := F.AssociatedGraded

instance associatedCarrierCommRing : CommRing (AssociatedPolynomialCarrier F w x hx) :=
  inferInstanceAs (CommRing F.AssociatedGraded)

instance associatedCarrierAlgebra : Algebra K (AssociatedPolynomialCarrier F w x hx) :=
  inferInstanceAs (Algebra K F.AssociatedGraded)

instance associatedCarrierPolynomialAlgebra :
    Algebra (MvPolynomial V K) (AssociatedPolynomialCarrier F w x hx) :=
  associatedPolynomialAlgebra F w x hx

instance associatedCarrierScalarTower :
    IsScalarTower K (MvPolynomial V K) (AssociatedPolynomialCarrier F w x hx) :=
  associatedPolynomialScalarTower F w x hx

/-- This is an identity on values, identifying the action-carrying alias
with the literal associated coefficient algebra. -/
def associatedCarrierEquiv : AssociatedPolynomialCarrier F w x hx ≃ₐ[K] F.AssociatedGraded :=
  AlgEquiv.refl

@[simp] theorem associatedPolynomialMap_X (v : V) :
    associatedPolynomialMap F w x hx (MvPolynomial.X v)=leadingVariable F w x hx v :=
  MvPolynomial.aeval_X _ _

theorem associatedPolynomialVariable_mem
    {Γ : Type*} [AddMonoid Γ] [DecidableEq Γ]
    (P : Γ → Submodule K A) [GradedAlgebra P]
    (g : Γ) (hX : ∀ v,x v∈P g) (v : V) :
    associatedPolynomialMap F w x hx (MvPolynomial.X v)∈F.associatedPiece (P g) := by
  rw [associatedPolynomialMap_X]
  exact F.symbol_mem_associatedPiece (P g) (w v) ⟨x v,hx v⟩ (hX v)

end FourPapers.FilteredTensorKoszul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BigradedTensorFiltration -/
section

/-! # Homogeneity of the actual filtered tensor Koszul algebra -/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BigradedTensorKoszul

open Classical CommAlg FilteredTensorKoszul IntegerFiltered DirectSum
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]

/-- Homogeneous decomposition commutes with extraction of the actual
exterior coefficient, with the exterior contribution removed from q. -/
theorem coefficient_decompose (γ : ℤ × ℕ) (s : Finset V)
    (z : Total (K:=K) (A:=A) (V:=V)) :
    coefficient s (DirectSum.decompose (piece P) z γ).val=
      (DirectSum.decompose P (coefficient s z) (γ.1-(s.card:ℤ),γ.2)).val := by
  refine DirectSum.Decomposition.inductionOn (piece P) ?_ ?_ ?_ z
  · simp only [map_zero,DirectSum.decompose_zero,DirectSum.zero_apply,Submodule.coe_zero]
  · intro δ x
    have hc := (mem_piece P δ x.val).mp x.property s
    by_cases hδ : δ=γ
    · subst δ
      rw [DirectSum.decompose_of_mem_same (piece P) x.property,
        DirectSum.decompose_of_mem_same P hc]
    · rw [DirectSum.decompose_of_mem_ne (piece P) x.property hδ,map_zero,
        DirectSum.decompose_of_mem_ne P hc]
      intro he
      apply hδ
      apply Prod.ext
      · have h := congrArg Prod.fst he
        change δ.1-(s.card:ℤ)=γ.1-(s.card:ℤ) at h
        omega
      · have h := congrArg (fun t : ℤ × ℕ => t.2) he
        exact h
  · intro x y hx hy
    simp only [DirectSum.decompose_add,DirectSum.add_apply,Submodule.coe_add,map_add,hx,hy]

variable (F : MultiplicativeFiltration K A) (w : V → ℤ)
  (hF : ∀ n,SetLike.IsHomogeneous P (F.level n))

include hF in
/-- The coefficientwise weight filtration is homogeneous for the actual
internal and auxiliary grading of K(A). -/
theorem filtration_homogeneous (n : ℤ) :
    SetLike.IsHomogeneous (piece (V:=V) P) ((filtration F w).level n) := by
  intro γ z hz
  change (DirectSum.decompose (piece (V:=V) P) z γ).val ∈ FilteredTensorKoszul.level F w n
  rw [mem_level]
  intro s
  rw [coefficient_decompose]
  exact hF (n-faceWeight w s) (γ.1-(s.card:ℤ),γ.2)
    ((mem_level F w n z).mp hz s)

/-- Auxiliary-degree-one chains are the literal coordinatewise restriction
to A_(*,1), without a cycle or quotient condition. -/
def auxiliaryPiece (m : ℕ) : Submodule K (Total (K:=K) (A:=A) (V:=V)) :=
  coordinatePiece (fun _ => BigradedPolynomialAlgebra.auxiliaryCoefficientPiece P m)

theorem piece_le_auxiliaryPiece (γ : ℤ × ℕ) :
    piece (V:=V) P γ≤auxiliaryPiece P γ.2 := by
  intro z hz
  rw [auxiliaryPiece,mem_coordinatePiece]
  intro s
  exact Submodule.subset_span ⟨γ.1-(s.card:ℤ),(mem_piece P γ z).mp hz s⟩

theorem coefficient_auxiliary_projection (m : ℕ) (γ : ℤ × ℕ) {a : A}
    (ha : a∈BigradedPolynomialAlgebra.auxiliaryCoefficientPiece P m) :
    (DirectSum.decompose P a γ).val∈BigradedPolynomialAlgebra.auxiliaryCoefficientPiece P m := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨q,hq⟩ := ha
      by_cases he : (q,m)=γ
      · rw [DirectSum.decompose_of_mem_same P (he ▸ hq)]
        exact Submodule.subset_span ⟨q,hq⟩
      · rw [DirectSum.decompose_of_mem_ne P hq he]
        exact Submodule.zero_mem _
  | zero =>
      simp only [DirectSum.decompose_zero,DirectSum.zero_apply,Submodule.coe_zero]
      exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
      simpa only [DirectSum.decompose_add,DirectSum.add_apply,Submodule.coe_add]
        using Submodule.add_mem _ iha ihb
  | smul c a ha ih =>
      simpa only [DirectSum.decompose_smul,DirectSum.smul_apply,Submodule.coe_smul]
        using Submodule.smul_mem _ c ih

theorem coefficient_auxiliary_projection_ne (m : ℕ) (γ : ℤ × ℕ) (hm : γ.2≠m) {a : A}
    (ha : a∈BigradedPolynomialAlgebra.auxiliaryCoefficientPiece P m) :
    (DirectSum.decompose P a γ).val=0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨q,hq⟩ := ha
      exact DirectSum.decompose_of_mem_ne P hq
        (fun he => hm (congrArg Prod.snd he).symm)
  | zero => simp only [DirectSum.decompose_zero,DirectSum.zero_apply,Submodule.coe_zero]
  | add a b ha hb iha ihb =>
      simp only [DirectSum.decompose_add,DirectSum.add_apply,Submodule.coe_add,iha,ihb,add_zero]
  | smul c a ha ih =>
      simp only [DirectSum.decompose_smul,DirectSum.smul_apply,Submodule.coe_smul,ih,smul_zero]

theorem piece_inf_auxiliaryPiece (γ : ℤ × ℕ) (m : ℕ) :
    piece (V:=V) P γ⊓auxiliaryPiece P m=if γ.2=m then piece P γ else ⊥ := by
  by_cases hm : γ.2=m
  · rw [if_pos hm]
    apply inf_eq_left.mpr
    simpa only [hm] using piece_le_auxiliaryPiece (V:=V) P γ
  · rw [if_neg hm]
    apply bot_unique
    intro z hz
    rw [Submodule.mem_bot]
    apply TensorExteriorKoszul.coordinates.injective
    ext s
    change coefficient s z=0
    have hp := (mem_piece P γ z).mp hz.1 s
    have ha := (mem_coordinatePiece _ z).mp hz.2 s
    have he := coefficient_auxiliary_projection_ne P m
      (γ.1-(s.card:ℤ),γ.2) hm ha
    rw [DirectSum.decompose_of_mem_same P hp] at he
    exact he

theorem auxiliaryPiece_homogeneous (m : ℕ) :
    SetLike.IsHomogeneous (piece (V:=V) P) (auxiliaryPiece P m) := by
  intro γ z hz
  rw [auxiliaryPiece,mem_coordinatePiece]
  intro s
  rw [coefficient_decompose]
  exact coefficient_auxiliary_projection P m (γ.1-(s.card:ℤ),γ.2)
    ((mem_coordinatePiece _ z).mp hz s)

variable (hX : ∀ v,algebraMap (MvPolynomial V K) A (MvPolynomial.X v)∈P (1,0))

include hX in
theorem differential_auxiliaryPiece (m : ℕ) (z : Total (K:=K) (A:=A) (V:=V))
    (hz : z∈auxiliaryPiece P m) : (D (K:=K) (A:=A) (V:=V)).d z∈auxiliaryPiece P m := by
  rw [← sum_coefficients z,map_sum]
  apply Submodule.sum_mem
  intro s _
  dsimp only [D,TensorExteriorKoszul.parityDifferential]
  rw [differential_tmul_exterior]
  apply Submodule.sum_mem
  intro v _
  apply (auxiliaryPiece P m).toAddSubgroup.zsmul_mem
  apply tmul_basis_mem_coordinatePiece
  simpa only [baseVariable,Algebra.smul_def] using
    BigradedPolynomialAlgebra.auxiliaryCoefficientPiece_X P hX m v.val _
      ((mem_coordinatePiece _ z).mp hz s)

/-- The literal projection to one full (q,m,p) strand. -/
def strandProjection (γ : ℤ × ℕ) (p : ℤ) :
    Total (K:=K) (A:=A) (V:=V) →ₗ[K] strand (V:=V) P γ p :=
  (Grading.projection (basis (V:=V) P) (fullDegree (V:=V) P) (γ,p)).codRestrict
    (strand (V:=V) P γ p) (Grading.projection_mem (basis (V:=V) P) (fullDegree (V:=V) P) (γ,p))

theorem strandProjection_self (γ : ℤ × ℕ) (p : ℤ) (z : strand (V:=V) P γ p) :
    strandProjection P γ p z.val=z :=
  Subtype.ext (Grading.projection_eq_self z.property)

theorem coefficient_strandProjection (γ : ℤ × ℕ) (p : ℤ) (s : Finset V)
    (z : Total (K:=K) (A:=A) (V:=V)) :
    coefficient s (strandProjection P γ p z).val=
      if (s.card:ℤ)=p then
        Grading.projection (BigradedPolynomialAlgebra.fullBasis P) (fun a => a.1)
          (γ.1-(s.card:ℤ),γ.2) (coefficient s z) else 0 := by
  apply (BigradedPolynomialAlgebra.fullBasis P).repr.injective
  ext a
  change (BigradedPolynomialAlgebra.fullBasis P).repr
    (coefficient s (Grading.projection (basis (V:=V) P) (fullDegree (V:=V) P) (γ,p) z)) a=_
  rw [← basis_repr_coefficient]
  have he : fullDegree (V:=V) P (a,s)=(γ,p) ↔
      a.1=(γ.1-(s.card:ℤ),γ.2) ∧ (s.card:ℤ)=p := by
    constructor
    · intro h
      refine ⟨?_,congrArg Prod.snd h⟩
      have hh := congrArg Prod.fst h
      apply Prod.ext
      · have hq := congrArg Prod.fst hh
        change a.1.1+(s.card:ℤ)=γ.1 at hq
        omega
      · have h := congrArg (fun t : ℤ × ℕ => t.2) hh
        exact h
    · rintro ⟨ha,hp⟩
      unfold fullDegree degree
      rw [ha,hp]
      simp only [sub_add_cancel]
  simp only [Grading.projection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,Grading.filterMap_apply,Finsupp.filter_apply,he]
  by_cases hs : (s.card:ℤ)=p
  · simp only [hs,↓reduceIte,and_true]
    rw [basis_repr_coefficient]
    simp only [LinearEquiv.apply_symm_apply,Finsupp.filter_apply]
  · simp only [hs,↓reduceIte,and_false,map_zero,Finsupp.zero_apply]

include hF in
theorem strandProjection_preserves_filtration (γ : ℤ × ℕ) (p n : ℤ)
    (z : Total (K:=K) (A:=A) (V:=V)) (hz : z∈(filtration F w).level n) :
    (strandProjection P γ p z).val∈(filtration F w).level n := by
  change (strandProjection P γ p z).val ∈ FilteredTensorKoszul.level F w n
  rw [mem_level]
  intro s
  rw [coefficient_strandProjection]
  by_cases hs : (s.card:ℤ)=p
  · rw [if_pos hs,BigradedPolynomialAlgebra.fullBasis_projection]
    exact hF (n-faceWeight w s) (γ.1-(s.card:ℤ),γ.2)
      ((mem_level F w n z).mp hz s)
  · rw [if_neg hs]
    exact Submodule.zero_mem _

include hX in
theorem strandProjection_differential (γ : ℤ × ℕ) (p : ℤ)
    (z : Total (K:=K) (A:=A) (V:=V)) :
    (D (K:=K) (A:=A) (V:=V)).d (strandProjection P γ p z).val=
      (strandProjection P γ (p-1) ((D (K:=K) (A:=A) (V:=V)).d z)).val := by
  let shift : (ℤ × ℕ) × ℤ → (ℤ × ℕ) × ℤ := fun g => (g.1,g.2-1)
  have hinj : Function.Injective shift := by
    intro a b h
    apply Prod.ext
    · have he := congrArg (fun g : (ℤ × ℕ) × ℤ => g.1) h
      exact he
    · have he := congrArg (fun g : (ℤ × ℕ) × ℤ => g.2) h
      dsimp only [shift] at he
      omega
  have hd : ∀ a,(D (K:=K) (A:=A) (V:=V)).d (basis (V:=V) P a)∈
      Grading.Piece (basis (V:=V) P) (fullDegree (V:=V) P) (shift (fullDegree (V:=V) P a)) := by
    intro a
    exact differential_strand (V:=V) P hX (degree P a) (a.2.card:ℤ) (basis (V:=V) P a)
      (Grading.basis_mem_piece (basis (V:=V) P) (fullDegree (V:=V) P) a)
  exact LinearMap.congr_fun (shiftedProjection_commutes (basis (V:=V) P) (basis (V:=V) P)
    (fullDegree (V:=V) P) (fullDegree (V:=V) P) shift hinj
    (D (K:=K) (A:=A) (V:=V)).d hd (γ,p)) z

end FourPapers.BigradedTensorKoszul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.AssociatedComponentHomologyCarrier -/
section

/-! # A canonical presentation of actual associated-component homology

The carrier retains the filtration and the three component submodules in its
head. Its group and scalar structures are exactly those of the literal cycle
quotient. The identity linear equivalence below records this explicitly.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)
  (W U Z : Submodule K A)
  (hWU : ∀ x ∈ W, D.d x ∈ U) (hUZ : ∀ x ∈ U, D.d x ∈ Z)

/-- The literal associated cycle quotient, with a stable type head. -/
def AssociatedComponentHomologyCarrier : Type _ :=
  F.associatedComponentHomology D hd hp W U Z hWU hUZ

instance associatedComponentHomologyCarrierAddCommGroup :
    AddCommGroup (F.AssociatedComponentHomologyCarrier D hd hp W U Z hWU hUZ) :=
  inferInstanceAs (AddCommGroup (F.associatedComponentHomology D hd hp W U Z hWU hUZ))

instance associatedComponentHomologyCarrierModule :
    Module K (F.AssociatedComponentHomologyCarrier D hd hp W U Z hWU hUZ) :=
  inferInstanceAs (Module K (F.associatedComponentHomology D hd hp W U Z hWU hUZ))

/-- This presentation is the identity on the actual homology quotient. -/
def associatedComponentHomologyCarrierEquiv :
    F.AssociatedComponentHomologyCarrier D hd hp W U Z hWU hUZ ≃ₗ[K]
      F.associatedComponentHomology D hd hp W U Z hWU hUZ :=
  LinearEquiv.refl K _

/-- The canonical presentation has exactly the literal homology dimension. -/
theorem associatedComponentHomologyCarrier_finrank :
    Module.finrank K (F.AssociatedComponentHomologyCarrier D hd hp W U Z hWU hUZ) =
      Module.finrank K (F.associatedComponentHomology D hd hp W U Z hWU hUZ) :=
  (F.associatedComponentHomologyCarrierEquiv D hd hp W U Z hWU hUZ).finrank_eq

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BigradedCycleLifting -/
section

/-!
# Global multiplicative cycle lifts preserve each genuine graded Betti number

The projection onto the actual (q,m,p) tensor strand preserves the weight
filtration and commutes with the differential. Applying it to a global
lift proves individual three-term homology equality. The outgoing space
in homological degree zero is the actual zero exterior-degree-minus-one
space; comparison with the ordinary Tor convention is proved explicitly.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.BigradedCycleLifting

open Classical BigradedTensorKoszul FilteredTensorKoszul FilteredHomology IntegerFiltered
open MultiplicativeFiltration

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  (hX : ∀ v,algebraMap (MvPolynomial V K) A (MvPolynomial.X v)∈P (1,0))

def outgoing (γ : ℤ × ℕ) (p : ℕ) :
    strand (V:=V) P γ (p:ℤ) →ₗ[K] strand (V:=V) P γ ((p:ℤ)-1) :=
  componentDifferentialBetween (D (K:=K) (A:=A) (V:=V))
    (strand (V:=V) P γ (p:ℤ)) (strand (V:=V) P γ ((p:ℤ)-1))
    (differential_strand (V:=V) P hX γ (p:ℤ))

include hX in
theorem incoming_mem (γ : ℤ × ℕ) (p : ℕ)
    (z : BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (hz : z∈strand (V:=V) P γ ((p+1:ℕ):ℤ)) :
    (D (K:=K) (A:=A) (V:=V)).d z∈strand (V:=V) P γ (p:ℤ) := by
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    using differential_strand (V:=V) P hX γ ((p+1:ℕ):ℤ) z hz

def incoming (γ : ℤ × ℕ) (p : ℕ) :
    strand (V:=V) P γ ((p+1:ℕ):ℤ) →ₗ[K] strand (V:=V) P γ (p:ℤ) :=
  componentDifferentialBetween (D (K:=K) (A:=A) (V:=V))
    (strand (V:=V) P γ ((p+1:ℕ):ℤ)) (strand (V:=V) P γ (p:ℤ)) (incoming_mem P hX γ p)

theorem incoming_outgoing (γ : ℤ × ℕ) (p : ℕ) :
    (outgoing P hX γ p).comp (incoming P hX γ p)=0 :=
  componentDifferentialBetween_comp (D (K:=K) (A:=A) (V:=V))
    (strand (V:=V) P γ ((p+1:ℕ):ℤ)) (strand (V:=V) P γ (p:ℤ)) (strand (V:=V) P γ ((p:ℤ)-1))
    (incoming_mem P hX γ p) (differential_strand (V:=V) P hX γ (p:ℤ))

abbrev Homology (γ : ℤ × ℕ) (p : ℕ) := FilteredHomology.Homology
  (incoming (V:=V) P hX γ p) (outgoing P hX γ p) (incoming_outgoing P hX γ p)

def tensorHomologyEquiv (m : ℕ) (q : ℤ) (p : ℕ) :
    BigradedTensorTor.Homology (V:=V) P hX m q p ≃ₗ[K] Homology P hX (q,m) p := by
  let f : strand (V:=V) P (q,m) ((p+1:ℕ):ℤ) →ₗ[K] strand (V:=V) P (q,m) (p:ℤ) :=
    BigradedTensorTor.differential P hX m q p
  let g : strand (V:=V) P (q,m) (p:ℤ) →ₗ[K] strand (V:=V) P (q,m) (p.pred:ℤ) :=
    BigradedTensorTor.previous P hX m q p
  let hfg := BigradedTensorTor.previous_comp P hX m q p
  let j := (strand (V:=V) P (q,m) (p.pred:ℤ)).subtype
  let j' := (strand (V:=V) P (q,m) ((p:ℤ)-1)).subtype
  let H := homologyEquiv_postcompose (R:=K)
    (X:=strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)) (Y:=strand (V:=V) P (q,m) (p:ℤ))
    (Z:=strand (V:=V) P (q,m) (p.pred:ℤ)) (W:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V))
    f g hfg j Subtype.val_injective
  let H' := homologyEquiv_postcompose (R:=K)
    (X:=strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)) (Y:=strand (V:=V) P (q,m) (p:ℤ))
    (Z:=strand (V:=V) P (q,m) ((p:ℤ)-1)) (W:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V))
    (incoming P hX (q,m) p) (outgoing P hX (q,m) p)
    (incoming_outgoing P hX (q,m) p) j' Subtype.val_injective
  refine H.trans ((threeTermHomologyEquiv (R:=K)
    (X:=strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)) (Y:=strand (V:=V) P (q,m) (p:ℤ))
    (Z:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V))
    (X':=strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)) (Y':=strand (V:=V) P (q,m) (p:ℤ))
    (Z':=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) f (j.comp g) (postcompose_comp_zero f g hfg j)
    (incoming P hX (q,m) p) (j'.comp (outgoing P hX (q,m) p))
    (postcompose_comp_zero (incoming P hX (q,m) p) (outgoing P hX (q,m) p)
      (incoming_outgoing P hX (q,m) p) j')
    (LinearEquiv.refl K _) (LinearEquiv.refl K _) (LinearEquiv.refl K _)
    (fun x => rfl) ?_).trans H'.symm)
  intro z
  exact BigradedTensorTor.previous_val P hX m q p z

theorem bettiNumber_eq_finrank (m p : ℕ) (q : ℤ) :
    BigradedPolynomialAlgebra.bettiNumber P hX m p q=
      Module.finrank K (Homology P hX (q,m) p) := by
  rw [BigradedTensorTor.bettiNumber_eq_finrank]
  exact (tensorHomologyEquiv P hX m q p).finrank_eq

/-- Keep the canonical tensor module structures fixed before supplying
the concrete graded subspaces and coefficient filtration. -/
theorem tensor_three_component_bounds
    (T' : MultiplicativeFiltration K (BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)))
    (W U Z : Submodule K (BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)))
    [Module.Finite K W] [Module.Finite K U] [Module.Finite K Z] :
    ∃ (L : ℤ)
      (hLW : (T'.level (L-1)).comap W.subtype=⊥)
      (hLU : (T'.level (L-1)).comap U.subtype=⊥)
      (hLZ : (T'.level (L-1)).comap Z.subtype=⊥) (N : ℕ),
      (T'.componentFiltration W L hLW).level N=⊤ ∧
      (T'.componentFiltration U L hLU).level N=⊤ ∧
      (T'.componentFiltration Z L hLZ).level N=⊤ := by
  exact exists_three_component_bounds (K:=K)
    (A:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) T' W U Z

variable [∀ γ,Module.Finite K (P γ)]
  (F : MultiplicativeFiltration K A) (w : V → ℤ)
  (hF : ∀ n,DirectSum.SetLike.IsHomogeneous P (F.level n))
  (hw : ∀ v,baseVariable (K:=K) (A:=A) (V:=V) v∈F.level (w v))

local instance (priority := 1200) strandAddCommGroup (γ : ℤ × ℕ) (p : ℤ) :
    AddCommGroup (strand (V:=V) P γ p) :=
  Submodule.addCommGroup (R:=K)
    (M:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (strand (V:=V) P γ p)

local instance (priority := 1200) strandModule (γ : ℤ × ℕ) (p : ℤ) :
    Module K (strand (V:=V) P γ p) :=
  Submodule.module (R:=K)
    (M:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (strand (V:=V) P γ p)

local notation "T" => filtration F w
local notation "DA" => D (K:=K) (A:=A) (V:=V)

include hw in
/-- Differential preservation with the actual filtration as its head. -/
theorem tensor_filtration_differential_preserves :
    ∀ (n : ℤ) (z : BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)),
      z ∈ (T).level n → (DA).d z ∈ (T).level n :=
  differential_preserves F w (baseVariable (K:=K) (A:=A) (V:=V)) hw

/-- Parity preservation with the same actual filtration head. -/
theorem tensor_filtration_parity_preserves :
    ∀ (n : ℤ) (z : BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)),
      z ∈ (T).level n → (DA).parity z ∈ (T).level n :=
  parity_preserves F w

include hF in
theorem tensor_strandProjection_preserves (γ : ℤ × ℕ) (p : ℤ) :
    ∀ (n : ℤ) (z : BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)),
      z ∈ (T).level n → (strandProjection (V:=V) P γ p z).val ∈ (T).level n :=
  strandProjection_preserves_filtration P F w hF γ p

include hX in
theorem tensor_strandProjection_incoming (γ : ℤ × ℕ) (p : ℕ)
    (z : BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) :
    (DA).d (strandProjection (V:=V) P γ ((p+1:ℕ):ℤ) z).val =
      (strandProjection (V:=V) P γ (p:ℤ) ((DA).d z)).val := by
  have hp' : ((p+1:ℕ):ℤ)-1=(p:ℤ) := by omega
  exact (strandProjection_differential P hX γ ((p+1:ℕ):ℤ) z).trans
    (congrArg (fun r : ℤ => (strandProjection (V:=V) P γ r ((DA).d z)).val) hp')

local notation "hd" => tensor_filtration_differential_preserves (V:=V) F w hw
local notation "hp" => tensor_filtration_parity_preserves (V:=V) F w

/-- The tensor Koszul ring need not be commutative. Keep its canonical
Rees quotient structures explicit, avoiding a search through the optional
commutative-ring instances for coefficient associated algebras. -/
local instance (priority := 1400) tensorReesRing : Ring (T).rees := reesRing (T)

local instance (priority := 1400) tensorReesAddCommGroup : AddCommGroup (T).rees :=
  (reesRing (T)).toAddCommGroup

local instance (priority := 1400) tensorReesAlgebra : Algebra K (T).rees := reesAlgebra (T)

local instance (priority := 1400) tensorReesModule : Module K (T).rees := reesModule (T)

local instance (priority := 1400) tensorAssociatedRing : Ring (T).AssociatedGraded :=
  associatedGradedRing (T)

local instance (priority := 1400) tensorAssociatedAddCommGroup :
    AddCommGroup (T).AssociatedGraded :=
  (associatedGradedRing (T)).toAddCommGroup

local instance (priority := 1400) tensorAssociatedAlgebra :
    Algebra K (T).AssociatedGraded := associatedGradedAlgebra (T)

local instance (priority := 1400) tensorAssociatedModule :
    Module K (T).AssociatedGraded := associatedGradedModule (T)

local instance (priority := 1500) tensorAssociatedPieceAddCommGroup
    (W : Submodule K (BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V))) :
    AddCommGroup ((T).associatedPiece W) :=
  Submodule.addCommGroup (R:=K) (M:=(T).AssociatedGraded) ((T).associatedPiece W)

local instance (priority := 1500) tensorAssociatedPieceModule
    (W : Submodule K (BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V))) :
    Module K ((T).associatedPiece W) :=
  Submodule.module (R:=K) (M:=(T).AssociatedGraded) ((T).associatedPiece W)

attribute [local irreducible] BigradedTensorKoszul.strand
  BigradedTensorKoszul.strandProjection FilteredTensorKoszul.filtration
  TensorExteriorKoszul.parityDifferential

include hF in
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
/-- Every p,q,m is retained. Finite lower and upper filtration bounds are
derived internally from the original finite-dimensional coefficient pieces. -/
theorem bettiNumber_eq_associatedHomology_of_lifts
    (hlift : (T).LiftsCycles DA) (m p : ℕ) (q : ℤ) :
    BigradedPolynomialAlgebra.bettiNumber P hX m p q=
      Module.finrank K (AssociatedComponentHomologyCarrier (K:=K)
        (A:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (T) DA hd hp
        (strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)) (strand (V:=V) P (q,m) (p:ℤ))
        (strand (V:=V) P (q,m) ((p:ℤ)-1)) (incoming_mem P hX (q,m) p)
        (differential_strand (V:=V) P hX (q,m) (p:ℤ))) := by
  let W := strand (V:=V) P (q,m) ((p+1:ℕ):ℤ)
  let U := strand (V:=V) P (q,m) (p:ℤ)
  let Z := strand (V:=V) P (q,m) ((p:ℤ)-1)
  letI : Module.Finite K W := strand_finite P (q,m) ((p+1:ℕ):ℤ)
  letI : Module.Finite K U := strand_finite P (q,m) (p:ℤ)
  letI : Module.Finite K Z := strand_finite P (q,m) ((p:ℤ)-1)
  have hbounds := tensor_three_component_bounds (K:=K) (A:=A) (V:=V) (T) W U Z
  obtain ⟨L,hLW,hLU,hLZ,N,hNW,hNU,hNZ⟩ := hbounds
  have lf := componentDifferentialBetween_lifts_of_projection (K:=K)
    (A:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (T) W U DA
    (incoming_mem P hX (q,m) p) hlift
    (strandProjection P (q,m) ((p+1:ℕ):ℤ)) (strandProjection P (q,m) (p:ℤ))
    (strandProjection_self P (q,m) ((p+1:ℕ):ℤ))
    (tensor_strandProjection_preserves P F w hF (q,m) ((p+1:ℕ):ℤ))
    (tensor_strandProjection_incoming P hX (q,m) p)
    L hLW hLU
  have lg := componentDifferentialBetween_lifts_of_projection (K:=K)
    (A:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (T) U Z DA
    (differential_strand (V:=V) P hX (q,m) (p:ℤ)) hlift
    (strandProjection P (q,m) (p:ℤ)) (strandProjection P (q,m) ((p:ℤ)-1))
    (strandProjection_self P (q,m) (p:ℤ))
    (tensor_strandProjection_preserves P F w hF (q,m) (p:ℤ))
    (strandProjection_differential P hX (q,m) (p:ℤ)) L hLU hLZ
  rw [bettiNumber_eq_finrank]
  refine (componentHomology_dimension_eq_actualAssociated (K:=K)
    (A:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (T) DA hd hp W U Z
    (incoming_mem P hX (q,m) p) (differential_strand (V:=V) P hX (q,m) (p:ℤ))
    L hLW hLU hLZ N hNW hNU hNZ lf lg).trans ?_
  exact (associatedComponentHomologyCarrier_finrank (K:=K)
    (A:=BigradedTensorKoszul.Total (K:=K) (A:=A) (V:=V)) (T) DA hd hp W U Z
    (incoming_mem P hX (q,m) p) (differential_strand (V:=V) P hX (q,m) (p:ℤ))).symm

end FourPapers.BigradedCycleLifting

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredBigradedComparison -/
section

/-! # The actual associated tensor components are the Koszul components of gr(A)

These equivalences retain the original internal, auxiliary and exterior
degrees. The polynomial action on gr(A) is the action of the literal
leading variable symbols. In particular the comparison is with its actual
derived Tor, not a renamed associated complex supplied as a hypothesis.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredBigradedComparison

open Classical CommAlg FilteredTensorKoszul BigradedTensorKoszul
open FilteredHomology IntegerFiltered IntegerFiltered.MultiplicativeFiltration
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  (hX : ∀ v,baseVariable (K:=K) (A:=A) (V:=V) v∈P (1,0))
  (F : MultiplicativeFiltration K A) (w : V → ℤ)
  (hF : ∀ n,DirectSum.SetLike.IsHomogeneous P (F.level n))
  (hw : ∀ v,baseVariable (K:=K) (A:=A) (V:=V) v∈F.level (w v))

local notation "B" => AssociatedPolynomialCarrier F w
  (baseVariable (K:=K) (A:=A) (V:=V)) hw

/-- The actual induced coefficient pieces; the filtration compatibility
proof is an explicit argument so its grading instance has an inferable head. -/
def associatedGrading (_hF : ∀ n,DirectSum.SetLike.IsHomogeneous P (F.level n))
    (γ : ℤ × ℕ) : Submodule K B := F.associatedPiece (P γ)

local instance associatedGradingInstance :
    GradedAlgebra (associatedGrading P F w hw hF) :=
  F.associatedGradingAlgebra P hF

local notation "Q" => associatedGrading P F w hw hF
local notation "T" => filtration F w
local notation "DA" => D (K:=K) (A:=A) (V:=V)
local notation "DB" => D (K:=K) (A:=B) (V:=V)
local notation "hd" => differential_preserves F w (baseVariable (K:=K) (A:=A) (V:=V)) hw
local notation "hp" => parity_preserves F w

theorem associated_baseVariable (v : V) :
    baseVariable (K:=K) (A:=B) (V:=V) v=
      leadingVariable F w (baseVariable (K:=K) (A:=A) (V:=V)) hw v :=
  associatedPolynomialMap_X F w (baseVariable (K:=K) (A:=A) (V:=V)) hw v

include hX in
theorem associatedVariableHomogeneous (v : V) :
    baseVariable (K:=K) (A:=B) (V:=V) v∈Q (1,0) := by
  rw [associated_baseVariable]
  exact F.symbol_mem_associatedPiece (P (1,0)) (w v) ⟨baseVariable (K:=K) (A:=A) v,hw v⟩ (hX v)

theorem associated_differential (z : (T).AssociatedGraded) :
    associatedAlgebraEquiv F w (((T).associatedDGA DA hd hp).d z)=
      (DB).d (associatedAlgebraEquiv F w z) := by
  have he : baseVariable (K:=K) (A:=B) (V:=V)=
      leadingVariable F w (baseVariable (K:=K) (A:=A) (V:=V)) hw :=
    funext (associated_baseVariable F w hw)
  change associatedAlgebraEquiv F w ((associatedKoszulDGA F w (baseVariable (K:=K) (A:=A)) hw).d z)=
    (TensorExteriorKoszul.parityDifferential (baseVariable (K:=K) (A:=B))).d
      (associatedAlgebraEquiv F w z)
  rw [he]
  exact associatedAlgebraEquiv_differential F w (baseVariable (K:=K) (A:=A)) hw z

theorem associated_piece (γ : ℤ × ℕ) :
    ((T).associatedPiece (piece (V:=V) P γ)).map (associatedAlgebraEquiv F w).toLinearMap=
      piece (V:=V) Q γ := by
  simpa only [piece_eq_coordinatePiece,associatedGrading] using
    associated_coordinatePiece F w (fun s : Finset V => P (γ.1-(s.card:ℤ),γ.2))

def associatedPieceEquiv (γ : ℤ × ℕ) :
    (T).associatedPiece (piece (V:=V) P γ) ≃ₗ[K] piece (V:=V) Q γ :=
  (associatedAlgebraEquiv F w).toLinearEquiv.ofSubmodules _ _
    (associated_piece P F w hF hw γ)

@[simp] theorem associatedPieceEquiv_val (γ : ℤ × ℕ)
    (z : (T).associatedPiece (piece (V:=V) P γ)) :
    (associatedPieceEquiv P F w hF hw γ z).val=associatedAlgebraEquiv F w z.val := rfl

def associatedTotalHomologyEquiv (γ : ℤ × ℕ) :
    (T).associatedComponentHomology DA hd hp (piece P γ) (piece P γ) (piece P γ)
      (differential_piece P hX γ) (differential_piece P hX γ) ≃ₗ[K]
        BigradedTotalHomology.TotalHomology Q (associatedVariableHomogeneous P hX F w hF hw) γ :=
  threeTermHomologyEquiv (R:=K)
    (X:=(T).associatedPiece (piece (V:=V) P γ))
    (Y:=(T).associatedPiece (piece (V:=V) P γ))
    (Z:=(T).associatedPiece (piece (V:=V) P γ))
    (X':=BigradedTotalHomology.Component (V:=V) Q γ)
    (Y':=BigradedTotalHomology.Component (V:=V) Q γ)
    (Z':=BigradedTotalHomology.Component (V:=V) Q γ)
    ((T).associatedPieceDifferential DA hd hp (piece (V:=V) P γ) (piece (V:=V) P γ)
      (differential_piece P hX γ))
    ((T).associatedPieceDifferential DA hd hp (piece (V:=V) P γ) (piece (V:=V) P γ)
      (differential_piece P hX γ))
    ((T).associatedPieceDifferential_comp DA hd hp
      (piece (V:=V) P γ) (piece (V:=V) P γ) (piece (V:=V) P γ)
      (differential_piece P hX γ) (differential_piece P hX γ))
    (BigradedTotalHomology.d Q (associatedVariableHomogeneous P hX F w hF hw) γ)
    (BigradedTotalHomology.d Q (associatedVariableHomogeneous P hX F w hF hw) γ)
    (BigradedTotalHomology.d_comp Q (associatedVariableHomogeneous P hX F w hF hw) γ)
    (associatedPieceEquiv P F w hF hw γ) (associatedPieceEquiv P F w hF hw γ)
    (associatedPieceEquiv P F w hF hw γ)
    (fun z => Subtype.ext (associated_differential F w hw z.val))
    (fun z => Subtype.ext (associated_differential F w hw z.val))

theorem associated_strand (γ : ℤ × ℕ) (p : ℤ) :
    ((T).associatedPiece (strand (V:=V) P γ p)).map (associatedAlgebraEquiv F w).toLinearMap=
      strand (V:=V) Q γ p := by
  rw [strand_eq_coordinatePiece,associated_coordinatePiece,strand_eq_coordinatePiece]
  congr 1
  funext s
  split_ifs <;> simp only [associatedGrading,F.associatedPiece_bot]

def associatedStrandEquiv (γ : ℤ × ℕ) (p : ℤ) :
    (T).associatedPiece (strand (V:=V) P γ p) ≃ₗ[K] strand (V:=V) Q γ p :=
  (associatedAlgebraEquiv F w).toLinearEquiv.ofSubmodules _ _
    (associated_strand P F w hF hw γ p)

@[simp] theorem associatedStrandEquiv_val (γ : ℤ × ℕ) (p : ℤ)
    (z : (T).associatedPiece (strand (V:=V) P γ p)) :
    (associatedStrandEquiv P F w hF hw γ p z).val=associatedAlgebraEquiv F w z.val := rfl

/-- This keeps the signed outgoing degree p−1, including the actual zero
space at p=0. Its target is the homology already identified with derived Tor. -/
def associatedStrandHomologyEquiv (γ : ℤ × ℕ) (p : ℕ) :
    (T).associatedComponentHomology DA hd hp
      (strand P γ ((p+1:ℕ):ℤ)) (strand P γ (p:ℤ)) (strand P γ ((p:ℤ)-1))
      (BigradedCycleLifting.incoming_mem P hX γ p) (differential_strand P hX γ (p:ℤ)) ≃ₗ[K]
        BigradedCycleLifting.Homology Q (associatedVariableHomogeneous P hX F w hF hw) γ p :=
  threeTermHomologyEquiv (R:=K)
    (X:=(T).associatedPiece (strand (V:=V) P γ ((p+1:ℕ):ℤ)))
    (Y:=(T).associatedPiece (strand (V:=V) P γ (p:ℤ)))
    (Z:=(T).associatedPiece (strand (V:=V) P γ ((p:ℤ)-1)))
    (X':=strand (V:=V) Q γ ((p+1:ℕ):ℤ))
    (Y':=strand (V:=V) Q γ (p:ℤ)) (Z':=strand (V:=V) Q γ ((p:ℤ)-1))
    ((T).associatedPieceDifferential DA hd hp
      (strand (V:=V) P γ ((p+1:ℕ):ℤ)) (strand (V:=V) P γ (p:ℤ))
      (BigradedCycleLifting.incoming_mem P hX γ p))
    ((T).associatedPieceDifferential DA hd hp
      (strand (V:=V) P γ (p:ℤ)) (strand (V:=V) P γ ((p:ℤ)-1))
      (differential_strand P hX γ (p:ℤ)))
    ((T).associatedPieceDifferential_comp DA hd hp
      (strand (V:=V) P γ ((p+1:ℕ):ℤ)) (strand (V:=V) P γ (p:ℤ))
      (strand (V:=V) P γ ((p:ℤ)-1))
      (BigradedCycleLifting.incoming_mem P hX γ p) (differential_strand P hX γ (p:ℤ)))
    (BigradedCycleLifting.incoming Q (associatedVariableHomogeneous P hX F w hF hw) γ p)
    (BigradedCycleLifting.outgoing Q (associatedVariableHomogeneous P hX F w hF hw) γ p)
    (BigradedCycleLifting.incoming_outgoing Q (associatedVariableHomogeneous P hX F w hF hw) γ p)
    (associatedStrandEquiv P F w hF hw γ ((p+1:ℕ):ℤ))
    (associatedStrandEquiv P F w hF hw γ (p:ℤ))
    (associatedStrandEquiv P F w hF hw γ ((p:ℤ)-1))
    (fun z => Subtype.ext (associated_differential F w hw z.val))
    (fun z => Subtype.ext (associated_differential F w hw z.val))

theorem auxiliaryCoefficient_projection_zero (m : ℕ) (γ : ℤ × ℕ) (hγ : γ.2≠m)
    {a : A} (ha : a∈BigradedPolynomialAlgebra.auxiliaryCoefficientPiece P m) :
    GradedAlgebra.proj P γ a=0 :=
  BigradedTensorKoszul.coefficient_auxiliary_projection_ne P m γ hγ ha

include hF in
theorem associated_auxiliaryCoefficientPiece (m : ℕ) :
    F.associatedPiece (BigradedPolynomialAlgebra.auxiliaryCoefficientPiece P m)=
      BigradedPolynomialAlgebra.auxiliaryCoefficientPiece Q m := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨n,a,ha,rfl⟩
    let s := (DirectSum.decompose P a.val).support
    let b : (ℤ × ℕ) → F.level n := fun γ =>
      ⟨(DirectSum.decompose P a.val γ).val,hF n γ a.property⟩
    have hb : (∑ γ∈s,b γ)=a := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum,b,s] using DirectSum.sum_support_decompose P a.val
    rw [← hb,map_sum]
    apply Submodule.sum_mem
    intro γ _
    by_cases hγ : γ.2=m
    · apply Submodule.subset_span
      refine ⟨γ.1,?_⟩
      have he : γ=(γ.1,m) := Prod.ext rfl hγ
      have hmem := F.symbol_mem_associatedPiece (P γ) n (b γ)
        (DirectSum.decompose P a.val γ).property
      change F.symbol n (b γ) ∈ F.associatedPiece (P (γ.1,m))
      rw [← he]
      exact hmem
    · have he : b γ=0 := Subtype.ext (auxiliaryCoefficient_projection_zero P m γ hγ ha)
      rw [he,map_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro z ⟨q,hq⟩
    exact F.associatedPiece_mono
      (show P (q,m)≤BigradedPolynomialAlgebra.auxiliaryCoefficientPiece P m from
        fun a ha => Submodule.subset_span ⟨q,ha⟩) hq

include hF in
theorem associated_auxiliaryPiece (m : ℕ) :
    ((T).associatedPiece (auxiliaryPiece (V:=V) P m)).map
      (associatedAlgebraEquiv F w).toLinearMap=auxiliaryPiece (V:=V) Q m := by
  rw [auxiliaryPiece,associated_coordinatePiece,auxiliaryPiece]
  congr 1
  funext s
  exact associated_auxiliaryCoefficientPiece P F w hF hw m

include hF in
/-- Generation transfers through the actual associated Koszul algebra
equivalence and the proved auxiliary-degree correspondence. -/
theorem associated_generation (m : ℕ)
    (hgen : Algebra.adjoin K (selectedHomologyClasses DB (auxiliaryPiece (V:=V) Q m))=⊤) :
    Algebra.adjoin K (selectedHomologyClasses ((T).associatedDGA DA hd hp)
      ((T).associatedPiece (auxiliaryPiece (V:=V) P m)))=⊤ := by
  apply ParityDifferential.selected_generation_of_equiv
    ((T).associatedDGA DA hd hp) DB (associatedAlgebraEquiv F w)
    (associated_differential F w hw) ((T).associatedPiece (auxiliaryPiece P m))
  rw [associated_auxiliaryPiece P F w hF hw]
  exact hgen

end FourPapers.FilteredBigradedComparison

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ComponentHomologyCongruence -/
section

/-! # Submodule equalities induce actual component-homology equivalences

Keeping these transports explicit avoids rewriting a submodule underneath
a dependent proof that its differential is stable.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open FilteredHomology

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (D : ParityDifferential K A) (W U : Submodule K A)
  (hW : ∀ x∈W,D.d x∈W) (hU : ∀ x∈U,D.d x∈U)

/-- Square zero for a restricted differential needs no finiteness hypothesis. -/
theorem componentDifferential_comp_zero :
    (componentDifferential D W hW).comp (componentDifferential D W hW)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact D.square_zero x.val

def componentHomologyEquivOfEq (h : W=U) :
    Homology (componentDifferential D W hW) (componentDifferential D W hW)
      (componentDifferential_comp_zero D W hW) ≃ₗ[K]
    Homology (componentDifferential D U hU) (componentDifferential D U hU)
      (componentDifferential_comp_zero D U hU) := by
  subst U
  exact LinearEquiv.refl K _

variable (F : MultiplicativeFiltration K A)
  (hd : ∀ n x,x∈F.level n→D.d x∈F.level n)
  (hp : ∀ n x,x∈F.level n→D.parity x∈F.level n)

def associatedComponentHomologyEquivOfEq (h : W=U) :
    F.associatedComponentHomology D hd hp W W W hW hW ≃ₗ[K]
      F.associatedComponentHomology D hd hp U U U hU hU := by
  subst U
  exact LinearEquiv.refl K _

theorem component_homology_dimensions_of_eq_bot (h : W=⊥) :
    Module.finrank K (Homology (componentDifferential D W hW)
      (componentDifferential D W hW) (componentDifferential_comp_zero D W hW))=
      Module.finrank K (F.associatedComponentHomology D hd hp W W W hW hW) := by
  letI : Subsingleton W := (LinearEquiv.ofEq W ⊥ h).injective.subsingleton
  have ha : F.associatedPiece W=⊥ := (congrArg F.associatedPiece h).trans F.associatedPiece_bot
  letI : Subsingleton (F.associatedPiece W) :=
    (LinearEquiv.ofEq (F.associatedPiece W) ⊥ ha).injective.subsingleton
  simp only [Module.finrank_zero_of_subsingleton]

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Proposition31 -/
section

/-!
# Proposition 3.1: all auxiliary degrees for an arbitrary bigraded algebra

The coefficient algebra, its auxiliary modules, the associated algebra,
and both homology algebras are literal constructions. The two mathematical
hypotheses are precisely first-auxiliary-degree Betti equality and generation
of the associated Koszul homology in auxiliary degree one and the unit.

The proof works under slightly fewer structural hypotheses than the paper:
it does not use the additional identification A_(*,0)=R, nor independence
of the leading variable symbols. Hence it applies in particular to the
paper's variable-weight filtration on R. Componentwise exhaustion and
separation construct the global filtration by HomogeneousWeightFiltration.
No cycle lift, homology equivalence, Rees presentation, or first-power
comparison is hidden in an auxiliary structure parameter.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical BigradedPolynomialAlgebra BigradedTensorKoszul FilteredTensorKoszul
open FilteredBigradedComparison FilteredHomology IntegerFiltered
open IntegerFiltered.MultiplicativeFiltration

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  [∀ γ,Module.Finite K (P γ)]
  (hX : ∀ v,baseVariable (K:=K) (A:=A) (V:=V) v∈P (1,0))
  (F : MultiplicativeFiltration K A) (w : V → ℤ)
  (hF : ∀ n,DirectSum.SetLike.IsHomogeneous P (F.level n))
  (hw : ∀ v,baseVariable (K:=K) (A:=A) (V:=V) v∈F.level (w v))

local notation "B" => AssociatedPolynomialCarrier F w
  (baseVariable (K:=K) (A:=A) (V:=V)) hw

local instance proposition31_associatedGrading :
    GradedAlgebra (associatedGrading P F w hw hF) :=
  F.associatedGradingAlgebra P hF

local instance proposition31_associatedFinite (γ : ℤ × ℕ) :
    Module.Finite K (associatedGrading P F w hw hF γ) :=
  F.associatedPiece_finite_of_finite (P γ)

local instance proposition31_tensorFinite (γ : ℤ × ℕ) :
    Module.Finite K (piece (V:=V) P γ) := piece_finite P γ

local notation "Q" => associatedGrading P F w hw hF
local notation "hY" => associatedVariableHomogeneous P hX F w hF hw
local notation "T" => filtration F w
local notation "DA" => D (K:=K) (A:=A) (V:=V)
local notation "DB" => D (K:=K) (A:=B) (V:=V)
local notation "hd" => differential_preserves F w (baseVariable (K:=K) (A:=A) (V:=V)) hw
local notation "hp" => parity_preserves F w

/-- The first-degree numerical hypothesis in Proposition 3.1 forces
actual leading-cycle lifts on the original Koszul algebra. -/
theorem proposition31_cycleLifts
    (hβ : ∀ (p : ℕ) (q : ℤ),
      BigradedPolynomialAlgebra.bettiNumber P hX 1 p q=
        BigradedPolynomialAlgebra.bettiNumber Q hY 1 p q)
    (hgen : Algebra.adjoin K (selectedHomologyClasses DB (auxiliaryPiece (V:=V) Q 1))=⊤) :
    (T).LiftsCycles DA ∧
      Algebra.adjoin K (selectedHomologyClasses DA (auxiliaryPiece (V:=V) P 1))=⊤ := by
  have hfirst : ∀ γ,
      Module.finrank K (Homology
        (componentDifferential DA (piece P γ⊓auxiliaryPiece P 1)
          (fun x hx => ⟨differential_piece P hX γ x hx.1,
            differential_auxiliaryPiece P hX 1 x hx.2⟩))
        (componentDifferential DA (piece P γ⊓auxiliaryPiece P 1)
          (fun x hx => ⟨differential_piece P hX γ x hx.1,
            differential_auxiliaryPiece P hX 1 x hx.2⟩))
        (componentDifferential_square DA (piece P γ⊓auxiliaryPiece P 1)
          (fun x hx => ⟨differential_piece P hX γ x hx.1,
            differential_auxiliaryPiece P hX 1 x hx.2⟩)))=
      Module.finrank K ((T).associatedComponentHomology DA hd hp
        (piece P γ⊓auxiliaryPiece P 1) (piece P γ⊓auxiliaryPiece P 1)
        (piece P γ⊓auxiliaryPiece P 1)
        (fun x hx => ⟨differential_piece P hX γ x hx.1,
          differential_auxiliaryPiece P hX 1 x hx.2⟩)
        (fun x hx => ⟨differential_piece P hX γ x hx.1,
          differential_auxiliaryPiece P hX 1 x hx.2⟩)) := by
    rintro ⟨q,m⟩
    let W := piece (V:=V) P (q,m)⊓auxiliaryPiece P 1
    have hW : ∀ x∈W,(DA).d x∈W := fun x hx =>
      ⟨differential_piece P hX (q,m) x hx.1,differential_auxiliaryPiece P hX 1 x hx.2⟩
    by_cases hm : m=1
    · subst m
      have he : W=piece P (q,1) := by
        dsimp only [W]
        rw [piece_inf_auxiliaryPiece,if_pos rfl]
      let eA := componentHomologyEquivOfEq DA W (piece P (q,1)) hW
        (differential_piece P hX (q,1)) he
      let eB := associatedComponentHomologyEquivOfEq DA W (piece P (q,1)) hW
        (differential_piece P hX (q,1)) T hd hp he
      calc
        _ = Module.finrank K (BigradedTotalHomology.TotalHomology P hX (q,1)) := eA.finrank_eq
        _ =
            Module.finrank K (BigradedTotalHomology.TotalHomology Q hY (q,1)) :=
          BigradedTotalHomology.total_finrank_eq_of_betti_eq P hX Q hY 1 q (fun p => hβ p q)
        _ = _ := (eB.trans (associatedTotalHomologyEquiv P hX F w hF hw (q,1))).finrank_eq.symm
    · have he : W=⊥ := by
        dsimp only [W]
        rw [piece_inf_auxiliaryPiece,if_neg hm]
      exact component_homology_dimensions_of_eq_bot DA W hW T hd hp he
  have hgen' := associated_generation P F w hF hw 1 hgen
  obtain ⟨hlift,_,hactual⟩ := (T).propagation_from_actual_components DA hd hp (piece P)
    (filtration_homogeneous P F w hF) (differential_piece P hX)
    (auxiliaryPiece P 1) (auxiliaryPiece_homogeneous P 1)
    (differential_auxiliaryPiece P hX 1) hfirst hgen'
  exact ⟨hlift,hactual⟩

/-- **Proposition 3.1.** Every auxiliary, homological and integer internal
degree is retained, and the original Koszul homology algebra is generated
by its actual auxiliary-degree-one cycle classes and the unit. -/
theorem proposition31
    (hβ : ∀ (p : ℕ) (q : ℤ),
      BigradedPolynomialAlgebra.bettiNumber P hX 1 p q=
        BigradedPolynomialAlgebra.bettiNumber Q hY 1 p q)
    (hgen : Algebra.adjoin K (selectedHomologyClasses DB (auxiliaryPiece (V:=V) Q 1))=⊤) :
    (∀ (m p : ℕ) (q : ℤ),BigradedPolynomialAlgebra.bettiNumber P hX m p q=
      BigradedPolynomialAlgebra.bettiNumber Q hY m p q) ∧
      Algebra.adjoin K (selectedHomologyClasses DA (auxiliaryPiece (V:=V) P 1))=⊤ := by
  obtain ⟨hlift,hactual⟩ := proposition31_cycleLifts P hX F w hF hw hβ hgen
  refine ⟨?_,hactual⟩
  intro m p q
  calc
    BigradedPolynomialAlgebra.bettiNumber P hX m p q=
        Module.finrank K ((T).AssociatedComponentHomologyCarrier DA hd hp
          (strand P (q,m) ((p+1:ℕ):ℤ)) (strand P (q,m) (p:ℤ))
          (strand P (q,m) ((p:ℤ)-1)) (BigradedCycleLifting.incoming_mem P hX (q,m) p)
          (differential_strand P hX (q,m) (p:ℤ))) :=
      BigradedCycleLifting.bettiNumber_eq_associatedHomology_of_lifts P hX F w hF hw hlift m p q
    _ = Module.finrank K (BigradedCycleLifting.Homology Q hY (q,m) p) :=
      (((T).associatedComponentHomologyCarrierEquiv DA hd hp
        (strand P (q,m) ((p+1:ℕ):ℤ)) (strand P (q,m) (p:ℤ))
        (strand P (q,m) ((p:ℤ)-1)) (BigradedCycleLifting.incoming_mem P hX (q,m) p)
        (differential_strand P hX (q,m) (p:ℤ))).trans
          (associatedStrandHomologyEquiv P hX F w hF hw (q,m) p)).finrank_eq
    _ = BigradedPolynomialAlgebra.bettiNumber Q hY m p q :=
      (BigradedCycleLifting.bettiNumber_eq_finrank Q hY m p q).symm

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.proposition31_cycleLifts
#print axioms FourPapers.Sublattice.proposition31

end
end
end


end
