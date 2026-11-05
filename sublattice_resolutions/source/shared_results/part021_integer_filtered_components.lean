module
public import graph_foundation.part014
public import shared_results.part021_closed_graph_theorem11

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredComponents -/
section

/-! # Actual finite homogeneous pieces of the associated algebra

The associated piece of a submodule W is the span of actual symbols of
elements of W. A finite interval containing its induced filtration gives
an explicit equivalence with the product of its successive quotients.
Both injectivity and surjectivity are proved; the finite interval is not
an additional flatness or degeneration hypothesis.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical FilteredHomology
open scoped BigOperators

def quotientLift
    {K X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X]
    [AddCommMonoid Y] [Module K Y]
    (P : Submodule K X) (f : X →ₗ[K] Y) (h : P ≤ LinearMap.ker f) :
    (X ⧸ P) →ₗ[K] Y := by
  letI : AddCommGroup Y := Module.addCommMonoidToAddCommGroup K
  exact P.liftQ (R := K) (R₂ := K) (M := X) (M₂ := Y)
    (τ₁₂ := RingHom.id K) f h

def filteredGradeLift
    {K X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X]
    [AddCommMonoid Y] [Module K Y]
    (G : FilteredHomology.Filtration (K := K) X) (n : ℕ)
    (f : (G.level (n+1)) →ₗ[K] Y) (h : lowerInLevel G n ≤ LinearMap.ker f) :
    FilteredHomology.Grade G n →ₗ[K] Y :=
  quotientLift (K := K) (X := G.level (n+1)) (Y := Y) (lowerInLevel G n) f h

private theorem filteredGradeLift_mk
    {K X Y : Type*} [CommRing K] [AddCommGroup X] [Module K X]
    [AddCommMonoid Y] [Module K Y]
    (G : FilteredHomology.Filtration (K := K) X) (n : ℕ)
    (f : (G.level (n+1)) →ₗ[K] Y) (h : lowerInLevel G n ≤ LinearMap.ker f)
    (a : G.level (n+1)) :
    filteredGradeLift G n f h ((lowerInLevel G n).mkQ a) = f a := rfl

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (W : Submodule K A)

def associatedPiece : Submodule K F.AssociatedGraded :=
  Submodule.span K {z | ∃ n, ∃ a : F.level n,a.val∈W ∧ z=F.symbol n a}

@[simp] theorem associatedPiece_bot : F.associatedPiece (⊥ : Submodule K A)=⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro z ⟨n,a,ha,rfl⟩
  have ha0 : a=0 := Subtype.ext ((Submodule.mem_bot K).mp ha)
  rw [ha0,map_zero]
  exact Submodule.zero_mem _

theorem associatedPiece_mono {W U : Submodule K A} (hWU : W≤U) :
    F.associatedPiece W≤F.associatedPiece U := by
  apply Submodule.span_mono
  rintro z ⟨n,a,ha,rfl⟩
  exact ⟨n,a,hWU ha,rfl⟩

theorem symbol_mem_associatedPiece (n : ℤ) (a : F.level n) (ha : a.val∈W) :
    F.symbol n a ∈ F.associatedPiece W := Submodule.subset_span ⟨n,a,ha,rfl⟩

theorem leading_mem_associatedPiece (p : F.rees) (hp : ∀ n,p.val.coeff n∈W) :
    F.leadingMap p∈F.associatedPiece W := by
  rw [F.symbol_decomposition]
  exact Submodule.sum_mem _ (fun n _ => F.symbol_mem_associatedPiece W n _ (hp n))

theorem mem_associatedPiece_iff (z : F.AssociatedGraded) :
    z∈F.associatedPiece W ↔ ∃ p : F.rees,F.leadingMap p=z ∧ ∀ n,p.val.coeff n∈W := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨n,a,ha,rfl⟩ := hz
        refine ⟨F.monomial n a,rfl,?_⟩
        intro i
        rw [F.monomial_coeff]
        split_ifs
        · exact ha
        · exact W.zero_mem
    | zero => exact ⟨0,F.leadingMap.map_zero,fun n => W.zero_mem⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨p,rfl,hp⟩ := ihx
        obtain ⟨q,rfl,hq⟩ := ihy
        exact ⟨p+q,F.leadingMap.map_add p q,fun n => W.add_mem (hp n) (hq n)⟩
    | smul c x hx ih =>
        obtain ⟨p,rfl,hp⟩ := ih
        exact ⟨c•p,F.leadingMap.toLinearMap.map_smul c p,fun n => W.smul_mem c (hp n)⟩
  · rintro ⟨p,rfl,hp⟩
    exact F.leading_mem_associatedPiece W p hp

variable [FiniteDimensional K W] (L : ℤ)
  (hL : (F.level (L-1)).comap W.subtype=⊥)

local notation "G" => F.componentFiltration W L hL

instance componentLevelAddCommGroup (n : ℕ) : AddCommGroup ((G).level n) :=
  Submodule.addCommGroup (R := K) (M := W) ((G).level n)

instance componentLevelModule (n : ℕ) : Module K ((G).level n) :=
  Submodule.module (R := K) (M := W) ((G).level n)

instance componentGradeAddCommGroup (n : ℕ) : AddCommGroup (FilteredHomology.Grade G n) :=
  Submodule.Quotient.addCommGroup (R := K) (M := (G).level (n+1)) (lowerInLevel G n)

instance componentGradeModule (n : ℕ) : Module K (FilteredHomology.Grade G n) :=
  Submodule.Quotient.module (R := K) (M := (G).level (n+1)) (lowerInLevel G n)

def componentLevelInclusion (n : ℕ) : (G).level (n+1) →ₗ[K] F.level (L+(n:ℤ)) where
  toFun a := ⟨a.val.val,by
    have h := a.property
    change a.val.val∈F.level (L+((n+1:ℕ):ℤ)-1) at h
    have he : L+((n+1:ℕ):ℤ)-1=L+(n:ℤ) := by omega
    simpa only [he] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem componentLevelSymbol_lower (n : ℕ) (a : (G).level (n+1))
    (ha : a ∈ lowerInLevel G n) :
    F.symbol (L+(n:ℤ)) (F.componentLevelInclusion W L hL n a) = 0 :=
  (F.symbol_eq_zero (L+(n:ℤ)) (F.componentLevelInclusion W L hL n a)).mpr ha

def componentLevelSymbol (n : ℕ) : (G).level (n+1) →ₗ[K] F.AssociatedGraded where
  toFun a := F.symbol (L+(n:ℤ)) (F.componentLevelInclusion W L hL n a)
  map_add' a b := by
    rw [(F.componentLevelInclusion W L hL n).map_add, (F.symbol (L+(n:ℤ))).map_add]
  map_smul' c a := by
    rw [(F.componentLevelInclusion W L hL n).map_smul, (F.symbol (L+(n:ℤ))).map_smul]
    rfl

@[simp] theorem componentLevelSymbol_apply (n : ℕ) (a : (G).level (n+1)) :
    F.componentLevelSymbol W L hL n a =
      F.symbol (L+(n:ℤ)) (F.componentLevelInclusion W L hL n a) := rfl

theorem componentLevelSymbol_ker (n : ℕ) :
    lowerInLevel G n ≤ LinearMap.ker (F.componentLevelSymbol W L hL n) := by
  intro a ha
  exact F.componentLevelSymbol_lower W L hL n a ha

attribute [local irreducible] componentLevelSymbol filteredGradeLift

set_option backward.isDefEq.respectTransparency true in
def componentGradeSymbol (n : ℕ) : FilteredHomology.Grade G n →ₗ[K] F.AssociatedGraded :=
  filteredGradeLift (K := K) (X := W) (Y := F.AssociatedGraded) G n
    (componentLevelSymbol (K := K) (A := A) F W L hL n)
    (componentLevelSymbol_ker (K := K) (A := A) F W L hL n)

@[simp] theorem componentGradeSymbol_mk (n : ℕ) (a : (G).level (n+1)) :
    F.componentGradeSymbol W L hL n ((lowerInLevel G n).mkQ a)=
      F.symbol (L+(n:ℤ)) (F.componentLevelInclusion W L hL n a) := by
  rw [componentGradeSymbol, filteredGradeLift_mk, componentLevelSymbol_apply]

theorem componentGradeSymbol_injective (n : ℕ) :
    Function.Injective (F.componentGradeSymbol W L hL n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨a,rfl⟩ := (lowerInLevel G n).mkQ_surjective z
  rw [LinearMap.mem_ker,F.componentGradeSymbol_mk,F.symbol_eq_zero] at hz
  apply (Submodule.mem_bot K).mpr
  exact (Submodule.Quotient.mk_eq_zero (lowerInLevel G n)).mpr hz

theorem componentGradeSymbol_mem (n : ℕ) (z : FilteredHomology.Grade G n) :
    F.componentGradeSymbol W L hL n z ∈ F.associatedPiece W := by
  obtain ⟨a,rfl⟩ := (lowerInLevel G n).mkQ_surjective z
  rw [F.componentGradeSymbol_mk]
  exact F.symbol_mem_associatedPiece W (L+(n:ℤ))
    (F.componentLevelInclusion W L hL n a) a.val.property

theorem componentGradeSymbol_projection_ne (n : ℕ) (z : FilteredHomology.Grade G n) (i : ℤ)
    (hi : i≠L+(n:ℤ)) :
    F.associatedGradedEquiv (F.componentGradeSymbol W L hL n z) i=0 := by
  obtain ⟨a,rfl⟩ := (lowerInLevel G n).mkQ_surjective z
  rw [F.componentGradeSymbol_mk,F.associatedGradedEquiv_symbol]
  exact DirectSum.of_eq_of_ne _ _ _ hi

def componentGradedSum (N : ℕ) : (∀ n : Fin N,FilteredHomology.Grade G n.val) →ₗ[K] F.AssociatedGraded :=
  ∑ n : Fin N,(F.componentGradeSymbol W L hL n.val).comp (LinearMap.proj n)

theorem componentGradedSum_apply (N : ℕ) (z : ∀ n : Fin N,FilteredHomology.Grade G n.val) :
    F.componentGradedSum W L hL N z =
      ∑ n : Fin N,F.componentGradeSymbol W L hL n.val (z n) := by
  simp only [componentGradedSum,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]

theorem componentGradedSum_single (N : ℕ) (n : Fin N) (z : FilteredHomology.Grade G n.val) :
    F.componentGradedSum W L hL N (Pi.single n z)=F.componentGradeSymbol W L hL n.val z := by
  rw [F.componentGradedSum_apply]
  rw [Finset.sum_eq_single n]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact (h (Finset.mem_univ n)).elim

theorem componentGradedSum_injective (N : ℕ) :
    Function.Injective (F.componentGradedSum W L hL N) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  apply (Submodule.mem_bot K).mpr
  funext n
  apply F.componentGradeSymbol_injective W L hL n.val
  change F.componentGradeSymbol W L hL n.val (z n) =
    F.componentGradeSymbol W L hL n.val 0
  rw [(F.componentGradeSymbol W L hL n.val).map_zero]
  apply F.associatedGradedEquiv.injective
  ext i
  by_cases hi : i=L+(n.val:ℤ)
  · subst i
    have hh := congrArg (fun a : F.AssociatedGraded =>
      F.associatedGradedEquiv a (L+(n.val:ℤ))) hz
    change F.associatedGradedEquiv (F.componentGradedSum W L hL N z) (L+(n.val:ℤ))=0 at hh
    rw [F.componentGradedSum_apply,map_sum,DirectSum.sum_apply] at hh
    rw [Finset.sum_eq_single n] at hh
    · exact hh
    · intro j _ hj
      exact F.componentGradeSymbol_projection_ne W L hL j.val (z j) _
        (by intro h; apply hj; apply Fin.ext; omega)
    · intro h
      exact (h (Finset.mem_univ n)).elim
  · exact F.componentGradeSymbol_projection_ne W L hL n.val (z n) i hi

variable (N : ℕ)
  (hN : (F.componentFiltration W L hL).level N = (⊤ : Submodule K W))

include hN in
theorem symbol_mem_componentGradedSum_range (n : ℤ) (a : F.level n) (ha : a.val∈W) :
    F.symbol n a ∈ LinearMap.range (F.componentGradedSum W L hL N) := by
  by_cases hnlo : n<L
  · have ha0 : a.val=0 := by
      have h : (⟨a.val,ha⟩ : W)∈(F.level (L-1)).comap W.subtype :=
        F.mono (by omega) a.property
      rw [hL,Submodule.mem_bot] at h
      exact congrArg Subtype.val h
    have haz : a=0 := Subtype.ext ha0
    rw [haz,map_zero]
    exact Submodule.zero_mem _
  by_cases hnhi : L+(N:ℤ)≤n
  · have hz : F.symbol n a=0 := by
      rw [F.symbol_eq_zero]
      have h : (⟨a.val,ha⟩ : W)∈(G).level N := by rw [hN]; trivial
      exact F.mono (by omega) h
    rw [hz]
    exact Submodule.zero_mem _
  · let j : Fin N := ⟨(n-L).toNat,by omega⟩
    have hj : L+(j.val:ℤ)=n := by dsimp [j]; omega
    let b : (G).level (j.val+1) := ⟨⟨a.val,ha⟩,by
      change a.val∈F.level (L+((j.val+1:ℕ):ℤ)-1)
      have he : L+((j.val+1:ℕ):ℤ)-1=n := by omega
      simpa only [he] using a.property⟩
    refine ⟨Pi.single j ((lowerInLevel G j.val).mkQ b),?_⟩
    rw [F.componentGradedSum_single,F.componentGradeSymbol_mk]
    exact F.symbol_congr _ _ hj _ a rfl

include hN in
theorem componentGradedSum_range :
    LinearMap.range (F.componentGradedSum W L hL N)=F.associatedPiece W := by
  apply le_antisymm
  · rintro z ⟨a,rfl⟩
    rw [F.componentGradedSum_apply]
    exact Submodule.sum_mem _ (fun n _ => F.componentGradeSymbol_mem W L hL n.val (a n))
  · apply Submodule.span_le.mpr
    rintro z ⟨n,a,ha,rfl⟩
    exact F.symbol_mem_componentGradedSum_range W L hL N hN n a ha

/-- The actual associated piece is the finite product of the literal
successive quotients in any interval containing its induced filtration. -/
def componentAssociatedEquiv :
    (∀ n : Fin N,FilteredHomology.Grade G n.val) ≃ₗ[K] F.associatedPiece W :=
  (LinearEquiv.ofInjective (F.componentGradedSum W L hL N)
    (F.componentGradedSum_injective W L hL N)).trans
      (LinearEquiv.ofEq _ _ (F.componentGradedSum_range W L hL N hN))

@[simp] theorem componentAssociatedEquiv_val (z : ∀ n : Fin N,FilteredHomology.Grade G n.val) :
    (F.componentAssociatedEquiv W L hL N hN z).val=F.componentGradedSum W L hL N z := rfl

include hN in
theorem associatedPiece_finite : Module.Finite K (F.associatedPiece W) :=
  Module.Finite.equiv (F.componentAssociatedEquiv W L hL N hN)

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
