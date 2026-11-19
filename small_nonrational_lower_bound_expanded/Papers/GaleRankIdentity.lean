module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Fintype.Powerset
public import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

open Module

namespace Papers.RationalityTen

section ExactSequence

variable {K U V W Z : Type*} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z]

/-- Restricting an exact pair of linear maps to a coordinate kernel gives
the standard kernel equivalence used in Gale duality. -/
noncomputable def restrictedKernelEquiv
    (A : V →ₗ[K] W) (B : U →ₗ[K] V) (π : V →ₗ[K] Z)
    (hB : Function.Injective B) (hexact : B.range = A.ker) :
    (π.comp B).ker ≃ₗ[K] (A.comp π.ker.subtype).ker := by
  let f : (π.comp B).ker →ₗ[K] (A.comp π.ker.subtype).ker := {
    toFun := fun u => ⟨⟨B u, u.2⟩, by
      have hmem : B u ∈ B.range := ⟨u,rfl⟩
      rw [hexact] at hmem
      exact hmem⟩
    map_add' := by intro x y; apply Subtype.ext; apply Subtype.ext; exact B.map_add _ _
    map_smul' := by intro c x; apply Subtype.ext; apply Subtype.ext; exact B.map_smul _ _ }
  refine LinearEquiv.ofBijective f ⟨?_,?_⟩
  · intro x y h
    apply Subtype.ext
    apply hB
    exact congrArg (fun z : (A.comp π.ker.subtype).ker => (z.1 : V)) h
  · intro v
    have hv : (v.1 : V) ∈ B.range := by
      rw [hexact]
      exact v.2
    obtain ⟨u,hu⟩ := hv
    have huπ : u ∈ (π.comp B).ker := by
      change π (B u) = 0
      rw [hu]
      exact v.1.2
    refine ⟨⟨u,huπ⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu

/-- Rank of a restriction and complementary Gale rank satisfy an additive
identity, so no truncated subtraction obscures the dimension statement. -/
theorem exact_restriction_rank_identity
    [FiniteDimensional K U] [FiniteDimensional K V]
    (A : V →ₗ[K] W) (B : U →ₗ[K] V) (π : V →ₗ[K] Z)
    (hB : Function.Injective B) (hexact : B.range = A.ker) :
    finrank K (A.comp π.ker.subtype).range + finrank K U =
      finrank K π.ker + finrank K (π.comp B).range := by
  have hker := (restrictedKernelEquiv A B π hB hexact).finrank_eq
  have hA := (A.comp π.ker.subtype).finrank_range_add_finrank_ker
  have hπ := (π.comp B).finrank_range_add_finrank_ker
  omega

theorem range_eq_kernel_of_dimensions
    [FiniteDimensional K U] [FiniteDimensional K V] [FiniteDimensional K W]
    (A : V →ₗ[K] W) (B : U →ₗ[K] V)
    (hA : Function.Surjective A) (hB : Function.Injective B)
    (hAB : A.comp B = 0)
    (hdim : finrank K U + finrank K W = finrank K V) :
    B.range = A.ker := by
  have hle : B.range ≤ A.ker := by
    rintro _ ⟨u,rfl⟩
    change A (B u) = 0
    exact congrArg (fun f : U →ₗ[K] W => f u) hAB
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hBdim := LinearMap.finrank_range_of_inj hB
  have hAker := A.finrank_range_add_finrank_ker
  have hArange : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  rw [hArange,finrank_top] at hAker
  omega

end ExactSequence

section Coordinates

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def outsideRestriction (S : Finset ι) :
    (ι → K) →ₗ[K] ({i : ι // i ∉ S} → K) where
  toFun x i := x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def insideInjection (S : Finset ι) :
    ({i : ι // i ∈ S} → K) →ₗ[K] (ι → K) where
  toFun x i := if hi : i ∈ S then x ⟨i,hi⟩ else 0
  map_add' x y := by ext i; by_cases hi : i ∈ S <;> simp [hi]
  map_smul' c x := by ext i; by_cases hi : i ∈ S <;> simp [hi]

noncomputable def coordinateKernelEquiv (S : Finset ι) :
    ({i : ι // i ∈ S} → K) ≃ₗ[K] (outsideRestriction (K := K) S).ker := by
  let f : ({i : ι // i ∈ S} → K) →ₗ[K] (outsideRestriction (K := K) S).ker :=
    (insideInjection (K := K) S).codRestrict _ (by
      intro x
      ext i
      simp [outsideRestriction,insideInjection,i.2])
  refine LinearEquiv.ofBijective f ⟨?_,?_⟩
  · intro x y h
    ext i
    have h' := congrArg (fun z : (outsideRestriction (K := K) S).ker => z.1 i.1) h
    simpa [f,insideInjection,i.2] using h'
  · intro w
    refine ⟨fun i => w.1 i.1,?_⟩
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ S
    · simp [f,insideInjection,hi]
    · have hzero := congrFun w.2 ⟨i,hi⟩
      change (if h : i ∈ S then w.val (⟨i,h⟩ : {j // j∈S}).val else 0) = w.val i
      rw [dif_neg hi]
      exact hzero.symm

theorem finrank_coordinateKernel (S : Finset ι) :
    finrank K (outsideRestriction (K := K) S).ker = S.card := by
  rw [← (coordinateKernelEquiv (K := K) S).finrank_eq,
    Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_coe S

theorem insideInjection_range (S : Finset ι) :
    (insideInjection (K := K) S).range = (outsideRestriction (K := K) S).ker := by
  ext w
  constructor
  · rintro ⟨x,rfl⟩
    ext i
    simp [outsideRestriction,insideInjection,i.2]
  · intro hw
    obtain ⟨x,hx⟩ := (coordinateKernelEquiv (K := K) S).surjective ⟨w,hw⟩
    exact ⟨x,congrArg Subtype.val hx⟩

/-- The exact complementary-subset rank formula for an actual pair of
orthogonal coordinate configurations. This is the linear-algebraic content
of matroid duality needed by the paper's Gale reductions. -/
theorem gale_subset_rank_identity
    {U W : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup W] [Module K W]
    (A : (ι → K) →ₗ[K] W) (B : U →ₗ[K] (ι → K))
    (hB : Function.Injective B) (hexact : B.range = A.ker) (S : Finset ι) :
    finrank K (A.comp (insideInjection (K := K) S)).range + finrank K U =
      S.card + finrank K ((outsideRestriction (K := K) S).comp B).range := by
  have h := exact_restriction_rank_identity A B (outsideRestriction (K := K) S) hB hexact
  have hrange : (A.comp (insideInjection (K := K) S)).range =
      (A.comp (outsideRestriction (K := K) S).ker.subtype).range := by
    rw [LinearMap.range_comp,LinearMap.range_comp,insideInjection_range,
      Submodule.range_subtype]
  rw [← hrange,finrank_coordinateKernel] at h
  exact h

end Coordinates

end Papers.RationalityTen
