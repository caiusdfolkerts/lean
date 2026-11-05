/- Integral normalization from the paper's maximal-minor definition.
No total-unimodularity assumption is introduced: every smaller minor is
completed using basis columns genuinely selected from the configuration. -/
module
public import Unimodular.Extensions
public import Recovery.Unimodular.PriorExtensions.SignedSumsPorts
public import Mathlib.LinearAlgebra.Pi
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace Unimodular.SignedSums
/-- With all standard basis columns present, bounds on maximal minors imply
bounds on every square minor. The complementary standard columns complete
an arbitrary injectively selected minor to a full determinant. -/
theorem totallyUnimodular_of_maximal_bound {I J : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (I) J ℤ)
    (hmax : ∀ g : I → J, |(A.submatrix id g).det| ≤ 1)
    (hstd : ∀ i : I, ∃ j : J, (fun k => A k j) = Pi.single i 1) :
    A.IsTotallyUnimodular := by
  classical
  choose s hs using hstd
  have hentry (j i : I) : A i (s j) = if i = j then 1 else 0 := by
    simpa [Pi.single_apply, eq_comm] using congrFun (hs j) i
  intro k f g hf hg
  let C := {i : I // i ∉ Set.range f}
  let e : Fin k ⊕ C ≃ I :=
    ((Equiv.ofInjective f hf).sumCongr (Equiv.refl C)).trans
      (Equiv.sumCompl (fun i : I => i ∈ Set.range f))
  have heL (i : Fin k) : e (Sum.inl i) = f i := rfl
  have heR (i : C) : e (Sum.inr i) = i.val := rfl
  have heLinv (i : Fin k) : e.symm (f i) = Sum.inl i := by
    rw [← heL i, Equiv.symm_apply_apply]
  have heRinv (i : C) : e.symm i.val = Sum.inr i := by
    rw [← heR i, Equiv.symm_apply_apply]
  let h : Fin k ⊕ C → J := Sum.elim g (fun i => s i.val)
  let B : Matrix (I) (I) ℤ := A.submatrix id (h ∘ e.symm)
  let D : Matrix C (Fin k) ℤ := fun i j => A i.val (g j)
  have hblock : B.submatrix e e =
      Matrix.fromBlocks (A.submatrix f g) 0 D (1 : Matrix C C ℤ) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heL]
        | inr j =>
            have hij : f i ≠ j.val := by
              intro he
              exact j.property ⟨i, he⟩
            simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heL, hentry, hij]
    | inr i =>
        cases j with
        | inl j =>
            simp [B, h, D, Matrix.submatrix_apply, heLinv, heRinv, heR]
        | inr j =>
            by_cases hij : i = j
            · subst j
              simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heR, hentry,
                Matrix.one_apply]
            · have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
              simp [B, h, Matrix.submatrix_apply, heLinv, heRinv, heR, hentry,
                Matrix.one_apply, hij, hval]
  have hB : |B.det| ≤ 1 := hmax (h ∘ e.symm)
  have hedet : (B.submatrix e e).det = B.det :=
    Matrix.det_submatrix_equiv_self e B
  rw [← hedet, hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one] at hB
  have hbound := abs_le.mp hB
  have hsmall : (A.submatrix f g).det = 0 ∨
      (A.submatrix f g).det = 1 ∨ (A.submatrix f g).det = -1 := by omega
  rcases hsmall with h0 | h1 | hn1
  · exact ⟨0, by simpa using h0.symm⟩
  · exact ⟨1, by simpa using h1.symm⟩
  · exact ⟨-1, by simpa using hn1.symm⟩


/-- Absolute determinant is independent of the choice of an integral basis. -/
theorem determinant_abs_basis_independent {I M : Type*}
    [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℤ M]
    (b c : Module.Basis I ℤ M) (u : I → M) : |b.det u| = |c.det u| := by
  have he : b.det u = b.det c * c.det u := by
    have hm := b.det.eq_smul_basis_det c
    have hv := congrArg (fun f : M [⋀^I]→ₗ[ℤ] ℤ => f u) hm
    simpa only [AlternatingMap.smul_apply, smul_eq_mul] using hv
  have hunit : |b.det c| = 1 := Int.isUnit_iff_abs_eq.mp (b.isUnit_det c)
  rw [he, abs_mul, hunit, one_mul]


/-- The paper's determinant bounds are independent of integral coordinates
and of the finite type used to index a basis. -/
theorem uniform_basis_change {I J E M : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [AddCommGroup M] [Module ℤ M]
    (b₀ : Module.Basis J ℤ M) (b : Module.Basis I ℤ M) (U : E → M)
    (hU : IntegralRigidity.Uniform b₀ U) : IntegralRigidity.Uniform b U := by
  let e : I ≃ J := b.indexEquiv b₀
  intro g
  have hb := hU (g ∘ e.symm)
  have hd := determinant_abs_basis_independent (b.reindex e) b₀
    (U ∘ (g ∘ e.symm))
  rw [Module.Basis.det_reindex] at hd
  have he : (U ∘ (g ∘ e.symm)) ∘ e = U ∘ g := by ext i; simp
  rw [he] at hd
  exact hd.trans_le hb

/-- Coordinates in any selected integral basis are totally unimodular. -/
theorem coordinates_tu_of_uniform {I J E M : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [AddCommGroup M] [Module ℤ M]
    (b₀ : Module.Basis J ℤ M) (b : Module.Basis I ℤ M) (U : E → M)
    (hU : IntegralRigidity.Uniform b₀ U) (hb : ∀ i, ∃ j, U j = b i) :
    Matrix.IsTotallyUnimodular (fun i j => b.repr (U j) i) := by
  apply totallyUnimodular_of_maximal_bound
  · intro g
    have hd : (Matrix.submatrix (fun i j => b.repr (U j) i) id g).det =
        b.det (U ∘ g) := by rw [Module.Basis.det_apply]; rfl
    rw [hd]
    exact uniform_basis_change b₀ b U hU g
  · intro i
    obtain ⟨j, hj⟩ := hb i
    refine ⟨j, ?_⟩
    rw [hj]
    ext k
    simp [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]

def productCoordinates {P A M E : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] (P → ℤ) × (A → ℤ)) (U : E → M) : Matrix (P ⊕ A) E ℤ :=
  fun i j => Sum.elim (e (U j)).1 (e (U j)).2 i

/-- An independent port extends to a genuine integral basis, with every
basis vector chosen from the original system and each port placed first. -/
structure PortNormalization {n r : ℕ} {E : Type*} (U : E → Lattice n)
    (a : Fin r → E) where
  Complement : Type
  finiteComplement : Fintype Complement
  equiv : Lattice n ≃ₗ[ℤ] (Fin r → ℤ) × (Complement → ℤ)
  port_eq : ∀ i, equiv (U (a i)) = (Pi.single i 1, 0)
  totallyUnimodular : (productCoordinates equiv U).IsTotallyUnimodular

attribute [instance] PortNormalization.finiteComplement

theorem exists_portNormalization {n r : ℕ} {E : Type*} (U : E → Lattice n)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) U)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (U e))) = ⊤)
    (a : Fin r → E) (ha : LinearIndependent ℝ (fun i => embed (U (a i)))) :
    Nonempty (PortNormalization U a) := by
  classical
  let S := Set.range U
  have hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : S => u.val) := by
    intro f
    choose g hg using (fun i => (f i).property)
    have he : (fun u : S => u.val) ∘ f = U ∘ g := by funext i; exact (hg i).symm
    rw [he]
    exact hU g
  have hspanS : Submodule.span ℝ (embed '' S) = ⊤ := by
    have he : embed '' S = Set.range (fun e => embed (U e)) := by
      ext x
      simp [S, Set.mem_range]
    rw [he]
    exact hspan
  let aS : Fin r → S := fun i => ⟨U (a i), a i, rfl⟩
  obtain ⟨b, hbS, hba⟩ := LatticeHull.exists_lattice_basis_extension S hS hspanS aS ha
  choose c hc using hba
  have hc' (i : Fin r) : b (c i) = U (a i) := hc i
  have hci : Function.Injective c := by
    intro i j hij
    apply ha.injective
    change embed (U (a i)) = embed (U (a j))
    rw [← hc' i, ← hc' j, hij]
  let C := {j : Fin n // j ∉ Set.range c}
  let e : Fin r ⊕ C ≃ Fin n :=
    ((Equiv.ofInjective c hci).sumCongr (Equiv.refl C)).trans
      (Equiv.sumCompl (fun j : Fin n => j ∈ Set.range c))
  let b' := b.reindex e.symm
  have hb' (i : Fin r) : b' (.inl i) = U (a i) := by
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_symm]
    change b (c i) = U (a i)
    exact hc' i
  let φ : Lattice n ≃ₗ[ℤ] (Fin r → ℤ) × (C → ℤ) :=
    b'.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) C ℤ ℤ)
  have hφ (i : Fin r) : φ (U (a i)) = (Pi.single i 1, 0) := by
    rw [← hb' i]
    apply Prod.ext <;> ext j <;>
      simp [φ, Module.Basis.equivFun_self, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have hbcols : ∀ i, ∃ j, U j = b' i := by
    intro i
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_symm]
    exact hbS (e i)
  have ht := coordinates_tu_of_uniform (Pi.basisFun ℤ (Fin n)) b' U hU hbcols
  refine ⟨⟨C, inferInstance, φ, hφ, ?_⟩⟩
  convert ht using 1
  ext i j
  cases i <;> rfl

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.uniform_basis_change
#print axioms Unimodular.SignedSums.coordinates_tu_of_uniform
#print axioms Unimodular.SignedSums.exists_portNormalization
