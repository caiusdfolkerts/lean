/- Literal signed two- and three-sum lattice statements in Proposition 2.2.
Non-coloop means that deletion still spans; triangle ports are sign-aligned
as in the definition of the operation in the paper. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsMain
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

/-- Every conclusion refers to the literal quotient and its actual surviving
columns. A displayed integral basis witnesses freeness and the exact rank. -/
def SumConclusion {n₁ n₂ r : ℕ} {T L R : Type*} (τ : Fin r → T)
    (U : T ⊕ L → Lattice n₁) (V : T ⊕ R → Lattice n₂) : Prop :=
  ∃ k : ℕ, ∃ b : Module.Basis (Fin k) ℤ (PortQuotient τ U V),
    k + r = n₁ + n₂ ∧ IntegralRigidity.Uniform b (PortOutput τ U V) ∧
    Submodule.span ℤ (Set.range (PortOutput τ U V)) = ⊤ ∧
    Matrix.IsTotallyUnimodular (fun i j => b.repr (PortOutput τ U V j) i)

/-- Proposition 2.2, the signed 2-sum, in every pair of ranks. The nonzero
port automatically extends to an integral column basis, so the conclusion
requires no extra saturation or total-unimodularity assumption. -/
theorem proposition_2_2_two_sum {n₁ n₂ : ℕ} {L R : Type*}
    (U : Fin 1 ⊕ L → Lattice n₁) (V : Fin 1 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤)
    (hpU : U (.inl 0) ≠ 0) (hpV : V (.inl 0) ≠ 0) :
    SumConclusion id U V := by
  have haU : LinearIndependent ℝ (fun i : Fin 1 => embed (U (.inl i))) := by
    apply linearIndependent_unique_iff.mpr
    intro hz
    apply hpU
    apply LatticeHull.embed_injective
    exact hz.trans (by ext i; norm_num [embed])
  have haV : LinearIndependent ℝ (fun i : Fin 1 => embed (V (.inl i))) := by
    apply linearIndependent_unique_iff.mpr
    intro hz
    apply hpV
    apply LatticeHull.embed_injective
    exact hz.trans (by ext i; norm_num [embed])
  apply signed_port_sum (1 : Matrix (Fin 1) (Fin 1) ℤ) (one_port_compatible _) id
    U V hU hV hspanU hspanV haU haV
  · intro t
    have he : (fun i : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℤ) i t) = Pi.single t 1 := by
      ext i
      simp [Matrix.one_apply, Pi.single_apply]
    rw [he, portMap_basis]
    rfl
  · intro t
    have he : (fun i : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℤ) i t) = Pi.single t 1 := by
      ext i
      simp [Matrix.one_apply, Pi.single_apply]
    rw [he, portMap_basis]
    rfl

/-- The two independent triangle columns are indexed without changing their
actual sign or order. -/
def triangleBasisLabels : Fin 2 → Fin 3 := Fin.castSucc

theorem triangle_port_formula {n : ℕ} {L : Type*}
    (U : Fin 3 ⊕ L → Lattice n)
    (h : U (.inl 2) = U (.inl 0) + U (.inl 1)) (t : Fin 3) :
    U (.inl t) = portMap (fun i => U (.inl (triangleBasisLabels i)))
      (fun i => triangle i t) := by
  have h₀ : (fun i => triangle i 0) = Pi.single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [triangle, Pi.single_apply]
  have h₁ : (fun i => triangle i 1) = Pi.single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [triangle, Pi.single_apply]
  have h₂ : (fun i => triangle i 2) = Pi.single (0 : Fin 2) 1 + Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [triangle, Pi.single_apply]
  fin_cases t
  · change U (.inl 0) = portMap (fun i => U (.inl (triangleBasisLabels i)))
      (fun i => triangle i 0)
    rw [h₀, portMap_basis]
    rfl
  · change U (.inl 1) = portMap (fun i => U (.inl (triangleBasisLabels i)))
      (fun i => triangle i 1)
    rw [h₁, portMap_basis]
    rfl
  · change U (.inl 2) = portMap (fun i => U (.inl (triangleBasisLabels i)))
      (fun i => triangle i 2)
    rw [h₂, map_add, portMap_basis, portMap_basis]
    exact h

/-- Proposition 2.2, the signed 3-sum, for every pair of ambient ranks and
all surviving label sets. The only port hypotheses are an actual aligned
triangle and the stated deletion-spanning condition. -/
theorem proposition_2_2_three_sum {n₁ n₂ : ℕ} {L R : Type*}
    (U : Fin 3 ⊕ L → Lattice n₁) (V : Fin 3 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤)
    (haU : LinearIndependent ℝ (fun i => embed (U (.inl (triangleBasisLabels i)))))
    (haV : LinearIndependent ℝ (fun i => embed (V (.inl (triangleBasisLabels i)))))
    (htriU : U (.inl 2) = U (.inl 0) + U (.inl 1))
    (htriV : V (.inl 2) = V (.inl 0) + V (.inl 1)) :
    SumConclusion triangleBasisLabels U V :=
  signed_port_sum triangle triangle_compatible triangleBasisLabels U V
    hU hV hspanU hspanV haU haV (triangle_port_formula U htriU)
      (triangle_port_formula V htriV)

/-- The rank-zero port form is canonically the direct lattice sum. -/
theorem proposition_2_2_zero_port_sum {n₁ n₂ : ℕ} {L R : Type*}
    (U : Fin 0 ⊕ L → Lattice n₁) (V : Fin 0 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤) :
    SumConclusion id U V :=
  signed_port_sum (0 : Matrix (Fin 0) (Fin 0) ℤ) (no_port_compatible _) id U V
    hU hV hspanU hspanV linearIndependent_empty_type linearIndependent_empty_type
    (fun t => Fin.elim0 t) (fun t => Fin.elim0 t)

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.proposition_2_2_two_sum
#print axioms Unimodular.SignedSums.proposition_2_2_three_sum
#print axioms Unimodular.SignedSums.proposition_2_2_zero_port_sum
