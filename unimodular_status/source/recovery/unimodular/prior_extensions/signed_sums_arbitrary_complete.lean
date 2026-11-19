module

public import Recovery.Unimodular.PriorExtensions.SignedSumsArbitraryLattice

/-!
# All signed sums on the paper's original arbitrary integral lattices

The literal direct sum and freely chosen triangle signs are included here.
Every coordinate map is an actual integral equivalence commuting with the
original real embedding; no abstract matroid replaces the resulting vectors.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open TauCeti.Toric

namespace Unimodular.SignedSums
open LatticeCoordinates

section Direct
variable {n₁ n₂ : ℕ} {N₁ N₂ V₁ V₂ L S : Type*}
  [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
  {ι₁ : N₁ →+ V₁} {ι₂ : N₂ →+ V₂}

 def directLatticeFamily (U : L → N₁) (V : S → N₂) : L ⊕ S → N₁ × N₂ :=
  Sum.elim (fun l => (U l, 0)) (fun s => (0, V s))

/-- Full signed one-sum statement on the actual original lattice product. -/
theorem proposition_2_2_one_sum_arbitrary_lattice
    (hι₁ : IsIntegralLattice ι₁) (hι₂ : IsIntegralLattice ι₂)
    (b₁ : Module.Basis (Fin n₁) ℤ N₁) (b₂ : Module.Basis (Fin n₂) ℤ N₂)
    (U : L → N₁) (V : S → N₂)
    (hU : IntegralRigidity.Uniform b₁ U) (hV : IntegralRigidity.Uniform b₂ V)
    (hspanU : Submodule.span ℝ (Set.range (fun j => ι₁ (U j))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun j => ι₂ (V j))) = ⊤) :
    (∃ b : Module.Basis (Fin (n₁ + n₂)) ℤ (N₁ × N₂),
      IntegralRigidity.Uniform b (directLatticeFamily U V) ∧
      Submodule.span ℤ (Set.range (directLatticeFamily U V)) = ⊤ ∧
      Matrix.IsTotallyUnimodular (fun i j => b.repr (directLatticeFamily U V j) i)) ∧
    VectorMatroid.ofFamily (K := ℝ) (fun j =>
      (ι₁ (directLatticeFamily U V j).1, ι₂ (directLatticeFamily U V j).2)) =
      (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₁ (U j))).sum
        (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₂ (V j))) := by
  classical
  obtain ⟨b, _hu, hs, ht⟩ := proposition_2_2_one_sum (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V)
    ((uniform_coordinates_iff b₁ U).mpr hU) ((uniform_coordinates_iff b₂ V).mpr hV)
    ((lattice_span_coordinates_iff hι₁ b₁ U).mpr hspanU)
    ((lattice_span_coordinates_iff hι₂ b₂ V).mpr hspanV)
  let e := (latticeEquiv b₁).prodCongr (latticeEquiv b₂)
  let b' := b.map e.symm
  have he : e ∘ directLatticeFamily U V = directFamily (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V) := by
    funext j
    cases j <;> simp [e, directLatticeFamily, directFamily]
  have hcoords : (fun i j => b'.repr (directLatticeFamily U V j) i) =
      (fun i j => b.repr (directFamily (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V) j) i) := by
    funext i j
    change b.repr (e (directLatticeFamily U V j)) i = _
    have hj := congrFun he j
    dsimp only [Function.comp_apply] at hj
    rw [hj]
  have ht' : Matrix.IsTotallyUnimodular (fun i j => b'.repr (directLatticeFamily U V j) i) :=
    hcoords.symm ▸ ht
  refine ⟨⟨b', uniform_of_coordinate_tu b' _ ht', ?_, ht'⟩, ?_⟩
  · apply (Submodule.map_eq_top_iff (e := e)).mp
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span ℤ (Set.range (e ∘ directLatticeFamily U V)) = ⊤
    rw [he]
    exact hs
  · have hv : (fun j => (ι₁ (directLatticeFamily U V j).1,
        ι₂ (directLatticeFamily U V j).2)) =
        directVectors (K := ℝ) (fun j => ι₁ (U j)) (fun j => ι₂ (V j)) := by
      funext j
      cases j <;> simp [directLatticeFamily, directVectors]
    rw [hv]
    exact directVectors_matroid _ _

end Direct

section Alignment
variable {N : Type*} [AddCommGroup N] {L : Type*}

/-- Actual sign changes of only the first two port vectors. -/
def latticeAlignedTriangle (U : Fin 3 ⊕ L → N) (ε δ : ℤ) : Fin 3 ⊕ L → N :=
  fun j => triangleSigns ε δ j • U j

@[simp] theorem latticeAlignedTriangle_survivor (U : Fin 3 ⊕ L → N) (ε δ : ℤ) (j : L) :
    latticeAlignedTriangle U ε δ (.inr j) = U (.inr j) := by
  simp [latticeAlignedTriangle, triangleSigns]

 theorem latticeAlignedTriangle_coordinates {n : ℕ} (e : N ≃ₗ[ℤ] Lattice n)
    (U : Fin 3 ⊕ L → N) (ε δ : ℤ) :
    e ∘ latticeAlignedTriangle U ε δ = alignedTriangle (e ∘ U) ε δ := by
  funext j
  exact map_smul e (triangleSigns ε δ j) (U j)

end Alignment

section ArbitraryTriangle
variable {n₁ n₂ : ℕ} {N₁ N₂ V₁ V₂ L S : Type*}
  [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
  {ι₁ : N₁ →+ V₁} {ι₂ : N₂ →+ V₂} [Fintype L] [Fintype S]

/-- Every ordinary triangle circuit admits the signed operation on the
original lattices; signs, quotient freeness, exact rank, and ordinary output
matroid are all concluded, while both original input matroids are retained. -/
theorem proposition_2_2_three_sum_arbitrary_alignment
    (hι₁ : IsIntegralLattice ι₁) (hι₂ : IsIntegralLattice ι₂)
    (b₁ : Module.Basis (Fin n₁) ℤ N₁) (b₂ : Module.Basis (Fin n₂) ℤ N₂)
    (U : Fin 3 ⊕ L → N₁) (V : Fin 3 ⊕ S → N₂)
    (hU : IntegralRigidity.Uniform b₁ U) (hV : IntegralRigidity.Uniform b₂ V)
    (hspanU : Submodule.span ℝ (Set.range (fun j => ι₁ (U (.inr j)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun j => ι₂ (V (.inr j)))) = ⊤)
    (hCU : (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₁ (U j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
    (hCV : (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₂ (V j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ S))) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℤ,
      (ε₁ = 1 ∨ ε₁ = -1) ∧ (δ₁ = 1 ∨ δ₁ = -1) ∧
      (ε₂ = 1 ∨ ε₂ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧
      LatticeSumConclusion n₁ n₂ triangleBasisLabels
        (latticeAlignedTriangle U ε₁ δ₁) (latticeAlignedTriangle V ε₂ δ₂) ∧
      LatticeOrdinaryMatroidConclusion ι₁ ι₂ triangleBasisLabels
        (latticeAlignedTriangle U ε₁ δ₁) (latticeAlignedTriangle V ε₂ δ₂) ∧
      VectorMatroid.ofFamily (K := ℝ) (fun j => ι₁ (latticeAlignedTriangle U ε₁ δ₁ j)) =
        VectorMatroid.ofFamily (K := ℝ) (fun j => ι₁ (U j)) ∧
      VectorMatroid.ofFamily (K := ℝ) (fun j => ι₂ (latticeAlignedTriangle V ε₂ δ₂ j)) =
        VectorMatroid.ofFamily (K := ℝ) (fun j => ι₂ (V j)) := by
  obtain ⟨ε₁, δ₁, ε₂, δ₂, he₁, hd₁, he₂, hd₂, hsum, hmat, hmu, hmv⟩ :=
    proposition_2_2_three_sum_without_prescribed_alignment
      (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V)
      ((uniform_coordinates_iff b₁ U).mpr hU) ((uniform_coordinates_iff b₂ V).mpr hV)
      ((lattice_span_coordinates_iff hι₁ b₁ (U ∘ Sum.inr)).mpr hspanU)
      ((lattice_span_coordinates_iff hι₂ b₂ (V ∘ Sum.inr)).mpr hspanV)
      (by simpa only [Function.comp_apply, lattice_matroid_coordinates hι₁ b₁ U] using hCU)
      (by simpa only [Function.comp_apply, lattice_matroid_coordinates hι₂ b₂ V] using hCV)
  rw [← latticeAlignedTriangle_coordinates (latticeEquiv b₁) U ε₁ δ₁,
    ← latticeAlignedTriangle_coordinates (latticeEquiv b₂) V ε₂ δ₂] at hsum hmat
  rw [← latticeAlignedTriangle_coordinates (latticeEquiv b₁) U ε₁ δ₁] at hmu
  rw [← latticeAlignedTriangle_coordinates (latticeEquiv b₂) V ε₂ δ₂] at hmv
  refine ⟨ε₁, δ₁, ε₂, δ₂, he₁, hd₁, he₂, hd₂,
    latticeSumConclusion_of_coordinates (latticeEquiv b₁) (latticeEquiv b₂) _ _ _ hsum,
    latticeOrdinaryMatroidConclusion_of_coordinates hι₁ hι₂ b₁ b₂ _ _ _ hmat, ?_, ?_⟩
  · simpa only [Function.comp_apply, lattice_matroid_coordinates hι₁ b₁] using hmu
  · simpa only [Function.comp_apply, lattice_matroid_coordinates hι₂ b₂] using hmv

end ArbitraryTriangle

#print axioms proposition_2_2_one_sum_arbitrary_lattice
#print axioms latticeAlignedTriangle_coordinates
#print axioms proposition_2_2_three_sum_arbitrary_alignment

end Unimodular.SignedSums

#check Unimodular.SignedSums.proposition_2_2_three_sum_arbitrary_alignment
