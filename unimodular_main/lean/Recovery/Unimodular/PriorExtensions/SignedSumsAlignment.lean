/- Existence of the sign alignment for every ordinary triangle circuit.
The signs are derived from uniformity, never supplied as an extra premise. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsHypotheses
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

/-- In an arbitrary uniformly unimodular spanning family, every ordinary
three-element circuit has an actual integral relation with both coefficients
in `{1,-1}`. This supplies the sign alignment in the paper's 3-sum operation. -/
theorem triangle_signed_relation {n : ℕ} {L : Type*}
    (U : Fin 3 ⊕ L → Lattice n)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) U)
    (hspan : Submodule.span ℝ (Set.range (fun j => embed (U j))) = ⊤)
    (hC : (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L))) :
    ∃ ε δ : ℤ, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      U (.inl 2) = ε • U (.inl 0) + δ • U (.inl 1) := by
  classical
  obtain ⟨N⟩ := exists_portNormalization U hU hspan
    (fun i => Sum.inl (triangleBasisLabels i)) (triangle_independent_of_circuit U hC)
  let T := productCoordinates N.equiv U
  let f : Fin 3 ⊕ L → Fin 2 ⊕ N.Complement → ℝ := fun j i => (T i j : ℝ)
  let C : Set (Fin 3 ⊕ L) := Set.range Sum.inl
  have hC' : (VectorMatroid.ofFamily (K := ℝ) f).IsCircuit C := by
    change (VectorMatroid.ofFamily (K := ℝ)
      (fun j i => (productCoordinates N.equiv U i j : ℝ))).IsCircuit C
    rw [portNormalization_real_matroid U _ N]
    exact hC
  have h0 : N.equiv (U (.inl 0)) = (Pi.single (0 : Fin 2) 1, 0) := N.port_eq 0
  have h1 : N.equiv (U (.inl 1)) = (Pi.single (1 : Fin 2) 1, 0) := N.port_eq 1
  have hlabels : C \ {Sum.inl (2 : Fin 3)} = {Sum.inl 0, Sum.inl 1} := by
    ext j
    cases j with
    | inl t => fin_cases t <;> simp [C, Set.mem_range]
    | inr l => simp [C, Set.mem_range]
  have hc2 : f (.inl 2) ∈ Submodule.span ℝ (f '' (C \ {Sum.inl 2})) :=
    (ofFamily_mem_closure_iff f _ _).mp
      (hC'.mem_closure_sdiff_singleton_of_mem ⟨2, rfl⟩)
  rw [hlabels, Set.image_pair] at hc2
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hc2
  let ε : ℤ := T (.inl 0) (.inl 2)
  let δ : ℤ := T (.inl 1) (.inl 2)
  have ha : a = (ε : ℝ) := by
    have h := congrFun hab (.inl 0)
    simpa [f, T, productCoordinates, h0, h1, ε, Pi.single_apply] using h
  have hb : b = (δ : ℝ) := by
    have h := congrFun hab (.inl 1)
    simpa [f, T, productCoordinates, h0, h1, δ, Pi.single_apply] using h
  have hz (j : N.Complement) : (N.equiv (U (.inl 2))).2 j = 0 := by
    have h := congrFun hab (.inr j)
    have h' : ((N.equiv (U (.inl 2))).2 j : ℝ) = 0 := by
      simpa [f, T, productCoordinates, h0, h1] using h.symm
    exact_mod_cast h'
  have hrel : U (.inl 2) = ε • U (.inl 0) + δ • U (.inl 1) := by
    apply N.equiv.injective
    rw [map_add, map_smul, map_smul, h0, h1]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [ε, δ, T, productCoordinates, Pi.single_apply]
    · ext j
      simpa using hz j
  have he0 : ε ≠ 0 := by
    intro he
    have ha0 : a = 0 := by simp [ha, he]
    have hi := (VectorMatroid.ofFamily_indep f _).mp
      (hC'.sdiff_singleton_indep (e := Sum.inl 0) ⟨0, rfl⟩)
    have hnot := hi.notMem_span (i := Sum.inl 2)
      (show Sum.inl (2 : Fin 3) ∈ C \ {Sum.inl 0} from ⟨⟨2, rfl⟩, by simp⟩)
    apply hnot
    have hv : f (.inl 1) ∈ Submodule.span ℝ (f '' ((C \ {Sum.inl 0}) \ {Sum.inl 2})) :=
      Submodule.subset_span ⟨Sum.inl 1, ⟨⟨⟨1, rfl⟩, by simp⟩, by simp⟩, rfl⟩
    have h2 : f (.inl 2) = b • f (.inl 1) := by simpa [ha0] using hab.symm
    rw [h2]
    exact Submodule.smul_mem _ b hv
  have hd0 : δ ≠ 0 := by
    intro hd
    have hb0 : b = 0 := by simp [hb, hd]
    have hi := (VectorMatroid.ofFamily_indep f _).mp
      (hC'.sdiff_singleton_indep (e := Sum.inl 1) ⟨1, rfl⟩)
    have hnot := hi.notMem_span (i := Sum.inl 2)
      (show Sum.inl (2 : Fin 3) ∈ C \ {Sum.inl 1} from ⟨⟨2, rfl⟩, by simp⟩)
    apply hnot
    have hv : f (.inl 0) ∈ Submodule.span ℝ (f '' ((C \ {Sum.inl 1}) \ {Sum.inl 2})) :=
      Submodule.subset_span ⟨Sum.inl 0, ⟨⟨⟨0, rfl⟩, by simp⟩, by simp⟩, rfl⟩
    have h2 : f (.inl 2) = a • f (.inl 0) := by simpa [hb0] using hab.symm
    rw [h2]
    exact Submodule.smul_mem _ a hv
  have hes : ε = 0 ∨ ε = 1 ∨ ε = -1 :=
    Pivot.small_entry N.totallyUnimodular (Sum.inl 0) (Sum.inl 2)
  have hds : δ = 0 ∨ δ = 1 ∨ δ = -1 :=
    Pivot.small_entry N.totallyUnimodular (Sum.inl 1) (Sum.inl 2)
  exact ⟨ε, δ, hes.resolve_left he0, hds.resolve_left hd0, hrel⟩

/-- The actual sign function changes only the first two port orientations. -/
def triangleSigns {L : Type*} (ε δ : ℤ) : Fin 3 ⊕ L → ℤ :=
  Sum.elim ![ε, δ, 1] (fun _ => 1)

def alignedTriangle {n : ℕ} {L : Type*} (U : Fin 3 ⊕ L → Lattice n)
    (ε δ : ℤ) : Fin 3 ⊕ L → Lattice n :=
  fun j => triangleSigns ε δ j • U j

@[simp] theorem alignedTriangle_survivor {n : ℕ} {L : Type*}
    (U : Fin 3 ⊕ L → Lattice n) (ε δ : ℤ) (l : L) :
    alignedTriangle U ε δ (.inr l) = U (.inr l) := by simp [alignedTriangle, triangleSigns]

theorem triangleSigns_abs {L : Type*} {ε δ : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ∀ j : Fin 3 ⊕ L, |triangleSigns ε δ j| = 1 := by
  intro j
  cases j with
  | inl t => fin_cases t <;> rcases hε with rfl | rfl <;>
      rcases hδ with rfl | rfl <;> norm_num [triangleSigns]
  | inr l => simp [triangleSigns]

/-- Arbitrary column sign changes preserve the original ordinary real matroid. -/
theorem signed_family_real_matroid {n : ℕ} {E : Type*}
    (U : E → Lattice n) (s : E → ℤ) (hs : ∀ j, |s j| = 1) :
    VectorMatroid.ofFamily (K := ℝ) (fun j => embed (s j • U j)) =
      VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j)) := by
  classical
  have hs0 (j : E) : s j ≠ 0 := by
    intro h
    have := hs j
    simp [h] at this
  let w : E → ℝˣ := fun j => Units.mk0 (s j : ℝ) (by exact_mod_cast hs0 j)
  apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
  intro S
  change LinearIndependent ℝ (fun j : S => embed (s j.val • U j.val)) ↔
    LinearIndependent ℝ (fun j : S => embed (U j.val))
  have he : (fun j : S => embed (s j.val • U j.val)) =
      (fun j : S => w j.val) • (fun j : S => embed (U j.val)) := by
    funext j
    ext i
    simp [w, embed, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact LinearIndependent.units_smul_iff _ _

theorem alignedTriangle_matroid {n : ℕ} {L : Type*}
    (U : Fin 3 ⊕ L → Lattice n) {ε δ : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    VectorMatroid.ofFamily (K := ℝ) (fun j => embed (alignedTriangle U ε δ j)) =
      VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j)) :=
  signed_family_real_matroid U _ (triangleSigns_abs hε hδ)

/-- Every ordinary port triangle admits the prescribed sign alignment, with
survivors literally unchanged, uniformity retained, and original matroid retained. -/
theorem triangle_alignment_exists {n : ℕ} {L : Type*} [Fintype L]
    (U : Fin 3 ⊕ L → Lattice n)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) U)
    (hspan : Submodule.span ℝ (Set.range (fun j => embed (U j))) = ⊤)
    (hC : (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L))) :
    ∃ ε δ : ℤ, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      alignedTriangle U ε δ (.inl 2) =
        alignedTriangle U ε δ (.inl 0) + alignedTriangle U ε δ (.inl 1) ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (alignedTriangle U ε δ) ∧
      VectorMatroid.ofFamily (K := ℝ) (fun j => embed (alignedTriangle U ε δ j)) =
        VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j)) := by
  obtain ⟨ε, δ, hε, hδ, hrel⟩ := triangle_signed_relation U hU hspan hC
  refine ⟨ε, δ, hε, hδ, ?_, ?_, alignedTriangle_matroid U hε hδ⟩
  · simpa [alignedTriangle, triangleSigns] using hrel
  · exact FlowOrientations.uniform_signed_family U hU id _ (triangleSigns_abs hε hδ)

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.triangle_signed_relation
#print axioms Unimodular.SignedSums.signed_family_real_matroid
#print axioms Unimodular.SignedSums.triangle_alignment_exists
