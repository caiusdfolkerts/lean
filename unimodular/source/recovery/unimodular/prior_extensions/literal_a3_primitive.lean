module

public import Recovery.Unimodular.NativePort.VerifiedProgress

@[expose] public section

/-!
The primitive one-square example in the literal zero-sum A3 lattice.
The actual equation map is rebuilt in that lattice. Primitivity follows
from the proved fan correspondence and the two-element endpoint interval;
no unproved invariance assertion about boundary matrices is assumed.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric

namespace Unimodular.AllowedBlocks

variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- A nontrivial two-element interval of actual endpoint-cone fans gives
an actual Graver-primitive relation for every generic degree direction. -/
theorem primitive_of_only_endpoint_fans (hι : IsIntegralLattice ι)
    (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (Φ Ψ : FanOnRays ι u) (hne : Ψ ≠ Φ)
    (honly : ∀ Θ : FanOnRays ι u,
      (∀ C ∈ Θ.val.cones, C ∈ Φ.val.cones ∨ C ∈ Ψ.val.cones) → Θ = Φ ∨ Θ = Ψ) :
    Graver.Primitive (equationMap ι u w).ker (indicator ι u Ψ - indicator ι u Φ) := by
  classical
  obtain ⟨G,hG,hpath⟩ := theorem_1_1_all_cones ι u hι hnz hpos hw Φ Ψ
  let R : FanOnRays ι u → FanOnRays ι u → Prop := fun A B =>
    indicator ι u B - indicator ι u A ∈ G ∧
      (∀ C ∈ A.val.cones, C ∈ Φ.val.cones ∨ C ∈ Ψ.val.cones) ∧
      (∀ C ∈ B.val.cones, C ∈ Φ.val.cones ∨ C ∈ Ψ.val.cones)
  have hpath' : Relation.ReflTransGen R Φ Ψ := hpath
  have hcollapse : ∀ {A}, Relation.ReflTransGen R Φ A → A = Φ ∨ R Φ Ψ := by
    intro A h
    induction h with
    | refl => exact Or.inl rfl
    | @tail A B hprev hstep ih =>
      rcases ih with he | hdirect
      · subst A
        rcases honly B hstep.2.2 with hB | hB
        · exact Or.inl hB
        · exact Or.inr (hB ▸ hstep)
      · exact Or.inr hdirect
  exact (hG _).mp ((hcollapse hpath').resolve_left hne).1

end Unimodular.AllowedBlocks

namespace Unimodular.LiteralA3Primitive
open LiteralRootCoordinates LiteralA3Projectivity
open TypeAFanGeometry NormalFanSupport NormalFanCoordinateTransport

abbrev ActualFan := AllowedBlocks.FanOnRays (rootEmbedding 3) (literalRootFamily 3)

/-- The already proved lattice transport, with the equivalent exact ray predicate. -/
def toActualFan (Φ : A3RegularFanCount.CompleteRootFan) : ActualFan :=
  let Ψ := LiteralA3Projectivity.coordinateEquiv Φ
  ⟨Ψ.val,Ψ.property.1,(hasLiteralRays_iff Ψ.val).mp Ψ.property.2⟩

theorem toActualFan_injective : Function.Injective toActualFan := by
  intro Φ Ψ h
  apply LiteralA3Projectivity.coordinateEquiv.injective
  apply Subtype.ext
  simpa only [toActualFan] using congrArg (fun Γ : ActualFan => Γ.val) h

theorem toActualFan_surjective : Function.Surjective toActualFan := by
  intro Θ
  let L : LiteralCompleteRootFan :=
    ⟨Θ.val,Θ.property.1,(hasLiteralRays_iff Θ.val).mpr Θ.property.2⟩
  obtain ⟨Φ,hΦ⟩ := LiteralA3Projectivity.coordinateEquiv.surjective L
  refine ⟨Φ,?_⟩
  apply Subtype.ext
  simpa only [toActualFan,L] using
    congrArg (fun Γ : LiteralCompleteRootFan => Γ.val) hΦ

theorem transported_cone_mem (Φ : A3RegularFanCount.CompleteRootFan)
    (C : PointedCone ℝ (Ambient 3)) :
    C.map (realCoordinateEquiv 3).toLinearMap ∈ (toActualFan Φ).val.cones ↔
      C ∈ Φ.val.cones :=
  (FanTransport.equivalence (Heller.TypeA.coordinateEquiv 3).toAddEquiv
    (realCoordinateEquiv 3) (coordinateCompatibility 3) Φ.val).map_mem C

def seed : ActualFan := toActualFan A3PrimitiveReplacement.seed

def singleSplit (i : Fin 6) (b : Bool) : ActualFan :=
  toActualFan (A3PrimitiveReplacement.singleSplit i b)

theorem singleSplit_ne_seed (i : Fin 6) (b : Bool) : singleSplit i b ≠ seed := by
  intro h
  exact A3PrimitiveReplacement.singleSplit_ne_seed i b (toActualFan_injective h)

theorem only_endpoint_fans (i : Fin 6) (b : Bool) (Θ : ActualFan)
    (huse : ∀ C ∈ Θ.val.cones, C ∈ seed.val.cones ∨ C ∈ (singleSplit i b).val.cones) :
    Θ = seed ∨ Θ = singleSplit i b := by
  obtain ⟨Φ,rfl⟩ := toActualFan_surjective Θ
  have hcoord : ∀ C ∈ Φ.val.cones,
      C ∈ A3PrimitiveReplacement.seed.val.cones ∨
      C ∈ (A3PrimitiveReplacement.singleSplit i b).val.cones := by
    intro C hC
    rcases huse _ ((transported_cone_mem Φ C).mpr hC) with hS | hT
    · exact Or.inl ((transported_cone_mem A3PrimitiveReplacement.seed C).mp hS)
    · exact Or.inr ((transported_cone_mem (A3PrimitiveReplacement.singleSplit i b) C).mp hT)
  rcases A3PrimitiveReplacement.only_endpoint_fans i b Φ hcoord with h | h
  · exact Or.inl (congrArg toActualFan h)
  · exact Or.inr (congrArg toActualFan h)

theorem literal_roots_nonzero (e : Edge 3) :
    rootEmbedding 3 (literalRootFamily 3 e) ≠ 0 := by
  intro h
  have he : realCoordinateEquiv 3 (FanBridge.standardEmbedding 3 (rootFamily 3 e)) = 0 := by
    rw [coordinateCompatibility,coordinate_rootFamily]
    exact h
  exact realRoot_ne_zero e.property ((realCoordinateEquiv 3).map_eq_zero_iff.mp he)

theorem literal_roots_positive_span :
    PointedCone.hull ℝ (Set.range (fun e : Edge 3 =>
      rootEmbedding 3 (literalRootFamily 3 e))) = ⊤ := by
  let C := PointedCone.hull ℝ (Set.range (fun e : Edge 3 =>
    rootEmbedding 3 (literalRootFamily 3 e)))
  have hmap : PointedCone.hull ℝ (Set.range (fun e : Edge 3 =>
      FanBridge.standardEmbedding 3 (rootFamily 3 e))) ≤
      C.comap (realCoordinateEquiv 3).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨e,rfl⟩
    change realCoordinateEquiv 3 (FanBridge.standardEmbedding 3 (rootFamily 3 e)) ∈ C
    rw [coordinateCompatibility,coordinate_rootFamily]
    exact PointedCone.subset_hull ⟨e,rfl⟩
  apply top_unique
  intro y hy
  obtain ⟨x,rfl⟩ := (realCoordinateEquiv 3).surjective y
  exact hmap (by rw [A3PrimitiveReplacement.roots_positive_span]; trivial)

theorem seed_projective : HasIntegralNormalFan seed.val := by
  have h := (literal_normalFan_iff_integral
    (LiteralA3Projectivity.coordinateEquiv A3PrimitiveReplacement.seed)).mp
      ((literalRootFans_normalFan_iff A3PrimitiveReplacement.seed.val).mpr
        A3PrimitiveReplacement.seed_projective)
  exact h

theorem singleSplit_nonprojective (i : Fin 6) (b : Bool) :
    ¬HasPolytopeNormalFan (singleSplit i b).val := by
  intro h
  exact A3PrimitiveReplacement.singleSplit_nonprojective i b
    ((literalRootFans_normalFan_iff (A3PrimitiveReplacement.singleSplit i b).val).mp h)

/-- Every generic direction uses the actual full boundary-and-degree equation map
in the literal integral root lattice, not the coordinate model's equation map. -/
theorem singleSplit_primitive (i : Fin 6) (b : Bool) {w : RootSpace 3}
    (hw : RayHyperplanes.GenericDirection (fun e : Edge 3 =>
      rootEmbedding 3 (literalRootFamily 3 e)) w) :
    Graver.Primitive (AllowedBlocks.equationMap (rootEmbedding 3) (literalRootFamily 3) w).ker
      (AllowedBlocks.indicator (rootEmbedding 3) (literalRootFamily 3) (singleSplit i b) -
        AllowedBlocks.indicator (rootEmbedding 3) (literalRootFamily 3) seed) :=
  AllowedBlocks.primitive_of_only_endpoint_fans (rootEmbedding 3) (literalRootFamily 3)
    (rootEmbedding_isIntegralLattice 3) literal_roots_nonzero literal_roots_positive_span hw
    seed (singleSplit i b) (singleSplit_ne_seed i b) (only_endpoint_fans i b)

/-- The paper's example in its literal zero-sum lattice, including an actual
integral normal polytope for the seed and actual Graver primitivity of the change. -/
theorem one_square_nonprojective_primitive (i : Fin 6) (b : Bool) :
    HasIntegralNormalFan seed.val ∧ ¬HasPolytopeNormalFan (singleSplit i b).val ∧
      ∃ w : RootSpace 3,
        RayHyperplanes.GenericDirection (fun e : Edge 3 =>
          rootEmbedding 3 (literalRootFamily 3 e)) w ∧
        Graver.Primitive (AllowedBlocks.equationMap (rootEmbedding 3) (literalRootFamily 3) w).ker
          (AllowedBlocks.indicator (rootEmbedding 3) (literalRootFamily 3) (singleSplit i b) -
            AllowedBlocks.indicator (rootEmbedding 3) (literalRootFamily 3) seed) := by
  obtain ⟨w,hw⟩ := (RayHyperplanes.genericDirection_dense (fun e : Edge 3 =>
    rootEmbedding 3 (literalRootFamily 3 e))).nonempty
  exact ⟨seed_projective,singleSplit_nonprojective i b,w,hw,singleSplit_primitive i b hw⟩

#print axioms toActualFan_injective
#print axioms toActualFan_surjective
#print axioms only_endpoint_fans
#print axioms literal_roots_positive_span
#print axioms seed_projective
#print axioms singleSplit_nonprojective
#print axioms singleSplit_primitive
#print axioms one_square_nonprojective_primitive

end Unimodular.LiteralA3Primitive
#print axioms Unimodular.AllowedBlocks.primitive_of_only_endpoint_fans
end
#check "UNIMODULAR_LITERAL_A3_PRIMITIVE_EOF_V1"
