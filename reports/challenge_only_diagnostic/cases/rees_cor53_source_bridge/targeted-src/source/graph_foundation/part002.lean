module
public import graph_foundation.part001

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: TauCeti.Algebra.Homology.HomologicalComplex.Basic -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Additional API for homological complexes

This file records additivity of the cycles functor, degreewise recursion for powers of a
complex endomorphism, and the existence of coproducts of complexes, computed degreewise. It also
records the basic properties of the maps
`K.toCycles i j : K.X i ⟶ K.cycles j` induced by the differentials: they kill the cycles in degree
`i`, commute with morphisms of complexes, vanish after a morphism from a complex concentrated in
degree `i`, and are epimorphisms in degrees where the complex is exact. In a degree with no nonzero
differential into it, the identification of the homology with the cycles is natural
(`HomologicalComplex.isoHomologyπ_inv_naturality`). The sequence
`Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of cycles is exact when `j = c.next i`
(`HomologicalComplex.cyclesShortComplex_exact`). For adjacent degrees `i` and `j`, the cycles of a
complex exact in degree `j` fit into a short exact sequence `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Zⱼ ⟶ 0`
(`HomologicalComplex.cyclesShortComplex_shortExact`), which stays short exact when its outer terms
are replaced by isomorphic objects (`HomologicalComplex.cyclesShortComplex_shortExact_of_iso`);
likewise a monomorphism onto the kernel of the differential `Kᵢ ⟶ Kⱼ` gives a short exact sequence
`0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` (`HomologicalComplex.shortExact_toCycles`). Constructing the bundled cycle
sequence requires homology only in the two selected degrees.
The exactness results additionally require homology of the cycle sequence itself.
For chain complexes indexed by the natural numbers, the identification of zero chains with
cycles is natural (`ChainComplex.cycles₀Iso_inv_naturality`), and so is the passage from zero
chains to zeroth homology (`ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap`).
The isomorphisms `homologyIsoSc'`
are natural (`HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom`), and exactness in a degree
is the vanishing of the homology of the short complex `sc'` there
(`HomologicalComplex.exactAt_iff_isZero_homology_sc'`).
Homology of complexes commutes with an additive functor preserving homology
(`CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`), the complex-level form of
Mathlib's `CategoryTheory.ShortComplex.homologyFunctorIso`.
-/

section
open CategoryTheory Limits

universe w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Degreewise recursion for the powers of a chain endomorphism. -/
lemma pow_f_succ (m : ℕ) (i : ι) :
    (End.of s ^ (m + 1)).asHom.f i = (End.of s ^ m).asHom.f i ≫ s.f i := by
  rw [pow_succ', End.mul_asHom, comp_f]

/-- Homological complexes have the coproducts that the underlying category has. They are
computed degreewise. -/
instance hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{w} (HomologicalComplex C c) :=
  fun _ ↦ inferInstance

/-! ### The maps onto the cycles -/

section Cycles

variable (K) {L : HomologicalComplex C c}

/-- The map from the cycles in degree `i` to the cycles in degree `j` induced by the differential
vanishes. -/
@[reassoc]
lemma iCycles_toCycles (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp]

/-- The short complex `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` cut out of a homological complex. Its
second map is the differential with codomain restricted to the cycles in degree `j`. -/
noncomputable def cyclesShortComplex (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j)

/-- The cycle sequence is formed by the inclusion of cycles and the corestricted differential. -/
lemma cyclesShortComplex_def (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.cyclesShortComplex i j =
      ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j) := (rfl)

@[simp]
lemma cyclesShortComplex_X₁ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₁ = K.cycles i := (rfl)

@[simp]
lemma cyclesShortComplex_X₂ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₂ = K.X i := (rfl)

@[simp]
lemma cyclesShortComplex_X₃ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₃ = K.cycles j := (rfl)

/-- The first map of the cycle sequence is the inclusion of cycles, transported along the
object equalities `cyclesShortComplex_X₁` and `cyclesShortComplex_X₂`. -/
@[simp]
lemma cyclesShortComplex_f (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).f = eqToHom (K.cyclesShortComplex_X₁ i j) ≫ K.iCycles i ≫
      eqToHom (K.cyclesShortComplex_X₂ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- The second map of the cycle sequence is the corestricted differential, transported along the
object equalities `cyclesShortComplex_X₂` and `cyclesShortComplex_X₃`. -/
@[simp]
lemma cyclesShortComplex_g (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).g = eqToHom (K.cyclesShortComplex_X₂ i j) ≫ K.toCycles i j ≫
      eqToHom (K.cyclesShortComplex_X₃ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

variable {K}

/-- The maps onto the cycles induced by the differentials commute with morphisms of complexes. -/
@[reassoc]
lemma toCycles_cyclesMap (φ : K ⟶ L) (i j : ι) [K.HasHomology j] [L.HasHomology j] :
    K.toCycles i j ≫ cyclesMap φ j = φ.f i ≫ L.toCycles i j :=
  (cancel_mono (L.iCycles j)).1 <| by simp

/-- In a degree `j` with no nonzero differential into it, the identifications
`K.isoHomologyπ i j` of the homology with the cycles commute with the maps induced by a morphism of
complexes. -/
@[reassoc]
lemma isoHomologyπ_inv_naturality (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i) (hK : K.d i j = 0)
    (hL : L.d i j = 0) [K.HasHomology j] [L.HasHomology j] :
    homologyMap φ j ≫ (L.isoHomologyπ i j hi hL).inv =
      (K.isoHomologyπ i j hi hK).inv ≫ cyclesMap φ j := by
  rw [← cancel_epi (K.isoHomologyπ i j hi hK).hom]
  simp

variable [HasZeroObject C] [DecidableEq ι] {i : ι} {X : C}

/-- A morphism from a complex concentrated in degree `i` vanishes after the differential out of
degree `i`. -/
@[reassoc]
lemma single_f_d (g : (single C c i).obj X ⟶ L) (j : ι) : g.f i ≫ L.d i j = 0 := by
  rw [g.comm i j, single_obj_d, zero_comp]

/-- A morphism from a complex concentrated in degree `i` vanishes after the map onto the cycles in
degree `j`. -/
@[reassoc]
lemma single_f_toCycles (g : (single C c i).obj X ⟶ L) (j : ι) [L.HasHomology j] :
    g.f i ≫ L.toCycles i j = 0 := by
  rw [← cancel_mono (L.iCycles j), Category.assoc, toCycles_i, single_f_d, zero_comp]

end Cycles

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

variable (K) in
/-- The sequence `Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of the cycles of a complex `K` is exact when `j` is the degree
following `i`: the cycles in degree `i` are the kernel of the differential. -/
lemma cyclesShortComplex_exact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [hH : (K.cyclesShortComplex i j).HasHomology] (hij : c.next i = j) :
    (K.cyclesShortComplex i j).Exact := by
  rw [cyclesShortComplex_def] at hH ⊢
  let S := ShortComplex.mk _ _ (K.iCycles_toCycles i j)
  have hS := isKernelOfComp (K.iCycles j) (K.d i j) (K.cyclesIsKernel i j hij)
    (K.iCycles_toCycles i j) (K.toCycles_i i j)
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  have h : hS.lift (KernelFork.ofι S.iCycles S.iCycles_g) ≫ S.f = S.iCycles :=
    Fork.IsLimit.lift_ι _
  rw [← h, Category.assoc, S.f_pOpcycles, comp_zero]

/-- A morphism killed by the differential `Kᵢ ⟶ Kⱼ` is killed by its corestriction to the
cycles in degree `j`. -/
lemma comp_toCycles_eq_zero {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) : a ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, K.toCycles_i, ha, zero_comp]

/-- The corestriction `Kᵢ ⟶ Zⱼ` of the differential has the same kernel as the differential
`Kᵢ ⟶ Kⱼ`: if `A ⟶ Kᵢ ⟶ Kⱼ` is exact, then so is `A ⟶ Kᵢ ⟶ Zⱼ`. -/
lemma exact_toCycles {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha))
    (S₂ := ShortComplex.mk a (K.d i j) ha)
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := K.iCycles j }).2 hex

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- In a complex exact in degree `j`, the map onto the cycles in degree `j` from the preceding
degree is an epimorphism. -/
lemma epi_toCycles_of_exactAt {i j : ι} [K.HasHomology j]
    (h : K.ExactAt j) (hij : c.prev j = i) :
    Epi (K.toCycles i j) := by
  rw [exactAt_iff' _ i j (c.next j) hij rfl] at h
  have := h.hasHomology
  rw [← epi_comp_iff_of_isIso _ (K.cyclesIsoSc' i j (c.next j) hij rfl).hom,
    K.toCycles_cyclesIsoSc'_hom]
  exact h.epi_toCycles

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` is short exact when `i` and `j` are adjacent
and `K` is exact in degree `j`. -/
lemma cyclesShortComplex_shortExact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology]
    (hij : c.Rel i j) (hK : K.ExactAt j) : (K.cyclesShortComplex i j).ShortExact := by
  have hE := K.cyclesShortComplex_exact i j (c.next_eq' hij)
  rw [cyclesShortComplex_def] at hE ⊢
  exact ShortComplex.ShortExact.mk' hE
    inferInstance (epi_toCycles_of_exactAt hK (c.prev_eq' hij))

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)`, with its outer terms replaced along isomorphisms
`X ≅ Zᵢ(K)` and `Zⱼ(K) ≅ Y`, is short exact when `i` and `j` are adjacent and `K` is exact in
degree `j`. -/
lemma cyclesShortComplex_shortExact_of_iso {i j : ι} [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology] (hij : c.Rel i j) (hK : K.ExactAt j) {X Y : C}
    (e : X ≅ K.cycles i) (e' : K.cycles j ≅ Y) :
    (ShortComplex.mk (e.hom ≫ K.iCycles i) (K.toCycles i j ≫ e'.hom)
      (by simp [iCycles_toCycles_assoc])).ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk e.symm (Iso.refl (K.X i)) e') <|
    K.cyclesShortComplex_def i j ▸ K.cyclesShortComplex_shortExact i j hij hK

/-- A monomorphism `A ⟶ Kᵢ` onto the kernel of the differential `Kᵢ ⟶ Kⱼ` fits into a short exact
sequence `0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` when `i` precedes `j` and `K` is exact in degree `j`. -/
lemma shortExact_toCycles {A : C} {i j : ι} [K.HasHomology j] (a : A ⟶ K.X i) [Mono a]
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact)
    (hij : c.prev j = i) (hK : K.ExactAt j) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).ShortExact :=
  have := epi_toCycles_of_exactAt hK hij
  { exact := exact_toCycles j a ha hex }

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- Taking cycles is additive on morphisms of complexes. -/
@[simp]
lemma cyclesMap_add (f g : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i := by
  apply (cancel_mono (L.iCycles i)).1
  simp only [Preadditive.add_comp, cyclesMap_i, add_f_apply, Preadditive.comp_add]

instance cyclesFunctor_additive [CategoryWithHomology C] (i : ι) :
    (cyclesFunctor C c i).Additive where
  map_add := by
    intro X Y f g
    -- `cyclesFunctor` is opaque, so expose its defining map before applying the map-level API.
    change cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i
    exact cyclesMap_add f g i

section HomologyIsoSc'

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L) (i j k : ι)
  (hi : c.prev j = i) (hk : c.next j = k) [K.HasHomology j] [L.HasHomology j]
  [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology]

/-- The isomorphisms `homologyIsoSc'` are natural (this is the naturality of Mathlib's
`homologyFunctorIso'`, for complexes which only individually have homology). -/
@[reassoc]
lemma homologyMap_comp_homologyIsoSc'_hom :
    homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor' C c i j k).map f) := by
  rw [homologyIsoSc', homologyIsoSc', ShortComplex.homologyMapIso_hom,
    ShortComplex.homologyMapIso_hom, homologyMap]
  -- the source of `homologyMap f j` is `K.homology j`, which is `(K.sc j).homology` only up to
  -- unfolding `HomologicalComplex.homology`, so the generic `homologyMap_comp` needs `erw`
  erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (natIsoSc' C c i j k hi hk).hom.naturality f

end HomologyIsoSc'

/-- A homological complex is exact at `j` exactly when the homology of its short complex at `j`,
with explicit neighbouring indices, is zero. -/
lemma exactAt_iff_isZero_homology_sc' {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} (L : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) [(L.sc' i j k).HasHomology] :
    L.ExactAt j ↔ IsZero (L.sc' i j k).homology :=
  (exactAt_iff' L i j k hi hk).trans (ShortComplex.exact_iff_isZero_homology _)

end HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {K L : ChainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- The identification of degree-zero chains with degree-zero cycles is natural. -/
@[reassoc]
lemma cycles₀Iso_inv_naturality (φ : K ⟶ L) :
    K.cycles₀Iso.inv ≫ HomologicalComplex.cyclesMap φ 0 =
      φ.f 0 ≫ L.cycles₀Iso.inv := by
  apply (cancel_mono (L.iCycles 0)).1
  simp

/-- The passage from degree-zero chains to degree-zero homology, through the identification of
the homology with the opcycles, is natural. -/
@[reassoc]
lemma pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap (φ : K ⟶ L) :
    K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ L.pOpcycles 0 ≫ L.isoHomologyι₀.inv := by
  rw [ChainComplex.isoHomologyι₀_inv_naturality, HomologicalComplex.p_opcyclesMap_assoc]

end ChainComplex

namespace HomologicalComplex

section HomologyTransport

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [CategoryWithHomology C]
  {ι : Type*} {c : ComplexShape ι} {L L' M M' : HomologicalComplex C c}

/-- A morphism transported along equalities of complexes induces the corresponding transport
of the homology map. -/
lemma homologyMap_comp_eqToHom (ψ : L ⟶ L') (hM : M = L) (hM' : M' = L')
    (τ : M ⟶ M') (hτ : τ = eqToHom hM ≫ ψ ≫ eqToHom hM'.symm) (q : ι) :
    homologyMap τ q ≫ eqToHom (congrArg (·.homology q) hM') =
      eqToHom (congrArg (·.homology q) hM) ≫ homologyMap ψ q := by
  subst hM hM' hτ
  simp

end HomologyTransport

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [Preadditive C] [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- Homology of homological complexes commutes with a functor preserving homology. -/
noncomputable def mapHomologicalComplexCompHomologyFunctorIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  -- the short complex of `F` applied to `K` in degree `i` is `F` applied to that of `K`
  isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C c i) (ShortComplex.homologyFunctorIso F)

@[simp]
lemma mapHomologicalComplexCompHomologyFunctorIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexCompHomologyFunctorIso c i).hom.app K =
      ((K.sc i).mapHomologyIso F).hom :=
  (rfl)

end CategoryTheory.Functor

end
end

/- BEGIN EXACT BODY: TauCeti.Algebra.Homology.Homotopy -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Constructions on chain homotopies

Four constructions of chain homotopies: two produce new homotopies from old ones, and the
other two assemble a null-homotopy from components given all at once.

`Homotopy.descCokernel` descends a homotopy along a degreewise cokernel.  Let `p : L ⟶ M` exhibit
`M` in each degree as the cokernel of `u : K ⟶ L`, and let `p' : L' ⟶ M'` be any morphism of
complexes.  A chain homotopy between morphisms `L ⟶ L'` whose components send the image of `u`
into the kernel of `p'` then descends to a chain homotopy between the induced morphisms `M ⟶ M'`.
Only the source side is assumed to be a degreewise cokernel; on the target side the hypothesis is
the bare vanishing `u.f i ≫ HL.hom i j ≫ p'.f j = 0`, which is what the universal property needs.
This is the mechanism behind homotopy invariance of relative homology, where `M` is the relative
chain complex of a pair, that is, the degreewise cokernel of the chains of the subspace, and the
vanishing holds because the homotopy restricts to the subspace.

`Homotopy.idPow` iterates a chain homotopy from the identity of `K` to an endomorphism `s`: it
exhibits every power `sᵐ` as homotopic to the identity, through the explicit operator
`∑_{k < m} sᵏ ≫ h`.  Its components are needed, and not just the existence of some homotopy, when
`m` is allowed to vary from one summand of `K` to another, as in the proof that small singular
chains for an open cover include as a chain homotopy equivalence.

`Homotopy.mkChainComplex` builds a null-homotopy of a chain map between `ℕ`-indexed chain
complexes from its components `h n : P.X n ⟶ Q.X (n + 1)`, given all at once together with the
homotopy identities in degree zero and in positive degrees.  It is the non-inductive counterpart of
Mathlib's `Homotopy.mkInductive`, for the situation where the components are constructed by a
recursion of their own rather than one degree at a time from the previous two.

`Homotopy.mkCochainComplexInt` is its counterpart for `ℤ`-indexed cochain complexes: a
null-homotopy of `e : P ⟶ Q` from components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy
identities `e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`, stated in every degree `n + 1` so that no
index is a difference.

`Homotopy.comm_zero_apply` and `Homotopy.comm_succ_apply` are the homotopy identities of a
homotopy between maps of `ℕ`-indexed chain complexes of modules, evaluated on elements.

`CochainComplex.nonempty_homotopy_mkHomToSingle_zero_iff` characterizes null-homotopic chain maps
from a cochain complex `K` to an object `A` placed in degree `i`: the map given by `φ : Kⁱ ⟶ A` is
null-homotopic if and only if `φ` factors through the differential `Kⁱ ⟶ Kⁱ⁺¹`. It is Mathlib's
criterion `CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff`, translated from
coboundaries to homotopies.

`Homotopy.cyclesMap_sub_eq` expresses the difference of the maps on cycles induced by
homotopic maps as a factorization through a term of the target complex. In particular, these
maps agree after passing to a stable category that kills that term.
-/

section
noncomputable section

open CategoryTheory Limits

universe v u

namespace Homotopy

/-- On cycles, the difference of homotopic maps factors through the preceding target term.
This identity does not require exactness of either complex. -/
theorem cyclesMap_sub_eq {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c} {f g : K ⟶ L}
    (h : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.cyclesMap f i - HomologicalComplex.cyclesMap g i =
      K.iCycles i ≫ h.hom i (c.prev i) ≫ L.toCycles (c.prev i) i := by
  apply (cancel_mono (L.iCycles i)).mp
  simp only [Preadditive.sub_comp, HomologicalComplex.cyclesMap_i, Category.assoc,
    HomologicalComplex.toCycles_i]
  rw [h.comm i]
  simp [dNext, prevD, Preadditive.comp_add, ← Category.assoc]

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L M L' M' : HomologicalComplex C c}
  {fL gL : L ⟶ L'} {fM gM : M ⟶ M'}
  (HL : Homotopy fL gL)
  (u : K ⟶ L) (p : L ⟶ M) (p' : L' ⟶ M')
  (hw : ∀ i, u.f i ≫ p.f i = 0)
  (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p.f i) (hw i)))
  (hcomm : ∀ i j, u.f i ≫ HL.hom i j ≫ p'.f j = 0)

include hw hp hcomm

/-- The components of the chain homotopy that `Homotopy.descCokernel` obtains on the quotient
complex `M`. -/
@[no_expose]
def descCokernelHom (i j : ι) : M.X i ⟶ M'.X j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).1

@[reassoc (attr := simp)]
lemma π_descCokernelHom (i j : ι) :
    p.f i ≫ descCokernelHom HL u p p' hw hp hcomm i j = HL.hom i j ≫ p'.f j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).2

private lemma π_comp_dNext (i : ι) :
    p.f i ≫ dNext i (descCokernelHom HL u p p' hw hp hcomm) = dNext i HL.hom ≫ p'.f i := by
  rw [← dNext_comp_left, ← dNext_comp_right]
  exact congrArg (fun F ↦ dNext i F) (by funext a b; exact π_descCokernelHom ..)

private lemma π_comp_prevD (i : ι) :
    p.f i ≫ prevD i (descCokernelHom HL u p p' hw hp hcomm) = prevD i HL.hom ≫ p'.f i := by
  rw [← prevD_comp_left, ← prevD_comp_right]
  exact congrArg (fun F ↦ prevD i F) (by funext a b; exact π_descCokernelHom ..)

/-- A chain homotopy on the total complexes whose components kill the subcomplex after composing
with `p'` descends to a chain homotopy on the quotient complex `M`. -/
@[no_expose]
def descCokernel (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') : Homotopy fM gM where
  hom := descCokernelHom HL u p p' hw hp hcomm
  zero i j hij := Cofork.IsColimit.hom_ext (hp i) (by simp [HL.zero i j hij])
  comm i := Cofork.IsColimit.hom_ext (hp i) (by
    simp only [Cofork.π_ofπ, Preadditive.comp_add, π_comp_dNext, π_comp_prevD,
      ← HomologicalComplex.comp_f p fM, ← HomologicalComplex.comp_f p gM, hf, hg,
      HomologicalComplex.comp_f]
    rw [← Preadditive.add_comp, ← Preadditive.add_comp, ← HL.comm i])

@[simp]
lemma descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') :
    (descCokernel HL u p p' hw hp hcomm hf hg).hom = descCokernelHom HL u p p' hw hp hcomm := (rfl)

@[reassoc]
lemma π_descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') (i j : ι) :
    p.f i ≫ (descCokernel HL u p p' hw hp hcomm hf hg).hom i j = HL.hom i j ≫ p'.f j :=
  π_descCokernelHom HL u p p' hw hp hcomm i j

end Homotopy

section Pow

variable {C : Type u} [Category.{v} C] {ι : Type*} {c : ComplexShape ι}

namespace Homotopy

variable [Preadditive C] {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Iterating a chain homotopy from the identity.  If `h` is a chain homotopy from the identity of
`K` to a chain endomorphism `s`, then `h.idPow m` is a chain homotopy from the identity to the
`m`-th power of `s`, whose operator in bidegree `(i, j)` is `∑_{k < m} (sᵏ)ᵢ ≫ hᵢⱼ`. -/
@[no_expose]
def idPow (h : Homotopy (𝟙 K) s) (m : ℕ) : Homotopy (𝟙 K) (End.of s ^ m).asHom where
  hom i j := ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j
  zero i j hij := by simp [h.zero i j hij]
  comm i := by
    have hdn : dNext i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom := by
      simpa only [Finset.sum_fn, dNext_comp_left] using
        map_sum (dNext i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hpv : prevD i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ prevD i h.hom := by
      simpa only [Finset.sum_fn, prevD_comp_left] using
        map_sum (prevD i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hstep : ∀ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom +
        (End.of s ^ k).asHom.f i ≫ prevD i h.hom =
        (End.of s ^ k).asHom.f i - (End.of s ^ (k + 1)).asHom.f i := fun k _ ↦ by
      have hsum : dNext i h.hom + prevD i h.hom = 𝟙 (K.X i) - s.f i := by
        have hc := h.comm i
        rw [HomologicalComplex.id_f] at hc
        rw [hc]
        abel
      rw [← Preadditive.comp_add, hsum, Preadditive.comp_sub, Category.comp_id,
        HomologicalComplex.pow_f_succ]
    rw [hdn, hpv, ← Finset.sum_add_distrib, Finset.sum_congr rfl hstep,
      Finset.sum_range_sub' (fun k ↦ (End.of s ^ k).asHom.f i) m, pow_zero, End.one_asHom,
      HomologicalComplex.id_f]
    abel

@[simp]
lemma idPow_hom (h : Homotopy (𝟙 K) s) (m : ℕ) (i j : ι) :
    (h.idPow m).hom i j = ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j := (rfl)

end Homotopy

end Pow

section MkChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : ChainComplex C ℕ}

namespace Homotopy

/-- A null-homotopy of a chain map `e : P ⟶ Q` between `ℕ`-indexed chain complexes, from its
components `h n : P.X n ⟶ Q.X (n + 1)` and the homotopy identities `e.f 0 = h 0 ≫ d` and
`e.f (n + 1) = d ≫ h n + h (n + 1) ≫ d`. The components are given all at once; compare
`Homotopy.mkInductive`, which constructs them one degree at a time. -/
@[no_expose]
def mkChainComplex (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1)) (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : i + 1 = j then h i ≫ eqToHom (congrArg Q.X hij) else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.down_Rel] using hij)
  comm i := by
    cases i with
    | zero =>
        rw [dNext_zero_chainComplex, prevD_chainComplex]
        simpa using comm_zero
    | succ i =>
        rw [dNext_succ_chainComplex, prevD_chainComplex]
        simpa using comm_succ i

@[simp]
lemma mkChainComplex_hom_succ (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1))
    (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1))
    (n : ℕ) : (mkChainComplex e h comm_zero comm_succ).hom n (n + 1) = h n := by
  simp [mkChainComplex]

end Homotopy

end MkChainComplex

section MkCochainComplexInt

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : CochainComplex C ℤ}

namespace Homotopy

/-- A null-homotopy of a map `e : P ⟶ Q` between `ℤ`-indexed cochain complexes, from its
components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy identities
`e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`. Every degree is written as `n + 1`, so that no index is
ever a difference. The components are given all at once, as in `Homotopy.mkChainComplex`. -/
@[no_expose]
def mkCochainComplexInt (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : j + 1 = i then eqToHom (congrArg P.X hij.symm) ≫ h j else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.up_Rel] using hij)
  comm i := by
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (ComplexShape.up_mk (n + 1) (n + 1 + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk n (n + 1) rfl)]
    simpa using comm n

@[simp]
lemma mkCochainComplexInt_hom (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1))
    (n : ℤ) : (mkCochainComplexInt e h comm).hom (n + 1) n = h n := by
  simp [mkCochainComplexInt]

end Homotopy

end MkCochainComplexInt

section ModuleCat

variable {R : Type*} [Ring R] {P Q : ChainComplex (ModuleCat R) ℕ} {e e' : P ⟶ Q}

namespace Homotopy

/-- The homotopy identity in degree zero, on elements: the difference of the two maps is the
boundary of the homotopy. -/
theorem comm_zero_apply (h : Homotopy e e') (x : P.X 0) :
    e.f 0 x = Q.d 1 0 (h.hom 0 1 x) + e'.f 0 x := by
  have hc := h.comm 0
  rw [dNext_zero_chainComplex, prevD_chainComplex, zero_add] at hc
  simpa using congrArg (fun φ : P.X 0 ⟶ Q.X 0 ↦ φ x) hc

/-- The homotopy identity in positive degrees, on elements. -/
theorem comm_succ_apply (h : Homotopy e e') (n : ℕ) (x : P.X (n + 1)) :
    e.f (n + 1) x =
      h.hom n (n + 1) (P.d (n + 1) n x) + Q.d (n + 2) (n + 1) (h.hom (n + 1) (n + 2) x) +
        e'.f (n + 1) x := by
  have hc := h.comm (n + 1)
  rw [dNext_succ_chainComplex, prevD_chainComplex] at hc
  simpa [add_assoc] using congrArg (fun φ : P.X (n + 1) ⟶ Q.X (n + 1) ↦ φ x) hc

end Homotopy

end ModuleCat

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

open HomComplex in
/-- **Null-homotopic chain maps to an object in one degree**: the chain map from `K` to `A`
placed in degree `i` given by `φ : Kⁱ ⟶ A` is null-homotopic if and only if `φ` factors through
the differential `Kⁱ ⟶ Kʲ`, where `j = i + 1`. -/
lemma nonempty_homotopy_mkHomToSingle_zero_iff (K : CochainComplex C ℤ) {i j : ℤ}
    (hij : i + 1 = j) {A : C} (φ : K.X i ⟶ A)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel k i → K.d k i ≫ φ = 0) :
    Nonempty (Homotopy (HomologicalComplex.mkHomToSingle φ hφ) 0) ↔
      ∃ g : K.X j ⟶ A, K.d i j ≫ g = φ := by
  have hφ' : K.d (i - 1) i ≫ φ = 0 := hφ _ (by simp)
  rw [← Cocycle.toSingleMk_mem_coboundaries_iff φ (add_zero i) (i - 1) (by lia) hφ' j hij,
    mem_coboundaries_iff _ (-1) (by simp)]
  -- The cocycle of `Cocycle.toSingleMk` is the zero-cochain of the chain map.
  have h : (Cocycle.toSingleMk φ (add_zero i) (i - 1) (by lia) hφ' : Cochain _ _ 0) =
      Cochain.ofHom (HomologicalComplex.mkHomToSingle φ hφ) :=
    (Cochain.toSingleEquiv (add_zero i)).injective (by
      simp [Cochain.toSingleEquiv, HomologicalComplex.mkHomToSingle_f])
  rw [h]
  exact ⟨fun ⟨ho⟩ ↦ ⟨Cochain.ofHomotopy ho, by simp [δ_ofHomotopy]⟩,
    fun ⟨z, hz⟩ ↦ ⟨(Cochain.equivHomotopy _ _).symm ⟨z, by simpa using hz.symm⟩⟩⟩

end CochainComplex

end
end
end

/- BEGIN EXACT BODY: TauCeti.Algebra.Homology.Linear -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Homology commutes with scalar multiplication of chain maps

For a linear category `C`, the map induced on homology by a chain map is linear in the chain
map: `homologyMap (a • φ) i = a • homologyMap φ i`. This is the homological-complex version of
Mathlib's `ShortComplex.homologyMap_smul`, recorded as a TODO in
`Mathlib/Algebra/Homology/Linear.lean`. It identifies, for instance, the map induced by
multiplication by a scalar on a complex of modules with multiplication by that scalar on
homology, and it makes the homology functor in each degree a linear functor.
-/

section
open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} {c : ComplexShape ι}

/-- The short complex attached to a degree sends a scalar multiple of a chain map to the scalar
multiple of the induced morphism of short complexes. -/
@[simp]
lemma shortComplexFunctor_map_smul (i : ι) (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (shortComplexFunctor C c i).map (a • φ) = a • (shortComplexFunctor C c i).map φ := by
  -- Each component is `smul_f_apply`, stated for the `SMul` instance of the complexes.
  ext <;> exact smul_f_apply _ _ _

/-- The map induced on homology by a scalar multiple of a chain map is the scalar multiple of the
induced map. -/
@[simp]
lemma homologyMap_smul (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    homologyMap (a • φ) i = a • homologyMap φ i := by
  rw [homologyMap, shortComplexFunctor_map_smul]
  exact ShortComplex.homologyMap_smul _ _

/-- Taking homology in a fixed degree is a linear functor. -/
instance [CategoryWithHomology C] (i : ι) : (homologyFunctor C c i).Linear R where
  map_smul φ a := homologyMap_smul a φ i

end HomologicalComplex

end
end

/- BEGIN EXACT BODY: TauCeti.LinearAlgebra.CliffordAlgebra.Grading -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Reading the `ℤ/2`-grading: base cases, exterior bases, and ordered products

An induction over the `ℤ/2`-grading of a Clifford algebra — Mathlib's
`CliffordAlgebra.evenOdd_induction` — hands its base case back as membership in a power of
`LinearMap.range (ι Q)` whose exponent is a `ZMod.val`. Since `(0 : ZMod 2).val` is `0` and
`(1 : ZMod 2).val` is `1`, that membership says "a scalar" in the even case and "a vector" in the
odd one. Reading it that way is bookkeeping that every such induction repeats, so it is recorded
here once and shared.

In the other direction, the ordered product `(l.map (ι Q)).prod` of a list of vectors — the
spelling `TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Basic.lean` uses for the volume
element — is homogeneous of degree `l.length`, which is Mathlib's
`SetLike.list_prod_map_mem_graded` for the graded monoid `CliffordAlgebra.evenOdd Q` with the
degree of each factor read off `CliffordAlgebra.ι_mem_evenOdd_one`. Reading it off by the parity of
the length is what matters downstream.

The grade involution acts on the graded piece of parity `p` by the sign `(-1) ^ p`, combining
Mathlib's `CliffordAlgebra.involute_eq_of_mem_even` and `CliffordAlgebra.involute_eq_of_mem_odd`
into one statement indexed by the parity. Once `2` is invertible, the two graded pieces are the
eigenspaces of the grade involution: the even part is its fixed space and the odd part its
`-1`-eigenspace. Mathlib proves one implication of each (the two lemmas above) and leaves the
converses as a TODO; they are recorded here. This is the form in which the grading is
transported along maps commuting with the involution, such as extension of scalars.

The coordinate basis of an exterior algebra is homogeneous for this grading: the basis vector
indexed by `s` has degree `s.card`, and — over a nontrivial ring, where a basis vector is nonzero
and the two graded pieces meet only in `0` — that degree is the *only* one it has. This statement
belongs to the grading API independently of any spin representation.

## Main results

* `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero`: in the even base case the
  element is a scalar.
* `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`: in the odd base case it is a vector.
* `CliffordAlgebra.ι_range_pow_le_evenOdd`: the `n`-th power of the range of `ι` lies in the
  graded piece of degree `n`.
* `CliffordAlgebra.prod_map_ι_mem_evenOdd`: an ordered product of `n` generators is homogeneous
  of degree `n`, and `CliffordAlgebra.prod_map_ι_mem_evenOdd_zero_of_even_length` and
  `CliffordAlgebra.prod_map_ι_mem_evenOdd_one_of_odd_length` read that off in the even and the odd
  case.
* `CliffordAlgebra.involute_eq_uzpow_smul_of_mem_evenOdd`: the grade involution acts on the graded
  piece of parity `p` by `(-1) ^ p`.
* `CliffordAlgebra.involute_eq_self_iff` and `CliffordAlgebra.involute_eq_neg_iff`: with `2`
  invertible, the even and odd parts are the `±1`-eigenspaces of the grade involution.
* `Module.Basis.exteriorAlgebra_mem_evenOdd_card`: an exterior coordinate-basis vector is
  homogeneous of degree given by the cardinality of its index set, and
  `Module.Basis.exteriorAlgebra_mem_evenOdd_iff` says that this is the only degree it has.
* `Module.Basis.mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero`: an exterior element is
  homogeneous of a given parity exactly when its coordinates vanish at every index set of the
  other parity.
-/



universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- An element of the `(0 : ZMod 2).val`-th power of the range of `ι` is a scalar. This is the
`i = 0` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_algebraMap_of_mem_range_ι_pow_zero {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (0 : ZMod 2).val) :
    ∃ r : R, algebraMap R (CliffordAlgebra Q) r = v :=
  Submodule.mem_one.mp (by simpa using hv)

/-- An element of the `(1 : ZMod 2).val`-th power of the range of `ι` is a vector. This is the
`i = 1` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_ι_of_mem_range_ι_pow_one {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (1 : ZMod 2).val) : ∃ a, ι Q a = v := by
  simpa [ZMod.val_one] using hv

/-- **The `n`-th power of the vectors is homogeneous of degree `n`** for the `ℤ/2` grading: it is
one of the summands defining `CliffordAlgebra.evenOdd Q n`. -/
theorem ι_range_pow_le_evenOdd (n : ℕ) :
    LinearMap.range (ι Q) ^ n ≤ evenOdd Q (n : ZMod 2) := by
  rw [evenOdd]
  exact le_iSup (fun j : {m : ℕ // (m : ZMod 2) = (n : ZMod 2)} => LinearMap.range (ι Q) ^ (j : ℕ))
    ⟨n, rfl⟩

/-- **An ordered product of `n` generators is homogeneous of degree `n`** for the `ℤ/2` grading. -/
theorem prod_map_ι_mem_evenOdd (l : List M) :
    (l.map (ι Q)).prod ∈ evenOdd Q (l.length : ZMod 2) := by
  simpa using SetLike.list_prod_map_mem_graded (A := evenOdd Q) l (fun _ => (1 : ZMod 2)) (ι Q)
    fun j _ => ι_mem_evenOdd_one Q j

/-- **The ordered product of an even number of vectors is even.** -/
theorem prod_map_ι_mem_evenOdd_zero_of_even_length {l : List M} (hlen : Even l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 0 := by
  have h : (l.length : ZMod 2) = 0 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.even_iff.mp hlen, Nat.cast_zero]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-- **The ordered product of an odd number of vectors is odd.** -/
theorem prod_map_ι_mem_evenOdd_one_of_odd_length {l : List M} (hlen : Odd l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 1 := by
  have h : (l.length : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.odd_iff.mp hlen, Nat.cast_one]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-! ### The graded pieces as eigenspaces of the grade involution -/

section Involute

/-- Every Clifford element is the sum of an even and an odd element. -/
private theorem exists_add_eq (x : CliffordAlgebra Q) :
    ∃ e ∈ evenOdd Q 0, ∃ o ∈ evenOdd Q 1, e + o = x :=
  Submodule.mem_sup.mp ((evenOdd_isCompl Q).sup_eq_top ▸ Submodule.mem_top)

/-- **The grade involution acts on the graded piece of parity `p` by the sign `(-1) ^ p`.** -/
theorem involute_eq_uzpow_smul_of_mem_evenOdd {p : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q p) : involute x = ((-1 : ℤˣ) ^ p) • x := by
  obtain rfl | rfl : p = 0 ∨ p = 1 := by clear hx; revert p; decide
  · rw [involute_eq_of_mem_even hx, uzpow_zero, one_smul]
  · rw [involute_eq_of_mem_odd hx, uzpow_one, Units.neg_smul, one_smul]

variable [Invertible (2 : R)]

/-- **The even part is the fixed space of the grade involution** once `2` is invertible. Mathlib's
`CliffordAlgebra.involute_eq_of_mem_even` is the reverse implication. -/
theorem involute_eq_self_iff {x : CliffordAlgebra Q} : involute x = x ↔ x ∈ evenOdd Q 0 := by
  refine ⟨fun hx => ?_, involute_eq_of_mem_even⟩
  obtain ⟨e, he, o, ho, rfl⟩ := exists_add_eq x
  rw [map_add, involute_eq_of_mem_even he, involute_eq_of_mem_odd ho] at hx
  have h2 : (2 : R) • o = 0 := by linear_combination (norm := module) -hx
  simpa [(isUnit_of_invertible (2 : R)).smul_eq_zero.mp h2] using he

/-- **The odd part is the `-1`-eigenspace of the grade involution** once `2` is invertible.
Mathlib's `CliffordAlgebra.involute_eq_of_mem_odd` is the reverse implication. -/
theorem involute_eq_neg_iff {x : CliffordAlgebra Q} : involute x = -x ↔ x ∈ evenOdd Q 1 := by
  refine ⟨fun hx => ?_, involute_eq_of_mem_odd⟩
  obtain ⟨e, he, o, ho, rfl⟩ := exists_add_eq x
  rw [map_add, involute_eq_of_mem_even he, involute_eq_of_mem_odd ho] at hx
  have h2 : (2 : R) • e = 0 := by linear_combination (norm := module) hx
  simpa [(isUnit_of_invertible (2 : R)).smul_eq_zero.mp h2] using ho

end Involute

end CliffordAlgebra

namespace Module.Basis

variable {R : Type u} {M : Type v} {I : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I]

/-- **An exterior coordinate-basis vector is homogeneous of degree its number of coordinates.** -/
@[simp] theorem exteriorAlgebra_mem_evenOdd_card (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (s.card : ZMod 2) := by
  rw [CliffordAlgebra.evenOdd]
  refine Submodule.mem_iSup_of_mem ⟨s.card, rfl⟩ ?_
  have h := (b.exteriorPower s.card
    (⟨s, rfl⟩ : Set.powersetCard I s.card)).2
  rw [← ExteriorAlgebra.basis_eq_coe_basis] at h
  exact h

/-- **An exterior coordinate-basis vector is homogeneous of exactly one degree**: it lies in the
graded piece `i` precisely when `i` is the parity of its number of coordinates. -/
@[simp]
theorem exteriorAlgebra_mem_evenOdd_iff [Nontrivial R] (b : Module.Basis I R M) (s : Finset I)
    (i : ZMod 2) :
    b.ExteriorAlgebra s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i ↔
      (s.card : ZMod 2) = i := by
  refine ⟨fun hmem => ?_, fun h => h ▸ b.exteriorAlgebra_mem_evenOdd_card s⟩
  by_contra hne
  have hcard := b.exteriorAlgebra_mem_evenOdd_card s
  have hpair : ∀ c d : ZMod 2, c ≠ d → (c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0) := by decide
  have hsplit := hpair _ _ hne
  have hbot : b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 0 ⊓
        CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 1 := by
    rcases hsplit with ⟨hc, hi⟩ | ⟨hc, hi⟩
    · exact ⟨hc ▸ hcard, hi ▸ hmem⟩
    · exact ⟨hi ▸ hmem, hc ▸ hcard⟩
  rw [(CliffordAlgebra.evenOdd_isCompl (Q := (0 : QuadraticForm R M))).inf_eq_bot,
    Submodule.mem_bot] at hbot
  exact b.ExteriorAlgebra.ne_zero s hbot

/-- **An exterior element is homogeneous of parity `i` exactly when it has no coordinates of the
other parity**: its coordinate in the exterior coordinate basis vanishes at every index set whose
cardinality has the other parity. -/
theorem mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero (b : Module.Basis I R M) {i : ZMod 2}
    {x : _root_.ExteriorAlgebra R M} :
    x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i ↔
      ∀ t : Finset I, (t.card : ZMod 2) ≠ i → b.ExteriorAlgebra.repr x t = 0 := by
  classical
  have hsupp : ∀ (j : ZMod 2) (y : _root_.ExteriorAlgebra R M),
      (∀ t : Finset I, (t.card : ZMod 2) ≠ j → b.ExteriorAlgebra.repr y t = 0) →
        y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) j := by
    intro j y hy
    rw [← b.ExteriorAlgebra.linearCombination_repr y, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun s hs ↦ Submodule.smul_mem _ _ ?_
    have hs' : (s.card : ZMod 2) = j := by_contra fun h ↦ Finsupp.mem_support_iff.1 hs (hy s h)
    exact hs' ▸ b.exteriorAlgebra_mem_evenOdd_card s
  refine ⟨fun hx t ht ↦ ?_, hsupp i x⟩
  -- `y` is the part of `x` of the parity opposite to `i`; it is homogeneous of both parities.
  let y := b.ExteriorAlgebra.repr.symm
    ((b.ExteriorAlgebra.repr x).filter fun s ↦ (s.card : ZMod 2) ≠ i)
  have hrepr (s : Finset I) : b.ExteriorAlgebra.repr y s =
      if (s.card : ZMod 2) ≠ i then b.ExteriorAlgebra.repr x s else 0 := by
    simp only [y, LinearEquiv.apply_symm_apply, Finsupp.filter_apply]
  have hflip : ∀ c d : ZMod 2, c ≠ d + 1 → c = d := by decide
  have hy₁ : y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (i + 1) :=
    hsupp _ y fun s hs ↦ by rw [hrepr, ite_eq_right (not_not.2 (hflip _ _ hs))]
  have hy₀ : y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i := by
    have hrest : x - y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i :=
      hsupp i _ fun s hs ↦ by rw [map_sub, Finsupp.sub_apply, hrepr, ite_eq_left hs, sub_self]
    simpa using Submodule.sub_mem _ hx hrest
  have hdisj : Disjoint (CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i)
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (i + 1)) := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · exact (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm R M)).disjoint
    · exact (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm R M)).disjoint.symm
  have hy : y = 0 := (Submodule.disjoint_def.1 hdisj) y hy₀ hy₁
  have hcoord := hrepr t
  rw [hy, ite_eq_left ht, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  exact hcoord.symm

end Module.Basis

end

/- BEGIN EXACT BODY: TauCeti.LinearAlgebra.CliffordAlgebra.Contraction -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Private: `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
-- `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one` are used only inside a proof.

/-!
# Contraction against the `ℤ/2`-grading, and the change of form on right factors

Mathlib's `CliffordAlgebra.contractLeft` lowers the degree of a multivector by one, so it
exchanges the two halves of the `ℤ/2`-grading. Mathlib records neither half of that sentence:
`involute` interacts with products (`involute` is an algebra homomorphism) and with the grading,
but never with a contraction, and `evenOdd` is never related to `contractLeft` at all.

This file proves both. That a contraction carries `evenOdd Q i` into `evenOdd Q (i + 1)` is the
grading statement itself, and it is what makes an annihilation operator odd; anticommutation with
the grade involution is its operator shadow, and is what makes the grade involution usable as an
*even* operator alongside exterior multiplication and contraction — for instance because an
anisotropic vector orthogonal to a polarization acts on a spinor module by its scalar coordinate
times the grade involution. More precisely, contraction is a derivation twisted by the grade
involution, `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`, the graded Leibniz rule of an odd
operator.

The degree bookkeeping is in `ZMod 2`, where lowering and raising the degree by one are the same
map, so `evenOdd Q (i + 1)` and `evenOdd Q (i - 1)` are the same submodule; the statement below
names the first.

The parity statement is proved by induction over the grading; its base case is read off by
`CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
`CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`, which are general facts about the
grading and live with it.

Mathlib's `CliffordAlgebra.changeForm` is built by folding from the left, so Mathlib describes
it on left factors only (`CliffordAlgebra.changeForm_ι_mul`). The second half of this file supplies
the right-handed description `CliffordAlgebra.changeForm_mul_ι`, which rests on the graded
Leibniz rules for a contraction meeting a vector factor on the far side and on the commutation of
left with right contraction, left as a `TODO` in Mathlib. From it, `changeForm` commutes with
reversion when the bilinear form is symmetric; and since contraction anticommutes with the grade
involution, `changeForm` commutes with the grade involution for every bilinear form. In particular
`CliffordAlgebra.equivExterior` intertwines both operations with those of the exterior algebra.

## Main results

* `CliffordAlgebra.contractLeft_map`: contraction is natural under quadratic isometries.

* `CliffordAlgebra.contractLeft_mem_evenOdd`: **contraction shifts the parity**.
* `CliffordAlgebra.involute_contractLeft`: `involute (d ⌋ x) = -(d ⌋ involute x)`.
* `CliffordAlgebra.contractLeft_mul`: the graded Leibniz rule
  `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.
* `CliffordAlgebra.contractLeft_mul_ι` and `CliffordAlgebra.contractRight_ι_mul`: the graded
  Leibniz rules for a vector factor on the far side.
* `CliffordAlgebra.contractRight_contractLeft`: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`.
* `CliffordAlgebra.contractLeft_prod_map_ι_eq_zero`: a contraction kills a product of vectors in
  its kernel.
* `CliffordAlgebra.changeForm_mul_ι`: `changeForm` on a right vector factor.
* `CliffordAlgebra.changeForm_involute` and `CliffordAlgebra.changeForm_reverse`: `changeForm`
  commutes with the grade involution, and with reversion for a symmetric form.
* `CliffordAlgebra.equivExterior_involute` and `CliffordAlgebra.equivExterior_reverse`: the same
  for the isomorphism with the exterior algebra.
* `CliffordAlgebra.equivExterior_mem_evenOdd_iff`: that isomorphism preserves the `ℤ/2`-grading.
* `CliffordAlgebra.equivExterior_ι_mul` and `CliffordAlgebra.equivExterior_mul_ι`: that
  isomorphism on left and right vector factors.
* `CliffordAlgebra.equivExterior_prod_map_ι_of_pairwise_isOrtho`: that isomorphism sends a product
  of pairwise orthogonal vectors to their exterior product.

## References

* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators themselves.
-/



universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

section Naturality

variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Contraction against a linear functional commutes with the algebra map induced by a
quadratic isometry, after pulling back the functional. -/
theorem contractLeft_map (f : Q₁ →qᵢ Q₂) (d : Module.Dual R M₂)
    (x : CliffordAlgebra Q₁) :
    contractLeft d (map f x) = map f (contractLeft (d ∘ₗ f.toLinearMap) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes, contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [map_mul, map_apply_ι, contractLeft_ι_mul, hx, map_sub,
      map_smul, LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap]

end Naturality

/-- **The grade involution anticommutes with contraction.** Contracting against a linear
functional lowers the degree by one, hence swaps the even and odd parts of the Clifford algebra,
so it anticommutes with the operator that is `+1` on the even part and `-1` on the odd part. -/
@[simp, grind =]
theorem involute_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    involute (contractLeft d x) = -contractLeft d (involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x a hx =>
    have hlhs : involute (contractLeft d (ι Q a * x))
        = d a • involute x - ι Q a * contractLeft d (involute x) := by
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι, hx, neg_mul_neg]
    have hrhs : involute (ι Q a * x) = -(ι Q a * involute x) := by
      rw [map_mul, involute_ι, neg_mul]
    rw [hlhs, hrhs, map_neg, neg_neg, contractLeft_ι_mul]

/-- **Contraction shifts the parity.** Contracting against a linear functional lowers the degree
of a multivector by one, so it carries the `i`-th half of the `ℤ/2`-grading into the other one. -/
theorem contractLeft_mem_evenOdd (d : Module.Dual R M) {i : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q i) : contractLeft d x ∈ evenOdd Q (i + 1) := by
  -- Two parity facts, used to keep the indices in `ZMod 2` honest.
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  have hshift : ∀ c : ZMod 2, (1 : ZMod 2) + (c + 1) = c := by decide
  induction x, hx using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    -- `i.val` is `0` or `1`, so `v` is a scalar or a vector.
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · obtain ⟨r, rfl⟩ := exists_algebraMap_of_mem_range_ι_pow_zero hv
      simp
    · obtain ⟨a, rfl⟩ := exists_ι_of_mem_range_ι_pow_one hv
      rw [contractLeft_ι, hone]
      exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h₂ : ι Q m₂ * x ∈ evenOdd Q (i + 1) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) hx
    have h₁ : contractLeft d (ι Q m₂ * x) ∈ evenOdd Q i := by
      rw [contractLeft_ι_mul]
      refine sub_mem (Submodule.smul_mem _ _ hx) ?_
      simpa only [hshift] using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) ih
    rw [mul_assoc, contractLeft_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ h₂) ?_
    rw [add_comm]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₁) h₁

/-- **The graded Leibniz rule for contraction.** Contraction against `d` is a derivation twisted
by the grade involution: `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.  On a homogeneous
multivector `x` of degree `n` the involution is the sign `(-1) ^ n`, which gives the familiar
odd-derivation rule. -/
theorem contractLeft_mul (d : Module.Dual R M) (x y : CliffordAlgebra Q) :
    contractLeft d (x * y) = contractLeft d x * y + involute x * contractLeft d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, zero_mul, zero_add,
      AlgHom.commutes]
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']; abel
  | ι_mul x a hx =>
    rw [mul_assoc, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_mul, involute_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, neg_mul, mul_assoc]
    abel

/-- **The graded Leibniz rule for a right vector factor.** Contraction against `d` passes through
a right factor `ι Q m`, at the cost of the term `d m • involute x` produced by contracting that
factor itself after it has moved past `x`. -/
theorem contractLeft_mul_ι (d : Module.Dual R M) (x : CliffordAlgebra Q) (m : M) :
    contractLeft d (x * ι Q m) = contractLeft d x * ι Q m + d m • involute x := by
  rw [contractLeft_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]

/-- **The graded Leibniz rule for right contraction and a left vector factor**, the mirror image of
`CliffordAlgebra.contractLeft_mul_ι` under reversion: `(ι Q a * x) ⌊ d` is
`ι Q a * (x ⌊ d) + d a • involute x`. -/
theorem contractRight_ι_mul (d : Module.Dual R M) (a : M) (x : CliffordAlgebra Q) :
    contractRight (ι Q a * x) d = ι Q a * contractRight x d + d a • involute x := by
  simp [contractRight_eq, contractLeft_mul_ι, reverse_involute_commute.eq]

/-- **Left and right contraction commute**: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`. This is the statement
left as a `TODO` after `CliffordAlgebra.contractRight_comm` in Mathlib. -/
theorem contractRight_contractLeft (d d' : Module.Dual R M) (x : CliffordAlgebra Q) :
    contractRight (contractLeft d x) d' = contractLeft d (contractRight x d') := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | ι_mul x a hx =>
    simp [contractLeft_ι_mul, contractRight_ι_mul, hx, involute_contractLeft]
    abel

/-- Contraction against a functional `d` kills a product of vectors that `d` annihilates. -/
theorem contractLeft_prod_map_ι_eq_zero (d : Module.Dual R M) {l : List M}
    (h : ∀ m ∈ l, d m = 0) : contractLeft d (l.map (ι Q)).prod = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, h a List.mem_cons_self, zero_smul,
      ih fun m hm ↦ h m (List.mem_cons_of_mem a hm), mul_zero, sub_zero]

section changeForm

variable {Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M}
  (h : B.toQuadraticMap = Q' - Q)

/-- **`changeForm` and a right vector factor**: the right-handed counterpart of Mathlib's
`CliffordAlgebra.changeForm_ι_mul`, in which the correction term contracts from the right against
the functional `B.flip m = B · m`. No symmetry of `B` is needed. -/
theorem changeForm_mul_ι (x : CliffordAlgebra Q) (m : M) :
    changeForm h (x * ι Q m) =
      changeForm h x * ι Q' m - contractRight (changeForm h x) (B.flip m) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.commutes, changeForm_ι_mul, changeForm_algebraMap, contractLeft_algebraMap,
      contractRight_algebraMap, sub_zero, sub_zero, Algebra.commutes]
  | add x y hx hy =>
    simp only [add_mul, map_add, hx, hy, LinearMap.add_apply]
    abel
  | ι_mul x a hx =>
    simp [mul_assoc, changeForm_ι_mul, hx, contractLeft_mul_ι, contractRight_contractLeft,
      contractRight_ι_mul, mul_sub, sub_mul]
    abel

/-- **`changeForm` commutes with the grade involution**, for every bilinear form `B`. -/
@[simp]
theorem changeForm_involute (x : CliffordAlgebra Q) :
    changeForm h (involute x) = involute (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_ι_mul, hx, involute_contractLeft]
    abel

/-- **`changeForm` commutes with reversion** when the bilinear form `B` is symmetric. This covers
`CliffordAlgebra.equivExterior`, whose bilinear form is the symmetric
`QuadraticMap.associated (-Q)`. -/
theorem changeForm_reverse (hB : B.IsSymm) (x : CliffordAlgebra Q) :
    changeForm h (reverse x) = reverse (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    have hflip : B.flip=B := by
      ext x y
      exact hB.eq y x
    simp [changeForm_mul_ι,hx,changeForm_ι_mul,contractRight_eq,hflip]

end changeForm

section equivExterior

variable [Invertible (2 : R)] (Q)

/-- `CliffordAlgebra.equivExterior` on a left vector factor: the specialization of Mathlib's
`CliffordAlgebra.changeForm_ι_mul` to the bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_ι_mul (m : M) (x : CliffordAlgebra Q) :
    equivExterior Q (ι Q m * x) =
      ExteriorAlgebra.ι R m * equivExterior Q x -
        contractLeft (QuadraticMap.associated (-Q) m) (equivExterior Q x) :=
  changeForm_ι_mul changeForm.associated_neg_proof m x

/-- `CliffordAlgebra.equivExterior` on a right vector factor: the specialization of
`CliffordAlgebra.changeForm_mul_ι` to the symmetric bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_mul_ι (x : CliffordAlgebra Q) (m : M) :
    equivExterior Q (x * ι Q m) =
      equivExterior Q x * ExteriorAlgebra.ι R m -
        contractRight (equivExterior Q x) (QuadraticMap.associated (-Q) m) := by
  rw [← QuadraticMap.associated_flip]
  exact changeForm_mul_ι changeForm.associated_neg_proof x m

/-- `CliffordAlgebra.equivExterior` intertwines the grade involutions.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, where `CliffordAlgebra.changeForm_involute` applies. -/
theorem equivExterior_involute (x : CliffordAlgebra Q) :
    equivExterior Q (involute x) = involute (equivExterior Q x) :=
  changeForm_involute changeForm.associated_neg_proof x

/-- **`CliffordAlgebra.equivExterior` preserves the `ℤ/2`-grading**: a Clifford element has
parity `i` exactly when its image in the exterior algebra has parity `i`. -/
theorem equivExterior_mem_evenOdd_iff {i : ZMod 2} {x : CliffordAlgebra Q} :
    equivExterior Q x ∈ evenOdd (0 : QuadraticForm R M) i ↔ x ∈ evenOdd Q i := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by revert i; decide
  · rw [← involute_eq_self_iff, ← involute_eq_self_iff, ← equivExterior_involute,
      (equivExterior Q).injective.eq_iff]
  · rw [← involute_eq_neg_iff, ← involute_eq_neg_iff, ← equivExterior_involute, ← map_neg,
      (equivExterior Q).injective.eq_iff]

/-- `CliffordAlgebra.equivExterior` intertwines reversion, because the bilinear form
`QuadraticMap.associated (-Q)` it changes the form by is symmetric.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_reverse (x : CliffordAlgebra Q) :
    equivExterior Q (reverse x) = reverse (equivExterior Q x) :=
  changeForm_reverse changeForm.associated_neg_proof ⟨(QuadraticForm.associated_isSymm R (-Q)).eq⟩ x

/-- **`CliffordAlgebra.equivExterior` sends a product of pairwise orthogonal vectors to their
exterior product.** Each correction term of `CliffordAlgebra.equivExterior_ι_mul` contracts the
later factors against the first, and vanishes by orthogonality. No hypothesis on `Q` is needed;
in particular `Q` may be degenerate. -/
theorem equivExterior_prod_map_ι_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    equivExterior Q (l.map (ι Q)).prod = (l.map (ExteriorAlgebra.ι R)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, equivExterior_ι_mul, ih hl.2,
      contractLeft_prod_map_ι_eq_zero, sub_zero, List.map_cons, List.prod_cons]
    intro m hm
    simp [hl.1 m hm]

end equivExterior

end CliffordAlgebra

end

/- BEGIN EXACT BODY: TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coordinate projections on an exterior algebra

Left multiplication by a basis vector after contraction by its dual coordinate is the projection
onto the exterior basis vectors containing that coordinate. This is the occupation-number
projection used by both scalar detection in Clifford algebras and the matrix-unit construction
from creation and annihilation operators.

Each of the two halves acts on an exterior basis vector by a single coordinate move, up to the
shuffle sign that carries the moved coordinate to the front: contraction erases the coordinate
from the index set, and left multiplication inserts it, each vanishing when the index set is on
the wrong side of that move. Creation after contraction at distinct coordinates therefore
replaces an occupied coordinate with an unoccupied one, with the product of their shuffle signs.

The grade involution is diagonal for the exterior basis as well: it multiplies an exterior
monomial, and so the basis vector indexed by `s`, by the parity of its degree.

Every basis vector is the product of the exterior-algebra generators of its index set, in
increasing order; for index sets with one or two elements this is also recorded in the explicit
forms `TauCeti.ExteriorAlgebra.basis_singleton` and `TauCeti.ExteriorAlgebra.basis_pair`.

Independently of a basis, `ExteriorAlgebra.contractLeft_map` states naturality under a linear
map: pull back the contracting functional and then map the contracted element. This follows
from the general quadratic-isometry statement `CliffordAlgebra.contractLeft_map`.

Independently of a basis, the grade involution is the sign `(-1) ^ n` on the `n`-th exterior power,
a contraction carries the `(n + 1)`-th exterior power into the `n`-th, and a vector graded-commutes
with every multivector: `ι m * x = involute x * ι m`.  Together with the graded Leibniz rule
`CliffordAlgebra.contractLeft_mul`, these say that a contraction is an odd derivation of degree
`-1` of the graded-commutative exterior algebra. On a wedge product of vectors it is the alternating
sum of deletions (`TauCeti.ExteriorAlgebra.contractLeft_ιMulti`); this is the differential of the
Koszul complex.

In degree at least the rank, contraction loses no information: if `d m = 1` and
`finrank R M ≤ n`, every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. Hence two forms killed by `d` multiply to
zero once their degrees add up to the rank, and in rank at most four a two-form `x` satisfies
`x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. This is the algebra behind the splitting of a two-form on a product
`ℝ × Y` along the unit normal of the factor `Y`.

On `M × R`, with `e = (0, 1)`, every element `z` of the exterior algebra splits as `a + e ∧ b`,
where `a` and `b` are the images in `⋀ M` of `z` and of its contraction by the second coordinate
(`ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`). This is the
decomposition `⋀ᵏ⁺¹ (M × R) ≅ ⋀ᵏ⁺¹ M ⊕ e ∧ ⋀ᵏ M` used to adjoin one element to a Koszul complex.
In this splitting, the contraction by `φ + x · snd` acts as `d(a + e ∧ b) = (d a + x b) - e ∧ d b`
(`ExteriorAlgebra.map_fst_contractLeft_coprod`,
`ExteriorAlgebra.contractLeft_map_fst_contractLeft_snd`).
-/


open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- **An exterior-basis vector is the product of its generators in increasing order**: the basis
vector indexed by `s` is `ι (b i₁) * ⋯ * ι (b iₖ)` for `s.sort = [i₁, …, iₖ]`. -/
theorem _root_.Module.Basis.exteriorAlgebra_eq_prod_map_sort {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s = ((s.sort.map b).map (ExteriorAlgebra.ι R)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  congr 1
  refine List.ext_getElem (by simp) fun n _ _ ↦ ?_
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_map,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.ofCard]
  exact congrArg (fun i ↦ ExteriorAlgebra.ι R (b i)) (Finset.orderEmbOfFin_apply _ _ _)

/-- Contracting an exterior-basis vector by a coordinate not in its index set gives zero. -/
@[simp]
private theorem contractLeft_coord_basis_eq_zero_of_not_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [b.exteriorAlgebra_eq_prod_map_sort]
  refine contractLeft_prod_map_ι_eq_zero _ fun m hm ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    ite_eq_right_iff]
  rintro rfl
  exact absurd ((Finset.mem_sort _).mp hj) hi

/-- **The grade involution acts on an exterior monomial by the parity of its degree.** The
monomial is the product of its `n` generators, each of which the involution negates. -/
@[simp]
theorem involute_ιMulti {n : ℕ} (v : Fin n → M) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  -- Every exterior monomial is the product of the list of its generators.
  have h : ExteriorAlgebra.ιMulti R n v =
      ((List.ofFn v).map (CliffordAlgebra.ι (0 : QuadraticForm R M))).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl
  rw [h, CliffordAlgebra.involute_prod_map_ι, List.length_ofFn]

/-- **The grade involution acts on an exterior-basis vector by the parity of its index set.** The
basis vector indexed by `s` is the monomial on `s.card` generators. -/
@[simp]
theorem involute_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (b.ExteriorAlgebra s) =
      (-1 : R) ^ s.card • b.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply]
  exact involute_ιMulti _

def basisEraseSignOfErase {I : Type w} [LinearOrder I]
    (i : I) (t : Finset I) (hi : i ∉ t) : ℤˣ :=
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t' : Set.powersetCard I t.card := ⟨t, rfl⟩
  (Set.powersetCard.permOfDisjoint (s := u) (t := t') (by simp [u, t', hi])).sign

/-- The shuffle sign for the singleton basis vector indexed by `i` followed by the basis vector
indexed by `s.erase i`. When `i ∈ s`, this is the sign of moving `i` to the front of `s`. -/
def basisEraseSign {I : Type w} [LinearOrder I] (i : I) (s : Finset I) : ℤˣ :=
  basisEraseSignOfErase i (s.erase i) (by simp)

private theorem basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem
    {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) (hi : i ∈ s) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  let n := (s.erase i).card
  have hsCard : s.card = n + 1 := by
    simpa [n] using (Finset.card_erase_add_one hi).symm
  -- Enumerate `s` in increasing order. The position `k` of `i` counts precisely the entries
  -- which the shuffle crosses when it moves the singleton `{i}` to the front.
  let e : Fin (n + 1) ↪o I := s.orderEmbOfFin hsCard
  let k : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨i, hi⟩
  have hek : e k = i := by
    exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨i, hi⟩)
  have hremove : k.removeNth (fun j ↦ e j) =
      (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      exact Finset.mem_erase.mpr ⟨fun h ↦ k.succAbove_ne j (e.injective (h.trans hek.symm)),
        Finset.orderEmbOfFin_mem s hsCard _⟩
    · exact e.strictMono.comp (Fin.strictMono_succAbove k)
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I n := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hsCard' : s.card = 1 + n := hsCard.trans (Nat.add_comm n 1)
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) hsCard' : Set.powersetCard I (1 + n)) := by
    apply Subtype.ext
    simp [u, t, hi]
  let p : Equiv.Perm (Fin (1 + n)) := Set.powersetCard.permOfDisjoint hdisj
  let c : Fin (1 + n) ≃ Fin (n + 1) := finCongr (Nat.add_comm 1 n)
  let p' : Equiv.Perm (Fin (n + 1)) := c.symm.trans (p.trans c)
  -- After reconciling the two cardinality presentations, this shuffle is the inverse cycle
  -- which moves position `k` to the front and shifts the preceding positions one step right.
  have hec : (fun q ↦ e (c q)) =
      (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop := by
    apply Finset.orderEmbOfFin_unique
    · intro q
      have hdval : (Set.powersetCard.disjUnion hdisj).val = s :=
        congrArg Subtype.val hunion
      rw [hdval]
      exact Finset.orderEmbOfFin_mem s hsCard (c q)
    · intro a b hab
      apply e.strictMono
      simpa [c, Fin.ext_iff] using hab
  have hp : p' = k.cycleRange.symm := by
    apply Equiv.ext
    intro j
    apply e.injective
    -- Unfold the conjugated shuffle so both sides are compared in the increasing enumeration.
    change e (c (p (c.symm j))) = e (k.cycleRange.symm j)
    have hrhs : e (k.cycleRange.symm j) =
        (Fin.cons (e k) (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j := by
      simpa only [Function.comp_apply] using
        congrFun (Fin.cons_removeNth_eq_comp_cycleRange_symm e k) j |>.symm
    rw [hrhs, hek]
    -- The disjoint-union permutation enumerates the singleton first and the erased set second.
    change e (c (p (c.symm j))) =
      (Fin.cons i (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j
    rw [hremove]
    -- Expose the function represented by the increasing enumeration before applying `hec`.
    change (fun q ↦ e (c q)) (p (c.symm j)) = _
    rw [hec]
    let x : (Set.powersetCard.disjUnion hdisj).val :=
      Equiv.Finset.disjUnionEquiv u.val t.val hdisj
        (((Set.powersetCard.orderIsoOfFin u).sumCongr
          (Set.powersetCard.orderIsoOfFin t)) (finSumFinEquiv.symm (c.symm j)))
    have hx : (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop (p (c.symm j)) = x := by
      have hpApply : p (c.symm j) =
          (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).symm x := rfl
      rw [hpApply]
      exact congrArg Subtype.val
        ((Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).apply_symm_apply x)
    rw [hx]
    cases j using Fin.cases with
    | zero =>
        have hzero : finSumFinEquiv.symm (c.symm 0) = Sum.inl (0 : Fin 1) := by
          apply finSumFinEquiv.injective
          apply Fin.ext
          rfl
        simp only [x, hzero, Fin.cons_zero]
        -- Coercing the disjoint-union subtype reveals the singleton entry.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inl ((Set.powersetCard.orderIsoOfFin u) 0))) = i
        rw [Equiv.Finset.disjUnionEquiv_inl]
        dsimp only [Set.powersetCard.orderIsoOfFin, u]
        -- The unique increasing enumeration of a singleton is constant at its element.
        change Finset.orderEmbOfFin {i} (Finset.card_singleton i) 0 = i
        exact Finset.orderEmbOfFin_singleton i 0
    | succ q =>
        have hsucc : finSumFinEquiv.symm (c.symm q.succ) = Sum.inr q := by
          apply finSumFinEquiv.injective
          rw [finSumFinEquiv.apply_symm_apply]
          apply Fin.ext
          simp [c]
          omega
        simp only [x, hsucc, Fin.cons_succ]
        -- Coercing the right summand reveals the increasing enumeration of `s.erase i`.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inr ((Set.powersetCard.orderIsoOfFin t) q))) =
            (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rw [Equiv.Finset.disjUnionEquiv_inr]
        dsimp only [Set.powersetCard.orderIsoOfFin, t]
        change (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q =
          (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rfl
  have hsign : Equiv.Perm.sign p' = Equiv.Perm.sign p := by
    simp [p']
  rw [basisEraseSign]
  -- Unfolding the local permutation exposes the sign computed above.
  change Equiv.Perm.sign p = _
  rw [← hsign, hp, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  congr 1
  -- The initial segment below `k` is order-isomorphic to the elements of `s` strictly below `i`,
  -- so its cardinality is the exponent in the claimed sign.
  have himage : Finset.image e (Finset.Iio k) = s.filter (fun j ↦ j < i) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hsCard j, hek ▸ e.strictMono hj⟩
    · rintro ⟨hxs, hxi⟩
      let j : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨x, hxs⟩
      refine ⟨j, ?_, ?_⟩
      · exact e.lt_iff_lt.mp (by simpa [e, j, k] using hxi)
      · exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨x, hxs⟩)
  rw [← Fin.card_Iio k, ← himage, Finset.card_image_of_injective _ e.injective]

/-- The shuffle sign which moves `i` to the front of an ordered exterior monomial is `-1`
raised to the number of indices before `i`. This formula also applies when `i ∉ s`: inserting
`i` changes neither the erased set defining the shuffle nor the indices strictly below `i`. -/
@[simp]
theorem basisEraseSign_eq_neg_one_pow_card_filter_lt {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  by_cases hi : i ∈ s
  · exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i s hi
  · have hsign : basisEraseSign i (insert i s) = basisEraseSign i s := by
      simp [basisEraseSign, hi]
    have hfilter : (insert i s).filter (fun j ↦ j < i) = s.filter (fun j ↦ j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hji' | hjs, hji⟩
        · exact ((ne_of_lt hji) hji').elim
        · exact ⟨hjs, hji⟩
      · exact fun h ↦ ⟨Or.inr h.1, h.2⟩
    rw [← hsign, ← hfilter]
    exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i (insert i s)
      (Finset.mem_insert_self i s)

/-- The exterior-basis vector indexed by a singleton is the image of the corresponding basis
vector under the exterior-algebra generator. -/
@[simp]
theorem basis_singleton {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  simp [b.exteriorAlgebra_eq_prod_map_sort]

/-- The exterior-basis vector indexed by a pair `{i, j}` with `i < j` is the product of the two
basis vectors in increasing order. -/
theorem basis_pair {I : Type w} [LinearOrder I] (b : Module.Basis I R M) {i j : I} (hij : i < j) :
    b.ExteriorAlgebra {i, j} = ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b j) := by
  rw [b.exteriorAlgebra_eq_prod_map_sort,
    Finset.sort_insert _ (by simpa using hij.le) (by simpa using hij.ne)]
  simp

/-- Multiplying the basis vector for `i` by the basis vector for `s.erase i` reconstructs the
basis vector for `s`, with the shuffle sign that moves `i` to the front. -/
theorem basis_singleton_mul_basis_erase {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∈ s) :
    b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
      basisEraseSign i s • b.ExteriorAlgebra s := by
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) (by
        rw [Finset.card_erase_of_mem hi]
        have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega) : Set.powersetCard I (1 + (s.erase i).card)) := by
    apply Subtype.ext
    simp [Set.powersetCard.disjUnion, u, t, hi]
  have hprod := ExteriorAlgebra.basis_mul_of_disjoint b u t hdisj
  rw [hunion] at hprod
  simpa [basisEraseSign, basisEraseSignOfErase, u, t] using hprod

/-- **Creating a basis coordinate inserts it into the index set**, with the shuffle sign that
moves it to the front; it is zero when the coordinate is already present, since a repeated
generator squares to zero. -/
@[simp]
theorem ι_mul_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra s =
      if i ∈ s then 0
        else basisEraseSign i (insert i s) • b.ExteriorAlgebra (insert i s) := by
  classical
  rw [← basis_singleton]
  split_ifs with hi
  · exact ExteriorAlgebra.basis_mul_of_not_disjoint b
      (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard I 1) (⟨s, rfl⟩ : Set.powersetCard I s.card)
      (by simp [hi])
  · have h := basis_singleton_mul_basis_erase b i (insert i s) (Finset.mem_insert_self i s)
    rwa [Finset.erase_insert hi] at h

/-- Contracting an exterior-basis vector erases the contracted coordinate, with the shuffle sign
that moves that coordinate to the front; it is zero when the coordinate is absent. -/
@[simp]
theorem contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then basisEraseSign i s • b.ExteriorAlgebra (s.erase i) else 0 := by
  classical
  split_ifs with hi
  · have hprod' := basis_singleton_mul_basis_erase b i s hi
    have hcontract : contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)
        (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
        b.ExteriorAlgebra (s.erase i) := by
      rw [basis_singleton, contractLeft_ι_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [contractLeft_coord_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
        mul_zero, sub_zero]
      simp
    rcases Int.units_eq_one_or (basisEraseSign i s) with hsign | hsign
    · rw [hsign, one_smul] at hprod' ⊢
      rw [← hprod']
      exact hcontract
    · have hprodNeg : b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
          -b.ExteriorAlgebra s := by
        rw [hsign] at hprod'
        simpa using hprod'
      rw [hprodNeg, map_neg] at hcontract
      have h := congrArg Neg.neg hcontract
      rw [hsign]
      simpa using h
  · exact contractLeft_coord_basis_eq_zero_of_not_mem b i s hi

/-- Creating an unoccupied coordinate after contracting an occupied one replaces that
coordinate in an exterior-basis vector, with the product of the two shuffle signs. -/
theorem ι_mul_contractLeft_coord_basis_of_not_mem_of_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i j : I) (s : Finset I) (hi : i ∉ s) (hj : j ∈ s) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord j) (b.ExteriorAlgebra s) =
      (basisEraseSign j s * basisEraseSign i (insert i (s.erase j))) •
        b.ExteriorAlgebra (insert i (s.erase j)) := by
  classical
  simp [contractLeft_coord_basis, ι_mul_basis, hi, hj, mul_smul_comm, smul_smul]

/-- Creation after contraction by a basis coordinate is the projection onto exterior basis
vectors containing that coordinate.

This is not a `simp` lemma because `contractLeft_coord_basis` is the canonical normal form for
the contraction in its left-hand side. -/
theorem ι_mul_contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [contractLeft_coord_basis]
  split_ifs with hi
  · rw [← basis_singleton]
    rw [mul_smul_comm]
    rw [basis_singleton_mul_basis_erase b i s hi]
    let n := (s.filter fun j ↦ j < i).card
    have hsignSq : ((-1 : ℤˣ) ^ n) * ((-1 : ℤˣ) ^ n) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [basisEraseSign_eq_neg_one_pow_card_filter_lt, smul_smul, hsignSq, one_smul]
  · rw [mul_zero]

/-! ### Exterior powers under the grade involution and contraction -/

/-- **The grade involution acts on the `n`-th exterior power by `(-1) ^ n`.** -/
theorem involute_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    involute (Q := (0 : QuadraticForm R M)) x = (-1 : R) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ih, involute_ι, mul_smul_comm, neg_mul, smul_neg, pow_succ', mul_smul,
      neg_one_smul]

/-- Contraction annihilates the zeroth exterior power, the scalars. -/
theorem contractLeft_eq_zero_of_mem_exteriorPower_zero (d : Module.Dual R M)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x = 0 := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact contractLeft_algebraMap (Q := (0 : QuadraticForm R M)) d r

/-- **Contraction lowers the exterior degree by one**: it carries the `(n + 1)`-th exterior power
into the `n`-th. -/
theorem contractLeft_mem_exteriorPower (d : Module.Dual R M) {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^n M := by
  suffices h : ∀ i (x : ExteriorAlgebra R M) (_ : x ∈ ⋀[R]^i M),
      contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^(i - 1) M from h _ x hx
  intro i x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [contractLeft_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    rcases i with _ | i
    · rw [contractLeft_eq_zero_of_mem_exteriorPower_zero d hx, mul_zero]
      exact zero_mem _
    · rw [Nat.add_sub_cancel] at ih
      exact ι_mul_mem_exteriorPower v ih

/-- **Contraction of a wedge product of vectors** is the alternating sum of the contractions of
its factors: `d ⌋ (v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i d(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem contractLeft_ιMulti (d : Module.Dual R M) {n : ℕ} (v : Fin (n + 1) → M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * d (v i)) •
        ExteriorAlgebra.ιMulti R n (i.removeNth v) := by
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have hrem (i : Fin (n + 1)) : ExteriorAlgebra.ιMulti R (n + 1) (i.succ.removeNth v) =
        ExteriorAlgebra.ι R (v 0) *
          ExteriorAlgebra.ιMulti R n (i.removeNth (Matrix.vecTail v)) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 2
      ext j
      simp [Matrix.vecTail, Fin.removeNth_apply, Fin.succ_succAbove_succ]
    rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, ih, Fin.sum_univ_succ (n := n + 1),
      Finset.mul_sum]
    simp [hrem, pow_succ, sub_eq_add_neg, Matrix.vecTail, Fin.tail,
      Function.comp_def]

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Contraction against a functional commutes with an exterior-algebra map after pulling
back the functional. -/
theorem contractLeft_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R N)) d (_root_.ExteriorAlgebra.map f x) =
      _root_.ExteriorAlgebra.map f
        (contractLeft (Q := (0 : QuadraticForm R M)) (d ∘ₗ f) x) := by
  -- The exterior-algebra map is the zero-quadratic-form case of the Clifford-algebra map.
  exact CliffordAlgebra.contractLeft_map { f with map_app' := fun _ => rfl } d x

/-- **A vector graded-commutes with every multivector**: moving `ι R m` past `x` applies the grade
involution to `x`. -/
theorem ι_mul_eq_involute_mul (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * x =
      involute (Q := (0 : QuadraticForm R M)) x * ExteriorAlgebra.ι R m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
    rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap m v
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, map_mul, mul_assoc]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

end ExteriorAlgebra

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Contraction in degree at least the rank -/

variable [Module.Free R M] [Module.Finite R M]

/-- **A form of degree at least the rank is divisible by any vector `m` with `d m = 1`**: if
`d m = 1` and `finrank R M ≤ n`, then every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. -/
theorem eq_ι_mul_contractLeft_of_finrank_le {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {n : ℕ} (hn : Module.finrank R M ≤ n) {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    x = ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x := by
  -- `m ∧ x` lies above the rank, so it vanishes, and contracting it by `d` gives the claim.
  have h0 : ι R m * x = 0 := ZeroMemClass.coe_eq_zero.mpr <|
    exteriorPower.eq_zero_of_finrank_lt (1 + n) (by omega)
      ⟨_, SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) hx⟩
  have h := congrArg (contractLeft (Q := (0 : QuadraticForm R M)) d) h0
  rwa [contractLeft_ι_mul, hdm, one_smul, map_zero, sub_eq_zero] at h

/-- **Forms killed by a contraction multiply to zero in degree at least the rank**: if `d m = 1`,
the forms `x ∈ ⋀ᵏ M` and `y ∈ ⋀ˡ M` satisfy `d ⌋ x = 0` and `d ⌋ y = 0`, and
`finrank R M ≤ k + l`, then `x ∧ y = 0`. -/
theorem mul_eq_zero_of_contractLeft_eq_zero {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {k l : ℕ} (hkl : Module.finrank R M ≤ k + l) {x y : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) (hy : y ∈ ⋀[R]^l M)
    (hdx : contractLeft (Q := (0 : QuadraticForm R M)) d x = 0)
    (hdy : contractLeft (Q := (0 : QuadraticForm R M)) d y = 0) : x * y = 0 := by
  rw [eq_ι_mul_contractLeft_of_finrank_le hdm hkl (SetLike.mul_mem_graded hx hy), contractLeft_mul,
    hdx, hdy, zero_mul, mul_zero, add_zero, mul_zero]

/-- **The square of a two-form in rank at most four.** If `d m = 1` and `finrank R M ≤ 4`, a
two-form `x` satisfies `x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. -/
theorem mul_self_eq_two_smul_mul_ι_mul_contractLeft {d : Module.Dual R M} {m : M}
    (hdm : d m = 1) (h4 : Module.finrank R M ≤ 4) {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^2 M) :
    x * x = 2 • (x * (ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x)) := by
  -- Write `x = m ∧ a + b` with `a = d ⌋ x`. Then `d ⌋ b = 0`, so `b ∧ b = 0` in rank at most
  -- four; also `(m ∧ a) ∧ (m ∧ a) = 0`, and the two-forms `m ∧ a` and `b` commute.
  -- The contraction `d ⌋ x` is a vector `a`.
  obtain ⟨a, ha⟩ : ∃ a, ι R a = contractLeft (Q := (0 : QuadraticForm R M)) d x :=
    ⟨_, ι_ιInv_of_mem_exteriorPower_one (contractLeft_mem_exteriorPower d (n := 1) hx)⟩
  rw [← ha]
  set g := ι R m * ι R a with hg
  have hgmem : g ∈ ⋀[R]^2 M :=
    SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) (ι_mem_exteriorPower_one a)
  -- The remainder `b = x - m ∧ a` is a two-form killed by `d`.
  set b := x - g with hb
  have hbmem : b ∈ ⋀[R]^2 M := sub_mem hx hgmem
  have hdb : contractLeft (Q := (0 : QuadraticForm R M)) d b = 0 := by
    have hda : contractLeft (Q := (0 : QuadraticForm R M)) d (ι R a) = 0 := by
      rw [ha, contractLeft_contractLeft]
    rw [hb, map_sub, hg, contractLeft_ι_mul, hdm, one_smul, hda, mul_zero, sub_zero, ha,
      sub_self]
  have hbb : b * b = 0 :=
    mul_eq_zero_of_contractLeft_eq_zero hdm (by omega) hbmem hbmem hdb hdb
  have hgg : g * g = 0 := by
    have h := ι_add_mul_swap (R := R) a m
    rw [add_eq_zero_iff_eq_neg] at h
    calc g * g = ι R m * (ι R a * ι R m) * ι R a := by simp only [hg, mul_assoc]
      _ = 0 := by rw [h, mul_neg, ← mul_assoc, ι_sq_zero, zero_mul, neg_zero, zero_mul]
  -- A two-form is fixed by the grade involution, so it commutes with the two-form `g`.
  have hinv : involute (Q := (0 : QuadraticForm R M)) b = b := by
    rw [involute_of_mem_exteriorPower hbmem]
    simp
  have hcomm : g * b = b * g := by
    rw [hg, mul_assoc, ι_mul_eq_involute_mul a b, hinv, ← mul_assoc, ι_mul_eq_involute_mul m b,
      hinv, mul_assoc]
  have hx' : x = b + g := (sub_add_cancel x g).symm
  rw [hx', add_mul, mul_add, mul_add, hbb, hgg, hcomm, add_mul, hgg, two_smul]
  abel

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Splitting off a free coordinate -/

/-- **Splitting off a free coordinate.** In the exterior algebra of `M × R`, with `e = (0, 1)`,
every element `z` is `a + e ∧ b`, where `a` is the image of `z` under `⋀ M × R → ⋀ M → ⋀ (M × R)`
and `b` is the image of the contraction of `z` by the second coordinate. -/
theorem map_inl_map_fst_add_ι_inr_mul_contractLeft_snd (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.inl R M R) (map (LinearMap.fst R M R) z) +
        ι R (LinearMap.inr R M R 1) * map (LinearMap.inl R M R) (map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      z := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, mul_add]
    conv_rhs => rw [← h₁, ← h₂]
    abel
  | ι_mul z m ih =>
    -- Write `m = (m₁, 0) + m₂ e`; then `e ∧ e = 0` and `(m₁, 0) ∧ e = -(e ∧ (m₁, 0))`.
    have hm : ι R m = ι R (LinearMap.inl R M R m.1) + m.2 • ι R (LinearMap.inr R M R 1) := by
      rw [← map_smul, ← map_add]; congr 1; ext <;> simp
    have he := ι_sq_zero (R := R) (LinearMap.inr R M R (1 : R))
    have hc := eq_neg_of_add_eq_zero_right <|
      ι_add_mul_swap (R := R) (LinearMap.inr R M R (1 : R)) (LinearMap.inl R M R m.1)
    -- `left_induction` states the step with `CliffordAlgebra.ι 0`, which is `ι R` by definition.
    change _ = ι R m * z
    rw [contractLeft_ι_mul]
    simp only [map_mul, map_sub, map_smul, map_apply_ι]
    conv_rhs => rw [← ih, hm]
    simp only [add_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, ← mul_assoc, he, hc,
      smul_zero, add_zero, neg_mul, LinearMap.fst_apply, LinearMap.snd_apply]
    abel

/-! ### Contractions on `M × R` in the splitting `a + e ∧ b` -/

/-- The contraction by `φ.coprod ψ` on the image of `⋀ M` in `⋀ (M × N)` is the contraction
by `φ`. -/
theorem contractLeft_coprod_map_inl {N : Type*} [AddCommGroup N] [Module R N]
    (φ : Module.Dual R M) (ψ : Module.Dual R N) (w : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R (M × N))) (φ.coprod ψ)
        (map (LinearMap.inl R M N) w) =
      map (LinearMap.inl R M N) (contractLeft (Q := (0 : QuadraticForm R M)) φ w) := by
  rw [contractLeft_map, LinearMap.coprod_inl]

/-- The contraction by `φ + x · snd` on `e ∧ w`, with `e = (0, 1)`: `d(e ∧ w) = x w - e ∧ d w`. -/
theorem contractLeft_coprod_ι_inr_mul (φ : Module.Dual R M) (x : R)
    (w : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (φ.coprod (LinearMap.toSpanSingleton R R x)) (ι R (LinearMap.inr R M R 1) * w) =
        x • w - ι R (LinearMap.inr R M R 1) *
          contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) w := by
  rw [contractLeft_ι_mul]
  simp

/-- Projection onto the first factor retracts the induced map of exterior algebras. -/
theorem leftInverse_map_fst_map_inl {N : Type*} [AddCommGroup N] [Module R N] :
    Function.LeftInverse (map (LinearMap.fst R M N)) (map (LinearMap.inl R M N)) :=
  leftInverse_map_iff.2 fun _ ↦ rfl

/-- The `⋀ M`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the `⋀ M`-component of `d z` is `d a + x b`. -/
theorem map_fst_contractLeft_coprod (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R)))
          (φ.coprod (LinearMap.toSpanSingleton R R x)) z) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R) z) +
        x • map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z) := by
  conv_lhs => rw [← map_inl_map_fst_add_ι_inr_mul_contractLeft_snd z]
  rw [map_add, contractLeft_coprod_map_inl, contractLeft_coprod_ι_inr_mul,
    contractLeft_coprod_map_inl]
  simp only [LinearMap.coe_inr, map_add, map_sub, map_smul, map_mul, map_apply_ι,
    LinearMap.fst_apply, map_zero, zero_mul, sub_zero]
  rw [leftInverse_map_fst_map_inl, leftInverse_map_fst_map_inl]

/-- The `e`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the contraction `d b` is minus the
`e`-component of `d z`. -/
theorem contractLeft_map_fst_contractLeft_snd (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      -map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) z)) := by
  have hD := map_inl_map_fst_add_ι_inr_mul_contractLeft_snd
    (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)
  rw [contractLeft_contractLeft, map_zero, map_zero, mul_zero, add_zero] at hD
  rw [← leftInverse_map_fst_map_inl (R := R) (M := M) (N := R) (contractLeft _ _),
    ← contractLeft_coprod_map_inl φ (LinearMap.toSpanSingleton R R x),
    hD, contractLeft_comm, map_neg]

end ExteriorAlgebra

end

/- BEGIN EXACT BODY: TauCeti.RingTheory.KoszulComplex.Basic -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# The Koszul complex of a linear functional

For a linear functional `φ : M → R` on a module over a commutative ring, the Koszul complex
`K(φ)` is the chain complex `⋯ → ⋀³ M → ⋀² M → M → R` with `K(φ)ₙ = ⋀ⁿ M` and differential the
contraction by `φ`,
`d(v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`.
For a finite sequence `x = (x₁, …, xₙ)` in `R`, the functional `v ↦ ∑ᵢ vᵢ xᵢ` on `Rⁿ` gives the
Koszul complex `K(x)` of the sequence, whose zeroth homology is `R ⧸ (x₁, …, xₙ)`.

## Main declarations

* `TauCeti.koszulComplex φ`: the Koszul complex of `φ`, as an `ℕ`-indexed chain complex of
  `R`-modules.
* `TauCeti.koszulDifferential φ n`: its differential `⋀ⁿ⁺¹ M → ⋀ⁿ M`, the contraction by `φ`, with
  the alternating-deletion formula `TauCeti.koszulDifferential_ιMulti`.
* `TauCeti.zeroEquiv_koszulDifferential_zero`: under `⋀⁰ M ≅ R` and `⋀¹ M ≅ M`, the first
  differential is `φ` itself.
* `TauCeti.exact_koszulDifferential_of_retract`: exactness of a Koszul complex passes to a
  retract along linear maps compatible with the functionals.
* `TauCeti.map_fst_koszulDifferential_coprod`: the coordinate formula for the differential
  after adjoining one scalar to a linear functional.
* `TauCeti.koszulComplex.exactAt_succ_iff`: `Hₖ₊₁(K(φ)) = 0` exactly when the Koszul
  differentials out of and into `⋀ᵏ⁺¹ M` are exact.
* `TauCeti.koszulComplex.map`: the chain map `K(φ) → K(ψ)` induced by a linear map `g` with
  `ψ ∘ g = φ`, functorial in `g`, and `TauCeti.koszulComplex.mapIso`, the isomorphism induced by a
  linear equivalence.
* `TauCeti.koszulComplex.smulHomotopy`: for `m : M`, exterior multiplication by `m` is a
  null-homotopy of multiplication by `φ(m)`, so that `φ(m)` annihilates the Koszul homology
  (`TauCeti.koszulComplex.smul_homology_eq_zero`).
* `TauCeti.koszulComplex.homologyZeroEquiv`: `H₀(K(φ)) ≃ R ⧸ φ(M)`, and its specialization
  `TauCeti.koszulComplex.homologyZeroEquivSpan` to `H₀(K(x)) ≃ R ⧸ (x₁, …, xₙ)` for a finite
  sequence.

## References

* [The Stacks Project, Tags 0622, 0623 and 0624](https://stacks.math.columbia.edu/tag/0621)

The interface (the Koszul complex of a linear functional with exterior-power terms, the
alternating-deletion differential, `koszulComplex.map` along `ψ ∘ g = φ`, and the homotopy
`d(m ∧ v) + m ∧ d(v) = φ(m) v`) follows the design of Nailin Guan in the Mathlib pull requests
[mathlib4#43708](https://github.com/leanprover-community/mathlib4/pull/43708) (definition
of the Koszul complex) and
[mathlib4#43706](https://github.com/leanprover-community/mathlib4/pull/43706) (homotopy of the
Koszul complex). No code from those pull requests is vendored here.
-/

section
noncomputable section

universe u v

open CategoryTheory CliffordAlgebra

namespace TauCeti

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Differential

variable (φ : Module.Dual R M)

/-- The Koszul differential `⋀ⁿ⁺¹ M → ⋀ⁿ M` of a linear functional `φ`: the contraction by `φ`,
`v₀ ∧ ⋯ ∧ vₙ ↦ ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ` (see `koszulDifferential_ιMulti`). -/
def koszulDifferential (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  (contractLeft (Q := (0 : QuadraticForm R M)) φ).restrict fun _ hx ↦
    ExteriorAlgebra.contractLeft_mem_exteriorPower φ hx

/-- The Koszul differential is the contraction by `φ`. -/
@[simp]
theorem coe_koszulDifferential_apply (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    (koszulDifferential φ n x : ExteriorAlgebra R M) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ x :=
  (rfl)

/-- The Koszul differential on a wedge product of vectors is the alternating sum of deletions:
`d(v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem koszulDifferential_ιMulti (n : ℕ) (v : Fin (n + 1) → M) :
    koszulDifferential φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * φ (v i)) •
        exteriorPower.ιMulti R n (i.removeNth v) := by
  ext
  simp only [coe_koszulDifferential_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.contractLeft_ιMulti, Submodule.coe_sum, Submodule.coe_smul]

/-- The Koszul differential squares to zero. -/
@[simp]
theorem koszulDifferential_comp_koszulDifferential (n : ℕ) :
    koszulDifferential φ n ∘ₗ koszulDifferential φ (n + 1) = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (contractLeft_contractLeft φ x.1)

/-- The Koszul differential squares to zero, elementwise. -/
@[simp]
theorem koszulDifferential_koszulDifferential (n : ℕ) (x : ⋀[R]^(n + 2) M) :
    koszulDifferential φ n (koszulDifferential φ (n + 1) x) = 0 :=
  LinearMap.congr_fun (koszulDifferential_comp_koszulDifferential φ n) x

/-- **The first Koszul differential is `φ`**: under the identifications `⋀⁰ M ≅ R` and
`⋀¹ M ≅ M`, the differential `⋀¹ M → ⋀⁰ M` is `φ`. -/
theorem zeroEquiv_comp_koszulDifferential_zero :
    (exteriorPower.zeroEquiv R M).toLinearMap ∘ₗ koszulDifferential φ 0 =
      φ ∘ₗ (exteriorPower.oneEquiv R M).toLinearMap := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp [koszulDifferential_ιMulti]

/-- **The first Koszul differential is `φ`**, elementwise. -/
@[simp]
theorem zeroEquiv_koszulDifferential_zero (x : ⋀[R]^1 M) :
    exteriorPower.zeroEquiv R M (koszulDifferential φ 0 x) = φ (exteriorPower.oneEquiv R M x) :=
  LinearMap.congr_fun (zeroEquiv_comp_koszulDifferential_zero φ) x

/-- The image of the first Koszul differential, transported along `⋀⁰ M ≅ R`, is the image
of `φ`. -/
theorem map_zeroEquiv_range_koszulDifferential_zero :
    (LinearMap.range (koszulDifferential φ 0)).map (exteriorPower.zeroEquiv R M).toLinearMap =
      LinearMap.range φ := by
  rw [← LinearMap.range_comp, zeroEquiv_comp_koszulDifferential_zero,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The Koszul differential is natural: if `ψ ∘ g = φ`, then `⋀ g` intertwines the Koszul
differentials of `φ` and `ψ`. -/
theorem koszulDifferential_comp_map {N : Type*} [AddCommGroup N] [Module R N]
    {ψ : Module.Dual R N} {g : M →ₗ[R] N} (h : ψ ∘ₗ g = φ) (n : ℕ) :
    koszulDifferential ψ n ∘ₗ exteriorPower.map (n + 1) g =
      exteriorPower.map n g ∘ₗ koszulDifferential φ n :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp [ExteriorAlgebra.contractLeft_map, h]

/-- The Koszul differential is natural, elementwise: `⋀ g` carries the Koszul differential of
`ψ ∘ g` to that of `ψ`. -/
@[simp]
theorem koszulDifferential_map {N : Type*} [AddCommGroup N] [Module R N]
    (ψ : Module.Dual R N) (g : M →ₗ[R] N) (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    koszulDifferential ψ n (exteriorPower.map (n + 1) g x) =
      exteriorPower.map n g (koszulDifferential (ψ ∘ₗ g) n x) :=
  LinearMap.congr_fun (koszulDifferential_comp_map _ rfl n) x

/-- The `⋀ M`-component of the Koszul differential of `K(φ, x)`: writing `z = a + e ∧ b`, it is
`d a + x b`. -/
theorem map_fst_koszulDifferential_coprod (x : R) (k : ℕ) (z : ⋀[R]^(k + 1) (M × R)) :
    exteriorPower.map k (LinearMap.fst R M R)
        (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) k z) =
      koszulDifferential φ k (exteriorPower.map (k + 1) (LinearMap.fst R M R) z) +
        x • exteriorPower.map k (LinearMap.fst R M R)
          (koszulDifferential (LinearMap.snd R M R) k z) :=
  Subtype.ext <| by
    simp only [exteriorPower.coe_map, coe_koszulDifferential_apply, Submodule.coe_add,
      Submodule.coe_smul, ExteriorAlgebra.map_fst_contractLeft_coprod]

variable {φ} in
/-- **Exactness passes to retracts.** If `g : M → N` has a retraction `h` and `ψ = φ ∘ h` (so
that also `φ = ψ ∘ g`), then the Koszul complex `K(φ)` is a retract of `K(ψ)`, and exactness of
`K(ψ)` at `⋀ⁿ⁺¹ N` implies exactness of `K(φ)` at `⋀ⁿ⁺¹ M`. -/
theorem exact_koszulDifferential_of_retract {N : Type*} [AddCommGroup N] [Module R N]
    {ψ : Module.Dual R N} (g : M →ₗ[R] N) (h : N →ₗ[R] M) (hhg : h ∘ₗ g = LinearMap.id)
    (hψ : φ ∘ₗ h = ψ) (n : ℕ)
    (hex : Function.Exact (koszulDifferential ψ (n + 1)) (koszulDifferential ψ n)) :
    Function.Exact (koszulDifferential φ (n + 1)) (koszulDifferential φ n) := by
  have hφ : ψ ∘ₗ g = φ := by rw [← hψ, LinearMap.comp_assoc, hhg, LinearMap.comp_id]
  refine LinearMap.exact_of_comp_of_mem_range
    (koszulDifferential_comp_koszulDifferential φ n) fun z hz ↦ ?_
  obtain ⟨y, hy⟩ := (hex (exteriorPower.map (n + 1) g z)).1 (by
    rw [koszulDifferential_map, hφ, hz, map_zero])
  refine ⟨exteriorPower.map (n + 2) h y, ?_⟩
  rw [koszulDifferential_map, hψ, hy]
  simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp, hhg,
    exteriorPower.map_id, LinearMap.id_apply]

/-- The Koszul homotopy identity in degree zero: `d(m ∧ r) = φ(m) r` for `r ∈ ⋀⁰ M`. -/
theorem koszulDifferential_comp_wedgeLeft_zero (m : M) :
    koszulDifferential φ 0 ∘ₗ ExteriorAlgebra.wedgeLeft m 0 = φ m • LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext <| by
    simp [contractLeft_ι_mul, ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero φ x.2]

/-- The Koszul homotopy identity in positive degrees: `m ∧ d(v) + d(m ∧ v) = φ(m) v`. -/
theorem wedgeLeft_comp_koszulDifferential_add (m : M) (n : ℕ) :
    ExteriorAlgebra.wedgeLeft m n ∘ₗ koszulDifferential φ n +
        koszulDifferential φ (n + 1) ∘ₗ ExteriorAlgebra.wedgeLeft m (n + 1) =
      φ m • LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp [contractLeft_ι_mul]

end Differential

/-- The **Koszul complex** `K(φ)` of a linear functional `φ : M → R`: the `ℕ`-indexed chain complex
with `K(φ)ₙ = ⋀ⁿ M` and differential `koszulDifferential φ`, the contraction by `φ`.

The body is exposed so that the terms of the complex are definitionally the exterior powers, and
elements of `(koszulComplex φ).X n` can be used as elements of `⋀ⁿ M`. -/
@[expose] def koszulComplex (φ : Module.Dual R M) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulDifferential φ n))
    fun n ↦ ModuleCat.hom_ext (koszulDifferential_comp_koszulDifferential φ n)

section

variable (φ : Module.Dual R M)

/-- The terms of the Koszul complex are the exterior powers. -/
@[simp]
theorem koszulComplex_X (n : ℕ) : (koszulComplex φ).X n = ModuleCat.of R (⋀[R]^n M) :=
  (rfl)

/-- The differential of the Koszul complex is the Koszul differential. -/
theorem koszulComplex_d (n : ℕ) :
    (koszulComplex φ).d (n + 1) n = ModuleCat.ofHom (koszulDifferential φ n) := by
  simp [koszulComplex]

/-- The differential of the Koszul complex is the Koszul differential, elementwise. -/
@[simp]
theorem koszulComplex_d_apply (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    ((koszulComplex φ).d (n + 1) n).hom x = koszulDifferential φ n x :=
  congr($(koszulComplex_d φ n).hom x)

end

namespace koszulComplex

variable (φ : Module.Dual R M)

/-- The Koszul complex `K(φ)` is exact at `⋀ᵏ⁺¹ M`, i.e. `Hₖ₊₁(K(φ)) = 0`, exactly when the
Koszul differentials `⋀ᵏ⁺² M → ⋀ᵏ⁺¹ M → ⋀ᵏ M` are exact. -/
theorem exactAt_succ_iff (k : ℕ) :
    (koszulComplex φ).ExactAt (k + 1) ↔
      Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, koszulComplex_d]
  -- `ModuleCat.Hom.hom (ModuleCat.ofHom f)` is `f`; `ModuleCat.hom_ofHom` does not rewrite here
  -- because the terms of `koszulComplex φ` are only definitionally the exterior powers.
  rfl

section Map

variable {N P : Type v} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {φ} {ψ : Module.Dual R N} {χ : Module.Dual R P}

/-- The chain map `K(φ) → K(ψ)` induced by a linear map `g : M → N` with `ψ ∘ g = φ`: in degree
`n` it is `⋀ⁿ g`. -/
def map (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) : koszulComplex φ ⟶ koszulComplex ψ :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (exteriorPower.map n g)) fun n ↦ by
    rw [koszulComplex_d, koszulComplex_d]
    exact ModuleCat.hom_ext (koszulDifferential_comp_map _ h n)

/-- In degree `n`, the chain map induced by `g` is `⋀ⁿ g`. -/
@[simp]
theorem map_f (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (n : ℕ) :
    (map g h).f n = ModuleCat.ofHom (exteriorPower.map n g) := by
  rfl

/-- The identity of `M` induces the identity of `K(φ)`. -/
@[simp]
theorem map_id : map (φ := φ) LinearMap.id (LinearMap.comp_id φ) = 𝟙 (koszulComplex φ) := by
  ext n : 1
  rw [map_f, exteriorPower.map_id, HomologicalComplex.id_f]
  exact ModuleCat.ofHom_id

/-- The chain map induced by a composite is the composite of the induced chain maps. -/
@[reassoc]
theorem map_comp (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (g' : N →ₗ[R] P) (h' : χ ∘ₗ g' = ψ) :
    map (g' ∘ₗ g) (by rw [← LinearMap.comp_assoc, h', h]) = map g h ≫ map g' h' := by
  ext n : 1
  rw [map_f, HomologicalComplex.comp_f, map_f, map_f, exteriorPower.map_comp]
  exact ModuleCat.ofHom_comp _ _

/-- The isomorphism `K(φ) ≅ K(ψ)` induced by a linear equivalence `e : M ≃ N` with `ψ ∘ e = φ`;
in degree `n` it is `⋀ⁿ e`. -/
def mapIso (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    koszulComplex φ ≅ koszulComplex ψ where
  hom := map e.toLinearMap h
  inv := map e.symm.toLinearMap (by rw [← h, LinearMap.comp_assoc, e.comp_symm, LinearMap.comp_id])
  hom_inv_id := by
    rw [← map_comp, ← map_id]
    congr 1
    exact e.symm_comp
  inv_hom_id := by
    rw [← map_comp, ← map_id]
    congr 1
    exact e.comp_symm

/-- The isomorphism induced by a linear equivalence `e` is the chain map induced by `e`. -/
@[simp]
theorem mapIso_hom (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    (mapIso e h).hom = map e.toLinearMap h :=
  (rfl)

/-- The inverse of the isomorphism induced by `e` is the chain map induced by `e.symm`. -/
@[simp]
theorem mapIso_inv (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    (mapIso e h).inv =
      map e.symm.toLinearMap (by rw [← h, LinearMap.comp_assoc, e.comp_symm, LinearMap.comp_id]) :=
  (rfl)

end Map

section Homotopy

/-- **Koszul homotopy**: for `m : M`, exterior multiplication `v ↦ m ∧ v` is a null-homotopy of
multiplication by `φ(m)` on `K(φ)`; see `koszulDifferential_comp_wedgeLeft_zero` and
`wedgeLeft_comp_koszulDifferential_add`. -/
def smulHomotopy (m : M) : Homotopy (φ m • 𝟙 (koszulComplex φ)) 0 :=
  Homotopy.mkChainComplex _ (fun n ↦ ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft m n))
    (ModuleCat.hom_ext (koszulDifferential_comp_wedgeLeft_zero φ m).symm)
    fun n ↦ by
      rw [koszulComplex_d, koszulComplex_d]
      exact ModuleCat.hom_ext (wedgeLeft_comp_koszulDifferential_add φ m n).symm

/-- The components of the Koszul homotopy are exterior multiplication by `m`. -/
@[simp]
theorem smulHomotopy_hom (m : M) (n : ℕ) :
    (smulHomotopy φ m).hom n (n + 1) = ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft m n) :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ n

/-- **Every value of `φ` annihilates the Koszul homology**: `φ(m) • z = 0` for every class `z` in
every homology module of `K(φ)`. -/
theorem smul_homology_eq_zero (m : M) (n : ℕ) (z : (koszulComplex φ).homology n) :
    φ m • z = 0 := by
  have h := (smulHomotopy φ m).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_zero,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply] using
    congr(($h).hom z)

end Homotopy

section HomologyZero

/-- `H₀(K(φ))` is the cokernel of the first differential `⋀¹ M → ⋀⁰ M`. -/
def homologyZeroIso :
    (koszulComplex φ).homology 0 ≅
      ModuleCat.of R (⋀[R]^0 M ⧸ LinearMap.range (koszulDifferential φ 0)) :=
  (koszulComplex φ).isoHomologyι₀ ≪≫
    (koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
      ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso

private theorem pOpcycles_comp_homologyZeroIso_hom :
    (koszulComplex φ).pOpcycles 0 ≫ (koszulComplex φ).isoHomologyι₀.inv ≫
        (homologyZeroIso φ).hom =
      ModuleCat.ofHom (LinearMap.range (koszulDifferential φ 0)).mkQ := by
  have h := ((koszulComplex φ).pOpcycles_opcyclesIsoSc'_hom_assoc 1 0 0 (by simp) (by simp)
    ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso.hom).trans
      ((koszulComplex φ).sc' 1 0 0).pOpcycles_comp_moduleCatOpcyclesIso_hom
  simp only [homologyZeroIso, Iso.trans_hom, Iso.inv_hom_id_assoc]
  -- The codomain of `homologyZeroIso` is that of `moduleCatOpcyclesIso` with `sc'` unfolded.
  exact h

/-- **Zeroth Koszul homology**: `H₀(K(φ)) ≃ R ⧸ φ(M)`. It is the cokernel of the first
differential, transported along `⋀⁰ M ≅ R`; see `homologyZeroEquiv_apply`. -/
def homologyZeroEquiv : (koszulComplex φ).homology 0 ≃ₗ[R] R ⧸ LinearMap.range φ :=
  (homologyZeroIso φ).toLinearEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (exteriorPower.zeroEquiv R M)
      (map_zeroEquiv_range_koszulDifferential_zero φ)

/-- `homologyZeroEquiv` sends the class of `x ∈ ⋀⁰ M` to the class of the corresponding scalar. -/
@[simp]
theorem homologyZeroEquiv_apply (x : ⋀[R]^0 M) :
    homologyZeroEquiv φ
        ((koszulComplex φ).isoHomologyι₀.inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
      Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R M x) := by
  have hx : (homologyZeroIso φ).hom.hom
      ((koszulComplex φ).isoHomologyι₀.inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
      (LinearMap.range (koszulDifferential φ 0)).mkQ x :=
    congr(($(pOpcycles_comp_homologyZeroIso_hom φ)).hom x)
  -- `simp` does not rewrite with `Iso.toLinearEquiv_apply` here, so expose `hx` by `rw` first.
  rw [homologyZeroEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, hx]
  simp

/-- **Zeroth Koszul homology of a finite sequence**: for `x = (xᵢ)` in `R`, the Koszul complex of
the functional `v ↦ ∑ᵢ vᵢ xᵢ` has `H₀ ≃ R ⧸ (xᵢ)`. -/
def homologyZeroEquivSpan {ι : Type*} [Fintype ι] (x : ι → R) :
    (koszulComplex (Fintype.linearCombination R x)).homology 0 ≃ₗ[R]
      R ⧸ Ideal.span (Set.range x) :=
  homologyZeroEquiv _ ≪≫ₗ Submodule.quotEquivOfEq _ _ (Fintype.range_linearCombination R x)

/-- `homologyZeroEquivSpan` sends the class of `y ∈ ⋀⁰ Rⁿ` to the class of the corresponding
scalar modulo `(xᵢ)`. -/
@[simp]
theorem homologyZeroEquivSpan_apply {ι : Type*} [Fintype ι] (x : ι → R)
    (y : ⋀[R]^0 (ι → R)) :
    homologyZeroEquivSpan x
        ((koszulComplex (Fintype.linearCombination R x)).isoHomologyι₀.inv.hom
          (((koszulComplex (Fintype.linearCombination R x)).pOpcycles 0).hom y)) =
      Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R (ι → R) y) := by
  simpa [homologyZeroEquivSpan] using Submodule.quotEquivOfEq_mk _ _
    (Fintype.range_linearCombination R x) (exteriorPower.zeroEquiv R (ι → R) y)

end HomologyZero

end koszulComplex

end TauCeti

end
end
end

/- BEGIN EXACT BODY: TauCeti.Algebra.Ring.Subgroup -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Additive closures in rings

This file gives criteria for the additive closure of a set in a ring to be closed under
multiplication, and hence to coincide with the underlying additive subgroup of the subring
generated by that set.

## Main results

* `TauCeti.AddSubgroup.mul_mem_closure_of_mul_mem`: products of elements of an additive closure
  remain in the closure when this holds for its generators.
* `AddSubgroup.closure_mul_closure`: the product of two additive closures is the additive
  closure of the pairwise products.
* `Subring.toAddSubgroup_closure_of_one_mem_of_mul_mem`: under the corresponding
  hypotheses, the subring and additive-subgroup closures have the same underlying additive group.
* `AddSubgroup.multiplierRing`: the subring of elements `x` with `x W ⊆ W`, for an additive
  subgroup `W` of a ring.
-/

section
open scoped Pointwise

namespace TauCeti

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- The product of two additive closures is the additive closure of the pairwise products.

This is the additive-subgroup analogue of `AddSubmonoid.closure_mul_closure` from
`Mathlib.Algebra.Ring.Submonoid.Pointwise`. -/
theorem _root_.AddSubgroup.closure_mul_closure (S T : Set R) :
    AddSubgroup.closure S * AddSubgroup.closure T = AddSubgroup.closure (S * T) := by
  apply AddSubgroup.toAddSubmonoid_injective
  simp only [AddSubgroup.mul_toAddSubmonoid, AddSubgroup.closure_toAddSubmonoid,
    AddSubmonoid.closure_union, AddSubmonoid.closure_neg,
    AddSubmonoid.sup_mul, AddSubmonoid.mul_sup, AddSubmonoid.closure_mul_closure,
    neg_mul, mul_neg, AddSubmonoid.neg_sup, neg_neg, sup_idem, sup_comm]

/-- If products of generators lie in their additive closure, then that additive closure is
closed under multiplication. -/
theorem AddSubgroup.mul_mem_closure_of_mul_mem {R : Type*} [NonUnitalNonAssocRing R] {s : Set R}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ AddSubgroup.closure s) {x y : R}
    (hx : x ∈ AddSubgroup.closure s) (hy : y ∈ AddSubgroup.closure s) :
    x * y ∈ AddSubgroup.closure s := by
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy => exact hs x hx y hy
  | zero_left => simp
  | zero_right => simp
  | add_left _ _ _ _ _ _ hx hy => simpa [add_mul] using AddSubgroup.add_mem _ hx hy
  | add_right _ _ _ _ _ _ hx hy => simpa [mul_add] using AddSubgroup.add_mem _ hx hy
  | neg_left _ _ _ _ hx => simpa [neg_mul] using AddSubgroup.neg_mem _ hx
  | neg_right _ _ _ _ hx => simpa [mul_neg] using AddSubgroup.neg_mem _ hx

/-- If the additive closure of a set contains one and products of generators lie in that closure,
then it is the underlying additive subgroup of the subring closure of the set. -/
theorem _root_.Subring.toAddSubgroup_closure_of_one_mem_of_mul_mem {R : Type*} [NonAssocRing R]
    {s : Set R}
    (h1 : (1 : R) ∈ AddSubgroup.closure s)
    (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ AddSubgroup.closure s) :
    (Subring.closure s).toAddSubgroup = AddSubgroup.closure s := by
  refine le_antisymm (fun x hx => ?_) ((AddSubgroup.closure_le _).2 fun x hx => ?_)
  · rw [Subring.mem_toAddSubgroup] at hx
    induction hx using Subring.closure_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | one => exact h1
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
    | mul _ _ _ _ hx hy => exact AddSubgroup.mul_mem_closure_of_mul_mem hmul hx hy
  · exact Subring.mem_toAddSubgroup.2 (Subring.subset_closure hx)

/-- The *multiplier ring* of an additive subgroup `W` of a ring: the elements `x` with `x W ⊆ W`,
that is, the transporter of `W` into itself under left multiplication. It is a subring even when
`W` is not. -/
def _root_.AddSubgroup.multiplierRing {R : Type*} [Ring R] (W : AddSubgroup R) : Subring R where
  carrier := {x | ∀ z ∈ W, x * z ∈ W}
  one_mem' z hz := by rwa [one_mul]
  mul_mem' hx hy z hz := by
    rw [mul_assoc]
    exact hx _ (hy z hz)
  zero_mem' z _ := by
    rw [zero_mul]
    exact zero_mem W
  add_mem' hx hy z hz := by
    rw [add_mul]
    exact add_mem (hx z hz) (hy z hz)
  neg_mem' hx z hz := by
    rw [neg_mul]
    exact neg_mem (hx z hz)

@[simp]
theorem _root_.AddSubgroup.mem_multiplierRing {R : Type*} [Ring R] {W : AddSubgroup R} {x : R} :
    x ∈ W.multiplierRing ↔ ∀ z ∈ W, x * z ∈ W :=
  Iff.rfl

end TauCeti

end
end


end
