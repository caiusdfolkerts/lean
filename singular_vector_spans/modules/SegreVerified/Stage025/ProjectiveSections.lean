module
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs
public import SegreVerified.Stage001
public import SegreVerified.Stage002
public import SegreVerified.Stage003
public import SegreVerified.Stage004
public import SegreVerified.Stage005
public import SegreVerified.Stage006
public import SegreVerified.Stage007
public import SegreVerified.Stage008
public import SegreVerified.Stage009
public import SegreVerified.Stage010
public import SegreVerified.Stage011
public import SegreVerified.Stage012
public import SegreVerified.Stage013
public import SegreVerified.Stage014
public import SegreVerified.Stage015
public import SegreVerified.Stage016
public import SegreVerified.Stage017
public import SegreVerified.Stage018
public import SegreVerified.Stage019
public import SegreVerified.Stage020
public import SegreVerified.Stage021
public import SegreVerified.Stage022
public import SegreVerified.Stage023
public import SegreVerified.Stage024

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Tactic.Push
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Data.Sym.NatCard
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Sym2
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Function.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Logic.Equiv.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Lean.Util.CollectAxioms
import all Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Lean.Util.Sorry
public import Lean.Elab.Command
public import Lean.PrettyPrinter

public import SegreVerified.Stage025.ProjectiveCech

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreProjectiveCohomology

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreProjectiveCohomology"
  out.flush

/-!
# Projective exterior cohomology and the full Koszul gap

The named sections preserve the original proof stages and local scopes.
-/


section SegreProjectiveGlobalSections

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted to literal MvPolynomial projective space from the pinned TauCeti
TwistingSheaf/GlobalSections proof at commit 06d5bb4e3ebb737dc6538567f5c53bf8800b9362.
-/


/-!
# All global sections of the literal projective twisting sheaves

The fraction comparison and cancellation argument computes actual global sections
on Proj of the polynomial ring. The map is the literal polynomial divided by one.
This supplies the degree-zero comparison needed to identify the Euler kernel with
alternating bilinear tensors; it does not replace sheaf cohomology by a new definition.
-/

set_option autoImplicit false



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.ProjectiveGlobalSections

open CategoryTheory AlgebraicGeometry

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

/-- The literal polynomial projective space has its canonical morphism to the coefficient field. -/
def projectiveToSpec : Proj 𝒜 ⟶ Spec (.of K) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0)))

instance polynomialProjectiveOver : (Proj 𝒜).Over (Spec (.of K)) :=
  ⟨projectiveToSpec (I := I) (K := K)⟩

/-- The canonical base-field action on global functions is the literal constant polynomial. -/
theorem val_baseRingToGlobalSections_apply (c : K) (x : (⊤ : (Proj 𝒜).Opens)) :
    ((Scheme.Modules.baseRingToGlobalSections K (Proj 𝒜) c).val x).val=
      Localization.mk (MvPolynomial.C c) 1 := by
  rw [Scheme.Modules.baseRingToGlobalSections_apply]
  change (((projectiveToSpec (I := I) (K := K)).appTop
    ((Scheme.ΓSpecIso _).inv c)).val x).val=_
  erw [projectiveToSpec, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hΓ := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K (𝒜 0)))) c
  change (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv (algebraMap K (𝒜 0) c) =
    (Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) at hΓ
  erw [← hΓ]
  simpa only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq] using
    (Proj.val_toSpecZero_appTop_apply («𝒜» := 𝒜) (algebraMap K (𝒜 0) c) x)

/-- On the overlap `D₊(Xᵢ Xⱼ)`, two fractions `rᵢ / Xᵢ ^ kᵢ` and `rⱼ / Xⱼ ^ kⱼ` of a section agree
exactly when `Xⱼ ^ kⱼ * rᵢ = Xᵢ ^ kᵢ * rⱼ`: the coordinates are nonzerodivisors, so the
localization `A_{XᵢXⱼ}` does not identify more. -/
private theorem mul_eq_mul_of_restrict_eq {n : ℤ} {i j : I}
    {kᵢ kⱼ jᵢ jⱼ : ℕ}
    (hᵢ : (jᵢ : ℤ) = (kᵢ * 1 : ℕ) + n) (hⱼ : (jⱼ : ℤ) = (kⱼ * 1 : ℕ) + n)
    {rᵢ rⱼ : MvPolynomial I K} (hrᵢ : rᵢ ∈ 𝒜 jᵢ) (hrⱼ : rⱼ ∈ 𝒜 jⱼ)
    (hsᵢ : MvPolynomial.X i ^ kᵢ ∈ 𝒜 (kᵢ * 1)) (hsⱼ : MvPolynomial.X j ^ kⱼ ∈ 𝒜 (kⱼ * 1))
    (hUᵢ : Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i ^ kᵢ))
    (hUⱼ : Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ Proj.basicOpen 𝒜 (MvPolynomial.X j ^ kⱼ))
    (s : Γ(Proj.twistingSheaf 𝒜 n, ⊤))
    (eᵢ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s =
      Proj.twistingSheaf.const hᵢ rᵢ _ hrᵢ hsᵢ _ hUᵢ)
    (eⱼ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s =
      Proj.twistingSheaf.const hⱼ rⱼ _ hrⱼ hsⱼ _ hUⱼ) :
    MvPolynomial.X j ^ kⱼ * rᵢ = MvPolynomial.X i ^ kᵢ * rⱼ := by
  have hle := (Proj.basicOpen_mul 𝒜 (MvPolynomial.X i) (MvPolynomial.X j)).le
  -- both sides are the restriction of `s` to the overlap: restricting a section keeps its values,
  -- which is `Proj.twistingSheaf.res_apply`, true by `rfl`
  have e : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_left)).op
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s) =
      (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_right)).op
        ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s) :=
    Proj.twistingSheaf.ext fun _ ↦ rfl
  rw [eᵢ, eⱼ, Proj.twistingSheaf.res_const, Proj.twistingSheaf.res_const,
    Proj.twistingSheaf.const_eq_const_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 two_pos
      ((MvPolynomial.isHomogeneous_X (R := K) i).mul
        (MvPolynomial.isHomogeneous_X (R := K) j)))] at e
  obtain ⟨N, hN⟩ := e
  exact sub_eq_zero.mp ((((MvPolynomial.isRegular_X (R := K) (n := i)).mul (MvPolynomial.isRegular_X (R := K) (n := j))).pow N
    ).left.mul_left_eq_zero_iff.mp hN)

/-- **Every global section of `𝒪(n)` is a function `q / 1`.** For a coordinate `Xᵢ` there are a
`k` and an element `q` of `A` such that `Xᵢ ^ k * q` is a form of degree `k + n` and the section
takes the value `q / 1` at every point. -/
private theorem homogeneous_X_pow_dvd_subsingleton [Subsingleton I]
    (i : I) (a k : ℕ) (hka : k ≤ a) (p : MvPolynomial I K)
    (hp : p.IsHomogeneous a) : MvPolynomial.X i ^ k ∣ p := by
  rw [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero]
  ext d
  by_cases hd : Finsupp.single i k ≤ d
  · simp only [MvPolynomial.coeff_modMonomial_of_le p hd, MvPolynomial.coeff_zero, Pi.zero_apply,
      Finsupp.zero_apply]
  · rw [MvPolynomial.coeff_modMonomial_of_not_le p hd, MvPolynomial.coeff_zero]
    by_contra hc
    have hdeg : d.degree = a := by
      rw [Finsupp.degree_eq_weight_one]
      exact hp hc
    have he : d = Finsupp.single i (d i) := by
      ext j
      have hji : j = i := Subsingleton.elim _ _
      subst j
      simp
    have hdi : d i = a := by
      have h := congrArg (fun e : I →₀ ℕ => e.degree) he
      rw [Finsupp.degree_single] at h
      exact h.symm.trans hdeg
    apply hd
    intro j
    have hji : j = i := Subsingleton.elim _ _
    subst j
    simpa only [Finsupp.single_eq_same, hdi] using hka

/-- The fraction comparison also covers a single variable in nonnegative
degree: homogeneity then supplies the missing divisibility directly. -/
private theorem exists_forall_apply_eq [Nonempty I] {n : ℤ}
    (hn : 0 ≤ n ∨ Nontrivial I) (i : I) (s : Γ(Proj.twistingSheaf 𝒜 n, ⊤)) :
    ∃ (k j : ℕ) (_ : (j : ℤ) = k + n) (q : MvPolynomial I K),
      MvPolynomial.X i ^ k * q ∈ 𝒜 j ∧ ∀ y, s.1 y = Localization.mk q 1 := by
  -- on each chart `D₊(Xₗ)`, the section is a fraction `r l / Xₗ ^ k l`
  choose k j h r hr H using fun l : I ↦ Proj.twistingSheaf.exists_eq_const_basicOpen
    (MvPolynomial.isHomogeneous_X (R := K) l) one_pos
    ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s)
  have hrel (l l' : I) : MvPolynomial.X l' ^ k l' * r l = MvPolynomial.X l ^ k l * r l' :=
    mul_eq_mul_of_restrict_eq (h l) (h l') (hr l) (hr l') _ _ _ _ s (H l) (H l')
  -- A second coordinate supplies divisibility; for P⁰, nonnegative degree
  -- supplies it by homogeneity of the unique-variable numerator.
  have hdiv : MvPolynomial.X i ^ k i ∣ r i := by
    rcases subsingleton_or_nontrivial I with hI | hI
    · letI := hI
      have hn0 : 0 ≤ n := hn.elim id (fun h => by
        letI := h
        obtain ⟨j, hj⟩ := exists_ne i
        exact (hj (Subsingleton.elim j i)).elim)
      apply homogeneous_X_pow_dvd_subsingleton i (j i) (k i) _ (r i) (hr i)
      have hi := h i
      omega
    · letI := hI
      obtain ⟨i', hi'⟩ := exists_ne i
      exact (MvPolynomial.X_pow_dvd_X_pow_mul_iff hi'.symm).mp ⟨r i', hrel i i'⟩
  obtain ⟨q, hq⟩ := hdiv
  -- then every numerator is `r l = Xₗ ^ k l * q`
  have hrq (l : I) : r l = MvPolynomial.X l ^ k l * q :=
    ((MvPolynomial.isRegular_X (R := K) (n := i)).pow (k i)).left <| by
      beta_reduce
      rw [← hrel, hq]; ring
  refine ⟨k i, j i, by simpa using h i, q, hq ▸ hr i, fun y ↦ ?_⟩
  obtain ⟨l, hl⟩ : ∃ l, y.1 ∈ Proj.basicOpen 𝒜 (MvPolynomial.X l) := by
    have hy : y.1 ∈ ⨆ l, Proj.basicOpen 𝒜 (MvPolynomial.X l) := by
      change y.1 ∈ ⨆ l, ProjectiveCech.coordinateOpen (I := I) (K := K) l
      rw [ProjectiveCech.coordinate_cover (I := I) (K := K)]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  have e := Proj.twistingSheaf.res_apply (homOfLE (le_top (a := Proj.basicOpen 𝒜 (MvPolynomial.X l)))) s
    ⟨y.1, hl⟩
  rw [H l] at e
  refine e.symm.trans ((Proj.twistingSheaf.const_apply ..).trans
    (Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1, ?_⟩)))
  simp [hrq l, mul_comm]

/-- **Twisting sheaves of negative degree have no global sections** on projective space: for
`n < 0`, every global section of `𝒪(n)` on `Proj (MvPolynomial I K)`, with at least two variables,
vanishes. -/
theorem twistingSheaf_top_eq_zero_of_neg {n : ℤ} (hn : n < 0) 
    [Nontrivial I] (s : Γ(Proj.twistingSheaf 𝒜 n, ⊤)) : s = 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  obtain ⟨k, j, hj, q, hq, hs⟩ := exists_forall_apply_eq (Or.inr inferInstance) i s
  -- `Xᵢ ^ k * q` is a form of degree `j < k`, so it vanishes
  have hpow : MvPolynomial.X i ^ k ∈ 𝒜 k := by
    change (MvPolynomial.X i ^ k).IsHomogeneous k
    simpa only [one_mul] using (MvPolynomial.isHomogeneous_X (R := K) i).pow k
  have hq0 : MvPolynomial.X i ^ k * q = 0 := by
    rw [← DirectSum.decompose_of_mem_same 𝒜 hq,
      DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hpow (by omega)]
  ext y
  rw [hs, ((MvPolynomial.isRegular_X (R := K) (n := i)).pow k).left.mul_left_eq_zero_iff.mp hq0, Localization.mk_zero]
  exact (Proj.twistingSheaf.zero_apply y).symm

/-- **The global sections of `𝒪(j)` on projective space are the forms of degree `j`**: for every nonempty variable family, including P⁰, the map `r ↦ r / 1` from the homogeneous elements of degree `j` of
`MvPolynomial I K` to `Γ(Proj (MvPolynomial I K), 𝒪(j))` is bijective. -/
theorem bijective_toTwistingSheaf_top (j : ℕ) [Nonempty I] :
    Function.Bijective (Proj.toTwistingSheaf 𝒜 (rfl : (j : ℤ) = j) ⊤) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  have hpow (k : ℕ) : MvPolynomial.X i ^ k ∈ 𝒜 k := by
    change (MvPolynomial.X i ^ k).IsHomogeneous k
    simpa only [one_mul] using (MvPolynomial.isHomogeneous_X (R := K) i).pow k
  refine ⟨(injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_, fun s ↦ ?_⟩
  · -- on `D₊(Xᵢ)`, the fraction `r / 1` vanishes only if a power of `Xᵢ` kills `r`
    have e := congrArg ((Proj.twistingSheaf 𝒜 j).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (MvPolynomial.X i)))).op) hr
    rw [Proj.res_toTwistingSheaf, map_zero, Proj.toTwistingSheaf_eq_const,
      Proj.twistingSheaf.const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos
        (MvPolynomial.isHomogeneous_X (R := K) i))] at e
    obtain ⟨N, hN⟩ := e
    exact Subtype.ext (((MvPolynomial.isRegular_X (R := K) (n := i)).pow N).left.mul_left_eq_zero_iff.mp hN)
  · obtain ⟨k, j', hj', q, hq, hs⟩ :=
      exists_forall_apply_eq (Or.inl (Nat.cast_nonneg j)) i s
    -- comparing components of degree `k + j`, the element `q` is a form of degree `j`
    have hqj : q = DirectSum.decompose 𝒜 q j := by
      refine ((MvPolynomial.isRegular_X (R := K) (n := i)).pow k).left ?_
      beta_reduce
      rw [← DirectSum.decompose_of_mem_same 𝒜 hq,
        DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒜 (hpow k) (by omega),
        show j' - k = j by omega]
    refine ⟨⟨q, hqj ▸ (DirectSum.decompose 𝒜 q j).2⟩, Proj.twistingSheaf.ext fun y ↦ ?_⟩
    exact (Proj.toTwistingSheaf_apply_apply ..).trans (hs y).symm

/-- The actual global sections of O(j) are all homogeneous degree-j polynomials. -/
def homogeneousGlobalSectionsEquiv (j : ℕ) [Nonempty I] :
    𝒜 j ≃+ Γ(Proj.twistingSheaf 𝒜 j, ⊤) :=
  AddEquiv.ofBijective (Proj.toTwistingSheaf 𝒜 (rfl : (j : ℤ)=j) ⊤)
    (bijective_toTwistingSheaf_top j)

@[simp] theorem homogeneousGlobalSectionsEquiv_apply (j : ℕ) [Nonempty I] (p : 𝒜 j) :
    homogeneousGlobalSectionsEquiv j p=Proj.toTwistingSheaf 𝒜 rfl ⊤ p := rfl

/-- Polynomial-to-section multiplication preserves the canonical base-field action. -/
theorem toTwistingSheaf_top_smul {n : ℤ} {j : ℕ} (h : (j : ℤ)=n)
    (c : K) (p : 𝒜 j) :
    Proj.toTwistingSheaf 𝒜 h ⊤ (c • p)=c • Proj.toTwistingSheaf 𝒜 h ⊤ p := by
  apply Proj.twistingSheaf.ext
  intro x
  rw [Scheme.Modules.base_smul_globalSections]
  refine Eq.trans ?_ (Proj.twistingSheaf.smul_apply _ _ x).symm
  erw [val_baseRingToGlobalSections_apply,Proj.toTwistingSheaf_apply_apply,
    Proj.toTwistingSheaf_apply_apply,Localization.mk_mul,one_mul,Submodule.coe_smul,
    Algebra.smul_def]
  rfl

/-- The full global-section computation is linear for the actual coefficient-field structure. -/
def homogeneousGlobalSectionsLinearEquiv (j : ℕ) [Nonempty I] :
    𝒜 j ≃ₗ[K] Γ(Proj.twistingSheaf 𝒜 j,⊤) :=
  LinearEquiv.ofBijective
    { toFun := Proj.toTwistingSheaf 𝒜 (rfl : (j : ℤ)=j) ⊤
      map_add' := map_add _
      map_smul' := toTwistingSheaf_top_smul rfl }
    (bijective_toTwistingSheaf_top j)

@[simp] theorem homogeneousGlobalSectionsLinearEquiv_apply (j : ℕ) [Nonempty I]
    (p : 𝒜 j) : homogeneousGlobalSectionsLinearEquiv j p=Proj.toTwistingSheaf 𝒜 rfl ⊤ p := rfl

end PaperVerification.Segre.ProjectiveGlobalSections

end SegreProjectiveGlobalSections

section SegreEulerLocal

/-!
# The exterior Euler sequence on actual coordinate localizations

On an intersection containing the chart `Xⱼ ≠ 0`, the coordinate functional
`(vᵢ) ↦ Σ Xᵢvᵢ` has the literal right inverse `Xⱼ⁻¹ eⱼ`. Its kernel is the
local tautological hyperplane. Every exterior power of that actual kernel
is identified with the corresponding literal coordinate Koszul cycles,
and all positive Koszul degrees are exact. These are local statements on
the actual coordinate rings; global sheaf gluing is a separate obligation.
-/

set_option autoImplicit false



namespace PaperVerification.Segre.EulerLocal

open CoordinateLocalization SplitKoszul TauCeti
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

/-- The actual coordinate function in the coordinate localization. -/
def coordinate (S : Finset I) (i : I) : LocalLaurent K I S :=
  localizationMap S (MvPolynomial.X i)

/-- The exponent of the reciprocal of one inverted coordinate. -/
def inverseCoordinateExponent (S : Finset I) (j : I) (hj : j∈S) : allowedExponents S :=
  ⟨fun i => if i=j then -1 else 0,by
    intro i hi
    have hij : i≠j := by rintro rfl; exact hi hj
    simp only [if_neg hij,le_refl]⟩

def inverseCoordinate (S : Finset I) (j : I) (hj : j∈S) : LocalLaurent K I S :=
  AddMonoidAlgebra.single (inverseCoordinateExponent S j hj) 1

theorem coordinate_mul_inverse (S : Finset I) (j : I) (hj : j∈S) :
    coordinate (K := K) S j*inverseCoordinate S j hj=1 := by
  change AddMonoidAlgebra.mapDomain (naturalExponentMap S)
      (AddMonoidAlgebra.single (Finsupp.single j 1) (1 : K)) *
        AddMonoidAlgebra.single (inverseCoordinateExponent S j hj) 1=1
  rw [AddMonoidAlgebra.mapDomain_single,AddMonoidAlgebra.single_mul_single,one_mul]
  have he : naturalExponentMap S (Finsupp.single j 1)+inverseCoordinateExponent S j hj=0 := by
    apply Subtype.ext
    funext i
    simp only [AddSubmonoid.coe_add,Pi.add_apply,naturalExponentMap,inverseCoordinateExponent,
      Finsupp.single_apply]
    by_cases hi : i=j
    · subst i; simp
    · simp [hi,Ne.symm hi]
  rw [he,← AddMonoidAlgebra.one_def]

/-- The literal coordinate functional of the Euler sequence. -/
def coordinateFunctional (S : Finset I) :
    Module.Dual (LocalLaurent K I S) (I → LocalLaurent K I S) where
  toFun v := ∑ i, coordinate S i*v i
  map_add' v w := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The actual local splitting vector. -/
def splittingVector (S : Finset I) (j : I) (hj : j∈S) : I → LocalLaurent K I S :=
  Pi.single j (inverseCoordinate S j hj)

@[simp] theorem coordinateFunctional_splittingVector (S : Finset I) (j : I) (hj : j∈S) :
    coordinateFunctional (K := K) S (splittingVector S j hj)=1 := by
  change (∑ i, coordinate S i * splittingVector S j hj i) = 1
  simp only [splittingVector, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp only [if_pos rfl]
    exact coordinate_mul_inverse S j hj
  · intro i _ hij
    simp [hij,Ne.symm hij]
  · intro hj0
    exact (hj0 (Finset.mem_univ j)).elim

abbrev EulerKernel (S : Finset I) := LinearMap.ker (coordinateFunctional (K := K) S)

/-- Every exterior degree of the actual local tautological hyperplane is exactly the
corresponding coordinate contraction kernel. -/
def exteriorEulerKernelEquiv (S : Finset I) (j : I) (hj : j∈S) (n : ℕ) :
    ⋀[LocalLaurent K I S]^(n+1) (EulerKernel (K := K) S) ≃ₗ[LocalLaurent K I S]
      LinearMap.ker (koszulDifferential (coordinateFunctional (K := K) S) n) :=
  exteriorKernelEquiv (coordinateFunctional S) (splittingVector S j hj)
    (coordinateFunctional_splittingVector S j hj) n

/-- The coordinate Koszul complex is exact in every positive degree on every actual chart intersection. -/
theorem coordinate_koszul_exact (S : Finset I) (hS : S.Nonempty) (n : ℕ) :
    Function.Exact (koszulDifferential (coordinateFunctional (K := K) S) (n+1))
      (koszulDifferential (coordinateFunctional (K := K) S) n) := by
  obtain ⟨j,hj⟩ := hS
  exact exact_koszul_of_unit_value (coordinateFunctional S) (splittingVector S j hj)
    (coordinateFunctional_splittingVector S j hj) n

end PaperVerification.Segre.EulerLocal

end SegreEulerLocal

end SegreProjectiveCohomology

end
end
end ProbeLayer391

/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
