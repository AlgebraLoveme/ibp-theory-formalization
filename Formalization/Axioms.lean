module
public import Formalization.Definition
public import Mathlib

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Axioms

/-- The reviewed positive-real gamma/digamma boundary. -/
axiom external_gamma :
  let ψ := fun x : ℝ => deriv Real.Gamma x / Real.Gamma x
  (∀ x, 0 < x → 0 < Real.Gamma x ∧ DifferentiableAt ℝ Real.Gamma x) ∧
  StrictMonoOn ψ (Set.Ioi 0) ∧
  (∀ x, 0 < x → ψ (x + 1) = ψ x + 1 / x) ∧
  (∀ x, 0 < x → Real.Gamma (x + 1) = x * Real.Gamma x) ∧
  Real.Gamma 1 = 1 ∧ Real.Gamma (1 / 2) = Real.sqrt Real.pi ∧
  (∀ a : ℝ, Tendsto
    (fun x : ℝ => (Real.Gamma (x + a) / Real.Gamma x) / x ^ a)
    atTop (nhds 1))

/-- General normal and chi moments, linear combinations, and sign symmetry. -/
axiom external_gaussian_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (Z : Fin n → Ω → ℝ) (hZ : ∀ j, HasLaw (Z j) (gaussianReal 0 1) μ)
    (hInd : iIndepFun Z μ) :
  (∀ j, Integrable (fun ω => |Z j ω|) μ ∧
    Integrable (fun ω => Z j ω ^ 2) μ ∧
    Integrable (fun ω => Z j ω ^ 4) μ ∧
    (∫ ω, |Z j ω| ∂μ) = Real.sqrt (2 / Real.pi) ∧
    (∫ ω, Z j ω ^ 2 ∂μ) = 1 ∧ (∫ ω, Z j ω ^ 4 ∂μ) = 3) ∧
  (∀ a : Fin n → ℝ,
    HasLaw (fun ω => ∑ j, a j * Z j ω)
      (gaussianReal 0 (∑ j, (Real.toNNReal (a j ^ 2)))) μ) ∧
  (∀ a : Fin n → ℝ, a ≠ 0 → ∀ t : ℝ,
    μ {ω | (∑ j, a j * Z j ω) = t} = 0) ∧
  μ.map (fun ω j => Z j ω) = μ.map (fun ω j => -Z j ω) ∧
  Integrable (fun ω => Real.sqrt (∑ j, Z j ω ^ 2)) μ ∧
  (∫ ω, Real.sqrt (∑ j, Z j ω ^ 2) ∂μ) =
    if n = 0 then 0 else
      Real.sqrt 2 * Real.Gamma (((n : ℝ) + 1) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- Normalized normal sampling of the uniform sphere, with independent radius.
Uniformity is expressed by unit-sphere support and orthogonal invariance. -/
axiom external_sphere {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (Z : Fin n → Ω → ℝ) (hZ : ∀ j, HasLaw (Z j) (gaussianReal 0 1) μ)
    (hInd : iIndepFun Z μ) :
  let r := fun ω => Real.sqrt (∑ j, Z j ω ^ 2)
  let s := fun ω j => Z j ω / r ω
  (∀ᵐ ω ∂μ, ∑ j, s ω j ^ 2 = 1) ∧
  IndepFun r s μ ∧
  (∀ V : Matrix (Fin n) (Fin n) ℝ,
    V.transpose * V = 1 → V * V.transpose = 1 →
    μ.map (fun ω i => ∑ j, V i j * s ω j) = μ.map s)

/-- Only the Gaussian-square strong law and bounded-L² expectation convergence
used in the reconstruction limit cross this probability boundary. -/
axiom external_probability_limits {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
  (∀ Z : ℕ → Ω → ℝ, (∀ j, HasLaw (Z j) (gaussianReal 0 1) μ) →
    iIndepFun Z μ →
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, Z j ω ^ 2) / (n : ℝ))
      atTop (nhds 1)) ∧
  (∀ (Y : ℕ → Ω → ℝ) (Ylim : Ω → ℝ) (C : ℝ),
    (∀ n, Integrable (Y n) μ ∧ Integrable (fun ω => Y n ω ^ 2) μ) →
    AEMeasurable Ylim μ →
    (∀ n, (∫ ω, Y n ω ^ 2 ∂μ) ≤ C) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Ylim ω))) →
    Integrable Ylim μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop (nhds (∫ ω, Ylim ω ∂μ)))

end Axioms
