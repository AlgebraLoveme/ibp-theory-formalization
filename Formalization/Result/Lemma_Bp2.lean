module
public import Formalization.Result.helpers.Lemma_Bp2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Axioms

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Lemma_Bp2

theorem gamma_ratio_growth :
    let g := fun s : ℝ => s * Real.Gamma (s / 2) /
      (Real.sqrt Real.pi * Real.Gamma ((s + 1) / 2))
    StrictMonoOn g (Set.Ici 1) ∧ MonotoneOn g (Set.Ici 1) ∧
    g 2 = 4 / Real.pi ∧ (127 / 100 : ℝ) < g 2 ∧
    (∀ s, 2 ≤ s → g 2 ≤ g s) := (by
  -- formalizer:proof-begin
  dsimp only
  let ψ := fun x : ℝ => deriv Real.Gamma x / Real.Gamma x
  let g := fun s : ℝ => s * Real.Gamma (s / 2) /
    (Real.sqrt Real.pi * Real.Gamma ((s + 1) / 2))
  -- Lemma B.2: differentiate the quotient; the gamma prefactor is positive.
  have hd := Machinery.ratio_derivative
  have hpos (s : ℝ) (hs : 1 ≤ s) : 0 < deriv g s := by
    have hs0 : 0 < s := by linarith
    rw [(hd s hs0).deriv]
    apply mul_pos
    · exact div_pos (external_gamma.1 _ (by positivity)).1
        (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (external_gamma.1 _ (by positivity)).1)
    -- Compare ψ((s+1)/2) with ψ(s/2+1), then use ψ(x+1)=ψ(x)+1/x.
    have hc := external_gamma.2.1 (show 0 < (s + 1) / 2 by positivity)
      (show 0 < s / 2 + 1 by positivity) (show (s + 1) / 2 < s / 2 + 1 by linarith)
    have hr := external_gamma.2.2.1 (s / 2) (by positivity)
    change ψ ((s + 1) / 2) < ψ (s / 2 + 1) at hc
    change ψ (s / 2 + 1) = ψ (s / 2) + 1 / (s / 2) at hr
    rw [hr] at hc
    have hm := mul_lt_mul_of_pos_left hc (show 0 < s / 2 by positivity)
    have hi : s / 2 * (1 / (s / 2)) = 1 := by field_simp
    change 0 < 1 + s / 2 * (ψ (s / 2) - ψ ((s + 1) / 2))
    nlinarith
  -- The mean value theorem on [1,∞) yields strict increase, hence monotonicity.
  have hmono : StrictMonoOn g (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro s hs
      exact (hd s (by have := hs; simp only [Set.mem_Ici] at this; linarith)).continuousAt.continuousWithinAt
    · intro s hs
      exact hpos s (interior_subset hs)
  -- Gamma(1)=1 and Gamma(3/2)=(1/2)sqrt(π) give the exact value at 2.
  have hv : g 2 = 4 / Real.pi := by
    have hr := external_gamma.2.2.2.1 (1 / 2) (by norm_num)
    have hhalf := external_gamma.2.2.2.2.2.1
    dsimp [g]
    norm_num at hr ⊢
    rw [hr, hhalf]
    have hsq := Real.sq_sqrt Real.pi_pos.le
    have hp := Real.pi_pos.ne'
    have hq := (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp
    nlinarith
  -- The elementary bound π<22/7 implies the stated decimal lower bound.
  have hpi : Real.pi < 22 / 7 := by linarith [Real.pi_lt_d4]
  have hnum : (127 / 100 : ℝ) < g 2 := by
    rw [hv]
    apply (lt_div_iff₀ Real.pi_pos).mpr
    linarith
  exact ⟨hmono, hmono.monotoneOn, hv, hnum,
    fun s hs => hmono.monotoneOn (by norm_num) (by change 1 ≤ s; linarith) hs⟩
  -- formalizer:proof-end
)
end Lemma_Bp2
