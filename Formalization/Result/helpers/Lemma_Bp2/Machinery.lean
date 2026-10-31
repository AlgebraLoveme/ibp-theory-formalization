module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Lemma_Bp2.Machinery

-- formalizer:machinery-begin
lemma ratio_derivative (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => t * Real.Gamma (t / 2) /
      (Real.sqrt Real.pi * Real.Gamma ((t + 1) / 2)))
      (Real.Gamma (s / 2) / (Real.sqrt Real.pi * Real.Gamma ((s + 1) / 2)) *
        (1 + s / 2 * (deriv Real.Gamma (s / 2) / Real.Gamma (s / 2) -
          deriv Real.Gamma ((s + 1) / 2) / Real.Gamma ((s + 1) / 2)))) s := by
  have ha := Axioms.external_gamma.1 (s / 2) (by positivity)
  have hb := Axioms.external_gamma.1 ((s + 1) / 2) (by positivity)
  have hq : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have da := ha.2.hasDerivAt.comp s ((hasDerivAt_id s).div_const 2)
  have db := hb.2.hasDerivAt.comp s (((hasDerivAt_id s).add_const 1).div_const 2)
  convert ((hasDerivAt_id s).mul da).div (db.const_mul (Real.sqrt Real.pi))
    (mul_ne_zero hq hb.1.ne') using 1 <;> dsimp
  field_simp
  <;> ring

-- formalizer:machinery-end

end Lemma_Bp2.Machinery
