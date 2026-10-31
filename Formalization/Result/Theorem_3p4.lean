module
public import Formalization.Result.helpers.Theorem_3p4.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_3p3

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Theorem_3p4

theorem non_pi_sign_rectangle (d : Fin 3 → ℕ) (hd : ∀ k, 0 < d k)
    (W : ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (i i' : Fin (d 2)) (j j' : Fin (d 0))
    (hne : ∀ k, W 0 k j ≠ 0 ∧ W 0 k j' ≠ 0 ∧ W 1 i k ≠ 0 ∧ W 1 i' k ≠ 0)
    (hneg : linear_network.F(linear_network 2 d W) i j * linear_network.F(linear_network 2 d W) i j' *
      linear_network.F(linear_network 2 d W) i' j * linear_network.F(linear_network 2 d W) i' j' < 0) :
    ¬ propagation_invariance 2 d W := (by
  -- formalizer:proof-begin
  intro hpi
  let k : Fin (d 1) := ⟨0, hd 1⟩
  -- Lemma 3.3 gives one weak sign at each position. A nonzero path
  -- then has strictly positive product with its end-to-end sum.
  have hs := (Lemma_3p3.pi_characterization d hd W).2.mp hpi
  have coeff := Machinery.network_product d W
  have aligned (r : Fin (d 2)) (s : Fin (d 0))
      (hn : W 1 r k * W 0 k s ≠ 0) :
      0 < linear_network.F(linear_network 2 d W) r s * (W 1 r k * W 0 k s) := by
    rw [coeff]
    change 0 < (∑ t : Fin (d 1), W 1 r t * W 0 t s) * (W 1 r k * W 0 k s)
    exact Machinery.sum_mul_path_pos
      (fun t => W 1 r t * W 0 t s) k hn (hs r s)
  obtain ⟨ha, hb, hc, he⟩ := hne k
  have h₁ := aligned i j (mul_ne_zero hc ha)
  have h₂ := aligned i j' (mul_ne_zero hc hb)
  have h₃ := aligned i' j (mul_ne_zero he ha)
  have h₄ := aligned i' j' (mul_ne_zero he hb)
  -- At the fixed hidden index, the four paths multiply to
  -- (W₂ᵢₖ W₂ᵢ'ₖ W₁ₖⱼ W₁ₖⱼ')² > 0 (Theorem 3.4).
  let q := W 1 i k * W 1 i' k * W 0 k j * W 0 k j'
  have hq : 0 < q ^ 2 := sq_pos_of_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hc he) ha) hb)
  have hp := mul_pos (mul_pos (mul_pos h₁ h₂) h₃) h₄
  have rearrange :
      (linear_network.F(linear_network 2 d W) i j * (W 1 i k * W 0 k j)) *
      (linear_network.F(linear_network 2 d W) i j' * (W 1 i k * W 0 k j')) *
      (linear_network.F(linear_network 2 d W) i' j * (W 1 i' k * W 0 k j)) *
      (linear_network.F(linear_network 2 d W) i' j' * (W 1 i' k * W 0 k j')) =
      (linear_network.F(linear_network 2 d W) i j * linear_network.F(linear_network 2 d W) i j' *
      linear_network.F(linear_network 2 d W) i' j * linear_network.F(linear_network 2 d W) i' j') * q ^ 2 := by
    dsimp [q]
    ring
  rw [rearrange] at hp
  -- The negative product of end-to-end entries contradicts this positivity.
  exact (not_lt_of_ge (le_of_lt hp)) (mul_neg_of_neg_of_pos hneg hq)
  -- formalizer:proof-end
)
end Theorem_3p4
