module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Theorem_3p2.Machinery

-- formalizer:machinery-begin
lemma layer_endpoints {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    (Definition.boxes c r (fun z => A.mulVec z)).2.1 =
      (A.mulVec c - (A.map abs).mulVec r, A.mulVec c + (A.map abs).mulVec r) := by
  apply Prod.ext
  · funext i
    exact (Lemma_Bp1.Machinery.row_extrema
      (A i) c r hr).1
  · funext i
    exact (Lemma_Bp1.Machinery.row_extrema
      (A i) c r hr).2

lemma endpoint_center {n : ℕ} (c r : Fin n → ℝ) :
    (fun i => ((c + r) i + (c - r) i) / 2) = c := by
  funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring

lemma endpoint_radius {n : ℕ} (c r : Fin n → ℝ) :
    (fun i => ((c + r) i - (c - r) i) / 2) = r := by
  funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring

lemma absolute_mulVec_nonneg {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) : ∀ i, 0 ≤ (A.map abs).mulVec r i := by
  intro i
  change 0 ≤ Finset.univ.sum (fun j => |A i j| * r j)
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hr j))

-- formalizer:machinery-end

end Theorem_3p2.Machinery
