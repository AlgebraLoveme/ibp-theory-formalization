module
public import Formalization.Result.helpers.Lemma_3p3.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_Bp1

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Lemma_3p3

theorem pi_characterization (d : Fin 3 → ℕ) (hd : ∀ k, 0 < d k)
    (W : ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ) :
    (propagation_invariance 2 d W ↔
      ∀ (i : Fin (d 2)) (j : Fin (d 0)),
        |∑ k, W 1 i k * W 0 k j| = ∑ k, |W 1 i k * W 0 k j|) ∧
    (propagation_invariance 2 d W ↔
      ∀ (i : Fin (d 2)) (j : Fin (d 0)),
        (∀ k, 0 ≤ W 1 i k * W 0 k j) ∨ (∀ k, W 1 i k * W 0 k j ≤ 0)) := (by
  -- formalizer:proof-begin
  classical
  let N := linear_network 2 d W
  have coeff := Machinery.network_coefficients d W
  have first : propagation_invariance 2 d W ↔
      ∀ (i : Fin (d 2)) (j : Fin (d 0)),
        |∑ k, W 1 i k * W 0 k j| = ∑ k, |W 1 i k * W 0 k j| := by
    constructor
    · intro h i j
      -- Lemma B.1 gives the radii. Testing a coordinate unit radius
      -- recovers each entry of the optimal and sequential radius matrices.
      let e : Fin (d 0) → ℝ := fun t => if t = j then 1 else 0
      have he : ∀ t, 0 ≤ e t := by intro t; dsimp [e]; split_ifs <;> norm_num
      have hb := Lemma_Bp1.two_layer_boxes d hd W 0 e he
      have hp := h 0 e he
      have hr : N.2.1.mulVec e = N.2.2.1.mulVec e := by
        rw [← hb.2.2.1, ← hb.2.2.2]
        exact congrArg (fun p : (Fin (d 2) → ℝ) × (Fin (d 2) → ℝ) =>
          (p.2 - p.1) / 2) hp
      have hi := congrFun hr i
      rw [coeff.1, coeff.2] at hi
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply,
        e, abs_mul] using hi
    · intro h x e he
      -- Equal path coefficients give equal radii for every nonnegative e;
      -- Lemma B.1 gives equal centers, hence both endpoints agree.
      have hb := Lemma_Bp1.two_layer_boxes d hd W x e he
      have hm : N.2.1 = N.2.2.1 := by
        rw [coeff.1, coeff.2]
        ext i j
        simpa [Matrix.mul_apply, Matrix.map_apply, abs_mul] using h i j
      apply Machinery.endpoints_eq
      · exact hb.1.trans hb.2.1.symm
      · exact hb.2.2.1.trans ((congrArg (fun A => A.mulVec e) hm).trans hb.2.2.2.symm)
  refine ⟨first, first.trans ?_⟩
  -- In the triangle equality, split each path into positive and negative
  -- parts p and q. Then |p-q| = p+q forces p=0 or q=0.
  have scalar {n : ℕ} (a : Fin n → ℝ) :
      |∑ k, a k| = ∑ k, |a k| ↔ (∀ k, 0 ≤ a k) ∨ (∀ k, a k ≤ 0) := by
    constructor
    · intro h
      have hs := Machinery.signed_sum_decomposition a
      rw [hs.1, hs.2] at h
      have hp : 0 ≤ ∑ k, max (a k) 0 := Finset.sum_nonneg (fun k _ => le_max_right _ _)
      have hq : 0 ≤ ∑ k, max (-a k) 0 := Finset.sum_nonneg (fun k _ => le_max_right _ _)
      rcases le_total 0 ((∑ k, max (a k) 0) - (∑ k, max (-a k) 0)) with hs | hs
      · rw [abs_of_nonneg hs] at h
        have hz : (∑ k, max (-a k) 0) = 0 := by linarith
        have hh := Machinery.nonpos_of_positive_sum_zero (fun k => -a k) hz
        exact Or.inl (fun k => neg_nonpos.mp (hh k))
      · rw [abs_of_nonpos hs] at h
        have hz : (∑ k, max (a k) 0) = 0 := by linarith
        exact Or.inr (Machinery.nonpos_of_positive_sum_zero a hz)
    · rintro (h | h)
      · rw [abs_of_nonneg (Finset.sum_nonneg (fun k _ => h k))]
        exact Finset.sum_congr rfl (fun k _ => (abs_of_nonneg (h k)).symm)
      · rw [abs_of_nonpos (Finset.sum_nonpos (fun k _ => h k)), ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun k _ => (abs_of_nonpos (h k)).symm)
  -- A zero sum of nonnegative parts means every such part vanishes.
  -- Thus all paths have one weak sign; conversely either sign gives equality.
  constructor
  · intro h i j; exact (scalar (fun k => W 1 i k * W 0 k j)).mp (h i j)
  · intro h i j; exact (scalar (fun k => W 1 i k * W 0 k j)).mpr (h i j)
  -- formalizer:proof-end
)
end Lemma_3p3
