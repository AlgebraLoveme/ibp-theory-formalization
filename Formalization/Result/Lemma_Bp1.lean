module
public import Formalization.Result.helpers.Lemma_Bp1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Lemma_Bp1

theorem two_layer_boxes (d : Fin 3 → ℕ) (hd : ∀ k, 0 < d k)
    (W : ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (x e : Fin (d 0) → ℝ) (he : ∀ j, 0 ≤ e j) :
    let N := linear_network 2 d W
    let p := N.2.2.2 x e
    (p.1.2 + p.1.1) / 2 = linear_network.F(N).mulVec x ∧
    (p.2.2 + p.2.1) / 2 = linear_network.F(N).mulVec x ∧
    (p.1.2 - p.1.1) / 2 = N.2.1.mulVec e ∧
    (p.2.2 - p.2.1) / 2 = N.2.2.1.mulVec e := (by
  -- formalizer:proof-begin
  classical
  -- Equation (pf1-1): each row is bounded by its absolute weighted radius;
  -- the two sign-selected corners attain the bounds, including zero radii.
  have layer {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
      (c r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
      (boxes c r (fun z => A.mulVec z)).2.1 =
        (A.mulVec c - (A.map abs).mulVec r, A.mulVec c + (A.map abs).mulVec r) := by
    apply Prod.ext
    · funext i
      exact (Machinery.row_extrema
        (A i) c r hr).1
    · funext i
      exact (Machinery.row_extrema
        (A i) c r hr).2
  have center {n : ℕ} (c r : Fin n → ℝ) :
      (fun i => ((c + r) i + (c - r) i) / 2) = c := by
    funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have radius {n : ℕ} (c r : Fin n → ℝ) :
      (fun i => ((c + r) i - (c - r) i) / 2) = r := by
    funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W 0
  let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
  have hfirst : ∀ i, 0 ≤ (A.map abs).mulVec e i := by
    intro i
    change 0 ≤ ∑ j, |A i j| * e j
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (he j))
  -- Equation (pf1-2): take the first hull, then propagate its center and
  -- nonnegative radius through the second layer.
  have first := layer A x e he
  have second := layer B (A.mulVec x) ((A.map abs).mulVec e) hfirst
  -- Equation (pf1-3): apply the same row computation to the composed map.
  have optimal := layer (B * A) x e he
  let p := (boxes x e (fun z => (B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).mulVec z)).2.1
  let q := (boxes
    (fun i => (boxes.hi(boxes (fun j => ((x + e) j + (x - e) j) / 2)
      (fun j => ((x + e) j - (x - e) j) / 2) (fun z => A.mulVec z)) i +
      boxes.lo(boxes (fun j => ((x + e) j + (x - e) j) / 2)
      (fun j => ((x + e) j - (x - e) j) / 2) (fun z => A.mulVec z)) i) / 2)
    (fun i => (boxes.hi(boxes (fun j => ((x + e) j + (x - e) j) / 2)
      (fun j => ((x + e) j - (x - e) j) / 2) (fun z => A.mulVec z)) i -
      boxes.lo(boxes (fun j => ((x + e) j + (x - e) j) / 2)
      (fun j => ((x + e) j - (x - e) j) / 2) (fun z => A.mulVec z)) i) / 2)
    (fun z => B.mulVec z)).2.1
  change (p.2 + p.1) / 2 = (B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).mulVec x ∧
    (q.2 + q.1) / 2 = (B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).mulVec x ∧
    (p.2 - p.1) / 2 = ((B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).map abs).mulVec e ∧
    (q.2 - q.1) / 2 = (B.map abs * (A.map abs * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).mulVec e
  dsimp only [p, q]
  simp only [Matrix.mul_one, center, radius, first, second, optimal]
  -- Matrix multiplication rearranges the finite path sums in (pf1-2).
  -- Taking half-sums and half-differences recovers the asserted centers/radii.
  simp only [← Matrix.mulVec_mulVec]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;>
    simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.ofNat_apply] <;> ring
  -- formalizer:proof-end
)
end Lemma_Bp1
