module
public import Mathlib

@[expose] public section

open scoped BigOperators NNReal
open MeasureTheory

namespace Definition

/-- Full input box, optimal endpoints, optimal center/radius, and optimal box.
The geometric domain is `0 ≤ e`; extrema describe continuous maps on this box.
The definitions are totalized outside that domain using real infima and suprema. -/
noncomputable def boxes {n m : ℕ} (x e : Fin n → ℝ)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) :
    Set (Fin n → ℝ) × ((Fin m → ℝ) × (Fin m → ℝ)) ×
      ((Fin m → ℝ) × (Fin m → ℝ)) × Set (Fin m → ℝ) :=
  let B := {z | ∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j}
  let lo := fun i => sInf ((fun z => f z i) '' B)
  let hi := fun i => sSup ((fun z => f z i) '' B)
  (B, (lo, hi), ((hi + lo) / 2, (hi - lo) / 2),
    {z | ∀ i, lo i ≤ z i ∧ z i ≤ hi i})

/-- A finite factorization. The returned data are `F`, `O`, `Q`, and the
optimal/sequential endpoint functions. Positive widths and `L ≥ 1` are the
network domain. The recursion takes hulls, without assuming a radius formula. -/
noncomputable def linear_network (L : ℕ) (d : Fin (L + 1) → ℕ)
    (W : ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ) :
    Matrix (Fin (d (Fin.last L))) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ ×
    Matrix (Fin (d (Fin.last L))) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ ×
    Matrix (Fin (d (Fin.last L))) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ ×
    ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) → (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) →
      ((Fin (d (Fin.last L)) → ℝ) × (Fin (d (Fin.last L)) → ℝ)) ×
      ((Fin (d (Fin.last L)) → ℝ) × (Fin (d (Fin.last L)) → ℝ))) := by
  classical
  let prod := Nat.rec
    (motive := fun k => (hk : k ≤ L) → Bool →
      Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
    (fun _ _ => 1)
    (fun k ih hk a =>
      let w := W ⟨k, by omega⟩
      fun i j => ∑ t, (if a then |w i t| else w i t) * ih (by omega) a t j)
  let seq := Nat.rec
    (motive := fun k => (hk : k ≤ L) →
      (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) →
      (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) →
      (Fin (d ⟨k, by omega⟩) → ℝ) × (Fin (d ⟨k, by omega⟩) → ℝ))
    (fun _ x e => (x - e, x + e))
    (fun k ih hk x e =>
      let p := ih (by omega) x e
      (boxes (fun i => (p.2 i + p.1 i) / 2) (fun i => (p.2 i - p.1 i) / 2)
        (fun z => (W ⟨k, by omega⟩).mulVec z)).2.1)
  let F := prod L le_rfl false
  exact (F, F.map abs, prod L le_rfl true,
    fun x e => ((boxes x e (fun z => F.mulVec z)).2.1, seq L le_rfl x e))

/-- Unique winning class, with the difference map and its negative orthant.
The subtype of competing labels is empty for a one-class classifier. -/
def robust_classification {n c : ℕ} (y : (Fin n → ℝ) → (Fin c → ℝ))
    (t : Fin c) (x e : Fin n → ℝ) :
    ((Fin n → ℝ) → ({i : Fin c // i ≠ t} → ℝ)) × Prop ×
      Set ({i : Fin c // i ≠ t} → ℝ) :=
  (fun z i => y z i - y z t,
    ∀ z, (∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j) →
      ∀ i, i ≠ t → y z i < y z t,
    {v | ∀ i, v i < 0})

/-- Equality of geometric endpoint boxes for every full input box. -/
noncomputable def propagation_invariance (L : ℕ) (d : Fin (L + 1) → ℕ)
    (W : ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ) : Prop :=
  ∀ x e, (∀ j, 0 ≤ e j) →
    ((linear_network L d W).2.2.2 x e).1 = ((linear_network L d W).2.2.2 x e).2

/-- Coordinate ratios on their positive-denominator domains, separately for
samples and expectations, followed by the scalar functions `t` and `g`.
Random radii are supplied as random variables, allowing deterministic input
boxes and also the local ReLU growth rates to use the expectation operation. -/
noncomputable def propagation_tightness {Ω : Type*} [MeasurableSpace Ω]
    {m : ℕ} (μ : Measure Ω) (r s : Fin m → ℝ)
    (R S : Ω → Fin m → ℝ) :
    ({i : Fin m // 0 < s i} → ℝ) ×
    ({i : Fin m // 0 < ∫ ω, S ω i ∂μ} → ℝ) ×
    ({n : ℕ // 1 ≤ n} → ℝ) × ({u : ℝ // 1 ≤ u} → ℝ) :=
  (fun i => r i / s i,
   fun i => (∫ ω, R ω i ∂μ) / (∫ ω, S ω i ∂μ),
   fun n => Real.sqrt Real.pi * Real.Gamma (((n.val : ℝ) + 1) / 2) /
     ((n.val : ℝ) * Real.Gamma ((n.val : ℝ) / 2)),
   fun u => u.val * Real.Gamma (u.val / 2) /
     (Real.sqrt Real.pi * Real.Gamma ((u.val + 1) / 2)))

/-- Independent centered Gaussian entries with positive layer standard
 deviations. The second component is the additional input-law condition for
 the ReLU initialization result; it is not imposed on deterministic DLN inputs. -/
noncomputable def gaussian_initialization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : ℕ) (d : Fin (L + 1) → ℕ)
    (σ : Fin L → ℝ≥0)
    (W : Ω → ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (X : Ω → Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) : Prop × Prop := by
  let entry := fun (p : Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc))
    (ω : Ω) => W ω p.1 p.2.1 p.2.2
  exact
    (IsProbabilityMeasure μ ∧ 1 ≤ L ∧ (∀ k, 0 < d k) ∧ (∀ k, 0 < σ k) ∧
      ProbabilityTheory.iIndepFun entry μ ∧
      (∀ p, ProbabilityTheory.HasLaw (entry p)
        (ProbabilityTheory.gaussianReal 0 ((σ p.1) ^ 2)) μ),
     AEMeasurable X μ ∧ ProbabilityTheory.IndepFun X (fun ω p => entry p ω) μ ∧
       μ.map X = μ.map (fun ω => -X ω) ∧ μ {ω | X ω = 0} = 0)

/-- ReLU evaluation with a linear last layer. Components are the nonzero
hidden-preactivation domain, masks (the last mask is one), radius functions,
their right derivatives at zero, and the partial coordinate ratio. -/
noncomputable def relu_local_radii (L : ℕ) (d : Fin (L + 1) → ℕ)
    (W : ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (b : ∀ k : Fin L, Fin (d k.succ) → ℝ) (x : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) :
    Prop × (∀ k : Fin L, Fin (d k.succ) → ℝ) ×
    (ℝ → (Fin (d (Fin.last L)) → ℝ) × (Fin (d (Fin.last L)) → ℝ)) ×
    ((Fin (d (Fin.last L)) → ℝ) × (Fin (d (Fin.last L)) → ℝ)) ×
    (Fin (d (Fin.last L)) → Option ℝ) := by
  classical
  let layer : ∀ k : Fin L, (Fin (d k.castSucc) → ℝ) → (Fin (d k.succ) → ℝ) :=
    fun k z =>
    fun i => if k.val + 1 < L then max 0 ((W k).mulVec z i + b k i)
      else (W k).mulVec z i + b k i
  let eval := Nat.rec
    (motive := fun k => (hk : k ≤ L) →
      (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) → Fin (d ⟨k, by omega⟩) → ℝ)
    (fun _ z => z)
    (fun k ih hk z => layer ⟨k, by omega⟩ (ih (by omega) z))
  let seq := Nat.rec
    (motive := fun k => (hk : k ≤ L) → ℝ →
      (Fin (d ⟨k, by omega⟩) → ℝ) × (Fin (d ⟨k, by omega⟩) → ℝ))
    (fun _ ε => ((fun i => x i - ε), (fun i => x i + ε)))
    (fun k ih hk ε =>
      let p := ih (by omega) ε
      (boxes (fun i => (p.2 i + p.1 i) / 2) (fun i => (p.2 i - p.1 i) / 2)
        (layer ⟨k, by omega⟩)).2.1)
  let pre := fun (k : Fin L) =>
    (W k).mulVec (eval k.val (Nat.le_of_lt k.isLt) x) + b k
  let radii := fun ε =>
    let p := seq L le_rfl ε
    ((boxes x (fun _ => ε) (eval L le_rfl)).2.2.1.2, (p.2 - p.1) / 2)
  let r := fun i => derivWithin (fun ε => (radii ε).1 i) (Set.Ioi 0) 0
  let s := fun i => derivWithin (fun ε => (radii ε).2 i) (Set.Ioi 0) 0
  exact
    (1 ≤ L ∧ (∀ k, 0 < d k) ∧ (∀ k : Fin L, k.val + 1 < L → ∀ i, pre k i ≠ 0),
     fun k i => if k.val + 1 < L then (if 0 < pre k i then 1 else 0) else 1,
     radii, (r, s), fun i => if 0 < s i then some (r i / s i) else none)

/-- Risk as a function of input radius, its source domain and local homogeneous
tightness assumptions, and the maximum optimal row sum. Parameters are exactly
the finite collection of weight entries, with their Euclidean inner product.
The data measure is fixed independently of those parameters. -/
noncomputable def ibp_training_risk (L : ℕ) (d : Fin (L + 1) → ℕ)
    (μ : Measure ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))))
    (τ : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) → ℝ)
    (θ : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc))) :
    ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) → ℝ) × Prop × ℝ := by
  classical
  let net := fun (p : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc))) =>
    linear_network L d (fun k i j => p ⟨k, i, j⟩)
  let F := fun p => (net p).1
  let O := fun p => (net p).2.1
  let Q := fun p => (net p).2.2.1
  let risk := fun e => ∫ xy,
    Real.log (1 + ∑ i ∈ Finset.univ.erase xy.2,
      Real.exp ((F θ).mulVec xy.1 i - (F θ).mulVec xy.1 xy.2 +
        (Q θ).mulVec e i + (Q θ).mulVec e xy.2)) ∂μ
  exact (risk,
    1 ≤ L ∧ (∀ k, 0 < d k) ∧ IsProbabilityMeasure μ ∧
      (∀ᵐ xy ∂μ, ∀ j, |xy.1 j| ≤ 1) ∧
      DifferentiableAt ℝ O θ ∧ DifferentiableAt ℝ Q θ ∧
      (∀ i j, 0 < Q θ i j) ∧
      (∃ s, IsOpen s ∧ θ ∈ s ∧ DifferentiableOn ℝ τ s ∧
        ∀ p ∈ s, 0 < τ p ∧ ∀ i j, O p i j = τ p * Q p i j),
    sSup (Set.range (fun i => ∑ j, O θ i j)))

/-- Haar-uniformity is expressed by probability, orthogonal support and
invariance under every left orthogonal translation. The remaining components
are the first columns, encoding, projector, reconstructed center, and the
geometrically defined optimal and sequential radii for the supplied matrix.
The intended domain is 1 ≤ k ≤ d and ε > 0. -/
noncomputable def random_reconstruction (d k : ℕ) (hkd : k ≤ d)
    (μ : Measure (Fin d → Fin d → ℝ))
    (U : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) (ε : ℝ) :
    Prop × Matrix (Fin d) (Fin k) ℝ × Matrix (Fin k) (Fin d) ℝ ×
    Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) ×
    (Fin d → ℝ) × (Fin d → ℝ) := by
  classical
  let orth := fun V : Matrix (Fin d) (Fin d) ℝ =>
    V.transpose * V = 1 ∧ V * V.transpose = 1
  let A : Matrix (Fin d) (Fin k) ℝ := fun i j => U i (Fin.castLE hkd j)
  let P := A * A.transpose
  let first := (boxes x (fun _ => ε) (fun z => A.transpose.mulVec z)).2.2.1
  let opt := (boxes x (fun _ => ε) (fun z => P.mulVec z)).2.2.1.2
  let seq := (boxes first.1 first.2 (fun z => A.mulVec z)).2.2.1.2
  exact (1 ≤ k ∧ 0 < ε ∧ IsProbabilityMeasure μ ∧
    (∀ᵐ V ∂μ, orth V) ∧ (∀ V, orth V → μ.map (fun (T : Fin d → Fin d → ℝ) => (fun i j => (∑ a, V i a * T a j) : Fin d → Fin d → ℝ)) = μ),
    A, A.transpose, P, P.mulVec x, opt, seq)

end Definition


-- Export-only notation: expands to original projections; no new mathematical declarations.
notation:max "boxes.B(" value ")" => value.1

notation:max "boxes.lo(" value ")" => value.2.1.1

notation:max "boxes.hi(" value ")" => value.2.1.2

notation:max "linear_network.F(" value ")" => value.1

notation:max "ibp_training_risk.risk(" value ")" => value.1

notation:max "relu_local_radii.radii(" value ")" => value.2.2.1

notation:max "relu_local_radii.r(" value ")" => value.2.2.2.1.1

notation:max "relu_local_radii.s(" value ")" => value.2.2.2.1.2

notation:max "random_reconstruction.opt(" value ")" => value.2.2.2.2.2.1

notation:max "random_reconstruction.seq(" value ")" => value.2.2.2.2.2.2
