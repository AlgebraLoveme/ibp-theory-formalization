module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Theorem_3p2
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Theorem_3p9.Machinery

-- formalizer:machinery-begin
lemma sufficient_numeric_bound {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hc1 : c < 1) (h : c ≤ (1 + 4 * M)⁻¹) :
    2 * M * c * (1 + c) ≤ 1 - c := by
  have hp : 0 < 1 + 4 * M := by positivity
  have hmul : c * (1 + 4 * M) ≤ 1 := by
    exact (le_div_iff₀ hp).mp (by simpa only [one_div] using h)
  have hMc : 0 ≤ M * c := mul_nonneg hM hc
  nlinarith [mul_nonneg hMc (sub_nonneg.mpr (le_of_lt hc1))]

lemma relative_norm_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (α β : E) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (h : ‖α‖ ≤ c * ‖β‖) :
    ‖α‖ ≤ c / (1 - c) * ‖α - β‖ ∧
    ‖α - β‖ ≤ (1 + c) * ‖β‖ := by
  have hb : ‖β‖ ≤ ‖α‖ + ‖α - β‖ := by
    simpa only [norm_sub_rev] using norm_le_insert α β
  have ha : (1 - c) * ‖α‖ ≤ c * ‖α - β‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hb hc]
  constructor
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sub_pos.mpr hc1)).mpr
    nlinarith
  · have ht := norm_sub_le α β
    nlinarith

lemma relative_inner_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (α β : E) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (h : ‖α‖ ≤ c * ‖β‖) :
    ‖α - β‖ ^ 2 / (1 + c) ≤ -inner ℝ β (α - β) := by
  have hn := (relative_norm_bounds α β hc hc1 h).2
  have ha2 : ‖α‖ ^ 2 ≤ c ^ 2 * ‖β‖ ^ 2 := by
    nlinarith [sq_nonneg (c * ‖β‖ - ‖α‖),
      mul_nonneg (sub_nonneg.mpr h) (norm_nonneg α)]
  have hh2 : ‖α - β‖ ^ 2 ≤ (1 + c) ^ 2 * ‖β‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (norm_nonneg (α - β)),
      sq_nonneg ((1 + c) * ‖β‖ - ‖α - β‖)]
  have hex := norm_add_sq_real β (α - β)
  rw [add_sub_cancel] at hex
  have hm := mul_nonneg (sub_nonneg.mpr hh2) (sub_nonneg.mpr hc1.le)
  have hm' := mul_nonneg (sub_nonneg.mpr ha2) (show 0 ≤ 1 + c by linarith)
  apply (div_le_iff₀ (show 0 < 1 + c by linarith)).mpr
  nlinarith

lemma homogeneous_gradient_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {O Q τ : E → ℝ} {θ : E}
    (hQ : DifferentiableAt ℝ Q θ) (hτ : DifferentiableAt ℝ τ θ)
    (h : O =ᶠ[nhds θ] fun p => τ p * Q p)
    (hQpos : 0 < Q θ) (hτpos : 0 < τ θ) :
    (O θ)⁻¹ • gradient O θ - (Q θ)⁻¹ • gradient Q θ =
      (τ θ)⁻¹ • gradient τ θ := by
  have hv := h.eq_of_nhds
  have hg := h.gradient_eq
  have hm : gradient (fun p => τ p * Q p) θ =
      τ θ • gradient Q θ + Q θ • gradient τ θ := by
    simp only [gradient, fderiv_fun_mul hτ hQ, map_add, map_smul]
  rw [hg, hm, hv, smul_add, smul_smul, smul_smul]
  have hq0 := ne_of_gt hQpos
  have ht0 := ne_of_gt hτpos
  have ha : (τ θ * Q θ)⁻¹ * τ θ = (Q θ)⁻¹ := by field_simp
  have hb : (τ θ * Q θ)⁻¹ * Q θ = (τ θ)⁻¹ := by field_simp
  rw [ha, hb]
  abel

lemma rescale_negative_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B v : E) {q t c : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hc : 0 ≤ c)
    (h : ‖t⁻¹ • v‖ ^ 2 / (1 + c) ≤ -inner ℝ (q⁻¹ • B) (t⁻¹ • v)) :
    inner ℝ B v ≤ -(‖v‖ ^ 2 / t / (1 + c)) * q := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht,
    real_inner_smul_left, real_inner_smul_right] at h
  have hcp : 0 < 1 + c := by linarith
  have ht0 := ne_of_gt ht
  have hq0 := ne_of_gt hq
  have hc0 := ne_of_gt hcp
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ t ^ 2 * q * (1 + c) by positivity)
  field_simp at hh ⊢
  nlinarith

lemma rescale_absolute_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A v : E) {o t c : ℝ}
    (ho : 0 < o) (ht : 0 < t) (hc1 : c < 1)
    (h : ‖o⁻¹ • A‖ ≤ c / (1 - c) * ‖t⁻¹ • v‖) :
    |inner ℝ A v| ≤ c * (‖v‖ ^ 2 / t) / (1 - c) * o := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht,
    abs_of_pos ho] at h
  have hcpos : 0 < 1 - c := sub_pos.mpr hc1
  have ht0 := ne_of_gt ht
  have ho0 := ne_of_gt ho
  have hc0 := ne_of_gt hcpos
  have hh := mul_le_mul_of_nonneg_right h (norm_nonneg v)
  have hi := abs_real_inner_le_norm A v
  have hi' := mul_le_mul_of_nonneg_right hi
    (show 0 ≤ (1 - c) * t by positivity)
  field_simp at hh ⊢
  nlinarith

lemma network_matrix_differentiable (L : ℕ) (d : Fin (L + 1) → ℕ) :
    Differentiable ℝ (fun p : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) =>
        linear_network.F(Definition.linear_network L d (fun k i j => p ⟨k,i,j⟩))) := by
  classical
  let prod := fun p : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) => Nat.rec
    (motive := fun k => (hk : k ≤ L) → Bool →
      Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
    (fun _ _ => 1)
    (fun k ih hk a =>
      fun i j => Finset.univ.sum fun t =>
        (if a then |p ⟨⟨k, by omega⟩,i,t⟩| else p ⟨⟨k, by omega⟩,i,t⟩) *
          ih (by omega) a t j)
  have hp : ∀ k (hk : k ≤ L) i j,
      Differentiable ℝ (fun p => prod p k hk false i j) := by
    intro k
    induction k with
    | zero => intro hk i j; exact differentiable_const _
    | succ k ih =>
      intro hk i j p
      change DifferentiableAt ℝ (fun p => Finset.univ.sum fun t =>
        p ⟨⟨k, by omega⟩,i,t⟩ * prod p k (by omega) false t j) p
      apply DifferentiableAt.fun_sum
      intro t ht
      exact ((PiLp.hasFDerivAt_apply 2 p _).differentiableAt).mul (ih (by omega) t j p)
  intro p
  exact differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => hp L le_rfl i j p

lemma absolute_gradient_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {θ : E}
    (hf : DifferentiableAt ℝ f θ) (hne : f θ ≠ 0) (v : E) :
    |inner ℝ (gradient (fun p => |f p|) θ) v| =
      |inner ℝ (gradient f θ) v| := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hg : gradient (fun p => |f p|) θ = -gradient f θ := by
      simp only [gradient, (hf.hasFDerivAt.abs_of_neg hneg).fderiv, map_neg]
    rw [hg, inner_neg_left, abs_neg]
  · have hg : gradient (fun p => |f p|) θ = gradient f θ := by
      simp only [gradient, (hf.hasFDerivAt.abs_of_pos hpos).fderiv]
    rw [hg]

lemma linear_combination_directional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ι : Type*} [Fintype ι]
    (a : E → ι → ℝ) (x : ι → ℝ) (θ v : E)
    (ha : ∀ j, DifferentiableAt ℝ (fun p => a p j) θ) :
    inner ℝ (gradient (fun p => ∑ j, a p j * x j) θ) v =
      ∑ j, inner ℝ (gradient (fun p => a p j) θ) v * x j := by
  classical
  have hd : ∀ j, DifferentiableAt ℝ (fun p => a p j * x j) θ :=
    fun j => (ha j).mul_const _
  rw [inner_gradient_left (DifferentiableAt.fun_sum (fun j _ => hd j)),
    fderiv_fun_sum (fun j _ => hd j)]
  simp only [ContinuousLinearMap.sum_apply, fderiv_mul_const (ha _),
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_gradient_left (ha j)]
  ring

lemma bounded_input_row {ι : Type*} [Fintype ι] (a b x : ι → ℝ) {K : ℝ}
    (hx : ∀ j, |x j| ≤ 1) (hb : ∀ j, |b j| ≤ K * |a j|) :
    |∑ j, b j * x j| ≤ K * ∑ j, |a j| := by
  classical
  calc
    |∑ j, b j * x j| ≤ ∑ j, |b j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, K * |a j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hx j)).trans (hb j)
    _ = K * ∑ j, |a j| := (Finset.mul_sum _ _ _).symm

lemma oscillation_numeric_bound {M c γ : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hγ : 0 ≤ γ) (h : 2 * M * c * (1 + c) ≤ 1 - c) :
    2 * (c * γ / (1 - c) * M) ≤ γ / (1 + c) := by
  have hp : 0 < 1 - c := sub_pos.mpr hc1
  have hq : 0 < 1 + c := by linarith
  have hh := mul_le_mul_of_nonneg_right h hγ
  field_simp
  nlinarith

lemma weighted_oscillation {ι : Type*} [Fintype ι]
    (p d : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {R : ℝ} (hd : ∀ i j, d i - d j ≤ R) (i : ι) :
    d i - ∑ j, p j * d j ≤ R := by
  classical
  calc
    d i - ∑ j, p j * d j = ∑ j, p j * (d i - d j) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
    _ ≤ ∑ j, p j * R := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hd i j) (hp j)
    _ = R := by rw [← Finset.sum_mul, hs, one_mul]

lemma softmax_covariance_bound {ι : Type*} [Fintype ι]
    (p r d : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hr : ∀ i, 0 ≤ r i) {R : ℝ} (hd : ∀ i j, d i - d j ≤ R) :
    ∑ i, p i * r i * (d i - ∑ j, p j * d j) ≤ R * ∑ i, p i * r i := by
  classical
  calc
    _ ≤ ∑ i, (p i * r i) * R := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (weighted_oscillation p d hp hs hd i)
        (mul_nonneg (hp i) (hr i))
    _ = R * ∑ i, p i * r i := by rw [← Finset.sum_mul, mul_comm]

lemma weighted_variance_nonneg {ι : Type*} [Fintype ι]
    (p r : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 ≤ (∑ i, p i * r i ^ 2) - (∑ i, p i * r i) ^ 2 := by
  classical
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => mul_nonneg (hp i) (sq_nonneg (r i - ∑ j, p j * r j)))
  have he : (∑ i, p i * (r i - ∑ j, p j * r j) ^ 2) =
      (∑ i, p i * r i ^ 2) - (∑ i, p i * r i) ^ 2 := by
    calc
      _ = (∑ i, p i * r i ^ 2) -
          (2 * ∑ i, p i * r i) * (∑ i, p i * r i) +
          (∑ i, p i * r i) ^ 2 * (∑ i, p i) := by
        rw [Finset.mul_sum Finset.univ (fun i => p i * r i) (2 * ∑ i, p i * r i),
          Finset.mul_sum Finset.univ p ((∑ i, p i * r i) ^ 2),
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [hs]; ring
  rwa [he] at h

lemma exponential_sum_positive {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → ℝ) : 0 < ∑ i, Real.exp (z i) := by
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma softmax_probability {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) :
    (∀ i, 0 ≤ Real.exp (z i) / ∑ j, Real.exp (z j)) ∧
      (∑ i, Real.exp (z i) / ∑ j, Real.exp (z j)) = 1 := by
  have h := exponential_sum_positive z
  exact ⟨fun i => div_nonneg (Real.exp_pos _).le h.le,
    by rw [← Finset.sum_div, div_self h.ne']⟩

lemma logsumexp_path_derivative {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.log (∑ i, Real.exp (z i + s * r i)))
      (∑ i, (Real.exp (z i + t * r i) / ∑ j, Real.exp (z j + t * r j)) * r i) t := by
  have hd : ∀ i, HasDerivAt (fun s => Real.exp (z i + s * r i))
      (Real.exp (z i + t * r i) * r i) t := by
    intro i
    convert (((hasDerivAt_id t).mul_const (r i)).const_add (z i)).exp using 1 <;> simp
  have hsum : HasDerivAt (fun s => ∑ i, Real.exp (z i + s * r i))
      (∑ i, Real.exp (z i + t * r i) * r i) t :=
    HasDerivAt.fun_sum (fun i _ => hd i)
  have hs := hsum.log (exponential_sum_positive (fun i => z i + t * r i)).ne'
  convert hs using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma softmax_path_derivative {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt
      (fun s => Real.exp (z i + s * r i) / ∑ j, Real.exp (z j + s * r j))
      ((Real.exp (z i + t * r i) / ∑ j, Real.exp (z j + t * r j)) *
        (r i - ∑ j, (Real.exp (z j + t * r j) / ∑ k, Real.exp (z k + t * r k)) * r j)) t := by
  have hd : ∀ j, HasDerivAt (fun s => Real.exp (z j + s * r j))
      (Real.exp (z j + t * r j) * r j) t := by
    intro j
    convert (((hasDerivAt_id t).mul_const (r j)).const_add (z j)).exp using 1 <;> simp
  have hsum : HasDerivAt (fun s => ∑ j, Real.exp (z j + s * r j))
      (∑ j, Real.exp (z j + t * r j) * r j) t :=
    HasDerivAt.fun_sum (fun j _ => hd j)
  have hpos := exponential_sum_positive (fun j => z j + t * r j)
  convert (hd i).div hsum hpos.ne' using 1
  have he : (∑ j, (Real.exp (z j + t * r j) / ∑ k, Real.exp (z k + t * r k)) * r j) =
      (∑ j, Real.exp (z j + t * r j) * r j) / ∑ k, Real.exp (z k + t * r k) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  field_simp

lemma covariance_symmetry {ι : Type*} [Fintype ι] (p r d : ι → ℝ) :
    (∑ i, p i * (r i - ∑ j, p j * r j) * d i) =
      ∑ i, p i * r i * (d i - ∑ j, p j * d j) := by
  classical
  let R := ∑ j, p j * r j
  let D := ∑ j, p j * d j
  change (∑ i, p i * (r i - R) * d i) = ∑ i, p i * r i * (d i - D)
  calc
    _ = (∑ i, p i * r i * d i) - R * D := by
      dsimp [D]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      dsimp [R]
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma softmax_average_derivative {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r d : ι → ℝ) (t : ℝ) :
    let p := fun s i => Real.exp (z i + s * r i) / ∑ j, Real.exp (z j + s * r j)
    HasDerivAt (fun s => ∑ i, p s i * d i)
      (∑ i, p t i * r i * (d i - ∑ j, p t j * d j)) t := by
  dsimp only
  rw [← covariance_symmetry]
  exact HasDerivAt.fun_sum (fun i _ => (softmax_path_derivative z r t i).mul_const (d i))

lemma softmax_average_increment {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r d : ι → ℝ) (hr : ∀ i, 0 ≤ r i) {R : ℝ}
    (hd : ∀ i j, d i - d j ≤ R) :
    let p := fun t i => Real.exp (z i + t * r i) / ∑ j, Real.exp (z j + t * r j)
    (∑ i, p 1 i * d i) - (∑ i, p 0 i * d i) ≤
      R * (Real.log (∑ i, Real.exp (z i + r i)) - Real.log (∑ i, Real.exp (z i))) := by
  dsimp only
  let p := fun t i => Real.exp (z i + t * r i) / ∑ j, Real.exp (z j + t * r j)
  let ell := fun t => Real.log (∑ i, Real.exp (z i + t * r i))
  have hdiff := fun t => (softmax_average_derivative z r d t).sub
    ((logsumexp_path_derivative z r t).const_mul R)
  have hanti := antitone_of_hasDerivAt_nonpos hdiff (fun t => by
    have hp := softmax_probability (fun i => z i + t * r i)
    exact sub_nonpos.mpr (softmax_covariance_bound (p t) r d hp.1 hp.2 hr hd))
  have hh := hanti (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [Pi.sub_apply, zero_mul, add_zero, one_mul] at hh ⊢
  linarith

lemma logsumexp_increment_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    let Δ := Real.log (∑ i, Real.exp (z i + r i)) - Real.log (∑ i, Real.exp (z i))
    0 ≤ Δ ∧ Δ ≤ ∑ i, (Real.exp (z i + r i) / ∑ j, Real.exp (z j + r j)) * r i := by
  classical
  let p := fun t i => Real.exp (z i + t * r i) / ∑ j, Real.exp (z j + t * r j)
  let m := fun t => ∑ i, p t i * r i
  let ell := fun t => Real.log (∑ i, Real.exp (z i + t * r i))
  have hp := fun t => softmax_probability (fun i => z i + t * r i)
  have hm : Monotone m := by
    apply monotone_of_hasDerivAt_nonneg (fun t => softmax_average_derivative z r r t)
    intro t
    have h := weighted_variance_nonneg (p t) r (hp t).1 (hp t).2
    have he : (∑ i, p t i * r i * (r i - ∑ j, p t j * r j)) =
        (∑ i, p t i * r i ^ 2) - (∑ i, p t i * r i) ^ 2 := by
      rw [pow_two, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    change 0 ≤ ∑ i, p t i * r i * (r i - ∑ j, p t j * r j)
    rwa [he]
  have hell : Monotone ell := by
    apply monotone_of_hasDerivAt_nonneg (fun t => logsumexp_path_derivative z r t)
    intro t
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((hp t).1 i) (hr i)
  have hd : ∀ t, HasDerivAt (fun s => ell s - s * m 1) (m t - m 1) t := by
    intro t
    simpa only [id_eq, one_mul] using
      (logsumexp_path_derivative z r t).sub ((hasDerivAt_id t).mul_const (m 1))
  have hcont : Continuous (fun s => ell s - s * m 1) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hanti : AntitoneOn (fun s => ell s - s * m 1) (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont.continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    exact sub_nonpos.mpr (hm (interior_subset ht).2)
  have hlow := hell (show (0 : ℝ) ≤ 1 by norm_num)
  have hupp := hanti (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show (0 : ℝ) ≤ 1 by norm_num)
  dsimp [ell, m, p] at hlow hupp
  simp only [zero_mul, add_zero, one_mul] at hlow hupp
  dsimp only
  constructor <;> linarith

lemma softmax_loss_directional_nonpos {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r d dr : ι → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ i j, d i - d j ≤ lam)
    (hdr : ∀ i, dr i ≤ -lam * r i) :
    let p₀ := fun i => Real.exp (z i) / ∑ j, Real.exp (z j)
    let p₁ := fun i => Real.exp (z i + r i) / ∑ j, Real.exp (z j + r j)
    (∑ i, (p₁ i - p₀ i) * d i) + (∑ i, p₁ i * dr i) ≤ 0 := by
  classical
  dsimp only
  let p₁ := fun i => Real.exp (z i + r i) / ∑ j, Real.exp (z j + r j)
  have hp := softmax_probability (fun i => z i + r i)
  have hi := softmax_average_increment z r d hr hd
  dsimp only at hi
  simp only [one_mul, zero_mul, add_zero] at hi
  have hΔ := (logsumexp_increment_bounds z r hr).2
  have hmul := mul_le_mul_of_nonneg_left hΔ hlam
  have hr' : (∑ i, p₁ i * dr i) ≤ -lam * ∑ i, p₁ i * r i := by
    calc
      _ ≤ ∑ i, p₁ i * (-lam * r i) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hdr i) (hp.1 i)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  simp only [sub_mul, Finset.sum_sub_distrib]
  dsimp [p₁] at hr'
  linarith

lemma logsumexp_gradient_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : E → ι → ℝ) (θ v : E)
    (hz : ∀ i, DifferentiableAt ℝ (fun p => z p i) θ) :
    inner ℝ (gradient (fun p => Real.log (∑ i, Real.exp (z p i))) θ) v =
      ∑ i, (Real.exp (z θ i) / ∑ j, Real.exp (z θ j)) *
        inner ℝ (gradient (fun p => z p i) θ) v := by
  classical
  have hd : ∀ i, HasFDerivAt (fun p => Real.exp (z p i))
      (Real.exp (z θ i) • fderiv ℝ (fun p => z p i) θ) θ :=
    fun i => (hz i).hasFDerivAt.exp
  have hsum : HasFDerivAt (fun p => ∑ i, Real.exp (z p i))
      (∑ i, Real.exp (z θ i) • fderiv ℝ (fun p => z p i) θ) θ :=
    HasFDerivAt.fun_sum (fun i _ => hd i)
  have hlog := hsum.log (exponential_sum_positive (z θ)).ne'
  rw [inner_gradient_left hlog.differentiableAt, hlog.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_gradient_left (hz i)]
  ring

lemma directional_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f g : E → ℝ} {θ : E}
    (hf : DifferentiableAt ℝ f θ) (hg : DifferentiableAt ℝ g θ) (v : E) :
    inner ℝ (gradient (fun p => f p + g p) θ) v =
      inner ℝ (gradient f θ) v + inner ℝ (gradient g θ) v := by
  rw [inner_gradient_left (hf.fun_add hg), fderiv_fun_add hf hg,
    ContinuousLinearMap.add_apply, inner_gradient_left hf, inner_gradient_left hg]

lemma directional_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f g : E → ℝ} {θ : E}
    (hf : DifferentiableAt ℝ f θ) (hg : DifferentiableAt ℝ g θ) (v : E) :
    inner ℝ (gradient (fun p => f p - g p) θ) v =
      inner ℝ (gradient f θ) v - inner ℝ (gradient g θ) v := by
  rw [inner_gradient_left (hf.fun_sub hg), fderiv_fun_sub hf hg,
    ContinuousLinearMap.sub_apply, inner_gradient_left hf, inner_gradient_left hg]

lemma logsumexp_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (z : E → ι → ℝ) (θ : E)
    (hz : ∀ i, DifferentiableAt ℝ (fun p => z p i) θ) :
    DifferentiableAt ℝ (fun p => Real.log (∑ i, Real.exp (z p i))) θ :=
  (DifferentiableAt.fun_sum (fun i _ => (hz i).exp)).log
    (exponential_sum_positive (z θ)).ne'

lemma logsumexp_difference_directional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r : E → ι → ℝ) (θ v : E)
    (hz : ∀ i, DifferentiableAt ℝ (fun p => z p i) θ)
    (hr : ∀ i, DifferentiableAt ℝ (fun p => r p i) θ) :
    let p₀ := fun i => Real.exp (z θ i) / ∑ j, Real.exp (z θ j)
    let p₁ := fun i => Real.exp (z θ i + r θ i) / ∑ j, Real.exp (z θ j + r θ j)
    inner ℝ (gradient (fun p => Real.log (∑ i, Real.exp (z p i + r p i)) -
      Real.log (∑ i, Real.exp (z p i))) θ) v =
      (∑ i, (p₁ i - p₀ i) * inner ℝ (gradient (fun p => z p i) θ) v) +
      (∑ i, p₁ i * inner ℝ (gradient (fun p => r p i) θ) v) := by
  classical
  dsimp only
  rw [directional_sub (logsumexp_differentiable _ θ (fun i => (hz i).fun_add (hr i)))
    (logsumexp_differentiable z θ hz) v,
    logsumexp_gradient_inner _ θ v (fun i => (hz i).fun_add (hr i)),
    logsumexp_gradient_inner z θ v hz]
  simp_rw [directional_add (hz _) (hr _) v]
  simp only [mul_add, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma logsumexp_change_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (z r : ι → ℝ) {C : ℝ} (hr : ∀ i, |r i| ≤ C) :
    |Real.log (∑ i, Real.exp (z i + r i)) - Real.log (∑ i, Real.exp (z i))| ≤ C := by
  classical
  have hb : ∀ t, |∑ i, (Real.exp (z i + t * r i) / ∑ j, Real.exp (z j + t * r j)) * r i| ≤ C := by
    intro t
    let p := fun i => Real.exp (z i + t * r i) / ∑ j, Real.exp (z j + t * r j)
    have hp := softmax_probability (fun i => z i + t * r i)
    calc
      _ ≤ ∑ i, |p i * r i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, p i * |r i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hp.1 i)]
      _ ≤ ∑ i, p i * C := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hr i) (hp.1 i)
      _ = C := by rw [← Finset.sum_mul, hp.2, one_mul]
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (logsumexp_path_derivative z r t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)
  simpa only [zero_mul, add_zero, one_mul, Real.norm_eq_abs] using h

lemma full_sum_cross_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f ρ : ι → ℝ) (y : ι) :
    (∑ i, Real.exp (f i - f y + if i = y then 0 else ρ i + ρ y)) =
      1 + ∑ i ∈ Finset.univ.erase y, Real.exp (f i - f y + ρ i + ρ y) := by
  have h := Finset.sum_erase_add Finset.univ
    (fun i => Real.exp (f i - f y + if i = y then 0 else ρ i + ρ y))
    (Finset.mem_univ y)
  rw [← h]
  simp only [ite_true, sub_self, add_zero, Real.exp_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_neg (Finset.mem_erase.mp hi).1]
  congr 1
  ring

lemma network_radius_continuous (L : ℕ) (d : Fin (L + 1) → ℕ) :
    Continuous (fun p : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) =>
        (Definition.linear_network L d (fun k i j => p ⟨k,i,j⟩)).2.2.1) := by
  classical
  let prod := fun p : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) => Nat.rec
    (motive := fun k => (hk : k ≤ L) → Bool →
      Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
    (fun _ _ => 1)
    (fun k ih hk a =>
      fun i j => Finset.univ.sum fun t =>
        (if a then |p ⟨⟨k, by omega⟩,i,t⟩| else p ⟨⟨k, by omega⟩,i,t⟩) *
          ih (by omega) a t j)
  have hp : ∀ k (hk : k ≤ L) i j,
      Continuous (fun p => prod p k hk true i j) := by
    intro k
    induction k with
    | zero => intro hk i j; exact continuous_const
    | succ k ih =>
      intro hk i j
      change Continuous (fun p => Finset.univ.sum fun t =>
        |p ⟨⟨k, by omega⟩,i,t⟩| * prod p k (by omega) true t j)
      apply continuous_finset_sum
      intro t ht
      exact ((PiLp.continuous_apply 2 _ _).abs).mul (ih (by omega) t j)
  exact continuous_pi fun i => continuous_pi fun j => hp L le_rfl i j

lemma matrix_row_norm_bound {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin m) :
    |Matrix.mulVec A x i| ≤ ‖A‖ * ∑ j, |x j| := by
  classical
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖A‖ * |x j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma logsumexp_sub_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) {C : ℝ} (h : ∀ i, |a i - b i| ≤ C) :
    |Real.log (∑ i, Real.exp (a i)) - Real.log (∑ i, Real.exp (b i))| ≤ C := by
  simpa only [add_sub_cancel] using logsumexp_change_bound b (fun i => a i - b i) h

lemma box_loss_change_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f g ρ σ : ι → ℝ) (y : ι) {C D : ℝ}
    (hf : ∀ i, |f i - g i| ≤ C) (hr : ∀ i, |ρ i - σ i| ≤ D) :
    |Real.log (∑ i, Real.exp (f i - f y + if i = y then 0 else ρ i + ρ y)) -
      Real.log (∑ i, Real.exp (g i - g y + if i = y then 0 else σ i + σ y))| ≤
        2 * C + 2 * D := by
  apply logsumexp_sub_bound
  intro i
  have hC := (abs_nonneg _).trans (hf y)
  have hD := (abs_nonneg _).trans (hr y)
  by_cases hi : i = y
  · subst i
    simp only [ite_true, sub_self, add_zero, abs_zero]
    linarith
  · simp only [if_neg hi]
    obtain ⟨hfi, hfi'⟩ := abs_le.mp (hf i)
    obtain ⟨hfy, hfy'⟩ := abs_le.mp (hf y)
    obtain ⟨hri, hri'⟩ := abs_le.mp (hr i)
    obtain ⟨hry, hry'⟩ := abs_le.mp (hr y)
    apply abs_le.mpr
    constructor <;> linarith

lemma integrable_on_ae_compact {n m : ℕ}
    (μ : MeasureTheory.Measure ((Fin n → ℝ) × Fin m)) [MeasureTheory.IsFiniteMeasure μ]
    {K : Set ((Fin n → ℝ) × Fin m)} (hK : IsCompact K)
    (hμ : ∀ᵐ a ∂μ, a ∈ K) {f : ((Fin n → ℝ) × Fin m) → ℝ}
    (hf : Continuous f) : MeasureTheory.Integrable f μ := by
  have h := hf.continuousOn.integrableOn_compact (μ := μ) hK
  change MeasureTheory.Integrable f (μ.restrict K) at h
  rwa [MeasureTheory.Measure.restrict_eq_self_of_ae_mem hμ] at h

lemma integral_directional_nonpos {κ : Type*} [Fintype κ] {n m : ℕ}
    (μ : MeasureTheory.Measure ((Fin n → ℝ) × Fin m)) [MeasureTheory.IsFiniteMeasure μ]
    (f : EuclideanSpace ℝ κ → ((Fin n → ℝ) × Fin m) → ℝ)
    (θ v : EuclideanSpace ℝ κ)
    {K : Set ((Fin n → ℝ) × Fin m)} (hK : IsCompact K)
    (hμ : ∀ᵐ a ∂μ, a ∈ K)
    (hcont : Continuous (fun a : ((Fin n → ℝ) × Fin m) × EuclideanSpace ℝ κ => f a.2 a.1))
    (hdiff : ∀ a, DifferentiableAt ℝ (fun p => f p a) θ)
    {s : Set (EuclideanSpace ℝ κ)} (hs : s ∈ nhds θ) {C : ℝ}
    (hbound : ∀ a ∈ K, ∀ p ∈ s, ‖f p a - f θ a‖ ≤ C * ‖p - θ‖)
    (hneg : ∀ᵐ a ∂μ, inner ℝ (gradient (fun p => f p a) θ) v ≤ 0) :
    inner ℝ (gradient (fun p => ∫ a, f p a ∂μ) θ) v ≤ 0 := by
  have hc : ∀ p, Continuous (f p) := fun p =>
    hcont.comp (continuous_id.prodMk continuous_const)
  have hi := integrable_on_ae_compact μ hK hμ (hc θ)
  have hm := (measurable_fderiv_with_param (f := fun a p => f p a) ℝ hcont).comp
    (measurable_id.prodMk (measurable_const (a := θ)))
  have hder := hasFDerivAt_integral_of_dominated_loc_of_lip' (μ := μ)
    (F := f) (F' := fun a => fderiv ℝ (fun p => f p a) θ) (bound := fun _ => C)
    hs (fun p _ => (hc p).aestronglyMeasurable) hi hm.aestronglyMeasurable
    (hμ.mono fun a ha => hbound a ha) (MeasureTheory.integrable_const C)
    (Filter.Eventually.of_forall fun a => (hdiff a).hasFDerivAt)
  rw [inner_gradient_left hder.2.differentiableAt, hder.2.fderiv,
    ContinuousLinearMap.integral_apply hder.1 v]
  apply MeasureTheory.integral_nonpos_of_ae
  exact hneg.mono fun a ha => by rwa [inner_gradient_left (hdiff a)] at ha

lemma continuous_finite_choice {T : Type*} [TopologicalSpace T] {m : ℕ}
    (y : T → Fin m) (f : T → Fin m → ℝ) (hy : Continuous y)
    (hf : ∀ i, Continuous (fun t => f t i)) : Continuous (fun t => f t (y t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have he : ∀ᶠ u in nhds t, y u = y t :=
    hy.continuousAt ((isOpen_discrete {y t}).mem_nhds rfl)
  apply (hf (y t)).continuousAt.congr_of_eventuallyEq
  filter_upwards [he] with u hu
  rw [hu]

lemma continuous_box_loss {T : Type*} [TopologicalSpace T] {m : ℕ} [Nonempty (Fin m)]
    (f ρ : T → Fin m → ℝ) (y : T → Fin m)
    (hf : ∀ i, Continuous (fun t => f t i)) (hr : ∀ i, Continuous (fun t => ρ t i))
    (hy : Continuous y) :
    Continuous (fun t => Real.log (∑ i, Real.exp
      (f t i - f t (y t) + if i = y t then 0 else ρ t i + ρ t (y t)))) := by
  apply continuous_finite_choice y
    (fun t j => Real.log (∑ i, Real.exp (f t i - f t j + if i = j then 0 else ρ t i + ρ t j))) hy
  intro j
  apply Continuous.log
  · apply continuous_finset_sum
    intro i hi
    apply Real.continuous_exp.comp
    apply Continuous.add ((hf i).sub (hf j))
    by_cases hij : i = j
    · simp only [if_pos hij]; exact continuous_const
    · simp only [if_neg hij]; exact (hr i).add (hr j)
  · intro t
    exact (exponential_sum_positive _).ne'

lemma matrix_row_sub_norm_bound {m n : ℕ} (A B : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin m) :
    |Matrix.mulVec A x i - Matrix.mulVec B x i| ≤
      ‖A - B‖ * ∑ j, |x j| := by
  simpa only [Matrix.mulVec, dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using matrix_row_norm_bound (A - B) x i

lemma continuous_parameter_slice {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : β → α → ℝ) (hf : Continuous (fun a : α × β => f a.2 a.1)) (b : β) :
    Continuous (f b) := hf.comp (continuous_id.prodMk continuous_const)

-- formalizer:machinery-end

end Theorem_3p9.Machinery
