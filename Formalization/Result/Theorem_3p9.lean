module
public import Formalization.Result.helpers.Theorem_3p9.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Theorem_3p2

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Theorem_3p9

theorem training_increases_tightness (L : ℕ) (d : Fin (L + 1) → ℕ)
    (μ : Measure ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))))
    (τ : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) → ℝ)
    (θ : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)))
    (hdom : (ibp_training_risk L d μ τ θ).2.1)
    (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    (hgrad : ∀ i j,
      ‖gradient (fun p => (linear_network L d (fun k r s => p ⟨k,r,s⟩)).2.1 i j) θ‖ /
        (linear_network L d (fun k r s => θ ⟨k,r,s⟩)).2.1 i j ≤
      c * (‖gradient (fun p => (linear_network L d (fun k r s => p ⟨k,r,s⟩)).2.2.1 i j) θ‖ /
        (linear_network L d (fun k r s => θ ⟨k,r,s⟩)).2.2.1 i j)) :
    let M := (ibp_training_risk L d μ τ θ).2.2
    (2 * M * c * (1 + c) ≤ 1 - c →
      ∀ e : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ, (∀ j, 0 ≤ e j) →
        inner ℝ
          (gradient (fun p => ibp_training_risk.risk(ibp_training_risk L d μ τ p) e -
            ibp_training_risk.risk(ibp_training_risk L d μ τ p) 0) θ)
          (gradient τ θ) ≤ 0) ∧
    (c ≤ (1 + 4 * M)⁻¹ → 2 * M * c * (1 + c) ≤ 1 - c) := (by
  -- formalizer:proof-begin
  classical
  let O := fun p : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) =>
    (linear_network L d (fun k r s => p ⟨k,r,s⟩)).2.1
  let Q := fun p : EuclideanSpace ℝ
      (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) =>
    (linear_network L d (fun k r s => p ⟨k,r,s⟩)).2.2.1
  obtain ⟨hL, hd, hμ, hx, hO, hQ, hQpos, s, hs, hθs, hτ, hhom⟩ := hdom
  change DifferentiableAt ℝ O θ at hO
  change DifferentiableAt ℝ Q θ at hQ
  change ∀ i j, 0 < Q θ i j at hQpos
  change ∀ p ∈ s, 0 < τ p ∧ ∀ i j, O p i j = τ p * Q p i j at hhom
  let M := sSup (Set.range (fun i => ∑ j, O θ i j))
  have hM : 0 ≤ M := by
    let i : Fin (d (Fin.last L)) := ⟨0, hd _⟩
    apply le_csSup_of_le (Set.finite_range _).bddAbove (Set.mem_range_self i)
    exact Finset.sum_nonneg fun j _ =>
      le_of_lt (by rw [(hhom θ hθs).2 i j]; exact mul_pos (hhom θ hθs).1 (hQpos i j))
  constructor
  · intro hnum e he
    -- Appendix, homogeneous identity: O = τQ holds on an open neighborhood,
    -- so it may be differentiated at θ; both matrices have positive entries.
    have hτθ := hτ.differentiableAt (hs.mem_nhds hθs)
    have hτpos := (hhom θ hθs).1
    let v := gradient τ θ
    let α := fun i j => (O θ i j)⁻¹ • gradient (fun p => O p i j) θ
    let β := fun i j => (Q θ i j)⁻¹ • gradient (fun p => Q p i j) θ
    have hOpos : ∀ i j, 0 < O θ i j := by
      intro i j
      rw [(hhom θ hθs).2 i j]
      exact mul_pos hτpos (hQpos i j)
    have hidentity : ∀ i j, α i j - β i j = (τ θ)⁻¹ • v := by
      intro i j
      apply Machinery.homogeneous_gradient_identity
        (differentiableAt_pi.mp (differentiableAt_pi.mp hQ i) j) hτθ
        _ (hQpos i j) hτpos
      filter_upwards [hs.mem_nhds hθs] with p hp
      exact (hhom p hp).2 i j
    have hnorm : ∀ i j, ‖α i j‖ ≤ c * ‖β i j‖ := by
      intro i j
      simpa only [α, β, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos (hOpos i j), abs_of_pos (hQpos i j),
        div_eq_mul_inv, mul_comm] using hgrad i j
    -- Appendix, the norm comparison and expansion of ‖β+h‖² give the
    -- sharp negative directional bound; Cauchy–Schwarz bounds the O term.
    have hnormα : ∀ i j, ‖α i j‖ ≤ c / (1 - c) * ‖(τ θ)⁻¹ • v‖ := by
      intro i j
      have h := (Machinery.relative_norm_bounds
        (α i j) (β i j) hc₀ hc₁ (hnorm i j)).1
      rwa [hidentity i j] at h
    have hinnerβ : ∀ i j, ‖(τ θ)⁻¹ • v‖ ^ 2 / (1 + c) ≤
        -inner ℝ (β i j) ((τ θ)⁻¹ • v) := by
      intro i j
      have h := Machinery.relative_inner_bound
        (α i j) (β i j) hc₀ hc₁ (hnorm i j)
      rwa [hidentity i j] at h
    let γ := ‖v‖ ^ 2 / τ θ
    let lam := γ / (1 + c)
    have hDQ : ∀ i j, inner ℝ (gradient (fun p => Q p i j) θ) v ≤
        -lam * Q θ i j := by
      intro i j
      exact Machinery.rescale_negative_inner
        _ v (hQpos i j) hτpos hc₀ (hinnerβ i j)
    have hDO : ∀ i j, |inner ℝ (gradient (fun p => O p i j) θ) v| ≤
        c * γ / (1 - c) * O θ i j := by
      intro i j
      exact Machinery.rescale_absolute_inner
        _ v (hOpos i j) hτpos hc₁ (hnormα i j)
    let F := fun p : EuclideanSpace ℝ
        (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) =>
      linear_network.F(linear_network L d (fun k r s => p ⟨k,r,s⟩))
    have hF := Machinery.network_matrix_differentiable L d
    have hFij : ∀ i j, DifferentiableAt ℝ (fun p => F p i j) θ := by
      intro i j
      exact differentiableAt_pi.mp (differentiableAt_pi.mp (hF θ) i) j
    have hOF : ∀ p i j, O p i j = |F p i j| := by intro p i j; rfl
    -- Equation (ibp_logit_oscillation): O=|F|>0 fixes the local entry signs,
    -- so absolute directional derivatives of F and O agree.
    have hDF : ∀ i j, |inner ℝ (gradient (fun p => F p i j) θ) v| ≤
        c * γ / (1 - c) * |F θ i j| := by
      intro i j
      have hn : F θ i j ≠ 0 := abs_pos.mp (hOpos i j)
      have ha := Machinery.absolute_gradient_inner
        (hFij i j) hn v
      rw [← ha]
      exact hDO i j
    have hK : 0 ≤ c * γ / (1 - c) := by
      dsimp [γ]
      exact div_nonneg (mul_nonneg hc₀ (div_nonneg (sq_nonneg _) hτpos.le))
        (sub_nonneg.mpr hc₁.le)
    have hlogit : ∀ x : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ,
        (∀ j, |x j| ≤ 1) → ∀ i,
        |inner ℝ (gradient (fun p => (F p).mulVec x i) θ) v| ≤
          c * γ / (1 - c) * M := by
      intro x hxb i
      change |inner ℝ (gradient (fun p => ∑ j, F p i j * x j) θ) v| ≤ _
      rw [Machinery.linear_combination_directional
        (fun p => F p i) x θ v (hFij i)]
      apply (Machinery.bounded_input_row
        (F θ i) (fun j => inner ℝ (gradient (fun p => F p i j) θ) v) x hxb (hDF i)).trans
      apply mul_le_mul_of_nonneg_left _ hK
      exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
    have hγ : 0 ≤ γ := div_nonneg (sq_nonneg _) hτpos.le
    have hlam : 0 ≤ lam := div_nonneg hγ (by linarith)
    have hoscnum : 2 * (c * γ / (1 - c) * M) ≤ lam :=
      Machinery.oscillation_numeric_bound
        hc₀ hc₁ hγ hnum
    have hosc : ∀ x : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ,
        (∀ j, |x j| ≤ 1) → ∀ i k,
        inner ℝ (gradient (fun p => (F p).mulVec x i) θ) v -
          inner ℝ (gradient (fun p => (F p).mulVec x k) θ) v ≤ lam := by
      intro x hxb i k
      have hi := (abs_le.mp (hlogit x hxb i)).2
      have hk := (abs_le.mp (hlogit x hxb k)).1
      linarith
    -- Theorem 3.2 identifies the propagated radius as ρ=Qe. Nonnegative
    -- input radii preserve the entrywise contraction under finite summation.
    let ρ := fun p => (Q p).mulVec e
    have hρ : ∀ i, 0 ≤ ρ θ i := by
      intro i
      change 0 ≤ ∑ j, Q θ i j * e j
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hQpos i j).le (he j)
    have hDρ : ∀ i, inner ℝ (gradient (fun p => ρ p i) θ) v ≤ -lam * ρ θ i := by
      intro i
      change inner ℝ (gradient (fun p => ∑ j, Q p i j * e j) θ) v ≤ _
      rw [Machinery.linear_combination_directional
        (fun p => Q p i) e θ v
        (fun j => differentiableAt_pi.mp (differentiableAt_pi.mp hQ i) j)]
      calc
        _ ≤ ∑ j, (-lam * Q θ i j) * e j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hDQ i j) (he j)
        _ = -lam * ρ θ i := by dsimp [ρ, Matrix.mulVec, dotProduct]; rw [Finset.mul_sum]; congr 1; funext j; ring
    letI : Nonempty (Fin (d (Fin.last L))) := ⟨⟨0, hd _⟩⟩
    let z := fun (x : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ)
      (y : Fin (d (Fin.last L))) p i => (F p).mulVec x i - (F p).mulVec x y
    let r := fun (y : Fin (d (Fin.last L))) p i =>
      if i = y then (0 : ℝ) else ρ p i + ρ p y
    let δ := fun p (xy : (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))) =>
      Real.log (∑ i, Real.exp (z xy.1 xy.2 p i + r xy.2 p i)) -
        Real.log (∑ i, Real.exp (z xy.1 xy.2 p i))
    have hfrow : ∀ x i, DifferentiableAt ℝ (fun p => (F p).mulVec x i) θ := by
      intro x i
      change DifferentiableAt ℝ (fun p => ∑ j, F p i j * x j) θ
      exact DifferentiableAt.fun_sum fun j _ => (hFij i j).mul_const (x j)
    have hρdiff : ∀ i, DifferentiableAt ℝ (fun p => ρ p i) θ := by
      intro i
      change DifferentiableAt ℝ (fun p => ∑ j, Q p i j * e j) θ
      exact DifferentiableAt.fun_sum fun j _ =>
        (differentiableAt_pi.mp (differentiableAt_pi.mp hQ i) j).mul_const (e j)
    have hzdiff : ∀ x y i, DifferentiableAt ℝ (fun p => z x y p i) θ := by
      intro x y i
      exact (hfrow x i).fun_sub (hfrow x y)
    have hrdiff : ∀ y i, DifferentiableAt ℝ (fun p => r y p i) θ := by
      intro y i
      by_cases hi : i = y
      · simp only [r, if_pos hi]; exact differentiableAt_const _
      · simp only [r, if_neg hi]; exact (hρdiff i).fun_add (hρdiff y)
    have hrpos : ∀ y i, 0 ≤ r y θ i := by
      intro y i
      dsimp [r]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (hρ i) (hρ y)
    have hdr : ∀ y i, inner ℝ (gradient (fun p => r y p i) θ) v ≤ -lam * r y θ i := by
      intro y i
      by_cases hi : i = y
      · simp only [r, if_pos hi, gradient_fun_const, inner_zero_left, mul_zero, le_refl]
      · simp only [r, if_neg hi]
        rw [Machinery.directional_add
          (hρdiff i) (hρdiff y) v]
        nlinarith [hDρ i, hDρ y]
    have hdz : ∀ x y i, inner ℝ (gradient (fun p => z x y p i) θ) v =
        inner ℝ (gradient (fun p => (F p).mulVec x i) θ) v -
          inner ℝ (gradient (fun p => (F p).mulVec x y) θ) v := by
      intro x y i
      exact Machinery.directional_sub
        (hfrow x i) (hfrow x y) v
    -- For each sample use the margins z_i=f_i-f_y and r_i=ρ_i+ρ_y,
    -- setting r_y=0. Differentiation gives (p₁-p₀)·D_vz+p₁·D_vr.
    have hpoint : ∀ xy, (∀ j, |xy.1 j| ≤ 1) →
        inner ℝ (gradient (fun p => δ p xy) θ) v ≤ 0 := by
      intro xy hxb
      change inner ℝ (gradient (fun p =>
        Real.log (∑ i, Real.exp (z xy.1 xy.2 p i + r xy.2 p i)) -
          Real.log (∑ i, Real.exp (z xy.1 xy.2 p i))) θ) v ≤ 0
      rw [Machinery.logsumexp_difference_directional
        (z xy.1 xy.2) (r xy.2) θ v (hzdiff xy.1 xy.2) (hrdiff xy.2)]
      -- The softmax covariance is bounded by range(D_vz)·p_t·r.
      -- Its endpoint comparison gives (p₁-p₀)·D_vz ≤ lam·Δ;
      -- nonnegative variance gives Δ≤p₁·r, and radius contraction finishes.
      apply Machinery.softmax_loss_directional_nonpos
        _ _ _ _ hlam (hrpos xy.2) _ (hdr xy.2)
      intro i k
      rw [hdz xy.1 xy.2 i, hdz xy.1 xy.2 k]
      linarith [hosc xy.1 hxb i k]
    have hδdiff : ∀ xy, DifferentiableAt ℝ (fun p => δ p xy) θ := by
      intro xy
      exact (Machinery.logsumexp_differentiable
        _ θ (fun i => (hzdiff xy.1 xy.2 i).fun_add (hrdiff xy.2 i))).fun_sub
        (Machinery.logsumexp_differentiable
          _ θ (hzdiff xy.1 xy.2))
    have hδformula : ∀ p xy, δ p xy =
        Real.log (1 + ∑ i ∈ Finset.univ.erase xy.2,
          Real.exp ((F p).mulVec xy.1 i - (F p).mulVec xy.1 xy.2 + ρ p i + ρ p xy.2)) -
        Real.log (1 + ∑ i ∈ Finset.univ.erase xy.2,
          Real.exp ((F p).mulVec xy.1 i - (F p).mulVec xy.1 xy.2)) := by
      intro p xy
      dsimp only [δ, z, r]
      rw [Machinery.full_sum_cross_entropy
        ((F p).mulVec xy.1) (ρ p) xy.2]
      have hn := Machinery.full_sum_cross_entropy
        ((F p).mulVec xy.1) (fun _ => 0) xy.2
      simp only [add_zero, ite_self] at hn
      rw [hn]
    have hae : ∀ᵐ xy ∂μ, inner ℝ (gradient (fun p => δ p xy) θ) v ≤ 0 :=
      hx.mono (fun xy hxb => hpoint xy hxb)
    letI : IsProbabilityMeasure μ := hμ
    let loss := fun (b : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) p
        (xy : (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))) =>
      Real.log (∑ i, Real.exp ((F p).mulVec xy.1 i - (F p).mulVec xy.1 xy.2 +
        if i = xy.2 then 0 else (Q p).mulVec b i + (Q p).mulVec b xy.2))
    have hδeq : δ = fun p xy => loss e p xy - loss 0 p xy := by
      funext p xy
      simp only [δ, loss, z, r, ρ, Matrix.mulVec_zero, Pi.zero_apply, add_zero, ite_self]
    have hQc : Continuous Q :=
      Machinery.network_radius_continuous L d
    have hlc : ∀ b, Continuous (fun a :
        ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))) ×
          EuclideanSpace ℝ (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) =>
        loss b a.2 a.1) := by
      intro b
      apply Machinery.continuous_box_loss
        (fun a : ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))) × EuclideanSpace ℝ (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) => (F a.2).mulVec a.1.1)
        (fun a => (Q a.2).mulVec b) (fun a => a.1.2)
      · intro i
        change Continuous (fun a : ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))) × EuclideanSpace ℝ (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) => ∑ j, F a.2 i j * a.1.1 j)
        apply continuous_finset_sum
        intro j hj
        exact (((continuous_apply j).comp ((continuous_apply i).comp hF.continuous)).comp continuous_snd).mul
          ((continuous_apply j).comp (continuous_fst.comp continuous_fst))
      · intro i
        change Continuous (fun a : ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))) × EuclideanSpace ℝ (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) => ∑ j, Q a.2 i j * b j)
        apply continuous_finset_sum
        intro j hj
        exact (((continuous_apply j).comp ((continuous_apply i).comp hQc)).comp continuous_snd).mul_const _
      · exact continuous_snd.comp continuous_fst
    have hδc : Continuous (fun a :
        ((Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) × Fin (d (Fin.last L))) ×
          EuclideanSpace ℝ (Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)) => δ a.2 a.1) := by
      rw [hδeq]
      exact (hlc e).sub (hlc 0)
    let K := Metric.closedBall (0 : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) 1 ×ˢ
      (Set.univ : Set (Fin (d (Fin.last L))))
    have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_univ
    have hμK : ∀ᵐ xy ∂μ, xy ∈ K := hx.mono (fun xy hxb => by
      refine ⟨?_, Set.mem_univ _⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hxb)
    have hli : ∀ b p, Integrable (loss b p) μ := by
      intro b p
      exact Machinery.integrable_on_ae_compact
        (f := loss b p) μ hK hμK
        (Machinery.continuous_parameter_slice
          (loss b) (hlc b) p)
    have hlrisk : ∀ b p, ibp_training_risk.risk(ibp_training_risk L d μ τ p) b = ∫ xy, loss b p xy ∂μ := by
      intro b p
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro xy
      dsimp only [ibp_training_risk, loss]
      rw [Machinery.full_sum_cross_entropy]
    have hriskeq : (fun p => ibp_training_risk.risk(ibp_training_risk L d μ τ p) e -
        ibp_training_risk.risk(ibp_training_risk L d μ τ p) 0) = (fun p => ∫ xy, δ p xy ∂μ) := by
      funext p
      rw [hlrisk e p, hlrisk 0 p, hδeq, integral_sub (hli e p) (hli 0 p)]
    rw [hriskeq]
    -- The final expectation step uses a bound uniform over bounded inputs.
    -- Differentiability of F and Q gives anchored local linear bounds;
    -- the softmax weights sum to one, so loss changes obey the same bounds.
    let FF := fun p i j => F p i j
    let QQ := fun p i j => Q p i j
    have hFF : DifferentiableAt ℝ FF θ := hF θ
    have hQQ : DifferentiableAt ℝ QQ θ := hQ
    obtain ⟨CF, hCF, hbF⟩ := hFF.hasFDerivAt.isBigO_sub.exists_pos
    obtain ⟨CQ, hCQ, hbQ⟩ := hQQ.hasFDerivAt.isBigO_sub.exists_pos
    let U := {p | ‖FF p - FF θ‖ ≤ CF * ‖p - θ‖ ∧ ‖QQ p - QQ θ‖ ≤ CQ * ‖p - θ‖}
    have hU : U ∈ nhds θ := hbF.bound.and hbQ.bound
    let N : ℝ := d ⟨0, Nat.zero_lt_succ L⟩
    let S : ℝ := ∑ j, |e j|
    have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hbound : ∀ xy ∈ K, ∀ p ∈ U,
        ‖δ p xy - δ θ xy‖ ≤ (4 * CF * N + 2 * CQ * S) * ‖p - θ‖ := by
      intro xy hxy p hp
      have hxnorm : ‖xy.1‖ ≤ 1 := by
        have hh := hxy.1
        rwa [Metric.mem_closedBall, dist_zero_right] at hh
      have hsum : (∑ j, |xy.1 j|) ≤ N := by
        calc
          _ ≤ ∑ j : Fin (d ⟨0, Nat.zero_lt_succ L⟩), (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => (norm_le_pi_norm xy.1 j).trans hxnorm
          _ = N := by
            simp [N]
            exact Fintype.card_fin _
      have hfx : ∀ i, |(F p).mulVec xy.1 i - (F θ).mulVec xy.1 i| ≤ CF * N * ‖p - θ‖ := by
        intro i
        calc
          _ ≤ ‖FF p - FF θ‖ * ∑ j, |xy.1 j| :=
            Machinery.matrix_row_sub_norm_bound
              (FF p) (FF θ) xy.1 i
          _ ≤ (CF * ‖p - θ‖) * N :=
            mul_le_mul hp.1 hsum (Finset.sum_nonneg fun j _ => abs_nonneg _) (by positivity)
          _ = _ := by ring
      have hrx : ∀ i, |ρ p i - ρ θ i| ≤ CQ * S * ‖p - θ‖ := by
        intro i
        calc
          _ ≤ ‖QQ p - QQ θ‖ * S :=
            Machinery.matrix_row_sub_norm_bound
              (QQ p) (QQ θ) e i
          _ ≤ (CQ * ‖p - θ‖) * S := mul_le_mul_of_nonneg_right hp.2 hS
          _ = _ := by ring
      have he := Machinery.box_loss_change_bound
        ((F p).mulVec xy.1) ((F θ).mulVec xy.1) (ρ p) (ρ θ) xy.2 hfx hrx
      change |loss e p xy - loss e θ xy| ≤
        2 * (CF * N * ‖p - θ‖) + 2 * (CQ * S * ‖p - θ‖) at he
      have hz := Machinery.box_loss_change_bound
        ((F p).mulVec xy.1) ((F θ).mulVec xy.1) (fun _ => 0) (fun _ => 0) xy.2 hfx
        (show ∀ i, |(0 : ℝ) - 0| ≤ 0 by simp)
      have hz' : |loss 0 p xy - loss 0 θ xy| ≤ 2 * (CF * N * ‖p - θ‖) := by
        simpa only [loss, Matrix.mulVec_zero, Pi.zero_apply, sub_self, add_zero, ite_self, mul_zero] using hz
      rw [hδeq, Real.norm_eq_abs]
      calc
        _ = |(loss e p xy - loss e θ xy) - (loss 0 p xy - loss 0 θ xy)| := by congr 1; ring
        _ ≤ |loss e p xy - loss e θ xy| + |loss 0 p xy - loss 0 θ xy| := abs_sub _ _
        _ ≤ _ := by nlinarith [he, hz']
    -- Dominated differentiation now interchanges the parameter derivative
    -- and expectation. Averaging the already proved samplewise inequality
    -- yields the claimed inner product with v=∇τ.
    exact Machinery.integral_directional_nonpos
      μ δ θ v hK hμK hδc hδdiff hU hbound hae
  · intro hbound
    -- The last step of Theorem 3.9: 2Mc(1+c) ≤ 4Mc ≤ 1-c.
    exact Machinery.sufficient_numeric_bound
      hM hc₀ hc₁ hbound
  -- formalizer:proof-end
)
end Theorem_3p9
