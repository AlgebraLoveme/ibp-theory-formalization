module
public import Formalization.Result.helpers.Corollary_Ap2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_3p7

open Axioms Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Corollary_Ap2

/-- Hidden width is indexed by n+1, so every member has positive width. -/
theorem relu_initialization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d₀ d₂ : ℕ) (hd₀ : 0 < d₀) (hd₂ : 0 < d₂)
    (σ : Fin 2 → ℝ≥0) (X : Ω → Fin d₀ → ℝ)
    (W : ∀ n : ℕ, Ω → ∀ k : Fin 2,
      Matrix (Fin (![d₀,n+1,d₂] k.succ)) (Fin (![d₀,n+1,d₂] k.castSucc)) ℝ)
    (hinit : ∀ n,
      (gaussian_initialization μ 2 ![d₀,n+1,d₂] σ (W n) X).1 ∧
      (gaussian_initialization μ 2 ![d₀,n+1,d₂] σ (W n) X).2)
    (i : Fin d₂) :
    let rates := fun n ω =>
      (relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)).2.2.2.1
    let t := fun n : ℕ => Real.sqrt Real.pi * Real.Gamma (((n : ℝ) + 1) / 2) /
      ((n : ℝ) * Real.Gamma ((n : ℝ) / 2))
    (∀ n, ∀ᵐ ω ∂μ,
      (relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)).1) ∧
    (∀ n, 0 < ∫ ω, (rates n ω).2 i ∂μ) ∧
    Tendsto
      (fun n => ((∫ ω, (rates n ω).1 i ∂μ) / (∫ ω, (rates n ω).2 i ∂μ)) /
        (Real.sqrt 2 * t (n + 1)))
      atTop (nhds 1) := (by
  -- formalizer:proof-begin
  classical
  dsimp only
  have hdomain (n : ℕ) : ∀ᵐ ω ∂μ,
      (relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)).1 := by
    rcases (hinit n).1 with ⟨hprob, hL, hd, hσ, hInd, hLaw⟩
    letI := hprob
    rcases (hinit n).2 with ⟨hX, hXW, _, hXzero⟩
    have hXne : ∀ᵐ ω ∂μ, X ω ≠ 0 := by
      simpa only [ae_iff, not_not] using hXzero
    -- Appendix A: conditioning on nonzero X makes each Gaussian row's
    -- preactivation nondegenerate; finitely many rows are nonzero a.s.
    have hrow (k : Fin (n+1)) : ∀ᵐ ω ∂μ,
        (W n ω 0).mulVec (X ω) k ≠ 0 := by
      let Z : Fin d₀ → Ω → ℝ := fun j ω => (σ 0 : ℝ)⁻¹ * W n ω 0 k j
      have hZ (j : Fin d₀) : HasLaw (Z j) (gaussianReal 0 1) μ :=
        Lemma_3p7.Machinery.gaussian_standardized
          μ _ (σ 0) (hσ 0) (hLaw ⟨0, k, j⟩)
      have hiZ : iIndepFun Z μ :=
        (hInd.precomp (g := fun j : Fin d₀ => ⟨0, k, j⟩)
          (by intro a b h; simpa using h)).comp
          (fun _ z => (σ 0 : ℝ)⁻¹ * z) (fun _ => by fun_prop)
      have hXZ : IndepFun X (fun ω j => Z j ω) μ :=
        hXW.comp (φ := id)
          (ψ := fun (v : (Σ l : Fin 2,
            Fin (![d₀,n+1,d₂] l.succ) × Fin (![d₀,n+1,d₂] l.castSucc)) → ℝ)
            (j : Fin d₀) => (σ 0 : ℝ)⁻¹ * v ⟨0, k, j⟩)
          measurable_id (by fun_prop)
      have hn :=
        Machinery.gaussian_random_dot_ne_zero
          μ d₀ Z hZ hiZ X hX hXZ hXne
      filter_upwards [hn] with ω hω
      have heq : (∑ j, X ω j * Z j ω) =
          (σ 0 : ℝ)⁻¹ * (W n ω 0).mulVec (X ω) k := by
        simp only [Z, Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [heq] at hω
      exact fun h => hω (by rw [h, mul_zero])
    filter_upwards [ae_all_iff.mpr hrow] with ω hω
    change 1 ≤ 2 ∧ (∀ k, 0 < ![d₀,n+1,d₂] k) ∧ _
    refine ⟨hL, hd, ?_⟩
    intro k hk j
    have hk0 : k = 0 := Fin.ext (by omega)
    subst k
    change (W n ω 0).mulVec (X ω) j + 0 ≠ 0
    simpa only [add_zero] using hω j
  -- On the nonzero-preactivation event, a sufficiently small input box
  -- keeps every activation sign fixed. Its optimal and sequential boxes
  -- are those of the masked linear network, and their right derivatives
  -- are |W₂ D W₁|1 and |W₂| |D W₁|1 (Appendix A, primed radii).
  have hrates (n : ℕ) : ∀ᵐ ω ∂μ,
      let C : Matrix (Fin (n+1)) (Fin d₀) ℝ := fun k j =>
        (if 0 < (W n ω 0).mulVec (X ω) k then 1 else 0) * W n ω 0 k j
      let B : Matrix (Fin d₂) (Fin (n+1)) ℝ := W n ω 1
      (relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)).2.2.2.1 =
        (((B * C).map abs).mulVec (fun _ => 1),
          (B.map abs).mulVec ((C.map abs).mulVec (fun _ => 1))) := by
    filter_upwards [hdomain n] with ω hω
    apply Machinery.relu_local_rates
    intro k
    have hk := hω.2.2 0 (by norm_num) k
    change (W n ω 0).mulVec (X ω) k + 0 ≠ 0 at hk
    simpa only [add_zero] using hk
  -- Row reversal flips the activation but preserves the absolute path
  -- product. Gaussian absolute means therefore give σ₁σ₂/π per path,
  -- also after averaging over the independent nonzero input.
  have hpath (n : ℕ) (k : Fin (n+1)) (j : Fin d₀) :
      Integrable (fun ω => if 0 < (W n ω 0).mulVec (X ω) k then
        |W n ω 1 i k| * |W n ω 0 k j| else 0) μ ∧
      (∫ ω, if 0 < (W n ω 0).mulVec (X ω) k then
        |W n ω 1 i k| * |W n ω 0 k j| else 0 ∂μ) =
        (σ 1 : ℝ) * (σ 0 : ℝ) / Real.pi := by
    rcases (hinit n).1 with ⟨hprob, _, _, hσ, hInd, hLaw⟩
    letI := hprob
    rcases (hinit n).2 with ⟨hX, hXW, _, hXzero⟩
    let Z : (Σ l : Fin 2, Fin (![d₀,n+1,d₂] l.succ) ×
        Fin (![d₀,n+1,d₂] l.castSucc)) → Ω → ℝ :=
      fun p ω => (σ p.1 : ℝ)⁻¹ * W n ω p.1 p.2.1 p.2.2
    have hZ p : HasLaw (Z p) (gaussianReal 0 1) μ :=
      Lemma_3p7.Machinery.gaussian_standardized
        μ _ (σ p.1) (hσ p.1) (hLaw p)
    have hiZ : iIndepFun Z μ := hInd.comp
      (fun p z => (σ p.1 : ℝ)⁻¹ * z) (fun _ => by fun_prop)
    have hirow : iIndepFun (fun j : Fin d₀ => Z ⟨0,k,j⟩) μ :=
      hiZ.precomp (g := fun j : Fin d₀ => ⟨0,k,j⟩) (by intro a b h; simpa using h)
    have hvec :=
      Lemma_3p7.Machinery.independent_vectors
        μ Z (fun p => (hZ p).aemeasurable) hiZ
        (fun _ : Fin 1 => ⟨1,i,k⟩) (fun j : Fin d₀ => ⟨0,k,j⟩)
        (by intro a b h; have hh := congrArg Sigma.fst h; cases hh)
    have hYZ : IndepFun (Z ⟨1,i,k⟩) (fun ω (j : Fin d₀) => Z ⟨0,k,j⟩ ω) μ :=
      hvec.comp (measurable_pi_apply 0) measurable_id
    have hXjoint : IndepFun X
        (fun ω => (Z ⟨1,i,k⟩ ω, fun j : Fin d₀ => Z ⟨0,k,j⟩ ω)) μ :=
      hXW.comp measurable_id (show Measurable
        (fun (v : (Σ l : Fin 2, Fin (![d₀,n+1,d₂] l.succ) ×
            Fin (![d₀,n+1,d₂] l.castSucc)) → ℝ) =>
          ((σ 1 : ℝ)⁻¹ * v ⟨1,i,k⟩,
            fun j : Fin d₀ => (σ 0 : ℝ)⁻¹ * v ⟨0,k,j⟩)) by fun_prop)
    have hm :=
      Machinery.random_gated_gaussian_path_mean
        μ d₀ (fun j => Z ⟨0,k,j⟩) (Z ⟨1,i,k⟩) (fun j => hZ ⟨0,k,j⟩)
        (hZ ⟨1,i,k⟩) hirow hYZ X hX hXjoint
        (by simpa only [ae_iff, not_not] using hXzero) j
    have hs0 : (0 : ℝ) < σ 0 := by exact_mod_cast hσ 0
    have hs1 : (0 : ℝ) < σ 1 := by exact_mod_cast hσ 1
    have hz (p) (ω : Ω) : W n ω p.1 p.2.1 p.2.2 = (σ p.1 : ℝ) * Z p ω := by
      dsimp [Z]
      field_simp [ne_of_gt (show (0 : ℝ) < σ p.1 by exact_mod_cast hσ p.1)]
    have hp (ω : Ω) : (W n ω 0).mulVec (X ω) k =
        (σ 0 : ℝ) * ∑ j : Fin d₀, X ω j * Z ⟨0,k,j⟩ ω := by
      change (∑ j, W n ω 0 k j * X ω j) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hz ⟨0,k,j⟩ ω]
      ring
    have heq : (fun ω => if 0 < (W n ω 0).mulVec (X ω) k then
        |W n ω 1 i k| * |W n ω 0 k j| else 0) =
        (fun ω => ((σ 1 : ℝ) * (σ 0 : ℝ)) *
          (if 0 < ∑ j : Fin d₀, X ω j * Z ⟨0,k,j⟩ ω then
            |Z ⟨1,i,k⟩ ω| * |Z ⟨0,k,j⟩ ω| else 0)) := by
      funext ω
      simp only [hp, mul_pos_iff_of_pos_left hs0]
      rw [hz ⟨1,i,k⟩ ω, hz ⟨0,k,j⟩ ω]
      split_ifs <;> simp only [abs_mul, abs_of_pos hs0, abs_of_pos hs1, mul_zero] <;> ring
    rw [heq]
    exact ⟨hm.1.const_mul _, by rw [integral_const_mul, hm.2]; ring⟩
  -- Equation (relu_init_layerwise_radius): sum the d₀(n+1) paths.
  -- Positive variances and widths give a positive expected denominator,
  -- while all-inactive samples are still included with value zero.
  have hden (n : ℕ) :
      (∫ ω, relu_local_radii.s(relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)) i ∂μ) =
        (n+1 : ℝ) * (d₀ : ℝ) * ((σ 1 : ℝ) * (σ 0 : ℝ) / Real.pi) := by
    have heq : (fun ω =>
        relu_local_radii.s(relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)) i) =ᵐ[μ]
        (fun ω => ∑ k : Fin (n+1), ∑ j : Fin d₀,
          if 0 < (W n ω 0).mulVec (X ω) k then |W n ω 1 i k| * |W n ω 0 k j| else 0) := by
      filter_upwards [hrates n] with ω hω
      rw [hω]
      change (∑ k, |W n ω 1 i k| *
        ∑ j, |(if 0 < (W n ω 0).mulVec (X ω) k then 1 else 0) * W n ω 0 k j| * 1) = _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [integral_congr_ae heq]
    erw [integral_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun j _ => (hpath n k j).1))]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => (hpath n _ j).1)]
    simp_rw [(hpath n _ _).2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  -- For the optimal coefficient, condition on the first layer. The
  -- second-layer normal mean leaves sqrt(S_n), where S_n is the sum
  -- of gated squared row coordinates. Row symmetry gives mean 1/2
  -- and second moment 3/2 for each summand, hence variance 5/(4n)
  -- after normalization. The square-root estimate is uniform in x≠0,
  -- so independence permits averaging it over X.
  have hcoef (n : ℕ) (j : Fin d₀) :
      let F := fun ω => |∑ k : Fin (n+1),
        (if 0 < (W n ω 0).mulVec (X ω) k then W n ω 0 k j else 0) * W n ω 1 i k|
      Integrable F μ ∧
      |(∫ ω, F ω ∂μ) /
        ((σ 1 : ℝ) * (σ 0 : ℝ) * (Real.sqrt (n+1 : ℝ) * Real.sqrt (2 / Real.pi))) -
        Real.sqrt (1/2)| ≤ Real.sqrt ((5/4) / (n+1 : ℝ)) / Real.sqrt (1/2) := by
    rcases (hinit n).1 with ⟨hprob, _, _, hσ, hInd, hLaw⟩
    letI := hprob
    rcases (hinit n).2 with ⟨hX, hXW, _, hXzero⟩
    let Z : (Σ l : Fin 2, Fin (![d₀,n+1,d₂] l.succ) ×
        Fin (![d₀,n+1,d₂] l.castSucc)) → Ω → ℝ :=
      fun p ω => (σ p.1 : ℝ)⁻¹ * W n ω p.1 p.2.1 p.2.2
    have hZ p : HasLaw (Z p) (gaussianReal 0 1) μ :=
      Lemma_3p7.Machinery.gaussian_standardized
        μ _ (σ p.1) (hσ p.1) (hLaw p)
    have hiZ : iIndepFun Z μ := hInd.comp
      (fun p z => (σ p.1 : ℝ)⁻¹ * z) (fun _ => by fun_prop)
    have hirow k : iIndepFun (fun j : Fin d₀ => Z ⟨0,k,j⟩) μ :=
      hiZ.precomp (g := fun j : Fin d₀ => ⟨0,k,j⟩) (by intro a b h; simpa using h)
    have hiY : iIndepFun (fun k : Fin (n+1) => Z ⟨1,i,k⟩) μ :=
      hiZ.precomp (g := fun k : Fin (n+1) => ⟨1,i,k⟩) (by intro a b h; simpa using h)
    have hrows : Pairwise (fun k l : Fin (n+1) => IndepFun
        (fun ω (j : Fin d₀) => Z ⟨0,k,j⟩ ω) (fun ω (j : Fin d₀) => Z ⟨0,l,j⟩ ω) μ) := by
      intro k l hkl
      exact Lemma_3p7.Machinery.independent_vectors
        μ Z (fun p => (hZ p).aemeasurable) hiZ
        (fun j : Fin d₀ => ⟨0,k,j⟩) (fun j : Fin d₀ => ⟨0,l,j⟩)
        (by
          intro a b h
          apply hkl
          have hp : (k, a) = (l, b) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
          exact congrArg Prod.fst hp)
    have hvec :=
      Lemma_3p7.Machinery.independent_vectors
        μ Z (fun p => (hZ p).aemeasurable) hiZ
        (fun k : Fin (n+1) => ⟨1,i,k⟩) (fun p : Fin (n+1) × Fin d₀ => ⟨0,p.1,p.2⟩)
        (by intro a b h; have hh := congrArg Sigma.fst h; cases hh)
    have hYZ : IndepFun (fun ω (k : Fin (n+1)) => Z ⟨1,i,k⟩ ω)
        (fun ω (k : Fin (n+1)) (j : Fin d₀) => Z ⟨0,k,j⟩ ω) μ := by
      exact hvec.comp measurable_id
        (show Measurable (fun v : (Fin (n+1) × Fin d₀) → ℝ => fun k j => v (k,j)) by fun_prop)
    have hXjoint : IndepFun X
        (fun ω => ((fun (k : Fin (n+1)) (j : Fin d₀) => Z ⟨0,k,j⟩ ω),
          fun (k : Fin (n+1)) => Z ⟨1,i,k⟩ ω)) μ :=
      hXW.comp measurable_id (show Measurable
        (fun (v : (Σ l : Fin 2, Fin (![d₀,n+1,d₂] l.succ) ×
            Fin (![d₀,n+1,d₂] l.castSucc)) → ℝ) =>
          ((fun (k : Fin (n+1)) (j : Fin d₀) => (σ 0 : ℝ)⁻¹ * v ⟨0,k,j⟩),
            fun k : Fin (n+1) => (σ 1 : ℝ)⁻¹ * v ⟨1,i,k⟩)) by fun_prop)
    have hm :=
      Machinery.random_gated_normal_sum_bound
        μ (n+1) d₀ (by omega) (fun k j => Z ⟨0,k,j⟩) (fun k => Z ⟨1,i,k⟩)
        (fun k j => hZ ⟨0,k,j⟩) (fun k => hZ ⟨1,i,k⟩) hirow hiY hrows hYZ
        X hX hXjoint (by simpa only [ae_iff, not_not] using hXzero) j
    have hs0 : (0 : ℝ) < σ 0 := by exact_mod_cast hσ 0
    have hs1 : (0 : ℝ) < σ 1 := by exact_mod_cast hσ 1
    have hz (p) (ω : Ω) : W n ω p.1 p.2.1 p.2.2 = (σ p.1 : ℝ) * Z p ω := by
      dsimp [Z]
      field_simp [ne_of_gt (show (0 : ℝ) < σ p.1 by exact_mod_cast hσ p.1)]
    have hp (ω : Ω) (k : Fin (n+1)) : (W n ω 0).mulVec (X ω) k =
        (σ 0 : ℝ) * ∑ j : Fin d₀, X ω j * Z ⟨0,k,j⟩ ω := by
      change (∑ j, W n ω 0 k j * X ω j) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hz ⟨0,k,j⟩ ω]
      ring
    have heq : (fun ω => |∑ k : Fin (n+1),
        (if 0 < (W n ω 0).mulVec (X ω) k then W n ω 0 k j else 0) * W n ω 1 i k|) =
        (fun ω => ((σ 1 : ℝ) * (σ 0 : ℝ)) *
          |∑ k : Fin (n+1), (if 0 < ∑ j : Fin d₀, X ω j * Z ⟨0,k,j⟩ ω then
            Z ⟨0,k,j⟩ ω else 0) * Z ⟨1,i,k⟩ ω|) := by
      funext ω
      rw [← abs_of_pos (mul_pos hs1 hs0), ← abs_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [hp, mul_pos_iff_of_pos_left hs0]
      rw [hz ⟨0,k,j⟩ ω, hz ⟨1,i,k⟩ ω]
      split_ifs <;> ring
    dsimp only
    rw [heq]
    refine ⟨hm.1.const_mul _, ?_⟩
    rw [integral_const_mul, mul_div_mul_left _ _ (ne_of_gt (mul_pos hs1 hs0))]
    simpa only [Nat.cast_add, Nat.cast_one] using hm.2
  have hnum (n : ℕ) :
      |(∫ ω, relu_local_radii.r(relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)) i ∂μ) /
        (((σ 1 : ℝ) * (σ 0 : ℝ) * (Real.sqrt (n+1 : ℝ) * Real.sqrt (2 / Real.pi))) * d₀) -
        Real.sqrt (1/2)| ≤ Real.sqrt ((5/4) / (n+1 : ℝ)) / Real.sqrt (1/2) := by
    let F := fun (j : Fin d₀) ω => |∑ k : Fin (n+1),
      (if 0 < (W n ω 0).mulVec (X ω) k then W n ω 0 k j else 0) * W n ω 1 i k|
    have heq : (fun ω =>
        relu_local_radii.r(relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)) i) =ᵐ[μ]
        (fun ω => ∑ j, F j ω) := by
      filter_upwards [hrates n] with ω hω
      rw [hω]
      change (∑ j, |∑ k, W n ω 1 i k *
        ((if 0 < (W n ω 0).mulVec (X ω) k then 1 else 0) * W n ω 0 k j)| * 1) = _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [F]
      split_ifs <;> ring
    rw [integral_congr_ae heq, integral_finset_sum Finset.univ (fun j _ => (hcoef n j).1)]
    have h := Machinery.finite_average_bound
      d₀ hd₀ (fun j => (∫ ω, F j ω ∂μ) /
        ((σ 1 : ℝ) * (σ 0 : ℝ) * (Real.sqrt (n+1 : ℝ) * Real.sqrt (2 / Real.pi))))
      _ _ (fun j => (hcoef n j).2)
    simpa only [← Finset.sum_div, div_div] using h
  -- For the unmasked Gaussian sum T_n, the same square-root estimate
  -- uses Var(T_n/n)=2/n. The chi mean identifies its expectation with
  -- the Gamma ratio in Lemma 3.7.
  let M := fun n : ℕ => (Real.sqrt 2 * Real.Gamma (((n : ℝ) + 2) / 2) /
    Real.Gamma (((n : ℝ) + 1) / 2)) / Real.sqrt (n+1 : ℝ)
  have hchi (n : ℕ) : |M n - 1| ≤ Real.sqrt (2 / (n+1 : ℝ)) := by
    rcases (hinit n).1 with ⟨hprob, _, _, hσ, hInd, hLaw⟩
    letI := hprob
    let Z : Fin (n+1) → Ω → ℝ := fun k ω => (σ 1 : ℝ)⁻¹ * W n ω 1 i k
    have hZ k : HasLaw (Z k) (gaussianReal 0 1) μ :=
      Lemma_3p7.Machinery.gaussian_standardized
        μ _ (σ 1) (hσ 1) (hLaw ⟨1,i,k⟩)
    have hiZ : iIndepFun Z μ :=
      (hInd.precomp (g := fun k : Fin (n+1) => ⟨1,i,k⟩)
        (by intro a b h; simpa using h)).comp
        (fun _ z => (σ 1 : ℝ)⁻¹ * z) (fun _ => by fun_prop)
    have hb :=
      Machinery.gaussian_square_root_average_bound
        μ (n+1) (by omega) Z hZ hiZ
    simp_rw [Real.sqrt_div' _ (Nat.cast_nonneg (n+1))] at hb
    rw [integral_div, (external_gaussian_moments μ (n+1) Z hZ hiZ).2.2.2.2.2] at hb
    simpa [M, Nat.cast_add, Nat.cast_one, add_assoc, show (1:ℝ)+1=2 by norm_num] using hb
  refine ⟨hdomain, ?_, ?_⟩
  · intro n
    rw [hden]
    have hs := (hinit n).1.2.2.2.1
    have hs0 : (0 : ℝ) < σ 0 := by exact_mod_cast hs 0
    have hs1 : (0 : ℝ) < σ 1 := by exact_mod_cast hs 1
    exact mul_pos (mul_pos (by positivity) (by exact_mod_cast hd₀))
      (div_pos (mul_pos hs1 hs0) Real.pi_pos)
  · let A := fun n : ℕ =>
      (∫ ω, relu_local_radii.r(relu_local_radii 2 ![d₀,n+1,d₂] (W n ω) (fun _ => 0) (X ω)) i ∂μ) /
        (((σ 1 : ℝ) * (σ 0 : ℝ) * (Real.sqrt (n+1 : ℝ) * Real.sqrt (2 / Real.pi))) * d₀)
    have hdiv (c : ℝ) : Tendsto (fun n : ℕ => c / (n+1 : ℝ)) atTop (nhds 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) c).comp
        (tendsto_add_atTop_nat 1)
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
    have herr : Tendsto (fun n : ℕ => Real.sqrt ((5/4)/(n+1 : ℝ)) / Real.sqrt (1/2))
        atTop (nhds 0) := by
      simpa using ((hdiv (5/4)).sqrt.div_const (Real.sqrt (1/2)))
    have hA : Tendsto A atTop (nhds (Real.sqrt (1/2))) := by
      apply tendsto_iff_norm_sub_tendsto_zero.2
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => hnum n) herr
    have hM : Tendsto M atTop (nhds 1) := by
      apply tendsto_iff_norm_sub_tendsto_zero.2
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => hchi n)
        (by simpa using (hdiv 2).sqrt)
    -- Dividing the two expected rates cancels the dimensions and layer
    -- scales. The remaining ratio is sqrt(2) A_n/M_n, with limits
    -- A_n→sqrt(1/2) and M_n→1 from the two variance estimates above.
    have hlim := (hA.const_mul (Real.sqrt 2)).div hM (by norm_num : (1:ℝ) ≠ 0)
    have hc : Real.sqrt 2 * Real.sqrt (1/2) = 1 := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hc, div_one] at hlim
    apply hlim.congr'
    apply Filter.Eventually.of_forall
    intro n
    dsimp only [Pi.div_apply]
    rw [hden]
    have hs := (hinit n).1.2.2.2.1
    have hs0 : (0 : ℝ) < σ 0 := by exact_mod_cast hs 0
    have hs1 : (0 : ℝ) < σ 1 := by exact_mod_cast hs 1
    have hg := (external_gamma.1 (((n : ℝ)+2)/2) (by positivity)).1
    have hh := (external_gamma.1 (((n : ℝ)+1)/2) (by positivity)).1
    dsimp only [A, M]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    exact (Machinery.radius_ratio_normalization
      _ _ _ _ _ _ (by positivity) (by exact_mod_cast hd₀) (mul_pos hs1 hs0) hg hh).symm
  -- formalizer:proof-end
)
end Corollary_Ap2
