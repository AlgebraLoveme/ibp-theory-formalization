module
public import Formalization.Result.helpers.Theorem_3p10.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_Bp1

open Axioms Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Theorem_3p10

theorem box_reconstruction :
    let c := fun d : ℕ => 1 / (d : ℝ) + 2 * ((d : ℝ) - 1) / (Real.pi * (d : ℝ))
    let a := fun k : ℕ => 2 / Real.sqrt Real.pi *
      Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2)
    (∀ (d k : ℕ) (hkd : k ≤ d)
      (μ : Measure (Fin d → Fin d → ℝ)) (x : Fin d → ℝ) (ε : ℝ),
      (∀ U, (random_reconstruction d k hkd μ U x ε).1) →
      let R := fun U => random_reconstruction d k hkd μ U x ε
      (∀ U,
        let A := (R U).2.1
        let first := (boxes x (fun _ => ε) (fun z => A.transpose.mulVec z)).2.2.1
        (boxes x (fun _ => ε) (fun z => ((R U).2.2.2.1).mulVec z)).2.2.1.1 =
          (R U).2.2.2.2.1 ∧
        (boxes first.1 first.2 (fun z => A.mulVec z)).2.2.1.1 = (R U).2.2.2.2.1) ∧
      (∀ i, (∫ U, (R U).2.2.2.2.2.2 i / ε ∂μ) = (k : ℝ) * c d)) ∧
    Tendsto c atTop (nhds (2 / Real.pi)) ∧
    (∀ (d k : ℕ), 1 ≤ k → k ≤ d →
      (2 / Real.pi) * (k : ℝ) ≤ (k : ℝ) * c d ∧ (k : ℝ) * c d ≤ (k : ℝ)) ∧
    (∀ (k : ℕ) (hk : 1 ≤ k)
      (μ : ∀ n : ℕ, Measure (Fin (k+n) → Fin (k+n) → ℝ))
      (x : ∀ n : ℕ, Fin (k+n) → ℝ) (ε : ℕ → ℝ)
      (i : ∀ n : ℕ, Fin (k+n)),
      (∀ n U, (random_reconstruction (k+n) k (Nat.le_add_right k n)
        (μ n) U (x n) (ε n)).1) →
      Tendsto (fun n => ∫ U,
        random_reconstruction.opt(random_reconstruction (k+n) k (Nat.le_add_right k n)
          (μ n) U (x n) (ε n)) (i n) / ε n ∂(μ n))
        atTop (nhds (a k))) ∧
    Asymptotics.IsTheta atTop a (fun k : ℕ => Real.sqrt (k : ℝ)) := (by
  -- formalizer:proof-begin
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d k hkd μ x ε h
    have hε : 0 < ε := (h 0).2.1
    constructor
    · intro U
      -- Lemma B.1: the optimal hull has center Px. The first hull has
      -- center Aᵀx and radius |Aᵀ|ε1; propagating it gives center AAᵀx.
      let A : Matrix (Fin d) (Fin k) ℝ := fun i j => U i (Fin.castLE hkd j)
      have first := Machinery.linear_box
        A.transpose x (fun _ => ε) (fun _ => hε.le)
      have optimal := Machinery.linear_box
        (A * A.transpose) x (fun _ => ε) (fun _ => hε.le)
      have hn : ∀ i, 0 ≤ (A.transpose.map abs).mulVec (fun _ => ε) i := by
        intro i
        change 0 ≤ ∑ j, |A.transpose i j| * ε
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hε.le)
      have second := Machinery.linear_box
        A (A.transpose.mulVec x) ((A.transpose.map abs).mulVec (fun _ => ε)) hn
      change (boxes x (fun _ => ε) (fun z => (A * A.transpose).mulVec z)).2.2.1.1 =
          (A * A.transpose).mulVec x ∧
        (boxes (boxes x (fun _ => ε) (fun z => A.transpose.mulVec z)).2.2.1.1
          (boxes x (fun _ => ε) (fun z => A.transpose.mulVec z)).2.2.1.2
          (fun z => A.mulVec z)).2.2.1.1 = (A * A.transpose).mulVec x
      rw [optimal, first, second, Matrix.mulVec_mulVec]
      exact ⟨rfl, rfl⟩
    · intro i
      letI : IsProbabilityMeasure μ := (h 0).2.2.1
      have ho : ∀ᵐ U ∂μ, (U : Matrix (Fin d) (Fin d) ℝ).transpose * U = 1 :=
        ((h 0).2.2.2.1).mono (fun _ hU => hU.1)
      -- The first display of the reconstruction proof expands δ†/ε as
      -- Σ_j Σ_p |U_ij||U_pj|. Orthogonal support bounds each summand by 1,
      -- allowing both finite sums to pass through the expectation.
      have hr : ∀ U, random_reconstruction.seq(random_reconstruction d k hkd μ U x ε) i / ε =
          ∑ j : Fin k, ∑ p : Fin d, |U i (Fin.castLE hkd j)| * |U p (Fin.castLE hkd j)| := by
        intro U
        exact Machinery.sequential_radius
          (fun i j => U i (Fin.castLE hkd j)) x ε hε i
      -- Permuting rows preserves Haar law, so every diagonal column moment
      -- is equal. Their sum is 1 because each orthogonal column has norm 1.
      have diagonal : ∀ p j : Fin d, (∫ U, U p j ^ 2 ∂μ) = 1 / (d : ℝ) := by
        intro p j
        have same : ∀ q : Fin d, (∫ U, U p j ^ 2 ∂μ) = ∫ U, U q j ^ 2 ∂μ := by
          intro q
          let σ := Equiv.swap p q
          have h₁ : (σ.permMatrix ℝ).transpose * σ.permMatrix ℝ = 1 := by
            simp [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
          have h₂ : σ.permMatrix ℝ * (σ.permMatrix ℝ).transpose = 1 := by
            simp [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
          have hm := (h 0).2.2.2.2 (σ.permMatrix ℝ) ⟨h₁, h₂⟩
          have ht := Machinery.invariant_integral
            μ (σ.permMatrix ℝ) hm (fun U => U p j ^ 2) (by fun_prop)
          have hperm : ∀ U : Fin d → Fin d → ℝ,
              (∑ a, σ.permMatrix ℝ p a * U a j) = U (σ p) j := by
            intro U
            exact Machinery.permutation_entry
              σ U p j
          simp only [hperm] at ht
          simpa [σ] using ht.symm
        have hi : ∀ q : Fin d, Integrable (fun U => U q j ^ 2) μ := by
          intro q
          simpa only [← pow_two, sq_abs] using
            Machinery.integrable_entry_product
              μ ho q q j
        have hs : (∫ U, ∑ q : Fin d, U q j ^ 2 ∂μ) = 1 := by
          calc
            _ = ∫ _ : Fin d → Fin d → ℝ, (1 : ℝ) ∂μ := by
              apply integral_congr_ae
              filter_upwards [ho] with U hU
              have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M j j) hU
              simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using he
            _ = 1 := by simp
        rw [integral_finset_sum _ (fun q _ => hi q)] at hs
        simp_rw [← same] at hs
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        exact (eq_div_iff (by exact_mod_cast (show d ≠ 0 from Nat.ne_of_gt (Fin.pos p)))).mpr
          (by simpa [mul_comm] using hs)
      simp_rw [hr]
      rw [integral_finset_sum]
      · simp_rw [integral_finset_sum _ (fun p _ =>
          Machinery.integrable_entry_product
            μ ho i p _)]
        -- The spherical calculation is E|s_i s_p|=2/(πd)
        -- for distinct coordinates, obtained from the uniform planar angle.
        have off_diagonal : ∀ p j : Fin d, p ≠ i →
            (∫ U, |U i j| * |U p j| ∂μ) = 2 / (Real.pi * (d : ℝ)) := by
          intro p j hpi
          -- Average planar rotations. Haar invariance keeps the expectation
          -- fixed, while the angular integral equals twice the squared radius.
          let f := fun θ (U : Fin d → Fin d → ℝ) =>
            |(Real.cos θ * U i j - Real.sin θ * U p j) *
              (Real.sin θ * U i j + Real.cos θ * U p j)|
          have invariant : ∀ θ, (∫ U, f θ U ∂μ) = ∫ U, |U i j| * |U p j| ∂μ := by
            intro θ
            obtain ⟨V, hV, hrows⟩ :=
              Machinery.plane_rotation_matrix
                i p hpi.symm θ
            have hm := (h 0).2.2.2.2 V hV
            have ht := Machinery.invariant_integral
              μ V hm (fun U => |U i j| * |U p j|) (by fun_prop)
            have hr₁ : ∀ U : Fin d → Fin d → ℝ, (∑ a, V i a * U a j) =
                Real.cos θ * U i j - Real.sin θ * U p j := fun U => (hrows U j).1
            have hr₂ : ∀ U : Fin d → Fin d → ℝ, (∑ a, V p a * U a j) =
                Real.sin θ * U i j + Real.cos θ * U p j := fun U => (hrows U j).2
            simpa only [hr₁, hr₂, ← abs_mul] using ht
          have hf := Machinery.rotated_entry_integrable
            μ ho i p j
          have swap := intervalIntegral_integral_swap (f := f) hf
          simp_rw [invariant] at swap
          have pointwise : ∀ U, (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ U) =
              2 * (U i j ^ 2 + U p j ^ 2) := fun U =>
            Machinery.planar_rotation_integral
              (U i j) (U p j)
          simp_rw [pointwise] at swap
          have hi : ∀ q : Fin d, Integrable (fun U => U q j ^ 2) μ := by
            intro q
            simpa only [← pow_two, sq_abs] using
              Machinery.integrable_entry_product
                μ ho q q j
          rw [integral_const_mul, integral_add (hi i) (hi p), diagonal, diagonal] at swap
          simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at swap
          apply (eq_div_iff (ne_of_gt (mul_pos Real.pi_pos (by exact_mod_cast Fin.pos i)))).mpr
          have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Fin.pos i))
          field_simp [hd0] at swap
          nlinarith
        have column : ∀ j : Fin d,
            (∑ p : Fin d, ∫ U, |U i j| * |U p j| ∂μ) =
              1 / (d : ℝ) + 2 * ((d : ℝ) - 1) / (Real.pi * d) := by
          intro j
          have hm : ∀ p : Fin d, (∫ U, |U i j| * |U p j| ∂μ) =
              2 / (Real.pi * (d : ℝ)) +
                if p = i then 1 / (d : ℝ) - 2 / (Real.pi * d) else 0 := by
            intro p
            by_cases hp : p = i
            · subst p
              simp only [← pow_two, sq_abs, diagonal, ite_true]
              ring
            · rw [off_diagonal p j hp, if_neg hp, add_zero]
          simp_rw [hm]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        simp_rw [column]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      · intro j _
        exact integrable_finset_sum _ (fun p _ =>
          Machinery.integrable_entry_product
            μ ho i p _)
  · -- The explicit sphere-moment coefficient tends to 2/π as 1/d tends to zero.
    have ht := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (1 - 2 / Real.pi)
    have ht' := ht.const_add (2 / Real.pi)
    simp only [zero_mul, add_zero] at ht'
    apply ht'.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    field_simp
    <;> ring
  · -- Since d ≥ 1 and π ≥ 2, the exact coefficient lies between 2/π and 1.
    intro d k hk hkd
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hp := Real.pi_gt_three
    have hpd : 0 < Real.pi * (d : ℝ) := mul_pos Real.pi_pos (by linarith)
    have hlo : 2 / Real.pi ≤ 1 / (d : ℝ) + 2 * ((d : ℝ) - 1) / (Real.pi * d) := by
      field_simp
      nlinarith
    have hhi : 1 / (d : ℝ) + 2 * ((d : ℝ) - 1) / (Real.pi * d) ≤ 1 := by
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hd) (show 0 ≤ Real.pi - 2 by linarith)]
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg k)
    · simpa using mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg k)
  · intro k hk μ x ε i h
    -- Lemma B.1 gives δ*/ε as the absolute projector row sum, the starting
    -- point for the diagonal/off-diagonal expectation decomposition.
    have hr : ∀ n U,
        random_reconstruction.opt(random_reconstruction (k+n) k (Nat.le_add_right k n)
          (μ n) U (x n) (ε n)) (i n) / ε n =
        ∑ p : Fin (k+n), |∑ j : Fin k,
          U (i n) (Fin.castLE (Nat.le_add_right k n) j) *
          U p (Fin.castLE (Nat.le_add_right k n) j)| := by
      intro n U
      exact Machinery.optimal_radius
        (fun p j => U p (Fin.castLE (Nat.le_add_right k n) j))
        (x n) (ε n) ((h n U).2.1) (i n)
    simp_rw [hr]
    -- Couple the sphere rows by normalizing the first k+n coordinates of
    -- one independent Gaussian sequence, as in Appendix B's fixed-k limit.
    let ν : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)
    haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    have hZ : ∀ j : ℕ, HasLaw (fun ω : ℕ → ℝ => ω j) (gaussianReal 0 1) ν := by
      intro j
      exact ⟨(measurable_pi_apply j).aemeasurable, Measure.infinitePi_map_eval _ j⟩
    have hInd : iIndepFun (fun j (ω : ℕ → ℝ) => ω j) ν :=
      iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
    let A := fun ω : ℕ → ℝ => ∑ j ∈ Finset.range k, ω j ^ 2
    let T := fun n (ω : ℕ → ℝ) => ∑ j ∈ Finset.range (k+n), ω j ^ 2
    let S := fun n ω => A ω / T n ω
    let Y := fun n ω => Real.sqrt (((k+n : ℕ) : ℝ) * S n ω * (1 - S n ω))
    have hbounds : ∀ n ω, 0 ≤ S n ω ∧ S n ω ≤ 1 ∧ T n ω * S n ω = A ω := by
      intro n ω
      exact Machinery.energy_fraction_bounds
        (Finset.sum_nonneg (fun j _ => sq_nonneg (ω j)))
        (Machinery.partial_square_sum_le
          ω (Nat.le_add_right k n))
    have has : ∀ᵐ ω ∂ν, Tendsto (fun n => Y n ω) atTop (nhds (Real.sqrt (A ω))) := by
      have strong := (external_probability_limits ν).1 _ hZ hInd
      filter_upwards [strong] with ω hω
      have hd : Tendsto (fun n : ℕ => k+n) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left n k) tendsto_id
      have ht : Tendsto (fun n => T n ω / ((k+n : ℕ) : ℝ)) atTop (nhds 1) := hω.comp hd
      have hscaled : Tendsto (fun n => ((k+n : ℕ) : ℝ) * S n ω) atTop (nhds (A ω)) := by
        have he : ∀ n, ((k+n : ℕ) : ℝ) * S n ω = A ω / (T n ω / ((k+n : ℕ) : ℝ)) := by
          intro n
          dsimp only [S]
          rw [div_div_eq_mul_div]
          ring
        simp_rw [he]
        simpa using tendsto_const_nhds.div ht (by norm_num : (1 : ℝ) ≠ 0)
      have hinv : Tendsto (fun n : ℕ => 1 / ((k+n : ℕ) : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat.comp hd
      have hs : Tendsto (fun n => S n ω) atTop (nhds 0) := by
        have hmul := hscaled.mul hinv
        simp only [mul_zero] at hmul
        convert hmul using 1
        funext n
        have hd0 : ((k+n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k+n ≠ 0 by omega)
        field_simp
      have hy := (hscaled.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hs)).sqrt
      simpa only [sub_zero, mul_one] using hy
    -- Radius/direction independence gives E S_d=k/d: multiply S_d by
    -- the squared Gaussian radius and use E Z_j²=1 in the numerator.
    have gaussian : ∀ m : ℕ,
        (∀ j : Fin m, HasLaw (fun ω : ℕ → ℝ => ω j) (gaussianReal 0 1) ν) ∧
          iIndepFun (fun j : Fin m => fun ω : ℕ → ℝ => ω j) ν := by
      intro m
      exact ⟨fun j => hZ j, hInd.precomp Fin.val_injective⟩
    have square_moments : ∀ m : ℕ,
        Integrable (fun ω : ℕ → ℝ => ∑ j ∈ Finset.range m, ω j ^ 2) ν ∧
          (∫ ω, ∑ j ∈ Finset.range m, ω j ^ 2 ∂ν) = (m : ℝ) := by
      intro m
      have hm := (external_gaussian_moments ν m _ (gaussian m).1 (gaussian m).2).1
      have he : (fun ω : ℕ → ℝ => ∑ j ∈ Finset.range m, ω j ^ 2) =
          fun ω => ∑ j : Fin m, ω j ^ 2 := by
        funext ω
        exact (Fin.sum_univ_eq_sum_range (fun j => ω j ^ 2) m).symm
      rw [he]
      refine ⟨integrable_finset_sum _ (fun j _ => (hm j).2.1), ?_⟩
      rw [integral_finset_sum _ (fun j _ => (hm j).2.1)]
      simp only [(fun j => (hm j).2.2.2.2.1), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    have ES : ∀ n, (∫ ω, S n ω ∂ν) = (k : ℝ) / ((k+n : ℕ) : ℝ) := by
      intro n
      let r := fun ω : ℕ → ℝ => Real.sqrt (∑ j : Fin (k+n), ω j ^ 2)
      let s := fun ω (j : Fin (k+n)) => ω j / r ω
      have sphere := external_sphere ν (k+n) (by omega) _ (gaussian (k+n)).1 (gaussian (k+n)).2
      have he : ∀ ω, (∑ j : Fin k, s ω (Fin.castLE (Nat.le_add_right k n) j) ^ 2) = S n ω := by
        intro ω
        exact Machinery.normalized_partial_energy
          ω (Nat.le_add_right k n)
      have hr2 : ∀ ω, r ω ^ 2 = T n ω := by
        intro ω
        dsimp only [r, T]
        have hn : 0 ≤ ∑ j : Fin (k+n), ω j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (ω j))
        rw [Real.sq_sqrt hn]
        exact Fin.sum_univ_eq_sum_range (fun j => ω j ^ 2) (k+n)
      have hind : IndepFun (fun ω => r ω ^ 2) (fun ω => ∑ j : Fin k, s ω (Fin.castLE (Nat.le_add_right k n) j) ^ 2) ν :=
        sphere.2.1.comp (φ := fun t : ℝ => t ^ 2)
          (ψ := fun v : Fin (k+n) → ℝ => ∑ j : Fin k, v (Fin.castLE (Nat.le_add_right k n) j) ^ 2)
          (by fun_prop) (by fun_prop)
      simp_rw [he, hr2] at hind
      have hTmeas : Measurable (T n) := by dsimp [T]; fun_prop
      have hSmeas : Measurable (S n) := by dsimp [S, A, T]; fun_prop
      have hm := hind.integral_fun_mul_eq_mul_integral hTmeas.aestronglyMeasurable hSmeas.aestronglyMeasurable
      simp_rw [(fun ω => (hbounds n ω).2.2)] at hm
      rw [(square_moments k).2, (square_moments (k+n)).2] at hm
      apply (eq_div_iff (by exact_mod_cast (show k+n ≠ 0 by omega))).mpr
      simpa [mul_comm] using hm.symm
    have hYint : ∀ n, Integrable (Y n) ν ∧ Integrable (fun ω => Y n ω ^ 2) ν := by
      intro n
      have hm : Measurable (Y n) := by dsimp [Y, S, A, T]; fun_prop
      have hb : ∀ ω, Y n ω ^ 2 ≤ ((k+n : ℕ) : ℝ) * S n ω ∧ Y n ω ≤ Real.sqrt ((k+n : ℕ) : ℝ) := by
        intro ω
        exact Machinery.energy_sqrt_bounds
          (Nat.cast_nonneg _) (hbounds n ω).1 (hbounds n ω).2.1
      constructor
      · refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := Real.sqrt ((k+n : ℕ) : ℝ)) ?_⟩
        exact Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact (hb ω).2)
      · refine ⟨(hm.pow_const 2).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := ((k+n : ℕ) : ℝ)) ?_⟩
        exact Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact (hb ω).1.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbounds n ω).2.1 (Nat.cast_nonneg (k+n))))
    have hL2 : ∀ n, (∫ ω, Y n ω ^ 2 ∂ν) ≤ (k : ℝ) := by
      intro n
      have hm : Measurable (S n) := by dsimp [S, A, T]; fun_prop
      have hi : Integrable (S n) ν := ⟨hm.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := 1) (Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hbounds n ω).1]
          exact (hbounds n ω).2.1))⟩
      have hle := integral_mono (hYint n).2 (hi.const_mul ((k+n : ℕ) : ℝ))
        (fun ω => (Machinery.energy_sqrt_bounds
          (Nat.cast_nonneg (k+n)) (hbounds n ω).1 (hbounds n ω).2.1).1)
      rw [integral_const_mul, ES] at hle
      have hd0 : ((k+n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k+n ≠ 0 by omega)
      rw [mul_div_cancel₀ _ hd0] at hle
      exact hle
    -- The bounded-L² boundary upgrades almost-sure convergence of Y_d
    -- to convergence of its expectations to the chi-k mean.
    have hEY := (external_probability_limits ν).2 Y (fun ω => Real.sqrt (A ω)) k
      hYint (by exact (show Measurable (fun ω => Real.sqrt (A ω)) by dsimp [A]; fun_prop).aemeasurable)
      hL2 has
    have chi : (∫ ω, Real.sqrt (A ω) ∂ν) =
        Real.sqrt 2 * Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2) := by
      have hm := (external_gaussian_moments ν k _ (gaussian k).1 (gaussian k).2).2.2.2.2.2
      simp only [if_neg (show k ≠ 0 by omega)] at hm
      convert hm using 1
      congr 1
      funext ω
      congr 1
      exact (Fin.sum_univ_eq_sum_range (fun j => ω j ^ 2) k).symm
    rw [chi] at hEY
    let q := fun t : ℝ => Real.Gamma (t / 2) / (Real.sqrt Real.pi * Real.Gamma ((t+1) / 2))
    -- The scalar gamma-ratio asymptotic yields √m q_m → √2/√π.
    have hq : Tendsto (fun t : ℝ => Real.sqrt t * q t) atTop
        (nhds (Real.sqrt 2 / Real.sqrt Real.pi)) := by
      have hg := external_gamma.2.2.2.2.2.2 (1 / 2 : ℝ)
      have hx : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
        tendsto_id.atTop_div_const (by norm_num)
      have ht := (tendsto_const_nhds (x := Real.sqrt 2 / Real.sqrt Real.pi)).div (hg.comp hx) (by norm_num : (1 : ℝ) ≠ 0)
      have ht' : Tendsto (fun t : ℝ => (Real.sqrt 2 / Real.sqrt Real.pi) /
          ((Real.Gamma (t/2+1/2) / Real.Gamma (t/2)) / (t/2) ^ (1/2 : ℝ)))
          atTop (nhds (Real.sqrt 2 / Real.sqrt Real.pi)) := by simpa using ht
      apply ht'.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      dsimp only [q]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div ht.le 2]
      have ha : t / 2 + 1 / 2 = (t+1)/2 := by ring
      rw [ha]
      field_simp
    have hd : Tendsto (fun n : ℕ => ((k+n : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_atTop_mono (fun n => Nat.le_add_left n k) tendsto_id)
    have hi : Tendsto (fun n : ℕ => 1 / ((k+n : ℕ) : ℝ)) atTop (nhds 0) :=
      by simpa only [one_div] using tendsto_inv_atTop_zero.comp hd
    have hratio : Tendsto (fun n : ℕ => Real.sqrt ((((k+n : ℕ) : ℝ) - 1) / ((k+n : ℕ) : ℝ)))
        atTop (nhds 1) := by
      have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub hi).sqrt
      simp only [sub_zero, Real.sqrt_one] at ht
      convert ht using 1
      funext n
      congr 1
      have hd0 : ((k+n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k+n ≠ 0 by omega)
      field_simp
    have hprefactor : Tendsto (fun n : ℕ =>
        ((((k+n : ℕ) : ℝ) - 1) / Real.sqrt ((k+n : ℕ) : ℝ)) * q (((k+n : ℕ) : ℝ) - 1))
        atTop (nhds (Real.sqrt 2 / Real.sqrt Real.pi)) := by
      have ht := hratio.mul (hq.comp ((tendsto_atTop_add_const_right atTop (-1) hd)))
      simp only [one_mul] at ht
      apply ht.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hd1 : (1 : ℝ) ≤ ((k+n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k+n by omega)
      rw [Real.sqrt_div (sub_nonneg.mpr hd1)]
      have hs := Real.sq_sqrt (sub_nonneg.mpr hd1)
      dsimp only [Function.comp_def]
      simp only [← sub_eq_add_neg]
      calc
        _ = Real.sqrt (((k+n : ℕ) : ℝ) - 1) ^ 2 / Real.sqrt ((k+n : ℕ) : ℝ) *
            q (((k+n : ℕ) : ℝ) - 1) := by ring
        _ = _ := by rw [hs]
    have hdiag : Tendsto (fun n : ℕ => (k : ℝ) / ((k+n : ℕ) : ℝ)) atTop (nhds 0) := by
      simpa only [mul_zero, mul_one_div] using hi.const_mul (k : ℝ)
    -- Gaussian radius/direction independence computes the absolute sphere
    -- coordinate mean; rotational invariance extends it to any linear form.
    have sphere_linear_mean : ∀ (m : ℕ) (hm : 0 < m) (v : Fin m → ℝ),
        (∫ ω : ℕ → ℝ, |∑ j : Fin m, v j * (ω j / Real.sqrt (∑ a : Fin m, ω a ^ 2))| ∂ν) =
          q (m : ℝ) * Real.sqrt (∑ j, v j ^ 2) := by
      intro m hm v
      let zero : Fin m := ⟨0, hm⟩
      let r := fun ω : ℕ → ℝ => Real.sqrt (∑ a : Fin m, ω a ^ 2)
      let s := fun (ω : ℕ → ℝ) (j : Fin m) => ω j / r ω
      have hs := external_sphere ν m hm _ (gaussian m).1 (gaussian m).2
      have hg := external_gaussian_moments ν m _ (gaussian m).1 (gaussian m).2
      have coord : (∫ ω, |s ω zero| ∂ν) = q (m : ℝ) := by
        have hind := hs.2.1.comp (φ := id) (ψ := fun u : Fin m → ℝ => |u zero|)
          measurable_id (by fun_prop)
        have hrmeas : Measurable r := by dsimp [r]; fun_prop
        have hsmeas : Measurable (fun ω => |s ω zero|) := by dsimp [s, r]; fun_prop
        have he := hind.integral_fun_mul_eq_mul_integral hrmeas.aestronglyMeasurable hsmeas.aestronglyMeasurable
        have hprod : ∀ ω : ℕ → ℝ, r ω * |s ω zero| = |ω zero| := fun ω =>
          Machinery.radius_mul_abs_coordinate
            (fun j : Fin m => ω j) zero
        change (∫ ω, r ω * |s ω zero| ∂ν) = (∫ ω, r ω ∂ν) * (∫ ω, |s ω zero| ∂ν) at he
        simp_rw [hprod] at he
        rw [(hg.1 zero).2.2.2.1, hg.2.2.2.2.2] at he
        simp only [if_neg (Nat.ne_of_gt hm)] at he
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2) Real.pi] at he
        have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
        have hg₀ := (external_gamma.1 ((m : ℝ) / 2) (by positivity)).1
        have hg₁ := (external_gamma.1 (((m : ℝ) + 1) / 2) (by positivity)).1
        dsimp only [q]
        apply (eq_div_iff (by positivity)).mpr
        have he' := congrArg (fun t : ℝ => t * (Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2))) he
        field_simp at he'
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
      let R := Real.sqrt (∑ j, v j ^ 2)
      have hR : 0 ≤ R := Real.sqrt_nonneg _
      have hsum : R ^ 2 = ∑ j, v j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      by_cases hzero : R = 0
      · have hv : ∀ j, v j = 0 := by
          intro j
          have hj := Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ j)
          rw [← hsum, hzero] at hj
          nlinarith [sq_nonneg (v j)]
        simp [hv]
      · let u := fun j => v j / R
        have hu : ∑ j, u j ^ 2 = 1 := by
          dsimp only [u]
          simp_rw [div_pow]
          rw [← Finset.sum_div, ← hsum, div_self (pow_ne_zero _ hzero)]
        obtain ⟨V, hV, hrow, _⟩ :=
          Machinery.orthogonal_row_completion zero u hu
        have sm : Measurable s := by dsimp [s, r]; fun_prop
        have he := Machinery.vector_invariant_integral
          ν s sm V (hs.2.2 V hV.1 hV.2) (fun u => |u zero|) (by fun_prop)
        simp only [hrow] at he
        rw [coord] at he
        have hlin : ∀ ω : ℕ → ℝ, |∑ j, v j * s ω j| = R * |∑ j, u j * s ω j| := by
          intro ω
          rw [← abs_of_nonneg hR, ← abs_mul]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          dsimp only [u]
          field_simp
        change (∫ ω, |∑ j, v j * s ω j| ∂ν) = _
        simp_rw [hlin]
        rw [integral_const_mul, he]
        exact mul_comm _ _
    -- The row-law identity is the source's conditional-sphere
    -- calculation, with squared projected length S_d(1-S_d).
    have row_average : ∀ n, 2 ≤ k+n →
        (∫ U, ∑ p : Fin (k+n), |∑ j : Fin k,
          U (i n) (Fin.castLE (Nat.le_add_right k n) j) *
          U p (Fin.castLE (Nat.le_add_right k n) j)| ∂μ n) =
        ((((k+n : ℕ) : ℝ) - 1) / Real.sqrt ((k+n : ℕ) : ℝ)) * q (((k+n : ℕ) : ℝ) - 1) *
          (∫ ω, Y n ω ∂ν) + (k : ℝ) / ((k+n : ℕ) : ℝ) := by
      intro n hn
      letI : IsProbabilityMeasure (μ n) := (h n 0).2.2.1
      let sr := fun (ω : ℕ → ℝ) (a : Fin (k+n)) => ω a / Real.sqrt (∑ b : Fin (k+n), ω b ^ 2)
      have sr_meas : Measurable sr := by dsimp [sr]; fun_prop
      have sphere := external_sphere ν (k+n) (by omega) _ (gaussian (k+n)).1 (gaussian (k+n)).2
      -- Averaging a row completion transfers any bounded continuous row
      -- observable from Haar matrices to the normalized Gaussian sphere law.
      have row_transfer (f : (Fin (k+n) → ℝ) → ℝ) (hf : Continuous f)
          (C : ℝ) (hC : ∀ v, ‖f v‖ ≤ C) :
          (∫ U, f (U (i n)) ∂μ n) = ∫ ω, f (sr ω) ∂ν := by
        let F := fun (ω : ℕ → ℝ) (U : Fin (k+n) → Fin (k+n) → ℝ) =>
          f (fun b => ∑ a, sr ω a * U a b)
        have hm : Measurable (Function.uncurry F) := by
          dsimp [F, Function.uncurry]
          fun_prop
        have hiF : Integrable (Function.uncurry F) (ν.prod (μ n)) :=
          ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded
            (Filter.Eventually.of_forall (fun z => hC _))⟩
        have hleft : ∀ᵐ ω ∂ν, (∫ U, F ω U ∂μ n) = ∫ U, f (U (i n)) ∂μ n := by
          filter_upwards [sphere.1] with ω hω
          obtain ⟨V, hV, hv, _⟩ :=
            Machinery.orthogonal_row_completion
              (i n) (sr ω) hω
          have hinv := (h n 0).2.2.2.2 V hV
          have ht := Machinery.invariant_integral
            (μ n) V hinv (fun U => f (U (i n))) (by fun_prop)
          simpa only [F, hv] using ht
        have hright : ∀ᵐ U ∂μ n, (∫ ω, F ω U ∂ν) = ∫ ω, f (sr ω) ∂ν := by
          filter_upwards [(h n 0).2.2.2.1] with U hU
          have hmap := sphere.2.2 (Matrix.transpose U) (by simpa using hU.2) (by simpa using hU.1)
          have ht := Machinery.vector_invariant_integral
            ν sr sr_meas (Matrix.transpose U) hmap f hf
          simpa only [F, Matrix.transpose_apply, mul_comm] using ht
        have hswap := integral_integral_swap hiF
        rw [integral_congr_ae hleft, integral_congr_ae hright] at hswap
        simpa using hswap
      let energy := fun v : Fin (k+n) → ℝ => ∑ j : Fin k, v (Fin.castLE (Nat.le_add_right k n) j) ^ 2
      have hsenergy : ∀ ω, energy (sr ω) = S n ω := fun ω =>
        Machinery.normalized_partial_energy
          ω (Nat.le_add_right k n)
      have henergy : ∀ᵐ U ∂μ n, energy (U (i n)) ≤ 1 := by
        filter_upwards [(h n 0).2.2.2.1] with U hU
        have he := congrArg (fun M : Matrix (Fin (k+n)) (Fin (k+n)) ℝ => M (i n) (i n)) hU.2
        have hu : ∑ j, U (i n) j ^ 2 = 1 := by
          simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, ← pow_two] using he
        exact (Machinery.partial_fin_square_sum_le
          (Nat.le_add_right k n) (U (i n))).trans_eq hu
      have hdiag : (∫ U, energy (U (i n)) ∂μ n) = (k : ℝ) / ((k+n : ℕ) : ℝ) := by
        have he := row_transfer (fun v => min (energy v) 1) (by dsimp [energy]; fun_prop) 1 (fun v => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Finset.sum_nonneg (fun j _ => sq_nonneg _)) zero_le_one)]
          exact min_le_right _ _)
        have hl : (∫ U, min (energy (U (i n))) 1 ∂μ n) = ∫ U, energy (U (i n)) ∂μ n := by
          apply integral_congr_ae
          filter_upwards [henergy] with U hU
          exact min_eq_left hU
        rw [hl] at he
        simp_rw [hsenergy, (fun ω => min_eq_left (hbounds n ω).2.1)] at he
        exact he.trans (ES n)
      -- The projection onto the orthogonal complement has squared length
      -- S_d(1-S_d); transfer this radius to the common Gaussian coupling.
      have hradius : (∫ U, Real.sqrt (energy (U (i n)) * (1 - energy (U (i n)))) ∂μ n) =
          (∫ ω, Y n ω ∂ν) / Real.sqrt ((k+n : ℕ) : ℝ) := by
        have he := row_transfer (fun v => Real.sqrt (energy v * (1 - energy v)))
          (by dsimp [energy]; fun_prop) 1 (fun v => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
            exact Machinery.sqrt_quadratic_le_one _)
        rw [he]
        simp_rw [hsenergy]
        have hy : ∀ ω, Y n ω = Real.sqrt ((k+n : ℕ) : ℝ) * Real.sqrt (S n ω * (1 - S n ω)) := by
          intro ω
          dsimp only [Y]
          rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg _)]
        simp_rw [hy]
        rw [integral_const_mul, mul_div_cancel_left₀ _ (by positivity)]
      have hprojected : ∀ᵐ U ∂μ n,
          (∑ p ∈ Finset.univ.erase (i n),
            (∑ j : Fin k, U p (Fin.castLE (Nat.le_add_right k n) j) *
              U (i n) (Fin.castLE (Nat.le_add_right k n) j)) ^ 2) =
          energy (U (i n)) * (1 - energy (U (i n))) := by
        filter_upwards [(h n 0).2.2.2.1] with U hU
        let B : Matrix (Fin (k+n)) (Fin k) ℝ := fun p j => U p (Fin.castLE (Nat.le_add_right k n) j)
        have hB := Machinery.first_columns_orthonormal
          (Nat.le_add_right k n) U hU.1
        exact Machinery.projector_off_diagonal_norm
          B hB (i n)
      -- Average the orthogonal subgroup fixing row i. Its other row is a
      -- unit sphere vector in iᗮ, so each cross term has mean q_(d-1) times
      -- the projected length computed above. This implements conditioning
      -- by invariance and Fubini, without choosing a conditional kernel.
      have cross_mean : ∀ p : Fin (k+n), p ≠ i n →
          (∫ U, |∑ j : Fin k, U (i n) (Fin.castLE (Nat.le_add_right k n) j) *
            U p (Fin.castLE (Nat.le_add_right k n) j)| ∂μ n) =
          q (((k+n : ℕ) : ℝ) - 1) *
            (∫ U, Real.sqrt (energy (U (i n)) * (1 - energy (U (i n)))) ∂μ n) := by
        intro p hpi
        let e : Fin (k+n-1) ≃ ↥(Finset.univ.erase (i n)) :=
          (Fintype.equivFinOfCardEq (by simp)).symm
        have esum (f : Fin (k+n) → ℝ) :
            (∑ a : Fin (k+n-1), f (e a)) = ∑ a ∈ Finset.univ.erase (i n), f a := by
          rw [← Finset.sum_coe_sort (Finset.univ.erase (i n)) f]
          exact e.sum_comp (fun a => f a)
        let s := fun (ω : ℕ → ℝ) (a : Fin (k+n-1)) =>
          ω a / Real.sqrt (∑ b : Fin (k+n-1), ω b ^ 2)
        have hs := external_sphere ν (k+n-1) (by omega) _ (gaussian (k+n-1)).1 (gaussian (k+n-1)).2
        let coeff := fun (U : Fin (k+n) → Fin (k+n) → ℝ) (a : Fin (k+n)) =>
          ∑ j : Fin k, U (i n) (Fin.castLE (Nat.le_add_right k n) j) *
            U a (Fin.castLE (Nat.le_add_right k n) j)
        let F := fun (ω : ℕ → ℝ) (U : Fin (k+n) → Fin (k+n) → ℝ) =>
          |∑ a : Fin (k+n-1), s ω a * coeff U (e a)|
        have sint : ∀ a : Fin (k+n-1), Integrable (fun ω => s ω a) ν := by
          intro a
          have hm : Measurable (fun ω => s ω a) := by dsimp [s]; fun_prop
          refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
          filter_upwards [hs.1] with ω hω
          have hb := Finset.single_le_sum (fun b _ => sq_nonneg (s ω b)) (Finset.mem_univ a)
          change (∑ b, s ω b ^ 2) = 1 at hω
          rw [hω] at hb
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> nlinarith [sq_nonneg (s ω a + 1), sq_nonneg (s ω a - 1)]
        have cint : ∀ a, Integrable (fun U => coeff U a) (μ n) := by
          intro a
          have hm : Measurable (fun U => coeff U a) := by dsimp [coeff]; fun_prop
          apply (integrable_norm_iff hm.aestronglyMeasurable).mp
          simpa only [Real.norm_eq_abs] using
            Machinery.integrable_projector_entry
              (Nat.le_add_right k n) (μ n) (((h n 0).2.2.2.1).mono (fun _ hU => hU.1)) (i n) a
        have hint : Integrable (Function.uncurry F) (ν.prod (μ n)) :=
          (integrable_finset_sum _ (fun a _ => (sint a).mul_prod (cint (e a)))).abs
        have hright : ∀ᵐ U ∂μ n, (∫ ω, F ω U ∂ν) =
            q (((k+n : ℕ) : ℝ) - 1) * Real.sqrt (energy (U (i n)) * (1 - energy (U (i n)))) := by
          filter_upwards [hprojected] with U hU
          have he := sphere_linear_mean (k+n-1) (by omega) (fun a => coeff U (e a))
          have hcast : ((k+n-1 : ℕ) : ℝ) = ((k+n : ℕ) : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ k+n), Nat.cast_one]
          have heq : (∑ a : Fin (k+n-1), coeff U (e a) ^ 2) =
              energy (U (i n)) * (1 - energy (U (i n))) := by
            rw [esum (fun a => coeff U a ^ 2)]
            simpa only [coeff, mul_comm] using hU
          simpa only [F, s, mul_comm, hcast, heq] using he
        have hleft : ∀ᵐ ω ∂ν, (∫ U, F ω U ∂μ n) = ∫ U, |coeff U p| ∂μ n := by
          filter_upwards [hs.1] with ω hω
          let w : Fin (k+n) → ℝ := fun a =>
            if ha : a = i n then 0 else s ω (e.symm ⟨a, Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩⟩)
          have wi : w (i n) = 0 := by simp [w]
          have we : ∀ a : Fin (k+n-1), w (e a) = s ω a := by
            intro a
            have ha := (Finset.mem_erase.mp (e a).property).1
            simp [w, ha]
          have hw : ∑ a, w a ^ 2 = 1 := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i n)), ← esum (fun a => w a ^ 2)]
            simp_rw [we, wi]
            simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using hω
          obtain ⟨V, hV, hp, hfix⟩ :=
            Machinery.orthogonal_row_completion p w hw
          have hiv := hfix (i n) hpi.symm wi
          have hirow : ∀ (U : Fin (k+n) → Fin (k+n) → ℝ) b,
              (∑ a, V (i n) a * U a b) = U (i n) b := by
            intro U b
            rw [hiv]
            simp [Matrix.one_apply]
          have hprow : ∀ (U : Fin (k+n) → Fin (k+n) → ℝ) b,
              (∑ a, V p a * U a b) = ∑ a : Fin (k+n-1), s ω a * U (e a) b := by
            intro U b
            rw [hp, ← Finset.sum_erase_add _ _ (Finset.mem_univ (i n)), wi, zero_mul, add_zero,
              ← esum (fun a => w a * U a b)]
            simp_rw [we]
          have hinv := (h n 0).2.2.2.2 V hV
          have ht := Machinery.invariant_integral
            (μ n) V hinv (fun U => |coeff U p|) (by dsimp [coeff]; fun_prop)
          have he : ∀ U : Fin (k+n) → Fin (k+n) → ℝ,
              |coeff (fun a b => ∑ t, V a t * U t b) p| = F ω U := by
            intro U
            dsimp only [coeff, F]
            simp only [hirow, hprow]
            congr 1
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro j _
            ring
          simpa only [he] using ht
        have hswap := integral_integral_swap hint
        rw [integral_congr_ae hleft, integral_congr_ae hright, integral_const_mul] at hswap
        simpa using hswap
      -- Sum the d-1 equal cross-term expectations and add E P_ii=k/d,
      -- obtaining the source formula used in the final limit.
      have hint : ∀ p : Fin (k+n), Integrable
          (fun U => |∑ j : Fin k, U (i n) (Fin.castLE (Nat.le_add_right k n) j) *
            U p (Fin.castLE (Nat.le_add_right k n) j)|) (μ n) := fun p =>
        Machinery.integrable_projector_entry
          (Nat.le_add_right k n) (μ n) (((h n 0).2.2.2.1).mono (fun _ hU => hU.1)) (i n) p
      rw [integral_finset_sum _ (fun p _ => hint p)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i n))]
      have hdiag' : (∫ U, |∑ j : Fin k, U (i n) (Fin.castLE (Nat.le_add_right k n) j) *
          U (i n) (Fin.castLE (Nat.le_add_right k n) j)| ∂μ n) = (k : ℝ) / ((k+n : ℕ) : ℝ) := by
        have he : ∀ U : Fin (k+n) → Fin (k+n) → ℝ,
            |∑ j : Fin k, U (i n) (Fin.castLE (Nat.le_add_right k n) j) * U (i n) (Fin.castLE (Nat.le_add_right k n) j)| = energy (U (i n)) := by
          intro U
          rw [show (∑ j : Fin k, U (i n) (Fin.castLE (Nat.le_add_right k n) j) * U (i n) (Fin.castLE (Nat.le_add_right k n) j)) = energy (U (i n)) by simp only [energy, pow_two]]
          exact abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))
        simpa only [he] using hdiag
      rw [hdiag']
      have hsum := Finset.sum_congr (s₁ := Finset.univ.erase (i n)) rfl
        (fun p hp => cross_mean p (Finset.mem_erase.mp hp).1)
      rw [hsum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hradius]
      rw [Nat.cast_sub (by omega : 1 ≤ k+n), Nat.cast_one]
      ring
    have hlim := (hprefactor.mul hEY.2).add hdiag
    have hc : (Real.sqrt 2 / Real.sqrt Real.pi) *
        (Real.sqrt 2 * Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2)) + 0 =
        2 / Real.sqrt Real.pi * Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2) := by
      have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ = (Real.sqrt 2 * Real.sqrt 2) / Real.sqrt Real.pi *
          Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2) := by ring
        _ = _ := by rw [hs]
    rw [hc] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (row_average n (by omega)).symm
  · -- The scalar gamma-ratio asymptotic at x=k/2 yields a nonzero
    -- limit for a(k)/√k, hence the final Θ(√k) assertion.
    have hg := Axioms.external_gamma.2.2.2.2.2.2 (1 / 2 : ℝ)
    have hx : Tendsto (fun k : ℕ => (k : ℝ) / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    have ht := hg.comp hx
    have hs : ∀ k : ℕ, Real.sqrt ((k : ℝ) / 2) = Real.sqrt (k : ℝ) / Real.sqrt 2 :=
      fun k => Real.sqrt_div (Nat.cast_nonneg k) 2
    have hratio : Tendsto
        (fun k : ℕ => (2 / Real.sqrt Real.pi *
          Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2)) /
          Real.sqrt (k : ℝ)) atTop (nhds ((2 / Real.sqrt Real.pi) / Real.sqrt 2)) := by
      have ht' := ht.const_mul ((2 / Real.sqrt Real.pi) / Real.sqrt 2)
      simp only [mul_one] at ht'
      apply ht'.congr'
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hgpos := (Axioms.external_gamma.1 ((k : ℝ) / 2) (by positivity)).1
      dsimp only [Function.comp_def]
      rw [← Real.sqrt_eq_rpow, hs]
      have ha : (k : ℝ) / 2 + 1 / 2 = ((k : ℝ) + 1) / 2 := by ring
      rw [ha]
      field_simp
    exact (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio (by positivity)).symm
  -- formalizer:proof-end
)
end Theorem_3p10
