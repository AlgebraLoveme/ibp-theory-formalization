module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Theorem_3p10.Machinery

-- formalizer:machinery-begin
lemma linear_box {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x e : Fin n → ℝ) (he : ∀ j, 0 ≤ e j) :
    (Definition.boxes x e (fun z => A.mulVec z)).2.2.1 =
      (A.mulVec x, (A.map abs).mulVec e) := by
  have ends : (Definition.boxes x e (fun z => A.mulVec z)).2.1 =
      (A.mulVec x - (A.map abs).mulVec e,
       A.mulVec x + (A.map abs).mulVec e) := by
    apply Prod.ext
    · funext i
      exact (Lemma_Bp1.Machinery.row_extrema
        (A i) x e he).1
    · funext i
      exact (Lemma_Bp1.Machinery.row_extrema
        (A i) x e he).2
  change ((boxes.hi(Definition.boxes x e (fun z => A.mulVec z)) +
      boxes.lo(Definition.boxes x e (fun z => A.mulVec z))) / 2,
    (boxes.hi(Definition.boxes x e (fun z => A.mulVec z)) -
      boxes.lo(Definition.boxes x e (fun z => A.mulVec z))) / 2) = _
  rw [ends]
  apply Prod.ext <;> funext i <;>
    simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.ofNat_apply] <;> ring

lemma orthogonal_entry_bound {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : U.transpose * U = 1) (i j : Fin d) : |U i j| ≤ 1 := by
  have hsum : ∑ p, U p j ^ 2 = 1 := by
    have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M j j) hU
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using he
  have hle : U i j ^ 2 ≤ ∑ p, U p j ^ 2 :=
    Finset.single_le_sum (fun p _ => sq_nonneg (U p j)) (Finset.mem_univ i)
  rw [hsum] at hle
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (U i j + 1), sq_nonneg (U i j - 1)]

lemma integrable_entry_product {d : ℕ}
    (μ : MeasureTheory.Measure (Fin d → Fin d → ℝ)) [MeasureTheory.IsProbabilityMeasure μ]
    (horth : ∀ᵐ U ∂μ, (U : Matrix (Fin d) (Fin d) ℝ).transpose * U = 1)
    (i p j : Fin d) :
    MeasureTheory.Integrable (fun U => |U i j| * |U p j|) μ := by
  have hc : Continuous (fun U : Fin d → Fin d → ℝ => |U i j| * |U p j|) := by
    fun_prop
  refine ⟨hc.aestronglyMeasurable, MeasureTheory.HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards [horth] with U hU
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
  exact (mul_le_mul (orthogonal_entry_bound U hU i j)
    (orthogonal_entry_bound U hU p j) (abs_nonneg _) (by norm_num)).trans (by norm_num)

lemma sequential_radius {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ)
    (x : Fin d → ℝ) (ε : ℝ) (hε : 0 < ε) (i : Fin d) :
    (Definition.boxes (Definition.boxes x (fun _ => ε) (fun z => A.transpose.mulVec z)).2.2.1.1
      (Definition.boxes x (fun _ => ε) (fun z => A.transpose.mulVec z)).2.2.1.2
      (fun z => A.mulVec z)).2.2.1.2 i / ε = ∑ j, ∑ p, |A i j| * |A p j| := by
  have hn : ∀ j, 0 ≤ (A.transpose.map abs).mulVec (fun _ => ε) j := by
    intro j
    change 0 ≤ ∑ p, |A p j| * ε
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (abs_nonneg _) hε.le)
  rw [linear_box A.transpose x (fun _ => ε) (fun _ => hε.le)]
  rw [linear_box A _ _ hn]
  change (∑ j, |A i j| * (∑ p, |A p j| * ε)) / ε = _
  simp_rw [Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
  exact mul_div_cancel_right₀ _ hε.ne'

lemma optimal_radius {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ)
    (x : Fin d → ℝ) (ε : ℝ) (hε : 0 < ε) (i : Fin d) :
    (Definition.boxes x (fun _ => ε) (fun z => (A * A.transpose).mulVec z)).2.2.1.2 i / ε =
      ∑ p, |∑ j, A i j * A p j| := by
  rw [linear_box (A * A.transpose) x (fun _ => ε) (fun _ => hε.le)]
  change (∑ p, |∑ j, A i j * A p j| * ε) / ε = _
  rw [← Finset.sum_mul, mul_div_cancel_right₀ _ hε.ne']

lemma invariant_integral {d : ℕ}
    (μ : MeasureTheory.Measure (Fin d → Fin d → ℝ))
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hmap : μ.map (fun U : Fin d → Fin d → ℝ =>
      (fun i j => ∑ p, V i p * U p j : Fin d → Fin d → ℝ)) = μ)
    (f : (Fin d → Fin d → ℝ) → ℝ) (hf : Continuous f) :
    (∫ U, f (fun i j => ∑ p, V i p * U p j) ∂μ) = ∫ U, f U ∂μ := by
  have hc : Continuous (fun U : Fin d → Fin d → ℝ =>
      (fun i j => ∑ p, V i p * U p j : Fin d → Fin d → ℝ)) := by
    fun_prop
  rw [← MeasureTheory.integral_map hc.aemeasurable hf.aestronglyMeasurable, hmap]

lemma permutation_entry {d : ℕ} (σ : Equiv.Perm (Fin d))
    (U : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (σ.permMatrix ℝ * U) i j = U (σ i) j := by
  change ((σ.permMatrix ℝ).mulVec (fun p => U p j)) i = _
  rw [Matrix.permMatrix_mulVec]
  rfl

lemma planar_angle_integral :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), |Real.cos θ * Real.sin θ|) = 2 := by
  have hc : Continuous (fun θ : ℝ => |Real.cos θ * Real.sin θ|) := by fun_prop
  have hp : Function.Periodic (fun θ : ℝ => |Real.cos θ * Real.sin θ|) (Real.pi / 2) := by
    intro θ
    simp [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, mul_comm]
  have hquarter : (∫ θ in (0 : ℝ)..(Real.pi / 2), |Real.cos θ * Real.sin θ|) = 1 / 2 := by
    calc
      _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.cos θ := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        dsimp only
        rw [Set.uIcc_of_le (by positivity)] at hθ
        rw [abs_of_nonneg (mul_nonneg
          (Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]))
          (Real.sin_nonneg_of_mem_Icc (by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])))]
        ring
      _ = 1 / 2 := by rw [integral_sin_mul_cos₁]; simp
  have hm := hp.intervalIntegral_add_zsmul_eq 4 0 (fun a b => hc.intervalIntegrable a b)
  norm_num only [zero_add, zsmul_eq_mul, Int.cast_ofNat] at hm
  have he : (4 : ℝ) * (Real.pi / 2) = 2 * Real.pi := by ring
  rw [he, hquarter] at hm
  norm_num at hm ⊢
  exact hm

lemma planar_rotation_integral (a b : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      |(Real.cos θ * a - Real.sin θ * b) *
        (Real.sin θ * a + Real.cos θ * b)|) = 2 * (a ^ 2 + b ^ 2) := by
  let z : ℂ := ⟨a, b⟩
  have ha : ‖z‖ * Real.cos z.arg = a := Complex.norm_mul_cos_arg z
  have hb : ‖z‖ * Real.sin z.arg = b := Complex.norm_mul_sin_arg z
  have hnorm : ‖z‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simpa [z, Complex.normSq_apply, pow_two] using Complex.sq_norm z
  have hid : ∀ θ : ℝ,
      |(Real.cos θ * a - Real.sin θ * b) * (Real.sin θ * a + Real.cos θ * b)| =
      ‖z‖ ^ 2 * |Real.cos (θ + z.arg) * Real.sin (θ + z.arg)| := by
    intro θ
    have he : (Real.cos θ * a - Real.sin θ * b) * (Real.sin θ * a + Real.cos θ * b) =
        ‖z‖ ^ 2 * (Real.cos (θ + z.arg) * Real.sin (θ + z.arg)) := by
      rw [← ha, ← hb, Real.cos_add, Real.sin_add]
      ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simp_rw [hid]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right
    (fun θ => |Real.cos θ * Real.sin θ|) z.arg]
  have hp : Function.Periodic (fun θ : ℝ => |Real.cos θ * Real.sin θ|) (2 * Real.pi) := by
    intro θ
    simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have ht := hp.intervalIntegral_add_eq z.arg 0
  simp only [zero_add] at ht
  rw [zero_add, add_comm (2 * Real.pi), ht, planar_angle_integral, hnorm]
  ring

lemma plane_rotation_matrix {d : ℕ} (i p : Fin d) (hip : i ≠ p) (θ : ℝ) :
    ∃ V : Matrix (Fin d) (Fin d) ℝ,
      (V.transpose * V = 1 ∧ V * V.transpose = 1) ∧
      ∀ (U : Matrix (Fin d) (Fin d) ℝ) j,
        (V * U) i j = Real.cos θ * U i j - Real.sin θ * U p j ∧
        (V * U) p j = Real.sin θ * U i j + Real.cos θ * U p j := by
  classical
  let V : Matrix (Fin d) (Fin d) ℝ := 1 +
    Matrix.single i i (Real.cos θ - 1) + Matrix.single p p (Real.cos θ - 1) +
    Matrix.single p i (Real.sin θ) + Matrix.single i p (-Real.sin θ)
  refine ⟨V, ?_, ?_⟩
  · have hs := Real.sin_sq_add_cos_sq θ
    constructor <;>
      dsimp only [V] <;>
      simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
        add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hip,
        Matrix.single_mul_single_of_ne _ _ _ _ hip.symm] <;>
      ext a b <;>
      simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.single_apply] <;>
      split_ifs <;> (try subst_vars) <;> (try contradiction) <;> nlinarith
  · intro U j
    dsimp only [V]
    simp only [add_mul, Matrix.one_mul, Matrix.add_apply]
    simp [Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne, hip, hip.symm]
    constructor <;> ring

lemma rotated_entry_integrable {d : ℕ}
    (μ : MeasureTheory.Measure (Fin d → Fin d → ℝ)) [MeasureTheory.IsProbabilityMeasure μ]
    (ho : ∀ᵐ U ∂μ, (U : Matrix (Fin d) (Fin d) ℝ).transpose * U = 1)
    (i p j : Fin d) :
    MeasureTheory.Integrable (fun z : ℝ × (Fin d → Fin d → ℝ) =>
      |(Real.cos z.1 * z.2 i j - Real.sin z.1 * z.2 p j) *
        (Real.sin z.1 * z.2 i j + Real.cos z.1 * z.2 p j)|)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod μ) := by
  rw [Set.uIoc_of_le (by positivity)]
  have hc : Continuous (fun z : ℝ × (Fin d → Fin d → ℝ) =>
      |(Real.cos z.1 * z.2 i j - Real.sin z.1 * z.2 p j) *
        (Real.sin z.1 * z.2 i j + Real.cos z.1 * z.2 p j)|) := by fun_prop
  refine ⟨hc.aestronglyMeasurable, MeasureTheory.HasFiniteIntegral.of_bounded (C := 4) ?_⟩
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_le hc.norm.measurable measurable_const)).mpr
  apply Filter.Eventually.of_forall
  intro θ
  filter_upwards [ho] with U hU
  have ha := orthogonal_entry_bound U hU i j
  have hb := orthogonal_entry_bound U hU p j
  have bound : ∀ t a : ℝ, |t| ≤ 1 → |a| ≤ 1 → |t * a| ≤ 1 := by
    intro t a ht ha
    rw [abs_mul]
    nlinarith [mul_le_mul ht ha (abs_nonneg a) (by norm_num : (0 : ℝ) ≤ 1)]
  have hca := bound _ _ (Real.abs_cos_le_one θ) ha
  have hsa := bound _ _ (Real.abs_sin_le_one θ) ha
  have hcb := bound _ _ (Real.abs_cos_le_one θ) hb
  have hsb := bound _ _ (Real.abs_sin_le_one θ) hb
  have hleft : |Real.cos θ * U i j - Real.sin θ * U p j| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  have hright : |Real.sin θ * U i j + Real.cos θ * U p j| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  simp only [Real.norm_eq_abs, abs_abs, abs_mul]
  nlinarith [mul_le_mul hleft hright (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]

lemma partial_square_sum_le (z : ℕ → ℝ) {k d : ℕ} (hkd : k ≤ d) :
    (∑ j ∈ Finset.range k, z j ^ 2) ≤ ∑ j ∈ Finset.range d, z j ^ 2 := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkd)
    (fun j _ _ => sq_nonneg (z j))

lemma normalized_partial_energy (z : ℕ → ℝ) {k d : ℕ} (hkd : k ≤ d) :
    (∑ j : Fin k, (z j / Real.sqrt (∑ p : Fin d, z p ^ 2)) ^ 2) =
      (∑ j ∈ Finset.range k, z j ^ 2) / (∑ j ∈ Finset.range d, z j ^ 2) := by
  have hn : 0 ≤ ∑ p : Fin d, z p ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg (z p))
  simp_rw [div_pow, Real.sq_sqrt hn]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun j => z j ^ 2),
    Fin.sum_univ_eq_sum_range (fun j => z j ^ 2)]

lemma energy_fraction_bounds {A T : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T) :
    0 ≤ A / T ∧ A / T ≤ 1 ∧ T * (A / T) = A := by
  by_cases hT : T = 0
  · have ha : A = 0 := le_antisymm (hT ▸ hAT) hA
    simp [hT, ha]
  · have ht : 0 < T := lt_of_le_of_ne (hA.trans hAT) (Ne.symm hT)
    refine ⟨div_nonneg hA ht.le, (div_le_one ht).mpr hAT, ?_⟩
    field_simp

lemma energy_sqrt_bounds {d S : ℝ} (hd : 0 ≤ d) (hS : 0 ≤ S) (hS1 : S ≤ 1) :
    (Real.sqrt (d * S * (1 - S))) ^ 2 ≤ d * S ∧
      Real.sqrt (d * S * (1 - S)) ≤ Real.sqrt d := by
  have hp : 0 ≤ d * S * (1 - S) := mul_nonneg (mul_nonneg hd hS) (sub_nonneg.mpr hS1)
  rw [Real.sq_sqrt hp]
  have hle : d * S * (1 - S) ≤ d * S := by nlinarith [mul_nonneg hd (sq_nonneg S)]
  exact ⟨hle, Real.sqrt_le_sqrt (hle.trans (by nlinarith))⟩

lemma orthogonal_row_completion {d : ℕ} (i : Fin d) (u : Fin d → ℝ)
    (hu : ∑ j, u j ^ 2 = 1) :
    ∃ V : Matrix (Fin d) (Fin d) ℝ,
      (V.transpose * V = 1 ∧ V * V.transpose = 1) ∧ V i = u ∧
      ∀ p, p ≠ i → u p = 0 → V p = (1 : Matrix (Fin d) (Fin d) ℝ) p := by
  classical
  let w : Fin d → ℝ := fun j => u j - if j = i then 1 else 0
  have hw : ∑ j, w j ^ 2 = 2 * (1 - u i) := by
    have he : ∀ j, w j ^ 2 = u j ^ 2 + if j = i then 1 - 2 * u j else 0 := by
      intro j
      dsimp [w]
      split_ifs <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, hu]
    simp
    ring
  by_cases hi : u i = 1
  · have hz : ∀ j, w j = 0 := by
      intro j
      have hle := Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ j)
      rw [hw, hi] at hle
      nlinarith [sq_nonneg (w j)]
    refine ⟨1, by simp, ?_, fun p _ _ => rfl⟩
    funext j
    have hj := hz j
    dsimp [w] at hj
    simp only [Matrix.one_apply]
    split_ifs with h <;> split_ifs at hj <;> (try omega) <;> linarith
  · let c : ℝ := (1 - u i)⁻¹
    let V : Matrix (Fin d) (Fin d) ℝ := 1 - c • Matrix.vecMulVec w w
    have hc : 1 - u i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
    have ht : V.transpose = V := by simp [V, Matrix.transpose_vecMulVec]
    have hVV : V * V = 1 := by
      dsimp only [V]
      rw [sub_mul, mul_sub, mul_sub]
      simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.vecMulVec_mul_vecMulVec]
      have hdot : w ⬝ᵥ w = 2 * (1 - u i) := by simpa only [dotProduct, ← pow_two] using hw
      rw [hdot]
      ext a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      dsimp only [c]
      field_simp
      <;> ring
    refine ⟨V, by rw [ht]; exact ⟨hVV, hVV⟩, ?_, ?_⟩
    · funext j
      dsimp [V, w, c]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
        Matrix.one_apply, if_pos rfl]
      split_ifs <;> (try subst_vars) <;> (try contradiction) <;> field_simp <;> ring
    · intro p hpi hp
      funext j
      simp [V, w, Matrix.vecMulVec_apply, hp, hpi]

lemma vector_invariant_integral {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : MeasureTheory.Measure Ω) (s : Ω → Fin d → ℝ) (hs : Measurable s)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hmap : ν.map (fun ω i => ∑ j, V i j * s ω j) = ν.map s)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    (∫ ω, f (fun i => ∑ j, V i j * s ω j) ∂ν) = ∫ ω, f (s ω) ∂ν := by
  have hm : Measurable (fun ω i => ∑ j, V i j * s ω j) := by fun_prop
  rw [← MeasureTheory.integral_map hm.aemeasurable hf.aestronglyMeasurable,
    hmap, MeasureTheory.integral_map hs.aemeasurable hf.aestronglyMeasurable]

lemma first_columns_orthonormal {d k : ℕ} (hkd : k ≤ d)
    (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.transpose * U = 1) :
    let A : Matrix (Fin d) (Fin k) ℝ := fun i j => U i (Fin.castLE hkd j)
    A.transpose * A = 1 := by
  dsimp only
  ext i j
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M (Fin.castLE hkd i) (Fin.castLE hkd j)) hU
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using he

lemma projector_off_diagonal_norm {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ)
    (hA : A.transpose * A = 1) (i : Fin d) :
    let P := A * A.transpose
    (∑ p ∈ Finset.univ.erase i, P p i ^ 2) =
      (∑ j, A i j ^ 2) * (1 - ∑ j, A i j ^ 2) := by
  classical
  let P := A * A.transpose
  have hs : P.transpose = P := by simp [P, Matrix.transpose_mul]
  have hp : P * P = P := by
    dsimp only [P]
    calc
      _ = A * (A.transpose * A) * A.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA, Matrix.mul_one]
  have hdiag : P i i = ∑ j, A i j ^ 2 := by simp [P, Matrix.mul_apply, pow_two]
  have hnorm : ∑ p, P p i ^ 2 = P i i := by
    have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i i) hp
    have heq : ∀ p, P i p = P p i := fun p =>
      congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M p i) hs
    simpa only [Matrix.mul_apply, heq, ← pow_two] using he
  have he := Finset.sum_erase_add Finset.univ (fun p => P p i ^ 2) (Finset.mem_univ i)
  dsimp only at he
  rw [hnorm, hdiag] at he
  dsimp only
  change (∑ p ∈ Finset.univ.erase i, P p i ^ 2) = _
  nlinarith

lemma integrable_projector_entry {d k : ℕ} (hkd : k ≤ d)
    (μ : MeasureTheory.Measure (Fin d → Fin d → ℝ)) [MeasureTheory.IsProbabilityMeasure μ]
    (ho : ∀ᵐ U ∂μ, (U : Matrix (Fin d) (Fin d) ℝ).transpose * U = 1)
    (i p : Fin d) :
    MeasureTheory.Integrable (fun U => |∑ j : Fin k, U i (Fin.castLE hkd j) * U p (Fin.castLE hkd j)|) μ := by
  have hc : Continuous (fun U : Fin d → Fin d → ℝ =>
      |∑ j : Fin k, U i (Fin.castLE hkd j) * U p (Fin.castLE hkd j)|) := by fun_prop
  refine ⟨hc.aestronglyMeasurable, MeasureTheory.HasFiniteIntegral.of_bounded (C := (k : ℝ)) ?_⟩
  filter_upwards [ho] with U hU
  simp only [Real.norm_eq_abs, abs_abs]
  calc
    _ ≤ ∑ j : Fin k, |U i (Fin.castLE hkd j) * U p (Fin.castLE hkd j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul (orthogonal_entry_bound U hU i _) (orthogonal_entry_bound U hU p _)
        (abs_nonneg _) (by norm_num)).trans (by norm_num)
    _ = _ := by simp

lemma partial_fin_square_sum_le {d k : ℕ} (hkd : k ≤ d) (u : Fin d → ℝ) :
    (∑ j : Fin k, u (Fin.castLE hkd j) ^ 2) ≤ ∑ j : Fin d, u j ^ 2 := by
  classical
  have he : (∑ j : Fin k, u (Fin.castLE hkd j) ^ 2) =
      ∑ j ∈ Finset.univ.image (Fin.castLE hkd), u j ^ 2 := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Fin.castLE_injective hkd hab
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => sq_nonneg (u j))

lemma sqrt_quadratic_le_one (t : ℝ) : Real.sqrt (t * (1 - t)) ≤ 1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · nlinarith [sq_nonneg (t - 1 / 2)]

lemma radius_mul_abs_coordinate {m : ℕ} (z : Fin m → ℝ) (i : Fin m) :
    Real.sqrt (∑ j, z j ^ 2) * |z i / Real.sqrt (∑ j, z j ^ 2)| = |z i| := by
  have hn : 0 ≤ ∑ j, z j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (z j))
  by_cases hr : Real.sqrt (∑ j, z j ^ 2) = 0
  · have hs : (∑ j, z j ^ 2) = 0 := by nlinarith [Real.sq_sqrt hn]
    have hi := Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
    have hz : z i = 0 := by rw [hs] at hi; nlinarith [sq_nonneg (z i)]
    simp [hr, hz]
  · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), mul_div_cancel₀ _ hr]

-- formalizer:machinery-end

end Theorem_3p10.Machinery
