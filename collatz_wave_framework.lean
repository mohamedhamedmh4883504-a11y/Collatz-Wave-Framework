-- ============================================================================
-- Collatz Wave Framework: Formalization of Accelerated Wave Dynamics in Lean 4
-- ============================================================================

-- 1. Parity Contrast: For any odd K, either (K - 1) or (K + 1) is divisible by 4
theorem k_minus_one_or_plus_one_div_four (K : Nat) (hK : K % 2 = 1) :
    (K - 1) % 4 = 0 ∨ (K + 1) % 4 = 0 := by
  omega

-- 2. Step-by-Step Fuel Depletion: 3*(2^(a+1)*M - 1) + 1 = 2*(2^a*(3*M) - 1)
theorem fuel_depletion_step (a M : Nat) (hM : M ≥ 1) :
    3 * (2 ^ (a + 1) * M - 1) + 1 = 2 * (2 ^ a * (3 * M) - 1) := by
  have hX : 2 ^ a * M ≥ 1 := Nat.mul_pos Nat.one_le_two_pow hM
  rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_comm _ 2, Nat.mul_left_comm (2 ^ a) 3 M]
  generalize 2 ^ a * M = X at *
  omega

-- 3. Guaranteed Wave Break at a = 1 (Numerator divisible by at least 4)
theorem wave_break_at_one (M : Nat) (hM_odd : M % 2 = 1) :
    (3 * (2 * M - 1) + 1) % 4 = 0 := by
  omega

-- Single accelerated odd step: (3x + 1) / 2
def odd_step (x : Nat) : Nat := (3 * x + 1) / 2

-- Iterate odd_step 'a' times
def climb : Nat → Nat → Nat
  | 0, x => x
  | a + 1, x => climb a (odd_step x)

-- Single fuel step using odd_step
theorem odd_step_fuel (a M : Nat) (hM : M ≥ 1) :
    odd_step (2 ^ (a + 1) * M - 1) = 2 ^ a * (3 * M) - 1 := by
  unfold odd_step
  rw [fuel_depletion_step a M hM]
  omega

-- 4. Full Wave Ascent Theorem (by Mathematical Induction)
-- Proves that 2^a * M - 1 reaches 3^a * M - 1 after 'a' steps for any natural number a
theorem full_wave_climb (a M : Nat) (hM : M ≥ 1) :
    climb a (2 ^ a * M - 1) = 3 ^ a * M - 1 := by
  induction a generalizing M with
  | zero =>
    simp [climb]
  | succ a ih =>
    dsimp [climb]
    rw [odd_step_fuel a M hM]
    rw [ih (3 * M) (by omega)]
    rw [Nat.pow_succ, Nat.mul_assoc]

-- 5. Wave Linking Equation
-- Relates previous wave parameters (a, M) to next wave (a_next, M_next) at e = 2
theorem wave_linking_equation (a M a_next M_next x_next : Nat)
    (hM : M ≥ 1) (hM_next : M_next ≥ 1)
    (h_break : 2 * x_next = 3 ^ a * M - 1)
    (h_next_form : x_next = 2 ^ a_next * M_next - 1) :
    2 ^ (a_next + 1) * M_next = 3 ^ a * M + 1 := by
  have h1 : 3 ^ a * M ≥ 1 := Nat.mul_pos (Nat.pow_pos (by decide)) hM
  have h2 : 2 ^ a_next * M_next ≥ 1 := Nat.mul_pos Nat.one_le_two_pow hM_next
  rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_comm _ 2]
  omega

-- 6. Global Wave Descent Condition
-- Proves strict descent (x_next < x) whenever division powers dominate ascent powers
theorem wave_global_descent (a e M x x_next : Nat)
    (he : e ≥ 1)
    (hx : x = 2 ^ a * M - 1)
    (h_next : 2 ^ (e - 1) * x_next = 3 ^ a * M - 1)
    (h_cond : (2 ^ (a + e - 1) - 3 ^ a) * M ≥ 2 ^ (e - 1)) :
    x_next < x := by
  have hp1 : 2 ^ (e - 1) ≥ 1 := Nat.one_le_two_pow
  have h_le : 3 ^ a ≤ 2 ^ (a + e - 1) := by
    rcases Nat.lt_or_ge (2 ^ (a + e - 1)) (3 ^ a) with h_lt | h_ge
    · have h_zero : 2 ^ (a + e - 1) - 3 ^ a = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h_lt)
      rw [h_zero, Nat.zero_mul] at h_cond
      omega
    · exact h_ge
  have h_expand : (2 ^ (a + e - 1) - 3 ^ a) * M = 2 ^ (a + e - 1) * M - 3 ^ a * M :=
    Nat.sub_mul _ _ _
  rw [h_expand] at h_cond
  have h_exp : a + e - 1 = (e - 1) + a := by omega
  have h_pow : 2 ^ (a + e - 1) = 2 ^ (e - 1) * 2 ^ a := by
    rw [h_exp, Nat.pow_add]
  have h_mul : 2 ^ (e - 1) * x = 2 ^ (a + e - 1) * M - 2 ^ (e - 1) := by
    rw [hx, Nat.mul_sub, ← Nat.mul_assoc, ← h_pow, Nat.mul_one]
  have hM : M ≥ 1 := by
    rcases Nat.eq_zero_or_pos M with rfl | h_pos
    · simp at h_cond
    · exact h_pos
  have h_3aM : 3 ^ a * M ≥ 1 := Nat.mul_pos (Nat.pow_pos (by decide)) hM
  have h_strict : 2 ^ (e - 1) * x_next < 2 ^ (e - 1) * x := by
    omega
  rcases Nat.lt_or_ge x_next x with h_ans | h_ge
  · exact h_ans
  · have h_bad : 2 ^ (e - 1) * x ≤ 2 ^ (e - 1) * x_next := Nat.mul_le_mul_left _ h_ge
    omega

-- 7. Corollary: Immediate descent for class (a = 1, e = 2) when M ≥ 2
theorem descent_a1_e2 (M x x_next : Nat)
    (hM : M ≥ 2)
    (hx : x = 2 ^ 1 * M - 1)
    (h_next : 2 ^ (2 - 1) * x_next = 3 ^ 1 * M - 1) :
    x_next < x := by
  apply wave_global_descent 1 2 M x x_next (by decide) hx h_next
  simp
  omega

-- 8. Corollary: Immediate descent for class (a = 2, e = 3) when M ≥ 1
theorem descent_a2_e3 (M x x_next : Nat)
    (hM : M ≥ 1)
    (hx : x = 2 ^ 2 * M - 1)
    (h_next : 2 ^ (3 - 1) * x_next = 3 ^ 2 * M - 1) :
    x_next < x := by
  apply wave_global_descent 2 3 M x x_next (by decide) hx h_next
  simp
  omega

-- 9. Two-Wave Composition Descent: (a₁ = 2, e₁ = 2) followed by (a₂ = 1, e₂ = 3)
theorem two_wave_descent (M x x₁ x₂ : Nat)
    (hM : M ≥ 1)
    (hx : x = 4 * M - 1)
    (hw1 : 2 * x₁ = 9 * M - 1)
    (hw2 : 4 * x₂ = 3 * x₁ - 1) :
    x₂ < x := by
  omega
-- 10. General Two-Wave Composition Equation
theorem general_two_wave_equation (a₁ e₁ a₂ e₂ M x₁ x₂ : Nat)
    (he₁ : e₁ ≥ 1)
    (he₂ : e₂ ≥ 1)
    (hw1 : 2 ^ (e₁ - 1) * x₁ = 3 ^ a₁ * M - 1)
    (hw2 : 2 ^ (e₂ - 1) * x₂ = 3 ^ a₂ * x₁ - 1) :
    2 ^ (e₁ + e₂ - 2) * x₂ = 3 ^ (a₁ + a₂) * M - (3 ^ a₂ + 2 ^ (e₁ - 1)) := by
  have h_exp : e₁ + e₂ - 2 = (e₁ - 1) + (e₂ - 1) := by omega
  have h_pow2 : 2 ^ (e₁ + e₂ - 2) = 2 ^ (e₁ - 1) * 2 ^ (e₂ - 1) := by
    rw [h_exp, Nat.pow_add]
  have h_pow3 : 3 ^ (a₁ + a₂) = 3 ^ a₂ * 3 ^ a₁ := by
    rw [Nat.add_comm, Nat.pow_add]
  have h_step1 : 2 ^ (e₁ + e₂ - 2) * x₂ = 2 ^ (e₁ - 1) * (3 ^ a₂ * x₁ - 1) := by
    rw [h_pow2, Nat.mul_assoc, hw2]
  have h_step2 : 2 ^ (e₁ - 1) * (3 ^ a₂ * x₁ - 1) =
      3 ^ a₂ * (2 ^ (e₁ - 1) * x₁) - 2 ^ (e₁ - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_left_comm]
  rw [h_step1, h_step2, hw1, Nat.mul_sub, Nat.mul_one, ← Nat.mul_assoc, ← h_pow3]
  exact Nat.sub_sub _ _ _

-- Apply wave step function 'f' n times
def apply_n (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => apply_n f n (f x)

-- Addition rule for iterated wave steps
theorem apply_n_add (f : Nat → Nat) (n m x : Nat) :
    apply_n f (n + m) x = apply_n f m (apply_n f n x) := by
  induction n generalizing x with
  | zero => simp [apply_n]
  | succ n ih =>
    rw [Nat.succ_add]
    dsimp [apply_n]
    rw [ih]

-- 11. Collatz Convergence by Wave Descent (Strong Induction)
-- Proves that if every x > 1 eventually drops below x, all positive integers reach 1
theorem collatz_by_wave_descent (f : Nat → Nat)
    (h_descent : ∀ x, x > 1 → ∃ k, 1 ≤ apply_n f k x ∧ apply_n f k x < x) :
    ∀ x, x ≥ 1 → ∃ n, apply_n f n x = 1 := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx
    rcases Nat.eq_or_lt_of_le hx with rfl | h_gt
    · exact ⟨0, rfl⟩
    · obtain ⟨k, h_ge1, h_lt⟩ := h_descent x h_gt
      obtain ⟨m, hm⟩ := ih (apply_n f k x) h_lt h_ge1
      refine ⟨k + m, ?_⟩
      rw [apply_n_add, hm]

-- 12. Verified Descent Step for class (a = 1, e = 2)
theorem verified_descent_step (M x x_next : Nat)
    (hM : M ≥ 2)
    (hx : x = 2 * M - 1)
    (h_next : 2 * x_next = 3 * M - 1) :
    x_next < x := by
  omega

-- 13. General Two-Wave Descent Condition
theorem two_wave_global_descent (a₁ e₁ a₂ e₂ M x x₁ x₂ : Nat)
    (ha₁ : a₁ ≥ 1)
    (he₁ : e₁ ≥ 1)
    (he₂ : e₂ ≥ 1)
    (hM : M ≥ 1)
    (hx : x = 2 ^ a₁ * M - 1)
    (hw1 : 2 ^ (e₁ - 1) * x₁ = 3 ^ a₁ * M - 1)
    (hw2 : 2 ^ (e₂ - 1) * x₂ = 3 ^ a₂ * x₁ - 1)
    (h_cond : 3 ^ (a₁ + a₂) * M + 2 ^ (e₁ + e₂ - 2) <
              2 ^ (a₁ + e₁ + e₂ - 2) * M + (3 ^ a₂ + 2 ^ (e₁ - 1))) :
    x₂ < x := by
  have h_eq := general_two_wave_equation a₁ e₁ a₂ e₂ M x₁ x₂ he₁ he₂ hw1 hw2
  have h_exp : a₁ + e₁ + e₂ - 2 = (e₁ + e₂ - 2) + a₁ := by omega
  have h_pow : 2 ^ (a₁ + e₁ + e₂ - 2) = 2 ^ (e₁ + e₂ - 2) * 2 ^ a₁ := by
    rw [h_exp, Nat.pow_add]
  have h_mul_x : 2 ^ (e₁ + e₂ - 2) * x = 2 ^ (a₁ + e₁ + e₂ - 2) * M - 2 ^ (e₁ + e₂ - 2) := by
    rw [hx, Nat.mul_sub, ← Nat.mul_assoc, ← h_pow, Nat.mul_one]
  have h_2e_all : 2 ^ (e₁ + e₂ - 2) ≥ 1 := Nat.one_le_two_pow
  have h2a1 : 2 ^ a₁ ≥ 2 := Nat.pow_le_pow_right (by decide : 2 > 0) ha₁
  have hx1 : x ≥ 1 := by
    have : 2 ^ a₁ * M ≥ 2 := Nat.le_trans h2a1 (Nat.le_mul_of_pos_right _ hM)
    omega
  have h_mul_x_pos : 2 ^ (e₁ + e₂ - 2) * x ≥ 1 := Nat.mul_pos h_2e_all hx1
  have h_strict : 2 ^ (e₁ + e₂ - 2) * x₂ < 2 ^ (e₁ + e₂ - 2) * x := by
    omega
  rcases Nat.lt_or_ge x₂ x with h_ans | h_ge
  · exact h_ans
  · have h_bad : 2 ^ (e₁ + e₂ - 2) * x ≤ 2 ^ (e₁ + e₂ - 2) * x₂ :=
      Nat.mul_le_mul_left _ h_ge
    generalize 2 ^ (e₁ + e₂ - 2) * x₂ = LHS at h_strict h_bad
    generalize 2 ^ (e₁ + e₂ - 2) * x = RHS at h_strict h_bad
    omega

-- 14. Direct Application of Theorem 13: Descent of (a₁=2, e₁=2) -> (a₂=1, e₂=3)
theorem two_wave_a2_e2_to_a1_e3 (M x x₁ x₂ : Nat)
    (hM : M ≥ 1)
    (hx : x = 2 ^ 2 * M - 1)
    (hw1 : 2 ^ (2 - 1) * x₁ = 3 ^ 2 * M - 1)
    (hw2 : 2 ^ (3 - 1) * x₂ = 3 ^ 1 * x₁ - 1) :
    x₂ < x := by
  apply two_wave_global_descent 2 2 1 3 M x x₁ x₂ (by decide) (by decide) (by decide) hM hx hw1 hw2
  simp
  omega

-- Cumulative ascent powers (A) and division powers (E) over N waves
def sum_a (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sum_a a n + a n

def sum_e (e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sum_e e n + (e n - 1)

-- 15. General N-Wave Composition Theorem (by Induction)
-- Proves that N consecutive waves satisfy: 2^(E_n) * x_n + C = 3^(A_n) * x_0
theorem n_wave_composition (a e x : Nat → Nat)
    (hx_pos : ∀ i, x i ≥ 1)
    (h_waves : ∀ i, 2 ^ (e i - 1) * x (i + 1) = 3 ^ (a i) * x i - 1) :
    ∀ n, ∃ C, 2 ^ (sum_e e n) * x n + C = 3 ^ (sum_a a n) * x 0 := by
  intro n
  induction n with
  | zero =>
    exact ⟨0, by simp [sum_e, sum_a]⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    have hw := h_waves n
    have h_3axn : 3 ^ (a n) * x n ≥ 1 :=
      Nat.mul_pos (Nat.pow_pos (by decide : 3 > 0)) (hx_pos n)
    have hw_plus : 2 ^ (e n - 1) * x (n + 1) + 1 = 3 ^ (a n) * x n := by
      omega
    have h_alg : (2 ^ (sum_e e n) * 2 ^ (e n - 1)) * x (n + 1) + 2 ^ (sum_e e n) =
        2 ^ (sum_e e n) * (2 ^ (e n - 1) * x (n + 1) + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
    refine ⟨2 ^ (sum_e e n) + 3 ^ (a n) * C, ?_⟩
    calc
      2 ^ (sum_e e (n + 1)) * x (n + 1) + (2 ^ (sum_e e n) + 3 ^ (a n) * C)
        = (2 ^ (sum_e e n) * 2 ^ (e n - 1)) * x (n + 1) + 2 ^ (sum_e e n) + 3 ^ (a n) * C := by
          simp [sum_e, Nat.pow_add, Nat.add_assoc]
      _ = 2 ^ (sum_e e n) * (2 ^ (e n - 1) * x (n + 1) + 1) + 3 ^ (a n) * C := by
          rw [h_alg]
      _ = 2 ^ (sum_e e n) * (3 ^ (a n) * x n) + 3 ^ (a n) * C := by
          rw [hw_plus]
      _ = 3 ^ (a n) * (2 ^ (sum_e e n) * x n + C) := by
          rw [Nat.mul_add, Nat.mul_left_comm]
      _ = 3 ^ (a n) * (3 ^ (sum_a a n) * x 0) := by
          rw [hC]
      _ = 3 ^ (sum_a a (n + 1)) * x 0 := by
          rw [sum_a, Nat.pow_add]
          ac_rfl

-- 16. Final Theorem: General N-Wave Global Descent Condition
-- Proves strict descent (x_n < x_0) whenever 3^(A_n) < 2^(E_n)
theorem n_wave_global_descent (a e x : Nat → Nat) (n : Nat)
    (hx_pos : ∀ i, x i ≥ 1)
    (h_waves : ∀ i, 2 ^ (e i - 1) * x (i + 1) = 3 ^ (a i) * x i - 1)
    (h_pow : 3 ^ (sum_a a n) < 2 ^ (sum_e e n)) :
    x n < x 0 := by
  obtain ⟨C, hC⟩ := n_wave_composition a e x hx_pos h_waves n
  have h1 : 2 ^ (sum_e e n) * x n ≤ 3 ^ (sum_a a n) * x 0 := by
    omega
  have h_step : (3 ^ (sum_a a n) + 1) * x 0 ≤ 2 ^ (sum_e e n) * x 0 :=
    Nat.mul_le_mul_right (x 0) h_pow
  rw [Nat.add_mul, Nat.one_mul] at h_step
  have hx0 := hx_pos 0
  have h_strict : 2 ^ (sum_e e n) * x n < 2 ^ (sum_e e n) * x 0 := by
    omega
  rcases Nat.lt_or_ge (x n) (x 0) with h_ans | h_ge
  · exact h_ans
  · have h_bad : 2 ^ (sum_e e n) * x 0 ≤ 2 ^ (sum_e e n) * x n :=
      Nat.mul_le_mul_left _ h_ge
    generalize 2 ^ (sum_e e n) * x n = LHS at h_strict h_bad
    generalize 2 ^ (sum_e e n) * x 0 = RHS at h_strict h_bad
    omega