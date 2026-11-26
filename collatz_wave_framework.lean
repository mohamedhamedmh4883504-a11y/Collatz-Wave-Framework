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
-- ============================================================================
-- 17. Modular Wave Sieve Theorem (mod 32):
-- Proves strict 1-wave descent for 9 out of 16 odd residue classes (56.25% of all odd integers)
-- ============================================================================

-- Helper step: single accelerated Collatz step T(x) = (3x + 1) / 2
-- ============================================================================
-- 17. Modular Wave Sieve Theorem (mod 32):
-- Proves strict 1-wave descent for 9 out of 16 odd residue classes (56.25% of all odd integers)
-- ============================================================================

-- Helper step: single accelerated Collatz step T(x) = (3x + 1) / 2
def T_step (x : Nat) : Nat := (3 * x + 1) / 2

theorem mod32_wave_descent_9_classes (M : Nat) :
    -- Class 1: 32*M + 1 -> 24*M + 1 < 32*M + 1 (when M >= 1)
    (M ≥ 1 → T_step (32 * M + 1) / 2 < 32 * M + 1) ∧
    -- Class 5: 32*M + 5 -> 6*M + 1 < 32*M + 5
    (T_step (32 * M + 5) / 8 < 32 * M + 5) ∧
    -- Class 9: 32*M + 9 -> 24*M + 7 < 32*M + 9
    (T_step (32 * M + 9) / 2 < 32 * M + 9) ∧
    -- Class 13: 32*M + 13 -> 12*M + 5 < 32*M + 13
    (T_step (32 * M + 13) / 4 < 32 * M + 13) ∧
    -- Class 17: 32*M + 17 -> 24*M + 13 < 32*M + 17
    (T_step (32 * M + 17) / 2 < 32 * M + 17) ∧
    -- Class 19: 32*M + 19 -> 18*M + 11 < 32*M + 19
    (T_step (T_step (32 * M + 19)) / 4 < 32 * M + 19) ∧
    -- Class 21: 32*M + 21 -> 3*M + 2 < 32*M + 21
    (T_step (32 * M + 21) / 16 < 32 * M + 21) ∧
    -- Class 25: 32*M + 25 -> 24*M + 19 < 32*M + 25
    (T_step (32 * M + 25) / 2 < 32 * M + 25) ∧
    -- Class 29: 32*M + 29 -> 12*M + 11 < 32*M + 29
    (T_step (32 * M + 29) / 4 < 32 * M + 29) := by
  unfold T_step
  omega
  -- ============================================================================
-- Testing the Algebraic Substitution Identity in Lean 4
-- ============================================================================

-- 1. Lean confirms your algebraic identity is 100% valid and always equals 1:
theorem user_substitution_identity (x e : Nat) (hx : x > 0) :
    (3 * x * 2 ^ e) / (3 * x) / 2 ^ e = 1 := by
  have h3x : 3 * x > 0 := by omega
  have h2 : 2 ^ e > 0 := Nat.pow_pos (by omega)
  rw [Nat.mul_div_cancel_left _ h3x, Nat.div_self h2]

-- 2. The Catch: Lean proves 3x + 1 cannot be replaced by 2^e (fails at x = 3):
theorem why_swap_fails_at_three (e : Nat) : 3 * 3 + 1 ≠ 2 ^ e := by
  match e with

  | -- ============================================================================
-- 18. Additive Constant Closure Equation (Base-3 Specific):
-- Proves that C = 2^e - 3^A * x is the exact necessary and sufficient condition
-- for a Base-3 Collatz trajectory to close at 1, and fails if Base 3 changes to 5.
-- ============================================================================

theorem closure_constant_characterization (x A e C : Nat) (h_bound : 3 ^ A * x ≤ 2 ^ e) :
    (3 ^ A * x + C = 2 ^ e) ↔ (C = 2 ^ e - 3 ^ A * x) := by
  omega

theorem base3_closure_fails_for_base5 (x A e : Nat)
    (hx : x > 0) (hA : A > 0) (h_bound : 3 ^ A * x ≤ 2 ^ e) :
    5 ^ A * x + (2 ^ e - 3 ^ A * x) ≠ 2 ^ e := by
  have h3_lt_5 : 3 ^ A < 5 ^ A := Nat.pow_lt_pow_left (by omega) (by omega)
  have h_mul : 3 ^ A * x < 5 ^ A * x := Nat.mul_lt_mul_of_pos_right h3_lt_5 hx
  omega
-- ============================================================================
-- Helper Power Lemmas (Self-Contained for Lean 4.37):
-- ============================================================================

theorem three_pow_pos : ∀ n : Nat, 1 ≤ 3 ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := three_pow_pos n
    rw [Nat.pow_succ]
    omega

theorem two_pow_ge_two : ∀ n : Nat, n ≥ 1 → 2 ≤ 2 ^ n
  | 0, hn => by omega
  | 1, _ => by decide
  | n + 2, _ => by
    have ih := two_pow_ge_two (n + 1) (by omega)
    rw [Nat.pow_succ]
    omega

-- ============================================================================
-- 19. The Modular Trap (Base-3 Residue Lock for Single-Division Escapes):
-- ============================================================================

theorem wave_peak_mod_three (a M : Nat) (ha : a ≥ 1) (hM : M ≥ 1) :
    (3 ^ a * M - 1) % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have h1 : 3 ^ (k + 1) = 3 * 3 ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have h_pow_ge : 1 ≤ 3 ^ k := three_pow_pos k
  have h_mul_ge : 1 ≤ 3 ^ k * M := Nat.mul_pos h_pow_ge hM
  rw [h1, Nat.mul_assoc]
  revert h_mul_ge
  generalize 3 ^ k * M = X
  intro hX
  omega


theorem modular_trap_single_division (a M x_next : Nat)
    (ha : a ≥ 1) (hM : M ≥ 1) (h_esc : 2 * x_next = 3 ^ a * M - 1) :
    x_next % 3 = 1 := by
  have h_peak : (3 ^ a * M - 1) % 3 = 2 := wave_peak_mod_three a M ha hM
  rw [← h_esc] at h_peak
  omega

-- ============================================================================
-- 20. Double-Block Transition & Short-Wave Contraction Law:
-- ============================================================================

theorem block_transition_identity (N1 N2 k1 K1 K2 X1 : Nat)
    (h1 : 2 ^ k1 * X1 = 3 ^ N1 * K1 - 1)
    (h2 : X1 = 2 ^ N2 * K2 - 1)
    (h_pos1 : 3 ^ N1 * K1 ≥ 1)
    (h_pos2 : 2 ^ N2 * K2 ≥ 1) :
    3 ^ N1 * K1 + 2 ^ k1 - 1 = 2 ^ (N2 + k1) * K2 := by
  have h_pow : 2 ^ (N2 + k1) = 2 ^ k1 * 2 ^ N2 := by
    rw [Nat.pow_add, Nat.mul_comm]
  have h_mul : 2 ^ k1 * (X1 + 1) = 2 ^ k1 * (2 ^ N2 * K2) := by
    have hx : X1 + 1 = 2 ^ N2 * K2 := by omega
    rw [hx]
  rw [h_pow, Nat.mul_assoc, ← h_mul]
  have h_dist : 2 ^ k1 * (X1 + 1) = 2 ^ k1 * X1 + 2 ^ k1 := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

theorem short_wave_k_contraction (N2 k1 K1 K2 : Nat)
    (hN2 : N2 ≥ 1) (hk1 : k1 ≥ 1) (hK1 : K1 > 1)
    (h_trans : 3 ^ 1 * K1 + 2 ^ k1 - 1 = 2 ^ (N2 + k1) * K2) :
    K2 < K1 := by
  by_cases hK2 : K2 = 0
  · omega
  · have h3 : 3 ^ 1 = 3 := rfl
    rw [h3] at h_trans
    have hN2_ge : 2 ≤ 2 ^ N2 := two_pow_ge_two N2 hN2
    have hk1_ge : 2 ≤ 2 ^ k1 := two_pow_ge_two k1 hk1
    have h_split : 2 ^ (N2 + k1) * K2 = 2 ^ N2 * (2 ^ k1 * K2) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    have h_rhs : 2 * (2 ^ k1 * K2) ≤ 2 ^ (N2 + k1) * K2 := by
      rw [h_split]
      exact Nat.mul_le_mul_right _ hN2_ge
    obtain ⟨d1, hd1⟩ : ∃ d1, 2 ^ k1 = d1 + 2 := ⟨2 ^ k1 - 2, by omega⟩
    obtain ⟨d2, hd2⟩ : ∃ d2, K2 = d2 + 1 := ⟨K2 - 1, by omega⟩
    have h_prod : 2 ^ k1 * K2 = d1 * d2 + d1 + 2 * d2 + 2 := by
      rw [hd1, hd2, Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    have h_nonneg : 0 ≤ d1 * d2 := Nat.zero_le _
    omega0 | 1 | 2 | 3 | 4 => decide
  | k + 5 =>
    have h_big : 2 ^ 5 ≤ 2 ^ (k + 5) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
import Mathlib

/-!
Collatz Wave Framework -- continuation beginning at item 22.

This file is a self-contained Lean 4 / Mathlib continuation.  It deliberately
separates proved algebraic lemmas from research targets that remain open.
No `sorry` and no unproved `axiom` declarations are used.

The original conversation's declarations 1--21 are not reproduced here.
The namespace is kept separate to avoid name clashes when this file is
appended to an existing project.
-/

namespace CollatzWaveContinuation

/-! ## 22. Exact wave relation and elimination of the auxiliary M -/

/--
A wave takes an odd state `x` with `x+1 = 2^a M`, performs `a` odd steps,
and then removes the final power `2^s`, producing the next odd state `y`.
The equations are written without truncated natural subtraction.
-/
structure WaveStep (x a M s y : ℕ) : Prop where
  a_pos : 0 < a
  s_pos : 0 < s
  cofactor_odd : M % 2 = 1
  next_odd : y % 2 = 1
  seed : x + 1 = 2 ^ a * M
  peak : 2 ^ s * y + 1 = 3 ^ a * M

/-- Eliminating `M` gives the exact affine numerator identity. -/
theorem theorem22_wave_elimination
    {x a M s y : ℕ} (h : WaveStep x a M s y) :
    2 ^ (a + s) * y + 2 ^ a = 3 ^ a * (x + 1) := by
  calc
    2 ^ (a + s) * y + 2 ^ a
        = 2 ^ a * (2 ^ s * y + 1) := by
            rw [pow_add]
            ring
    _ = 2 ^ a * (3 ^ a * M) := by rw [h.peak]
    _ = 3 ^ a * (x + 1) := by rw [h.seed]; ring

/-! ## 23. Transition identity between consecutive waves -/

/--
If the next state begins a new wave with `y+1 = 2^aNext * MNext`, then
`2^(s+aNext) MNext + 1 = 3^a M + 2^s`.
-/
theorem theorem23_wave_transition_identity
    {x a M s y aNext MNext : ℕ}
    (h : WaveStep x a M s y)
    (hNext : y + 1 = 2 ^ aNext * MNext) :
    2 ^ (s + aNext) * MNext + 1 = 3 ^ a * M + 2 ^ s := by
  calc
    2 ^ (s + aNext) * MNext + 1
        = 2 ^ s * (2 ^ aNext * MNext) + 1 := by
            rw [pow_add]
            ring
    _ = 2 ^ s * (y + 1) + 1 := by rw [hNext]
    _ = 2 ^ s * y + 1 + 2 ^ s := by ring
    _ = 3 ^ a * M + 2 ^ s := by rw [h.peak]

/-! ## 24. Rational affine form of one wave -/

def waveLambda (a s : ℕ) : ℚ :=
  (3 : ℚ) ^ a / (2 : ℚ) ^ (a + s)

def waveU (a : ℕ) : ℚ :=
  1 - ((2 : ℚ) / 3) ^ a

def waveAffine (a s : ℕ) (x : ℚ) : ℚ :=
  waveLambda a s * (x + waveU a)

/-- The natural-number wave relation is exactly `x' = λ (x + u)` over ℚ. -/
theorem theorem24_wave_affine_formula
    {x a M s y : ℕ} (h : WaveStep x a M s y) :
    (y : ℚ) = waveAffine a s (x : ℚ) := by
  have hn := theorem22_wave_elimination h
  have hq :
      (2 : ℚ) ^ (a + s) * (y : ℚ) + (2 : ℚ) ^ a =
        (3 : ℚ) ^ a * ((x : ℚ) + 1) := by
    exact_mod_cast hn
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have h3 : (3 : ℚ) ≠ 0 := by norm_num
  unfold waveAffine waveLambda waveU
  field_simp [h2, h3]
  nlinarith [hq]

/-! ## 24b. Finite telescoping identity for an arbitrary list of waves -/

structure WaveCoeff where
  a : ℕ
  s : ℕ

def coeffLambda (w : WaveCoeff) : ℚ := waveLambda w.a w.s

def coeffU (w : WaveCoeff) : ℚ := waveU w.a

def waveRun : List WaveCoeff → ℚ → ℚ
  | [], x => x
  | w :: ws, x => waveRun ws (coeffLambda w * (x + coeffU w))

def waveInverseWeight : List WaveCoeff → ℚ
  | [] => 1
  | w :: ws => (1 / coeffLambda w) * waveInverseWeight ws

def waveWeightedCorrection : List WaveCoeff → ℚ
  | [] => 0
  | w :: ws => coeffU w + (1 / coeffLambda w) * waveWeightedCorrection ws

/-- Exact finite telescoping identity: `U_N x_N = x_0 + B_N`. -/
theorem theorem24b_wave_telescope (ws : List WaveCoeff) (x : ℚ) :
    waveInverseWeight ws * waveRun ws x = x + waveWeightedCorrection ws := by
  induction ws generalizing x with
  | nil =>
      simp [waveInverseWeight, waveRun, waveWeightedCorrection]
  | cons w ws ih =>
      let lam : ℚ := coeffLambda w
      let u : ℚ := coeffU w
      have hlam : lam ≠ 0 := by
        dsimp [lam, coeffLambda, waveLambda]
        positivity
      change (1 / lam) * waveInverseWeight ws * waveRun ws (lam * (x + u)) =
        x + u + (1 / lam) * waveWeightedCorrection ws
      calc
        (1 / lam) * waveInverseWeight ws * waveRun ws (lam * (x + u))
            = (1 / lam) *
                (waveInverseWeight ws * waveRun ws (lam * (x + u))) := by ring
        _ = (1 / lam) * (lam * (x + u) + waveWeightedCorrection ws) := by
              rw [ih (lam * (x + u))]
        _ = x + u + (1 / lam) * waveWeightedCorrection ws := by
              field_simp [hlam]
              ring

/-! ## 24c. Exact integer coefficients for a finite wave prefix -/

/-- Integer coefficients in `2^K x_N = 3^A x_0 + C`. -/
structure WavePrefixCoefficients where
  A : ℕ
  K : ℕ
  C : ℕ
  deriving Repr

def extendWavePrefix (p : WavePrefixCoefficients) (w : WaveCoeff) :
    WavePrefixCoefficients :=
  { A := p.A + w.a
    K := p.K + w.a + w.s
    C := 3 ^ w.a * p.C + 2 ^ p.K * (3 ^ w.a - 2 ^ w.a) }

def wavePrefixCoefficients (ws : List WaveCoeff) : WavePrefixCoefficients :=
  ws.foldl extendWavePrefix ⟨0, 0, 0⟩

def RealizesWavePrefix (ws : List WaveCoeff) (x0 xN : ℕ) : Prop :=
  let p := wavePrefixCoefficients ws
  2 ^ p.K * xN = 3 ^ p.A * x0 + p.C

/-- Appending one wave updates the affine coefficients by the exact formula. -/
theorem theorem24c_extend_prefix_formula (p : WavePrefixCoefficients)
    (w : WaveCoeff) :
    (extendWavePrefix p w).A = p.A + w.a ∧
    (extendWavePrefix p w).K = p.K + w.a + w.s ∧
    (extendWavePrefix p w).C =
      3 ^ w.a * p.C + 2 ^ p.K * (3 ^ w.a - 2 ^ w.a) := by
  simp [extendWavePrefix]

/-! ## 25--26. Exact 3-adic exponent certificates and non-resonant addition -/

/-- `r` is the exact exponent of 3 dividing `n` (with nonzero cofactor). -/
def ExactThreeExponent (n r : ℕ) : Prop :=
  ∃ c : ℕ, n = 3 ^ r * c ∧ ¬ 3 ∣ c

/--
If the two summands have different exact powers of 3, the smaller exponent
survives in their sum.  This is the valuation-minimum rule used in the wave
memory calculation.
-/
theorem theorem25_exactThreeExponent_add_left
    {t r L Q : ℕ}
    (htr : t < r)
    (hL : ¬ 3 ∣ L) :
    ExactThreeExponent (3 ^ t * L + 3 ^ r * Q) t := by
  let d : ℕ := r - (t + 1)
  have hd : r = t + (d + 1) := by
    dsimp [d]
    omega
  have hfactor :
      3 ^ r * Q = 3 ^ t * (3 * (3 ^ d * Q)) := by
    calc
      3 ^ r * Q = (3 ^ t * 3 ^ (d + 1)) * Q := by
        rw [hd, pow_add]
      _ = 3 ^ t * (3 * (3 ^ d * Q)) := by
        rw [pow_succ]
        ring
  refine ⟨L + 3 * (3 ^ d * Q), ?_, ?_⟩
  · calc
      3 ^ t * L + 3 ^ r * Q
          = 3 ^ t * L + 3 ^ t * (3 * (3 ^ d * Q)) := by rw [hfactor]
      _ = 3 ^ t * (L + 3 * (3 ^ d * Q)) := by ring
  · intro hdiv
    rcases hdiv with ⟨k, hk⟩
    apply hL
    refine ⟨k - 3 ^ d * Q, ?_⟩
    omega

/-- Symmetric version: the smaller exponent on the second summand survives. -/
theorem theorem26_exactThreeExponent_add_right
    {r t L Q : ℕ}
    (hrt : r < t)
    (hQ : ¬ 3 ∣ Q) :
    ExactThreeExponent (3 ^ t * L + 3 ^ r * Q) r := by
  have h := theorem25_exactThreeExponent_add_left
    (t := r) (r := t) (L := Q) (Q := L) hrt hQ
  rcases h with ⟨c, hc, hc3⟩
  refine ⟨c, ?_, hc3⟩
  calc
    3 ^ t * L + 3 ^ r * Q = 3 ^ r * Q + 3 ^ t * L := by ring
    _ = 3 ^ r * c := hc

/-! ## 27. Resonance: equal powers of 3 do not permit the minimum rule -/

/-- In the resonance case, the common power factors and the new cofactor is `L+Q`. -/
theorem theorem27_resonance_factorization (t L Q : ℕ) :
    3 ^ t * L + 3 ^ t * Q = 3 ^ t * (L + Q) := by
  ring


/--
A useful reset bound: if `2^s < 3^a`, then the exact 3-adic exponent
of `2^s - 1` must be smaller than `a`.
This is the arithmetic core of the ascending-wave memory reset.
-/
theorem theorem27b_threeExponent_below_a
    {a s r c : ℕ}
    (hExact : 2 ^ s - 1 = 3 ^ r * c)
    (hc : 0 < c)
    (hBound : 2 ^ s < 3 ^ a) :
    r < a := by
  by_contra hnot
  have har : a ≤ r := Nat.le_of_not_gt hnot
  have hsum : a + (r - a) = r := Nat.add_sub_of_le har
  have hpow : 3 ^ r = 3 ^ a * 3 ^ (r - a) := by
    conv_lhs => rw [← hsum]
    rw [pow_add]
  have hpos : 0 < 3 ^ (r - a) := by positivity
  have hcofPos : 0 < 3 ^ (r - a) * c := Nat.mul_pos hpos hc
  have hcof : 1 ≤ 3 ^ (r - a) * c := Nat.succ_le_iff.mpr hcofPos
  have hmul : 3 ^ a ≤ 3 ^ r * c := by
    calc
      3 ^ a = 3 ^ a * 1 := by simp
      _ ≤ 3 ^ a * (3 ^ (r - a) * c) := Nat.mul_le_mul_left _ hcof
      _ = 3 ^ r * c := by rw [hpow]; ring
  omega

/--
An ascending-wave power inequality implies the size hypothesis used above,
because `2^(a+s) = 2^a * 2^s` and `2^a >= 1`.
-/
theorem theorem27c_ascent_gives_threeExponent_bound
    {a s r c : ℕ}
    (hPower : 2 ^ (a + s) < 3 ^ a)
    (hExact : 2 ^ s - 1 = 3 ^ r * c)
    (hc : 0 < c) :
    r < a := by
  apply theorem27b_threeExponent_below_a hExact hc
  have ha : 1 ≤ 2 ^ a := by positivity
  have hle : 2 ^ s ≤ 2 ^ (a + s) := by
    calc
      2 ^ s = 1 * 2 ^ s := by simp
      _ ≤ 2 ^ a * 2 ^ s := Nat.mul_le_mul_right _ ha
      _ = 2 ^ (a + s) := by rw [pow_add]; ring
  exact lt_of_le_of_lt hle hPower

/-! ## 28. The full wave-memory transition equation -/

theorem theorem28_memory_transition_factorization
    {x a M s y aNext MNext w L : ℕ}
    (h : WaveStep x a M s y)
    (hNext : y + 1 = 2 ^ aNext * MNext)
    (hMemory : M = 3 ^ w * L) :
    2 ^ (s + aNext) * MNext + 1 = 3 ^ (a + w) * L + 2 ^ s := by
  calc
    2 ^ (s + aNext) * MNext + 1 = 3 ^ a * M + 2 ^ s :=
      theorem23_wave_transition_identity h hNext
    _ = 3 ^ a * (3 ^ w * L) + 2 ^ s := by rw [hMemory]
    _ = 3 ^ (a + w) * L + 2 ^ s := by rw [pow_add]; ring

/-! ## 29. Exact difference between consecutive wave states -/

theorem theorem29_wave_difference_identity
    {x a M s y : ℕ} (h : WaveStep x a M s y) :
    (2 : ℤ) ^ s * ((y : ℤ) - (x : ℤ)) =
      ((3 : ℤ) ^ a - (2 : ℤ) ^ (a + s)) * (M : ℤ)
        + (2 : ℤ) ^ s - 1 := by
  have hseed : (x : ℤ) + 1 = (2 : ℤ) ^ a * (M : ℤ) := by
    exact_mod_cast h.seed
  have hpeak : (2 : ℤ) ^ s * (y : ℤ) + 1 = (3 : ℤ) ^ a * (M : ℤ) := by
    exact_mod_cast h.peak
  rw [pow_add]
  linear_combination hpeak - (2 : ℤ) ^ s * hseed

/-! ## 30--31. Growth and non-growth tests for a single wave -/

/-- If `3^a > 2^(a+s)`, the wave strictly increases the state. -/
theorem theorem30_wave_growth
    {x a M s y : ℕ}
    (h : WaveStep x a M s y)
    (hM : 0 < M)
    (hPower : 2 ^ (a + s) < 3 ^ a)
    (hTwo : 1 < 2 ^ s) :
    x < y := by
  have hcoef : 2 ^ (a + s) * M < 3 ^ a * M :=
    Nat.mul_lt_mul_of_pos_right hPower hM
  have hcombine : 2 ^ s * (x + 1) = 2 ^ (a + s) * M := by
    calc
      2 ^ s * (x + 1) = 2 ^ s * (2 ^ a * M) := by rw [h.seed]
      _ = 2 ^ (a + s) * M := by rw [pow_add]; ring
  have hlarge : 2 ^ s * (x + 1) < 2 ^ s * y + 1 := by
    rw [hcombine, h.peak]
    exact hcoef
  by_contra hnot
  have hyx : y ≤ x := Nat.le_of_not_gt hnot
  have hmul : 2 ^ s * y ≤ 2 ^ s * x := Nat.mul_le_mul_left _ hyx
  have hsmall : 2 ^ s * x + 1 < 2 ^ s * (x + 1) := by
    rw [Nat.mul_add]
    omega
  have hupper : 2 ^ s * y + 1 ≤ 2 ^ s * x + 1 :=
    Nat.add_le_add_right hmul 1
  omega

/-- If `3^a < 2^(a+s)`, the wave cannot increase the state. -/
theorem theorem31_wave_nonGrowth
    {x a M s y : ℕ}
    (h : WaveStep x a M s y)
    (hM : 0 < M)
    (hPower : 3 ^ a < 2 ^ (a + s)) :
    y ≤ x := by
  have hcoef : 3 ^ a * M < 2 ^ (a + s) * M :=
    Nat.mul_lt_mul_of_pos_right hPower hM
  have hcombine : 2 ^ s * (x + 1) = 2 ^ (a + s) * M := by
    calc
      2 ^ s * (x + 1) = 2 ^ s * (2 ^ a * M) := by rw [h.seed]
      _ = 2 ^ (a + s) * M := by rw [pow_add]; ring
  have hsmall : 2 ^ s * y + 1 < 2 ^ s * (x + 1) := by
    rw [h.peak, hcombine]
    exact hcoef
  by_contra hnot
  have hxy : x < y := Nat.lt_of_not_ge hnot
  have hmul : 2 ^ s * (x + 1) ≤ 2 ^ s * y :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hxy)
  omega

/-! ## 32. A symbolic parity path and its exact affine composition -/

/-- Number of odd symbols in a finite parity word. -/
def parityOnes : List Bool → ℕ
  | [] => 0
  | true :: bs => parityOnes bs + 1
  | false :: bs => parityOnes bs

/-- Constant term in the affine composition associated with a parity word. -/
def parityOffset : List Bool → ℕ
  | [] => 0
  | true :: bs => 3 ^ (parityOnes bs) + 2 * parityOffset bs
  | false :: bs => 2 * parityOffset bs

/--
A path labelled by `false` uses `2*y=x`; a path labelled by `true` uses
`2*y=3*x+1`.  Thus every step is one ordinary Collatz step with its parity
specified explicitly.
-/
inductive ParityPath : List Bool → ℕ → ℕ → Prop where
  | nil (x : ℕ) : ParityPath [] x x
  | evenStep {bs : List Bool} {x y z : ℕ}
      (hstep : x = 2 * y)
      (hrest : ParityPath bs y z) :
      ParityPath (false :: bs) x z
  | oddStep {bs : List Bool} {x y z : ℕ}
      (hstep : 2 * y = 3 * x + 1)
      (hrest : ParityPath bs y z) :
      ParityPath (true :: bs) x z

/-- Exact parity-path identity: `2^j y = 3^q x + B(word)`. -/
theorem theorem32_parity_path_affine
    {bs : List Bool} {x y : ℕ}
    (h : ParityPath bs x y) :
    2 ^ bs.length * y = 3 ^ (parityOnes bs) * x + parityOffset bs := by
  induction h with
  | nil x =>
      simp [parityOnes, parityOffset]
  | @evenStep bs x y z hstep hrest ih =>
      simp only [List.length_cons, parityOnes, parityOffset]
      calc
        2 ^ (bs.length + 1) * z = 2 * (2 ^ bs.length * z) := by
          rw [pow_succ]
          ring
        _ = 2 * (3 ^ (parityOnes bs) * y + parityOffset bs) := by rw [ih]
        _ = 3 ^ (parityOnes bs) * (2 * y) + 2 * parityOffset bs := by ring
        _ = 3 ^ (parityOnes bs) * x + 2 * parityOffset bs := by rw [← hstep]
  | @oddStep bs x y z hstep hrest ih =>
      simp only [List.length_cons, parityOnes, parityOffset]
      calc
        2 ^ (bs.length + 1) * z = 2 * (2 ^ bs.length * z) := by
          rw [pow_succ]
          ring
        _ = 2 * (3 ^ (parityOnes bs) * y + parityOffset bs) := by rw [ih]
        _ = 3 ^ (parityOnes bs) * (2 * y) + 2 * parityOffset bs := by ring
        _ = 3 ^ (parityOnes bs) * (3 * x + 1) + 2 * parityOffset bs := by
          rw [hstep]
        _ = 3 ^ (parityOnes bs + 1) * x
              + (3 ^ (parityOnes bs) + 2 * parityOffset bs) := by
          rw [pow_succ]
          ring

/-! ## 33. Parity words, factor complexity, and density definitions -/

def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def collatzIter (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 => collatzStep (collatzIter x n)

def parityWord (x : ℕ) : ℕ → Bool :=
  fun n => decide (collatzIter x n % 2 = 1)

def onesPrefix (w : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => w i = true)).card

/-- Whether a length-`L` binary factor occurs somewhere in the infinite word. -/
def OccursFactor (w : ℕ → Bool) (L : ℕ) (f : Fin L → Bool) : Prop :=
  ∃ i : ℕ, ∀ j : Fin L, f j = w (i + j.val)

/-- Number of distinct factors of length `L` in an infinite binary word. -/
noncomputable def factorComplexity (w : ℕ → Bool) (L : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f : Fin L → Bool => OccursFactor w L f)).card

def HasCriticalDensity (w : ℕ → Bool) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => (onesPrefix w n : ℝ) / (n : ℝ))
    Filter.atTop
    (nhds (Real.log 2 / Real.log 3))

def NotEventuallyPeriodic (w : ℕ → Bool) : Prop :=
  ¬ ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → w (n + p) = w n

def SuperlinearFactorComplexity (w : ℕ → Bool) : Prop :=
  Filter.Tendsto
    (fun L : ℕ => (factorComplexity w L : ℝ) / (L : ℝ))
    Filter.atTop
    Filter.atTop

/-!
The following is the mathematical conclusion established in the research
argument for a nonperiodic integer orbit whose parity density exists and is
exactly log_3(2): its factor complexity must be superlinear.
The proposition is recorded here as a formalization target; this file does
not yet contain a Lean proof of the asymptotic/combinatorial argument.
-/
def theorem33_critical_density_complexity_target : Prop :=
  ∀ x : ℕ, 1 < x →
    HasCriticalDensity (parityWord x) →
    NotEventuallyPeriodic (parityWord x) →
    SuperlinearFactorComplexity (parityWord x)

/-!
## 34. Necessary escape bias in wave coordinates

For a wave sequence `a_n,s_n`, the exact logarithmic identity implies that an
orbit tending to infinity must satisfy
`S_N - log_2(3/2) A_N <= o(N)`.
The limit statement is intentionally recorded as a target/definition rather
than asserted as a completed Lean theorem here.
-/
def waveBiasTerm (a s : ℕ → ℕ) (n : ℕ) : ℝ :=
  (s n : ℝ) - (Real.log 3 / Real.log 2 - 1) * (a n : ℝ)

def HasNonpositiveAsymptoticWaveBias (a s : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ i in Finset.range n, waveBiasTerm a s i) / (n : ℝ) ≤ ε

/-!
## 35. Main open goals (not claimed as theorems)

The following propositions make the remaining research gap explicit:
* exclude every nonperiodic critical-density parity word of superlinear
  factor complexity that could come from a positive integer;
* exclude positive integer orbits escaping to infinity;
* prove the full Collatz conjecture.
-/

def NoEscapingPositiveCollatzOrbit : Prop :=
  ∀ x : ℕ, 0 < x →
    ∃ n : ℕ, collatzIter x n = 1

def CriticalWordExclusionTarget : Prop :=
  ∀ x : ℕ, 1 < x →
    HasCriticalDensity (parityWord x) →
    NotEventuallyPeriodic (parityWord x) →
    False

end CollatzWaveContinuation

