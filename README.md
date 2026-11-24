# Collatz Wave Framework (Lean 4)

**Author:** Mohamed Hamed Sayed Mohamed  
**Language:** Lean 4 (`v4.37.0`) & Python 3

## Overview
This repository contains a formal mathematical framework in **Lean 4** that models the dynamics of the Collatz conjecture ($3x + 1$) using **Accelerated Wave Decomposition**. Instead of tracking individual odd and even steps, every odd integer is represented as:

$$x = 2^a \cdot M - 1$$

where $M$ is odd and $a \ge 1$ acts as the **"ascent fuel"** determining the exact number of consecutive accelerated odd steps before a wave breaks.

## Key Formalized Results (16 Theorems)
All 16 theorems in `collatz_wave_framework.lean` are completely machine-verified with **zero `sorry`s**:

1. **Parity Contrast & Fuel Depletion (`Theorems 1–3`):** Proves that for any odd $K$, either $K-1$ or $K+1$ is divisible by $4$, and proves step-by-step depletion of the ascent counter $a$ until guaranteed wave breaking at $a = 1$.
2. **Full Wave Ascent (`Theorem 4 - full_wave_climb`):** Uses mathematical induction to prove that $2^a \cdot M - 1$ reaches $3^a \cdot M - 1$ after $a$ accelerated steps for any $a \in \mathbb{N}$.
3. **Single & Two-Wave Descent (`Theorems 5–10, 12–14`):** Establishes the exact algebraic linking equation between consecutive waves and proves sufficient conditions for strict descent ($x_{\text{next}} < x$).
4. **General $N$-Wave Composition (`Theorem 15 - n_wave_composition`):** Proves by induction that any $N$ consecutive waves collapse into a single Diophantine equation:
   $$2^{E_n} \cdot x_n + C = 3^{A_n} \cdot x_0$$
5. **Conditional Global Convergence (`Theorems 11 & 16`):** Uses strong induction (`Nat.strongRecOn`) to prove that if cumulative division powers dominate multiplication powers ($3^{A_n} < 2^{E_n}$) for all $x_0 > 1$, every positive integer reaches $1$.

## Scientific Status
This work provides a **verified conditional framework**. Proving that the power dominance condition ($3^{A_n} < 2^{E_n}$) holds universally without exceptions in infinity remains the open core of the Collatz conjecture.

## Repository Structure
* `collatz_wave_framework.lean`: Complete Lean 4 formalization containing all 16 machine-verified theorems.
* `collatz_wave_lab.py`: Python 3 experimental script for generating wave maps and testing ascent/descent dynamics.
* `README.md`: Project documentation and mathematical summary.

6. **Modular Wave Sieve (`Theorem 17 - mod32_wave_descent_9_classes`):** Machine-verified proof of strict 1-wave descent for 9 out of 16 odd residue classes modulo 32 (covering **56.25%** of all odd integers).
