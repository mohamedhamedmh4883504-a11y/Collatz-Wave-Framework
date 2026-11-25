# Collatz Wave Framework (Formalized in Lean 4)

A formal mathematical framework and machine-verified Lean 4 library analyzing the **Collatz Conjecture ($3x + 1$)** through **2-adic Wave Decomposition**, **Closure Equations**, **Modular Residue Traps**, and **Double-Block Contraction Laws**.

---

## Core Mathematical Architecture

Instead of tracking individual steps, this framework decomposes every odd positive integer into structured ascent waves:
$$x = 2^a \cdot M - 1$$
where $a = v_2(x + 1)$ represents the exact length of consecutive $(3x + 1)/2$ ascent steps before reaching the wave peak $P = 3^a \cdot M - 1$.

---

## Machine-Verified Theorems (20 Theorems in Lean 4)

All theorems in `collatz_wave_framework.lean` compile cleanly with **zero `sorry` statements** and zero warnings:

### I. Wave Mechanics & Descent Foundations (Theorems 1–13)
* **Wave Peak & Parity Laws:** Exact algebraic characterization of wave peaks ($P = 3^a M - 1$) and guaranteed evenness at peak termination.
* **Well-Founded Descent (`collatz_by_wave_descent`):** Proves that if every odd integer $x > 1$ eventually drops strictly below its starting value ($x_n  1$).

---

## Open Frontier (Next Research Target)

While the modular trap and short-wave contraction laws restrict unbounded growth across consecutive blocks, the remaining open problem required to complete the global proof is establishing uniform cumulative division dominance across arbitrary infinite block sequences:
$$k_{\text{total}} > (\log_2 3 - 1) \cdot A_{\text{total}} \approx 0.585 \cdot A_{\text{total}}$$

---

## Repository Structure
* `collatz_wave_framework.lean` — Complete Lean 4 formalization containing all 20 verified theorems.
* `README.md` — Mathematical overview and theorem index.

* `collatz_wave_framework.lean`: Complete Lean 4 formalization containing all 16 machine-verified theorems.
* `collatz_wave_lab.py`: Python 3 experimental script for generating wave maps and testing ascent/descent dynamics.
* `README.md`: Project documentation and mathematical summary.

6. **Modular Wave Sieve (`Theorem 17 - mod32_wave_descent_9_classes`):** Machine-verified proof of strict 1-wave descent for 9 out of 16 odd residue classes modulo 32 (covering **56.25%** of all odd integers).
