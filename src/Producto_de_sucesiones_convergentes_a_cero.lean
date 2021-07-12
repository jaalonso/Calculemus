-- Producto_de_sucesiones_convergentes_a_cero.lean
-- Producto de sucesiones convergentes a cero
-- José A. Alonso Jiménez
-- Sevilla, 17 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--    λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
-- donde se usa la notación |x| para el valor absoluto de x
--    notation `|`x`|` := abs x
--
-- Demostrar que si las sucesiones u(n) y v(n) convergen a cero,
-- entonces u(n)·v(n) también converge a cero.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variables {u v : ℕ → ℝ}
variables {: ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
begin
  intros ε hε,
  cases hu ε hε with U hU,
  cases hv 1 zero_lt_one with V hV,
  set N := max U V with hN,
  use N,
  intros n hn,
  specialize hU n (le_of_max_le_left hn),
  specialize hV n (le_of_max_le_right hn),
  rw sub_zero at *,
  calc |(u * v) n|
       = |u n * v n|   : rfl
   ... = |u n| * |v n| : abs_mul (u n) (v n)
   ... < ε * 1         : mul_lt_mul'' hU hV (abs_nonneg (u n)) (abs_nonneg (v n))
   ... = ε             : mul_one ε,
end

-- 2ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
begin
  intros ε hε,
  cases hu ε hε with U hU,
  cases hv 1 (by linarith) with V hV,
  set N := max U V with hN,
  use N,
  intros n hn,
  specialize hU n (le_of_max_le_left hn),
  specialize hV n (le_of_max_le_right hn),
  rw sub_zero at *,
  calc |(u * v) n|
       = |u n * v n|   : rfl
   ... = |u n| * |v n| : abs_mul (u n) (v n)
   ... < ε * 1         : by { apply mul_lt_mul'' hU hV ; simp [abs_nonneg] }
   ... = ε             : mul_one ε,
end

-- 3ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
begin
  intros ε hε,
  cases hu ε hε with U hU,
  cases hv 1 (by linarith) with V hV,
  set N := max U V with hN,
  use N,
  intros n hn,
  have hUN : U ≤ N := le_max_left U V,
  have hVN : V ≤ N := le_max_right U V,
  specialize hU n (by linarith),
  specialize hV n (by linarith),
  rw sub_zero at ⊢ hU hV,
  rw pi.mul_apply,
  rw abs_mul,
  convert mul_lt_mul'' hU hV _ _, simp,
  all_goals {apply abs_nonneg},
end
