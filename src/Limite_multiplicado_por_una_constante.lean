-- Limite_multiplicado_por_una_constante.lean
-- Límite multiplicado por una constante
-- José A. Alonso Jiménez
-- Sevilla, 15 de julio de 2021
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
-- Demostrar que que si el límite de u(i) es a, entonces el de
-- c*u(i) es c*a.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variables (a c : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ n, c * (u n)) (c * a) :=
begin
  by_cases hc : c = 0,
  { subst hc,
    intros ε hε,
    by finish, },
  { intros ε hε,
    have hc' : 0 < |c| := abs_pos.mpr hc,
    have hεc : 0 < ε / |c| := div_pos hε hc',
    specialize h (ε/|c|) hεc,
    cases h with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    dsimp only,
    rw ← mul_sub,
    rw abs_mul,
    rw ← lt_div_iff' hc',
    exact hN, }
end

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ n, c * (u n)) (c * a) :=
begin
  by_cases hc : c = 0,
  { subst hc,
    intros ε hε,
    by finish, },
  { intros ε hε,
    have hc' : 0 < |c| := abs_pos.mpr hc,
    have hεc : 0 < ε / |c| := div_pos hε hc',
    specialize h (ε/|c|) hεc,
    cases h with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    dsimp only,
    calc |c * u n - c * a|
         = |c * (u n - a)| : congr_arg abs (mul_sub c (u n) a).symm
     ... = |c| * |u n - a| : abs_mul c  (u n - a)
     ... < |c| * (ε / |c|) : (mul_lt_mul_left hc').mpr hN
     ... = ε               : mul_div_cancel' ε (ne_of_gt hc') }
end

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ n, c * (u n)) (c * a) :=
begin
  by_cases hc : c = 0,
  { subst hc,
    intros ε hε,
    by finish, },
  { intros ε hε,
    have hc' : 0 < |c| := by finish,
    have hεc : 0 < ε / |c| := div_pos hε hc',
    cases h (ε/|c|) hεc with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    dsimp only,
    rw [← mul_sub, abs_mul, ← lt_div_iff' hc'],
    exact hN, }
end
