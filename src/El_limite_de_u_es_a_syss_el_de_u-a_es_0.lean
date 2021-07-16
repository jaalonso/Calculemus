-- El_limite_de_u_es_a_syss_el_de_u-a_es_0.lean
-- El límite de u es a syss el de u-a es 0.
-- José A. Alonso Jiménez
-- Sevilla, 16 de julio de 2021
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
-- Demostrar que el límite de u(i) es a si y solo si el de u(i)-a es
-- 0.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variable  {u : ℕ → ℝ}
variables {a c x : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  : limite u a ↔ limite (λ i, u i - a) 0 :=
begin
  rw iff_eq_eq,
  calc limite u a
       = ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε       : rfl
   ... = ∀ ε > 0, ∃ N, ∀ n ≥ N, |(u n - a) - 0| < ε : by simp
   ... = limite (λ i, u i - a) 0                    : rfl,
end

-- 2ª demostración
-- ===============

example
  : limite u a ↔ limite (λ i, u i - a) 0 :=
begin
  split,
  { intros h ε hε,
    convert h ε hε,
    norm_num, },
  { intros h ε hε,
    convert h ε hε,
    norm_num, },
end

-- 3ª demostración
-- ===============

example
  : limite u a ↔ limite (λ i, u i - a) 0 :=
begin
  split;
  { intros h ε hε,
    convert h ε hε,
    norm_num, },
end

-- 4ª demostración
-- ===============

lemma limite_con_suma
  (c : ℝ)
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
λ ε hε, (by convert h ε hε; norm_num)

lemma CNS_limite_con_suma
  (c : ℝ)
  : limite u a ↔ limite (λ i, u i + c) (a + c) :=
begin
  split,
  { apply limite_con_suma },
  { intro h,
    convert limite_con_suma (-c) h; simp, },
end

example
  (u : ℕ → ℝ)
  (a : ℝ)
  : limite u a ↔ limite (λ i, u i - a) 0 :=
begin
  convert CNS_limite_con_suma (-a),
  simp,
end
