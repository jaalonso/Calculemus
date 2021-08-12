-- Limite_de_sucesion_menor_que_otra_sucesion.lean
-- Límite de sucesión menor que otra sucesión.
-- José A. Alonso Jiménez
-- Sevilla, 30 de julio de 2021
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
-- Demostrar que si uₙ → a, vₙ → c y uₙ ≤ vₙ para todo n, entonces
-- a ≤ c.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variables (a c : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (c : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hεac,
  have hε : 0 < ε :=
    half_pos (sub_pos.mpr hlt),
  cases hu ε hε with Nu HNu,
  cases hv ε hε with Nv HNv,
  let N := max Nu Nv,
  have HNu' : Nu ≤ N := le_max_left Nu Nv,
  have HNv' : Nv ≤ N := le_max_right Nu Nv,
  have Ha : |u N - a| < ε := HNu N HNu',
  have Hc : |v N - c| < ε := HNv N HNv',
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  calc a - c
       = (a - u N) + (u N - c)   : by ring
   ... ≤ (a - u N) + (v N - c)   : by simp [HN]
   ... ≤ |(a - u N) + (v N - c)| : le_abs_self ((a - u N) + (v N - c))
   ... ≤ |a - u N| + |v N - c|   : abs_add (a - u N) (v N - c)
   ... = |u N - a| + |v N - c|   : by simp only [abs_sub_comm]
   ... < ε + ε                   : add_lt_add Ha Hc
   ... = a - c                   : add_halves (a - c),
end

-- 2ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hε,
  cases hu ε (by linarith) with Nu HNu,
  cases hv ε (by linarith) with Nv HNv,
  let N := max Nu Nv,
  have Ha : |u N - a| < ε :=
    HNu N (le_max_left Nu Nv),
  have Hc : |v N - c| < ε :=
    HNv N (le_max_right Nu Nv),
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  calc a - c
       = (a - u N) + (u N - c)   : by ring
   ... ≤ (a - u N) + (v N - c)   : by simp [HN]
   ... ≤ |(a - u N) + (v N - c)| : le_abs_self ((a - u N) + (v N - c))
   ... ≤ |a - u N| + |v N - c|   : abs_add (a - u N) (v N - c)
   ... = |u N - a| + |v N - c|   : by simp only [abs_sub_comm]
   ... < ε + ε                   : add_lt_add Ha Hc
   ... = a - c                   : add_halves (a - c),
end

-- 3ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hε,
  cases hu ε (by linarith) with Nu HNu,
  cases hv ε (by linarith) with Nv HNv,
  let N := max Nu Nv,
  have Ha : |u N - a| < ε :=
    HNu N (le_max_left Nu Nv),
  have Hc : |v N - c| < ε :=
    HNv N (le_max_right Nu Nv),
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  calc a - c
       = (a - u N) + (u N - c)   : by ring
   ... ≤ (a - u N) + (v N - c)   : by simp [HN]
   ... ≤ |(a - u N) + (v N - c)| : by simp [le_abs_self]
   ... ≤ |a - u N| + |v N - c|   : by simp [abs_add]
   ... = |u N - a| + |v N - c|   : by simp [abs_sub_comm]
   ... < ε + ε                   : add_lt_add Ha Hc
   ... = a - c                   : by simp,
end

-- 4ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hε,
  cases hu ε (by linarith) with Nu HNu,
  cases hv ε (by linarith) with Nv HNv,
  let N := max Nu Nv,
  have Ha : |u N - a| < ε :=
    HNu N (le_max_left Nu Nv),
  have Hc : |v N - c| < ε :=
    HNv N (le_max_right Nu Nv),
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  rw abs_lt at Ha Hc,
  linarith,
end
