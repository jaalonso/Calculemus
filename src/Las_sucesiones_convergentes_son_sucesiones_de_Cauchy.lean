-- Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.lean
-- Las sucesiones convergentes son sucesiones de Cauchy
-- José A. Alonso Jiménez
-- Sevilla, 21 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define
-- + el valor absoluto de x por
--      notation `|`x`|` := abs x
-- + a es un límite de la sucesión u , por
--      def limite (u : ℕ → ℝ) (a : ℝ) :=
--        ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| ≤ ε
-- + la sucesión u es convergente por
--      def suc_convergente (u : ℕ → ℝ) :=
--        ∃ l, limite u l
-- + la sucesión u es de Cauchy por
--      def suc_cauchy (u : ℕ → ℝ) :=
--        ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε
--
-- Demostrar que las sucesiones convergentes son de Cauchy.
-- ---------------------------------------------------------------------

import data.real.basic

variable {u : ℕ → ℝ }

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def suc_convergente (u : ℕ → ℝ) :=
  ∃ l, limite u l

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

-- 1ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  unfold suc_cauchy,
  intros ε hε,
  have hε2 : 0 < ε/2 := half_pos hε,
  cases h with l hl,
  cases hl (ε/2) hε2 with N hN,
  clear hε hl hε2,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : congr_arg2 (+) rfl (abs_sub_comm l (u q))
   ... < ε/2 + ε/2               : add_lt_add (hN p hp) (hN q hq)
   ... = ε                       : add_halves ε,
end

-- 2ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : congr_arg2 (+) rfl (abs_sub_comm l (u q))
   ... < ε/2 + ε/2               : add_lt_add (hN p hp) (hN q hq)
   ... = ε                       : add_halves ε,
end

-- 3ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  have cota1 : |u p - l| < ε / 2 := hN p hp,
  have cota2 : |u q - l| < ε / 2 := hN q hq,
  clear hN hp hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : by rw abs_sub_comm l (u q)
   ... < ε                       : by linarith,
end

-- 4ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : by rw abs_sub_comm l (u q)
   ... < ε                       : by linarith [hN p hp, hN q hq],
end

-- 5ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (by linarith) with N hN,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : by simp [abs_sub_comm]
   ... < ε                       : by linarith [hN p hp, hN q hq],
end
