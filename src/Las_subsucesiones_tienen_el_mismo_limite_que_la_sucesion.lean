-- Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.lean
-- Las subsucesiones tienen el mismo límite que la sucesión
-- José A. Alonso Jiménez
-- Sevilla, 1 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.
--
-- En Lean, se puede definir que φ es una función de extracción por
--    def extraccion (φ : ℕ → ℕ) :=
--      ∀ n m, n < m → φ n < φ m
-- que v es una subsucesión de u por
--    def subsucesion (v u : ℕ → ℝ) :=
--      ∃ φ, extraccion φ ∧ v = u ∘ φ
-- y que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
--
-- Demostrar que las subsucesiones de una sucesión convergente tienen el
-- mismo límite que la sucesión.
-- ---------------------------------------------------------------------

import data.real.basic
open nat

variables {u v : ℕ → ℝ}
variable  {a : ℝ}
variable  {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

-- En la demostración se usará el siguiente lema.
lemma aux
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
begin
  intro n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h m (m+1) (lt_add_one m), },
end

-- 1ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  unfold limite,
  intros ε hε,
  unfold limite at ha,
  cases ha ε hε with N hN,
  use N,
  intros n hn,
  unfold subsucesion at hv,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  apply hN,
  apply le_trans hn,
  exact aux hφ1 n,
end

-- 2ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  use N,
  intros n hn,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  apply hN,
  exact le_trans hn (aux hφ1 n),
end

-- 3ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  use N,
  intros n hn,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  exact hN (φ n) (le_trans hn (aux hφ1 n)),
end

-- 4ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  use N,
  exact λ n hn, hN (φ n) (le_trans hn (aux hφ1 n)),
end

-- 5ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  exact ⟨N, λ n hn, hN (φ n) (le_trans hn (aux hφ1 n))⟩,
end
