-- Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.lean
-- Si a es un punto de acumulación de la sucesión de Cauchy u, entonces a es el límite de u
-- José A. Alonso Jiménez
-- Sevilla, 4 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.
--
-- En Lean, se puede definir que φ es una función de extracción por
--    def extraccion (φ : ℕ → ℕ) :=
--      ∀ n m, n < m → φ n < φ m
-- que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
-- que a es un punto de acumulación de u por
--    def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
--      ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
-- que la sucesión u es de Cauchy por
--    def suc_cauchy (u : ℕ → ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε
--
-- Demostrar que si u es una sucesión de Cauchy y a es un punto de
-- acumulación de u, entonces a es el límite de u.
-- ---------------------------------------------------------------------

import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}
variable  {φ : ℕ → ℕ}

notation `|`x`|` := abs x

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

lemma aux1
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

lemma aux2
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N', ⟨max N N', ⟨le_max_right N N',
                    le_trans (le_max_left N N')
                             (aux1 h (max N N'))⟩⟩

lemma cerca_acumulacion
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  exact ⟨φ m, hm', hN' _ hm⟩,
end

-- 1ª demostración
example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  unfold limite,
  intros ε hε,
  unfold suc_cauchy at hu,
  cases hu (ε/2) (half_pos hε) with N hN,
  use N,
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2,
    apply cerca_acumulacion ha (ε/2) (half_pos hε),
  cases ha' with N' h,
  cases h with hNN' hN',
  intros n hn,
  calc   |u n - a|
       = |(u n - u N') + (u N' - a)| : by ring_nf
   ... ≤ |u n - u N'| + |u N' - a|   : abs_add (u n - u N') (u N' - a)
   ... < ε/2 + |u N' - a|            : add_lt_add_right (hN n hn N' hNN') _
   ... < ε/2 + ε/2                   : add_lt_add_left hN' (ε / 2)
   ... = ε                           : add_halves ε
end

-- 2ª demostración
example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with N hN,
  use N,
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2,
    apply cerca_acumulacion ha (ε/2) (by linarith),
  rcases ha' with ⟨N', hNN', hN'⟩,
  intros n hn,
  calc  |u n - a|
      = |(u n - u N') + (u N' - a)| : by ring_nf
  ... ≤ |u n - u N'| + |u N' - a|   : by simp [abs_add]
  ... < ε                           : by linarith [hN n hn N' hNN'],
end
