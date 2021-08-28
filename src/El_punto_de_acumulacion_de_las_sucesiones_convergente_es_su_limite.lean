-- El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.lean
-- El punto de acumulación de las sucesiones convergente es su límite.
-- José A. Alonso Jiménez
-- Sevilla, 2 de septiembre 2021
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
-- que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
-- que u es convergente por
--    def convergente (u : ℕ → ℝ) :=
--      ∃ a, limite u a
-- que a es un punto de acumulación de u por
--    def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
--      ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
--
-- Demostrar que si u es una sucesión convergente y a es un punto de
-- acumulación de u, entonces a es un límite de u.
-- ---------------------------------------------------------------------

import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- Lemas auxiliares
-- ================

lemma unicidad_limite_aux
  {a b: ℝ}
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
begin
  by_contra h,
  set ε := b - a with hε,
  cases ha (ε/2) (by linarith) with A hA,
  cases hb (ε/2) (by linarith) with B hB,
  set N := max A B with hN,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA N hAN,
  specialize hB N hBN,
  rw abs_lt at hA hB,
  linarith,
end

lemma unicidad_limite
  {a b: ℝ}
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
le_antisymm (unicidad_limite_aux hb ha)
            (unicidad_limite_aux ha hb)

lemma limite_subsucesion_aux
  {φ : ℕ → ℕ}
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

lemma limite_subsucesion
  {φ : ℕ → ℕ}
  {a : ℝ}
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  cases h ε hε with N hN,
  use N,
  intros k hk,
  calc |(u ∘ φ) k - a|
       = |u (φ k) - a| : rfl
   ... < ε             : hN (φ k) _,
  calc φ k
       ≥ k : limite_subsucesion_aux hφ k
   ... ≥ N : hk,
end

-- 1ª demostración
example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  unfold convergente at hu,
  cases hu with b hb,
  convert hb,
  unfold punto_acumulacion at ha,
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  have hφ₃ : limite (u ∘ φ) b,
    from limite_subsucesion hb hφ₁,
  exact unicidad_limite hφ₂ hφ₃,
end

-- 1ª demostración
example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  cases hu with b hb,
  convert hb,
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  apply unicidad_limite hφ₂ _,
  exact limite_subsucesion hb hφ₁,
end

-- 2ª demostración
example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  cases hu with b hb,
  convert hb,
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  exact unicidad_limite hφ₂ (limite_subsucesion hb hφ₁),
end
