-- CS_de_continuidad.lean
-- Pruebas de "Si f es continua en a y el límite de u es a,
--   entonces el límite de (f ∘ u) es f(a)"
-- José A. Alonso Jiménez
-- Sevilla, 17 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, se puede definir que a es el límite de la sucesión u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
-- y que f es continua en a por
--    def continua_en_punto (f : ℝ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε
--
-- Demostrar que si f es continua en a y el límite de u(n) es a,
-- entonces el límite de f(u(n)) es f(a).
-- ---------------------------------------------------------------------

import data.real.basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continua_en_punto (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

-- 1ª demostración
example
  (hf : continua_en_punto f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
begin
  intros ε hε,
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩,
  cases hu δ hδ1 with k hk,
  use k,
  intros n hn,
  apply hδ2,
  exact hk n hn,
end

-- 2ª demostración
example
  (hf : continua_en_punto f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
begin
  intros ε hε,
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩,
  cases hu δ hδ1 with k hk,
  exact ⟨k, λ n hn, hδ2 (u n) (hk n hn)⟩,
end

-- 3ª demostración
example
  (hf : continua_en_punto f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
begin
  intros ε hε,
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε,
  obtain ⟨k, hk⟩ := hu δ hδ1,
  exact ⟨k, λ n hn, hδ2 (u n) (hk n hn)⟩,
end
