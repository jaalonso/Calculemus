-- Limite_de_la_suma_de_sucesiones_convergentes.lean
-- Límite de la suma de sucesiones convergentes
-- José A. Alonso Jiménez
-- Sevilla, 14 de julio de 2021
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
-- Demostrar que el límite de la suma de dos sucesiones convergentes es
-- la suma de los límites de dichas sucesiones.
-- ---------------------------------------------------------------------

import data.real.basic

variables (u v : ℕ → ℝ)
variables (a b : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  have hε2 : 0 < ε / 2,
    { linarith },
  cases hu (ε / 2) hε2 with Nu hNu,
  cases hv (ε / 2) hε2 with Nv hNv,
  clear hu hv hε2 hε,
  use max Nu Nv,
  intros n hn,
  have hn₁ : n ≥ Nu,
    { exact le_of_max_le_left hn },
  specialize hNu n hn₁,
  have hn₂ : n ≥ Nv,
    { exact le_of_max_le_right hn },
  specialize hNv n hn₂,
  clear hn hn₁ hn₂ Nu Nv,
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  : by refl
   ... = |(u n - a) + (v n -  b)| : by {congr, ring}
   ... ≤ |u n - a| + |v n -  b|   : by apply abs_add
   ... < ε / 2 + ε / 2            : by linarith
   ... = ε                        : by apply add_halves,
end

-- 2ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  have hn₁ : n ≥ Nu := le_of_max_le_left hn,
  specialize hNu n hn₁,
  have hn₂ : n ≥ Nv := le_of_max_le_right hn,
  specialize hNv n hn₂,
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  : by refl
   ... = |(u n - a) + (v n -  b)| : by {congr, ring}
   ... ≤ |u n - a| + |v n -  b|   : by apply abs_add
   ... < ε / 2 + ε / 2            : by linarith
   ... = ε                        : by apply add_halves,
end

-- 3ª demostración
-- ===============

lemma max_ge_iff
  {α : Type*}
  [linear_order α]
  {p q r : α}
  : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  cases max_ge_iff.mp hn with hn₁ hn₂,
  have cota₁ : |u n - a| < ε/2 := hNu n hn₁,
  have cota₂ : |v n - b| < ε/2 := hNv n hn₂,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   : by rfl
   ... = |(u n - a) + (v n - b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n - b|   : by apply abs_add
   ... < ε                       : by linarith,
end

-- 4ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  cases max_ge_iff.mp hn with hn₁ hn₂,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   : by refl
   ... = |(u n - a) + (v n - b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n - b|   : by apply abs_add
   ... < ε/2 + ε/2               : add_lt_add (hNu n hn₁) (hNv n hn₂)
   ... = ε                       : by simp
end

-- 5ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  rw max_ge_iff at hn,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   : by refl
   ... = |(u n - a) + (v n - b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n - b|   : by apply abs_add
   ... < ε                       : by linarith [hNu n (by linarith), hNv n (by linarith)],
end

-- 6ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε Hε,
  cases hu (ε/2) (by linarith) with L HL,
  cases hv (ε/2) (by linarith) with M HM,
  set N := max L M with hN,
  use N,
  have HLN : N ≥ L := le_max_left _ _,
  have HMN : N ≥ M := le_max_right _ _,
  intros n Hn,
  have H3 : |u n - a| < ε/2 := HL n (by linarith),
  have H4 : |v n - b| < ε/2 := HM n (by linarith),
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|   : by refl
   ... = |(u n - a) + (v n - b)|   : by { congr, ring }
   ... ≤ |(u n - a)| + |(v n - b)| : by apply abs_add
   ... < ε/2 + ε/2                 : by linarith
   ... = ε                         : by ring
end
