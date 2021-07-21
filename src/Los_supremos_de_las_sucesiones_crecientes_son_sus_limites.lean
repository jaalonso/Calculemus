-- Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.lean
-- Los supremos de las sucesiones crecientes son sus límites
-- José A. Alonso Jiménez
-- Sevilla, 23 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea u una sucesión creciente. Demostrar que si M es un supremo de u,
-- entonces el límite de u es M.
-- ---------------------------------------------------------------------

import data.real.basic

variable (u : ℕ → ℝ)
variable (M : ℝ)

notation `|`x`|` := abs x

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- (supremo u M) expresa que el supremo de u es M.
def supremo (u : ℕ → ℝ) (M : ℝ) :=
  (∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- 1ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
begin
  -- unfold limite,
  intros ε hε,
  -- unfold supremo at h,
  cases hM with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split,
  { -- unfold monotone at h',
    specialize hu hn,
    calc -ε
         = (M - ε) - M : by ring
     ... ≤ u n₀ - M    : sub_le_sub_right hn₀ M
     ... ≤ u n - M     : sub_le_sub_right hu M },
  { calc u n - M
         ≤ M - M       : sub_le_sub_right (hM₁ n) M
     ... = 0           : sub_self M
     ... ≤ ε           : le_of_lt hε, },
end

-- 2ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
begin
  intros ε hε,
  cases hM with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split,
  { linarith [hu hn] },
  { linarith [hM₁ n] },
end

-- 3ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
begin
  intros ε hε,
  cases hM with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split ; linarith [hu hn, hM₁ n],
end

-- 4ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
assume ε,
assume hε : ε > 0,
have hM₁ : ∀ (n : ℕ), u n ≤ M,
  from hM.left,
have hM₂ : ∀ (ε : ℝ), ε > 0 → (∃ (n₀ : ℕ), u n₀ ≥ M - ε),
  from hM.right,
exists.elim (hM₂ ε hε)
  ( assume n₀,
    assume hn₀ : u n₀ ≥ M - ε,
    have h1 : ∀ n, n ≥ n₀ → |u n - M| ≤ ε,
      { assume n,
        assume hn : n ≥ n₀,
        have h2 : -ε ≤ u n - M,
          { have h3 : u n₀ ≤ u n,
              from hu hn,
            calc -ε
                 = (M - ε) - M : by ring
             ... ≤ u n₀ - M    : sub_le_sub_right hn₀ M
             ... ≤ u n - M     : sub_le_sub_right h3 M },
        have h4 : u n - M ≤ ε,
          { calc u n - M
                 ≤ M - M       : sub_le_sub_right (hM₁ n) M
             ... = 0           : sub_self M
             ... ≤ ε           : le_of_lt hε },
        show |u n - M| ≤ ε,
          from abs_le.mpr (and.intro h2 h4) },
    show ∃ N, ∀ n, n ≥ N → |u n - M| ≤ ε,
      from exists.intro n₀ h1)
