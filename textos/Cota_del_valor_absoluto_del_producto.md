---
Título: Si x,y,ε ∈ ℝ tales que 0 < ε ≤ 1, |x| < ε y |y| < ε, entonces |x*y| < ε
Autor:  José A. Alonso
---

Demostrar que si x,y,ε ∈ ℝ tales que 0 < ε ≤ 1, |x| < ε y |y| < ε, entonces |x*y| < ε.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic tactic

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic tactic

-- 1ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
begin
  intros x y ε he1 he2 hx hy,
  by_cases h : (|x| = 0),
  { calc |x * y|
         = |x| * |y| : abs_mul x y
     ... = 0 * |y|   : by rw h
     ... = 0         : zero_mul (abs y)
     ... < ε         : he1 },
  { have h1 : 0 < |x|,
    { have h2 : 0 ≤ |x| := abs_nonneg x,
      show 0 < |x|,
        exact lt_of_le_of_ne h2 (ne.symm h) },
    calc |x * y|
         = |x| * |y| : abs_mul x y
     ... < |x| * ε   : (mul_lt_mul_left h1).mpr hy
     ... < ε * ε     : (mul_lt_mul_right he1).mpr hx
     ... ≤ 1 * ε     : (mul_le_mul_right he1).mpr he2
     ... = ε         : one_mul ε },
end

-- 2ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
begin
  intros x y ε he1 he2 hx hy,
  by_cases h : (|x| = 0),
  { calc |x * y|
         = |x| * |y| : by apply abs_mul
     ... = 0 * |y|   : by rw h
     ... = 0         : by apply zero_mul
     ... < ε         : by apply he1 },
  { have h1 : 0 < |x|,
      { have h2 : 0 ≤ |x|,
          apply abs_nonneg,
        exact lt_of_le_of_ne h2 (ne.symm h) },
    calc |x * y|
         = |x| * |y| : by rw abs_mul
     ... < |x| * ε   : by apply (mul_lt_mul_left h1).mpr hy
     ... < ε * ε     : by apply (mul_lt_mul_right he1).mpr hx
     ... ≤ 1 * ε     : by apply (mul_le_mul_right he1).mpr he2
     ... = ε         : by rw [one_mul] },
end

-- 3ª demostración
-- ===============

example :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
begin
  intros x y ε he1 he2 hx hy,
  by_cases (|x| = 0),
  { by finish },
  { have : 0 < |x|, by finish,
    calc |x * y|
         = |x| * |y| : by rw abs_mul
     ... < |x| * ε   : by finish
     ... ≤ 1 * ε     : by nlinarith
     ... = ε         : by finish },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Cota_del_valor_absoluto_del_producto.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 26.
