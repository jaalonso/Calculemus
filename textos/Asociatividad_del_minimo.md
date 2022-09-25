---
Título: Si a, b, c ∈ ℝ, entonces min(min(a,b),c) = min(a,min(b,c))
Autor:  José A. Alonso
---

Sean a, b y c números reales. Demostrar que
<pre lang="text">
   min (min a b) c = min a (min b c)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic tactic
variables a b c : ℝ

example :
  min (min a b) c = min a (min b c) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic tactic

variables a b c : ℝ

-- 1ª demostración
-- ===============

-- Se usará el siguiente lema auxilar.
lemma aux1 : min (min a b) c ≤ min a (min b c) :=
begin
  apply le_min,
  { show min (min a b) c ≤ a,
      calc min (min a b) c
           ≤ min a b : min_le_left (min a b) c
       ... ≤ a       : min_le_left a b },
  { show min (min a b) c ≤ min b c,
    apply le_min,
    { show min (min a b) c ≤ b,
        calc min (min a b) c
             ≤ min a b  : min_le_left (min a b) c
         ... ≤ b        : min_le_right a b },
    { show min (min a b) c ≤ c,
      { by exact min_le_right (min a b) c }}},
end

example :
  min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,
  { show min (min a b) c ≤ min a (min b c),
      by exact aux1 a b c },
  { show min a (min b c) ≤ min (min a b) c,
      calc min a (min b c)
           = min (min b c) a : by apply min_comm
       ... = min (min c b) a : by {congr' 1, apply min_comm}
       ... ≤ min c (min b a) : by apply aux1
       ... = min c (min a b) : by {congr' 1, apply min_comm}
       ... = min (min a b) c : by apply min_comm },
end

-- 2ª demostración
-- ===============

-- Se usará el siguiente lema auxilar.
lemma aux2 : min (min a b) c ≤ min a (min b c) :=
begin
  apply le_min,
  { calc min (min a b) c
         ≤ min a b : by simp [min_le_left]
     ... ≤ a       : by simp [min_le_left] },
  { apply le_min,
    { calc min (min a b) c
           ≤ min a b  : by simp [min_le_left]
       ... ≤ b        : by simp [min_le_right] },
    { simp [min_le_right] }},
end

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,
  { by exact aux2 a b c },
  { calc min a (min b c)
         = min (min b c) a : by simp [min_comm]
     ... = min (min c b) a : by simp [min_comm]
     ... ≤ min c (min b a) : by simp [aux2]
     ... = min c (min a b) : by simp [min_comm]
     ... = min (min a b) c : by simp [min_comm] },
end

-- 3ª demostración
-- ===============

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,
  { by exact aux2 a b c },
  { calc min a (min b c)
         = min (min c b) a : by simp [min_comm]
     ... ≤ min c (min b a) : by simp [aux2]
     ... = min (min a b) c : by simp [min_comm] },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Asociatividad_del_minimo.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 19.
