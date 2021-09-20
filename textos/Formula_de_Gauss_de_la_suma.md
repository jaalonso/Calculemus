---
Título: Fórmula de Gauss de la suma
Autor:  José A. Alonso
---

La fórmula de Gauss para la suma de los primeros números naturales es
<pre lang="text">
   0 + 1 + 2 + ... + (n-1) = n(n-1)/2
</pre>

En un [ejercicio anterior](https://bit.ly/2Xu3IKh) se ha demostrado dicha fórmula por inducción. Otra forma de demostrarla, sin usar inducción, es la siguiente: La suma se puede escribir de dos maneras
<pre lang="text">
   S = 0     + 1     + 2     + ... + (n-3) + (n-2) + (n-1)
   S = (n-1) + (n-2) + (n-3) + ... + 2     + 1     + 0
</pre>
Al sumar, se observa que cada par de números de la misma columna da como suma (n-1), y puesto que hay n columnas en total, se sigue
<pre lang="text">
   2S = n(n-1)
</pre>
lo que prueba la fórmula.

Demostrar la fórmula de Gauss siguiendo el procedimiento anterior.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.big_operators.basic
import algebra.big_operators.intervals

open_locale big_operators
open finset nat

variables (n i : ℕ)

example :
  (∑ i in range n, i) * 2 = n * (n - 1) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.big_operators.basic
import algebra.big_operators.intervals

open_locale big_operators
open finset nat

variables (n i : ℕ)

-- Lema auxiliar
-- =============

-- Se usará el siguiente lema auxiliar del que se presentan distintas
-- demostraciones.

-- 1ª demostración del lema auxiliar
example : ∀ x, x ∈ range n → x + (n - 1 - x) = n - 1 :=
begin
  intros x hx,
  replace hx : x < n := mem_range.1 hx,
  replace hx : x ≤ n - 1 := le_pred_of_lt hx,
  exact nat.add_sub_cancel' hx,
end

-- 2ª demostración del lema auxiliar
example : ∀ x, x ∈ range n → x + (n - 1 - x) = n - 1 :=
begin
  intros x hx,
  exact nat.add_sub_cancel' (le_pred_of_lt (mem_range.1 hx)),
end

-- 3ª demostración del lema auxiliar
lemma auxiliar : ∀ x, x ∈ range n → x + (n - 1 - x) = n - 1 :=
λ x hx, nat.add_sub_cancel' (le_pred_of_lt (mem_range.1 hx))

-- Lema principal
-- ==============

-- 1ª demostración
example :
  (∑ i in range n, i) * 2 = n * (n - 1) :=
calc (∑ i in range n, i) * 2
     = (∑ i in range n, i) + (∑ i in range n, i)
         : mul_two _
 ... = (∑ i in range n, i) + (∑ i in range n, (n - 1 - i))
         : congr_arg2 (+) rfl (sum_range_reflect id n).symm
 ... = ∑ i in range n, (i + (n - 1 - i))
         : sum_add_distrib.symm
 ... = ∑ i in range n, (n - 1)
         : sum_congr rfl (auxiliar n)
 ... = card (range n) • (n - 1)
         : sum_const (n - 1)
 ... = card (range n) * (n - 1)
         : nat.nsmul_eq_mul _ _
 ... = n * (n - 1)
         : congr_arg2 (*) (card_range n) rfl

-- 2ª demostración
example :
  (∑ i in range n, i) * 2 = n * (n - 1) :=
calc (∑ i in range n, i) * 2
     = (∑ i in range n, i) + (∑ i in range n, (n - 1 - i))
         : by rw [sum_range_reflect (λ i, i) n, mul_two]
 ... = ∑ i in range n, (i + (n - 1 - i))
         : sum_add_distrib.symm
 ... = ∑ i in range n, (n - 1)
         : sum_congr rfl (auxiliar n)
 ... = n * (n - 1)
         : by rw [sum_const, card_range, nat.nsmul_eq_mul]
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Formula_de_Gauss_de_la_suma.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Formula_de_Gauss_de_la_suma
imports Main
begin

lemma
  fixes n :: nat
  shows "2 * (∑i<n. i) = n * (n - 1)"
proof -
  have "2 * (∑i<n. i) = (∑i<n. i) + (∑i<n. i)"
    by simp
  also have "… = (∑i<n. i) + (∑i<n. n - Suc i)"
    using sum.nat_diff_reindex [where g = id] by auto
  also have "… = (∑i<n. (i + (n - Suc i)))"
    using sum.distrib [where A = "{..<n}" and
                             g = id and
                             h = "λi. n - Suc i"] by auto
  also have "… = (∑i<n. n - 1)"
    by simp
  also have "… = n * (n -1)"
    using sum_constant by auto
  finally show "2 * (∑i<n. i) = n * (n - 1)" .
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
