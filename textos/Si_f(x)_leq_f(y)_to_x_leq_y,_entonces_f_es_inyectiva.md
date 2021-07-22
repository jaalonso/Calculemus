---
Título: Si `f x ≤ f y → x ≤ y`, entonces f es inyectiva
Autor:  José A. Alonso
---

Sea f una función de ℝ en ℝ tal que
<pre lang="text">
   ∀ x y, f(x) ≤ f(y) → x ≤ y
</pre>
Demostrar que f es inyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open function

variable (f : ℝ → ℝ)

example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : injective f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open function

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : injective f :=
begin
  intros x y hxy,
  apply le_antisymm,
  { apply h,
    exact le_of_eq hxy, },
  { apply h,
    exact ge_of_eq hxy, },
end

-- 2ª demostración
example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : injective f :=
begin
  intros x y hxy,
  apply le_antisymm,
  { exact h (le_of_eq hxy), },
  { exact h (ge_of_eq hxy), },
end

-- 3ª demostración
example
  (h : ∀ {x y}, f x ≤ f y → x ≤ y)
  : injective f :=
λ x y hxy, le_antisymm (h hxy.le) (h hxy.ge)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva"
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes f :: "real ⇒ real"
  assumes "∀ x y. f x ≤ f y ⟶ x ≤ y"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  show "x = y"
  proof (rule antisym)
    show "x ≤ y"
      by (simp only: assms ‹f x = f y›)
  next
    show "y ≤ x"
      by (simp only: assms ‹f x = f y›)
  qed
qed

(* 2ª demostración *)
lemma
  fixes f :: "real ⇒ real"
  assumes "∀ x y. f x ≤ f y ⟶ x ≤ y"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  then show "x = y"
    using assms
    by (simp add: eq_iff)
qed

(* 3ª demostración *)
lemma
  fixes f :: "real ⇒ real"
  assumes "∀ x y. f x ≤ f y ⟶ x ≤ y"
  shows   "inj f"
  by (smt (verit, ccfv_threshold) assms inj_on_def)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
