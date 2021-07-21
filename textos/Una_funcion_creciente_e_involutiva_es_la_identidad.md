---
Título: Una función creciente e involutiva es la identidad
Autor:  José A. Alonso
---

Sea una función f de ℝ en ℝ.

+ Se dice que f es creciente si para todo x e y tales que x ≤ y se tiene que f(x) ≤ f(y).
+ Se dice que f es involutiva si para todo x se tiene que f(f(x)) = x.

En Lean que f sea creciente se representa por `monotone f` y que sea involutiva por `involutive f`

Demostrar que si f es creciente e involutiva, entonces f es la identidad.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open function

variable (f : ℝ → ℝ)

example
  (hc : monotone f)
  (hi : involutive f)
  : f = id :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open function

variable (f : ℝ → ℝ)

-- 1ª demostración
example
  (hc : monotone f)
  (hi : involutive f)
  : f = id :=
begin
  unfold monotone involutive at *,
  funext,
  unfold id,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    have h3 : f (f x) ≤ f x,
      { apply hc,
        exact h1, },
    rwa hi at h3, },
  { apply antisymm _ h2,
    have h4 : f x ≤ f (f x),
      { apply hc,
        exact h2, },
    rwa hi at h4, },
end

-- 2ª demostración
example
  (hc : monotone f)
  (hi : involutive f)
  : f = id :=
begin
  funext,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    have h3 : f (f x) ≤ f x := hc h1,
    rwa hi at h3, },
  { apply antisymm _ h2,
    have h4 : f x ≤ f (f x) := hc h2,
    rwa hi at h4, },
end

-- 3ª demostración
example
  (hc : monotone f)
  (hi : involutive f)
  : f = id :=
begin
  funext,
  cases (le_total (f x) x) with h1 h2,
  { apply antisymm h1,
    calc x
         = f (f x) : (hi x).symm
     ... ≤ f x     : hc h1 },
  { apply antisymm _ h2,
    calc f x
         ≤ f (f x) : hc h2
     ... = x       : hi x },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Una_funcion_creciente_e_involutiva_es_la_identidad.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Una_funcion_creciente_e_involutiva_es_la_identidad
imports Main HOL.Real
begin

definition involutiva :: "(real ⇒ real) ⇒ bool"
  where "involutiva f ⟷ (∀x. f (f x) = x)"

(* 1ª demostración *)
lemma
  fixes f :: "real ⇒ real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof (unfold fun_eq_iff; intro allI)
  fix x
  have "x ≤ f x ∨ f x ≤ x"
    by (rule linear)
  then have "f x = x"
  proof (rule disjE)
    assume "x ≤ f x"
    then have "f x ≤ f (f x)"
      using assms(1) by (simp only: monoD)
    also have "… = x"
      using assms(2) by (simp only: involutiva_def)
    finally have "f x ≤ x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by (simp only: antisym)
  next
    assume "f x ≤ x"
    have "x = f (f x)"
      using assms(2) by (simp only: involutiva_def)
    also have "... ≤ f x"
      using ‹f x ≤ x› assms(1) by (simp only: monoD)
    finally have "x ≤ f x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by (simp only: monoD)
  qed
  then show "f x = id x"
    by (simp only: id_apply)
qed

(* 2ª demostración *)
lemma
  fixes f :: "real ⇒ real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof
  fix x
  have "x ≤ f x ∨ f x ≤ x"
    by (rule linear)
  then have "f x = x"
  proof
    assume "x ≤ f x"
    then have "f x ≤ f (f x)"
      using assms(1) by (simp only: monoD)
    also have "… = x"
      using assms(2) by (simp only: involutiva_def)
    finally have "f x ≤ x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by auto
  next
    assume "f x ≤ x"
    have "x = f (f x)"
      using assms(2) by (simp only: involutiva_def)
    also have "... ≤ f x"
      by (simp add: ‹f x ≤ x› assms(1) monoD)
    finally have "x ≤ f x"
      by this
    show "f x = x"
      using ‹f x ≤ x› ‹x ≤ f x› by auto
  qed
  then show "f x = id x"
    by simp
qed

(* 3ª demostración *)
lemma
  fixes f :: "real ⇒ real"
  assumes "mono f"
          "involutiva f"
  shows   "f = id"
proof
  fix x
  have "x ≤ f x ∨ f x ≤ x"
    by (rule linear)
  then have "f x = x"
  proof
    assume "x ≤ f x"
    then have "f x ≤ x"
      by (metis assms involutiva_def mono_def)
    then show "f x = x"
      using ‹x ≤ f x› by auto
  next
    assume "f x ≤ x"
    then have "x ≤ f x"
      by (metis assms involutiva_def mono_def)
    then show "f x = x"
      using ‹f x ≤ x› by auto
  qed
  then show "f x = id x"
    by simp
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
