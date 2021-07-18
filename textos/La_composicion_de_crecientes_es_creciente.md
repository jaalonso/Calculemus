---
Título: La composición de crecientes es creciente
Autor:  José A. Alonso
---

Se dice que una función f de ℝ en ℝ es [creciente](https://bit.ly/2UShggL) si para todo x e y tales que x ≤ y se tiene que f(x) ≤ f(y).

En Lean que f sea creciente se representa por `monotone f`.

Demostrar que la composición de dos funciones crecientes es una función creciente.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y hxy,
  calc (g ∘ f) x
       = g (f x)   : rfl
   ... ≤ g (f y)   : hg (hf hxy)
   ... = (g ∘ f) y : rfl,
end

-- 2ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  unfold monotone at *,
  intros x y h,
  unfold function.comp,
  apply hg,
  apply hf,
  exact h,
end

-- 3ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y h,
  apply hg,
  apply hf,
  exact h,
end

-- 4ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x xy h,
  apply hg,
  exact hf h,
end

-- 5ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y h,
  exact hg (hf h),
end

-- 6ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
λ x y h, hg (hf h)

-- 7ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
begin
  intros x y h,
  specialize hf h,
  exact hg hf,
end

-- 8ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
assume x y,
assume h1 : x ≤ y,
have h2 : f x ≤ f y,
  from hf h1,
show (g ∘ f) x ≤ (g ∘ f) y, from
  calc (g ∘ f) x
       = g (f x)   : rfl
   ... ≤ g (f y)   : hg h2
   ... = (g ∘ f) y : by refl

-- 9ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
-- by hint
by tauto

-- 10ª demostración
example
  (hf : monotone f)
  (hg : monotone g)
  : monotone (g ∘ f) :=
-- by library_search
monotone.comp hg hf
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_composicion_de_crecientes_es_creciente.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_composicion_de_crecientes_es_creciente
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes f g :: "real ⇒ real"
  assumes "mono f"
          "mono g"
  shows   "mono (g ∘ f)"
proof (rule monoI)
  fix x y :: real
  assume "x ≤ y"
  have "(g ∘ f) x = g (f x)"
    by (simp only: o_apply)
  also have "… ≤ g (f y)"
    using assms ‹x ≤ y›
    by (simp only: monoD)
  also have "… = (g ∘ f) y"
    by (simp only: o_apply)
  finally show "(g ∘ f) x ≤ (g ∘ f) y"
    by this
qed

(* 2ª demostración *)
lemma
  fixes f g :: "real ⇒ real"
  assumes "mono f"
          "mono g"
  shows   "mono (g ∘ f)"
proof (rule monoI)
  fix x y :: real
  assume "x ≤ y"
  have "(g ∘ f) x = g (f x)"    by simp
  also have "… ≤ g (f y)"     by (simp add: ‹x ≤ y› assms monoD)
  also have "… = (g ∘ f) y"    by simp
  finally show "(g ∘ f) x ≤ (g ∘ f) y" .
qed

(* 3ª demostración *)
lemma
  assumes "mono f"
          "mono g"
  shows   "mono (g ∘ f)"
  by (metis assms comp_def mono_def)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
