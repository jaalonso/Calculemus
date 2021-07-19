---
Título: La composición de una función creciente y una decreciente es decreciente
Autor:  José A. Alonso
---

Sea una función f de ℝ en ℝ. Se dice que f es creciente si para todo x e y tales que x ≤ y se tiene que f(x) ≤ f(y). Se dice que f es decreciente si para todo x e y tales que x ≤ y se tiene que f(x) ≥ f(y).

Demostrar que si f es creciente y g es decreciente, entonces (g ∘ f) es decreciente.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x y}, x ≤ y → f x ≤ f y

def decreciente (f : ℝ → ℝ) : Prop :=
∀ {x y}, x ≤ y → f x ≥ f y

example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables (f g : ℝ → ℝ)

def creciente (f : ℝ → ℝ) : Prop :=
∀ {x y}, x ≤ y → f x ≤ f y

def decreciente (f : ℝ → ℝ) : Prop :=
∀ {x y}, x ≤ y → f x ≥ f y

-- 1ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y hxy,
  calc (g ∘ f) x
       = g (f x)   : rfl
   ... ≥ g (f y)   : hg (hf hxy)
   ... = (g ∘ f) y : rfl,
end

-- 2ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  unfold creciente decreciente at *,
  intros x y h,
  unfold function.comp,
  apply hg,
  apply hf,
  exact h,
end

-- 3ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y h,
  apply hg,
  apply hf,
  exact h,
end

-- 4ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y h,
  apply hg,
  exact hf h,
end

-- 5ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
begin
  intros x y h,
  exact hg (hf h),
end

-- 6ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
λ x y h, hg (hf h)

-- 7ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
assume x y,
assume h : x ≤ y,
have h1 : f x ≤ f y,
  from hf h,
show (g ∘ f) x ≥ (g ∘ f) y,
  from hg h1

-- 8ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
assume x y,
assume h : x ≤ y,
show (g ∘ f) x ≥ (g ∘ f) y,
  from hg (hf h)

-- 9ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
λ x y h, hg (hf h)

-- 10ª demostración
example
  (hf : creciente f)
  (hg : decreciente g)
  : decreciente (g ∘ f) :=
-- by hint
by tauto
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_composicion_de_una_funcion_creciente_y_una_decreciente_es_decreciente
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes f g :: "real ⇒ real"
  assumes "mono f"
          "antimono g"
  shows   "antimono (g ∘ f)"
proof (rule antimonoI)
  fix x y :: real
  assume "x ≤ y"
  have "(g ∘ f) y = g (f y)"
    by (simp only: o_apply)
  also have "… ≤ g (f x)"
    using assms ‹x ≤ y›
    by (meson antimonoE monoE)
  also have "… = (g ∘ f) x"
    by (simp only: o_apply)
  finally show "(g ∘ f) x ≥ (g ∘ f) y"
    by this
qed

(* 2ª demostración *)
lemma
  fixes f g :: "real ⇒ real"
  assumes "mono f"
          "antimono g"
  shows   "antimono (g ∘ f)"
proof (rule antimonoI)
  fix x y :: real
  assume "x ≤ y"
  have "(g ∘ f) y = g (f y)"    by simp
  also have "… ≤ g (f x)"     by (meson ‹x ≤ y› assms antimonoE monoE)
  also have "… = (g ∘ f) x"    by simp
  finally show "(g ∘ f) x ≥ (g ∘ f) y" .
qed

(* 3ª demostración *)
lemma
  assumes "mono f"
          "antimono g"
  shows   "antimono (g ∘ f)"
  by (metis assms mono_def antimono_def comp_apply)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
