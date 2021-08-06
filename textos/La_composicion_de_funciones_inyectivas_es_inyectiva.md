---
Título: La composición de funciones inyectivas es inyectiva
Autor:  José A. Alonso
---

Demostrar que la composición de dos funciones inyectivas es una función inyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
begin
  intros x y h,
  apply Hf,
  apply Hg,
  exact h,
end

-- 2ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
begin
  intros x y h,
  apply Hf,
  exact Hg h,
end

-- 3ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
begin
  intros x y h,
  exact Hf (Hg h),
end

-- 4ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
λ x y h, Hf (Hg h)

-- 5ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
assume x y,
assume h1 : (g ∘ f) x = (g ∘ f) y,
have h2 : f x = f y, from Hg h1,
show x = y, from Hf h2

-- 6ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
assume x y,
assume h1 : (g ∘ f) x = (g ∘ f) y,
show x = y, from Hf (Hg h1)

-- 7ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
assume x y,
assume h1 : (g ∘ f) x = (g ∘ f) y,
Hf (Hg h1)

-- 8ª demostración
example
  (Hf : injective f)
  (Hg : injective g)
  : injective (g ∘ f) :=
λ x y h1, Hf (Hg h1)

-- 9ª demostración
example
  (Hg : injective g)
  (Hf : injective f)
  : injective (g ∘ f) :=
-- by library_search
injective.comp Hg Hf

-- 10ª demostración
example
  (Hg : injective g)
  (Hf : injective f)
  : injective (g ∘ f) :=
-- by hint
by tauto
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_composicion_de_funciones_inyectivas_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_composicion_de_funciones_inyectivas_es_inyectiva
imports Main
begin

(* 1ª demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f ∘ g)"
proof (rule injI)
  fix x y
  assume "(f ∘ g) x = (f ∘ g) y"
  then have "f (g x) = f (g y)"
    by (simp only: o_apply)
  then have "g x = g y"
    using ‹inj f› by (simp only: injD)
  then show "x = y"
    using ‹inj g› by (simp only: injD)
qed

(* 2ª demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f ∘ g)"
using assms
by (simp add: inj_def)

(* 3ª demostración *)
lemma
  assumes "inj f"
          "inj g"
  shows   "inj (f ∘ g)"
using assms
by (rule inj_compose)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
