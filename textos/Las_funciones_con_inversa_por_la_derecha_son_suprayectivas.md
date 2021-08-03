---
Título: Las funciones con inversa por la derecha son suprayectivas
Autor:  José A. Alonso
---

En Lean, que g es una inversa por la izquierda de f está definido por
<pre lang="text">
   left_inverse (g : β → α) (f : α → β) : Prop :=
      ∀ x, g (f x) = x
</pre>
que g es una inversa por la derecha de f está definido por
<pre lang="text">
   right_inverse (g : β → α) (f : α → β) : Prop :=
      left_inverse f g
</pre>
y que f tenga inversa por la derecha está definido por
<pre lang="text">
   has_right_inverse (f : α → β) : Prop :=
      ∃ g : β → α, right_inverse g f
</pre>
Finalmente, que f es suprayectiva está definido por
<pre lang="text">
   def surjective (f : α → β) : Prop :=
      ∀ b, ∃ a, f a = b
</pre>

Demostrar que si la función f tiene inversa por la derecha, entonces f es suprayectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {α β: Type*}
variable  {f : α → β}

example
  (hf : has_right_inverse f)
  : surjective f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
begin
  unfold surjective,
  unfold has_right_inverse at hf,
  cases hf with g hg,
  intro b,
  use g b,
  exact hg b,
end

-- 2ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
begin
  intro b,
  cases hf with g hg,
  use g b,
  exact hg b,
end

-- 3ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
begin
  intro b,
  cases hf with g hg,
  use [g b, hg b],
end

-- 4ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
has_right_inverse.surjective hf
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_funciones_con_inversa_por_la_derecha_son_suprayectivas
imports Main
begin

definition tiene_inversa_dcha :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_dcha f ⟷ (∃g. ∀y. f (g y) = y)"

(* 1ª demostración *)
lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "∀y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then have "f (g y) = y"
    by (rule allE)
  then have "y = f (g y)"
    by (rule sym)
  then show "∃x. y = f x"
    by (rule exI)
qed

(* 2ª demostración *)
lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "∀y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then have "y = f (g y)"
    by simp
  then show "∃x. y = f x"
    by (rule exI)
qed

(* 3ª demostración *)
lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  obtain g where "∀y. f (g y) = y"
    using assms tiene_inversa_dcha_def by auto
  then show "∃x. y = f x"
    by metis
qed

(* 4ª demostración *)
lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
proof (unfold surj_def; intro allI)
  fix y
  show "∃x. y = f x"
    using assms tiene_inversa_dcha_def
    by metis
qed

(* 5ª demostración *)
lemma
  assumes "tiene_inversa_dcha f"
  shows   "surj f"
using assms tiene_inversa_dcha_def surj_def
by metis

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
