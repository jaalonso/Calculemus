---
Título: Las funciones suprayectivas tienen inversa por la derecha
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

Demostrar que si f es una función suprayectiva, entonces f tiene inversa por la derecha.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

example
  (hf : surjective f)
  : has_right_inverse f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  unfold has_right_inverse,
  let g := λ y, some (hf y),
  use g,
  unfold function.right_inverse,
  unfold function.left_inverse,
  intro b,
  apply some_spec (hf b),
end

-- 2ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  let g := λ y, some (hf y),
  use g,
  intro b,
  apply some_spec (hf b),
end

-- 3ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  use surj_inv hf,
  intro b,
  exact surj_inv_eq hf b,
end

-- 4ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  use surj_inv hf,
  exact surj_inv_eq hf,
end

-- 5ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  use [surj_inv hf, surj_inv_eq hf],
end

-- 6ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
⟨surj_inv hf, surj_inv_eq hf⟩

-- 7ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
⟨_, surj_inv_eq hf⟩

-- 8ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
surjective.has_right_inverse hf
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_funciones_suprayectivas_tienen_inversa_por_la_derecha
imports Main
begin

definition tiene_inversa_dcha :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_dcha f ⟷ (∃g. ∀y. f (g y) = y)"

(* 1ª demostración *)
lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  let ?g = "λy. SOME x. f x = y"
  have "∀y. f (?g y) = y"
  proof (rule allI)
    fix y
    have "∃x. y = f x"
      using assms by (rule surjD)
    then have "∃x. f x = y"
      by auto
    then show "f (?g y) = y"
      by (rule someI_ex)
  qed
  then show "∃g. ∀y. f (g y) = y"
    by auto
qed

(* 2ª demostración *)
lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  let ?g = "λy. SOME x. f x = y"
  have "∀y. f (?g y) = y"
  proof (rule allI)
    fix y
    have "∃x. f x = y"
      by (metis assms surjD)
    then show "f (?g y) = y"
      by (rule someI_ex)
  qed
  then show "∃g. ∀y. f (g y) = y"
    by auto
qed

(* 3ª demostración *)
lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
proof (unfold tiene_inversa_dcha_def)
  have "∀y. f (inv f y) = y"
    by (simp add: assms surj_f_inv_f)
  then show "∃g. ∀y. f (g y) = y"
    by auto
qed

(* 4ª demostración *)
lemma
  assumes "surj f"
  shows   "tiene_inversa_dcha f"
  by (metis assms surjD tiene_inversa_dcha_def)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
