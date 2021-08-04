---
Título: Una función tiene inversa por la derecha si y solo si es suprayectiva
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

Demostrar que la función f tiene inversa por la derecha si y solo si es suprayectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

example : has_right_inverse f ↔ surjective f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example : has_right_inverse f ↔ surjective f :=
begin
  split,
  { intros hf b,
    cases hf with g hg,
    use g b,
    exact hg b, },
  { intro hf,
    let g := λ y, some (hf y),
    use g,
    intro b,
    apply some_spec (hf b), },
end

-- 2ª demostración
example : has_right_inverse f ↔ surjective f :=
surjective_iff_has_right_inverse.symm
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Una_funcion_tiene_inversa_por_la_derecha_si_y_solo_si_es_suprayectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Una_funcion_tiene_inversa_por_la_derecha_si_y_solo_si_es_suprayectiva
imports Main
begin

definition tiene_inversa_dcha :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_dcha f ⟷ (∃g. ∀y. f (g y) = y)"

(* 1ª demostración *)
lemma
  "tiene_inversa_dcha f ⟷ surj f"
proof (rule iffI)
  assume hf : "tiene_inversa_dcha f"
  show "surj f"
  proof (unfold surj_def; intro allI)
    fix y
    obtain g where "∀y. f (g y) = y"
      using hf tiene_inversa_dcha_def by auto
    then have "f (g y) = y"
      by (rule allE)
    then have "y = f (g y)"
      by (rule sym)
    then show "∃x. y = f x"
      by (rule exI)
  qed
next
  assume hf : "surj f"
  show "tiene_inversa_dcha f"
  proof (unfold tiene_inversa_dcha_def)
    let ?g = "λy. SOME x. f x = y"
    have "∀y. f (?g y) = y"
    proof (rule allI)
      fix y
      have "∃x. f x = y"
        by (metis hf surjD)
      then show "f (?g y) = y"
        by (rule someI_ex)
    qed
  then show "∃g. ∀y. f (g y) = y"
    by auto
  qed
qed

(* 2ª demostración *)
lemma
  "tiene_inversa_dcha f ⟷ surj f"
proof (rule iffI)
  assume "tiene_inversa_dcha f"
  then show "surj f"
    using tiene_inversa_dcha_def surj_def
    by metis
next
  assume "surj f"
  then show "tiene_inversa_dcha f"
    by (metis surjD tiene_inversa_dcha_def)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
