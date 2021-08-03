---
Título: Una función tiene inversa por la izquierda si y solo si es inyectiva
Autor:  José A. Alonso
---

En Lean, que g es una inversa por la izquierda de f que está definido en Lean por
<pre lang="text">
   left_inverse (g : β → α) (f : α → β) : Prop :=
      ∀ x, g (f x) = x
</pre>
y que f tenga inversa por la izquierda está definido por
<pre lang="text">
   has_left_inverse (f : α → β) : Prop :=
      ∃ finv : β → α, left_inverse finv f
</pre>
Finalmente, que f es inyectiva está definido por
<pre lang="text">
   injective (f : α → β) : Prop :=
      ∀ ⦃x y⦄, f x = f y → x = y
</pre>

Demostrar que una función f, con dominio no vacío, tiene inversa por la izquierda si y solo si es inyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {α : Type*} [nonempty α]
variable  {β : Type*}
variable  {f : α → β}

example :
  has_left_inverse f ↔ injective f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

variables {α : Type*} [nonempty α]
variable  {β : Type*}
variable  {f : α → β}

-- 1ª demostración
example : has_left_inverse f ↔ injective f :=
begin
  split,
  { intro hf,
    intros x y hxy,
    cases hf with g hg,
    calc x = g (f x) : (hg x).symm
       ... = g (f y) : congr_arg g hxy
       ... = y       : hg y, },
  { intro hf,
    use inv_fun f,
    intro x,
    apply hf,
    apply inv_fun_eq,
    use x, },
end

-- 2ª demostración
example : has_left_inverse f ↔ injective f :=
begin
  split,
  { intro hf,
    exact has_left_inverse.injective hf },
  { intro hf,
    exact injective.has_left_inverse hf },
end

-- 3ª demostración
example : has_left_inverse f ↔ injective f :=
⟨has_left_inverse.injective, injective.has_left_inverse⟩

-- 4ª demostración
example : has_left_inverse f ↔ injective f :=
injective_iff_has_left_inverse.symm
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Una_funcion_tiene_inversa_por_la_izquierda_si_y_solo_si_es_inyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Una_funcion_tiene_inversa_por_la_izquierda_si_y_solo_si_es_inyectiva
imports Main
begin

definition tiene_inversa_izq :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_izq f ⟷ (∃g. ∀x. g (f x) = x)"

(* 1ª demostración *)
lemma
  "tiene_inversa_izq f ⟷ inj f"
proof (rule iffI)
  assume "tiene_inversa_izq f"
  show "inj f"
  proof (unfold inj_def; intro allI impI)
    fix x y
    assume "f x = f y"
    obtain g where hg : "∀x. g (f x) = x"
      using ‹tiene_inversa_izq f› tiene_inversa_izq_def
      by auto
    have "x = g (f x)"
      by (simp only: hg)
    also have "… = g (f y)"
      by (simp only: ‹f x = f y›)
    also have "… = y"
      by (simp only: hg)
    finally show "x = y" .
  qed
next
  assume "inj f"
  show "tiene_inversa_izq f"
  proof (unfold tiene_inversa_izq_def)
    have "∀x. inv f (f x) = x"
    proof (rule allI)
      fix x
      show "inv f (f x) = x"
        using ‹inj f› by (simp only: inv_f_f)
    qed
  then show "(∃g. ∀x. g (f x) = x)"
    by (simp only: exI)
  qed
qed

(* 2ª demostración *)
lemma
  "tiene_inversa_izq f ⟷ inj f"
proof (rule iffI)
  assume "tiene_inversa_izq f"
  then show "inj f"
    by (metis inj_def tiene_inversa_izq_def)
next
  assume "inj f"
  then show "tiene_inversa_izq f"
    by (metis the_inv_f_f tiene_inversa_izq_def)
qed

(* 3ª demostración *)
lemma
  "tiene_inversa_izq f ⟷ inj f"
by (metis tiene_inversa_izq_def inj_def the_inv_f_f)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
