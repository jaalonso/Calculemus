---
Título: Las funciones con inversa por la izquierda son inyectivas
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

Demostrar que si f tiene inversa por la izquierda, entonces f es inyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

universes u v
variables {α : Type u}
variable  {β : Type v}
variable  {f : α → β}


example
  (hf : has_left_inverse f)
  : injective f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

universes u v
variables {α : Type u}
variable  {β : Type v}
variable  {f : α → β}

-- 1ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
begin
  intros x y hxy,
  unfold has_left_inverse at hf,
  unfold left_inverse at hf,
  cases hf with g hg,
  calc x = g (f x) : (hg x).symm
     ... = g (f y) : congr_arg g hxy
     ... = y       : hg y
end

-- 2ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
begin
  intros x y hxy,
  cases hf with g hg,
  calc x = g (f x) : (hg x).symm
     ... = g (f y) : congr_arg g hxy
     ... = y       : hg y
end

-- 3ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
exists.elim hf (λ finv inv, inv.injective)

-- 4ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
has_left_inverse.injective hf
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_funciones_con_inversa_por_la_izquierda_son_inyectivas
imports Main
begin

definition tiene_inversa_izq :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_izq f ⟷ (∃g. ∀x. g (f x) = x)"

(* 1ª demostración *)
lemma
  assumes "tiene_inversa_izq f"
  shows   "inj f"
proof (unfold inj_def; intro allI impI)
  fix x y
  assume "f x = f y"
  obtain g where hg : "∀x. g (f x) = x"
    using assms tiene_inversa_izq_def by auto
  have "x = g (f x)"
    by (simp only: hg)
  also have "… = g (f y)"
    by (simp only: ‹f x = f y›)
  also have "… = y"
    by (simp only: hg)
  finally show "x = y" .
qed

(* 2ª demostración *)
lemma
  assumes "tiene_inversa_izq f"
  shows   "inj f"
  by (metis assms inj_def tiene_inversa_izq_def)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
