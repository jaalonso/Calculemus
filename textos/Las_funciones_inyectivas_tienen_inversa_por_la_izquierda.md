---
Título: Las funciones inyectivas tienen inversa por la izquierda
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

Demostrar que si f es una función inyectiva con dominio no vacío, entonces f tiene inversa por la izquierda.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
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
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  classical,
  unfold has_left_inverse,
  let g := λ y, if h : ∃ x, f x = y then some h else choice hα,
  use g,
  unfold left_inverse,
  intro a,
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl,
  dsimp at *,
  dsimp [g],
  rw dif_pos h1,
  apply hf,
  exact some_spec h1,
end

-- 2ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  classical,
  let g := λ y, if h : ∃ x, f x = y then some h else choice hα,
  use g,
  intro a,
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl,
  dsimp [g],
  rw dif_pos h1,
  exact hf (some_spec h1),
end

-- 3ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  unfold has_left_inverse,
  use inv_fun f,
  unfold left_inverse,
  intro x,
  apply hf,
  apply inv_fun_eq,
  use x,
end

-- 4ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  use inv_fun f,
  intro x,
  apply hf,
  apply inv_fun_eq,
  use x,
end

-- 5ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
⟨inv_fun f, left_inverse_inv_fun hf⟩

-- 6ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
injective.has_left_inverse hf
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_funciones_inyectivas_tienen_inversa_por_la_izquierda
imports Main
begin

definition tiene_inversa_izq :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa_izq f ⟷ (∃g. ∀x. g (f x) = x)"

(* 1ª demostración *)
lemma
  assumes "inj f"
  shows   "tiene_inversa_izq f"
proof (unfold tiene_inversa_izq_def)
  let ?g = "(λy. SOME x. f x = y)"
  have "∀x. ?g (f x) = x"
  proof (rule allI)
    fix a
    have "∃x. f x = f a"
      by auto
    then have "f (?g (f a)) = f a"
      by (rule someI_ex)
    then show "?g (f a) = a"
      using assms
      by (simp only: injD)
  qed
  then show "(∃g. ∀x. g (f x) = x)"
    by (simp only: exI)
qed

(* 2ª demostración *)
lemma
  assumes "inj f"
  shows   "tiene_inversa_izq f"
proof (unfold tiene_inversa_izq_def)
  have "∀x. inv f (f x) = x"
  proof (rule allI)
    fix x
    show "inv f (f x) = x"
      using assms by (simp only: inv_f_f)
  qed
  then show "(∃g. ∀x. g (f x) = x)"
    by (simp only: exI)
qed

(* 3ª demostración *)
lemma
  assumes "inj f"
  shows   "tiene_inversa_izq f"
proof (unfold tiene_inversa_izq_def)
  have "∀x. inv f (f x) = x"
    by (simp add: assms)
  then show "(∃g. ∀x. g (f x) = x)"
    by (simp only: exI)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
