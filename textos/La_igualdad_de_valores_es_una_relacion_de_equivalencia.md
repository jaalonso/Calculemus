---
Título: La igualdad de valores es una relación de equivalencia
Autor:  José A. Alonso
---

Sean X e Y dos conjuntos y f una función de X en Y. Se define la relación R en X de forma que x está relacionado con y si f(x) = f(y).

Demostrar que R es una relación de equivalencia.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

universe u
variables {X Y : Type u}
variable  (f : X → Y)

def R (x y : X) := f x = f y

example : equivalence (R f) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

universe u
variables {X Y : Type u}
variable  (f : X → Y)

def R (x y : X) := f x = f y

-- 1ª demostración
example : equivalence (R f) :=
begin
  unfold equivalence,
  repeat { split },
  { unfold reflexive,
    intro x,
    unfold R, },
  { unfold symmetric,
    intros x y hxy,
    unfold R,
    exact symm hxy, },
  { unfold transitive,
    unfold R,
    intros x y z hxy hyz,
    exact eq.trans hxy hyz, },
end

-- 2ª demostración
example : equivalence (R f) :=
begin
  repeat { split },
  { intro x,
    exact rfl, },
  { intros x y hxy,
    exact eq.symm hxy, },
  { intros x y z hxy hyz,
    exact eq.trans hxy hyz, },
end

-- 3ª demostración
example : equivalence (R f) :=
begin
  repeat { split },
  { exact λ x, rfl, },
  { exact λ x y hxy, eq.symm hxy, },
  { exact λ x y z hxy hyz, eq.trans hxy hyz, },
end

-- 4ª demostración
example : equivalence (R f) :=
⟨λ x, rfl,
 λ x y hxy, eq.symm hxy,
 λ x y z hxy hyz, eq.trans hxy hyz⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_igualdad_de_valores_es_una_relacion_de_equivalencia.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_igualdad_de_valores_es_una_relacion_de_equivalencia
imports Main
begin

definition R :: "('a ⇒ 'b) ⇒ 'a ⇒ 'a ⇒ bool" where
  "R f x y ⟷ (f x = f y)"

(* 1ª demostración *)
lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
  proof (rule reflpI)
    fix x
    have "f x = f x"
      by (rule refl)
    then show "R f x x"
      by (unfold R_def)
  qed
next
  show "symp (R f)"
  proof (rule sympI)
    fix x y
    assume "R f x y"
    then have "f x = f y"
      by (unfold R_def)
    then have "f y = f x"
      by (rule sym)
    then show "R f y x"
      by (unfold R_def)
  qed
next
  show "transp (R f)"
  proof (rule transpI)
    fix x y z
    assume "R f x y" and "R f y z"
    then have "f x = f y" and "f y = f z"
      by (unfold R_def)
    then have "f x = f z"
      by (rule ssubst)
    then show "R f x z"
      by (unfold R_def)
  qed
qed

(* 2ª demostración *)
lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
  proof (rule reflpI)
    fix x
    show "R f x x"
      by (metis R_def)
  qed
next
  show "symp (R f)"
  proof (rule sympI)
    fix x y
    assume "R f x y"
    then show "R f y x"
      by (metis R_def)
  qed
next
  show "transp (R f)"
  proof (rule transpI)
    fix x y z
    assume "R f x y" and "R f y z"
    then show "R f x z"
      by (metis R_def)
  qed
qed

(* 3ª demostración *)
lemma "equivp (R f)"
proof (rule equivpI)
  show "reflp (R f)"
    by (simp add: R_def reflpI)
next
  show "symp (R f)"
    by (metis R_def sympI)
next
  show "transp (R f)"
    by (metis R_def transpI)
qed

(* 4ª demostración *)
lemma "equivp (R f)"
  by (metis R_def
            equivpI
            reflpI
            sympI
            transpI)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
