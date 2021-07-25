---
Título: La paradoja del barbero
Autor:  José A. Alonso
---

Demostrar la [paradoja del barbero](https://bit.ly/3eWyvVw); es decir, que no existe un hombre que afeite a todos los que no se afeitan a sí mismo y sólo a los que no se afeitan a sí mismo.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable (Hombre : Type)
variable (afeita : Hombre → Hombre → Prop)

example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable (Hombre : Type)
variable (afeita : Hombre → Hombre → Prop)

-- 1ª demostración
example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
begin
  intro h,
  cases h with b hb,
  specialize hb b,
  by_cases (afeita b b),
  { apply absurd h,
    exact hb.mp h, },
  { apply h,
    exact hb.mpr h, },
end

-- 2ª demostración
example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
begin
  intro h,
  cases h with b hb,
  specialize hb b,
  by_cases (afeita b b),
  { exact (hb.mp h) h, },
  { exact h (hb.mpr h), },
end

-- 3ª demostración
example :
  ¬(∃ x : Hombre, ∀ y : Hombre, afeita x y ↔ ¬ afeita y y) :=
begin
  intro h,
  cases h with b hb,
  specialize hb b,
  by itauto,
end

-- 4ª demostración
example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
begin
  rintro ⟨b, hb⟩,
  exact (iff_not_self (afeita b b)).mp (hb b),
end

-- 5ª demostración
example :
  ¬ (∃ x : Hombre,  ∀ y : Hombre, afeita x y ↔ ¬ afeita y y ) :=
λ ⟨b, hb⟩, (iff_not_self (afeita b b)).mp (hb b)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_paradoja_del_barbero.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_paradoja_del_barbero
imports Main
begin

(* 1ª demostración *)
lemma
  "¬(∃ x::'H. ∀ y::'H. afeita x y ⟷ ¬ afeita y y)"
proof (rule notI)
  assume "∃ x. ∀ y. afeita x y ⟷ ¬ afeita y y"
  then obtain b where "∀ y. afeita b y ⟷ ¬ afeita y y"
    by (rule exE)
  then have h : "afeita b b ⟷ ¬ afeita b b"
    by (rule allE)
  show False
  proof (cases "afeita b b")
    assume "afeita b b"
    then have "¬ afeita b b"
      using h by (rule rev_iffD1)
    then show False
      using ‹afeita b b› by (rule notE)
  next
    assume "¬ afeita b b"
    then have "afeita b b"
      using h by (rule rev_iffD2)
    with ‹¬ afeita b b› show False
      by (rule notE)
  qed
qed

(* 2ª demostración *)
lemma
  "¬(∃ x::'H. ∀ y::'H. afeita x y ⟷ ¬ afeita y y)"
proof
  assume "∃ x. ∀ y. afeita x y ⟷ ¬ afeita y y"
  then obtain b where "∀ y. afeita b y ⟷ ¬ afeita y y"
    by (rule exE)
  then have h : "afeita b b ⟷ ¬ afeita b b"
    by (rule allE)
  then show False
    by simp
qed

(* 3ª demostración *)
lemma
  "¬(∃ x::'H. ∀ y::'H. afeita x y ⟷ ¬ afeita y y)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
