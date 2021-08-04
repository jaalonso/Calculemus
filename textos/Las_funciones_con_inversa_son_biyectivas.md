---
Título: Las funciones con inversa son biyectivas
Autor:  José A. Alonso
---

En Lean se puede definir que g es una inversa de f por
<pre lang="text">
   def inversa (f : X → Y) (g : Y → X) :=
     (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)
</pre>
y que f tiene inversa por
<pre lang="text">
   def tiene_inversa (f : X → Y) :=
     ∃ g, inversa f g
</pre>

Demostrar que si la función f tiene inversa, entonces f es biyectiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

variables {X Y : Type*}
variable  (f : X → Y)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa f g

example
  (hf : tiene_inversa f)
  : bijective f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

variables {X Y : Type*}
variable  (f : X → Y)

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa f g

-- 1ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  split,
  { intros a b hab,
    calc a = g (f a) : (h1 a).symm
       ... = g (f b) : congr_arg g hab
       ... = b       : h1 b, },
  { intro y,
    use g y,
    exact h2 y, },
end

-- 2ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  split,
  { intros a b hab,
    calc a = g (f a) : (h1 a).symm
       ... = g (f b) : congr_arg g hab
       ... = b       : h1 b, },
  { intro y,
    use [g y, h2 y], },
end

-- 3ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  split,
  { exact left_inverse.injective h1, },
  { exact right_inverse.surjective h2, },
end

-- 4ª demostración
example
  (hf : tiene_inversa f)
  : bijective f :=
begin
  rcases hf with ⟨g, ⟨h1, h2⟩⟩,
  exact ⟨left_inverse.injective h1,
         right_inverse.surjective h2⟩,
end

-- 5ª demostración
example :
  tiene_inversa f → bijective f :=
begin
  rintros ⟨g, ⟨h1, h2⟩⟩,
  exact ⟨left_inverse.injective h1,
         right_inverse.surjective h2⟩,
end

-- 6ª demostración
example :
  tiene_inversa f → bijective f :=
λ ⟨g, ⟨h1, h2⟩⟩, ⟨left_inverse.injective h1,
                  right_inverse.surjective h2⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_funciones_con_inversa_son_biyectivas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_funciones_con_inversa_son_biyectivas
imports Main
begin

definition inversa :: "('a ⇒ 'b) ⇒ ('b ⇒ 'a) ⇒ bool" where
  "inversa f g ⟷ (∀ x. (g ∘ f) x = x) ∧ (∀ y. (f ∘ g) y = y)"

definition tiene_inversa :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa f ⟷ (∃ g. inversa f g)"

(* 1ª demostración *)
lemma
  fixes f :: "'a ⇒ 'b"
  assumes "tiene_inversa f"
  shows   "bij f"
proof -
  obtain g where h1 : "∀ x. (g ∘ f) x = x" and
                 h2 : "∀ y. (f ∘ g) y = y"
    by (meson assms inversa_def tiene_inversa_def)
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
qed

(* 2ª demostración *)
lemma
  fixes f :: "'a ⇒ 'b"
  assumes "tiene_inversa f"
  shows   "bij f"
proof -
  obtain g where h1 : "∀ x. (g ∘ f) x = x" and
                 h2 : "∀ y. (f ∘ g) y = y"
    by (meson assms inversa_def tiene_inversa_def)
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
