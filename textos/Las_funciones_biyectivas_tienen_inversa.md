---
Título: Las funciones biyectivas tienen inversa
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

Demostrar que si la función f es biyectiva, entonces f tiene inversa.

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
  (hf : bijective f)
  : tiene_inversa f :=
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
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use g,
  split,
  { intro a,
    apply hfiny,
    rw hg (f a), },
  { exact hg, },
end

-- 2ª demostración
example
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use g,
  split,
  { intro a,
    exact @hfiny (g (f a)) a (hg (f a)), },
  { exact hg, },
end

-- 3ª demostración
example
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use g,
  exact ⟨λ a, @hfiny (g (f a)) a (hg (f a)), hg⟩,
end

-- 4ª demostración
example
  (hf : bijective f)
  : tiene_inversa f :=
begin
  rcases hf with ⟨hfiny, hfsup⟩,
  choose g hg using hfsup,
  use [g, ⟨λ a, @hfiny (g (f a)) a (hg (f a)), hg⟩],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_funciones_biyectivas_tienen_inversa.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_funciones_biyectivas_tienen_inversa
imports Main
begin

definition inversa :: "('a ⇒ 'b) ⇒ ('b ⇒ 'a) ⇒ bool" where
  "inversa f g ⟷ (∀ x. (g ∘ f) x = x) ∧ (∀ y. (f ∘ g) y = y)"

definition tiene_inversa :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa f ⟷ (∃ g. inversa f g)"

(* 1ª demostración *)
lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "surj f"
    using assms by (rule bij_is_surj)
  then obtain g where hg : "∀y. f (g y) = y"
    by (metis surjD)
  have "inversa f g"
  proof (unfold inversa_def; intro conjI)
    show "∀x. (g ∘ f) x = x"
    proof (rule allI)
      fix x
      have "inj f"
        using ‹bij f› by (rule bij_is_inj)
      then show "(g ∘ f) x = x"
      proof (rule injD)
        have "f ((g ∘ f) x) = f (g (f x))"
          by simp
        also have "… = f x"
          by (simp add: hg)
        finally show "f ((g ∘ f) x) = f x"
          by this
      qed
    qed
    next
      show "∀y. (f ∘ g) y = y"
        by (simp add: hg)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by blast
qed

(* 2ª demostración *)
lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "surj f"
    using assms by (rule bij_is_surj)
  then obtain g where hg : "∀y. f (g y) = y"
    by (metis surjD)
  have "inversa f g"
  proof (unfold inversa_def; intro conjI)
    show "∀x. (g ∘ f) x = x"
    proof (rule allI)
      fix x
      have "inj f"
        using ‹bij f› by (rule bij_is_inj)
      then show "(g ∘ f) x = x"
      proof (rule injD)
        have "f ((g ∘ f) x) = f (g (f x))"
          by simp
        also have "… = f x"
          by (simp add: hg)
        finally show "f ((g ∘ f) x) = f x"
          by this
      qed
    qed
  next
    show "∀y. (f ∘ g) y = y"
      by (simp add: hg)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

(* 3ª demostración *)
lemma
  assumes "bij f"
  shows   "tiene_inversa f"
proof -
  have "inversa f (inv f)"
  proof (unfold inversa_def; intro conjI)
    show "∀x. (inv f ∘ f) x = x"
      by (simp add: ‹bij f› bij_is_inj)
  next
    show "∀y. (f ∘ inv f) y = y"
      by (simp add: ‹bij f› bij_is_surj surj_f_inv_f)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
