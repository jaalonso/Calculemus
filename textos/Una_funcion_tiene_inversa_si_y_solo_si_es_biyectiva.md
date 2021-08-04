---
Título: Una función tiene inversa si y solo si es biyectiva
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

Demostrar que la función f tiene inversa si y solo si f es biyectiva.

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

example : tiene_inversa f ↔ bijective f :=
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
example : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use g y,
      exact h2 y, }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use g,
    split,
    { intro a,
      apply hfinj,
      rw hg (f a), },
    { exact hg, }},
end

-- 2ª demostración
example : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use [g y, h2 y], }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use g,
    split,
    { intro a,
      exact @hfinj (g (f a)) a (hg (f a)), },
    { exact hg, }},
end

-- 3ª demostración
example : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use [g y, h2 y], }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use g,
    exact ⟨λ a, @hfinj (g (f a)) a (hg (f a)), hg⟩, },
end

-- 4ª demostración
example
  : tiene_inversa f ↔ bijective f :=
begin
  split,
  { rintro ⟨g, ⟨h1, h2⟩⟩,
    split,
    { intros p q hf,
      calc p = g (f p) : (h1 p).symm
         ... = g (f q) : congr_arg g hf
         ... = q       : h1 q, },
    { intro y,
      use [g y, h2 y], }},
  { rintro ⟨hfinj, hfsur⟩,
    choose g hg using hfsur,
    use [g, ⟨λ a, @hfinj (g (f a)) a (hg (f a)), hg⟩], },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Una_funcion_tiene_inversa_si_y_solo_si_es_biyectiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Una_funcion_tiene_inversa_si_y_solo_si_es_biyectiva
imports Main
begin

definition inversa :: "('a ⇒ 'b) ⇒ ('b ⇒ 'a) ⇒ bool" where
  "inversa f g ⟷ (∀ x. (g ∘ f) x = x) ∧ (∀ y. (f ∘ g) y = y)"

definition tiene_inversa :: "('a ⇒ 'b) ⇒ bool" where
  "tiene_inversa f ⟷ (∃ g. inversa f g)"

(* 1ª demostración *)
lemma "tiene_inversa f ⟷ bij f"
proof (rule iffI)
  assume "tiene_inversa f"
  then obtain g where h1 : "∀ x. (g ∘ f) x = x" and
                      h2 : "∀ y. (f ∘ g) y = y"
    using inversa_def tiene_inversa_def by metis
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
next
  assume "bij f"
  then have "surj f"
    by (rule bij_is_surj)
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

(* 2ª demostración *)
lemma "tiene_inversa f ⟷ bij f"
proof (rule iffI)
  assume "tiene_inversa f"
  then obtain g where h1 : "∀ x. (g ∘ f) x = x" and
                      h2 : "∀ y. (f ∘ g) y = y"
    using inversa_def tiene_inversa_def by metis
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
next
  assume "bij f"
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
