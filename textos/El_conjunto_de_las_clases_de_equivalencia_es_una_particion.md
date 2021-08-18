---
Título: El conjunto de las clases de equivalencia es una partición.
Autor:  José A. Alonso
---

Demostrar que si R es una relación de equivalencia en X, entonces las clases de equivalencia de R es una partición de X.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

def particion (A : set (set X)) : Prop :=
  (∀ x, (∃ B ∈ A, x ∈ B ∧ ∀ C ∈ A, x ∈ C → B = C)) ∧ ∅ ∉ A

example
  (h : equivalence R)
  : particion {a : set X | ∃ s : X, a = clase R s} :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable  {X : Type}
variables {x y: X}
variable  {R : X → X → Prop}

def clase (R : X → X → Prop) (x : X) :=
  {y : X | R x y}

def particion (A : set (set X)) : Prop :=
  (∀ x, (∃ B ∈ A, x ∈ B ∧ ∀ C ∈ A, x ∈ C → B = C)) ∧ ∅ ∉ A

lemma aux
  (h : equivalence R)
  (hxy : R x y)
  : clase R y ⊆ clase R x :=
λ z hz, h.2.2 hxy hz

-- 1ª demostración
example
  (h : equivalence R)
  : particion {a : set X | ∃ s : X, a = clase R s} :=
begin
  split,
  { simp,
    intro y,
    use (clase R y),
    split,
    { use y, },
    { split,
      { exact h.1 y, },
      { intros x hx,
        apply le_antisymm,
        { exact aux h hx, },
        { exact aux h (h.2.1 hx), }}}},
  { simp,
    intros x hx,
    have h1 : x ∈ clase R x := h.1 x,
    rw ← hx at h1,
    exact set.not_mem_empty x h1, },
end

-- 2ª demostración
example
  (h : equivalence R)
  : particion {a : set X | ∃ s : X, a = clase R s} :=
begin
  split,
  { simp,
    intro y,
    use (clase R y),
    split,
    { use y, },
    { split,
      { exact h.1 y, },
      { intros x hx,
        exact le_antisymm (aux h hx) (aux h (h.2.1 hx)), }}},
  { simp,
    intros x hx,
    have h1 : x ∈ clase R x := h.1 x,
    rw ← hx at h1,
    exact set.not_mem_empty x h1, },
end

-- 3ª demostración
example
  (h : equivalence R)
  : particion {a : set X | ∃ s : X, a = clase R s} :=
begin
  split,
  { simp,
    intro y,
    use [clase R y,
         ⟨by use y,
          ⟨h.1 y, λ x hx, le_antisymm (aux h hx) (aux h (h.2.1 hx))⟩⟩], },
  { simp,
    intros x hx,
    have h1 : x ∈ clase R x := h.1 x,
    rw ← hx at h1,
    exact set.not_mem_empty x h1, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/El_conjunto_de_las_clases_de_equivalencia_es_una_particion.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory El_conjunto_de_las_clases_de_equivalencia_es_una_particion
imports Main
begin

definition clase :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a set"
  where "clase R x = {y. R x y}"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

lemma
  fixes   R :: "'a ⇒ 'a ⇒ bool"
  assumes "equivp R"
  shows   "particion (⋃x. {clase R x})" (is "particion ?P")
proof (unfold particion_def; intro conjI)
  show "(∀x. ∃B∈?P. x ∈ B ∧ (∀C∈?P. x ∈ C ⟶ B = C))"
  proof (intro allI)
    fix x
    have "clase R x ∈ ?P"
      by auto
    moreover have "x ∈ clase R x"
      using assms clase_def equivp_def
      by (metis CollectI)
    moreover have "∀C∈?P. x ∈ C ⟶ clase R x = C"
    proof
      fix C
      assume "C ∈ ?P"
      then obtain y where "C = clase R y"
        by auto
      show "x ∈ C ⟶ clase R x = C"
      proof
        assume "x ∈ C"
        then have "R y x"
          using ‹C = clase R y› assms clase_def
          by (metis CollectD)
        then show "clase R x = C"
          using assms ‹C = clase R y› clase_def equivp_def
          by metis
      qed
    qed
    ultimately show "∃B∈?P. x ∈ B ∧ (∀C∈?P. x ∈ C ⟶ B = C)"
      by blast
  qed
next
  show "{} ∉ ?P"
  proof
    assume "{} ∈ ?P"
    then obtain x where "{} = clase R x"
      by auto
    moreover have "x ∈ clase R x"
      using assms clase_def equivp_def
      by (metis CollectI)
    ultimately show False
      by simp
  qed
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
