---
Título: Propiedad de la densidad de los reales
Autor:  José A. Alonso
---

Sean x, y números reales tales que
<pre lang="text">
   ∀ z, y < z → x ≤ z
</pre>
Demostrar que x ≤ y.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables {x y : ℝ}

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables {x y : ℝ}

-- 1ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  apply (lt_irrefl a),
  calc a
       < x : ha.2
   ... ≤ a : h a ha.1,
end

-- 2ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  apply (lt_irrefl a),
  exact lt_of_lt_of_le ha.2 (h a ha.1),
end

-- 3ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1)),
end

-- 3ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  rcases (exists_between hxy) with ⟨a, ha⟩,
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1)),
end

-- 4ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  rcases (exists_between hxy) with ⟨a, hya, hax⟩,
  exact (lt_irrefl a) (lt_of_lt_of_le hax (h a hya)),
end

-- 5ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_not_gt (λ hxy,
  let ⟨a, hya, hax⟩ := exists_between hxy in
  lt_irrefl a (lt_of_lt_of_le hax (h a hya)))

-- 6ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_forall_le_of_dense h
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_de_la_densidad_de_los_reales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Propiedad_de_la_densidad_de_los_reales
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes x y :: real
  assumes "∀ z. y < z ⟶ x ≤ z"
  shows "x ≤ y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "∃z. y < z ∧ z < x"
    by (rule dense)
  then obtain a where ha : "y < a ∧ a < x"
    by (rule exE)
  have "¬ a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
  proof -
    have "y < a ⟶ x ≤ a"
      using assms by (rule allE)
    moreover
    have "y < a"
      using ha by (rule conjunct1)
    ultimately have "x ≤ a"
      by (rule mp)
    moreover
    have "a < x"
      using ha by (rule conjunct2)
    ultimately show "a < a"
      by (simp only: less_le_trans)
  qed
  ultimately show False
    by (rule notE)
qed

(* 2ª demostración *)
lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "∃z. y < z ∧ z < x"
    by (rule dense)
  then obtain a where hya : "y < a" and hax : "a < x"
    by auto
  have "¬ a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
  proof -
    have "a < x"
      using hax .
    also have "… ≤ a"
      using assms[OF hya] .
    finally show "a < a" .
  qed
  ultimately show False
    by (rule notE)
qed

(* 3ª demostración *)
lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
proof (rule linorder_class.leI; intro notI)
  assume "y < x"
  then have "∃z. y < z ∧ z < x"
    by (rule dense)
  then obtain a where hya : "y < a" and hax : "a < x"
    by auto
  have "¬ a < a"
    by (rule order.irrefl)
  moreover
  have "a < a"
    using hax assms[OF hya] by (rule less_le_trans)
  ultimately show False
    by (rule notE)
qed

(* 4ª demostración *)
lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
by (meson assms dense not_less)

(* 5ª demostración *)
lemma
  fixes x y :: real
  assumes "⋀ z. y < z ⟹ x ≤ z"
  shows "x ≤ y"
using assms by (rule dense_ge)

(* 6ª demostración *)
lemma
  fixes x y :: real
  assumes "∀ z. y < z ⟶ x ≤ z"
  shows "x ≤ y"
using assms by (simp only: dense_ge)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
