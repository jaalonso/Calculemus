---
Título: Teorema del emparedado
Autor:  José A. Alonso
---

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

Se define que a es el límite de la sucesión u, por
<pre lang="text">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
   λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
</pre>
donde se usa la notación |x| para el valor absoluto de x
<pre lang="text">
   notation `|`x`|` := abs x
</pre>

Demostrar el [teorema del emparedado](https://bit.ly/3eqlZ0b); es decir, que si para todo n, u(n) ≤ v(n) ≤ w(n) y u(n) tienen el mismo límite, entonces v(n) también tiene dicho límite.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (u v w : ℕ → ℝ)
variable  (a : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

example
  (hu : limite u a)
  (hw : limite w a)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n) :
  limite v a :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables (u v w : ℕ → ℝ)
variable  (a : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- Nota. En la demostración se usará el siguiente lema:
lemma max_ge_iff
  {p q r : ℕ}
  : r ≥ max p q ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hw : limite w a)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n) :
  limite v a :=
begin
  intros ε hε,
  cases hu ε hε with N hN, clear hu,
  cases hw ε hε with N' hN', clear hw hε,
  use max N N',
  intros n hn,
  rw max_ge_iff at hn,
  specialize hN n hn.1,
  specialize hN' n hn.2,
  specialize h n,
  specialize h' n,
  clear hn,
  rw abs_le at *,
  split,
  { calc -ε
         ≤ u n - a : hN.1
     ... ≤ v n - a : by linarith, },
  { calc v n - a
         ≤ w n - a : by linarith
     ... ≤ ε       : hN'.2, },
end

-- 2ª demostración
example
  (hu : limite u a)
  (hw : limite w a)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n) :
  limite v a :=
begin
  intros ε hε,
  cases hu ε hε with N hN, clear hu,
  cases hw ε hε with N' hN', clear hw hε,
  use max N N',
  intros n hn,
  rw max_ge_iff at hn,
  specialize hN n (by linarith),
  specialize hN' n (by linarith),
  specialize h n,
  specialize h' n,
  rw abs_le at *,
  split,
  { linarith, },
  { linarith, },
end

-- 3ª demostración
example
  (hu : limite u a)
  (hw : limite w a)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n) :
  limite v a :=
begin
  intros ε hε,
  cases hu ε hε with N hN, clear hu,
  cases hw ε hε with N' hN', clear hw hε,
  use max N N',
  intros n hn,
  rw max_ge_iff at hn,
  specialize hN n (by linarith),
  specialize hN' n (by linarith),
  specialize h n,
  specialize h' n,
  rw abs_le at *,
  split ; linarith,
end

-- 4ª demostración
example
  (hu : limite u a)
  (hw : limite w a)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n) :
  limite v a :=
assume ε,
assume hε : ε > 0,
exists.elim (hu ε hε)
  ( assume N,
    assume hN : ∀ (n : ℕ), n ≥ N → |u n - a| ≤ ε,
    exists.elim (hw ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |w n - a| ≤ ε,
        show ∃ N, ∀ n, n ≥ N → |v n - a| ≤ ε, from
          exists.intro (max N N')
            ( assume n,
              assume hn : n ≥ max N N',
              have h1 : n ≥ N ∧ n ≥ N',
                from max_ge_iff.mp hn,
              have h2 : -ε ≤ v n - a,
                { have h2a : |u n - a| ≤ ε,
                    from hN n h1.1,
                  calc -ε
                       ≤ u n - a : and.left (abs_le.mp h2a)
                   ... ≤ v n - a : by linarith [h n], },
              have h3 : v n - a ≤ ε,
                { have h3a : |w n - a| ≤ ε,
                    from hN' n h1.2,
                  calc v n - a
                       ≤ w n - a : by linarith [h' n]
                   ... ≤ ε       : and.right (abs_le.mp h3a), },
              show |v n - a| ≤ ε,
                from abs_le.mpr (and.intro h2 h3))))
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Teorema_del_emparedado.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Teorema_del_emparedado
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma
  assumes "limite u a"
          "limite w a"
          "∀n. u n ≤ v n"
          "∀n. v n ≤ w n"
  shows   "limite v a"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume hε : "0 < ε"
  obtain N where hN : "∀n≥N. ¦u n - a¦ < ε"
    using assms(1) hε limite_def
    by auto
  obtain N' where hN' : "∀n≥N'. ¦w n - a¦ < ε"
    using assms(2) hε limite_def
    by auto
  have "∀n≥max N N'. ¦v n - a¦ < ε"
  proof (intro allI impI)
    fix n
    assume hn : "n≥max N N'"
    have "v n - a < ε"
    proof -
      have "v n - a ≤ w n - a"
        using assms(4) by simp
      also have "… ≤ ¦w n - a¦"
        by simp
      also have "… < ε"
        using hN' hn by auto
      finally show "v n - a < ε" .
    qed
    moreover
    have "-(v n - a) < ε"
    proof -
      have "-(v n - a) ≤ -(u n - a)"
        using assms(3) by auto
      also have "… ≤ ¦u n - a¦"
        by simp
      also have "… < ε"
        using hN hn by auto
      finally show "-(v n - a) < ε" .
    qed
    ultimately show "¦v n - a¦ < ε"
      by (simp only: abs_less_iff)
  qed
  then show "∃k. ∀n≥k. ¦v n - a¦ < ε"
    by (rule exI)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
