---
Título: Un número es par si y solo si lo es su cuadrado
Autor:  José A. Alonso
---

Demostrar que un número es par si y solo si lo es su cuadrado.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.int.parity
import tactic
open int

variable (n : ℤ)

example :
  even (n^2) ↔ even n :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.int.parity
import tactic
open int

variable (n : ℤ)

-- 1ª demostración
example :
  even (n^2) ↔ even n :=
begin
  split,
  { contrapose,
    rw ← odd_iff_not_even,
    rw ← odd_iff_not_even,
    unfold odd,
    intro h,
    cases h with k hk,
    use 2*k*(k+1),
    rw hk,
    ring, },
  { unfold even,
    intro h,
    cases h with k hk,
    use 2*k^2,
    rw hk,
    ring, },
end

-- 2ª demostración
example :
  even (n^2) ↔ even n :=
begin
  split,
  { contrapose,
    rw ← odd_iff_not_even,
    rw ← odd_iff_not_even,
    rintro ⟨k, rfl⟩,
    use 2*k*(k+1),
    ring, },
  { rintro ⟨k, rfl⟩,
    use 2*k^2,
    ring, },
end

-- 3ª demostración
example :
  even (n^2) ↔ even n :=
iff.intro
  ( have h : ¬even n → ¬even (n^2),
      { assume h1 : ¬even n,
        have h2 : odd n,
          from odd_iff_not_even.mpr h1,
        have h3: odd (n^2), from
          exists.elim h2
            ( assume k,
              assume hk : n = 2*k+1,
              have h4 : n^2 = 2*(2*k*(k+1))+1, from
                calc  n^2
                    = (2*k+1)^2       : by rw hk
                ... = 4*k^2+4*k+1     : by ring
                ... = 2*(2*k*(k+1))+1 : by ring,
              show odd (n^2),
                from exists.intro (2*k*(k+1)) h4),
        show ¬even (n^2),
          from odd_iff_not_even.mp h3 },
    show even (n^2) → even n,
      from not_imp_not.mp h )
  ( assume h1 : even n,
    show even (n^2), from
      exists.elim h1
        ( assume k,
          assume hk : n = 2*k ,
          have h2 : n^2 = 2*(2*k^2), from
            calc  n^2
                = (2*k)^2   : by rw hk
            ... = 2*(2*k^2) : by ring,
          show even (n^2),
            from exists.intro (2*k^2) h2 ))

-- 4ª demostración
example :
  even (n^2) ↔ even n :=
calc even (n^2)
     ↔ even (n * n)      : iff_of_eq (congr_arg even (sq n))
 ... ↔ (even n ∨ even n) : int.even_mul
 ... ↔ even n            : or_self (even n)

-- 5ª demostración
example :
  even (n^2) ↔ even n :=
calc even (n^2)
     ↔ even (n * n)      : by ring_nf
 ... ↔ (even n ∨ even n) : int.even_mul
 ... ↔ even n            : by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Un_numero_es_par_syss_lo_es_su_cuadrado.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Un_numero_es_par_syss_lo_es_su_cuadrado
imports Main
begin

(* 1ª demostración *)
lemma
  fixes n :: int
  shows "even (n²) ⟷ even n"
proof (rule iffI)
  assume "even (n²)"
  show "even n"
  proof (rule ccontr)
    assume "odd n"
    then obtain k where "n = 2*k+1"
      by (rule oddE)
    then have "n² = 2*(2*k*(k+1))+1"
    proof -
      have "n² = (2*k+1)²"
        by (simp add: ‹n = 2 * k + 1›)
      also have "… = 4*k²+4*k+1"
        by algebra
      also have "… = 2*(2*k*(k+1))+1"
        by algebra
      finally show "n² = 2*(2*k*(k+1))+1" .
    qed
    then have "∃k'. n² = 2*k'+1"
      by (rule exI)
    then have "odd (n²)"
      by fastforce
    then show False
      using ‹even (n²)› by blast
  qed
next
  assume "even n"
  then obtain k where "n = 2*k"
    by (rule evenE)
  then have "n² = 2*(2*k²)"
    by simp
  then show "even (n²)"
    by simp
qed

(* 2ª demostración *)
lemma
  fixes n :: int
  shows "even (n²) ⟷ even n"
proof
  assume "even (n²)"
  show "even n"
  proof (rule ccontr)
    assume "odd n"
    then obtain k where "n = 2*k+1"
      by (rule oddE)
    then have "n² = 2*(2*k*(k+1))+1"
      by algebra
    then have "odd (n²)"
      by simp
    then show False
      using ‹even (n²)› by blast
  qed
next
  assume "even n"
  then obtain k where "n = 2*k"
    by (rule evenE)
  then have "n² = 2*(2*k²)"
    by simp
  then show "even (n²)"
    by simp
qed

(* 3ª demostración *)
lemma
  fixes n :: int
  shows "even (n²) ⟷ even n"
proof -
  have "even (n²) = (even n ∧ (0::nat) < 2)"
    by (simp only: even_power)
  also have "… = (even n ∧ True)"
    by (simp only: less_numeral_simps)
  also have "… = even n"
    by (simp only: HOL.simp_thms(21))
  finally show "even (n²) ⟷ even n"
    by this
qed

(* 4ª demostración *)
lemma
  fixes n :: int
  shows "even (n²) ⟷ even n"
proof -
  have "even (n²) = (even n ∧ (0::nat) < 2)"
    by (simp only: even_power)
  also have "… = even n"
    by simp
  finally show "even (n²) ⟷ even n" .
qed

(* 5ª demostración *)
lemma
  fixes n :: int
  shows "even (n²) ⟷ even n"
  by simp

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
