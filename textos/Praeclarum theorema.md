# Praeclarum theorema

Demostrar el [Praeclarum theorema](http://bit.ly/2S9IYBX) de Leibniz:

<pre lang="isar">
theory Praeclarum_theorema
imports Main
begin

lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  oops
  
end
</pre>

<h4>Soluciones</h4>

Puedes escribir tus soluciones en los comentarios (con el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;) o ver las soluciones propuestas pulsando [expand title="aquí"]

<h4>Soluciones con Isabelle/HOL</h4>

<pre lang="isar">
theory Praeclarum_theorema
imports Main
begin

(* 1ª demostración: automática *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  by simp

(* 2ª demostración: aplicativa *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

(* 3ª demostración: estructurada *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
proof
  assume "(p ⟶ q) ∧ (r ⟶ s)"
  show "(p ∧ r) ⟶ (q ∧ s)"
  proof
    assume "p ∧ r"
    show "q ∧ s"
    proof
      have "p ⟶ q" using ‹(p ⟶ q) ∧ (r ⟶ s)› ..
      moreover have "p" using ‹p ∧ r› ..
      ultimately show "q" ..
    next
      have "r ⟶ s" using ‹(p ⟶ q) ∧ (r ⟶ s)› ..
      moreover have "r" using ‹p ∧ r› ..
      ultimately show "s" ..   
    qed
  qed
qed

(* 4ª demostración: detallada *)
lemma "(p ⟶ q) ∧ (r ⟶ s) ⟶ ((p ∧ r) ⟶ (q ∧ s))"
proof (rule impI)
  assume "(p ⟶ q) ∧ (r ⟶ s)"
  show "(p ∧ r) ⟶ (q ∧ s)"
  proof (rule impI)
    assume "p ∧ r"
    show "q ∧ s"
    proof (rule conjI)
      have "p ⟶ q" using ‹(p ⟶ q) ∧ (r ⟶ s)› by (rule conjunct1)
      moreover have "p" using ‹p ∧ r› by (rule conjunct1)
      ultimately show "q" by (rule mp)
    next
      have "r ⟶ s" using ‹(p ⟶ q) ∧ (r ⟶ s)› by (rule conjunct2)
      moreover have "r" using ‹p ∧ r› by (rule conjunct2)
      ultimately show "s" by (rule mp)
    qed
  qed
qed

end
</pre>
[/expand]

