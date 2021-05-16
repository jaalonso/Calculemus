theory Praeclarum_theorema
imports Main
begin

(* 1\<ordfeminine> demostración: automática *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  by simp

(* 2\<ordfeminine> demostración: aplicativa *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

(* 3\<ordfeminine> demostración: estructurada *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof
  assume "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof
    assume "p \<and> r"
    show "q \<and> s"
    proof
      have "p \<longrightarrow> q" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> ..
      moreover have "p" using \<open>p \<and> r\<close> ..
      ultimately show "q" ..
    next
      have "r \<longrightarrow> s" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> ..
      moreover have "r" using \<open>p \<and> r\<close> ..
      ultimately show "s" ..   
    qed
  qed
qed

(* 4\<ordfeminine> demostración: detallada *)
lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof (rule impI)
  assume "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof (rule impI)
    assume "p \<and> r"
    show "q \<and> s"
    proof (rule conjI)
      have "p \<longrightarrow> q" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> by (rule conjunct1)
      moreover have "p" using \<open>p \<and> r\<close> by (rule conjunct1)
      ultimately show "q" by (rule mp)
    next
      have "r \<longrightarrow> s" using \<open>(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)\<close> by (rule conjunct2)
      moreover have "r" using \<open>p \<and> r\<close> by (rule conjunct2)
      ultimately show "s" by (rule mp)
    qed
  qed
qed

section \<open>Soluciones de alumnos\<close>

subsection \<open>juanarcon\<close>

lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof (rule impI)
  assume 1: "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  have 2: "p \<longrightarrow> q" using 1 by (rule conjunct1)
  have 3: "r \<longrightarrow> s" using 1 by (rule conjunct2)
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof (rule impI)
    assume 4: "p \<and> r"
    have "p" using 4 by (rule conjunct1)
    have "q" using 2 `p` by (rule mp)
    have "r" using 4 by (rule conjunct2)
    have "s" using 3 `r` by (rule mp)
    show "q \<and> s" using `q` `s` by (rule conjI)
  qed
qed

subsection \<open>manmilinf\<close>

lemma P_th:
  "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  apply (rule)
  apply (erule conjE)
  apply (rule)+
   apply (erule mp)
   apply (erule conjunct1)
  apply (erule mp)
  apply (erule conjunct2)
  done

subsection \<open>inehenluq\<close>

lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
proof (rule impI)
  assume 1: "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s)"
  have 2: "p \<longrightarrow> q" using 1 by (rule conjunct1)
  have 3: "r \<longrightarrow> s" using 1 by (rule conjunct2)
  show "(p \<and> r) \<longrightarrow> (q \<and> s)"
  proof (rule impI)
    assume 4: "(p \<and> r)"
    have 5: "p" using 4 by (rule conjunct1)
    have 6: "r" using 4 by (rule conjunct2)
    have 7: "q" using 2 5 by (rule mp)
    have 8: "s" using 3 6 by (rule mp)
    show "q \<and> s" using 7 8 by (rule conjI)
  qed
qed


subsection \<open>antgongar\<close>

lemma "(p \<longrightarrow> q) \<and> (r \<longrightarrow> s) \<longrightarrow> ((p \<and> r) \<longrightarrow> (q \<and> s))"
  by auto

end
