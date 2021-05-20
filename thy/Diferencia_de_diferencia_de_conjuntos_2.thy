(* Diferencia_de_diferencia_de_conjuntos_2.lean
   2\<ordfeminine> diferencia de diferencia de conjuntos.
   José A. Alonso Jiménez
   Sevilla, 21 de mayo de 2021
   ---------------------------------------------------------------------
*)

text \<open>-- ---------------------------------------------------------------
-- Demostrar que
--    s - (t \<union> u) \<subseteq> (s - t) - u
-- --------------------------------------------------------------------\<close>

theory Diferencia_de_diferencia_de_conjuntos_2
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "s - (t \<union> u) \<subseteq> (s - t) - u"
proof (rule subsetI)
  fix x
  assume "x \<in> s - (t \<union> u)"
  then show "x \<in> (s - t) - u" 
  proof (rule DiffE)
    assume "x \<in> s"
    assume "x \<notin> t \<union> u"
    have "x \<notin> u" 
    proof (rule notI)
      assume "x \<in> u"
      then have "x \<in> t \<union> u" 
        by (simp only: UnI2)
      with \<open>x \<notin> t \<union> u\<close> show False
        by (rule notE)
    qed 
    have "x \<notin> t" 
    proof (rule notI)
      assume "x \<in> t"
      then have "x \<in> t \<union> u" 
        by (simp only: UnI1)
      with \<open>x \<notin> t \<union> u\<close> show False
        by (rule notE)
    qed 
    with \<open>x \<in> s\<close> have "x \<in> s - t" 
      by (rule DiffI)
    then show "x \<in> (s - t) - u" 
      using \<open>x \<notin> u\<close> by (rule DiffI)  
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma "s - (t \<union> u) \<subseteq> (s - t) - u"
proof 
  fix x
  assume "x \<in> s - (t \<union> u)"
  then show "x \<in> (s - t) - u" 
  proof 
    assume "x \<in> s"
    assume "x \<notin> t \<union> u"
    have "x \<notin> u" 
    proof 
      assume "x \<in> u"
      then have "x \<in> t \<union> u" 
        by simp
      with \<open>x \<notin> t \<union> u\<close> show False
        by simp
    qed 
    have "x \<notin> t" 
    proof 
      assume "x \<in> t"
      then have "x \<in> t \<union> u" 
        by simp
      with \<open>x \<notin> t \<union> u\<close> show False
        by simp
    qed 
    with \<open>x \<in> s\<close> have "x \<in> s - t" 
      by simp
    then show "x \<in> (s - t) - u" 
      using \<open>x \<notin> u\<close> by simp  
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma "s - (t \<union> u) \<subseteq> (s - t) - u"
proof 
  fix x
  assume "x \<in> s - (t \<union> u)"
  then show "x \<in> (s - t) - u" 
  proof 
    assume "x \<in> s"
    assume "x \<notin> t \<union> u"
    then have "x \<notin> u" 
      by simp 
    have "x \<notin> t" 
      using \<open>x \<notin> t \<union> u\<close> by simp
    with \<open>x \<in> s\<close> have "x \<in> s - t" 
      by simp
    then show "x \<in> (s - t) - u" 
      using \<open>x \<notin> u\<close> by simp  
  qed
qed

(* 4\<ordfeminine> demostración *)
lemma "s - (t \<union> u) \<subseteq> (s - t) - u"
proof 
  fix x
  assume "x \<in> s - (t \<union> u)"
  then show "x \<in> (s - t) - u" 
  proof 
    assume "x \<in> s"
    assume "x \<notin> t \<union> u"
    then show "x \<in> (s - t) - u" 
      using \<open>x \<in> s\<close> by simp  
  qed
qed

(* 5\<ordfeminine> demostración *)
lemma "s - (t \<union> u) \<subseteq> (s - t) - u"
proof 
  fix x
  assume "x \<in> s - (t \<union> u)"
  then show "x \<in> (s - t) - u" 
    by simp  
qed

(* 6\<ordfeminine> demostración *)
lemma "s - (t \<union> u) \<subseteq> (s - t) - u"
by auto

end
