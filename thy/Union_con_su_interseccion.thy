(* Union_con_su_interseccion.thy
   Unión con su intersección
   José A. Alonso Jiménez
   Sevilla, 26 de mayo de 2021
  ---------------------------------------------------------------------
*)

text \<open>-- ---------------------------------------------------------------
  Demostrar que
     s \<union> (s \<inter> t) = s
-- --------------------------------------------------------------------\<close>

theory Union_con_su_interseccion
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma "s \<union> (s \<inter> t) = s"
proof (rule equalityI)
  show "s \<union> (s \<inter> t) \<subseteq> s" 
  proof (rule subsetI)
    fix x
    assume "x \<in> s \<union> (s \<inter> t)"
    then show "x \<in> s"
    proof
      assume "x \<in> s"
      then show "x \<in> s"
        by this
    next
      assume "x \<in> s \<inter> t"
      then show "x \<in> s"
        by (simp only: IntD1)
    qed
  qed 
next
  show "s \<subseteq> s \<union> (s \<inter> t)" 
  proof (rule subsetI)
    fix x
    assume "x \<in> s" 
    then show "x \<in> s \<union> (s \<inter> t)"
      by (simp only: UnI1)
  qed 
qed

(* 2\<ordfeminine> demostración *)
lemma "s \<union> (s \<inter> t) = s"
proof
  show "s \<union> s \<inter> t \<subseteq> s" 
  proof
    fix x
    assume "x \<in> s \<union> (s \<inter> t)"
    then show "x \<in> s"
    proof
      assume "x \<in> s"
      then show "x \<in> s"
        by this
    next
      assume "x \<in> s \<inter> t"
      then show "x \<in> s"
        by simp
    qed
  qed 
next
  show "s \<subseteq> s \<union> (s \<inter> t)" 
  proof
    fix x
    assume "x \<in> s" 
    then show "x \<in> s \<union> (s \<inter> t)"
      by simp
  qed 
qed

(* 3\<ordfeminine> demostración *)
lemma "s \<union> (s \<inter> t) = s"
  by auto

end