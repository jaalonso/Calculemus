theory La_dama_o_el_tigre
imports Main
begin

(* 1\<ordfeminine> demostración *)
lemma
  assumes "c1 \<longleftrightarrow> dp \<and> ts"
    "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
    "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
  shows "ds"
  using assms
  by auto

(* 2\<ordfeminine> demostración *)
lemma
  assumes "c1 \<longleftrightarrow> dp \<and> ts"
    "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
    "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
  shows "ds"
proof -
  note \<open>(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)\<close>
  then show "ds"
  proof 
    assume "c1 \<and> \<not> c2"
    then have "c1" ..
    with \<open>c1 \<longleftrightarrow> dp \<and> ts\<close> have "dp \<and> ts" .. 
    then have "(dp \<and> ts) \<or> (ds \<and> tp)" ..
    with assms(2) have "c2" ..
    have "\<not> c2" using \<open>c1 \<and> \<not> c2\<close> ..
    then show "ds" using \<open>c2\<close> ..
  next
    assume "c2 \<and> \<not> c1"
    then have "c2" ..
    with assms(2) have "(dp \<and> ts) \<or> (ds \<and> tp)" ..
    then show "ds"
    proof
      assume "dp \<and> ts"
      with assms(1) have c1 ..
      have "\<not> c1" using \<open>c2 \<and> \<not> c1\<close> ..
      then show ds using \<open>c1\<close> ..
    next
      assume "ds \<and> tp"
      then show ds ..
    qed
  qed
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "c1 \<longleftrightarrow> dp \<and> ts"
    "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
    "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
  shows "ds"
proof -
  note \<open>(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)\<close>
  then show "ds"
  proof (rule disjE)
    assume "c1 \<and> \<not> c2"
    then have "c1" by (rule conjunct1)
    with \<open>c1 \<longleftrightarrow> dp \<and> ts\<close> have "dp \<and> ts" by (rule iffD1) 
    then have "(dp \<and> ts) \<or> (ds \<and> tp)" by (rule disjI1)
    with assms(2) have "c2" by (rule iffD2)
    have "\<not> c2" using \<open>c1 \<and> \<not> c2\<close> by (rule conjunct2)
    then show "ds" using \<open>c2\<close> by (rule notE)
  next
    assume "c2 \<and> \<not> c1"
    then have "c2" by (rule conjunct1)
    with assms(2) have "(dp \<and> ts) \<or> (ds \<and> tp)" by (rule iffD1)
    then show "ds"
    proof (rule disjE)
      assume "dp \<and> ts"
      with assms(1) have c1 by (rule iffD2)
      have "\<not> c1" using \<open>c2 \<and> \<not> c1\<close> by (rule conjunct2)
      then show ds using \<open>c1\<close> by (rule notE)
    next
      assume "ds \<and> tp"
      then show ds by (rule conjunct1)
    qed
  qed
qed

section \<open>enrniecar\<close>

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
  by auto

lemma ejercicio_46:
  "\<lbrakk>\<not>(p \<or> q)\<rbrakk> \<Longrightarrow> \<not>p \<and> \<not>q"
  apply (rule conjI)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply (erule notnotD)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply (erule notnotD)
  done

lemma retosemanal1:
  assumes "c1 \<longleftrightarrow> dp \<and> ts"
          "c2 \<longleftrightarrow> (dp \<and> ts) \<or> (ds \<and> tp)"
          "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)"
  shows   "ds"
proof - 
  have "c2 \<and> \<not> c1" 
  proof (rule disjE)
    show "(c1 \<and> \<not> c2) \<or> (c2 \<and> \<not> c1)" using assms(3) by this
  next
    assume "c1 \<and> \<not> c2"
    then have "c1" by (rule conjunct1)
    with assms(1) have "dp \<and> ts" by (rule iffD1)
    have "\<not> c2" using \<open>c1 \<and> \<not> c2\<close> by (rule conjunct2)
    have "(dp \<and> ts) \<or> (ds \<and> tp) \<longrightarrow> c2" 
    proof (rule impI)
      assume "(dp \<and> ts) \<or> (ds \<and> tp)"
      with assms(2) show "c2" by (rule iffD2)
    qed
    then have "\<not> ((dp \<and> ts) \<or> (ds \<and> tp))" using \<open>\<not> c2\<close> by (rule mt)
    then have "\<not> (dp \<and> ts) \<and> \<not>(ds \<and> tp)" by (rule ejercicio_46)
    then have "\<not> (dp \<and> ts)" by (rule conjunct1)
    then  have False using \<open>dp \<and> ts\<close> by (rule notE)
    then show "c2 \<and> \<not> c1" by (rule FalseE)
  next
    assume "c2 \<and> \<not> c1"
    then show "c2 \<and> \<not> c1" by this
  qed
  then have "c2" by (rule conjunct1)
  with assms(2) have "(dp \<and> ts) \<or> (ds \<and> tp)" by (rule iffD1)
  have "dp \<and> ts \<longrightarrow> c1"
  proof (rule impI)
    assume "dp \<and> ts"
    with assms(1) show "c1" by (rule iffD2)
  qed
  have " \<not> c1" using \<open>c2 \<and> \<not> c1\<close> by (rule conjunct2)
  with \<open>dp \<and> ts \<longrightarrow> c1\<close> have "\<not> (dp \<and> ts)" by (rule mt)
  show "ds"
  proof (rule disjE)
    show "(dp \<and> ts) \<or> (ds \<and> tp)" using \<open>(dp \<and> ts) \<or> (ds \<and> tp)\<close> by this
  next
    assume "dp \<and> ts"
    with \<open>\<not> (dp \<and> ts)\<close> have False by (rule notE)
    then show "ds" by (rule FalseE)
  next
    assume "ds \<and> tp"
    then show "ds" by (rule conjunct1)
  qed
qed

end