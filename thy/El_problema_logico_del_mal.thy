theory El_problema_logico_del_mal
imports Main
begin

lemma notnotI: "P \<Longrightarrow> \<not>\<not>P"
  by simp

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
  by simp

lemma
  assumes "C \<and> Q \<longrightarrow> P" 
          "\<not>C \<longrightarrow> \<not>Op" 
          "\<not>Q \<longrightarrow> M" 
          "\<not>P"  
          "E \<longrightarrow> Op \<and> \<not>M"
  shows  "\<not>E"
proof (rule notI)
  assume "E"
  with \<open>E \<longrightarrow> Op \<and> \<not>M\<close> have "Op \<and> \<not>M" by (rule mp)
  then have "Op" by (rule conjunct1)
  then have "\<not>\<not>Op" by (rule notnotI)
  with \<open>\<not>C \<longrightarrow> \<not>Op\<close> have "\<not>\<not>C" by (rule mt) 
  then have "C" by (rule notnotD)
  moreover
  have "\<not>M" using \<open>Op \<and> \<not>M\<close> by (rule conjunct2)
  with \<open>\<not>Q \<longrightarrow> M\<close> have "\<not>\<not>Q" by (rule mt)
  then have "Q" by (rule notnotD)
  ultimately have "C \<and> Q" by (rule conjI)
  with \<open>C \<and> Q \<longrightarrow> P\<close> have "P" by (rule mp)
  with \<open>\<not>P\<close> show False by (rule notE)
qed

end
