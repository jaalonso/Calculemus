theory reto

imports Main
begin

(* 1\<ordfeminine> solución *)

lemma "\<forall>(f :: bool \<Rightarrow> bool). f (f (f b)) = f b"
  by smt

(* 2\<ordfeminine> solución *)

lemma 
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b"
  by smt

(* 3\<ordfeminine> solución *)

lemma
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b"
  by (cases b; cases "f True"; cases "f False"; simp)

(* 4\<ordfeminine> solución *)

lemma
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b"
proof (cases "f True"; cases "f False"; cases b)
  assume "f True" "f False" "b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using \<open>f True\<close> by simp 
next
  assume "f True" "f False" "\<not> b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using \<open>f True\<close> \<open>f False\<close> \<open>\<not> b\<close> by simp 
next
  assume "f True" "\<not> f False" "b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using \<open>f True\<close> \<open>\<not> f False\<close> \<open>b\<close> by simp 
next
  assume "f True" "\<not> f False" "\<not> b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using \<open>f True\<close> \<open>\<not> f False\<close> \<open>\<not> b\<close> by simp 
next 
  assume "\<not> f True" "f False" "b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using \<open>\<not> f True\<close> \<open>f False\<close> \<open>b\<close> by simp 
next
  assume "\<not> f True" "f False" "\<not> b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using \<open>\<not> f True\<close> \<open>f False\<close> \<open>\<not> b\<close> by simp 
next
  assume "\<not> f True" "\<not> f False" "b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using \<open>\<not> f True\<close> \<open>\<not> f False\<close> \<open>b\<close> by simp 
next
  assume "\<not> f True" "\<not> f False" "\<not> b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using \<open>\<not> f True\<close> \<open>\<not> f False\<close> \<open>\<not>b\<close> by simp 
qed

(* 5\<ordfeminine> solución *)

lemma
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b"
proof (cases "f True"; cases "f False"; cases b)
  assume "f True" "f False" "b"
  have "f (f (f b)) = f (f (f True))" using \<open>b\<close> by simp
  also have "\<dots> = f (f True)" using \<open>f True\<close> by simp
  also have "\<dots> = f True" using \<open>f True\<close> by simp
  also have "\<dots> = f b" using \<open>b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "f True" "f False" "\<not> b"
  have "f (f (f b)) = f (f (f False))" using \<open>\<not>b\<close> by simp
  also have "\<dots> = f (f True)" using \<open>f False\<close> by simp
  also have "\<dots> = f True" using \<open>f True\<close> by simp
  also have "\<dots> = f False" using \<open>f True\<close> \<open>f False\<close> by simp
  also have "\<dots> = f b" using \<open>\<not> b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "f True" "\<not> f False" "b"
  have "f (f (f b)) = f (f (f True))" using \<open>b\<close> by simp
  also have "\<dots> = f (f True)" using \<open>f True\<close> by simp
  also have "\<dots> = f True" using \<open>f True\<close> by simp
  also have "\<dots> = f b" using \<open>b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "f True" "\<not> f False" "\<not> b"
  have "f (f (f b)) = f (f (f False))" using \<open>\<not>b\<close> by simp
  also have "\<dots> = f (f False)" using \<open>\<not> f False\<close> by simp
  also have "\<dots> = f False" using \<open>\<not> f False\<close> by simp
  also have "\<dots> = f b" using \<open>\<not> b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
next 
  assume "\<not> f True" "f False" "b"
  have "f (f (f b)) = f (f (f True))" using \<open>b\<close> by simp
  also have "\<dots> = f (f False)" using \<open>\<not> f True\<close> by simp
  also have "\<dots> = f True" using \<open>f False\<close> by simp
  also have "\<dots> = f b" using \<open>b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "\<not> f True" "f False" "\<not> b"
  have "f (f (f b)) = f (f (f False))" using \<open>\<not>b\<close> by simp
  also have "\<dots> = f (f True)" using \<open>f False\<close> by simp
  also have "\<dots> = f False" using \<open>\<not> f True\<close> by simp
  also have "\<dots> = f b" using \<open>\<not> b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "\<not> f True" "\<not> f False" "b"
  have "f (f (f b)) = f (f (f True))" using \<open>b\<close> by simp
  also have "\<dots> = f (f False)" using \<open>\<not> f True\<close> by simp
  also have "\<dots> = f False" using \<open>\<not> f False\<close> by simp
  also have "\<dots> = False" using \<open>\<not> f False\<close> by simp
  also have "\<dots> = f True" using \<open>\<not> f True\<close> by simp
  also have "\<dots> = f b" using \<open>b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "\<not> f True" "\<not> f False" "\<not> b"
  have "f (f (f b)) = f (f (f False))" using \<open>\<not>b\<close> by simp
  also have "\<dots> = f (f False)" using \<open>\<not> f False\<close> by simp
  also have "\<dots> = f False" using \<open>\<not> f False\<close> by simp
  also have "\<dots> = f b" using \<open>\<not> b\<close> by simp
  finally show "f (f (f b)) = f b" by this 
qed

(* 6\<ordfeminine> solución *)

theorem
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b" 
proof (cases b)
  assume b: b
  show ?thesis
  proof (cases "f True")
    assume ft: "f True"
    show ?thesis
      using b ft by auto
  next
    assume ft: "\<not> f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "\<not> f False"
      show ?thesis
        using b ft ff by auto
    qed
  qed
next
  assume b: "\<not> b"
  show ?thesis
  proof (cases "f True")
    assume ft: "f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "\<not> f False"
      show ?thesis
        using b ft ff by auto
    qed
  next
    assume ft: "\<not> f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "\<not> f False"
      show ?thesis
        using b ft ff by auto
    qed
  qed
qed

(* 7\<ordfeminine> solución *)

theorem
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b"
  by (cases b "f True" "f False"
      rule: bool.exhaust [ case_product bool.exhaust
                         , case_product bool.exhaust])
    auto

end
