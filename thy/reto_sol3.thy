theory reto_sol3
imports Main
begin

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

end