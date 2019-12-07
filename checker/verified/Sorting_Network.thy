theory Sorting_Network
  imports Main Sorting_Network_Bound "HOL-Library.Permutations" "HOL-Library.Multiset" "Huffman"
begin

lemma bool_min_is_conj[simp]: \<open>min a b = (a \<and> b)\<close>
  unfolding min_def by auto

lemma bool_max_is_disj[simp]: \<open>max a b = (a \<or> b)\<close>
  unfolding max_def by auto

lemma apply_cmp_logic:
  \<open>apply_cmp c v i = (v i \<and> (i \<noteq> fst c \<or> v (snd c)) \<or> (i = snd c \<and> v (fst c)))\<close>
  unfolding apply_cmp_def Let_def case_prod_unfold
  by auto

lemma apply_cmp_swap_or_id:
  \<open>apply_cmp c v = v \<or> apply_cmp c v = Fun.swap (fst c) (snd c) v\<close>
proof (cases \<open>v (fst c) \<and> \<not>v (snd c)\<close>)
  case True
  hence \<open>apply_cmp c v = Fun.swap (fst c) (snd c) v\<close>
    by (simp add: apply_cmp_def case_prod_beta' swap_def)
  thus ?thesis..
next
  case False
  hence \<open>apply_cmp c v = v\<close>
    unfolding apply_cmp_logic
    by blast
  thus ?thesis..
qed

lemma apply_cmp_same_channels:
  \<open>fst c = snd c \<Longrightarrow> apply_cmp c v = v\<close>
  using apply_cmp_swap_or_id by fastforce

lemma apply_cmp_fixed_width_snd_oob:
  assumes \<open>fixed_width_vect n v\<close> \<open>snd c \<ge> n\<close>
  shows \<open>apply_cmp c v = v\<close>
  using assms
  unfolding fixed_width_vect_def apply_cmp_logic
proof (intro impI ext)
  fix i
  assume fixed_width: \<open>\<forall>i\<ge>n. v i = True\<close>
  assume \<open>n \<le> snd c\<close>
  show \<open>(v i \<and> (i \<noteq> fst c \<or> v (snd c)) \<or> i = snd c \<and> v (fst c)) = v i\<close>
  proof (cases \<open>i \<ge> n\<close>)
    case True
    thus ?thesis
      by (simp add: assms(2) fixed_width)
  next
    case False
    thus ?thesis
      using assms(2) fixed_width by blast 
  qed
qed

(***)

definition weight :: \<open>vect \<Rightarrow> nat\<close> where
  \<open>weight v = card (v -` {False})\<close>

lemma \<open>weight (apply_cmp c v) = weight v\<close>
proof (cases \<open>apply_cmp c v = v\<close>)
  case True
  thus ?thesis
    by simp
next
  case False
  hence \<open>apply_cmp c v = Fun.swap (fst c) (snd c) v\<close>
    using apply_cmp_swap_or_id by blast
  hence \<open>apply_cmp c v = v \<circ> Fun.swap (fst c) (snd c) id\<close>
    by (simp add: comp_swap)
  hence \<open>apply_cmp c v -` {False} = (v \<circ> Fun.swap (fst c) (snd c) id) -` {False}\<close>
    by simp
  also have \<open>\<dots> = Fun.swap (fst c) (snd c) id -` v -` {False}\<close>
    by fastforce
  finally show ?thesis
    using card_vimage_inj[of \<open>Fun.swap (fst c) (snd c) id\<close>] weight_def by auto
qed

lemma fixed_width_false_set:
  \<open>fixed_width_vect n v \<Longrightarrow> (v -` {False}) \<subseteq> {..<n}\<close>
  unfolding fixed_width_vect_def
  using leI by blast

lemma fixed_width_weight_bound:
  \<open>fixed_width_vect n v \<Longrightarrow> weight v \<le> n\<close>
  by (metis fixed_width_false_set card_lessThan weight_def card_mono finite_lessThan)

lemma fixed_width_mono_at_weight:
  assumes \<open>fixed_width_vect n v\<close> \<open>mono v\<close> \<open>i = weight v\<close>
  shows \<open>v i = True\<close>
proof (rule ccontr)
  assume \<open>v i \<noteq> True\<close>
  hence \<open>(v -` {False}) \<supseteq> {..i}\<close>
    using assms(2) monoD by fastforce
  hence \<open>weight v > i\<close>
    by (metis Suc_le_eq assms(1) card_atMost card_mono finite_lessThan finite_subset
        fixed_width_false_set weight_def)
  thus False
    using assms(3) by simp
qed

lemma fixed_width_mono_from_weight:
  assumes \<open>fixed_width_vect n v\<close> \<open>mono v\<close>
  shows \<open>v i = (i \<ge> weight v)\<close>
proof (cases \<open>i \<ge> weight v\<close>)
  case True
  thus ?thesis
    by (meson assms(1) assms(2) fixed_width_mono_at_weight le_boolD mono_def) 
next
  case False
  thus ?thesis
    by (metis (full_types) assms(2) fixed_width_vect_def fixed_width_weight_bound le_boolD monoD)
qed

lemma weight_inj_on_fixed_width_mono:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> mono v \<and> fixed_width_vect n v\<close>
  shows \<open>inj_on weight V\<close>
proof (intro inj_onI ext)
  fix v w i assume vw: \<open>v \<in> V\<close> \<open>w \<in> V\<close> \<open>weight v = weight w\<close>
  show \<open>v i = w i\<close>
    by (metis assms fixed_width_mono_from_weight vw)
qed

lemma apply_cmp_fixed_width:
  assumes \<open>fixed_width_vect n v\<close>
  shows \<open>fixed_width_vect (Suc (max n (max (fst c) (snd c)))) (apply_cmp c v)\<close>
  unfolding apply_cmp_logic
  using assms fixed_width_vect_def by auto

lemma apply_cmp_fixed_width_in_bounds:
  assumes \<open>fixed_width_vect n v\<close> \<open>fst c < n\<close> \<open>snd c < n\<close>
  shows \<open>fixed_width_vect n (apply_cmp c v)\<close>
  unfolding apply_cmp_logic
  using assms fixed_width_vect_def by auto

lemma apply_cn_fixed_width:
  \<open>fixed_width_vect n v \<Longrightarrow> \<exists>n'. fixed_width_vect n' (fold apply_cmp cn v)\<close>
proof (induction cn arbitrary: n v)
  case Nil
  thus ?case
    by auto
next
  case (Cons c cn)
  thus ?case
    by (metis apply_cmp_fixed_width fold_simps(2)) 
qed

lemma weight_one:
  \<open>weight ((\<noteq>) i) = 1\<close>
proof -
  have \<open>(\<noteq>) i -` {False} = {i}\<close>
    by (rule set_eqI; auto)
  thus ?thesis
    by (simp add: weight_def)
qed

(***)

definition pls_bound :: \<open>vect set \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>pls_bound V b = (\<forall>cn. inj_on weight (fold apply_cmp cn ` V)  \<longrightarrow> length cn \<ge> b)\<close>

lemma pls_bound_implies_lower_size_bound:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close> \<open>pls_bound V b\<close>
  shows \<open>lower_size_bound V b\<close>
  unfolding lower_size_bound_def
proof (intro allI impI)
  fix cn assume cn_sorts: \<open>\<forall>v \<in> V. mono (fold apply_cmp cn v)\<close>

  have \<open>inj_on weight (fold apply_cmp cn ` V)\<close>
  proof
    fix v w assume v_asm: \<open>v \<in> fold apply_cmp cn ` V\<close>
      and w_asm: \<open>w \<in> fold apply_cmp cn ` V\<close>
      and vw_weight: \<open>weight v = weight w\<close>
    hence \<open>mono v \<and> mono w\<close>
      using cn_sorts by auto

    moreover obtain n_v where \<open>fixed_width_vect n_v v\<close> 
      by (metis v_asm apply_cn_fixed_width assms(1) imageE)
    moreover obtain n_w where \<open>fixed_width_vect n_w w\<close> 
      by (metis w_asm apply_cn_fixed_width assms(1) imageE)
    ultimately have \<open>\<And>i. v i = (i \<ge> weight v)\<close> \<open>\<And>i. w i = (i \<ge> weight w)\<close>
      using fixed_width_mono_from_weight
      by auto
    thus \<open>v = w\<close>
      using vw_weight by auto
  qed
  thus \<open>b \<le> length cn\<close>
    using assms(2) pls_bound_def by blast
qed

lemma trivial_bound: \<open>pls_bound V 0\<close>
  by (simp add: pls_bound_def)

lemma unsorted_bound: \<open>\<not>inj_on weight V \<Longrightarrow> pls_bound V 1\<close>
  using pls_bound_def not_less_eq_eq by fastforce

lemma suc_bound:
  assumes unsorted: \<open>\<not>inj_on weight V\<close> and suc_bounds: \<open>\<And>c. pls_bound (apply_cmp c ` V) b\<close>
  shows \<open>pls_bound V (Suc b)\<close>
proof (subst pls_bound_def; intro allI impI)
  fix cn assume sorts: \<open>inj_on weight (fold apply_cmp cn ` V)\<close>
  from this and unsorted have \<open>cn \<noteq> []\<close>
    using pls_bound_def by auto
  then obtain c cn' where cn_cons: \<open>cn = c # cn'\<close>
    using list.exhaust by blast
  from this and sorts have \<open>inj_on weight (fold apply_cmp cn' ` (apply_cmp c ` V))\<close>
    by (simp add: image_comp)
  from this and suc_bounds have \<open>length cn' \<ge> b\<close>
    using pls_bound_def cn_cons by auto
  thus \<open>length cn \<ge> Suc b\<close>
    using cn_cons by simp
qed

lemma bound_suc:
  assumes \<open>pls_bound V (Suc b)\<close>
  shows \<open>pls_bound (apply_cmp c ` V) b\<close>
  using assms
  unfolding pls_bound_def
  by (metis One_nat_def Suc_eq_plus1 Suc_le_mono fold.simps(2) image_comp list.size(4))

lemma bound_unsorted:
  assumes \<open>pls_bound V 1\<close>
  shows \<open>\<not>inj_on weight V\<close>
  using assms
  unfolding pls_bound_def
  by (metis One_nat_def Suc_n_not_le_n fold.simps(1) id_apply image_subsetI inj_on_subset
      list.size(3))

lemma bound_mono_subset:
  assumes \<open>pls_bound V b\<close> \<open>V \<subseteq> W\<close>
  shows \<open>pls_bound W b\<close>
  using pls_bound_def inj_on_subset image_mono
  by (metis assms)

lemma bound_weaken:
  \<open>pls_bound V (b + d) \<Longrightarrow> pls_bound V b\<close>
  using pls_bound_def by auto

(***)

lemma unsorted_by_card_bound:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close> \<open>card V > n + 1\<close>
  shows \<open>pls_bound V 1\<close>
proof(rule unsorted_bound; rule)
  assume \<open>inj_on weight V\<close>
  hence \<open>card (weight ` V) > n + 1\<close>
    using assms(2) card_image by fastforce
  moreover have \<open>weight ` V \<subseteq> {..n}\<close>
    using assms(1) fixed_width_weight_bound by auto
  hence \<open>card (weight ` V) \<le> n + 1\<close>
    by (metis Suc_eq_plus1 card_atMost card_mono finite_atMost)
  ultimately show False
    by simp
qed

(***)

lemma inj_on_invariant_bij_image:
  assumes \<open>bij g\<close> \<open>\<And>a. f (g a) = f a\<close> 
  shows \<open>inj_on f A = inj_on f (g ` A)\<close>
  by (metis assms bij_betw_def inj_on_image_iff inj_on_subset subset_UNIV)

(***)

definition apply_perm :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> vect \<Rightarrow> vect\<close> where
  \<open>apply_perm p v i = v (p i)\<close>


lemma apply_perm_bij:
  assumes \<open>bij p\<close>
  shows \<open>bij (apply_perm p)\<close> 
proof -
  have \<open>\<And>v i. apply_perm (inv p) (apply_perm p v) i = v i\<close>
    unfolding apply_perm_def
    by (metis assms bij_inv_eq_iff)
  hence \<open>apply_perm (inv p) \<circ> apply_perm p = id\<close>
    by (auto 0 3)
  moreover have \<open>\<And>v i. apply_perm p (apply_perm (inv p) v) i = v i\<close>
    unfolding apply_perm_def
    by (metis assms bij_inv_eq_iff)
  hence \<open>apply_perm p \<circ> apply_perm (inv p) = id\<close>
    by (auto 0 3)
  ultimately show ?thesis
    using o_bij by blast
qed

lemma apply_perm_comp:
  shows \<open>apply_perm f \<circ> apply_perm g = apply_perm (g \<circ> f)\<close>
  unfolding apply_perm_def by auto

lemma apply_perm_weight: 
  assumes \<open>bij p\<close>
  shows \<open>weight (apply_perm p v) = weight v\<close>
  unfolding weight_def apply_perm_def
proof -
  have \<open>(\<lambda>i. v (p i)) -` {False} = (v \<circ> p) -` {False}\<close>
    by fastforce
  also have \<open>\<dots> = p -` v -` {False}\<close>
    by (simp add: vimage_comp)
  also have \<open>\<dots> = (inv p) ` v -` {False}\<close>
    by (simp add: assms bij_vimage_eq_inv_image)
  finally have \<open>card ((\<lambda>i. v (p i)) -` {False}) = card (inv p ` v -` {False})\<close>
    by simp
  also have \<open>\<dots> = card (v -` {False})\<close>
    using card_vimage_inj[of \<open>inv p\<close> \<open>v -` {False}\<close>]
    by (metis assms bij_betw_imp_surj_on card_image inj_on_inv_into top_greatest)
  finally show \<open>card ((\<lambda>i. v (p i)) -` {False}) = card (v -` {False})\<close>.
qed

lemma apply_perm_cmp:
  assumes \<open>bij p\<close>
  shows \<open>apply_cmp c (apply_perm p v) = apply_perm p (apply_cmp (p (fst c), p (snd c)) v)\<close>
  unfolding apply_cmp_logic apply_perm_def fst_conv snd_conv
  by (metis assms bij_pointE)

lemma apply_perm_cmp_comp:
  assumes \<open>bij p\<close>
  shows \<open>apply_cmp c \<circ> apply_perm p = apply_perm p \<circ> apply_cmp (p (fst c), p (snd c))\<close>
  by (rule ext; insert assms; simp add: apply_perm_cmp)

lemma permuted_bound:
  assumes \<open>pls_bound V b\<close> \<open>bij p\<close>
  shows \<open>pls_bound (apply_perm p ` V) b\<close>
  using assms
proof (induction b arbitrary: p V)
  case 0
  have \<open>pls_bound (apply_perm p ` V) 0\<close>
    using trivial_bound.
  thus ?case.
next
  case (Suc b)

  have V_unsorted: \<open>\<not>inj_on weight V\<close>
    by (metis Suc.prems(1) bound_unsorted bound_weaken plus_1_eq_Suc)
  have weight_invariant: \<open>\<And>v. weight (apply_perm p v) = weight v\<close>
    using Suc.prems(2) apply_perm_weight by auto
  have p_bij: \<open>bij (apply_perm p)\<close>
    by (simp add: Suc.prems(2) apply_perm_bij)

  show ?case
  proof (rule suc_bound)
    show \<open>\<not>inj_on weight (apply_perm p ` V)\<close>
      using V_unsorted weight_invariant p_bij inj_on_invariant_bij_image by blast
  next
    fix c
    have \<open>pls_bound (apply_perm p ` apply_cmp (p (fst c), p (snd c)) ` V) b\<close>
      using Suc.IH Suc.prems(1) Suc.prems(2) bound_suc by blast
    thus \<open>pls_bound (apply_cmp c ` apply_perm p ` V) b\<close>
      using apply_perm_cmp_comp[of p c]
      by (metis Suc.prems(2) image_comp)
  qed
qed

lemma permuted_bound_iff:
  assumes \<open>bij p\<close>
  shows \<open>pls_bound V b = pls_bound (apply_perm p ` V) b\<close>
proof
  show \<open>pls_bound V b \<Longrightarrow> pls_bound (apply_perm p ` V) b\<close>
    using assms permuted_bound by auto
next
  assume \<open>pls_bound (apply_perm p ` V) b\<close>
  hence \<open>pls_bound (apply_perm (inv p) ` apply_perm p ` V) b\<close>
    by (simp add: assms bij_betw_inv_into permuted_bound)
  thus \<open>pls_bound V b\<close>
    using apply_perm_comp
    by (metis (no_types, lifting) apply_perm_bij assms bij_id bij_is_inj bijection.intro
        bijection.inv_comp_right image_comp inj_vimage_image_eq inv_id)
qed

lemma permuted_bounds_iff:
  assumes \<open>bij p\<close>
  shows \<open>pls_bound V = pls_bound (apply_perm p ` V)\<close>
proof
  fix x
  show \<open>pls_bound V x = pls_bound (apply_perm p ` V) x\<close>
    using assms permuted_bound_iff by blast
qed

lemma apply_perm_fixed_width:
  assumes \<open>p permutes {..<n}\<close> \<open>fixed_width_vect n v\<close>
  shows \<open>fixed_width_vect n (apply_perm p v)\<close>
  using assms unfolding fixed_width_vect_def apply_perm_def permutes_def
  by simp

lemma apply_perm_fixed_width_image:
  assumes \<open>p permutes {..<n}\<close> \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close>
  shows \<open>\<And>v. v \<in> apply_perm p ` V \<Longrightarrow> fixed_width_vect n v\<close>
  using apply_perm_fixed_width assms by blast

(***)

lemma apply_cmp_swap:
  \<open>apply_cmp (prod.swap c) v = apply_perm (Fun.swap (fst c) (snd c) id) (apply_cmp c v)\<close>
  unfolding apply_cmp_logic apply_perm_def fst_swap snd_swap
  by (metis (no_types, hide_lams) swap_id_eq)

lemma apply_cmp_swap_comp:
  \<open>apply_cmp (prod.swap c) = apply_perm (Fun.swap (fst c) (snd c) id) \<circ> apply_cmp c\<close>
  by (rule ext; auto simp add: apply_cmp_swap)

lemma apply_cmp_swap_bound:
  \<open>pls_bound (apply_cmp (prod.swap c) ` V) b = pls_bound (apply_cmp c ` V) b\<close>
proof -
  have \<open>pls_bound (apply_cmp (prod.swap c) ` V) b =
      pls_bound ((apply_perm (Fun.swap (fst c) (snd c) id) \<circ> apply_cmp c) ` V) b\<close>
    using apply_cmp_swap_comp by simp
  also have \<open>\<dots> = pls_bound (apply_cmp c ` V) b\<close>
    by (metis image_comp o_bij permuted_bound_iff swap_id_idempotent)
  finally show ?thesis.
qed

lemma suc_bound_noop:
  assumes unsorted: \<open>\<not>inj_on weight V\<close>
    and suc_bounds: \<open>\<And>c. pls_bound (apply_cmp c ` V) b \<or> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  shows \<open>pls_bound V (Suc b)\<close>
  using assms
proof (induction b)
  case 0
  thus ?case
    using unsorted_bound by auto 
next
  case (Suc b)
  thus ?case
    by (metis Suc_eq_plus1 bound_weaken suc_bound) 
qed

lemma ocmp_suc_bound:
  assumes unsorted: \<open>\<not>inj_on weight V\<close>
    and fixed_width: \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close>
    and suc_bounds:
      \<open>\<And>c. fst c < snd c \<and> snd c < n \<Longrightarrow>
        pls_bound (apply_cmp c ` V) b \<or> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  shows \<open>pls_bound V (Suc b)\<close>
proof -
  have \<open>\<And>c. pls_bound (apply_cmp c ` V) b \<or> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  proof -
    fix c
    have \<open>snd c \<ge> n \<Longrightarrow> \<forall>v \<in> V. apply_cmp c v = v\<close>
      using apply_cmp_fixed_width_snd_oob fixed_width not_less by blast
    hence \<open>snd c \<ge> n \<Longrightarrow> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
      by simp

    moreover have
      \<open>fst c \<ge> n \<Longrightarrow> \<forall>v \<in> V. apply_cmp c v = apply_perm (Fun.swap (fst c) (snd c) id) v\<close>
      by (metis apply_cmp_fixed_width_snd_oob apply_cmp_swap fixed_width fst_swap
          swap_commute swap_swap)
    hence \<open>fst c \<ge> n \<Longrightarrow>
        pls_bound (apply_cmp c ` V) = pls_bound (apply_perm (Fun.swap (fst c) (snd c) id) ` V)\<close>
      by auto
    hence \<open>fst c \<ge> n \<Longrightarrow> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
      by (metis o_bij permuted_bounds_iff swap_id_idempotent)

    moreover have
      \<open>fst c < snd c \<and> snd c < n \<Longrightarrow>
        pls_bound (apply_cmp c ` V) b \<or> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
      using suc_bounds by simp

    moreover have
      \<open>snd c < fst c \<and> fst c < n \<Longrightarrow>
        pls_bound (apply_cmp c ` V) b \<or> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
      using apply_cmp_swap_bound suc_bounds
      by (metis apply_cmp_swap_comp image_comp o_bij permuted_bounds_iff prod.exhaust_sel snd_swap
          swap_id_idempotent swap_simp)

    moreover have \<open>fst c = snd c \<Longrightarrow> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
      by (simp add: apply_cmp_same_channels)

    ultimately show \<open>pls_bound (apply_cmp c ` V) b \<or> pls_bound (apply_cmp c ` V) = pls_bound V\<close>
      using nat_neq_iff not_less by blast
  qed
  thus ?thesis
    using suc_bound_noop unsorted by blast
qed

(***)

definition redundant_cmp :: \<open>cmp \<Rightarrow> vect set \<Rightarrow> bool\<close> where
  \<open>redundant_cmp c V = (\<not>((\<exists>v \<in> V. v (fst c) \<and> \<not>v (snd c)) \<and> (\<exists>v \<in> V. \<not>v (fst c) \<and> v (snd c))))\<close>

lemma redundant_cmp_id:
  assumes \<open>\<not>(\<exists>v \<in> V. v (fst c) \<and> \<not>v (snd c))\<close>
  shows \<open>apply_cmp c ` V = V\<close>
proof -
  have \<open>\<And>v. v \<in> V \<Longrightarrow> apply_cmp c v = v\<close>
  proof 
    fix v i assume \<open>v \<in> V\<close>
    hence \<open>\<not>v (fst c) \<or> v (snd c)\<close>
      using assms by blast
    thus \<open>apply_cmp c v i = v i\<close>
      using apply_cmp_logic by auto
  qed
  thus ?thesis
    by simp
qed

lemma redundant_cmp_swap:
  assumes \<open>\<not>(\<exists>v \<in> V. \<not>v (fst c) \<and> v (snd c))\<close>
  shows \<open>apply_cmp c ` V = Fun.swap (fst c) (snd c) ` V\<close>
proof -
  have \<open>\<And>v. v \<in> V \<Longrightarrow> apply_cmp c v = Fun.swap (fst c) (snd c) v\<close>
  proof 
    fix v i assume \<open>v \<in> V\<close>
    hence \<open>v (fst c) \<or> \<not>v (snd c)\<close>
      using assms by blast
    thus \<open>apply_cmp c v i = Fun.swap (fst c) (snd c) v i\<close>
      using apply_cmp_logic
      by (metis swap_apply(1, 3) swap_commute)
  qed
  thus ?thesis
    by simp
qed

lemma redundant_cmp_id_bound:
  assumes \<open>\<not>(\<exists>v \<in> V. v (fst c) \<and> \<not>v (snd c))\<close>
  shows \<open>pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  by (simp add: assms redundant_cmp_id)

lemma redundant_cmp_swap_bound:
  assumes \<open>\<not>(\<exists>v \<in> V. \<not>v (fst c) \<and> v (snd c))\<close>
  shows \<open>pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  by (metis (no_types, lifting) apply_cmp_swap_comp assms fst_swap image_comp o_bij
      permuted_bounds_iff redundant_cmp_id snd_swap swap_id_idempotent)

lemma redundant_cmp_bound:
  assumes \<open>redundant_cmp c V\<close>
  shows \<open>pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  by (metis assms redundant_cmp_def redundant_cmp_id_bound redundant_cmp_swap_bound)

(***)

definition invert_vect :: \<open>nat \<Rightarrow> vect \<Rightarrow> vect\<close> where
  \<open>invert_vect n v i = (v i \<noteq> (i < n))\<close>

lemma invert_vect_invol: \<open>invert_vect n \<circ> invert_vect n = id\<close>
  unfolding invert_vect_def comp_apply by fastforce

lemma invert_vect_bij: \<open>bij (invert_vect n)\<close>
  using invert_vect_invol o_bij by blast

lemma invert_vect_fixed_width:
  assumes \<open>fixed_width_vect n v\<close>
  shows \<open>fixed_width_vect n (invert_vect n v)\<close>
  using assms fixed_width_vect_def invert_vect_def by auto

lemma invert_false_set:
  assumes \<open>fixed_width_vect n v\<close>
  shows \<open>invert_vect n v -` {False} = {..<n} - (v -` {False})\<close>
proof (rule set_eqI)
  fix i
  have \<open>(i \<in> {..<n} - v -` {False}) = (i \<in> {..<n}  \<and> i \<notin> v -` {False})\<close>
    by simp
  also have \<open>\<dots> = (i < n \<and> v i)\<close>
    by simp
  also have \<open>\<dots> = (v i = (i < n))\<close>
    using assms fixed_width_vect_def by auto
  also have \<open>\<dots> = (\<not>invert_vect n v i)\<close>
    by (simp add: invert_vect_def)
  also have \<open>\<dots> = (i \<in> invert_vect n v -` {False})\<close>
    by simp
  finally show \<open>(i \<in> invert_vect n v -` {False}) = (i \<in> {..<n} - v -` {False})\<close>
    by simp
qed

lemma invert_vect_weight:
  assumes \<open>fixed_width_vect n v\<close>
  shows \<open>weight (invert_vect n v) = n - weight v\<close>
  unfolding weight_def
  by (metis assms card_Diff_subset card_lessThan finite_lessThan finite_subset
      fixed_width_false_set invert_false_set)

lemma inj_on_inj_inj_image:
  assumes \<open>inj_on g A\<close> \<open>inj_on h (f ` A)\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> f (g a) = h (f a)\<close> 
  shows \<open>inj_on f A = inj_on f (g ` A)\<close>
proof
  assume fwd: \<open>inj_on f A\<close>
  show \<open>inj_on f (g ` A)\<close>
  proof
    fix x y assume x: \<open>x \<in> g ` A\<close> and y: \<open>y \<in> g ` A\<close> and f_eq: \<open>f x = f y\<close>
    thus \<open>x = y\<close>
      by (metis (full_types) fwd assms(2) assms(3) image_iff inj_on_eq_iff)
  qed
next
  assume bwd: \<open>inj_on f (g ` A)\<close>
  show \<open>inj_on f A\<close>
  proof
    fix x y assume x: \<open>x \<in> A\<close> and y: \<open>y \<in> A\<close> and f_eq: \<open>f x = f y\<close>
    thus \<open>x = y\<close>
      by (metis assms(1) assms(3) bwd imageI inj_on_contraD)
  qed
qed

lemma sub_inj_on: \<open>inj_on ((-) n) {0..n :: nat}\<close>
  by (metis atLeast0AtMost atMost_iff diff_diff_cancel inj_onI)

lemma invert_vect_cmp:
  assumes \<open>fst c < n\<close> \<open>snd c < n\<close>
  shows \<open>apply_cmp c (invert_vect n v) = invert_vect n (apply_cmp (prod.swap c) v)\<close>
  unfolding apply_cmp_logic invert_vect_def fst_swap snd_swap
  using assms by auto

lemma invert_vect_cmp_comp:
  assumes \<open>fst c < n\<close> \<open>snd c < n\<close>
  shows \<open>apply_cmp c \<circ> invert_vect n = invert_vect n \<circ> apply_cmp (prod.swap c)\<close>
  by (rule ext; insert assms; simp add: invert_vect_cmp)

lemma inverted_bound:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close> \<open>pls_bound V b\<close>
  shows \<open>pls_bound (invert_vect n ` V) b\<close>
  using assms
proof (induction b arbitrary: n V)
  case 0
  have \<open>pls_bound (invert_vect n ` V) 0\<close>
    using trivial_bound.
  thus ?case.
next
  case (Suc b)

  show ?case
  proof (rule ocmp_suc_bound[where n=n])
    have \<open>weight ` V \<subseteq> {0..n}\<close>
      by (simp add: Suc.prems(1) fixed_width_weight_bound image_subsetI)
    hence \<open>inj_on ((-) n) (weight ` V)\<close>
      by (meson inj_on_subset sub_inj_on)
    thus \<open>\<not>inj_on weight (invert_vect n ` V)\<close>
      using inj_on_inj_inj_image[of \<open>invert_vect n\<close> V \<open>\<lambda>x. n - x\<close> weight]
      by (metis Suc.prems(1) Suc.prems(2) bij_betw_def bound_unsorted bound_weaken inj_on_subset
          invert_vect_bij invert_vect_weight plus_1_eq_Suc subset_UNIV)
  next 
    fix v
    show \<open>v \<in> invert_vect n ` V \<Longrightarrow> fixed_width_vect n v\<close>
      using Suc.prems(1) invert_vect_fixed_width by auto
  next
    fix c assume \<open>fst c < snd c \<and> snd c < n\<close>
    hence bound_c: \<open>fst c < n\<close> \<open>snd c < n\<close>
      using less_trans by auto

    have \<open>pls_bound (apply_cmp (prod.swap c) ` V) b\<close>
      using Suc.prems(2) bound_suc
      by simp
    hence \<open>pls_bound (invert_vect n ` apply_cmp (prod.swap c) ` V) b\<close>
      using Suc.prems(1) Suc.IH apply_cmp_fixed_width_in_bounds bound_c
      by (metis (no_types, lifting) fst_swap imageE snd_swap) 

    thus \<open>pls_bound (apply_cmp c ` invert_vect n ` V) b \<or>
      pls_bound (apply_cmp c ` invert_vect n ` V) = pls_bound (invert_vect n ` V)\<close>
      by (simp add: bound_c image_comp invert_vect_cmp_comp)
  qed
qed

(***)

definition pruned_bound :: \<open>vect set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>pruned_bound V i b = (((\<noteq>) i) \<in> V \<and> pls_bound {v \<in> V. \<not>v i} b)\<close>

lemma pls_bound_from_pruned_bound:
  assumes \<open>pruned_bound V i b\<close>
  shows \<open>pls_bound V b\<close>
  by (rule bound_mono_subset[of \<open>{v \<in> V. \<not>v i}\<close>]; insert assms pruned_bound_def; blast)

lemma apply_cmp_sorted:
  assumes \<open>\<not>v (fst c)\<close>
  shows \<open>apply_cmp c v = v\<close>
  unfolding apply_cmp_logic
  using assms by auto

lemma apply_cmp_sorted_bound:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> \<not>v (fst c)\<close>
  shows \<open>pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  using apply_cmp_sorted by (simp add: assms)

lemma apply_cmp_sorted_pruned_bound:
  assumes \<open>pruned_bound V (fst c) b\<close>
  shows \<open>pruned_bound (apply_cmp c ` V) (fst c) b\<close>
  unfolding pruned_bound_def
proof
  show \<open>(\<noteq>) (fst c) \<in> apply_cmp c ` V\<close>
    using assms unfolding pruned_bound_def apply_cmp_logic by auto
next
  have \<open>pls_bound {v \<in> V. \<not>v (fst c)} b\<close>
    using assms pruned_bound_def by blast
  hence \<open>pls_bound (apply_cmp c ` {v \<in> V. \<not>v (fst c)}) b\<close>
    by (metis (mono_tags, lifting) apply_cmp_sorted_bound mem_Collect_eq)
  moreover have \<open>(apply_cmp c ` {v \<in> V. \<not>v (fst c)}) \<subseteq> {v \<in> apply_cmp c ` V. \<not>v (fst c)}\<close>
    by (metis (mono_tags, lifting) apply_cmp_sorted image_eqI image_subsetI mem_Collect_eq)
  ultimately show \<open>pls_bound {v \<in> apply_cmp c ` V. \<not>v (fst c)} b\<close>
    using bound_mono_subset by auto 
qed

lemma apply_cmp_rev_sorted:
  assumes \<open>\<not>v (snd c)\<close>
  shows \<open>apply_cmp c v = v \<circ> (Fun.swap (fst c) (snd c) id)\<close>
  unfolding apply_cmp_logic comp_apply
  using assms by (auto simp add: swap_id_eq)

lemma apply_cmp_rev_sorted_bound:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> \<not>v (snd c)\<close>
  shows \<open>pls_bound (apply_cmp c ` V) = pls_bound V\<close>
  using apply_cmp_rev_sorted
  by (metis (no_types, hide_lams) UNIV_I apply_cmp_sorted_bound apply_cmp_swap_comp assms
      bij_betw_id bij_betw_swap_iff fst_swap image_comp permuted_bounds_iff)

lemma apply_cmp_rev_sorted_pruned_bound:
  assumes \<open>pruned_bound V (snd c) b\<close>
  shows \<open>pruned_bound (apply_cmp c ` V) (fst c) b\<close>
  unfolding pruned_bound_def
proof
  have \<open>(\<noteq>) (snd c) \<in> V\<close>
    using assms unfolding pruned_bound_def by simp
  moreover have \<open>apply_cmp c ((\<noteq>) (snd c)) = ((\<noteq>) (fst c))\<close>
    unfolding apply_cmp_logic by auto
  ultimately show \<open>(\<noteq>) (fst c) \<in> apply_cmp c ` V\<close>
    using image_iff[of \<open>(\<noteq>) (fst c)\<close> \<open>apply_cmp c\<close> V] by fastforce
next
  have \<open>pls_bound {v \<in> V. \<not>v (snd c)} b\<close>
    using assms pruned_bound_def by blast
  hence \<open>pls_bound (apply_cmp c ` {v \<in> V. \<not>v (snd c)}) b\<close>
    by (metis (mono_tags, lifting) apply_cmp_rev_sorted_bound mem_Collect_eq)
  moreover have \<open>(apply_cmp c ` {v \<in> V. \<not>v (snd c)}) \<subseteq> {v \<in> apply_cmp c ` V. \<not>v (fst c)}\<close>
    by (metis (mono_tags, lifting) apply_cmp_logic imageI image_Collect_subsetI mem_Collect_eq)
  ultimately show \<open>pls_bound {v \<in> apply_cmp c ` V. \<not>v (fst c)} b\<close>
    using bound_mono_subset by auto 
qed

lemma apply_cmp_other_pruned_bound:
  assumes \<open>i \<noteq> fst c\<close> \<open>i \<noteq> snd c\<close> \<open>pruned_bound V i (Suc b)\<close>
  shows \<open>pruned_bound (apply_cmp c ` V) i b\<close>
  unfolding pruned_bound_def
proof
  have \<open>(\<noteq>) i \<in> V\<close>
    using assms unfolding pruned_bound_def by simp
  moreover have \<open>apply_cmp c ((\<noteq>) i) = ((\<noteq>) i)\<close>
    unfolding apply_cmp_logic using assms by auto
  ultimately show \<open>(\<noteq>) i \<in> apply_cmp c ` V\<close>
    using image_iff[of \<open>(\<noteq>) i\<close> \<open>apply_cmp c\<close> V] by fastforce
next
  have \<open>pls_bound {v \<in> V. \<not>v i} (Suc b)\<close>
    using assms pruned_bound_def by blast
  hence \<open>pls_bound (apply_cmp c ` {v \<in> V. \<not>v i}) b\<close>
    using bound_suc by blast
  moreover have \<open>\<And>v. apply_cmp c v i = v i\<close>
    unfolding apply_cmp_logic
    by (simp add: assms)
  hence \<open>(apply_cmp c ` {v \<in> V. \<not>v i}) = {v \<in> apply_cmp c ` V. \<not>v i}\<close>
    by blast
  ultimately show \<open>pls_bound {v \<in> apply_cmp c ` V. \<not>v i} b\<close>
    by auto
qed

lemma apply_cmp_other_pruned_zero_bound:
  assumes \<open>i \<noteq> fst c\<close> \<open>i \<noteq> snd c\<close> \<open>pruned_bound V i 0\<close>
  shows \<open>pruned_bound (apply_cmp c ` V) i 0\<close>
  unfolding pruned_bound_def
proof
  have \<open>(\<noteq>) i \<in> V\<close>
    using assms unfolding pruned_bound_def by simp
  moreover have \<open>apply_cmp c ((\<noteq>) i) = ((\<noteq>) i)\<close>
    unfolding apply_cmp_logic using assms by auto
  ultimately show \<open>(\<noteq>) i \<in> apply_cmp c ` V\<close>
    using image_iff[of \<open>(\<noteq>) i\<close> \<open>apply_cmp c\<close> V] by fastforce
next
  show \<open>pls_bound {v \<in> apply_cmp c ` V. \<not>v i} 0\<close>
    using trivial_bound.
qed

(***)

definition pruned_bounds :: \<open>vect set \<Rightarrow> (nat \<rightharpoonup> nat) \<Rightarrow> bool\<close> where
  \<open>pruned_bounds V B = (\<forall>i \<in> dom B. pruned_bound V i (the (B i)))\<close>

definition combine_bounds :: \<open>nat option \<Rightarrow> nat option \<Rightarrow> nat option\<close> where
  \<open>combine_bounds a b = (case a of
    None \<Rightarrow> b | Some a' \<Rightarrow> (case b of
      None \<Rightarrow> Some a' | Some b' \<Rightarrow> Some (max a' b')))\<close>

lemma combine_bounds_either:
  \<open>combine_bounds a b = a \<or> combine_bounds a b = b\<close>
  by (simp add: combine_bounds_def max_def option.case_eq_if)

definition pruned_bounds_suc :: \<open>cmp \<Rightarrow> (nat \<rightharpoonup> nat) \<Rightarrow> (nat \<rightharpoonup> nat)\<close> where
  \<open>pruned_bounds_suc c bs =
    (map_option nat.pred \<circ> bs)(
      snd c := None,
      fst c := combine_bounds (bs (fst c)) (bs (snd c)))\<close>

lemma the_map_option_dom[simp]:
  \<open>x \<in> dom f \<Longrightarrow> the (map_option g (f x)) = g (the (f x))\<close>
  by (simp add: domIff option.map_sel)

lemma apply_cmp_pruned_bounds:
  assumes \<open>pruned_bounds V B\<close> 
  shows \<open>pruned_bounds (apply_cmp c ` V) (pruned_bounds_suc c B)\<close>
  unfolding pruned_bounds_def
proof
  fix i assume in_dom: \<open>i \<in> dom (pruned_bounds_suc c B)\<close>
  show \<open>pruned_bound (apply_cmp c ` V) i (the (pruned_bounds_suc c B i))\<close>
  proof (cases \<open>i = fst c \<or> i = snd c\<close>)
    case True
    hence i_fst: \<open>i = fst c\<close>
      by (metis domIff fun_upd_def in_dom pruned_bounds_suc_def)

    show ?thesis
    proof (cases \<open>fst c = snd c\<close>)
      case True
      then show ?thesis
        unfolding pruned_bounds_suc_def
        by (simp add: i_fst True;metis True apply_cmp_rev_sorted_pruned_bound assms
            combine_bounds_either domD domI fun_upd_same i_fst in_dom pruned_bounds_def
            pruned_bounds_suc_def)
    next
      case False
      show ?thesis
        unfolding pruned_bounds_suc_def
        by (metis apply_cmp_rev_sorted_pruned_bound apply_cmp_sorted_pruned_bound assms(1)
            combine_bounds_either domIff fun_upd_same i_fst in_dom pruned_bounds_def
            pruned_bounds_suc_def)
    qed
  next
    case False
    hence in_dom': \<open>i \<in> dom B\<close>
      by (metis in_dom comp_apply domIff fun_upd_apply option.simps(8) pruned_bounds_suc_def)
    show ?thesis
      unfolding pruned_bounds_suc_def
      using False in_dom'
      by (simp; metis apply_cmp_other_pruned_bound apply_cmp_other_pruned_zero_bound assms(1)
          nat.split_sels(2) pred_def pruned_bounds_def)
  qed
qed

(***)

definition mset_ran :: \<open>('a \<rightharpoonup> 'b) \<Rightarrow> 'b multiset\<close> where
  \<open>mset_ran m = {#the (m a). a \<in># mset_set (dom m)#}\<close>

lemma size_mset_ran:
  \<open>finite (dom m) \<Longrightarrow> size (mset_ran m) = card (dom m)\<close>
  unfolding mset_ran_def
  by simp

lemma image_mset_set_cong:
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x = g x\<close>
  shows \<open>image_mset f (mset_set A) = image_mset g (mset_set A)\<close>
  by (metis assms finite_set_mset_mset_set image_mset_cong image_mset_empty mset_set.infinite)

lemma comp_push_lambda: \<open>f \<circ> (\<lambda>x. g x) = (\<lambda>x. f (g x))\<close>
  by auto

lemma mset_ran_map_option:
  \<open>mset_ran (map_option f \<circ> m) = image_mset f (mset_ran m)\<close>
proof -
  have \<open>\<And>a. a \<in> dom m \<Longrightarrow> the (map_option f (m a)) = f (the (m a))\<close>
    by simp
  hence
    \<open>{#the (map_option f (m a)). a \<in># mset_set (dom m)#} =
      {#f (the (m a)). a \<in># mset_set (dom m)#}\<close>
    by (meson image_mset_set_cong)
  thus ?thesis
    unfolding mset_ran_def 
    by (simp add: image_mset.compositionality; simp add: comp_push_lambda)
qed

abbreviation mset_option :: \<open>'a option \<Rightarrow> 'a multiset\<close> where
  \<open>mset_option \<equiv> case_option {#} (\<lambda>x. {#x#})\<close> 

lemma mset_option_Some:
  \<open>mset_option (Some x) = {#x#}\<close>
  by simp

lemma image_mset_set_diff:
  assumes \<open>finite A\<close> 
  shows \<open>image_mset f (mset_set (A - B)) =
    image_mset f (mset_set A) - image_mset f (mset_set (A \<inter> B))\<close>
  using assms
  by (metis Diff_Compl Diff_Diff_Int Diff_eq image_mset_Diff inf_le1 mset_set_Diff
      subset_imp_msubset_mset_set)

lemma mset_ran_upd_None:
  assumes \<open>finite (dom m)\<close>
  shows \<open>mset_ran (m(x := None)) = mset_ran m - mset_option (m x)\<close>
proof -
  have \<open>dom (m(x := None)) = dom m - {x}\<close>
    by simp
  hence \<open>mset_ran (m(x := None)) = {#the ((m(x := None)) a). a \<in># mset_set (dom m - {x})#}\<close>
    unfolding mset_ran_def
    by simp
  also have \<open>\<dots> = {#the (m a). a \<in># mset_set (dom m - {x})#}\<close>
    using image_mset_set_cong[of \<open>dom m - {x}\<close> \<open>\<lambda>a. the ((m(x := None)) a)\<close> \<open>\<lambda>a. the (m a)\<close>]
    by simp
  also have \<open>\<dots> = {#the (m a). a \<in># mset_set (dom m)#} - {#the (m a). a \<in># mset_set (dom m \<inter> {x})#}\<close>
    using image_mset_set_diff[of \<open>dom m\<close> _ \<open>{x}\<close>] assms
    by blast
  also have \<open>\<dots> = mset_ran m - mset_option (m x)\<close>
    unfolding mset_ran_def
    by (simp add: domIff option.case_eq_if)
  finally show ?thesis
    by simp
qed

lemma mset_ran_upd_new:
  assumes \<open>finite (dom m)\<close> \<open>x \<notin> dom m\<close>
  shows \<open>mset_ran (m(x \<mapsto> y)) = mset_ran m + {#y#}\<close>
proof -
  have \<open>mset_ran (m(x \<mapsto> y)) = {#the ((m(x \<mapsto> y)) a). a \<in># mset_set (dom m \<union> {x})#}\<close>
    unfolding mset_ran_def
    by simp
  also have \<open>\<dots> = {#the ((m(x \<mapsto> y)) a). a \<in># mset_set (dom m)#} +
      {#the ((m(x \<mapsto> y)) a). a \<in># mset_set {x}#}\<close>
    using assms(1) assms(2) by auto
  also have \<open>\<dots> = mset_ran m + {#the ((m(x \<mapsto> y)) a). a \<in># mset_set {x}#}\<close>
    unfolding mset_ran_def
    by (metis (mono_tags, lifting) assms(2) fun_upd_other image_mset_set_cong)
  finally show ?thesis
    by simp
qed

lemma mset_ran_upd_new_option:
  assumes \<open>finite (dom m)\<close> \<open>x \<notin> dom m\<close>
  shows \<open>mset_ran (m(x := y)) = mset_ran m + mset_option y\<close>
proof (cases \<open>y = None\<close>)
  case True
  then show ?thesis
    by (metis add.comm_neutral assms(2) domIff fun_upd_idem_iff option.simps(4))
next
  case False
  then show ?thesis
    using assms mset_ran_upd_new by fastforce
qed

lemma mset_ran_upd:
  assumes \<open>finite (dom m)\<close>
  shows \<open>mset_ran (m(x := y)) = mset_ran m - mset_option (m x) + mset_option y\<close>
proof -
  have \<open>mset_ran (m(x := None, x := y)) = mset_ran m - mset_option (m x) + mset_option y\<close>
    by (metis assms domIff dom_fun_upd finite_Diff fun_upd_same mset_ran_upd_None
        mset_ran_upd_new_option)
  thus ?thesis
    by simp
qed

lemma mset_ran_Melem:
  assumes \<open>finite (dom B)\<close> \<open>x \<in> dom B\<close>
  shows \<open>the (B x) \<in># mset_ran B\<close>
proof -
  have \<open>x \<in># mset_set (dom B)\<close>
    using assms by simp
  thus ?thesis
    unfolding mset_ran_def
    by simp
qed

lemma mset_ran_pair:
  assumes \<open>finite (dom B)\<close> \<open>x \<in> dom B\<close> \<open>y \<in> dom B\<close> \<open>x \<noteq> y\<close>
  shows \<open>{#the (B x), the (B y)#} \<subseteq># mset_ran B\<close>
proof -
  have \<open>{#x, y#} \<subseteq># mset_set (dom B)\<close>
    using assms mset_set.remove by fastforce
  thus ?thesis
    unfolding mset_ran_def
    using image_mset_subseteq_mono by fastforce
qed

lemma not_in_dom_None[simp]: \<open>x \<notin> dom B \<Longrightarrow> B x = None\<close>
  by blast

lemma in_dom_eq_None_case[simp]:
  \<open>x \<in> dom B \<Longrightarrow> (case B x of None \<Rightarrow> a | Some y \<Rightarrow> b y) = b (the (B x))\<close>
  by auto

(***)

definition sucmax :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sucmax a b = Suc (max a b)\<close>

global_interpretation sucmax: huffman_algebra sucmax
  defines sucmax_value_bound_huffman = sucmax.value_bound_huffman
  and sucmax_huffman_step_sorted_list = sucmax.huffman_step_sorted_list
  by (unfold_locales; unfold sucmax_def; auto)

lemma nat_pred_sucmax_mono:
  \<open>nat.pred (sucmax a b) \<le> sucmax (nat.pred a) (nat.pred b)\<close>
  by (cases a; cases b; simp add: sucmax_def)

lemma mono_nat_pred: \<open>mono nat.pred\<close>
  unfolding mono_def
proof (rule; rule; rule)
  fix x y :: nat assume \<open>x \<le> y\<close>
  thus \<open>nat.pred x \<le> nat.pred y\<close>
    by (cases x; simp; cases y; simp)
qed

lemma sucmax_value_bound_mset_pred:
  assumes \<open>A \<noteq> {#}\<close>
  shows \<open>nat.pred (sucmax.value_bound_mset A) \<le> sucmax.value_bound_mset (image_mset nat.pred A)\<close>
  by (rule sucmax.value_bound_mono; simp add: nat_pred_sucmax_mono mono_nat_pred assms)

lemma mset_ran_pruned_bounds_suc_nn:
  assumes \<open>finite (dom B)\<close> \<open>fst c \<notin> dom B\<close> \<open>snd c \<notin> dom B\<close>
  shows \<open>mset_ran (pruned_bounds_suc c B) = image_mset nat.pred (mset_ran B)\<close>
  unfolding pruned_bounds_suc_def
  using assms
  by (simp add: mset_ran_upd combine_bounds_def mset_ran_map_option)


lemma mset_ran_pruned_bounds_suc_in:
  assumes \<open>finite (dom B)\<close> \<open>fst c \<in> dom B\<close> \<open>snd c \<notin> dom B \<or> snd c = fst c\<close>
  shows \<open>mset_ran (pruned_bounds_suc c B) =
    add_mset (the (B (fst c))) (image_mset nat.pred (mset_ran B - {#the (B (fst c)) #}))\<close>
proof -
  have *: \<open>pruned_bounds_suc c B = (map_option nat.pred \<circ> B)(fst c \<mapsto> the (B (fst c)))\<close>
    unfolding pruned_bounds_suc_def combine_bounds_def
    using assms by auto
  show ?thesis
    unfolding *
    by (subst mset_ran_upd; simp add: assms mset_ran_map_option mset_ran_Melem image_mset_Diff)
qed

lemma mset_ran_pruned_bounds_suc_ni:
  assumes \<open>finite (dom B)\<close> \<open>fst c \<notin> dom B\<close> \<open>snd c \<in> dom B\<close>
  shows \<open>mset_ran (pruned_bounds_suc c B) =
    add_mset (the (B (snd c))) (image_mset nat.pred (mset_ran B - {#the (B (snd c)) #}))\<close>
proof -
  have *:
    \<open>pruned_bounds_suc c B = (map_option nat.pred \<circ> B)(snd c := None)(fst c \<mapsto> the (B (snd c)))\<close>
    unfolding pruned_bounds_suc_def combine_bounds_def
    using assms by auto
  show ?thesis
    unfolding *
    by (subst mset_ran_upd; simp add: assms mset_ran_map_option mset_ran_Melem image_mset_Diff;
        subst mset_ran_upd; simp add: assms mset_ran_map_option)
qed

lemma mset_ran_pruned_bounds_suc_ii:
  assumes \<open>finite (dom B)\<close> \<open>fst c \<in> dom B\<close> \<open>snd c \<in> dom B\<close> \<open>fst c \<noteq> snd c\<close>
  shows \<open>mset_ran (pruned_bounds_suc c B) =
    add_mset (max (the (B (fst c))) (the (B (snd c))))
    (image_mset nat.pred (mset_ran B - {#the (B (fst c)), the (B (snd c)) #}))\<close>
proof -
  have *:
    \<open>pruned_bounds_suc c B =
      (map_option nat.pred \<circ> B)(snd c := None)(fst c \<mapsto> max (the (B (fst c))) (the (B (snd c))))\<close>
    unfolding pruned_bounds_suc_def combine_bounds_def
    using assms by auto
  show ?thesis
    unfolding *
    by (subst mset_ran_upd; simp add: assms mset_ran_map_option mset_ran_pair image_mset_Diff;
        subst mset_ran_upd; simp add: assms mset_ran_map_option)
qed

lemma sucmax_value_bound_pruned_bounds_suc_nn:
  assumes \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close> \<open>fst c \<notin> dom B\<close> \<open>snd c \<notin> dom B\<close>
  shows \<open>nat.pred (sucmax.value_bound_mset (mset_ran B)) \<le>
    sucmax.value_bound_mset (mset_ran (pruned_bounds_suc c B))\<close>
  by (subst mset_ran_pruned_bounds_suc_nn; simp add: assms;
      rule sucmax_value_bound_mset_pred; insert assms mset_ran_Melem; fastforce)

lemma sucmax_value_bound_pruned_bounds_suc_in:
  assumes \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close> \<open>fst c \<in> dom B\<close> \<open>snd c \<notin> dom B \<or> snd c = fst c\<close>
  shows \<open>nat.pred (sucmax.value_bound_mset (mset_ran B)) \<le>
    sucmax.value_bound_mset (mset_ran (pruned_bounds_suc c B))\<close>
proof (subst mset_ran_pruned_bounds_suc_in; (insert assms; blast; fail)?)
  have i1:
    \<open>nat.pred (sucmax.value_bound_mset (mset_ran B))
      \<le> sucmax.value_bound_mset (image_mset nat.pred (mset_ran B))\<close>
    by (metis assms(1, 3) empty_iff mset_ran_Melem set_mset_empty sucmax_value_bound_mset_pred)

  have \<open>nat.pred (the (B (fst c))) \<in># image_mset nat.pred (mset_ran B)\<close>
    by (simp add: assms(1, 3) mset_ran_Melem)

  moreover have \<open>nat.pred (the (B (fst c))) \<le> the (B (fst c))\<close>
    by (metis Suc_n_not_le_n bot.extremum mono_def mono_nat_pred nat.split_sels(2) nat_le_linear)

  ultimately have i2:
    \<open>sucmax.value_bound_mset (image_mset nat.pred (mset_ran B))
      \<le> sucmax.value_bound_mset (
          image_mset nat.pred (mset_ran B)
            - {#nat.pred (the (B (fst c)))#}
            + {#the (B (fst c))#})\<close>
    using sucmax.value_bound_increasing by blast

  have e1:
    \<open>add_mset (the (B (fst c))) (image_mset nat.pred (mset_ran B - {#the (B (fst c))#})) =
      image_mset nat.pred (mset_ran B)
        - {#nat.pred (the (B (fst c)))#}
        + {#the (B (fst c))#}\<close>
    by (metis (no_types, lifting) add_mset_add_single assms(1, 3) image_mset_Diff image_mset_single
        mset_ran_Melem mset_subset_eq_single)

  show
    \<open>nat.pred (sucmax.value_bound_mset (mset_ran B))
      \<le> sucmax.value_bound_mset (
        add_mset (the (B (fst c))) (image_mset nat.pred (mset_ran B - {#the (B (fst c))#})))\<close>
    using i1 i2 e1 by auto
qed

lemma sucmax_value_bound_pruned_bounds_suc_ni:
  assumes \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close> \<open>fst c \<notin> dom B\<close> \<open>snd c \<in> dom B\<close>
  shows \<open>nat.pred (sucmax.value_bound_mset (mset_ran B)) \<le>
    sucmax.value_bound_mset (mset_ran (pruned_bounds_suc c B))\<close>
proof (subst mset_ran_pruned_bounds_suc_ni; (insert assms; blast; fail)?)
  have i1:
    \<open>nat.pred (sucmax.value_bound_mset (mset_ran B))
      \<le> sucmax.value_bound_mset (image_mset nat.pred (mset_ran B))\<close>
    by (metis assms(1, 4) empty_iff mset_ran_Melem set_mset_empty sucmax_value_bound_mset_pred)

  have \<open>nat.pred (the (B (snd c))) \<in># image_mset nat.pred (mset_ran B)\<close>
    by (simp add: assms(1, 4) mset_ran_Melem)

  moreover have \<open>nat.pred (the (B (snd c))) \<le> the (B (snd c))\<close>
    by (metis Suc_n_not_le_n bot.extremum mono_def mono_nat_pred nat.split_sels(2) nat_le_linear)

  ultimately have i2:
    \<open>sucmax.value_bound_mset (image_mset nat.pred (mset_ran B))
      \<le> sucmax.value_bound_mset (
          image_mset nat.pred (mset_ran B)
            - {#nat.pred (the (B (snd c)))#}
            + {#the (B (snd c))#})\<close>
    using sucmax.value_bound_increasing by blast

  have e1:
    \<open>add_mset (the (B (snd c))) (image_mset nat.pred (mset_ran B - {#the (B (snd c))#})) =
      image_mset nat.pred (mset_ran B)
        - {#nat.pred (the (B (snd c)))#}
        + {#the (B (snd c))#}\<close>
    by (metis (no_types, lifting) add_mset_add_single assms(1, 4) image_mset_Diff image_mset_single
        mset_ran_Melem mset_subset_eq_single)

  show
    \<open>nat.pred (sucmax.value_bound_mset (mset_ran B))
      \<le> sucmax.value_bound_mset (
        add_mset (the (B (snd c))) (image_mset nat.pred (mset_ran B - {#the (B (snd c))#})))\<close>
    using i1 i2 e1 by auto
qed

lemma sucmax_value_bound_pruned_bounds_suc_ii:
  assumes \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close> \<open>fst c \<in> dom B\<close> \<open>snd c \<in> dom B\<close> \<open>fst c \<noteq> snd c\<close>
  shows \<open>nat.pred (sucmax.value_bound_mset (mset_ran B)) \<le>
    sucmax.value_bound_mset (mset_ran (pruned_bounds_suc c B))\<close>
proof -
  define B_suc_ran where \<open>
    B_suc_ran = mset_ran B
      - {#the (B (fst c)), the (B (snd c)) #}
      + {#sucmax (the (B (fst c))) (the (B (snd c)))#}\<close>

  note B_suc_ran_def[simp]

  have e1: \<open>mset_ran (pruned_bounds_suc c B) = image_mset nat.pred B_suc_ran\<close>
    by (simp add: assms mset_ran_pruned_bounds_suc_ii sucmax_def)

  have i1: \<open>sucmax.value_bound_mset (mset_ran B) \<le> sucmax.value_bound_mset B_suc_ran\<close>
    using sucmax.combine_step_lower_bound
    by (simp add: assms mset_ran_pair)

  have i2:
    \<open>nat.pred (sucmax.value_bound_mset B_suc_ran)
      \<le> sucmax.value_bound_mset (image_mset nat.pred B_suc_ran)\<close>
    by (metis add_mset_add_single empty_not_add_mset sucmax_value_bound_mset_pred B_suc_ran_def)

  have i3:
    \<open>nat.pred (sucmax.value_bound_mset (mset_ran B))
      \<le> sucmax.value_bound_mset (image_mset nat.pred B_suc_ran)\<close>
    by (rule order_subst2[of
          \<open>sucmax.value_bound_mset (mset_ran B)\<close> \<open>sucmax.value_bound_mset B_suc_ran\<close>];
        insert i1 i2 mono_def mono_nat_pred; blast)

  show ?thesis
    using e1 i3 by auto
qed

lemma sucmax_value_bound_pruned_bounds_suc:
  assumes \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close>
  shows \<open>nat.pred (sucmax.value_bound_mset (mset_ran B)) \<le>
    sucmax.value_bound_mset (mset_ran (pruned_bounds_suc c B))\<close>
  using sucmax_value_bound_pruned_bounds_suc_nn
    sucmax_value_bound_pruned_bounds_suc_in
    sucmax_value_bound_pruned_bounds_suc_ni
    sucmax_value_bound_pruned_bounds_suc_ii
  by (metis assms)

lemma finite_dom_pruned_bounds_suc:
  assumes \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close>
  shows \<open>finite (dom (pruned_bounds_suc c B))\<close>
  unfolding pruned_bounds_suc_def combine_bounds_def
  using assms
  by auto

lemma nonempty_dom_pruned_bounds_suc:
  assumes \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close>
  shows \<open>dom (pruned_bounds_suc c B) \<noteq> {}\<close>
  unfolding pruned_bounds_suc_def combine_bounds_def
  using assms
  by (cases \<open>fst c \<in> dom B\<close>; cases \<open>snd c \<in> dom B\<close>; auto)


(***)

lemma pls_bound_1_from_sucmax_value_bound_mset:
  assumes \<open>pruned_bounds V B\<close> \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close>
    \<open>sucmax.value_bound_mset (mset_ran B) \<noteq> 0\<close>
  shows \<open>pls_bound V 1\<close>
proof (cases \<open>size (mset_ran B) = 1\<close>)
  case True
  then obtain b where b: \<open>mset_ran B = {#b#}\<close>
    using size_1_singleton_mset by blast
  hence b_ne_0: \<open>b \<noteq> 0\<close>
    using assms(4) sucmax.value_bound_singleton by auto
  
  obtain i where i: \<open>B i = Some b\<close>
    using b assms(2, 3) mset_ran_Melem by fastforce
  hence \<open>pruned_bound V i b\<close>
    by (metis assms(1) domI option.sel pruned_bounds_def)
  then show ?thesis
    by (metis One_nat_def Suc_le_eq b_ne_0 le_0_eq neq0_conv pls_bound_def
        pls_bound_from_pruned_bound) 
next
  case False
  moreover have \<open>size (mset_ran B) \<noteq> 0\<close>
    by (metis assms(2) assms(3) image_mset_is_empty_iff mset_ran_def mset_set_empty_iff
        size_eq_0_iff_empty)
  ultimately have \<open>size (mset_ran B) \<ge> 2\<close>
    by linarith
  hence card_dom_B: \<open>card (dom B) \<ge> 2\<close>
    using assms
    by (simp add: size_mset_ran)

  obtain i1 where i1: \<open>i1 \<in> dom B\<close>
    using assms(3) by blast

  have \<open>dom B - {i1} \<noteq> {}\<close>
    using card_dom_B
    by (metis One_nat_def Suc_n_not_le_n assms(2) card.remove card_empty i1
        one_add_one plus_1_eq_Suc)
  then obtain i2 where i2: \<open>i2 \<in> dom B - {i1}\<close>
    by blast
  hence \<open>((\<noteq>) i1) \<noteq> ((\<noteq>) i2)\<close>
    by (metis Diff_iff singletonI)
  moreover have \<open>((\<noteq>) i1) \<in> V\<close>
    using assms(1) i1 pruned_bounds_def pruned_bound_def by blast
  moreover have \<open>((\<noteq>) i2) \<in> V\<close>
    using assms(1) i2 pruned_bounds_def pruned_bound_def by blast
  ultimately have \<open>\<not>inj_on weight V\<close>
    by (metis (no_types, lifting) inj_on_contraD weight_one)
  then show ?thesis
    using unsorted_bound by blast
qed
  
lemma pls_bound_from_pruned_bounds':
  assumes \<open>pruned_bounds V B\<close> \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close>
    \<open>b \<le> sucmax.value_bound_mset (mset_ran B)\<close>
  shows \<open>pls_bound V b\<close>
  using assms
proof (induction b arbitrary: B V rule: less_induct)
  case (less b)
  show ?case
  proof (cases b)
    case 0
    then show ?thesis 
      using trivial_bound by simp
  next
    case (Suc b')

    hence \<open>pls_bound V 1\<close>
      using pls_bound_1_from_sucmax_value_bound_mset[of _ B] less.prems
      by auto

    moreover have \<open>\<And>c. pls_bound (apply_cmp c ` V) b'\<close>
    proof -
      fix c

      have *: \<open>pruned_bounds (apply_cmp c ` V) (pruned_bounds_suc c B)\<close>
        by (simp add: apply_cmp_pruned_bounds less.prems(1))

      have **:
        \<open>nat.pred (sucmax.value_bound_mset (mset_ran B))
          \<le> sucmax.value_bound_mset (mset_ran (pruned_bounds_suc c B))\<close>
        using less.prems(2) less.prems(3) sucmax_value_bound_pruned_bounds_suc by blast

      have ***:
        \<open>b' \<le> nat.pred (sucmax.value_bound_mset (mset_ran B))\<close>
        using Suc Suc_le_D less.prems(4) by fastforce

      show \<open>pls_bound (apply_cmp c ` V) b'\<close>
        by (rule less.IH[of _ _ \<open>pruned_bounds_suc c B\<close>];
            insert * ** *** less.prems finite_dom_pruned_bounds_suc nonempty_dom_pruned_bounds_suc
            dual_order.trans; auto simp add: Suc)
    qed

    ultimately show ?thesis
      by (simp add: Suc suc_bound bound_unsorted)
  qed
qed

lemma pls_bound_from_pruned_bounds:
  assumes \<open>pruned_bounds V B\<close> \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close>
  shows \<open>pls_bound V (sucmax.value_bound_mset (mset_ran B))\<close>
  using assms pls_bound_from_pruned_bounds'
  by blast

(***)

abbreviation apply_pol :: \<open>nat \<Rightarrow> bool \<Rightarrow> vect \<Rightarrow> vect\<close> where
  \<open>apply_pol n pol v \<equiv> (if pol then v else invert_vect n v)\<close>

lemma apply_pol_invol: \<open>apply_pol n pol (apply_pol n pol v) = v\<close>
  by (cases pol; simp add: invert_vect_invol pointfree_idE)

definition pruned_bound_pol :: \<open>nat \<Rightarrow> bool \<Rightarrow> vect set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>pruned_bound_pol n pol V i b = pruned_bound (apply_pol n pol ` V) i b\<close>

definition pruned_bounds_pol :: \<open>nat \<Rightarrow> bool \<Rightarrow> vect set \<Rightarrow> (nat \<rightharpoonup> nat) \<Rightarrow> bool\<close> where
  \<open>pruned_bounds_pol n pol V B = (\<forall>i \<in> dom B. pruned_bound_pol n pol V i (the (B i)))\<close>

lemma pls_bound_from_pruned_bounds_pol:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close>
    \<open>pruned_bounds_pol n pol V B\<close> \<open>finite (dom B)\<close> \<open>dom B \<noteq> {}\<close>
  shows \<open>pls_bound V (sucmax.value_bound_mset (mset_ran B))\<close>
proof (cases pol)
  case True
  hence \<open>pruned_bounds V B\<close>
    using assms unfolding pruned_bounds_def pruned_bounds_pol_def pruned_bound_pol_def
    by simp
  then show ?thesis
    using assms pls_bound_from_pruned_bounds by simp
next
  case False
  hence \<open>pruned_bounds (invert_vect n ` V) B\<close>
    using assms unfolding pruned_bounds_def pruned_bounds_pol_def pruned_bound_pol_def
    by simp
  hence \<open>pls_bound (invert_vect n ` V) (sucmax.value_bound_mset (mset_ran B))\<close>
    using assms pls_bound_from_pruned_bounds by blast
  hence \<open>pls_bound (invert_vect n ` invert_vect n ` V) (sucmax.value_bound_mset (mset_ran B))\<close>
    using assms(1) invert_vect_fixed_width
    by (auto intro: inverted_bound)
  then show ?thesis
    unfolding image_comp invert_vect_invol
    by simp
qed

lemma apply_pol_bound:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close> \<open>pls_bound V b\<close>
  shows \<open>pls_bound (apply_pol n pol ` V) b\<close>
  using assms
  by (cases pol; simp add: inverted_bound)

lemma apply_pol_bound_iff:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_width_vect n v\<close>
  shows \<open>pls_bound (apply_pol n pol ` V) b = pls_bound V b\<close>
proof
  assume \<open>pls_bound (apply_pol n pol ` V) b\<close>
  hence \<open>pls_bound (apply_pol n pol ` (apply_pol n pol ` V)) b\<close>
    by (intro apply_pol_bound[where V=\<open>apply_pol n pol ` V\<close>];
        insert assms invert_vect_fixed_width; auto)
  thus \<open>pls_bound V b\<close>
    using apply_pol_invol[where n=n and pol=pol]
    unfolding image_image by simp
next
  assume \<open>pls_bound V b\<close>
  thus \<open>pls_bound (apply_pol n pol ` V) b\<close>
    using assms apply_pol_bound by simp
qed

end