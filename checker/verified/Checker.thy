theory Checker
  imports Main Sorting_Network
begin

datatype proof_witness =
  ProofWitness (witness_step_id: int) (witness_invert: bool) (witness_perm: \<open>int list\<close>)

datatype proof_step_witnesses =
  HuffmanWitnesses (huffman_polarity: bool) (huffman_witnesses: \<open>proof_witness option list\<close>) |
  SuccessorWitnesses (successor_witnesses: \<open>proof_witness option list\<close>)

datatype proof_step =
  ProofStep
    (step_width: int)
    (step_vect_list: \<open>bool list list\<close>)
    (step_bound: int)
    (step_witnesses: proof_step_witnesses)

datatype proof_cert =
  ProofCert (cert_length: int) (cert_step: \<open>int \<Rightarrow> proof_step\<close>)

(***)

datatype vect_trie =
  VtEmpty | VtNode bool vect_trie vect_trie

fun vt_singleton :: \<open>bool list \<Rightarrow> vect_trie\<close> where
  \<open>vt_singleton [] = VtNode True VtEmpty VtEmpty\<close> |
  \<open>vt_singleton (False # xs) = VtNode False (vt_singleton xs) VtEmpty\<close> |
  \<open>vt_singleton (True # xs) = VtNode False VtEmpty (vt_singleton xs)\<close>

fun vt_union :: \<open>vect_trie \<Rightarrow> vect_trie \<Rightarrow> vect_trie\<close> where
  \<open>vt_union VtEmpty VtEmpty = VtEmpty\<close> |
  \<open>vt_union a VtEmpty = a\<close> |
  \<open>vt_union VtEmpty b = b\<close> |
  \<open>vt_union (VtNode a a_lo a_hi) (VtNode b b_lo b_hi) =
    VtNode (a \<or> b) (vt_union a_lo b_lo) (vt_union a_hi b_hi)\<close>

lemma vt_union_commutative:
  \<open>vt_union A B = vt_union B A\<close>
  by (induction A B rule: vt_union.induct; auto)

definition vt_list :: \<open>bool list list \<Rightarrow> vect_trie\<close> where
  \<open>vt_list ls = fold (vt_union \<circ> vt_singleton) ls VtEmpty\<close>

fun set_vt :: \<open>vect_trie \<Rightarrow> bool list set\<close> where
  \<open>set_vt VtEmpty = {}\<close> |
  \<open>set_vt (VtNode True lo hi) = {[]} \<union> (((#) False) ` set_vt lo) \<union> (((#) True) ` set_vt hi)\<close> |
  \<open>set_vt (VtNode False lo hi) = (((#) False) ` set_vt lo) \<union> (((#) True) ` set_vt hi)\<close> 

lemma set_vt_union:
  \<open>set_vt (vt_union A B) = set_vt A \<union> set_vt B\<close>
proof (induction A B rule: vt_union.induct; (simp; fail)?)
  case (4 a a_lo a_hi b b_lo b_hi)
  thus ?case
    by (subst vt_union.simps; cases a; cases b; auto)
qed

lemma set_vt_singleton:
  \<open>set_vt (vt_singleton xs) = {xs}\<close>
proof (induction xs)
  case Nil
  thus ?case
    by auto
next
  case (Cons x xs)
  thus ?case
    by (cases x; simp)
qed

lemma homo_fold:
  assumes \<open>\<And>A B. f (g A B) = h (f A) (f B)\<close>
  shows \<open>f (fold g xs x) = fold h (map f xs) (f x)\<close>
  by (induction xs arbitrary: x; simp add: assms)

lemma set_vt_list:
  \<open>set_vt (vt_list ls) = set ls\<close>
proof -
  have \<open>set_vt (vt_list ls) = set_vt (fold (vt_union) (map vt_singleton ls) VtEmpty)\<close>
    by (simp add: vt_list_def fold_map)
  also have \<open>\<dots> = fold (\<union>) (map set_vt (map vt_singleton ls)) (set_vt VtEmpty)\<close>
    by (simp add: homo_fold set_vt_union)
  also have \<open>\<dots> = fold (\<union>) (map (\<lambda>l. {l}) ls) {}\<close>
    by (simp add: comp_def set_vt_singleton)
  also have \<open>\<dots> = set ls\<close>
    by (metis Sup_set_fold UN_singleton image_set)
  finally show ?thesis.
qed

fun list_vt :: \<open>vect_trie \<Rightarrow> bool list list\<close> where
  \<open>list_vt VtEmpty = []\<close> |
  \<open>list_vt (VtNode True lo hi) =
    [] # map ((#) False) (list_vt lo) @ map ((#) True) (list_vt hi)\<close> |
  \<open>list_vt (VtNode False lo hi) =
    map ((#) False) (list_vt lo) @ map ((#) True) (list_vt hi)\<close>

lemma set_list_vt:
  \<open>set (list_vt A) = set_vt A\<close>
  by (induction A rule: list_vt.induct; auto)

fun list_vt_extend ::
  \<open>vect_trie \<Rightarrow> (bool list \<Rightarrow> bool list) \<Rightarrow> bool list list \<Rightarrow> bool list list\<close> where
  \<open>list_vt_extend VtEmpty el_prefix suffix = suffix\<close> |
  \<open>list_vt_extend (VtNode True lo hi) el_prefix suffix =
    el_prefix [] # list_vt_extend lo (el_prefix \<circ> ((#) False)) (
      list_vt_extend hi (el_prefix \<circ> ((#) True)) suffix)\<close> |
  \<open>list_vt_extend (VtNode False lo hi) el_prefix suffix =
    list_vt_extend lo (el_prefix \<circ> ((#) False)) (
      list_vt_extend hi (el_prefix \<circ> ((#) True)) suffix)\<close> 

lemma dlist_as_bs[simp]: \<open>((@) as \<circ> (@) bs) = ((@) (as @ bs))\<close>
  by (rule ext; simp)

lemma dlist_as_b[simp]: \<open>((@) as \<circ> (#) b) = ((@) (as @ [b]))\<close>
  by (rule ext; simp)

lemma dlist_a_bs[simp]: \<open>((#) a \<circ> (@) bs) = ((@) (a # bs))\<close>
  by (rule ext; simp)

lemma list_vt_extend_as_list_vt:
  \<open>list_vt_extend A ((@) el_prefix) suffix = map ((@) el_prefix) (list_vt A) @ suffix\<close>
  by (induction A \<open>((@) el_prefix)\<close> suffix arbitrary: el_prefix rule: list_vt_extend.induct; simp)

lemma list_vt_as_list_vt_extend[code]:
  \<open>list_vt A = list_vt_extend A id []\<close>
proof -
  have \<open>list_vt A = list_vt_extend A ((@) []) []\<close>
    using list_vt_extend_as_list_vt
    by (simp add: map_idI)
  also have \<open>\<dots> = list_vt_extend A id []\<close>
    by (metis append_Nil id_apply)
  finally show ?thesis.
qed

lemma empty_list_nmember_cons_image:
  \<open>[] \<notin> ((#) x) ` A\<close>
  by blast

lemma cons_image_disjoint:
  \<open>x \<noteq> y \<Longrightarrow> (((#) x) ` A) \<inter> (((#) y) ` B) = {}\<close>
  by blast

lemma distinct_map':
  \<open>\<lbrakk>distinct xs; inj f\<rbrakk> \<Longrightarrow> distinct (map f xs)\<close>
  using distinct_map inj_on_subset by blast

lemma distinct_list_vt:
  \<open>distinct (list_vt A)\<close>
  by (induction A rule: list_vt.induct;
      simp add: empty_list_nmember_cons_image cons_image_disjoint distinct_map')

fun is_subset_vt :: \<open>vect_trie \<Rightarrow> vect_trie \<Rightarrow> bool\<close> where
  \<open>is_subset_vt VtEmpty a = True\<close> |
  \<open>is_subset_vt (VtNode True a_lo a_hi) VtEmpty = False\<close> |
  \<open>is_subset_vt (VtNode False a_lo a_hi) VtEmpty =
    (is_subset_vt a_lo VtEmpty \<and> is_subset_vt a_hi VtEmpty)\<close> |
  \<open>is_subset_vt (VtNode True a_lo a_hi) (VtNode False b_lo b_hi) = False\<close> |
  \<open>is_subset_vt (VtNode False a_lo a_hi) (VtNode b b_lo b_hi) =
    (is_subset_vt a_lo b_lo \<and> is_subset_vt a_hi b_hi)\<close> |
  \<open>is_subset_vt (VtNode a a_lo a_hi) (VtNode True b_lo b_hi) =
    (is_subset_vt a_lo b_lo \<and> is_subset_vt a_hi b_hi)\<close> 

lemma set_vt_subset_cons_False:
  assumes \<open>set_vt A \<subseteq> set_vt B\<close>
  shows \<open>(#) False ` set_vt A \<subseteq> set_vt (VtNode b B B')\<close>
proof -
  have \<open>(#) False ` set_vt A \<subseteq> (#) False ` set_vt B\<close>
    by (meson assms image_mono)
  thus ?thesis
    by (metis (full_types) Un_commute le_supI1 set_vt.simps(2, 3))
qed

lemma set_vt_subset_cons_True:
  assumes \<open>set_vt A \<subseteq> set_vt B\<close>
  shows \<open>(#) True ` set_vt A \<subseteq> set_vt (VtNode b B' B)\<close>
proof -
  have \<open>(#) True ` set_vt A \<subseteq> (#) True ` set_vt B\<close>
    by (meson assms image_mono)
  thus ?thesis
    by (metis (full_types) Un_commute le_supI1 set_vt.simps(2, 3))
qed

lemma set_vt_subset_is_subset_vt:
  assumes \<open>is_subset_vt A B\<close>
  shows \<open>set_vt A \<subseteq> set_vt B\<close>
  using assms
  by (induction A B rule: is_subset_vt.induct;
      insert set_vt_subset_cons_False set_vt_subset_cons_True; auto)

fun is_member_vt :: \<open>bool list \<Rightarrow> vect_trie \<Rightarrow> bool\<close> where
  \<open>is_member_vt _ VtEmpty = False\<close> |
  \<open>is_member_vt [] (VtNode a _ _) = a\<close> |
  \<open>is_member_vt (False # xs) (VtNode _ a_lo _) = is_member_vt xs a_lo\<close> |
  \<open>is_member_vt (True # xs) (VtNode _ _ a_hi) = is_member_vt xs a_hi\<close>

lemma is_member_vt_as_member_set_vt:
  \<open>is_member_vt xs A = (xs \<in> set_vt A)\<close>
proof (induction xs A rule: is_member_vt.induct; (simp; fail)?)
  case (2 a uv uw)
  then show ?case
    by (cases a; simp add: empty_list_nmember_cons_image)
next
  case (3 xs ux a_lo uy)
  then show ?case
    by (cases ux; auto)
next
  case (4 xs uz va a_hi)
  then show ?case 
    by (cases uz; auto)
qed

(***)

fun list_to_vect :: \<open>bool list \<Rightarrow> bseq\<close> where
  \<open>list_to_vect [] i = True\<close> |
  \<open>list_to_vect (x # xs) 0 = x\<close> |
  \<open>list_to_vect (x # xs) (Suc i) = list_to_vect xs i\<close>

lemma list_to_vect_as_nth:
  \<open>list_to_vect xs = (\<lambda>i. if i < length xs then xs!i else True)\<close>
proof 
  fix i show \<open>list_to_vect xs i = (if i < length xs then xs ! i else True)\<close>
  proof (induction xs arbitrary: i)
    case Nil
    thus ?case
      by simp
  next
    case (Cons a xs)
    thus ?case
      by (cases i; simp)
  qed
qed

lemma list_to_vect_inj_on_same_length:
  \<open>inj_on list_to_vect {xs. length xs = n}\<close>
  by (rule; simp add: list_eq_iff_nth_eq list_to_vect_as_nth; metis)
  
fun apply_cmp_list :: \<open>cmp \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>apply_cmp_list (a, b) xs = (let xa = xs!a; xb = xs!b in xs[a := xa \<and> xb, b := xa \<or> xb])\<close>

lemma length_apply_cmp_list:
  \<open>length (apply_cmp_list c xs) = length xs\<close>
  by (metis apply_cmp_list.elims length_list_update)

lemma apply_cmp_list_to_vect:
  assumes \<open>a < length xs\<close> \<open>b < length xs\<close>
  shows \<open>apply_cmp (a, b) (list_to_vect xs) = list_to_vect (apply_cmp_list (a, b) xs)\<close>
  by (rule; simp add: assms list_to_vect_as_nth Let_def apply_cmp_def)

fun length_vt :: \<open>vect_trie \<Rightarrow> nat\<close> where
  \<open>length_vt VtEmpty = 0\<close> |
  \<open>length_vt (VtNode True lo hi) = Suc (length_vt lo + length_vt hi)\<close> |
  \<open>length_vt (VtNode False lo hi) = length_vt lo + length_vt hi\<close>

lemma length_vt_as_length_list_vt:
  \<open>length_vt A = length (list_vt A)\<close>
  by (induction A rule: list_vt.induct; simp)

lemma length_vt_as_card_set_vt:
  \<open>length_vt A = card (set_vt A)\<close>
proof -
  have \<open>length_vt A = card (set (list_vt A))\<close>
    by (simp add: length_vt_as_length_list_vt distinct_card distinct_list_vt)
  also have \<open>\<dots> = card (set_vt A)\<close>
    by (simp add: set_list_vt)
  finally show ?thesis.
qed

definition is_unsorted_vt :: \<open>nat \<Rightarrow> vect_trie \<Rightarrow> bool\<close> where
  \<open>is_unsorted_vt n A = (length_vt A > Suc n)\<close>

lemma fixed_len_bseq_list_to_vect:
  \<open>length xs = n \<Longrightarrow> fixed_len_bseq n (list_to_vect xs)\<close>
  unfolding fixed_len_bseq_def list_to_vect_as_nth
  by simp

lemma is_unsorted_vt_bound:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close> \<open>is_unsorted_vt n A\<close>
  shows \<open>pls_bound (list_to_vect ` set_vt A) 1\<close>
proof (rule unsorted_by_card_bound)
  fix v assume \<open>v \<in> list_to_vect ` set_vt A\<close>
  thus \<open>fixed_len_bseq n v\<close>
    using assms fixed_len_bseq_list_to_vect
    by blast 
next
  show \<open>n + 1 < card (list_to_vect ` set_vt A)\<close>
    using assms
    unfolding is_unsorted_vt_def length_vt_as_card_set_vt
    by (subst card_image; linarith?; insert inj_on_subset list_to_vect_inj_on_same_length; blast)
qed

abbreviation list_to_perm :: \<open>nat list \<Rightarrow> (nat \<Rightarrow> nat)\<close> where
  \<open>list_to_perm xs i \<equiv> if i < length xs then xs!i else i\<close>

lemma bij_list_to_perm:
  assumes \<open>distinct xs\<close> \<open>list_all (\<lambda>i. i < length xs) xs\<close>
  shows \<open>bij (list_to_perm xs)\<close>
proof -
  have *: \<open>card (set xs) = length xs\<close>
    by (simp add: assms(1) distinct_card)
  have \<open>set xs \<subseteq> {..<length xs}\<close>
    using assms distinct_Ex1 list_all_length by fastforce
  hence \<open>set xs = {..<length xs}\<close>
    using *
    by (simp add: card_subset_eq)
  hence \<open>bij_betw (\<lambda>i. xs!i) {..<length xs} {..<length xs}\<close>
    by (simp add: assms(1) bij_betw_nth)
  hence \<open>bij_betw (list_to_perm xs) {..<length xs} {..<length xs}\<close>
    using bij_betw_cong[of _ \<open>\<lambda>i. xs!i\<close> \<open>list_to_perm xs\<close>]
    by (meson lessThan_iff)

  moreover have
    \<open>bij_betw (list_to_perm xs) (-{..<length xs}) (-{..<length xs})\<close>
    using bij_betw_cong[of \<open>-{..<length xs}\<close> \<open>id\<close> \<open>list_to_perm xs\<close>]
    by auto

  ultimately show \<open>bij (list_to_perm xs)\<close>
    using bij_betw_combine[of
        \<open>list_to_perm xs\<close>
        \<open>{..<length xs}\<close> \<open>{..<length xs}\<close>
        \<open>-{..<length xs}\<close> \<open>-{..<length xs}\<close>]
    by (metis Compl_partition inf_compl_bot)
qed

definition permute_list_vect :: \<open>nat list \<Rightarrow> bool list \<Rightarrow> bool list\<close> where
  \<open>permute_list_vect ps xs = map (\<lambda>i. xs!i) ps\<close>

lemma list_to_vect_permute_list_vect_as_apply_perm:
  assumes \<open>list_all (\<lambda>x. x < length ps) ps\<close> \<open>length ps = length xs\<close>
  shows \<open>list_to_vect (permute_list_vect ps xs) = apply_perm (list_to_perm ps) (list_to_vect xs)\<close>
proof
  fix i
  show \<open>list_to_vect (permute_list_vect ps xs) i =
    apply_perm (list_to_perm ps) (list_to_vect xs) i\<close>
    unfolding permute_list_vect_def apply_perm_def list_to_vect_as_nth
    using assms
    by (simp add: list_all_length)
qed

lemma perm_list_to_vect_set:
  assumes \<open>list_all (\<lambda>x. x < length ps) ps\<close> \<open>length ps = n\<close> \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
  shows \<open>list_to_vect ` set_vt (vt_list (map (permute_list_vect ps) (list_vt A))) =
    apply_perm (list_to_perm ps) ` list_to_vect ` set_vt A\<close>
proof -
  have
    \<open>set_vt (vt_list (map (permute_list_vect ps) (list_vt A)))
      = set (map (permute_list_vect ps) (list_vt A))\<close>
    using set_vt_list by blast
  also have \<open>\<dots> = permute_list_vect ps ` set_vt A\<close>
    by (simp add: set_list_vt)
  finally have
    \<open>list_to_vect ` set_vt (vt_list (map (permute_list_vect ps) (list_vt A))) =
      list_to_vect ` permute_list_vect ps ` set_vt A\<close>
    by simp
  also have \<open>\<dots> = (\<lambda>xs. list_to_vect (permute_list_vect ps xs)) ` set_vt A\<close>
    by blast
  also have \<open>\<dots> = (\<lambda>xs. apply_perm (list_to_perm ps) (list_to_vect xs)) ` set_vt A\<close>
    by (rule image_cong; simp?; subst list_to_vect_permute_list_vect_as_apply_perm;
        (simp add: assms(1))?; insert assms; auto)
  finally show ?thesis
    by (simp add: image_image)
qed

lemma list_to_vect_map_Not_as_invert_vect:
  \<open>list_to_vect (map (Not) xs) = invert_vect (length xs) (list_to_vect xs)\<close>
  unfolding list_to_vect_as_nth invert_vect_def
  by simp

definition permute_vt :: \<open>nat list \<Rightarrow> vect_trie \<Rightarrow> vect_trie\<close> where
  \<open>permute_vt ps A = vt_list (map (permute_list_vect ps) (list_vt A))\<close>

lemma permute_vt_bound:
  assumes \<open>length ps = n\<close> \<open>distinct ps\<close> \<open>list_all (\<lambda>i. i < length ps) ps\<close>
    \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
    \<open>pls_bound (list_to_vect ` set_vt A) b\<close>
  shows \<open>pls_bound (list_to_vect ` set_vt (permute_vt ps A)) b\<close>
  using perm_list_to_vect_set assms bij_list_to_perm permute_vt_def permuted_bound by auto

lemma invert_list_to_vect_set:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
  shows \<open>list_to_vect ` set_vt (vt_list (map (map Not) (list_vt A))) =
    invert_vect n ` list_to_vect ` set_vt A\<close>
proof -
  have
    \<open>set_vt (vt_list (map (map Not) (list_vt A)))
      = set (map (map Not) (list_vt A))\<close>
    using set_vt_list by blast
  also have \<open>\<dots> = map Not ` set_vt A\<close>
    by (simp add: set_list_vt)
  finally have
    \<open>list_to_vect ` set_vt (vt_list (map (map Not) (list_vt A))) =
      list_to_vect ` map Not ` set_vt A\<close>
    by simp
  also have \<open>\<dots> = (\<lambda>xs. list_to_vect (map Not xs)) ` set_vt A\<close>
    by blast
  also have \<open>\<dots> = (\<lambda>xs. invert_vect n (list_to_vect xs)) ` set_vt A\<close>
    by (rule image_cong; simp?; subst list_to_vect_map_Not_as_invert_vect; insert assms; auto)
  finally show ?thesis
    by (simp add: image_image)
qed

definition invert_vt :: \<open>bool \<Rightarrow> vect_trie \<Rightarrow> vect_trie\<close> where
  \<open>invert_vt z A = (if z then vt_list (map (map Not) (list_vt A)) else A)\<close>

lemma list_to_vect_set_vt_fixed_width:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
  shows \<open>list_to_vect ` set_vt A \<subseteq> {v. fixed_len_bseq n v}\<close>
  by (metis (mono_tags, lifting) Ball_Collect assms fixed_len_bseq_list_to_vect image_subsetI
      mem_Collect_eq)

lemma invert_vt_bound:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
    \<open>pls_bound (list_to_vect ` set_vt A) b\<close>
  shows \<open>pls_bound (list_to_vect ` set_vt (invert_vt z A)) b\<close>
  by (cases z; unfold invert_vt_def; simp add: assms;
      subst invert_list_to_vect_set[where n=n]; simp add: assms;
      metis (mono_tags) Ball_Collect list_to_vect_set_vt_fixed_width assms(1, 2) inverted_bound)

lemma invert_vt_fixed_width:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
  shows \<open>set_vt (invert_vt z A) \<subseteq> {xs. length xs = n}\<close>
  using assms
  by (cases z; unfold invert_vt_def; auto simp add: set_vt_list set_list_vt)
  
fun get_bound
  :: \<open>(int \<Rightarrow> proof_step) \<Rightarrow> int \<Rightarrow> proof_witness option \<Rightarrow> nat \<Rightarrow> vect_trie \<Rightarrow> nat option\<close> where
  \<open>get_bound proof_steps step_limit None width A = Some (if is_unsorted_vt width A then 1 else 0)\<close> |
  \<open>get_bound proof_steps step_limit (Some witness) width A = (
    let
      witness_id = witness_step_id witness;
      perm = map nat (witness_perm witness);
      step = proof_steps witness_id;
      B_list = step_vect_list step;
      B = vt_list B_list;
      B' = permute_vt perm (invert_vt (witness_invert witness) B)
    in
    if \<not>(0 \<le> witness_id \<and> witness_id < step_limit)
      \<or> \<not>list_all (\<lambda>i. 0 \<le> i \<and> i < width) perm
      \<or> length perm \<noteq> width
      \<or> \<not>distinct perm
      \<or> \<not>list_all (\<lambda>xs. length xs = width) B_list
      \<or> \<not>is_subset_vt B' A
    then None
    else Some (nat (step_bound step))
  )\<close>

definition step_checked :: \<open>proof_step \<Rightarrow> bool\<close> where
  \<open>step_checked step = (
    list_all (\<lambda>xs. length xs = nat (step_width step)) (step_vect_list step) \<and>
    pls_bound (list_to_vect ` set_vt (vt_list (step_vect_list step))) (nat (step_bound step)))\<close>

lemma get_bound_bound:
  assumes \<open>\<And>step. 0 \<le> step \<and> step < step_limit \<Longrightarrow> step_checked (proof_steps step)\<close>
    \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
    \<open>get_bound proof_steps step_limit witness n A = Some b\<close>
  shows \<open>pls_bound (list_to_vect ` set_vt A) b\<close>
proof (cases witness)
  case None
  thus ?thesis
    using assms(2, 3) is_unsorted_vt_bound trivial_bound by auto
next
  case (Some some_witness)

  define witness_id where \<open>witness_id = witness_step_id some_witness\<close>
  define perm where \<open>perm = map nat (witness_perm some_witness)\<close>
  define B where \<open>B = vt_list (step_vect_list (proof_steps witness_id))\<close>
  define B' where \<open>B' = permute_vt perm (invert_vt (witness_invert some_witness) B)\<close>

  note witness_id_def[simp] perm_def[simp] B_def[simp] B'_def[simp]

  have c1: \<open>0 \<le> witness_id \<and> witness_id < step_limit\<close>
    by (rule ccontr; insert assms Some; simp)

  have c2: \<open>list_all (\<lambda>i. 0 \<le> i \<and> i < n) perm \<and> length perm = n \<and> distinct perm\<close>
    by (rule ccontr; insert assms Some; auto)

  have c3: \<open>is_subset_vt B' A\<close>
    by (rule ccontr; insert assms Some; auto)

  have c4: \<open>list_all (\<lambda>xs. length xs = n) (step_vect_list (proof_steps witness_id))\<close>
    by (rule ccontr; insert assms Some; auto)

  have b: \<open>nat (step_bound (proof_steps witness_id)) = b\<close>
    using c1 c2 c3 c4 assms Some 
    by simp

  have B: \<open>pls_bound (list_to_vect ` set_vt B) b\<close>
    unfolding B_def
    using assms(1) b c1 step_checked_def
    by blast

  have c4': \<open>set (step_vect_list (proof_steps witness_id)) \<subseteq> {xs. length xs = n}\<close>
    using c4
    unfolding Ball_Collect[symmetric] list.pred_set
    by blast

  have B_length: \<open>set_vt B \<subseteq> {xs. length xs = n}\<close>
    using c4'
    by (simp add: set_vt_list)

  have invert_B: \<open>pls_bound (list_to_vect ` set_vt (invert_vt (witness_invert some_witness) B)) b\<close>
    by (rule invert_vt_bound; insert B B_length; auto)

  have B': \<open>pls_bound (list_to_vect ` set_vt B') b\<close>
    unfolding B'_def
    by (rule permute_vt_bound; insert c2 B_length invert_vt_fixed_width invert_B; simp)

  thus ?thesis
    by (meson bound_mono_subset c3 image_mono set_vt_subset_is_subset_vt) 
qed

abbreviation list_any :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>list_any p xs \<equiv> \<not>(list_all (\<lambda>x. \<not>p x) xs)\<close>

fun is_redundant_cmp_vt :: \<open>cmp \<Rightarrow> vect_trie \<Rightarrow> bool\<close> where
  \<open>is_redundant_cmp_vt (a, b) A = (
    let vs = list_vt A in \<not>(list_any (\<lambda>xs. xs!a \<and> \<not>xs!b) vs \<and> list_any (\<lambda>xs. \<not>xs!a \<and> xs!b) vs))\<close>

lemma redundant_cmp_from_is_redundant_cmp_vt:
  assumes \<open>a < n\<close> \<open>b < n\<close>
    \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
  shows \<open>is_redundant_cmp_vt (a, b) A = redundant_cmp (a, b) (list_to_vect ` set_vt A)\<close>
  using assms
  by (simp add: redundant_cmp_def list_all_iff; insert list_to_vect_as_nth set_list_vt; auto)


lemma redundant_cmp_from_is_redundant_cmp_vt':
  assumes \<open>fst c < n\<close> \<open>snd c < n\<close>
    \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
  shows \<open>is_redundant_cmp_vt c A = redundant_cmp c (list_to_vect ` set_vt A)\<close>
  using redundant_cmp_from_is_redundant_cmp_vt
  by (metis assms prod.collapse)

definition ocmp_list :: \<open>nat \<Rightarrow> cmp list\<close> where
  \<open>ocmp_list n = concat (map (\<lambda>i. map (\<lambda>j. (j, i)) [0..<i]) [0..<n])\<close>

lemma set_ocmp_list:
  \<open>set (ocmp_list n) = {c. fst c < snd c \<and> snd c < n}\<close>
proof (rule set_eqI)
  fix c
  obtain a b :: nat where ab: \<open>c = (a, b)\<close>
    by fastforce
    
  have \<open>c \<in> {c. fst c < snd c \<and> snd c < n} = (a < b \<and> b < n)\<close>
    using ab by simp
  also have \<open>\<dots> = (c \<in> set (ocmp_list n))\<close>
    unfolding ab ocmp_list_def set_concat set_map image_image atLeast_upt[symmetric]
    by blast
  finally show \<open>c \<in> set (ocmp_list n) = (c \<in> {c. fst c < snd c \<and> snd c < n})\<close>
    ..
qed

definition check_successors :: \<open>(int \<Rightarrow> proof_step) \<Rightarrow> int \<Rightarrow> proof_step \<Rightarrow> bool\<close> where
  \<open>check_successors proof_steps step_limit step = (case step_witnesses step of
    HuffmanWitnesses _ _ \<Rightarrow> False |
    SuccessorWitnesses witnesses \<Rightarrow> 
      let
        width = (nat (step_width step));
        bound = (nat (step_bound step));
        ocmps = ocmp_list width;
        A_list = step_vect_list step;
        A = vt_list A_list;
        nrcmps = filter (\<lambda>c. \<not>is_redundant_cmp_vt c A) ocmps;
        Bs = map (\<lambda>c. vt_list (map (apply_cmp_list c) A_list)) nrcmps
      in
        bound \<noteq> 0 \<and>
        is_unsorted_vt width A \<and>
        length nrcmps = length witnesses \<and>
        list_all (\<lambda>xs. length xs = width) A_list \<and>
        list_all2 (\<lambda>B w.
          case get_bound proof_steps step_limit w width B of
            None \<Rightarrow> False | Some b \<Rightarrow> Suc b \<ge> bound
        ) Bs witnesses
  )\<close>

lemma list_all2_witness:
  assumes \<open>list_all2 P xs ys\<close>
  shows \<open>\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. y \<in> set ys \<and> P x y\<close>
proof -
  fix x assume \<open>x \<in> set xs\<close>
  then obtain i where \<open>i < length xs\<close> and x: \<open>x = xs!i\<close>
    by (metis in_set_conv_nth)
  hence \<open>ys!i \<in> set ys \<and> P x (ys!i)\<close>
    unfolding x
    using assms list_all2_conv_all_nth by auto
  thus \<open>\<exists>y. y \<in> set ys \<and> P x y\<close>
    by auto
qed

lemma apply_cmp_as_apply_cmp_list:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close> \<open>a < n\<close> \<open>b < n\<close>
  shows \<open>apply_cmp (a, b) ` list_to_vect ` set_vt A =
    list_to_vect ` set_vt (vt_list (map (apply_cmp_list (a, b)) (list_vt A)))\<close>
  unfolding set_vt_list set_map image_image set_list_vt
  by (rule image_cong; insert assms apply_cmp_list_to_vect; blast)

lemma apply_cmp_as_apply_cmp_list':
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close> \<open>fst c < n\<close> \<open>snd c < n\<close>
  shows \<open>apply_cmp c ` list_to_vect ` set_vt A =
    list_to_vect ` set_vt (vt_list (map (apply_cmp_list c) (list_vt A)))\<close>
  using apply_cmp_as_apply_cmp_list
  by (metis assms prod.collapse)

lemma check_successors_step_checked:
  assumes \<open>check_successors proof_steps step_limit step\<close>
    \<open>\<And>step. 0 \<le> step \<and> step < step_limit \<Longrightarrow> step_checked (proof_steps step)\<close>
  shows \<open>step_checked step\<close>
proof -

  obtain witnesses where witnesses: \<open>step_witnesses step = SuccessorWitnesses witnesses\<close>
    using assms(1) check_successors_def
    by (metis (no_types, lifting) proof_step_witnesses.case_eq_if proof_step_witnesses.collapse(2))

  define width where \<open>width = nat (step_width step)\<close>
  define bound where \<open>bound = nat (step_bound step)\<close>
  define ocmps where \<open>ocmps = ocmp_list width\<close>
  define A_list where \<open>A_list = step_vect_list step\<close>
  define A where \<open>A = vt_list A_list\<close>
  define nrcmps where \<open>nrcmps = filter (\<lambda>c. \<not>is_redundant_cmp_vt c A) ocmps\<close>
  define Bs where \<open>Bs = map (\<lambda>c. vt_list (map (apply_cmp_list c) A_list)) nrcmps\<close>

  note width_def[simp] bound_def[simp] ocmps_def[simp] A_list_def[simp] A_def[simp] nrcmps_def[simp]
  note Bs_def[simp]

  have nonzero_bound: \<open>bound \<noteq> 0\<close>
    using assms(1)
    unfolding witnesses check_successors_def
    by auto
  then obtain suc_bound where suc_bound: \<open>bound = Suc suc_bound\<close>
    using not0_implies_Suc by blast

  have A_list_lengths: \<open>list_all (\<lambda>xs. length xs = width) A_list\<close>
    using assms(1)
    unfolding witnesses check_successors_def
    by (simp; meson)
  hence A_lengths: \<open>set_vt A \<subseteq> {xs. length xs = width}\<close>
    by (simp add: list.pred_set set_vt_list subsetI)
 
  have \<open>is_unsorted_vt width A\<close> 
    using assms(1)
    unfolding witnesses check_successors_def
    by (simp; meson)
  hence is_unsorted: \<open>pls_bound (list_to_vect ` set_vt A) 1\<close>
    using is_unsorted_vt_bound A_lengths by simp

  have checked_witnesses:
    \<open>list_all2 (\<lambda>B w.
        case get_bound proof_steps step_limit w width B of
          None \<Rightarrow> False | Some b \<Rightarrow> Suc b \<ge> bound
      ) Bs witnesses\<close>
    unfolding Bs_def bound_def
    using assms(1)
    unfolding witnesses check_successors_def
    by (simp; meson)

  have A_suc_lengths:
    \<open>\<And>x. set_vt (vt_list (map (apply_cmp_list x) A_list)) \<subseteq> {xs. length xs = width}\<close>
    by (metis (mono_tags, lifting) A_list_lengths image_subsetI length_apply_cmp_list
        list.pred_set list.set_map mem_Collect_eq set_vt_list)

  have B_bound: \<open>\<And>B. B \<in> set Bs \<Longrightarrow> pls_bound (list_to_vect ` set_vt B) suc_bound\<close>
  proof -
    fix B assume B: \<open>B \<in> set Bs\<close>

    hence B_lengths: \<open>set_vt B \<subseteq> {xs. length xs = width}\<close>
      using A_suc_lengths by auto

    have \<open>\<exists>w. case get_bound proof_steps step_limit w width B of
          None \<Rightarrow> False | Some b \<Rightarrow> Suc b \<ge> Suc suc_bound\<close>
      using B checked_witnesses
      by (fold suc_bound; meson list_all2_witness)

    hence \<open>\<exists>w b. get_bound proof_steps step_limit w width B = Some b \<and> b \<ge> suc_bound\<close>
      by (metis (no_types, lifting) Suc_le_mono option.case_eq_if option.collapse)

    hence \<open>\<exists>b. pls_bound (list_to_vect ` set_vt B) b \<and> b \<ge> suc_bound\<close>
      by (metis B_lengths assms(2) get_bound_bound)

    thus \<open>pls_bound (list_to_vect ` set_vt B) suc_bound\<close>
      using pls_bound_def by auto
  qed

  have nrcmp_bounds:
    \<open>\<And>c. c \<in> set nrcmps \<Longrightarrow>
      pls_bound (apply_cmp c ` list_to_vect ` set_vt A) suc_bound\<close>
  proof -
    fix c assume c: \<open>c \<in> set nrcmps\<close>
    hence \<open>fst c < snd c \<and> snd c < width\<close>
      by (simp add: set_ocmp_list)
    hence c_range: \<open>fst c < width \<and> snd c < width\<close>
      by auto

    have \<open>pls_bound (list_to_vect ` apply_cmp_list c ` set_vt A) suc_bound\<close>
      using c B_bound set_vt_list by fastforce

    thus \<open>pls_bound (apply_cmp c ` list_to_vect ` set_vt A) suc_bound\<close>
      by (subst apply_cmp_as_apply_cmp_list'[where n=width];
          insert A_lengths c_range set_list_vt set_vt_list; auto)
  qed

  have rcmp_bounds:
    \<open>\<And>c. c \<in> set ocmps - set nrcmps \<Longrightarrow>
      pls_bound (apply_cmp c ` list_to_vect ` set_vt A) = pls_bound (list_to_vect ` set_vt A)\<close>
  proof -
    fix c assume c: \<open>c \<in> set ocmps - set nrcmps\<close>
    hence \<open>fst c < snd c \<and> snd c < width\<close>
      by (simp add: set_ocmp_list)
    hence c_range: \<open>fst c < width \<and> snd c < width\<close>
      by auto

    have \<open>is_redundant_cmp_vt c A\<close>
      using c by auto
    hence \<open>redundant_cmp c (list_to_vect ` set_vt A)\<close>
      using redundant_cmp_from_is_redundant_cmp_vt' A_lengths c_range
      by blast 
    
    thus \<open>pls_bound (apply_cmp c ` list_to_vect ` set_vt A) = pls_bound (list_to_vect ` set_vt A)\<close>
      using redundant_cmp_bound by blast
  qed

  have ocmp_bounds:
    \<open>\<And>c. c \<in> set ocmps \<Longrightarrow>
      pls_bound (apply_cmp c ` list_to_vect ` set_vt A) suc_bound \<or>
      pls_bound (apply_cmp c ` list_to_vect ` set_vt A) = pls_bound (list_to_vect ` set_vt A)\<close>
    using nrcmp_bounds rcmp_bounds
    by blast

  have \<open>pls_bound (list_to_vect ` set_vt A) bound\<close>
    unfolding suc_bound
  proof (rule ocmp_suc_bound)
    show \<open>\<not>inj_on weight (list_to_vect ` set_vt A)\<close>
      using is_unsorted bound_unsorted by blast
  next
    show \<open>\<And>v. v \<in> list_to_vect ` set_vt A \<Longrightarrow> fixed_len_bseq width v\<close>
      by (metis (full_types) A_lengths Ball_Collect list_to_vect_set_vt_fixed_width)
  next
    show  \<open>\<And>c. fst c < snd c \<and> snd c < width \<Longrightarrow>
      pls_bound (apply_cmp c ` list_to_vect ` set_vt A) suc_bound \<or>
      pls_bound (apply_cmp c ` list_to_vect ` set_vt A) = pls_bound (list_to_vect ` set_vt A)\<close>
      using ocmp_bounds
      by (simp add: set_ocmp_list)
  qed

  thus ?thesis
    using A_list_lengths step_checked_def by simp
qed

(***)

definition extremal_channels_vt :: \<open>vect_trie \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat list\<close> where
  \<open>extremal_channels_vt A n pol =
    filter (\<lambda>i. is_member_vt (map (\<lambda>j. (j = i) \<noteq> pol) [0..<n]) A) [0..<n]\<close>

lemma extremal_channels_vt_bound:
  assumes \<open>i \<in> set (extremal_channels_vt A n pol)\<close>
  shows \<open>i < n\<close>
proof -
  have \<open>i \<in> set [0..<n]\<close>
    using assms extremal_channels_vt_def by auto
  thus ?thesis
    by auto
qed

lemma extremal_channels_in_set:
  assumes \<open>i \<in> set (extremal_channels_vt A n pol)\<close>
  shows \<open>is_member_vt (map (\<lambda>j. (j = i) \<noteq> pol) [0..<n]) A\<close>
  using assms unfolding extremal_channels_vt_def
  by auto

lemma distinct_extremal_channels_vt:
  \<open>distinct (extremal_channels_vt A n pol)\<close>
  using distinct_filter extremal_channels_vt_def by simp

fun prune_extremal_vt :: \<open>bool \<Rightarrow> nat \<Rightarrow> vect_trie \<Rightarrow> vect_trie\<close> where
  \<open>prune_extremal_vt _ _ VtEmpty = VtEmpty\<close> |
  \<open>prune_extremal_vt True 0 (VtNode _ a_lo _) = a_lo\<close> |
  \<open>prune_extremal_vt False 0 (VtNode _ _ a_hi) = a_hi\<close> |
  \<open>prune_extremal_vt pol (Suc i) (VtNode a a_lo a_hi) =
    VtNode a (prune_extremal_vt pol i a_lo) (prune_extremal_vt pol i a_hi)\<close> 

fun remove_nth :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>remove_nth _ [] = []\<close> |
  \<open>remove_nth 0 (x # xs) = xs\<close> |
  \<open>remove_nth (Suc i) (x # xs) = x # remove_nth i xs\<close>

lemma remove_nth_as_take_drop:
  \<open>remove_nth i xs = take i xs @ drop (Suc i) xs\<close>
  by (induction i xs rule: remove_nth.induct; simp)

definition prune_nth :: \<open>nat \<Rightarrow> bseq \<Rightarrow> bseq\<close> where
  \<open>prune_nth n v i = (if i \<ge> n then v (Suc i) else v i)\<close>

lemma list_to_vect_remove_nth:
  assumes \<open>i < length xs\<close>
  shows \<open>list_to_vect (remove_nth i xs) = prune_nth i (list_to_vect xs)\<close>
  unfolding prune_nth_def list_to_vect_as_nth remove_nth_as_take_drop
  using assms
  by (auto simp add: nth_append min_def)

lemma list_to_vect_remove_nth_image:
  assumes \<open>i < n\<close> \<open>V \<subseteq> {xs. length xs = n}\<close>
  shows \<open>list_to_vect ` remove_nth i ` V = prune_nth i ` list_to_vect` V\<close>
  by (subst (1 2) image_image; rule image_cong; simp?;
      subst list_to_vect_remove_nth; insert assms; force)

lemma filter_hd_Cons_image:
  \<open>(#) x ` set_vt A \<inter> {xs. P (xs ! 0)} = (if P x then (#) x ` set_vt A else {})\<close>
  by (cases \<open>P x\<close>; auto simp add: Int_absorb2 image_subsetI)

lemma Cons_image_length:
  \<open>(#) x ` set_vt A \<subseteq> {xs. length xs = Suc n} = (set_vt A \<subseteq> {xs. length xs = n})\<close>
  using image_subset_iff by auto

lemma distrib_collect_bounded: \<open>{x \<in> A \<union> B. P x} = (A \<inter> {x. P x}) \<union> (B \<inter> {x. P x})\<close>
  by blast

lemma image_Cons_shift_filter_ith:
  \<open>(#) x ` set_vt a_lo \<inter> {xs. P (xs ! Suc i)} = (#) x ` (set_vt a_lo \<inter> {xs. P (xs ! i)})\<close>
  by auto

lemma set_vt_prune_extremal_vt:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close> \<open>i < n\<close>
  shows \<open>set_vt (prune_extremal_vt pol i A) = (\<lambda>xs. remove_nth i xs) ` {xs \<in> set_vt A. xs!i \<noteq> pol}\<close>
  using assms
proof (induction pol i A arbitrary: n rule: prune_extremal_vt.induct)
  case (1 uu uv)
  then show ?case
    by simp
next
  case (2 uw a_lo ux)
  then show ?case
    by (cases uw; simp add: remove_nth_as_take_drop drop_Suc Collect_conj_eq Collect_disj_eq
        Int_Un_distrib2 image_Un filter_hd_Cons_image image_image)
next
  case (3 uy uz a_hi)
  then show ?case
    by (cases uy; simp add: remove_nth_as_take_drop drop_Suc Collect_conj_eq Collect_disj_eq
        Int_Un_distrib2 image_Un filter_hd_Cons_image[where P=\<open>\<lambda>x. x\<close>] image_image)
next
  case (4 pol i a a_lo a_hi)
  then obtain n' where n': \<open>n = Suc n'\<close>
    using not0_implies_Suc by fastforce
  have a: \<open>a = False\<close>
    using 4 by auto

  have a_lo_length: \<open>set_vt a_lo \<subseteq> {xs. length xs = n'}\<close>
    using 4 n' unfolding a
    by (simp add: Cons_image_length)
  have a_hi_length: \<open>set_vt a_hi \<subseteq> {xs. length xs = n'}\<close>
    using 4 n' unfolding a
    by (simp add: Cons_image_length)

  have i: \<open>i < n'\<close>
    using 4 n' by simp

  have a_lo_IH:
    \<open>set_vt (prune_extremal_vt pol i a_lo) =
      (\<lambda>xs. remove_nth i xs) ` {xs \<in> set_vt a_lo. xs!i \<noteq> pol}\<close>
    using 4 a_lo_length i by blast

  have a_hi_IH:
    \<open>set_vt (prune_extremal_vt pol i a_hi) =
      (\<lambda>xs. remove_nth i xs) ` {xs \<in> set_vt a_hi. xs!i \<noteq> pol}\<close>
    using 4 a_hi_length i by blast

  have
    \<open>set_vt (prune_extremal_vt pol (Suc i) (VtNode False a_lo a_hi)) =
      ((#) False ` set_vt (prune_extremal_vt pol i a_lo)) \<union>
      ((#) True ` set_vt (prune_extremal_vt pol i a_hi))
      \<close>
    by simp

  then show ?case
    using 4 n' a_lo_length a_hi_length i
    unfolding a prune_extremal_vt.simps set_vt.simps a_lo_IH a_hi_IH image_image
      remove_nth.simps[symmetric] distrib_collect_bounded image_Un
      image_Cons_shift_filter_ith[where P=\<open>\<lambda>x. x \<noteq> pol\<close>] 
    by blast
qed

lemma prune_extremal_vt_lengths:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = Suc n}\<close> \<open>i < Suc n\<close>
  shows \<open>set_vt (prune_extremal_vt pol i A) \<subseteq> {xs. length xs = n}\<close>
  using assms
proof (induction pol i A arbitrary: n rule: prune_extremal_vt.induct)
  case (1 uu uv)
  then show ?case by simp
next
  case (2 uw a_lo ux)
  then show ?case
    by (cases uw; auto)
next
  case (3 uy uz a_hi)
  then show ?case
    by (cases uy; auto)
next
  case (4 pol i a a_lo a_hi)
  then obtain n' where n': \<open>n = Suc n'\<close>
    using not0_implies_Suc by fastforce
  then show ?case
    using 4
    by (cases pol; cases a; simp add: n' Cons_image_length)
qed


definition check_huffman :: \<open>(int \<Rightarrow> proof_step) \<Rightarrow> int \<Rightarrow> proof_step \<Rightarrow> bool\<close> where
  \<open>check_huffman proof_steps step_limit step = (case step_witnesses step of
    SuccessorWitnesses _ \<Rightarrow> False |
    HuffmanWitnesses pol witnesses \<Rightarrow>
      let
          width = (nat (step_width step));
          width' = nat.pred width;
          bound = (nat (step_bound step));
          A_list = step_vect_list step;
          A = vt_list A_list;
          extremal_channels = extremal_channels_vt A width pol;
          Bs = map (\<lambda>c. prune_extremal_vt pol c A) extremal_channels;
          bounds = map2 (\<lambda>B w. get_bound proof_steps step_limit w width' B) Bs witnesses;
          huffman_bound = sucmax_value_bound_huffman (mset (map the bounds))
      in
        width \<noteq> 0 \<and>
        list_all (\<lambda>xs. length xs = width) A_list \<and>
        witnesses \<noteq> [] \<and>
        length extremal_channels = length witnesses \<and>
        list_all (\<lambda>b. b \<noteq> None) bounds \<and>
        huffman_bound \<ge> bound
  )\<close>

lemma mset_ran_map_of_zip:
  assumes \<open>distinct xs\<close> \<open>length xs = length ys\<close>
  shows \<open>mset_ran (map_of (zip xs ys)) = mset ys\<close>
  using assms
  by (induction ys arbitrary: xs; unfold mset_ran_def; (simp; fail)?;
      metis dom_map_of_zip image_mset_map_of map_fst_zip map_snd_zip mset_set_set) 

lemma list_to_vect_prune_push:
  assumes \<open>set_vt A \<subseteq> {xs. length xs = n}\<close> \<open>i < n\<close>
  shows
    \<open>list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol} = {v \<in> list_to_vect ` set_vt A. (v i) \<noteq> pol}\<close>
  using assms(1) assms(2) list_to_vect_as_nth by auto

lemma extremal_list_to_vect:
  assumes \<open>i < n\<close>
  shows \<open>list_to_vect (map (\<lambda>j. (j = i) \<noteq> pol) [0..<n]) = apply_pol n pol ((\<noteq>) i)\<close>
  using assms unfolding invert_vect_def list_to_vect_as_nth
  by (cases pol; auto)

definition shift_channels :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>shift_channels n i j = (if Suc j = n then i else if j \<ge> i \<and> Suc j < n then Suc j else j)\<close>

definition unshift_channels :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>unshift_channels n i j =
    (if j = i then nat.pred n else if j > i \<and> j < n then nat.pred j else j)\<close>

lemma unshift_shift_inverse:
  assumes \<open>i < n\<close>
  shows \<open>unshift_channels n i (shift_channels n i j) = j\<close>
proof -
  have \<open>j < i \<Longrightarrow> unshift_channels n i (shift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by simp
  moreover have \<open>j \<ge> n \<Longrightarrow> unshift_channels n i (shift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by simp
  moreover have \<open>j = i \<Longrightarrow> unshift_channels n i (shift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by auto
  moreover have \<open>Suc j = n \<Longrightarrow> unshift_channels n i (shift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by auto
  moreover have \<open>j > i \<and> Suc j < n \<Longrightarrow> unshift_channels n i (shift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by simp
  ultimately show ?thesis by linarith
qed

lemma shift_unshift_inverse:
  assumes \<open>i < n\<close>
  shows \<open>shift_channels n i (unshift_channels n i j) = j\<close>
proof -
  have \<open>j < i \<Longrightarrow> shift_channels n i (unshift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by simp
  moreover have \<open>j \<ge> n \<Longrightarrow> shift_channels n i (unshift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by simp
  moreover have \<open>j = i \<Longrightarrow> shift_channels n i (unshift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by auto
  moreover have \<open>Suc j = n \<Longrightarrow> shift_channels n i (unshift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by (cases j; simp)
  moreover have \<open>j > i \<and> Suc j < n \<Longrightarrow> shift_channels n i (unshift_channels n i j) = j\<close>
    unfolding unshift_channels_def shift_channels_def using assms by (cases j; simp)
  ultimately show ?thesis by linarith
qed

lemma bij_shift_channels:
  assumes \<open>i < n\<close>
  shows \<open>bij (shift_channels n i)\<close>
  by (metis (full_types) assms bijI' shift_unshift_inverse unshift_shift_inverse)

lemma shift_channels_permutes:
  assumes \<open>i < n\<close>
  shows \<open>shift_channels n i permutes {..<n}\<close>
  using assms bij_shift_channels unfolding permutes_def
  by (metis Suc_lessD lessI lessThan_iff shift_channels_def shift_unshift_inverse
      unshift_shift_inverse)

lemma prune_nth_as_perm:
  assumes \<open>fixed_len_bseq n v\<close> \<open>v i\<close> \<open>i < n\<close>
  shows \<open>prune_nth i v = apply_perm (shift_channels n i) v\<close>
  unfolding prune_nth_def shift_channels_def apply_perm_def
  using assms fixed_len_bseq_def by auto

lemma inverted_prune_nth: 
  assumes \<open>i < Suc n\<close>
  shows \<open>invert_vect n (prune_nth i (invert_vect (Suc n) v)) = prune_nth i v\<close>
  unfolding invert_vect_def prune_nth_def
  using assms by auto

lemma prune_nth_as_perm_inverted:
  assumes \<open>fixed_len_bseq n v\<close> \<open>\<not>v i\<close> \<open>i < n\<close>
  shows
    \<open>prune_nth i v = invert_vect (nat.pred n) (apply_perm (shift_channels n i) (invert_vect n v))\<close>
proof -
  have \<open>fixed_len_bseq n (invert_vect n v)\<close>
    by (simp add: assms(1) invert_vect_fixed_width)
  moreover have \<open>(invert_vect n v) i\<close>
    by (simp add: assms(2) assms(3) invert_vect_def)
  ultimately have
    \<open>prune_nth i (invert_vect n v) = apply_perm (shift_channels n i) (invert_vect n v)\<close>
    by (simp add: assms(3) prune_nth_as_perm)
  moreover have \<open>invert_vect (nat.pred n) (prune_nth i (invert_vect n v)) = prune_nth i v\<close>
    using inverted_prune_nth[of i \<open>nat.pred n\<close> v]
    by (metis Suc_n_not_le_n assms(3) nat.split_sels(2) not_less0)
  ultimately show ?thesis
    by simp
qed

lemma prune_nth_as_perm_pol_image:
  assumes \<open>\<And>v. v \<in> V \<Longrightarrow> fixed_len_bseq n v\<close> \<open>\<And>v. v \<in> V \<Longrightarrow> v i = pol\<close> \<open>i < n\<close>
  shows
    \<open>prune_nth i ` V = apply_pol (nat.pred n) pol `
      apply_perm (shift_channels n i) ` apply_pol n pol ` V\<close>
  unfolding image_image
  by (intro image_cong; simp add: assms prune_nth_as_perm prune_nth_as_perm_inverted)

lemma pruned_bound_pol_using_prune_extremal_vt:
  assumes \<open>pls_bound (list_to_vect ` set_vt (prune_extremal_vt pol i A)) b\<close>
    \<open>i < n\<close>
    \<open>set_vt A \<subseteq> {xs. length xs = n}\<close>
    \<open>is_member_vt (map (\<lambda>j. (j = i) \<noteq> pol) [0..<n]) A\<close>
  shows \<open>pruned_bound_pol n pol (list_to_vect ` set_vt A) i b\<close>
proof -
  obtain n' where n': \<open>n = Suc n'\<close>
    using assms less_imp_Suc_add by blast 

  have f1: \<open>\<And>v. v \<in> list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol} \<Longrightarrow> fixed_len_bseq n v\<close>
    by (metis (mono_tags) Collect_subset assms(3) image_mono in_mono
        list_to_vect_set_vt_fixed_width mem_Collect_eq)

  hence \<open>\<And>v.
    v \<in> apply_pol n (\<not> pol) ` list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}
    \<Longrightarrow> fixed_len_bseq n v\<close>
    using invert_vect_fixed_width by auto

  hence \<open>\<And>v.
    v \<in> apply_perm (shift_channels n i) ` apply_pol n (\<not> pol) `
      list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}
    \<Longrightarrow> fixed_len_bseq n v\<close>
    by (meson apply_perm_fixed_width_image assms(2) shift_channels_permutes)

  moreover have \<open>\<And>v. v \<in> set_vt A \<and> v ! i \<noteq> pol \<Longrightarrow>
    apply_perm (shift_channels n i) (apply_pol n (\<not> pol) (
      list_to_vect v)) n'\<close>
    unfolding invert_vect_def list_to_vect_as_nth apply_perm_def shift_channels_def
    using n' assms(3) by force

  hence \<open>\<And>v.
    v \<in> apply_perm (shift_channels n i) ` apply_pol n (\<not> pol) `
      list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}
    \<Longrightarrow> v n'\<close>
    unfolding image_image by blast

  ultimately have f2: \<open>\<And>v.
    v \<in> apply_perm (shift_channels n i) ` apply_pol n (\<not> pol) `
      list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}
    \<Longrightarrow> fixed_len_bseq n' v\<close>
    unfolding n' fixed_len_bseq_def
    by (metis (no_types, lifting) Suc_leI le_imp_less_or_eq)


  have \<open>set_vt (prune_extremal_vt pol i A) = remove_nth i ` {xs \<in> set_vt A. xs ! i \<noteq> pol}\<close>
    using assms
    by (subst set_vt_prune_extremal_vt[where n=n]; simp)
  hence \<open>pls_bound (list_to_vect ` remove_nth i ` {xs \<in> set_vt A. xs ! i \<noteq> pol}) b\<close>
    using assms by simp
  hence \<open>pls_bound (prune_nth i ` list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}) b\<close>
    by (subst (asm) list_to_vect_remove_nth_image[where n=n]; insert Ball_Collect assms; auto)
  hence
    \<open>pls_bound (apply_pol n' (\<not>pol) `
      apply_perm (shift_channels n i) `
      apply_pol n (\<not>pol) `
      list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}) b\<close>
    by (subst (asm) prune_nth_as_perm_pol_image[where n=n and pol=\<open>\<not>pol\<close>];
        insert assms(2, 3) fixed_len_bseq_list_to_vect list_to_vect_as_nth; auto simp add: n')
  hence
    \<open>pls_bound (
      apply_perm (shift_channels n i) `
      apply_pol n (\<not>pol) `
      list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}) b\<close>
    by (subst (asm) apply_pol_bound_iff; simp add: f2)
  hence
    \<open>pls_bound (
      apply_pol n (\<not>pol) `
      list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}) b\<close>
    by (subst (asm) permuted_bounds_iff[symmetric]; simp add: assms(2) bij_shift_channels)
  hence
    \<open>pls_bound (list_to_vect ` {xs \<in> set_vt A. xs ! i \<noteq> pol}) b\<close>
    by (subst (asm) apply_pol_bound_iff; simp add: f1)
  hence *: \<open>pls_bound {v \<in> list_to_vect ` set_vt A. (v i) \<noteq> pol} b\<close>
    using list_to_vect_prune_push assms by simp

  have \<open>apply_pol n pol ((\<noteq>) i) \<in> list_to_vect ` set_vt A\<close>
    using assms is_member_vt_as_member_set_vt
    by (subst extremal_list_to_vect[symmetric]; simp)
  hence extremal: \<open>(\<noteq>) i \<in> apply_pol n pol ` list_to_vect ` set_vt A\<close>
    by (subst apply_pol_invol[where n=n and pol=pol and v=\<open>(\<noteq>) i\<close>, symmetric]; blast)
   

  have \<open>pls_bound {v \<in> apply_pol n pol ` list_to_vect ` set_vt A. \<not> v i} b\<close>
  proof (cases pol)
    case True
    then show ?thesis
      using * by auto
  next
    case False
    have \<open>pls_bound {v \<in> list_to_vect ` set_vt A. v i} b\<close>
      using * False by auto
    hence \<open>pls_bound (invert_vect n ` {v \<in> list_to_vect ` set_vt A. v i}) b\<close>
      by (intro inverted_bound; (simp; fail)?;
          metis (mono_tags) Ball_Collect Collect_subset assms(3) in_mono
          list_to_vect_set_vt_fixed_width)

    moreover have
      \<open>invert_vect n ` {v \<in> list_to_vect ` set_vt A. v i} =
        {v \<in> invert_vect n ` list_to_vect ` set_vt A. \<not> v i}\<close>
      by (intro set_eqI iffI; unfold invert_vect_def; simp; insert assms(2); blast)

    finally show ?thesis
      by (cases pol; simp add: False)
  qed

  hence \<open>pruned_bound (apply_pol n pol ` list_to_vect ` set_vt A) i b\<close>
    unfolding pruned_bound_def
    using extremal by simp

  thus ?thesis
    using pruned_bound_pol_def
    by simp
qed

lemma check_huffman_step_checked:
  assumes \<open>check_huffman proof_steps step_limit step\<close>
    \<open>\<And>step. 0 \<le> step \<and> step < step_limit \<Longrightarrow> step_checked (proof_steps step)\<close>
  shows \<open>step_checked step\<close>
proof -

  obtain witnesses pol where witnesses_pol: \<open>step_witnesses step = HuffmanWitnesses pol witnesses\<close>
    using assms(1) check_huffman_def
    by (metis (no_types, lifting) proof_step_witnesses.case_eq_if proof_step_witnesses.collapse(1))

  define width where \<open>width = nat (step_width step)\<close>
  define width' where \<open>width' = nat.pred width\<close>
  define bound where \<open>bound = nat (step_bound step)\<close>
  define A_list where \<open>A_list = step_vect_list step\<close>
  define A where \<open>A = vt_list A_list\<close>
  define extremal_channels where \<open>extremal_channels = extremal_channels_vt A width pol\<close>
  define Bs where \<open>Bs = map (\<lambda>c. prune_extremal_vt pol c A) extremal_channels\<close>
  define bounds where
    \<open>bounds = map2 (\<lambda>B w. get_bound proof_steps step_limit w width' B) Bs witnesses\<close>
  define huffman_bound where \<open>huffman_bound = sucmax_value_bound_huffman (mset (map the bounds))\<close>

  define D where \<open>D = map_of (zip extremal_channels (map the bounds))\<close>

  note width_def[simp] width'_def[simp] bound_def[simp] A_list_def[simp] A_def[simp] 
  note extremal_channels_def[simp] Bs_def[simp] bounds_def[simp] huffman_bound_def[simp] D_def[simp]

  have checked: \<open>
    width \<noteq> 0 \<and>
    list_all (\<lambda>xs. length xs = width) A_list \<and>
    witnesses \<noteq> [] \<and>
    length extremal_channels = length witnesses \<and>
    list_all (\<lambda>b. b \<noteq> None) bounds \<and>
    huffman_bound \<ge> bound\<close>
    using assms(1)
    unfolding witnesses_pol check_huffman_def
    unfolding width_def bound_def A_list_def A_def extremal_channels_def Bs_def bounds_def
      huffman_bound_def 
    unfolding Let_def
    by auto

  have A_list_lengths: \<open>list_all (\<lambda>xs. length xs = width) A_list\<close>
    using checked by simp
  hence A_lengths: \<open>set_vt A \<subseteq> {xs. length xs = width}\<close>
    by (simp add: list.pred_set set_vt_list subsetI)

  have witnesses_length: \<open>length extremal_channels = length witnesses\<close>
    using checked by simp

  have nonempty_witnesses: \<open>witnesses \<noteq> []\<close>
    using checked by simp

  have huffman_bound_bound: \<open>huffman_bound \<ge> bound\<close>
    using checked by auto

  have Bs_length: \<open>length Bs = length witnesses\<close>
    by (simp add: witnesses_length del: extremal_channels_def)
  hence bounds_length: \<open>length bounds = length witnesses\<close>
    by simp
  hence \<open>length (zip extremal_channels (map the bounds)) = length witnesses\<close>
    by auto
  hence card_dom_D: \<open>card (dom D) = length witnesses\<close>
    unfolding D_def
    by (subst dom_map_of_zip; (insert witnesses_length; auto)?;
        subst distinct_card; insert distinct_extremal_channels_vt witnesses_length; simp)

  have width': \<open>width = Suc width'\<close>
    by (metis Suc_n_not_le_n checked nat.split_sels(2) width'_def)

  have \<open>pls_bound (list_to_vect ` set_vt A) (sucmax.value_bound_mset (mset_ran D))\<close>
  proof (rule pls_bound_from_pruned_bounds_pol[where n=width and pol=pol and B=D])
    fix v assume v: \<open>v \<in> list_to_vect ` set_vt A\<close>
    thus \<open>fixed_len_bseq width v\<close>
      by (metis A_lengths Ball_Collect v list_to_vect_set_vt_fixed_width)
  next
    show \<open>finite (dom D)\<close>
      unfolding D_def
      using finite_dom_map_of by blast
  next
    show \<open>dom D \<noteq> {}\<close>
      using card_dom_D nonempty_witnesses by auto
  next
    have \<open>\<forall>c \<in> dom D. pruned_bound_pol width pol (list_to_vect ` set_vt A) c (the (D c))\<close>
    proof
      fix c assume \<open>c \<in> dom D\<close>
      hence c_set: \<open>c \<in> set extremal_channels\<close>
        using witnesses_length by auto
      then obtain i where c_def: \<open>c = extremal_channels!i\<close>
        and i_bound: \<open>i < length extremal_channels\<close>
        by (metis in_set_conv_nth)

      have c_bound: \<open>c < width\<close>
        using extremal_channels_vt_bound c_set extremal_channels_def by blast

      define w where \<open>w = witnesses!i\<close>
      define B where \<open>B = prune_extremal_vt pol c A\<close>

      have B_alt: \<open>B = Bs!i\<close>
        unfolding Bs_def B_def c_def
        using witnesses_length i_bound nth_map[of i extremal_channels]
        by simp

      have length_zip: \<open>length (zip Bs witnesses) = length witnesses\<close>
        using Bs_length by auto

      have
        \<open>bounds!i =
          (\<lambda>(x, y). get_bound proof_steps step_limit y width' x) (zip Bs witnesses ! i)\<close>
        unfolding bounds_def
        using nth_map[of i \<open>zip Bs witnesses\<close>] length_zip witnesses_length i_bound
        by simp
      also have \<open>\<dots> = get_bound proof_steps step_limit w width' B\<close>
        unfolding B_alt
        using nth_zip[of i Bs witnesses]
        using i_bound w_def witnesses_length by auto
      ultimately have get_bound_i: \<open>bounds!i = get_bound proof_steps step_limit w width' B\<close>
        by simp

      have \<open>bounds!i \<noteq> None\<close>
        by (metis (full_types) bounds_length checked i_bound list_all_length)
      then obtain b where b_def: \<open>bounds!i = Some b\<close>
        by blast
      hence b_alt: \<open>b = the (get_bound proof_steps step_limit w width' B)\<close>
        using get_bound_i
        by (metis option.sel) 

      have \<open>D c = Some b\<close>
        unfolding c_def D_def b_def[symmetric]
        by (subst map_of_zip_nth;
            insert b_def i_bound witnesses_length; auto simp add: distinct_extremal_channels_vt)
      hence the_D_c: \<open>the (D c) = b\<close>
        using b_alt by simp

      have B_lengths: \<open>set_vt B \<subseteq> {xs. length xs = width'}\<close>
        unfolding B_def using A_lengths width' c_bound
        by (intro prune_extremal_vt_lengths; auto)

      have \<open>pls_bound (list_to_vect ` set_vt B) b\<close>
        using b_def assms(2) B_lengths
        unfolding get_bound_i
        by (subst get_bound_bound[
              where step_limit=step_limit and proof_steps=proof_steps
                and witness=w and n=width']; simp)

      hence \<open>pruned_bound_pol width pol (list_to_vect ` set_vt A) c b\<close>
        using B_def c_bound A_lengths extremal_channels_in_set c_set extremal_channels_def
        by (intro pruned_bound_pol_using_prune_extremal_vt[where i=c and n=width]; auto)

      thus \<open>pruned_bound_pol width pol (list_to_vect ` set_vt A) c (the (D c))\<close>
        using the_D_c by simp
    qed
    thus \<open>pruned_bounds_pol width pol (list_to_vect ` set_vt A) D\<close>
      unfolding pruned_bounds_pol_def by auto
  qed

  moreover have \<open>mset_ran D = mset (map the bounds)\<close>
    by (simp del: bounds_def; subst mset_ran_map_of_zip;
        insert distinct_extremal_channels_vt witnesses_length bounds_length;
        auto simp del: bounds_def)
  hence \<open>bound \<le> sucmax_value_bound_huffman (mset_ran D)\<close>
    using huffman_bound_bound
    by simp
  hence \<open>bound \<le> sucmax.value_bound_mset (mset_ran D)\<close>
    by (simp add: sucmax.value_bound_huffman_mset)
  ultimately have \<open>pls_bound (list_to_vect ` set_vt A) bound\<close>
    by (meson dual_order.trans pls_bound_def)

  thus ?thesis
    using A_list_lengths step_checked_def by simp
qed

(***)

definition check_step :: \<open>(int \<Rightarrow> proof_step) \<Rightarrow> int \<Rightarrow> proof_step \<Rightarrow> bool\<close> where
  \<open>check_step proof_steps step_limit step = (case step_witnesses step of
    SuccessorWitnesses _ \<Rightarrow> check_successors proof_steps step_limit step  |
    HuffmanWitnesses _ _ \<Rightarrow> check_huffman proof_steps step_limit step)\<close>

lemma check_step_step_checked:
  assumes \<open>check_step proof_steps step_limit step\<close>
    \<open>\<And>step. 0 \<le> step \<and> step < step_limit \<Longrightarrow> step_checked (proof_steps step)\<close>
  shows \<open>step_checked step\<close>
proof (cases \<open>step_witnesses step\<close>)
  case (HuffmanWitnesses _ _)
  hence \<open>check_huffman proof_steps step_limit step\<close>
    using assms(1) check_step_def by auto
  then show ?thesis
    using assms(2) check_huffman_step_checked by blast 
next
  case (SuccessorWitnesses x2)
  hence \<open>check_successors proof_steps step_limit step\<close>
    using assms(1) check_step_def by auto
  then show ?thesis
    using assms(2) check_successors_step_checked by blast 
qed

(***)

lemma check_induct:
  assumes \<open>list_all (\<lambda>i. check_step proof_steps (int i) (proof_steps (int i))) [0..<n]\<close>
  shows \<open>\<And>step. 0 \<le> step \<and> step < int n \<Longrightarrow> step_checked (proof_steps step)\<close>
  using assms
proof (induction n)
  case 0
  then show ?case
    by linarith
next
  case (Suc n)
  have \<open>list_all (\<lambda>i. check_step proof_steps (int i) (proof_steps (int i))) [0..<n]\<close>
    using Suc.prems(2) by auto
  hence *: \<open>\<And>step. 0 \<le> step \<and> step < int n \<Longrightarrow> step_checked (proof_steps step)\<close>
    using Suc.IH by blast
  
  have \<open>check_step proof_steps (int n) (proof_steps (int n))\<close>
    using Suc by simp
  hence \<open>step_checked (proof_steps (int n))\<close>
    by (rule check_step_step_checked[where step_limit=\<open>int n\<close> and proof_steps=proof_steps];
        simp add: *)
  thus \<open>\<And>step. 0 \<le> step \<and> step < int (Suc n) \<Longrightarrow> step_checked (proof_steps step)\<close>
    using * nat_less_iff not_less_less_Suc_eq by fastforce
qed

definition par :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b\<close> where
  \<open>par a b = b\<close>

fun par_range_all :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>par_range_all f lo n = (
    if n < 1000 then list_all f [lo..<lo + n] else
      let n' = n div 2;
          a = par_range_all f lo n';
          b = par_range_all f (lo + n') (n - n')
      in (par b a) \<and> b)\<close>

declare par_range_all.simps[simp del]

lemma par_range_all_iff_list_all:
  \<open>par_range_all f lo n = list_all f [lo..<lo + n]\<close>
proof (induction f lo n rule: par_range_all.induct)
  case (1 f lo n)
  define n' where \<open>n' = n div 2\<close>
  hence n'_range: \<open>n' \<le> n\<close>
    by simp

  show ?case
  proof (cases \<open>n < 1000\<close>)
    case True
    then show ?thesis
      using 1 by (simp add: par_range_all.simps)
  next
    case False

    have \<open>par_range_all f lo n' = list_all f [lo..<lo + n']\<close>
      using 1 False n'_def
      by simp 

    moreover have \<open>par_range_all f (lo + n') (n - n') = list_all f [lo + n'..<lo + n' + (n - n')]\<close>
      using 1 False n'_def
      by simp

    ultimately have \<open>par_range_all f lo n = list_all f [lo..<lo + n' + (n - n')]\<close>
      using False
      by (subst par_range_all.simps; simp;
          metis le_add1 list_all_append n'_def par_def upt_add_eq_append)

    then show ?thesis
      using n'_range by simp
  qed
qed


lemma par_range_all_iff_list_all':
  \<open>par_range_all f 0 n = list_all f [0..<n]\<close>
  using par_range_all_iff_list_all by simp

definition check_proof :: \<open>proof_cert \<Rightarrow> bool\<close> where
  \<open>check_proof cert = (
    let
      steps = cert_step cert;
      n = cert_length cert
    in n \<ge> 0 \<and> par_range_all (\<lambda>i. check_step steps (int i) (steps (int i))) 0 (nat n))\<close>

lemma check_proof_spec:
  assumes \<open>check_proof cert\<close>
  shows \<open>\<And>step. 0 \<le> step \<and> step < cert_length cert \<Longrightarrow> step_checked (cert_step cert step)\<close>
  using assms unfolding check_proof_def par_range_all_iff_list_all'
  by (cases \<open>cert_length cert \<ge> 0\<close>; linarith?; metis check_induct int_nat_eq)

definition check_proof_get_bound :: \<open>proof_cert \<Rightarrow> (int \<times> int) option\<close> where
  \<open>check_proof_get_bound cert = (
    if check_proof cert \<and> cert_length cert > 0
    then
      let last_step = cert_step cert (cert_length cert - 1)
      in Some (step_width last_step, step_bound last_step)
    else None
  )\<close>

lemma step_checked_bound:
  assumes \<open>step_checked step\<close>
  shows \<open>partial_lower_size_bound {v. fixed_len_bseq (nat (step_width step)) v} (nat (step_bound step))\<close>
proof -
  define A where \<open>A = list_to_vect ` set_vt (vt_list (step_vect_list step))\<close>
  hence \<open>pls_bound A (nat (step_bound step))\<close>
    using assms step_checked_def by auto
  moreover have \<open>A \<subseteq> {v. fixed_len_bseq (nat (step_width step)) v}\<close>
    by (metis (no_types, lifting) A_def Ball_Collect assms list.pred_set
        list_to_vect_set_vt_fixed_width set_vt_list step_checked_def)
  ultimately have
    \<open>pls_bound {v. fixed_len_bseq (nat (step_width step)) v} (nat (step_bound step))\<close>
    using bound_mono_subset by blast
  thus ?thesis
    by (metis (full_types) mem_Collect_eq pls_bound_implies_lower_size_bound)
qed

lemma check_proof_get_bound_spec:
  assumes \<open>check_proof_get_bound cert = Some (width, bound)\<close>
  shows \<open>lower_size_bound (nat width) (nat bound)\<close>
proof -
  have checked: \<open>check_proof cert \<and> cert_length cert > 0\<close>
    using assms unfolding check_proof_get_bound_def
    by (meson option.distinct(1))

  define last_step where \<open>last_step = cert_step cert (cert_length cert - 1)\<close>
  hence \<open>step_checked last_step\<close>
    using checked check_proof_spec
    by simp

  thus ?thesis
    by (metis Pair_inject assms check_proof_get_bound_def checked last_step_def
        option.inject step_checked_bound lower_size_bound_def)
qed

end
