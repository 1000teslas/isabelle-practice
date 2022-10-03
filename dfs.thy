theory dfs
imports
Main
Simpl.StateSpace
Simpl.Vcg
Graph_Theory.Digraph
"HOL-Statespace.StateSpaceSyntax"
begin

hoarestate ('a, 'b) vars =
  G :: "('a, 'b) pre_digraph"
  root :: 'a
  discovered :: "'a set"

  stack :: "'a list"
  v :: 'a

context vars
begin

definition dfs where
"dfs G \<equiv>
  \<acute>discovered :== {};;
  \<acute>stack :== [\<acute>root];;
  WHILE \<acute>stack \<noteq> []
  INV \<lbrace> \<acute>G = G
        \<and> fin_digraph \<acute>G
        \<and> set \<acute>stack \<subseteq> verts \<acute>G
        \<and> {v. reachable \<acute>G \<acute>root v} = \<acute>discovered \<union> (\<Union>v \<in> set \<acute>stack. {w. reachable \<acute>G v w})
        \<and> (\<forall>v \<in> \<acute>discovered. \<forall>w. dominates \<acute>G v w \<longrightarrow> w \<in> \<acute>discovered \<union> set \<acute>stack)
      \<rbrace>
  VAR (card ({v. reachable \<acute>G \<acute>root v} - \<acute>discovered) <*MLEX*> (MEASURE length \<acute>stack))
  DO
    \<acute>v :== hd \<acute>stack;;
    \<acute>stack :== tl \<acute>stack;;
    IF \<acute>v \<notin> \<acute>discovered THEN
      \<acute>discovered :== insert \<acute>v \<acute>discovered;;
      \<acute>stack :== (SOME ws. set ws = {head \<acute>G e | e. e \<in> out_arcs \<acute>G \<acute>v}) @ \<acute>stack
    FI
  OD
"

lemma dfs_partial1:
assumes a1: "wf_digraph G"
and a2: "reachable G v x"
shows
"\<lbrakk> \<forall>v\<in>discovered. \<forall>w. v \<rightarrow>\<^bsub>G\<^esub> w \<longrightarrow> w \<in> discovered \<or> w \<in> set stack
; \<forall>xa\<in>set (tl stack). \<not> xa \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x
; v \<in> discovered
; v = hd stack
\<rbrakk> \<Longrightarrow> (v, x) \<in> rtrancl {(u, v). (u, v) \<in> arcs_ends G \<and> {u, v} \<subseteq> discovered}"
  apply (induct rule: wf_digraph.reachable_induct[where G=G and u=v])
  using a1 a2 apply blast+
  apply clarsimp
  apply (subgoal_tac "\<forall>xa\<in>set (tl stack). \<not> xa \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x")
   apply clarsimp
   apply (subgoal_tac "x \<in> discovered")
    apply (frule_tac x=x in bspec, simp)
    apply (erule_tac x=y in allE)
    apply (metis (no_types, lifting) a1 case_prod_conv insert_iff list.collapse list.sel(2) list.simps(15) mem_Collect_eq rtrancl.simps wf_digraph.adj_in_verts(2) wf_digraph.reachable_conv')
  using rtrancl.cases apply fastforce
  apply (meson a1 wf_digraph.reachable_adjI wf_digraph.reachable_trans)
  done

lemma dfs_total: "\<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>root \<in> verts \<acute>G \<and> fin_digraph \<acute>G \<rbrace> dfs G \<lbrace> \<acute>G = G \<and> \<acute>discovered = {v. reachable \<acute>G \<acute>root v} \<rbrace>"
(*
apply (rule TerminationPartial)
*)
unfolding dfs_def apply (vcg; clarsimp simp add: fin_digraph.axioms(1) wf_digraph.reachable_refl)
  apply (subgoal_tac "set (SOME ws. set ws = {pre_digraph.head G e |e. e \<in> arcs G \<and> tail G e = hd stack})
  = {pre_digraph.head G e |e. e \<in> arcs G \<and> tail G e = hd stack}")
  apply clarsimp
  apply (thin_tac "set (SOME ws. set ws = {pre_digraph.head G e |e. e \<in> arcs G \<and> tail G e = hd stack}) =
          {pre_digraph.head G e |e. e \<in> arcs G \<and> tail G e = hd stack}")
  apply (safe; clarsimp?)
              apply (metis Diff_insert0 card_Diff_insert diff_le_self nat_less_le)
             apply (subgoal_tac "hd stack \<in> discovered")
              apply blast
             apply (subgoal_tac "discovered \<union> (\<Union>v\<in>set stack. Collect (reachable G v)) - insert (hd stack) discovered
                        \<subseteq> discovered \<union> (\<Union>v\<in>set stack. Collect (reachable G v)) - discovered")
              apply (subgoal_tac "discovered \<union> (\<Union>v\<in>set stack. Collect (reachable G v)) - insert (hd stack) discovered
                         = discovered \<union> (\<Union>v\<in>set stack. Collect (reachable G v)) - discovered")
               apply (smt (verit, del_insts) Diff_iff UN_insert Un_iff fin_digraph.axioms(1) insertI1 list.collapse list.simps(15) mem_Collect_eq subsetD wf_digraph.reachable_refl)
              apply (subgoal_tac "finite (discovered \<union> (\<Union>v\<in>set stack. Collect (reachable G v)) - discovered)")
               apply (meson psubsetI psubset_card_mono)
              apply (subgoal_tac "finite (Collect (reachable G root))")
               apply (metis finite_Diff)
              apply (metis fin_digraph_axioms_def fin_digraph_def finite_subset mem_Collect_eq reachable_in_vertsE subsetI)
             apply fastforce
            apply (simp add: fin_digraph.axioms(1) wf_digraph.head_in_verts)
           apply (meson in_mono list.set_sel(2))
          apply (metis insertE list.collapse list.simps(15) pre_digraph.converse_reachable_cases reachableE)
         apply (meson fin_digraph_def in_mono list.set_sel(1) wf_digraph.reachable_refl)
        apply (metis arc_to_ends_def fin_digraph.axioms(1) hd_in_set wf_digraph.adj_reachable_trans wf_digraph.dominatesI)
       apply (meson list.set_sel(2))
      apply auto[1]
     apply (metis insertE list.collapse list.simps(15))
    apply (meson in_mono list.set_sel(2))
   apply (subgoal_tac "v = hd stack")
    apply clarsimp
    apply (subgoal_tac "(hd stack, x) \<in> rtrancl {(u, v). (u, v) \<in> arcs_ends G \<and> {u, v} \<subseteq> discovered}")
     apply (erule_tac ?a1.0="hd stack" in rtrancl.cases; clarsimp)
    apply (subgoal_tac "wf_digraph G")
     apply (rule dfs_partial1; blast)
  using fin_digraph.axioms(1) apply fastforce
     apply (metis insertE list.collapse list.simps(15))
    apply (meson list.set_sel(2))
   apply (metis insertE list.collapse list.simps(15))
  apply (subgoal_tac "finite {pre_digraph.head G e |e. e \<in> arcs G \<and> tail G e = hd stack}")
   apply (meson finite_list someI_ex)
  using finite_image_set fin_digraph.finite_arcs finite_subset apply fastforce
  done

end

end