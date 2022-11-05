import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*


object Lab03 extends lisa.Main{

  private val x = VariableLabel("x")
  private val x1 = VariableLabel("x1")
  private val x0 = VariableLabel("x0")

  private val y = VariableLabel("y")
  private val z = VariableLabel("z")
  private val Q = SchematicPredicateLabel("P", 1)
  private val H = SchematicPredicateLabel("R", 2)

  ///////////////////////
  // First Order Logic //
  ///////////////////////


  // you may need to use the following proof tactics:
  // have("_____ |- _____") by Restate
  // have("_____ |- _____") by Trivial
  // have("_____ |- _____") by Weakening     (Restate and Weakening can replace all single-premise Sequent Calculus proof steps. Try them before using Trivial.)
  // have("_____ |- _____") by LeftForall(term)(premise)
  // have("_____ |- _____") by RightForall(premise)
  // have("_____ |- _____") by LeftExists(premise)
  // have("_____ |- _____") by RightExists(term)
  // have("_____ |- _____") by InstantiateForall(term*)(premise)
  // have("_____ |- _____") by LeftOr(premise1, premise2)
  // have("_____ |- _____") by LeftImplies(premise1, premise2)
  // have("_____ |- _____") by RightIff(premise1, premise2)
  // have("_____ |- _____") by RightAnd(premise1, premise2)
  // have("_____ |- _____") by Cut(premise1, premise2)
  // andThen(applySubst(P <=> Q))      (replaces instances of P by instances of Q in the current sequent)
  // andThen(applySubst(x = y))        (replaces instances of x by instances of y in the current sequent)
  //
  // andThen("_____ |- _____") by Tactic    may be use instead of "have" and (premise). In that case, the premise is replaced by the previously proven step.
  //
  //Details about Sequent Calculus in LISA can be found here: https://github.com/epfl-lara/lisa/blob/main/Reference%20Manual/lisa.pdf

  THEOREM("Ex_All_implies_All_Ex") of "∃'x. ∀'y. 'R('x, 'y) ⊢ ∀'y. ∃'x. 'R('x, 'y)" PROOF {
    //TODO
    have("'R('x0, 'y) ⊢ 'R('x0, 'y)") by Hypothesis
    andThen ("∀'y. 'R('x0, 'y) |- 'R('x0, 'y)") by LeftForall(y)
    andThen ("∀'y. 'R('x0, 'y) |- ∃'x0.'R('x0, 'y)") by RightExists(x0)
    andThen ("∃'x0. ∀'y. 'R('x0, 'y) |- ∃'x0.'R('x0, 'y)") by LeftExists
    andThen ("∃'x. ∀'y. 'R('x, 'y) |- ∃'x. 'R('x, 'y)") by Restate
    andThen ("∃'x. ∀'y. 'R('x, 'y) |- ∀'y. ∃'x.'R('x, 'y)") by RightForall
    showCurrentProof()

  }
  show

  THEOREM("Unique_Exist_Variant") of "∃'y. ∀'x. ('P('x) ⇔ 'x='y) ⊢ ∃'y. 'P('y) ∧ (∀'x. 'P('x) ⇒ 'x='y)" PROOF {
    
    have("⊢'x='x") by RightRefl
    val left1 = andThen("⊢'x='x ; 'P('x) ; 'P('x)") by Weakening
    have("'P('x) ⊢ 'P('x)") by Hypothesis
    val right1 = andThen("'P('x) ⊢ 'P('x) ; 'P('x)") by Weakening

    val left2 =have("'x='x  ⇒  'P('x) ⊢ 'P('x) ;  'P('x)") by LeftImplies(left1, right1)
    have("⊢'x='x") by RightRefl
    val left3= andThen("'x='x ⊢ ('x='x) ; 'P('x)") by Weakening
    have("'P('x) ⊢ 'P('x)") by Hypothesis
    val right3 = andThen("('x='x) ; 'P('x) ⊢'P('x) ") by Weakening
    // have("('x='x) ∧ ('x='x) ∧ (('x='x)  ⇒  'P('x)) ⊢'P('x) ∨ 'P('x) ") by LeftImplies(left3, right3)
    val right2 =  have("('x='x) ; (('x='x)  ⇒  'P('x)) ⊢ 'P('x) ")  by LeftImplies(left3, right3)

    have("('P('x) ⇒ 'x='x) ; ('x='x ⇒ 'P('x)) ⊢'P('x)") by LeftImplies(left2, right2)
    andThen("'P('x) ⇔ 'x='x ⊢'P('x)") by Restate
    val leftBig = andThen ("∀'x0. 'P('x0) ⇔ 'x0='x ⊢'P('x)") by LeftForall(x)



    have("'P('x0) ⊢ 'P('x0)") by Hypothesis
    val left4 = andThen("'P('x0) ; ('x0='x ⇒ 'P('x0)) ⊢ 'P('x0) ; 'x0='x ") by Weakening
    have("'x0='x ⊢ 'x0='x") by Hypothesis
    val right4 = andThen("'P('x0) ; ('x0='x) ; ('x0='x ⇒ 'P('x0)) ⊢ 'x0='x ") by Weakening
    have("'P('x0) ; ('P('x0) ⇒ 'x0='x) ; ('x0='x ⇒ 'P('x0)) ⊢'x0='x") by LeftImplies(left4, right4)
    andThen("'P('x0) ; ('P('x0) ⇔ 'x0='x)  ⊢'x0='x") by Restate
    andThen("('P('x0) ⇔ 'x0='x)  ⊢ 'P('x0) ⇒ 'x0='x") by RightImplies
    andThen("∀'x0. ('P('x0) ⇔ 'x0='x) ⊢ 'P('x0) ⇒ 'x0='x") by LeftForall(x0)
    andThen("∀'x0. ('P('x0) ⇔ 'x0='x) ⊢∀ 'x0. 'P('x0) ⇒ 'x0='x") by RightForall
    val rightBig = andThen("∀'x0. ('P('x0) ⇔ 'x0='x) ⊢∀ 'x0. 'P('x0) ⇒ 'x0='x") by Restate


    have("∀'x0. ('P('x0) ⇔ 'x0='x) ⊢ 'P('x) ∧ (∀'x0. 'P('x0) ⇒ 'x0='x)") by RightAnd(leftBig, rightBig)
    andThen("∀'x0. ('P('x0) ⇔ 'x0='x) ⊢ ∃'x. 'P('x) ∧ (∀'x0. 'P('x0) ⇒ 'x0='x)") by RightExists(x)
    andThen("∀'x0. ('P('x0) ⇔ 'x0='x) ⊢ ∃'y. 'P('y) ∧ (∀'x0. 'P('x0) ⇒ 'x0='y)") by Restate
    andThen("∃'x. ∀'x0. ('P('x0) ⇔ 'x0='x) ⊢ ∃'y. 'P('y) ∧ (∀ 'x0. 'P('x0) ⇒ 'x0='y)") by LeftExists
    andThen("∃'y. ∀'x0. ('P('x0) ⇔ 'x0='y) ⊢ ∃'y. 'P('y) ∧ (∀ 'x0. 'P('x0) ⇒ 'x0='y)") by Restate
    andThen("∃'y. ∀'x. ('P('x) ⇔ 'x='y) ⊢ ∃'y. 'P('y) ∧ (∀ 'x. 'P('x) ⇒ 'x='y)") by Restate
    showCurrentProof()
  }
  show




  // ////////////////
  // // Set Theory //
  // ////////////////


  // //This one is given as an example
  // THEOREM("Subset_Reflexivity") of " ⊢ subset_of('x, 'x)" PROOF {
  //   val subs = have(subsetAxiom) //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x ⊆ 'y
  //                //shows the current sequent calculus proof
  //   val r1 = andThen(() |- forall(z, in(z, x) ==> in(z, x)) <=> subset(x, x)) by InstantiateForall(x, x)    //InstantiateForall will instantiate a universally bound formula on the right of a sequent with the given terms.
   
  //   have(() |- in(z, x) ==> in(z, x)) by Restate                                                           //Restate solves automatically a class of easy proposition, including reflexivity of equality, alpha-equivalence of formulas, and some propositional logic properties
  //   andThen(() |- forall(z, in(z, x) ==> in(z, x))) by RightForall
  //   andThen(applySubst(forall(z, in(z, x) ==> in(z, x)) <=> subset(x, x)))                                  //applySubst will replace  occurences of the left-hand-side of the equivalence given in argument by the right-hand-side in the current sequent.
  //   Discharge(r1)  
  //   showCurrentProof()                                                                                         //Discharge removes the formula proven on the right of sequent r1 from the left-hand-side of the current sequent
  // }

  // THEOREM("Subset_Transitivity") of "subset_of('x, 'y); subset_of('y, 'z) ⊢ subset_of('x, 'z)" PROOF {
  //   val subs = have(subsetAxiom)           //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x ⊆  'y
  //   //TODO
  // }

  // THEOREM("Subset_Antisymmetry") of "subset_of('x, 'y); subset_of('y, 'x)  ⊢ 'x='y " PROOF {
  //   val ext = have(extensionalityAxiom)    //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x ⊆ 'y
  //   val subs = have(subsetAxiom)           //  ⊢ ∀'x. ∀'y. 'x ⊆ 'y ⇔ (∀'z. 'z ∊ 'x ⇒ 'z ∊ 'y)
  //   //TODO
  // }


}
