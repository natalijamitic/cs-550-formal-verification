//> using file "Resolution.scala"
import Resolution.*
import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*



@main
def main: Unit = {
  //solveMansionMystery
    // val a = Function(Named("John"), Nil())
    // val b = Function(Named("Peanuts"), Nil()) 

    // // Variables
    // val x = Var(Named("x"))

    // // Predicates
    // def food(t: Term) = Predicate(Named("food"), List(t))
    // def likes(t: Term, s: Term) = Predicate(Named("likes"), List(t, s))

    // val mansionMystery: Formula = And(Neg(likes(a, b)), Or(Neg(food(x)), likes(a, x)))

    // val r5 = conjunctionPrenexSkolemizationNegation(mansionMystery)

    // r5.forall { c =>
    //   println("Naca")
    //   println(c)
    //   println("======================")
    //   true
    // }

    // val step_final = (
    //   List(Atom(Neg(food(b)))),
    //   Deduced(
    //     (0, 1),
    //     stainless.lang.Map(Synthetic(0) -> b)
    //   )
    // )

    // val assumptions: List[(Clause, Justification)] = r5.map { (_, Assumed) }
    
    // val steps = List[(Clause, Justification)](
    //   step_final
    // )

    // println("Found the proof: " + checkResolutionProof(assumptions ++ steps))

    solveMansionMystery
}

