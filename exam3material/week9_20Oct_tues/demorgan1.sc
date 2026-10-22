// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∀ x ¬P(x)   equivalent to   ¬(∃ x P(x))

@pure def demorgan1A[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => !P(x))
    )
    |-
    (
      !(∃((x: T) => P(x)))
    )
    Proof(
      1 ( ∀((x: T) => !P(x)) ) by Premise,

      //use NegI
      2 SubProof(
        3 Assume ( ∃((x: T) => P(x)) ),

        //try ExistsE with ∃((x: T) => P(x))
        4 Let ((alias: T) => SubProof(
          5 Assume ( P(alias) ),
          6 ( !P(alias) ) by AllE[T](1),
          7 ( F ) by NegE(5, 6)
          //goal: F
        )),
        8 ( F ) by ExistsE[T](3, 4)

        //goal: F
      ),
      9 ( !(∃((x: T) => P(x))) ) by NegI(2)
      //goal: !(∃((x: T) => P(x)))
    )
  )
}

//we did this direction before break
@pure def demorgan1B[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      !(∃((x: T) => P(x)))
    )
      |-
    (
      ∀((x: T) => !P(x))
    )
    Proof(
      1 (  !(∃((x: T) => P(x)))   ) by Premise,
      //use AllI pattern to prove ∀((x: T) => !P(x))
      2 Let ((a: T) => SubProof(
        //use NegI pattern to prove goal of !P(a)
        3 SubProof(
          4 Assume (P(a)),

          //can contradict with premise if we have 
          //∃((x: T) => P(x))

          5 ( ∃((x: T) => P(x)) ) by ExistsI[T](4),
          6 ( F ) by NegE(5, 1)

          //goal: F
        ),
        7 ( !P(a) ) by NegI(3)

        //goal: !P(a)
      )),
      8 ( ∀((x: T) => !P(x)) ) by AllI[T](2)

      //goal: ∀((x: T) => !P(x))
    )
  )
}