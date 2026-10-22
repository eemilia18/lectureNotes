// #Sireum #Logika
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∃ x ¬P(x)   equivalent to    ¬(∀ x P(x))

@pure def demorgan2A[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      ∃((x: T) => !P(x))
    )
      |-
    (
        !(∀((x: T) => P(x)))
    )
    Proof(
      1 (  ∃((x: T) => !P(x))            ) by Premise,

      //use NegI to prove !(∀((x: T) => P(x)))
      2 SubProof(
        3 Assume( ∀((x: T) => P(x)) ),

        4 Let((alias: T ) => SubProof(
          5 Assume ( !P(alias) ),
          6 ( P(alias) ) by AllE[T](3),
          7 ( F ) by NegE(6, 5)
          //goal: F
        )),
        8 ( F ) by ExistsE[T](1, 4)

        //goal: F
      ),
      9 (!(∀((x: T) => P(x))) )  by NegI(2)

      //goal: !(∀((x: T) => P(x)))

    )
  )
}

@pure def demorgan2B[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      !(∀((x: T) => P(x)))
    )
      |-
    (
      ∃((x: T) => !P(x))
    )
    Proof(
      1 ( !(∀((x: T) => P(x)) )              ) by Premise,
      
      //no obvious path, try PbC
      2 SubProof(
        3 Assume ( !(∃((x: T) => !P(x))) ),

        //if I had ∀((x: T) => P(x)), would F with 1
        //try AllI to create ∀((x: T) => P(x))
        4 Let ((a: T) => SubProof(
          //no obvious path to P(a), try PbC
          5 SubProof(
            6 Assume (!P(a) ),
            7 ( ∃((x: T) => !P(x)) ) by ExistsI[T](6),
            8 ( F ) by NegE(7, 3)
            //goal: F
          ),
          9 ( P(a) ) by PbC(5)
          //use PbC to conclude P(a)
          //need: P(a)
        )),
        10 ( ∀((x: T) => P(x)) ) by AllI[T](4),
        //use AllI to conclude ∀((x: T) => P(x))

        //goal: F
        11 ( F ) by NegE(10, 1)
      ),
      12 ( ∃((x: T) => !P(x)) ) by PbC(2)
      //goal: ∃((x: T) => !P(x))
    )
  )
}