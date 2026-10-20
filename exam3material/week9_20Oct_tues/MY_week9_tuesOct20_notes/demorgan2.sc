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
      2 SubProof(
        3 Assume( ∀((x: T) => P(x)) ), 

        4 Let((a: T) => SubProof(
          5 Assume( !P(a) ), 
          6 ( P(a) ) by AllE[T](3),
          7 ( F ) by NegE(6, 5), 
        )),
        8 ( F ) by ExistsE[T](1, 4), 
      ),
      9 (!(∀((x: T) => P(x)))) by NegI(2), 
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
      
      2 SubProof(
        3 Assume( !(∃((x: T) => !P(x))) ), 
        
        4 Let ((a: T) => SubProof(
          5 SubProof(
            6 Assume( !P(a) ), 
            7 ( ∃((x: T) => !P(x)) ) by ExistsI[T](6),
            8 ( F ) by NegE(7, 3), 
          ),
          9 ( P(a) ) by PbC(5), 
        )),
        10 ( (∀((x: T) => P(x))) ) by AllI[T](4),

        11 ( F ) by NegE(10, 1), 
      ),

      12 ( ∃((x: T) => !P(x)) ) by PbC(2), 

    )
  )
}