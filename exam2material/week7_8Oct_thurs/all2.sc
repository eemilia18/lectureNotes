// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ x (P(x) ⋀ Q(x))    equivalent to     (∀ x P(x)) ⋀ (∀ x Q(x))

@pure def all2part1[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
      |-
    (
       ∀((x: T) => P(x)) & ∀((x: T) => Q(x))
    )
    Proof(
      1 (∀((x: T) => (P(x) & Q(x)))) by Premise,

      //first prove ∀((x: T) => P(x))
      //use AllI
      2 Let ((a: T) => SubProof(
        3 ( P(a) & Q(a) ) by AllE[T](1),
        4 ( P(a) ) by AndE1(3)
        //goal: P(a)
      )),
      5 ( ∀((x: T) => P(x)) ) by AllI[T](2),

      //next prove ∀((x: T) => Q(x))
      //use AllI
      6 Let ((a: T) => SubProof(
        7 ( P(a) & Q(a) ) by AllE[T](1),
        8 ( Q(a) ) by AndE2(7)
        //goal: Q(a)
      )),
      9 ( ∀((x: T) => Q(x)) ) by AllI[T](6),

      10 ( ∀((x: T) => P(x)) & ∀((x: T) => Q(x)) ) by AndI(5, 9)
    )
  )
}

/*
@pure def all2part2[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => P(x)) & ∀((x: T) => Q(x))
    )
      |-
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
    Proof(
      1 (  ∀((x: T) => P(x)) & ∀((x: T) => Q(x))  ) by Premise,
      
    )
  )
}
*/