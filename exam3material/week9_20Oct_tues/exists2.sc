// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._


@pure def exists2[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ( ∃((x: T) => P(x)) ) | ( ∃((x: T) => Q(x)) )
    )
    |-
    (
      ∃((x: T) => (P(x) | Q(x)))
    )
      Proof(
      1 ( ( ∃((x: T) => P(x)) ) | ( ∃((x: T) => Q(x)) ) ) by Premise,

      2 SubProof(
        3 Assume ( ∃((x: T) => P(x)) ),
        4 Let ((a: T) => SubProof(
          5 Assume ( P(a) ),
          6 ( P(a) | Q(a) ) by OrI1(5),
          7 ( ∃((x: T) => (P(x) | Q(x))) ) by ExistsI[T](6)
        )),
        8 ( ∃((x: T) => (P(x) | Q(x))) ) by ExistsE[T](3,4)
      ),
      9 SubProof(
        10 Assume ( ∃((x: T) => Q(x)) ),
        11 Let ((a: T) => SubProof(
          12 Assume ( Q(a) ),
          13 ( P(a) | Q(a) ) by OrI2(12),
          14 ( ∃((x: T) => (P(x) | Q(x))) ) by ExistsI[T](13)
        )),
        15 ( ∃((x: T) => (P(x) | Q(x))) ) by ExistsE[T](10,11)
      ),
      16 ( ∃((x: T) => (P(x) | Q(x))) ) by OrE(1,2,9)
    )
  )
}