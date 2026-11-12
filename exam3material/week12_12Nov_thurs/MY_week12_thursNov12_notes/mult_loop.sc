// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract?

  Contract(
    Requires( y >= 0 )
    Ensures( Res[Z] == x*y )
  )

  var total: Z = 0
  var i: Z = 0

  //what goes here?
  Deduce(
    1 ( total == 0 ) by Premise, 
    2 ( i == 0 ) by Premise, 
    3 ( total == i*x ) by Algebra(1,2), 
    //total == i*x
  )

  while (i != y) {
    //what goes here?
    Invariant(
      Modifies(total, i), 
      total == i*x 
    )

    total = total + x
    Deduce(
      1 ( Old(total) == i*x ) by Premise, 
      2 ( total == Old(total) + x ) by Premise, 
      3 ( total == i*x + x ) by Algebra*(1,2)
    )

    i = i + 1

    Deduce(
      1 ( i = Old(i) + 1 ) by Premise, 
      2 ( total = Old(i)*x + x) by Premise, 
      3 ( total == i*x ) by Algebra*(2)
    )

    //what should we be able to assert here?
    // invariant is still true total == i*x
  }

  //what do we need here?
  Deduce(
    1 ( !(i != y) ) by Premise,
    2 ( i == y ) by Algebra*(1), 
    3 ( total == i*x ) by Premise, 
    4 ( total == x*y ) by Algebra*(2,3), 
  )

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

var ans: Z = mult(a, b)

Deduce(
  1 ( a == 5 ) by Premise, 
  2 ( b == 4 ) by Premise, 
  3 ( ans == a*b ) by Premise, //from post condition
  4 ( ans == 20 ) by Algebra*(1,2,3), 

  //need: ans == 20
)

//what do we want to assert that ans is?
assert(ans == 20)