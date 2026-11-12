// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?
  Contract(
    Requires( y >= 0 )
    Ensures( Res[Z] == x*y )
  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    Deduce(
      1 ( y == 0 ) by Premise, 
      2 ( answer == 0 ) by Premise, 
      3 ( y >= 0 ) by Premise, 
      4 ( answer == x*y ) by Algebra*(1,2),
    )

    //what do we need to do here?
    //answer == x*y
  } else {

      Deduce(
        1 ( y >= 0 ) by Premise, 
        2 ( !(y == 0) ) by Premise, 
        3 ( y-1 >= 0 ) by Algebra*(1, 2), 
        //prove y-1 >= 0
      )

    var temp: Z = mult(x, y-1)
    answer = x + temp

    Deduce(
      1 ( answer == x + temp ) by Premise, 
      2 ( !(y == 0) ) by Premise, //not needed
      3 ( temp == x*(y-1) ) by Premise, 
      4 ( temp == x*y - x ) by Algebra*(3), //extra step 
      5 ( answer == x + x*y - x ) by Algebra*(1,4), //extra step
      6 ( answer == x*y ) by Algebra*(5),  
    )

    //what do we need to show here?
    //need answer == x*y 
  }


  Deduce(
    1( answer == x*y ) by Premise
  )
  //what do we need to do here?
 //need to prove postcondition 
  //mnnd answer == x*y

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

//prove precondition before the call 
Deduce(
  1 ( b = 4 ) by Premise, 
  2 ( b >= 0 ) by Algebra*(1), 
    //need: b >= 0 
)

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