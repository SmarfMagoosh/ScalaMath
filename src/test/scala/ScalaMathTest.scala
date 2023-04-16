import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

class Bound(lower: Double, upper: Double) {
  def up: Double = upper
  def low: Double = lower
}

extension (d: Double)
  def +-(o: Double): Bound = new Bound(d - o, d + o)
  def in(b: Bound): Boolean = d < b.up && d > b.low || d.isNaN && b.low.isNaN

extension (ds: List[Double])
  def +-(o: Double): List[Bound] = for d <- ds yield new Bound(d - o, d + o)
  def in(bs: List[Bound]): Boolean = (for i <- 0 until bs.length yield ds(i) in bs(i)).count(!_) == 0

class ScalaMathTest extends AnyFlatSpec with Matchers {
  "function" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val input = List()
    val f = x
    input.map(f of _) in List() +- eps should equal(true)
    input.map(f.prime of _) in List() +- eps should equal(true)
    input.map(f.integral of _) in List() +- eps should equal(true)
    val scale = 2 * f
    input.map(scale of _) in List() +- eps should equal(true)
    input.map(scale.prime of _) in List() +- eps should equal(true)
    input.map(scale.integral of _) in List() +- eps should equal(true)
  }
  // testing functions, their derivatives, and integrals are evaluated correctly
  val inputs: List[List[Double]] = List(
    List(1, 2, 3, 4, 5), // Standard
    List(3, 9, 27, 81, 243), // Logs
    List(0, pi / 6, pi / 4, pi / 3, pi / 2), // Trig
    List(-1.5, -1, 0, sqrt(2) / 2, sqrt(3) / 2) // Inverse Trig
  )
  val eps: Double = 0.00000000001

  // REGULAR FUNCTIONS
  "constant function" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val f: Func = Constant(7)
    inputs(0).map(f of _) should equal (List(7,7,7,7,7))
    inputs(0).map(f.prime of _) should equal (List(0,0,0,0,0))
    inputs(0).map(f.integral of _) should equal(List(7, 14, 21, 28, 35))
    val scale: Func = 3 * f
    inputs(0).map(scale of _) should equal(List(21, 21, 21, 21, 21))
    inputs(0).map(scale.prime of _) should equal(List(0, 0, 0, 0, 0))
    inputs(0).map(scale.integral of _) should equal(List(21, 42, 63, 84, 105))
  }

  "line function" should
    "have itself, derivative, and integral evaluted correctly even with a scalar" in {
    val f = x;
    inputs(0).map(f of _) should equal (List(1, 2, 3, 4, 5))
    inputs(0).map(f.prime of _) should equal (List(1, 1, 1, 1, 1))
    inputs(0).map(f.integral of _) should equal (List(0.5, 2, 4.5, 8, 12.5))
    val scale = 3 * f
    inputs(0).map(scale of _) should equal (List(3, 6, 9, 12, 15))
    inputs(0).map(scale.prime of _) should equal (List(3, 3, 3, 3, 3))
    inputs(0).map(scale.integral of _) should equal (List(1.5, 6, 13.5, 24, 37.5))
  }

  "polynomial" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val f = new Poly(3)
    inputs(0).map(f of _) should equal(List(1, 8, 27, 64, 125))
    inputs(0).map(f.prime of _) should equal(List(3, 12, 27, 48, 75))
    inputs(0).map(f.integral of _) should equal(List(0.25, 4, 81.0 / 4, 64, 625.0 / 4))
    val scale = 4 * f
    inputs(0).map(scale of _) should equal(List(4, 32, 108, 256, 500))
    inputs(0).map(scale.prime of _) should equal(List(12, 48, 108, 192, 300))
    inputs(0).map(scale.integral of _) should equal(List(1, 16, 81, 256, 625))
  }

  it should "work for fraction exponents" in {
    val f = sqrt
    inputs(0).map(f of _) in inputs(0).map(sqrt(_)) +- eps should equal (true)
    inputs(0).map(f.prime of _) in inputs(0).map(0.5 * Math.pow(_, -0.5)) +- eps should equal (true)
    inputs(0).map(f.integral of _) in inputs(0).map(2 * Math.pow(_, 1.5) / 3) +- eps should equal(true)
    val scale = 4 * f
    inputs(0).map(scale of _) in inputs(0).map(4 * sqrt(_)) +- eps should equal(true)
    inputs(0).map(scale.prime of _) in inputs(0).map(2 * Math.pow(_, -0.5)) +- eps should equal(true)
    inputs(0).map(scale.integral of _) in inputs(0).map(8 * Math.pow(_, 1.5) / 3) +- eps should equal(true)
  }

  it should "integrate 1 / x correctly even when scaled" in {
    val f = new Poly(-1)
    inputs(0).map(f.integral of _) should equal (List(ln(1), ln(2), ln(3), ln(4), ln(5)))
    val scale = 3 * f
    inputs(0).map(scale.integral of _) should equal (List(ln(1), ln(2), ln(3), ln(4), ln(5)).map(3 * _))
  }

  "exponential" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val f = new Exp(2)
    inputs(0).map(f of _) should equal (List(2, 4, 8, 16, 32))
    inputs(0).map(f.prime of _) should equal (List(2, 4, 8, 16, 32).map(_ * ln(2)))
    inputs(0).map(f.integral of _) should equal(List(2, 4, 8, 16, 32).map(_ / ln(2)))
    val scale = 0.5 * f
    inputs(0).map(scale of _) should equal(List(1, 2, 4, 8, 16))
    inputs(0).map(scale.prime of _) should equal(List(1, 2, 4, 8, 16).map(_ * ln(2)))
    inputs(0).map(scale.integral of _) should equal (List(1, 2, 4, 8, 16).map(_ / ln(2)))
  }

  it should "work when the base is less than 1" in {
    val f = new Exp(0.5)
    (1 to 100000).map(f(_)).sum should equal (1.0)
    val scale = 5 * f
    (1 to 100000).map(scale(_)).sum should equal (5.0)
  }

  "logs" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val f = new Log(3)
    inputs(1).map(f of _) in List(1.0, 2, 3, 4, 5) +- eps should equal (true)
    inputs(0).map(f.prime of _) in List(1, 0.5, 1 / 3.0, 0.25, 0.2).map(_ / Math.log(3)) +- eps should equal (true)
    inputs(0).map(f.integral of _) in List(-0.910239226627, -0.558618946111, 0.269282320119, 1.40648112206, 2.77367147046) +- eps should equal (true)
    val scale = 3 * f
    inputs(1).map(scale of _) in List(3.0, 6, 9, 12, 15) +- eps should equal(true)
    inputs(0).map(scale.prime of _) in List(3, 1.5, 1, 0.75, 0.6).map(_ / Math.log(3)) +- eps should equal (true)
    inputs(0).map(scale.integral of _) in List(-2.73071767988, -1.67585683833, 0.807846960358, 4.21944336619, 8.32101441137) +- eps should equal (true)
  }

  // TRIGONOMETRIC FUNCTIONS
  "sine" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val f = sin
    inputs(2).map(f of _) in List(0, 0.5, 1 / sqrt(2), sqrt(3) / 2, 1) +- eps should equal (true)
    inputs(2).map(f.prime of _) in List(1, sqrt(3) / 2, 1 / sqrt(2), 0.5, 0) +- eps should equal (true)
    inputs(2).map(f.integral of _) in List(-1, -sqrt(3) / 2, -1 / sqrt(2), -0.5, 0) +- eps should equal (true)
    val scale = 2 * f
    inputs(2).map(scale of _) in List(0, 1, sqrt(2), sqrt(3), 2) +- eps should equal(true)
    inputs(2).map(scale.prime of _) in List(2, sqrt(3), sqrt(2), 1, 0) +- eps should equal(true)
    inputs(2).map(scale.integral of _) in List(-2, -sqrt(3), -sqrt(2), -1, -0) +- eps should equal(true)
  }

  "cosine" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val f = cos
    inputs(2).map(f of _) in List(1, sqrt(3) / 2, 1 / sqrt(2), 0.5, 0) +- eps should equal(true)
    inputs(2).map(f.prime of _) in List(0, -0.5, -1 / sqrt(2), -sqrt(3) / 2, -1) +- eps should equal(true)
    inputs(2).map(f.integral of _) in List(0, 0.5, 1 / sqrt(2), sqrt(3) / 2, 1) +- eps should equal (true)
    val scale = 2 * f
    inputs(2).map(scale of _) in List(2, sqrt(3), sqrt(2), 1, 0) +- eps should equal(true)
    inputs(2).map(scale.prime of _) in List(0, -1, -sqrt(2), -sqrt(3), -2) +- eps should equal(true)
    inputs(2).map(scale.integral of _) in List(0, 1, sqrt(2), sqrt(3), 2) +- eps should equal (true)
  }
  "tangent" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val input = inputs(2).slice(0, 4) // ignore pi / 2 since tan(pi / 2) is undefined
    val f = tan
    input.map(f of _) in List(0, 1 / sqrt(3), 1, sqrt(3)) +- eps should equal(true)
    input.map(f.prime of _) in List(1, 4.0 / 3, 2, 4) +- eps should equal(true)
    input.map(f.integral of _) in List(0, 0.143841036226, 0.34657359028, 0.69314718056) +- eps should equal(true)
    val scale = sqrt(3) * f
    input.map(scale of _) in List(0, 1, sqrt(3), 3) +- eps should equal(true)
    input.map(scale.prime of _) in List(1, 4.0 / 3, 2, 4).map(_ * sqrt(3)) +- eps should equal(true)
    input.map(scale.integral of _) in List(0, 0.249139982957, 0.600283066926, 1.20056613385) +- eps should equal(true)
  }

  "secant" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val input = inputs(2).slice(0, 4)
    val f = sec
    input.map(f of _) in List(1, 2 / sqrt(3), sqrt(2), 2) +- eps should equal(true)
    input.map(f.prime of _) in List(0, 2.0 / 3, sqrt(2), sqrt(12)) +- eps should equal(true)
    input.map(f.integral of _) in List(0, 0.549306144334, 0.88137358702, 1.31695789692) +- eps should equal(true)
    val scale = sqrt(3) * f
    input.map(scale of _) in List(sqrt(3), 2, sqrt(6), 2 * sqrt(3)) +- eps should equal(true)
    input.map(scale.prime of _) in List(0, sqrt(12) / 3, sqrt(6), 6) +- eps should equal(true)
    input.map(scale.integral of _) in List(0, 0.951426150896, 1.52658383317, 2.2810379889) +- eps should equal(true)
  }

  "cosecant" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val input = inputs(2).slice(1, 5)
    val f = csc
    input.map(f of _) in List(2, sqrt(2), 2 / sqrt(3), 1) +- eps should equal(true)
    input.map(f.prime of _) in List(-sqrt(12), -sqrt(2), -2 / 3.0, 0) +- eps should equal(true)
    input.map(f.integral of _) in List(-1.31695789692, -0.88137358702, -0.549306144334, 0) +- eps should equal(true)
    val scale = sqrt(3) * f
    input.map(scale of _) in List(sqrt(12), sqrt(6), 2, sqrt(3)) +- eps should equal(true)
    input.map(scale.prime of _) in List(-6, -sqrt(6), -sqrt(12) / 3.0, 0) +- eps should equal(true)
    input.map(scale.integral of _) in List(-2.2810379889, -1.52658383317, -0.951426150896, 0) +- eps should equal(true)
  }
  "cotangent" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val input = inputs(2).slice(1, 5)
    val f = cot
    input.map(f of _) in List(sqrt(3), 1, 1 / sqrt(3), 0) +- eps should equal (true)
    input.map(f.prime of _) in List(-4, -2, -4.0 / 3, -1) +- eps should equal (true)
    input.map(f.integral of _) in List(-0.69314718056, -0.34657359028, -0.143841036226, 0) +- eps should equal (true)
    val scale = 3 * f
    input.map(scale of _) in List(sqrt(27), 3, sqrt(3), 0) +- eps should equal (true)
    input.map(scale.prime of _) in List(-12, -6, -4, -3.0) +- eps should equal (true)
    input.map(scale.integral of _) in List(-2.07944154168, -1.03972077084, -0.431523108678, 0) +- eps should equal (true)
  }

  //INVERSE TRIGONOMETRIC FUNCTIONS
  "arcsin" should
    "have itself, derivative, and integral evaluated correctly even with a scalar" in {
    val input = inputs(3)
    val f = arcsin
    input.map(f of _) in List(-pi / 6, -pi / 2, 0, pi / 4, pi / 3) +- eps should equal(true)
    input.map(f.prime of _) in List() +- eps should equal(true)
    //input.map(f.integral of _) in List() +- eps should equal(true)
    val scale = 2 * f
    //input.map(scale of _) in List() +- eps should equal(true)
    //input.map(scale.prime of _) in List() +- eps should equal(true)
    //input.map(scale.integral of _) in List() +- eps should equal(true)
  }
}
