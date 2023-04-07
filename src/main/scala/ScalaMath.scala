import scala.util.Random
import scala.annotation.tailrec

// Helpers
private val r = Random
private def tests: List[Double] = for _ <- (0 to 50).toList yield r.nextInt(100) * r.nextDouble()

// Extensions
extension (d: Double)
  def +(f: Function): Function = Constant(d) + f
  def -(f: Function): Function = Constant(d) - f
  def *(f: Function): Function = Scalar(d, f)
  def /(f: Function): Function = Constant(d) / f
  def **(f: Function): Function = if f == x then Exponential(d) else Composite(Exponential(d), f)
  def ==(f: Function): Boolean = Constant(d) == f

extension (i: Int)
  def +(f: Function): Function = Constant(i) + f
  def -(f: Function): Function = Constant(i) - f
  def *(f: Function): Function = Scalar(i, f)
  def /(f: Function): Function = Constant(i) / f
  def **(f: Function): Function = if f == x then Exponential(i) else Composite(Exponential(i), f)
  def ==(f: Function): Boolean = Constant(i) == f

// Functions
abstract class Function {
  val funcType: Class[_ <: Function] = this.getClass
  def nonZero(i: Int = 0): Double = 0

  // basic values
  def of: Double => Double

  // arithmetic operations
  def apply(x: Double): Double = this of x
  def apply(f: Function): Function = {
    if f == x then this
    else if f.isConstant then Constant(this of f.as[Constant]._1)
    else if this isInverseOf f then x
    else Composite(this, f)
  }
  def +(x: Double): Function = Sum(this, Constant(x))
  def +(f: Function): Function = Sum(this, f)
  def -(x: Double): Function = Sum(this, Constant(-x))
  def -(f: Function): Function = Sum(this, Scalar(-1, x))
  def *(x: Double): Function = Scalar(x, this)
  def *(f: Function): Function = Product(this, f)
  def /(x: Double): Function = Scalar(1.0 / x, this)
  def /(f: Function): Function = Product(this, f ** -1)
  def **(x: Double): Function = Composite(Polynomial(x), this)
  def **(f: Function): Function = Tetration(this, f)

  // Comparative functions
  def ==(f: Function): Boolean = tests.count((this - f)(_).abs > 0.00000001) == 0
  def !=(f: Function): Boolean = !(this == f)
  def ==(d: Double): Boolean = this == Constant(d)
  def !=(d: Double): Boolean = this != Constant(d)
  def *=(f: Function): Boolean = f == this * f.of(nonZero()) / this.of(nonZero())
  def *=(d: Double): Boolean = this *= Constant(d)
  def !*=(f: Function): Boolean = !(this *= f)
  def !*=(d: Double): Boolean = !(this !*= d)
  def isInverseOf(f: Function): Boolean = tests.count((this(f) - x)(_).abs > 0.00000001) == 0
  def findScalar(f: Function): Double = if this *= f then f(nonZero()) / this(nonZero()) else Double.NaN

  // determines what type of function it is
  def isSum: Boolean = this.funcType.toString.toString == "class Sum"
  def isProduct: Boolean = this.funcType.toString == "class Product"
  def isComposite: Boolean = this.funcType.toString == "class Composite"
  def isTetration: Boolean = this.funcType.toString == "class Tetration"
  def isScalar: Boolean = false // overridden in Scalar Class
  def isConstant: Boolean = this.funcType.toString == "class Constant"
  def isLine: Boolean = this.funcType.toString == "class Line"
  def isPolynomial: Boolean = this.funcType.toString == "class Polynomial"
  def isExponential: Boolean = this.funcType.toString == "class Exponential"
  def isLog: Boolean = this.funcType.toString == "class Log"
  def isSine: Boolean = this.funcType.toString == "class Sine"
  def isCosine: Boolean = this.funcType.toString == "class Cosine"
  def isTangent: Boolean = this.funcType.toString == "class Tangent"
  def isSecant: Boolean = this.funcType.toString == "class Secant"
  def isCosecant: Boolean = this.funcType.toString == "class Cosecant"
  def isCotangent: Boolean = this.funcType.toString == "class Cotangent"
  def isArcSine: Boolean = this.funcType.toString == "class ArcSine"
  def isArcCosine: Boolean = this.funcType.toString == "class ArcCosine"
  def isArcTangent: Boolean = this.funcType.toString == "class ArcTangent"
  def isArcSecant: Boolean = this.funcType.toString == "class ArcSecant"
  def isArcCosecant: Boolean = this.funcType.toString == "class ArcCosecant"
  def isArcCotangent: Boolean = this.funcType.toString == "class ArcCotangent"
  def isHyperbolicSine: Boolean = this.funcType.toString == "class HyperbolicSine"
  def isHyperbolicCosine: Boolean = this.funcType.toString == "class HyperbolicCosine"
  def isHyperbolicTangent: Boolean = this.funcType.toString == "class HyperbolicTangent"
  def isHyperbolicSecant: Boolean = this.funcType.toString == "class HyperbolicSecant"
  def isHyperbolicCosecant: Boolean = this.funcType.toString == "class HyperbolicCosecant"
  def isHyperbolicCotangent: Boolean = this.funcType.toString == "class HyperbolicCotangent"

  // Casting because typing f.asInstanceOf[FunctionType] everytime is simply too long
  def as[T <: Function]: T = this.asInstanceOf[T]
}

// error function for when integrals can't be found
class Erf extends Function {
  def of: Double => Double = _ => Double.NaN
}

class Sum(f: Function, g: Function) extends Function {
  val _1: Function = f
  val _2: Function = g

  def of: Double => Double = (x: Double) => (f of x) + (g of x)

  // overridden functions
  override def apply(f: Function): Function = Sum(_1(f), _2(f))
}

class Product(f: Function, g: Function) extends Function {
  val _1: Function = f
  val _2: Function = g

  def of: Double => Double = (x: Double) => (f of x) * (g of x)
  // TODO override default functions for optimization
  // overridden function
}

class Composite(f: Function, g: Function) extends Function {
  val _1: Function = f
  val _2: Function = g

  def of: Double => Double = (x: Double) => f of (g of x)
}

class Tetration(base: Function, exp: Function) extends Function {
  val _1: Function = base
  val _2: Function = exp

  def of: Double => Double = (x: Double) => Math.pow(base of x, exp of x)
  // TODO override default functions for optimization
}

class Scalar(scalar: Double, f: Function) extends Function {
  override val funcType: Class[_ <: Function] = f.funcType
  val _1: Double = scalar
  val _2: Function = f

  def of: Double => Double = (x: Double) => scalar * f(x)
  // TODO override default functions for optimization

  override def isScalar: Boolean = true
}

class Constant(constant: Double) extends Function {
  val _1: Double = constant

  def of: Double => Double = _ => constant
  // TODO override default functions for optimization
}

class Line extends Function {
  def of: Double => Double = (x: Double) => x
  // TODO override default functions for optimization
}

class Polynomial(exp: Double) extends Function {
  val _1: Double = exp

  def of: Double => Double = (x: Double) => Math.pow(x, exp)
  // TODO override default functions for optimization
}

class Exponential(base: Double) extends Function {
  val _1: Double = base

  def of: Double => Double = (x: Double) => Math.pow(base, x)
  // TODO override default functions for optimization
}

class Log(base: Double) extends Function {
  val _1: Double = base

  def of: Double => Double = (x: Double) => Math.log(x) / Math.log(base)
  // TODO override default functions for optimization
  override def apply(f: Function): Function = {
    if f == x then this
    else if f.isConstant then Constant(this of f.as[Constant]._1)
    else if this isInverseOf f then x
    else Composite(this, f)
  }
  override def *(f: Function): Function = Product(this, f)
  override def /(f: Function): Function = Product(this, f ** -1)
  override def **(x: Double): Function = Composite(Polynomial(x), this)
}

class Sine extends Function {
  def of: Double => Double = (x: Double) => Math.sin(x)
}

class Cosine extends Function {
  def of: Double => Double = (x: Double) => Math.cos(x)
}

class Tangent extends Function {
  def of: Double => Double = (x: Double) => Math.tan(x)
}

class Secant extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.cos(x)
}

class Cosecant extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.sin(x)
}

class Cotangent extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.tan(x)
}

class ArcSine extends Function {
  def of: Double => Double = (x: Double) => Math.asin(x)
}

class ArcCosine extends Function {
  def of: Double => Double = (x: Double) => Math.acos(x)
}

class ArcTangent extends Function {
  def of: Double => Double = (x: Double) => Math.atan(x)
}

class ArcSecant extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.acos(x)
}

class ArcCosecant extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.asin(x)
}

class ArcCotangent extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.atan(x)
}

class HyperbolicSine extends Function {
  def of: Double => Double = (x: Double) => Math.sinh(x)
}
// test
class HyperbolicCosine extends Function {
  def of: Double => Double = (x: Double) => Math.cosh(x)
}

class HyperbolicTangent extends Function {
  def of: Double => Double = (x: Double) => Math.tanh(x)
}

class HyperbolicSecant extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.cosh(x)
}
class HyperbolicCosecant extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.sinh(x)
}

class HyperbolicCotangent extends Function {
  def of: Double => Double = (x: Double) => 1.0 / Math.tanh(x)
}

// general logarithmic functions 
val ln: Log = Log(Math.E)
val lg: Log = Log(2)

// f(x) = x
val x: Line = Line()

// trig functions
val sin: Sine = Sine()
val cos: Cosine = Cosine()
val tan: Tangent = Tangent()
val sec: Secant = Secant()
val csc: Cosecant = Cosecant()
val cot: Cotangent = Cotangent()

// inverse trig functions
val arcsin: ArcSine = ArcSine()
val arccos: ArcCosine = ArcCosine()
val arctan: ArcTangent = ArcTangent()
val arcsec: ArcSecant = ArcSecant()
val arccsc: ArcCosecant = ArcCosecant()
val arccot: ArcCotangent = ArcCotangent()

// hyperbolic trig functions
val sinh: HyperbolicSine = HyperbolicSine()
val cosh: HyperbolicCosine = HyperbolicCosine()
val tanh: HyperbolicTangent = HyperbolicTangent()
val sech: HyperbolicSecant = HyperbolicSecant()
val csch: HyperbolicCosecant = HyperbolicCosecant()
val coth: HyperbolicCotangent = HyperbolicCotangent()

// important constants
val e = Math.E
val pi: Double = Math.PI
val phi: Double = (1 + Math.sqrt(5)) / 2
val tau: Double = Math.TAU
