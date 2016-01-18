package simplifier

import javax.security.auth.login.FailedLoginException

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  //def simplify(node: Node) = node

  def simplify(node: Node): Node = node match {
    case BinExpr(op, leftNode, rightNode) => {
      val left: Node = simplify(leftNode)
      val right: Node = simplify(rightNode)

      op match {
        case "and" => and(left, right)
        case "or" => or(left, right)
        case "==" => equals(left, right)
        case "!=" => notequals(left, right)
        case "<=" => lowerOrEquals(left, right)
        case ">=" => greaterOrEquals(left, right)
        case "<" => lower(left, right)
        case ">" => greater(left, right)
        case "+" => add(left,right)
        case "-" => sub(left,right)
        case "*" => multiply(left,right)
        case "/" => divide(left,right)
        case "%" => modulo(left,right)
        case "is" => is(left,right)
        case _ => evaluateExpression(op, left, right)
      }

    }
    case Unary(op, expr) => {
      val simplyExpr: Node = simplify(expr)
      op match {
        case "not" => not(simplyExpr)
        case "+" => plus(simplyExpr)
        case "-" => minus(simplyExpr)
        case _ => Unary(op, simplyExpr)
      }

    }
    case NodeList(list) => {
      var a = list.map {
        case f => simplify(f)
      }
      a=a.filterNot(f => (f == null))
      var assignments = a.filter(f => (f.isInstanceOf[Assignment]))
      a=a.filterNot(f => f.isInstanceOf[Assignment])

      assignments=assignments.map(f => assignments(assignments.lastIndexWhere(f1 => isTheSameAssignment(f, f1))))

      a=a++assignments.distinct
      a=a.filterNot(f => (f == null))
      NodeList(a)
    }
    case KeyDatumList(list) => KeyDatumList(list.map{case f => simplifyKeyDatum(f)})
    case ElemList(list) => {

      val a = list.filterNot(f =>(simplify(f)==null))

      ElemList(a.map{
        case f => simplify(f)
      })}
    case IfInstr(cond, body) => {
      val condition = simplify(cond)
      val newBody = simplify(body)
      if(condition==FalseConst()) null
      else if(condition==TrueConst()) newBody
      else IfInstr(condition, newBody)
    }
    case IfElseInstr(cond, myIf, myElse) => {
      val condition = simplify(cond)
      if(condition==TrueConst()) simplify(myIf)
      else if(condition==FalseConst()) simplify(myElse)
      else IfElseInstr(simplify(cond), simplify(myIf), simplify(myElse))
    }
    case IfElseExpr(cond, myIf, myElse) => {
      val condition = simplify(cond)
      if(condition==TrueConst()) simplify(myIf)
      else if(condition==FalseConst()) simplify(myElse)
      else IfElseInstr(simplify(cond), simplify(myIf), simplify(myElse))
    }
    case Assignment(variable, assign)=> {
      val left: Node = simplify(variable)
      val right: Node = simplify(assign)
      if (left == right) null
      else
        Assignment(variable, simplify(assign))
    }
    case ReturnInstr(expr) => ReturnInstr(simplify(expr))
    case PrintInstr(expr) => PrintInstr(simplify(expr))
    case WhileInstr(cond, body) => {
      val condition = simplify(cond)
      if(condition == FalseConst()) null
      else WhileInstr(condition, simplify(body))
    }
    case Subscription(primary, expression_list) => Subscription(simplify(primary), simplify(expression_list))
    case GetAttr(expr, attr) => GetAttr(simplify(expr), attr)
    case KeyDatum(key, datum) => KeyDatum(simplify(key), simplify(datum))
    case FunCall(name, args) => FunCall(name, simplify(args))
    case FunDef(name, formal_args, body) => FunDef(name, simplify(formal_args), simplify(body))
    case ClassDef(name, inherit_list, suit) => ClassDef(name, simplify(inherit_list), simplify(suit))
    case _ => node
  }
  def isTheSameAssignment(template: Node, actual: Node):Boolean = (template, actual) match {
    case (Assignment(left, right), Assignment(left2, right2)) => {
      if(left==left2) true
      else false
    }
    case _ => false
  }

  //BinaryExpression helpers
  def and(left: Node, right: Node):Node = (left, right) match {
    case(_, FalseConst()) => FalseConst()
    case(FalseConst(), _) => FalseConst()
    case(TrueConst(), TrueConst()) => TrueConst()
    case(TrueConst(), nodeRight) => nodeRight
    case(nodeLeft, TrueConst()) => nodeLeft
    case(nodeLeft,nodeRight) if nodeLeft == simplify(nodeRight) => nodeLeft
    case(nodeLeft, nodeRight) => BinExpr("and", nodeRight,nodeLeft)
    case(_, _) => BinExpr("and", left, right)
  }
  def or(left: Node, right: Node):Node = (left, right) match {
    case(_, TrueConst()) => TrueConst()
    case(TrueConst(), _) => TrueConst()
    case(FalseConst(), FalseConst()) => FalseConst()
    case(nodeLeft, FalseConst()) => nodeLeft
    case(FalseConst(),nodeRight) => nodeRight
    case(nodeLeft,nodeRight) if nodeLeft == simplify(nodeRight) => nodeLeft
    case(nodeLeft, nodeRight) => BinExpr("or", nodeRight,nodeLeft)
    case(_, _) => BinExpr("or", left, right)
  }
  def equals(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft, equalRight) if (equalLeft == equalRight) => TrueConst()
    case(IntNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft == nodeRight) TrueConst() else  FalseConst()
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft == nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft == nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft == nodeRight) TrueConst() else  FalseConst()
    case(StringConst(nodeLeft), StringConst(nodeRight)) => if (nodeLeft == nodeRight) TrueConst() else  FalseConst()
    case(nodeLeft, nodeRight) => BinExpr("==", nodeRight,nodeLeft)
    case(_, _) => BinExpr("==", left, right)
  }

  def notequals(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft, equalRight) if (equalLeft == equalRight) => FalseConst()
    case(IntNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft != nodeRight) TrueConst() else  FalseConst()
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft != nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft != nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft != nodeRight) TrueConst() else  FalseConst()
    case(StringConst(nodeLeft), StringConst(nodeRight)) => if (nodeLeft != nodeRight) TrueConst() else  FalseConst()
    case(nodeLeft, nodeRight) => BinExpr("!=", nodeRight,nodeLeft)
    case(_, _) => BinExpr("!=", left, right)
  }
  def lowerOrEquals(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft, equalRight) if (equalLeft == equalRight) => TrueConst()
    case(IntNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft <= nodeRight) TrueConst() else  FalseConst()
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft <= nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft <= nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft <= nodeRight) TrueConst() else  FalseConst()
    case(_, _) => BinExpr("<=", left, right)
  }
  def greaterOrEquals(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft, equalRight) if (equalLeft == equalRight) => TrueConst()
    case(IntNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft >= nodeRight) TrueConst() else  FalseConst()
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft >= nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft >= nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft >= nodeRight) TrueConst() else  FalseConst()
    case(_, _) => BinExpr(">=", left, right)
  }
  def lower(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft, equalRight) if (equalLeft == equalRight) => FalseConst()
    case(IntNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft < nodeRight) TrueConst() else  FalseConst()
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft < nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft < nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft < nodeRight) TrueConst() else  FalseConst()
    case(_, _) => BinExpr("<", left, right)
  }
  def greater(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft, equalRight) if (equalLeft == equalRight) => FalseConst()
    case(IntNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft > nodeRight) TrueConst() else  FalseConst()
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft >  nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => if (nodeLeft > nodeRight) TrueConst() else  FalseConst()
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => if (nodeLeft > nodeRight) TrueConst() else  FalseConst()
    case(_, _) => BinExpr(">", left, right)
  }
  def add(left: Node, right: Node):Node = (left, right) match {
    case(nodeLeft,IntNum(zero) ) if zero == 0 => nodeLeft
    case(IntNum(zero), nodeRight ) if zero == 0 => nodeRight
    case(mirrorLeft,Unary("-", mirrorRight) ) if (mirrorLeft == mirrorRight) => IntNum(0)
    case(Unary("-", mirrorLeft),mirrorRight ) if (mirrorLeft == mirrorRight) => IntNum(0)
    case(IntNum(nodeLeft), IntNum(nodeRight)) => IntNum(nodeLeft + nodeRight)
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft + nodeRight)
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft + nodeRight)
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => FloatNum(nodeLeft + nodeRight)
    case(BinExpr("+",BinExpr("*",y,v2),sth),BinExpr("*",z,v)) if v == v2 => simplify(BinExpr("+",simplify(BinExpr("*",simplify(BinExpr("+",z,y)),v2)),sth))
    case(BinExpr("*",leftNode,IntNum(numl)),rightNode) if(leftNode==rightNode) => simplify(BinExpr("*",IntNum(numl + 1), rightNode))
    case(BinExpr("*",leftNode,IntNum(numl)),BinExpr("*",IntNum(numr),rightNode)) if(leftNode==rightNode) => simplify(BinExpr("*",IntNum(numl + numr), rightNode))
    case(BinExpr("*",z1,x),BinExpr("*",z2,y)) if z1 == z2 => simplify(BinExpr("*",simplify(simplify(BinExpr("+",x,y))),simplify(simplify(z1))))
    case(BinExpr("*",x, z1),BinExpr("*",y, z2)) if z1 == z2 => simplify(BinExpr("*",simplify(simplify(z1)),simplify(simplify(BinExpr("+",x,y)))))
    case(BinExpr("*",BinExpr("+",z,y),v),BinExpr("*",x,BinExpr("+",z2,y2)))
      if z == z2 && y == y2 => {
      simplify(BinExpr("*",simplify(BinExpr("+",v,x)),simplify(BinExpr("+", y, z))))
    }
    case(nodeLeft, nodeRight) => BinExpr("+", nodeRight,nodeLeft)
    case(_, _) => BinExpr("+", left, right)
  }
  def sub(left: Node, right: Node):Node = (left, right) match {
    case(nodeLeft,IntNum(zero) ) if zero == 0 => nodeLeft
    case(IntNum(zero), nodeRight ) if zero == 0 => nodeRight
    case(mirrorLeft,mirrorRight) if (mirrorLeft == mirrorRight) => IntNum(0)
    case(IntNum(nodeLeft), IntNum(nodeRight)) => IntNum(nodeLeft - nodeRight)
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft - nodeRight)
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft - nodeRight)
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => FloatNum(nodeLeft - nodeRight)
    case(BinExpr("*",leftNode,IntNum(numl)),rightNode) if(leftNode==rightNode) => simplify(BinExpr("*",IntNum(numl - 1), rightNode))
    case(BinExpr("*",leftNode,IntNum(numl)),BinExpr("*",IntNum(numr),rightNode)) if(leftNode==rightNode) => simplify(BinExpr("*",IntNum(numl - numr), rightNode))
    case(BinExpr("*",z1,x),BinExpr("*",z2,y)) if z1 == z2 => simplify(BinExpr("*",simplify(BinExpr("-",x,y)),z1))
    case(BinExpr("*",x, z1),BinExpr("*",y, z2)) if z1 == z2 => simplify(BinExpr("*",z1,simplify(BinExpr("-",x,y))))
    case(_, _) => BinExpr("-", left, right)
  }
  def multiply(left: Node, right: Node):Node = (left, right) match {
    case(IntNum(zero), _ ) if zero == 0 => IntNum(0)
    case( _, IntNum(zero) ) if zero == 0 => IntNum(0)
    case(IntNum(one) , nodeRight ) if one == 1 => nodeRight
    case( nodeLeft , IntNum(one) ) if one == 1 => nodeLeft
    case(IntNum(nodeLeft), IntNum(nodeRight)) => IntNum(nodeLeft * nodeRight)
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft * nodeRight)
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft * nodeRight)
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => FloatNum(nodeLeft * nodeRight)
    case(nodeLeft, BinExpr("/", IntNum(one), nodeRight)) if one == 1 => BinExpr("/", nodeLeft,nodeRight)
    case(nodeLeft, nodeRight) => BinExpr("*", nodeRight,nodeLeft)
    case(_, _) => BinExpr("*", left, right)
  }
  def divide(left: Node, right: Node):Node = (left, right) match {
    case(nodeLeft,nodeRight) if( simplify(nodeLeft)== simplify(nodeRight))=> IntNum(1) //////
    case(nodeLeft,nodeRight) if(simplify(nodeLeft) == nodeRight)=> IntNum(1)
    case(FloatNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft / nodeRight)
    case(IntNum(nodeLeft), FloatNum(nodeRight)) => FloatNum(nodeLeft / nodeRight)
    case(FloatNum(nodeLeft), IntNum(nodeRight)) => FloatNum(nodeLeft / nodeRight)
    case(IntNum(one), BinExpr("/", IntNum(oneExp),expression)) if (one == 1 && oneExp == 1) => expression
    case(BinExpr("+",yz1,x1),BinExpr("+",x2,yz2))if (yz1 == yz2 && x1==x2) => IntNum(1)
    case(_, _) => BinExpr("/", left, right)
  }
  def modulo(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft,equalRight) if (equalLeft == equalRight) => IntNum(0)
    case(IntNum(nodeLeft), IntNum(nodeRight)) => IntNum(nodeLeft % nodeRight)
    case (_, _) => BinExpr("%", left, right)
  }
  def is(left: Node, right: Node):Node = (left, right) match {
    case(equalLeft, equalRight) if (equalLeft == equalRight) => TrueConst()
    case(_, _) => BinExpr("is", left, right)
  }

  def not(expr: Node) = (expr) match {
    case(FalseConst()) => TrueConst()
    case(TrueConst()) => FalseConst()
    case(BinExpr("==",nodeLeft,nodeRight))=>BinExpr("!=",nodeLeft,nodeRight)
    case(BinExpr("!=",nodeLeft,nodeRight))=>BinExpr("==",nodeLeft,nodeRight)
    case(BinExpr(">",nodeLeft,nodeRight))=>BinExpr("<=",nodeLeft,nodeRight)
    case(BinExpr("<",nodeLeft,nodeRight))=>BinExpr(">=",nodeLeft,nodeRight)
    case(BinExpr("<=",nodeLeft,nodeRight))=>BinExpr(">",nodeLeft,nodeRight)
    case(BinExpr(">=",nodeLeft,nodeRight))=>BinExpr("<",nodeLeft,nodeRight)
    case(Unary("not",expr)) => expr
    case(_) => Unary("not", expr)
  }

  def minus(expr: Node) = (expr) match {
    case(IntNum(expression)) => IntNum(-expression)
    case(FloatNum(expression)) => FloatNum(-expression)
    case(Unary("-",expr)) => expr
    case(_) => Unary("-", expr)
  }

  def plus(expr: Node) = (expr) match {
    case(IntNum(expression)) => IntNum(expression)
    case(FloatNum(expression)) => FloatNum(expression)
    case(_) => Unary("+", expr)
  }
  def evaluateExpression(op: String, left: Node, right: Node):Node = (left, right) match {
    case(_, _) => BinExpr(op, left, right)
  }

  //Needed returning KeyDatum instead of Node
  def simplifyKeyDatum(keyDatum: Node): KeyDatum = keyDatum match {
    case KeyDatum(key, datum) => KeyDatum(simplify(key), simplify(datum))
    case _ => KeyDatum(StringConst("error"), StringConst("error"))
  }
}
