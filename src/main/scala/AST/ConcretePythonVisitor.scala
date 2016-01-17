package main.scala.AST

import parser.PythonParser._
import scala.collection.JavaConverters._


class ConcretePythonVisitor extends AbstractPythonVisitor {


  // expression : TRUE                                     # Expression_1
  override def visitExpression_1(ctx: Expression_1Context ): TrueConst = {
      TrueConst()
  }

  // expression : FALSE                                    # Expression_2
  override def visitExpression_2(ctx: Expression_2Context ): FalseConst = {
      FalseConst()
  }

  // expression : STRING                                   # Expression_3
  override def visitExpression_3(ctx: Expression_3Context ): StringConst = {
      StringConst(ctx.STRING().getSymbol.getText)
  }

  // expression : ID                                       # Expression_4
  override def visitExpression_4(ctx: Expression_4Context ): Variable = {
      Variable(ctx.ID().getSymbol.getText)
  }

  // expression : FLOAT                                    # Expression_5
  override def visitExpression_5(ctx: Expression_5Context ): FloatNum = {
    val number = ctx.FLOAT().getSymbol.getText
    FloatNum(number.toFloat)
  }

  // expression : INT                                      # Expression_6
  override def visitExpression_6(ctx: Expression_6Context ): IntNum = {
    val number = ctx.INT().getSymbol.getText
    IntNum(number.toInt)
  }

  // expression : INPUT '(' ')'                            # Expression_7
  override def visitExpression_7(ctx: Expression_7Context ): InputInstr = {
      InputInstr()
  }

  // expression : expression '(' expr_list ')'             # Expression_8
  override def visitExpression_8(ctx: Expression_8Context ): FunCall = {
      val name = ctx.expression().accept(this)
      val args_list = ctx.expr_list().accept(this)
      args_list match {
          case NodeList(l) => FunCall(name, NodeList(l))
          case _ => FunCall(name, NodeList(List()))
      }
  }

  // expression : '(' expression ')'                       # Expression_9
  override def visitExpression_9(ctx: Expression_9Context ): Node = {
      ctx.expression().accept(this)
  }

  // expression : '[' expr_list_comma ']'                  # Expression_10
  override def visitExpression_10(ctx: Expression_10Context ): Node = {
      val list = ctx.expr_list_comma().accept(this)
      list match {
          case NodeList(x) => ElemList(x)
          case _ => { println("Warn: expr_list didn't return NodeList"); list }
      }
  }

  // expression : '{' key_datum_list '}'                   # Expression_11
  override def visitExpression_11(ctx: Expression_11Context ): Node = {
      ctx.key_datum_list().accept(this)
  }
  
  // expression : expression '[' expression ']'            # Expression_12
  override def visitExpression_12(ctx: Expression_12Context ): Subscription = {
      val expr = ctx.expression(0).accept(this)
      val sub = ctx.expression(1).accept(this)
      Subscription(expr, sub)
  }

  // expression : expression '.' ID                        # Expression_13
  override def visitExpression_13(ctx: Expression_13Context ): GetAttr = {
      val expr = ctx.expression().accept(this)
      val attr = ctx.ID().getSymbol.getText
      GetAttr(expr, attr)
  }

  // expression : op=('+'|'-') expression                  # Expression_14
  override def visitExpression_14(ctx: Expression_14Context ): Node = {
      val expr  = ctx.expression().accept(this)
      val op = ctx.op.getText
      op match {
        case "+" => expr
        case "-" => Unary(op, expr)
        case _   => println("$op: skipping unknown operator"); expr
      }
  }

  // expression : op=('*'|'/'|'%') expression              # Expression_15
  override def visitExpression_15(ctx: Expression_15Context ): Node = {
      val left  = ctx.expression(0).accept(this)
      val right = ctx.expression(1).accept(this)
      val op = ctx.op.getText
      BinExpr(op, left, right)
  }

  // expression : expression op=('+'|'-') expression       # Expression_16
  override def visitExpression_16(ctx: Expression_16Context ): BinExpr = {
      val left  = ctx.expression(0).accept(this)
      val right = ctx.expression(1).accept(this)
      val op = ctx.op.getText
      BinExpr(op, left, right)
  }

  // expression : expression op=(IS|EQ|NEQ|LT|GT|LE|GE) expression  # Expression_17
  override def visitExpression_17(ctx: Expression_17Context ): BinExpr = {
      val left  = ctx.expression(0).accept(this)
      val right = ctx.expression(1).accept(this)
      val op = ctx.op.getText
      BinExpr(op, left, right)
  }

  // expression : NOT expression                           # Expression_18
  override def visitExpression_18(ctx: Expression_18Context ): Unary = {
     val left  = ctx.expression().accept(this)
     Unary("not", left)
  }

  // expression : expression op=AND expression             # Expression_19
  override def visitExpression_19(ctx: Expression_19Context ): BinExpr = {
     val left  = ctx.expression(0).accept(this)
     val right = ctx.expression(1).accept(this)
     BinExpr("and", left, right)
  }

  // expression : expression op=OR expression              # Expression_20
  override def visitExpression_20(ctx: Expression_20Context ): BinExpr = {
     val left  = ctx.expression(0).accept(this)
     val right = ctx.expression(1).accept(this)
     BinExpr("or", left, right)
  }

  // expression : expression IF expression ELSE expression # Expression_21
  override def visitExpression_21(ctx: Expression_21Context ): IfElseExpr = {
      val left  = ctx.expression(0).accept(this)
      val cond = ctx.expression(1).accept(this)
      val right = ctx.expression(2).accept(this)
      IfElseExpr(cond, left, right)
  }

  // expression : LAMBDA id_list ':' expression            # Expression_22
  override def visitExpression_22(ctx: Expression_22Context ): LambdaDef = {
     val formal_args = ctx.id_list().accept(this)
     val body = ctx.expression().accept(this)
     LambdaDef(formal_args, body)
  }


  // compound_statement : if_stmt                          # Compound_statement_1
  override def visitCompound_statement_1(ctx: Compound_statement_1Context): Node = {
      ctx.if_stmt().accept(this)
  }

  // compound_statement : while_stmt                       # Compound_statement_2
  override def visitCompound_statement_2(ctx: Compound_statement_2Context): Node = {
      ctx.while_stmt().accept(this)
  }

  // compound_statement : funcdef                          # Compound_statement_3
  override def visitCompound_statement_3(ctx: Compound_statement_3Context): Node = {
      ctx.funcdef().accept(this)
  }

  // compound_statement : classdef                         # Compound_statement_4
  override def visitCompound_statement_4(ctx: Compound_statement_4Context): Node = {
      ctx.classdef().accept(this)
  }


  // subscription : expression '[' expression ']'
  override def visitSubscription(ctx: SubscriptionContext ): Subscription = {
      val expr = ctx.expression(0).accept(this)
      val sub = ctx.expression(1).accept(this)
      Subscription(expr, sub)
  }


  // small_statement : expression             # Small_statement_1
  override def visitSmall_statement_1(ctx: Small_statement_1Context ): Node = {
      ctx.expression().accept(this)
  }

  // small_statement : target '=' expression  # Small_statement_2
  override def visitSmall_statement_2(ctx: Small_statement_2Context ): Assignment = {
      val left = ctx.target().accept(this)
      val right = ctx.expression().accept(this)
      Assignment(left, right)
  }

  // small_statement : PRINT expression       # Small_statement_3
  override def visitSmall_statement_3(ctx: Small_statement_3Context ): PrintInstr = {
      val expr = ctx.expression().accept(this)
      PrintInstr(expr)
  }
  
  // small_statement : RETURN expression      # Small_statement_4
  override def visitSmall_statement_4(ctx: Small_statement_4Context ): ReturnInstr = {
      val expr = ctx.expression().accept(this)
      ReturnInstr(expr)
  }

  // small_statement_list : small_statement ( ';' small_statement )*
  override def visitSmall_statement_list(ctx: Small_statement_listContext ): NodeList = {
      val list = ctx.small_statement().asScala.toList.map(_.accept(this))
      NodeList(list)
  }

  // module : (statement|NEWL)*
  override def visitModule(ctx: ModuleContext ): NodeList = {
      val list = ctx.statement().asScala.toList.map(_.accept(this))
      NodeList(list)
  }


  // funcdef : DEF ID '(' id_list ')' ':' suite
  override def visitFuncdef(ctx: FuncdefContext ): FunDef = {
      val name = ctx.ID().getSymbol.getText
      val formal_args = ctx.id_list().accept(this)
      val body = ctx.suite().accept(this)
      FunDef(name, formal_args, body)
  }

  // statement_list : statement+
  override def visitStatement_list(ctx: Statement_listContext ): NodeList = {
      val list = ctx.statement().asScala.toList.map(_.accept(this))
      NodeList(list) // a co jesli lista jest pusta
  }

  // key_datum_list : /* empty */
  // key_datum_list : key_datum ( ',' key_datum )*
  override def visitKey_datum_list(ctx: Key_datum_listContext ): KeyDatumList = {
      val list = ctx.key_datum().asScala.toList.map(visitKey_datum)
      KeyDatumList(list)
  }

  // while_stmt : WHILE expression ':' suite
  override def visitWhile_stmt(ctx: While_stmtContext ): WhileInstr = {
      val cond = ctx.expression().accept(this)
      val body = ctx.suite().accept(this)
      WhileInstr(cond, body)
  }

  // id_list : /* empty */
  // id_list : ID ( ',' ID )*
  override def visitId_list(ctx: Id_listContext ): IdList = {
      val list = ctx.ID().asScala.toList.map(_.getSymbol.getText)
      IdList(list.map(Variable))
  }

  // statement : simple_statement             # Statement_1
  override def visitStatement_1(ctx: Statement_1Context ): Node = {
      ctx.simple_statement().accept(this)
  }

  // statement : compound_statement           # Statement_2
  override def visitStatement_2(ctx: Statement_2Context ): Node = {
      ctx.compound_statement().accept(this)
  }

  // if_stmt : IF expression ':' suite (ELSE ':' suite)?   # IfInstr
  override def visitIfInstr(ctx: IfInstrContext ): Node = {
      val cond = ctx.expression().accept(this)
      val left = ctx.suite(0).accept(this)

      if(ctx.suite.size==1) {
          IfInstr(cond, left)
      }
      else {
          val right = ctx.suite(1).accept(this)
          IfElseInstr(cond, left, right)
      }
  }

  // expr_list_comma : expr_list opt_comma
  override def visitExpr_list_comma(ctx: Expr_list_commaContext ): Node = {
      ctx.expr_list().accept(this)
  }

  // key_datum : expression ':' expression  
  override def visitKey_datum(ctx: Key_datumContext ): KeyDatum = {
      val key = ctx.expression(0).accept(this)
      val value = ctx.expression(1).accept(this)
      KeyDatum(key, value)
  }

  // classdef : CLASS ID ('(' expr_list ','? ')')? ':' suite
  override def visitClassdef(ctx: ClassdefContext ): ClassDef = {
      val name = ctx.ID().getSymbol.getText
      val suite = ctx.suite().accept(this)
      if(ctx.expr_list()==null) {
          ClassDef(name, NodeList(List()), suite)
      }
      else {
          val inherit_list = ctx.expr_list().accept(this)
          ClassDef(name, inherit_list, suite)
      }
  }

  // program : module  
  override def visitProgram(ctx: ProgramContext ): Node = {
      ctx.module().accept(this)
  }

  // target : ID                              # Target_1
  override def visitTarget_1(ctx: Target_1Context): Variable = {
      Variable(ctx.ID().getSymbol.getText)
  }

  // target : subscription                    # Target_2
  override def visitTarget_2(ctx: Target_2Context): Node = {
      ctx.subscription().accept(this)
  }

  // target : expression '.' ID               # Target_3
  override def visitTarget_3(ctx: Target_3Context): GetAttr = {
      val expr = ctx.expression().accept(this)
      val attr = ctx.ID().getSymbol.getText
      GetAttr(expr, attr)
  }

  // suite : lpar statement_list rpar
  override def visitSuite(ctx: SuiteContext): Node = {
      ctx.statement_list().accept(this)
  }

  // simple_statement : small_statement_list ';'? NEWL+
  override def visitSimple_statement(ctx: Simple_statementContext): Node = {
      ctx.small_statement_list().accept(this)
  }

  // expr_list : /* empty */
  // expr_list : expression (',' expression )*      
  override def visitExpr_list(ctx: Expr_listContext ): NodeList = {
      val list = ctx.expression().asScala.toList.map(_.accept(this))
      NodeList(list)
  }

}
