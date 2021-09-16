module P4string = Types.P4string
module P4name = Types.P4name
module T = Typed
include Poulet4.Syntax

type coq_MethodPrototype = Types.tag Poulet4.Syntax.coq_MethodPrototype
type coq_Locator = Types.tag Poulet4.Syntax.coq_Locator
let noLocator = LGlobal []
type coq_ExpressionPreT = Types.tag Poulet4.Syntax.coq_ExpressionPreT
type coq_Expression = Types.tag Poulet4.Syntax.coq_Expression
type coq_MatchPreT = Types.tag Poulet4.Syntax.coq_MatchPreT
type coq_Match = Types.tag Poulet4.Syntax.coq_Match
type coq_TablePreActionRef = Types.tag Poulet4.Syntax.coq_TablePreActionRef
type coq_TableActionRef = Types.tag Poulet4.Syntax.coq_TableActionRef
type coq_TableKey = Types.tag Poulet4.Syntax.coq_TableKey
type coq_TableEntry = Types.tag Poulet4.Syntax.coq_TableEntry
type coq_TableProperty = Types.tag Poulet4.Syntax.coq_TableProperty
type coq_ValueBase = (Types.tag, bool) Poulet4.Syntax.coq_ValueBase
type coq_ValueSet = Types.tag Poulet4.Syntax.coq_ValueSet
type coq_StatementSwitchLabel = Types.tag Poulet4.Syntax.coq_StatementSwitchLabel
type coq_StatementSwitchCase = Types.tag Poulet4.Syntax.coq_StatementSwitchCase
type coq_StatementPreT = Types.tag Poulet4.Syntax.coq_StatementPreT
type coq_Statement = Types.tag Poulet4.Syntax.coq_Statement
type coq_Block = Types.tag Poulet4.Syntax.coq_Block
type coq_ParserCase = Types.tag Poulet4.Syntax.coq_ParserCase
type coq_ParserTransition = Types.tag Poulet4.Syntax.coq_ParserTransition
type coq_ParserState = Types.tag Poulet4.Syntax.coq_ParserState
type coq_DeclarationField = Types.tag Poulet4.Syntax.coq_DeclarationField
type coq_Declaration = Types.tag Poulet4.Syntax.coq_Declaration
type coq_ValueTable = Types.tag Poulet4.Syntax.coq_ValueTable
type coq_Env_EvalEnv = Types.tag Poulet4.Syntax.coq_Env_EvalEnv
type coq_ExternMethod = Types.tag Poulet4.Syntax.coq_ExternMethod
type coq_ExternMethods = Types.tag Poulet4.Syntax.coq_ExternMethods
type coq_ValuePreLvalue = Types.tag Poulet4.Syntax.coq_ValuePreLvalue
type coq_ValueLvalue = Types.tag Poulet4.Syntax.coq_ValueLvalue
type coq_ValueFunctionImplementation = Types.tag Poulet4.Syntax.coq_ValueFunctionImplementation
type coq_ValueObject = Types.tag Poulet4.Syntax.coq_ValueObject
type coq_ValueConstructor = Types.tag Poulet4.Syntax.coq_ValueConstructor
type coq_Value = (Types.tag, bool) Poulet4.Syntax.coq_Value
type program = Types.tag Poulet4.Syntax.program
  

(* Everything below this comment is runtime data structures and not
 * program syntax.
 *)
type buf = Cstruct_sexp.t
type pkt = {
  emitted: buf;
  main: buf;
  in_size: int;
}
type loc = P4string.t
type entries = (Ast.qualified_name * (int option * Ast.match_ list * Ast.action * Ast.id option) list) list * (Ast.qualified_name * Ast.action list) list

type vsets = coq_Match list list

type ctrl = entries * vsets

type signal =
  | SContinue
  | SReturn of coq_Value
  | SExit
  | SReject of P4string.t
