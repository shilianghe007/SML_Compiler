#include "KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <sstream>
//#include "toy.h"
// using std::string;
using namespace llvm;
using namespace llvm::orc;
// std::map<std::string, Value *> varTable;//用来存全局变量

//让我们一起画树吧！（默认为不画树）
bool DadyLetsDrawTree = 0;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
	tok_eof = -1, //结尾
	// commands
	tok_def = -2, //定义
	// let definition
	tok_let = -3,
	// primary
	tok_identifier = -4, //标识符
	tok_real = -5,       // double
	tok_int = -6,        // int
	tok_string = -7,     // string
	tok_char = -8,       // char
	// control,控制流
	tok_if = -9,
	tok_then = -10,
	tok_else = -11,
	tok_while = -12,
	tok_do = -13,
	tok_in = -16,
	tok_end = -17,
	// operators
	tok_binary = -14,
	tok_unary = -15,
	// 变量声明符
	tok_val = -18,
	//分号
	tok_semi = -19,
	// print
	tok_print = -20,
	tok_change = -21
};

static std::string IdentifierStr; // Filled in if tok_identifier
static double NumVal;             // Filled in if tok_real or tok_int
static std::string StringVal;     // 存储string和char变量
static int LastChar = ' ';

/// gettok - Return the next token from standard input.
static int gettok() {

	// Skip any whitespace和逗号.
	while (isspace(LastChar) || LastChar == ',')
		// while (isspace(LastChar))
		LastChar = getchar();
	if (LastChar == ';') {
		LastChar = getchar();
		return tok_semi;
	}
	if (isalpha(LastChar)) { // identifier: [a-zA-Z][a-zA-Z0-9]*
		IdentifierStr = LastChar;
		while (isalnum((LastChar = getchar())))
			IdentifierStr += LastChar;

		if (IdentifierStr == "fun")
			return tok_def;
		if (IdentifierStr == "let")
			return tok_let;
		if (IdentifierStr == "in")
			return tok_in;
		if (IdentifierStr == "if")
			return tok_if;
		if (IdentifierStr == "then")
			return tok_then;
		if (IdentifierStr == "else")
			return tok_else;
		if (IdentifierStr == "while")
			return tok_while;
		if (IdentifierStr == "do")
			return tok_do;
		if (IdentifierStr == "binary")
			return tok_binary;
		if (IdentifierStr == "end")
			return tok_end;
		if (IdentifierStr == "unary")
			return tok_unary;
		if (IdentifierStr == "val")
			return tok_val;
		if (IdentifierStr == "print")
			return tok_print;
		if (IdentifierStr == "changemode")
			return tok_change;
		return tok_identifier; //其他标识符
	}
	// real&int
	if (isdigit(LastChar)) { // Number: [0-9]+
		int type = 0;
		std::string NumStr;
		do {
			if (LastChar == '.' && LastChar == 1) {
				break;
			}
			if (LastChar == '.' && LastChar == 0) {
				type = 1;
			}
			NumStr += LastChar;
			LastChar = getchar();
		} while (isdigit(LastChar) || LastChar == '.');

		NumVal = strtod(NumStr.c_str(), nullptr);
		if (type == 1) {
			return tok_real;
		}
		return tok_int;
	}
	// string&char
	// if (LastChar == '"') {
	//  std::string StringStr = "";
	//  getchar(); // eat '"'
	//  int num = 0;
	//  while (LastChar != '"') {
	//    StringStr += LastChar;
	//    num++;
	//    getchar();
	//  }

	//  if (num == 0 || num == 1) {
	//    return tok_char;
	//  } else {
	//    return tok_string;
	//  }
	//}

	// TODO：注释
	if (LastChar == '#') {
		// Comment until end of line.
		do
			LastChar = getchar();
		while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

		if (LastChar != EOF)
			return gettok();
	}

	// Check for end of file.  Don't eat the EOF.
	if (LastChar == EOF)
		return tok_eof;

	// Otherwise, just return the character as its ascii value.
	int ThisChar = LastChar;
	LastChar = getchar();
	return ThisChar;
}

//===----------------------------------------------------------------------===//
// Abstract Syntax Tree (aka Parse Tree)
//===----------------------------------------------------------------------===//

namespace {

	/// ExprAST - Base class for all expression nodes.
	//各类Expr派生节点的type值：
	// RealExprAST：1
	// IntExprAST：2
	// CharExprAST：3
	// StringExprAST：4
	// VariableExprAST：5
	// UnaryExprAST：6
	// BinaryExprAST：7
	// CallExprAST：8
	// ExprsAST：9
	// IfExprAST：10
	// LetExprAST(val类型)：11
	// LetExprAST(fun类型)：12
	// whileExprAST：13
	// printExprAST:14

	class FunctionAST;

	class ExprAST {
	public:
		int type;

		virtual ~ExprAST() = default;

		virtual Value *codegen() = 0;

		virtual std::unique_ptr<FunctionAST> getFun() = 0;

		virtual void printTree(int level) = 0;

		ExprAST(int t) { type = t; }
	};

	//用于输出的print节点
	class PrintExprAST : public ExprAST {
	public:
		std::string val;
		bool type; // 0:字符串   1:变量
		PrintExprAST(std::string val, bool type)
			: val(val), type(type), ExprAST(14) {}

		Value *codegen() override;

		void printTree(int level) override;

		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	/// RealExprAST - Expression class for numeric literals like "1.0".
	class RealExprAST : public ExprAST {
		double Val;

	public:
		RealExprAST(double Val) : Val(Val), ExprAST(1) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	/// IntExprAST - Expression class for numeric literals like "1".
	class IntExprAST : public ExprAST {
		double Val;

	public:
		IntExprAST(double Val) : Val(Val), ExprAST(2) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	///// CharExprAST - Expression class for numeric literals like 's'.
	// class CharExprAST : public ExprAST {
	//  char Val;
	//
	// public:
	//  CharExprAST(char Val) : Val(Val)  ,ExprAST(3){}
	//
	//  Value *codegen() override;
	// std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	//};
	///// StringExprAST - Expression class for numeric literals like "dwd".
	// class StringExprAST : public ExprAST {
	//  std::string Val;
	//
	// public:
	//  StringExprAST(std::string Val) : Val(Val)  ,ExprAST(4){}
	//
	//  Value *codegen() override;

	// std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	//};

	/// VariableExprAST - Expression class for referencing a variable, like "a".
	// 函数参数节点
	class VariableExprAST : public ExprAST {
		std::string Name;

	public:
		VariableExprAST(const std::string &Name) : Name(Name), ExprAST(5) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
		const std::string &getName() const { return Name; }
	};

	/// UnaryExprAST - Expression class for a unary operator.
	// 一元运算符
	class UnaryExprAST : public ExprAST {
		char Opcode;
		std::unique_ptr<ExprAST> Operand;

	public:
		UnaryExprAST(char Opcode, std::unique_ptr<ExprAST> Operand)
			: Opcode(Opcode), Operand(std::move(Operand)), ExprAST(6) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	/// BinaryExprAST - Expression class for a binary operator.
	// 二元运算符
	class BinaryExprAST : public ExprAST {
		char Op;
		std::unique_ptr<ExprAST> LHS, RHS;

	public:
		BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
			std::unique_ptr<ExprAST> RHS)
			: Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)), ExprAST(7) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	/// CallExprAST - Expression class for function calls.
	// 函数调用
	class CallExprAST : public ExprAST {
		std::string Callee;
		std::vector<std::unique_ptr<ExprAST>> Args;

	public:
		CallExprAST(const std::string &Callee,
			std::vector<std::unique_ptr<ExprAST>> Args)
			: Callee(Callee), Args(std::move(Args)), ExprAST(8) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	//语句块
	class ExprsAST : public ExprAST {
		std::vector<std::unique_ptr<ExprAST>> Exprs;

	public:
		ExprsAST(std::vector<std::unique_ptr<ExprAST>> Exprs)
			: Exprs(std::move(Exprs)), ExprAST(9) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	/// IfExprAST - Expression class for if/then/else.
	class IfExprAST : public ExprAST {
		std::unique_ptr<ExprAST> Cond, Then, Else;

	public:
		IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then,
			std::unique_ptr<ExprAST> Else)
			: Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)),
			ExprAST(10) {}

		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	// while循环的节点
	class whileExprAST : public ExprAST {
		std::string VarName;
		std::unique_ptr<ExprAST> Start, End, Step, Body;

	public:
		whileExprAST(const std::string &VarName, std::unique_ptr<ExprAST> Start,
			std::unique_ptr<ExprAST> End, std::unique_ptr<ExprAST> Step,
			std::unique_ptr<ExprAST> Body)
			: VarName(VarName), Start(std::move(Start)), End(std::move(End)),
			Step(std::move(Step)), Body(std::move(Body)), ExprAST(13) {}
		Value *codegen() override;
		void printTree(int level) override;
		std::unique_ptr<FunctionAST> getFun() override { return nullptr; };
	};

	/// LetExprAST - Expression class for let/in
	// 这才是真正的局部变量定义
	class LetExprAST : public ExprAST {
		std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> LetNames;
		std::unique_ptr<ExprAST> Body;
		std::unique_ptr<FunctionAST> insideFun;

	public:
		//构造函数
		LetExprAST(
			std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> LetNames,
			std::unique_ptr<ExprAST> Body, std::unique_ptr<FunctionAST> Fun, int type)
			: LetNames(std::move(LetNames)), Body(std::move(Body)),
			insideFun(std::move(Fun)), ExprAST(type) {}
		//返回嵌套函数
		std::unique_ptr<FunctionAST> getFun() override {
			return std::move(insideFun);
		}
		Value *codegen() override;
		void printTree(int level) override;
	};

	/// PrototypeAST - This class represents the "prototype" for a function,
	/// which captures its name, and its argument names (thus implicitly the number
	/// of arguments the function takes), as well as if it is an operator.
	class PrototypeAST {
		std::string Name;
		std::vector<std::string> Args;
		bool IsOperator;
		unsigned Precedence; // Precedence if a binary op.

	public:
		PrototypeAST(const std::string &Name, std::vector<std::string> Args,
			bool IsOperator = false, unsigned Prec = 0)
			: Name(Name), Args(std::move(Args)), IsOperator(IsOperator),
			Precedence(Prec) {}

		Function *codegen();
		void printTree(int level);
		const std::string &getName() const { return Name; }
		// 对普通原型的扩充（自定义运算符）
		bool isUnaryOp() const { return IsOperator && Args.size() == 1; }
		bool isBinaryOp() const { return IsOperator && Args.size() == 2; }

		char getOperatorName() const {
			assert(isUnaryOp() || isBinaryOp());
			return Name[Name.size() - 1];
		}

		unsigned getBinaryPrecedence() const { return Precedence; }
	};

	/// FunctionAST - This class represents a function definition itself.
	class FunctionAST {
	public:
		std::unique_ptr<PrototypeAST> Proto;
		std::unique_ptr<ExprAST> Body;
		FunctionAST(std::unique_ptr<PrototypeAST> Proto,
			std::unique_ptr<ExprAST> Body)
			: Proto(std::move(Proto)), Body(std::move(Body)) {}
		virtual ~FunctionAST() = default;
		Function *codegen();
		void printTree(int level);
	};

	class GVAST {
	public:
		std::string GVname;
		double numVal;
		GVAST(const std::string &name, double val) : GVname(name), numVal(val) {}
		virtual ~GVAST() = default;
		GlobalVariable *codegen();
		void printTree(int level);
	};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Print Tree
//===----------------------------------------------------------------------===//
void LetExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "LetExprAST:\n";
	//依次输出参数的树
	if (type == 11) {
		std::cout << preStr << "    "
			<< "局部变量定义：\n";
		for (int i = 0; i < LetNames.size(); i++) {
			std::cout << preStr << "        " << LetNames[i].first << ":\n";
			LetNames[i].second.get()->printTree(level + 3);
		}
	}
	else {
		std::cout << preStr << "    "
			<< "嵌套函数节点：\n";
		insideFun->printTree(level + 2);
	}

	std::cout << preStr << "    "
		<< "in部分节点：\n";
	Body->printTree(level + 2);
}
void FunctionAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "FunctionAST:\n";
	//依次输出声明和函数主体的树
	Proto->printTree(level + 1);
	std::cout << preStr << "    "
		<< "函数主体:\n";
	Body->printTree(level + 2);
}
void PrototypeAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "PrototypeAST:";
	//依次输出参数的树
	std::cout << "函数名：" << Name << "  ";
	for (int i = 0; i < Args.size(); i++) {
		std::cout << "参数名：" << Args[i] << "  ";
	}
	std::cout << "\n";
}
void IfExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "IfElseThenAST:\n";
	//依次输出参数的树
	std::cout << preStr << "    "
		<< "判断条件节点：\n";
	Cond->printTree(level + 2);
	std::cout << preStr << "    "
		<< "条件为真节点：\n";
	Then->printTree(level + 2);
	std::cout << preStr << "    "
		<< "条件为假节点：\n";
	Else->printTree(level + 2);
}
void PrintExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "PrintExprAST: StrVal:  " << val << "\n";
}
void RealExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "RealExprAST: NumVal:  " << Val << "\n";
}
void IntExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "IntExprAST: NumVal:  " << (int)(Val) << "\n";
}
void VariableExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "VariableExprAST: VarName:  " << Name << "\n";
}
void UnaryExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "UnaryExprAST: OperatorName:  " << Opcode << "\n";
}
void BinaryExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "BinaryExprAST: OperatorName:  " << Op << "\n";
	//依次输出左右操作数的树
	std::cout << preStr << "    "
		<< "左操作数节点：\n";
	LHS->printTree(level + 2);
	std::cout << preStr << "    "
		<< "右操作数节点：\n";
	RHS->printTree(level + 2);
}
void CallExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "CallExprAST: CallName:  " << Callee << "\n";
	//依次输出参数的树
	for (int i = 0; i < Args.size(); i++) {
		std::cout << preStr << "    "
			<< "参数节点：\n";
		Args[i]->printTree(level + 2);
	}
}
void ExprsAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "ExprsAST:\n";
	//依次输出参数的树
	for (int i = 0; i < Exprs.size(); i++) {
		Exprs[i]->printTree(level + 1);
	}
}
void whileExprAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "whileExprAST:\n";
	//依次输出参数的树
	std::cout << preStr << "    "
		<< "循环条件节点：\n";
	End->printTree(level + 2);
	std::cout << preStr << "    "
		<< "循环主体节点：\n";
	Body->printTree(level + 2);
}
void GVAST::printTree(int level) {
	std::string preStr = ""; // 打印前缀
	for (int i = 0; i < level; i++) {
		preStr += "    ";
	}
	std::cout << preStr << "GlobalVariableAST:  name:" << GVname
		<< "  value:" << numVal;
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

//一些关于函数中|的定义的全局变量(parse处理时会更新这些值)
std::string FnName;              //函数名
double condNum;                  //判断参数是否等于的数值
bool LineFun = 0;                //是否是带|的函数，默认为0
std::unique_ptr<PrototypeAST> P; //全局proto
std::unique_ptr<ExprAST> B;      //全局Expr

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() { return CurTok = gettok(); }

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
	if (!isascii(CurTok))
		return -1;

	// Make sure it's a declared binop.
	int TokPrec = BinopPrecedence[CurTok];
	if (TokPrec <= 0)
		return -1;
	return TokPrec;
}

/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ExprAST> LogError(const char *Str) {
	fprintf(stderr, "Error: %s\n", Str);
	return nullptr;
}

std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
	LogError(Str);
	return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression();

// print "..."      print (变量名)
static std::unique_ptr<ExprAST> ParsePrintExpr() {
	getNextToken(); // eat 'print'
	std::string name = " ";
	if (CurTok == '(') {
		getNextToken(); // eat '('
		name = IdentifierStr;
		getNextToken(); // eat 变量
		if (CurTok != ')') {
			return LogError("expected ')'");
		}
		getNextToken(); // eat ‘)’
		return llvm::make_unique<PrintExprAST>(name, 1);
	}
	else if (CurTok == '"') {
		// IdentifierStr = LastChar; //第一个字符
		//                          //识别符号串
		// while ((LastChar = getchar()) != '"') {
		//  IdentifierStr += LastChar;
		//}
		// if (IdentifierStr != "\"")
		//  name = IdentifierStr;
		// getNextToken(); // eat '"'
		getNextToken(); // eat '"'
		name = IdentifierStr;
		getNextToken(); // eat 字符串
		if (CurTok != '"') {
			return LogError("expected \"");
		}
		getNextToken(); // eat ‘"’
		return llvm::make_unique<PrintExprAST>(name, 0);
	}
}

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseRealExpr() {
	auto Result = llvm::make_unique<RealExprAST>(NumVal);
	getNextToken(); // consume the number
	return std::move(Result);
}
/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseIntExpr() {
	auto Result = llvm::make_unique<IntExprAST>(NumVal);
	getNextToken(); // consume the number
	return std::move(Result);
}
///// numberexpr ::= number
// static std::unique_ptr<ExprAST> ParseStringExpr() {
//  auto Result = llvm::make_unique<StringExprAST>(StringVal);
//  getNextToken(); // consume the number
//  return std::move(Result);
//}
///// numberexpr ::= number
// static std::unique_ptr<ExprAST> ParseCharExpr() {
//  auto Result = llvm::make_unique<CharExprAST>(StringVal);
//  getNextToken(); // consume the number
//  return std::move(Result);
//}

/// parenexpr ::= '(' expression ')'
// 由括号包括的expr
static std::unique_ptr<ExprAST> ParseParenExpr() {
	getNextToken(); // eat (.
	auto V = ParseExpression();
	if (!V)
		return nullptr;

	if (CurTok != ')')
		return LogError("expected ')'");
	getNextToken(); // eat ).
	return V;
}

/// identifierexpr
///   ::= identifier   变量
///   ::= identifier '(' expression* ')'    函数调用
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
	std::string IdName = IdentifierStr;

	getNextToken(); // eat identifier.

	if (CurTok != '(') // Simple variable ref.
		return llvm::make_unique<VariableExprAST>(IdName);

	// Call.
	getNextToken(); // eat (
	std::vector<std::unique_ptr<ExprAST>> Args;
	if (CurTok != ')') {
		while (true) {
			if (auto Arg = ParseExpression())
				Args.push_back(std::move(Arg));
			else
				return nullptr;

			if (CurTok == ')')
				break;

			/*if (CurTok != ',')
			  return LogError("Expected ')' or ',' in argument list");*/
			  // getNextToken();
		}
	}

	// Eat the ')'.
	getNextToken();

	return llvm::make_unique<CallExprAST>(IdName, std::move(Args));
}

/// ifexpr ::= 'if' expression 'then' expression 'else' expression
static std::unique_ptr<ExprAST> ParseIfExpr() {
	getNextToken(); // eat the if.

	// condition.
	auto Cond = ParseExpression();
	if (!Cond)
		return nullptr;

	if (CurTok != tok_then)
		return LogError("expected then");
	getNextToken(); // eat the then

	auto Then = ParseExpression();
	if (!Then)
		return nullptr;

	if (CurTok != tok_else)
		return LogError("expected else");

	getNextToken();
	auto Else = ParseExpression();
	if (!Else)
		return nullptr;
	return llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
		std::move(Else));
}

static std::unique_ptr<FunctionAST> ParseDefinition();

// 局部变量与let in语句
// letexpr ::= 'let' identifier ('=' expression)?
//                  (',' identifier ('=' expression)?)* 'in' expression
//示例： let val a = 9 in a;     let fun a(s) = 8 in a(d)
//注意：在let和in后都支持多条语句，且语句间分号是可选的。
static std::unique_ptr<ExprAST> ParseLetExpr() {
	getNextToken(); // eat the let.

	std::vector<std::pair<std::string, std::unique_ptr<ExprAST>>> LetNames;
	std::vector<std::unique_ptr<ExprAST>> Exprs;
	// auto insideFuntion = nullptr;   放弃这种尝试
	// At least one variable name is required.
	if (CurTok != tok_val && CurTok != tok_def)
		return LogError("expected val or fun after let");

	if (CurTok == tok_val) {
		while (true) {
			getNextToken(); // eat val
			std::string Name = IdentifierStr;
			getNextToken(); // eat val & identifier.

			// Read the optional initializer.
			std::unique_ptr<ExprAST> Init = nullptr;
			if (CurTok == '=') {
				getNextToken(); // eat the '='.

				Init = ParseExpression();
				if (!Init)
					return nullptr;
			}

			LetNames.push_back(std::make_pair(Name, std::move(Init)));
			//多个val之间可以打分号也可以不打
			if (CurTok == tok_semi) {
				getNextToken();
			}

			// End of let list, exit loop.
			if (CurTok == tok_in)
				break;
			// getNextToken();

			if (CurTok != tok_val)
				return LogError("expected val after let");
		}
		auto insideFuntion = nullptr;

		//后面是很傻逼的代码
		// At this point, we have to have 'in'.
		if (CurTok != tok_in)
			return LogError("expected 'in' keyword after 'let'");

		getNextToken(); // eat 'in'.

		auto Expr = ParseExpression();
		if (!Expr)
			return nullptr;
		if (CurTok == tok_semi) {
			getNextToken();
		}
		Exprs.push_back(std::move(Expr));
		while (CurTok != tok_end) {
			Expr = ParseExpression();
			if (!Expr)
				return nullptr;
			if (CurTok == tok_semi) {
				getNextToken();
			}
			Exprs.push_back(std::move(Expr));
		}

		if (CurTok != tok_end)
			return LogError("expected 'end' keyword after 'in'");
		getNextToken(); // eat 'end'.
		auto Body = llvm::make_unique<ExprsAST>(std::move(Exprs));
		return llvm::make_unique<LetExprAST>(std::move(LetNames), std::move(Body),
			std::move(insideFuntion), 11);
	}
	else if (CurTok == tok_def) {
		//如果读到的是fun，则转换函数定义(bug:这里的fun应该还能在全局调用)
		auto insideFuntion = ParseDefinition();

		if (CurTok == ';') {
			getNextToken(); // eat ';'
		}

		//后面是很傻逼的代码
		// At this point, we have to have 'in'.
		if (CurTok != tok_in)
			return LogError("expected 'in' keyword after 'let'");

		getNextToken(); // eat 'in'.

		auto Expr = ParseExpression();
		if (!Expr)
			return nullptr;
		if (CurTok == tok_semi) {
			getNextToken();
		}
		Exprs.push_back(std::move(Expr));
		while (CurTok != tok_end) {
			Expr = ParseExpression();
			if (!Expr)
				return nullptr;
			if (CurTok == tok_semi) {
				getNextToken();
			}
			Exprs.push_back(std::move(Expr));
		}

		if (CurTok != tok_end)
			return LogError("expected 'end' keyword after 'in'");
		getNextToken(); // eat 'end'.
		auto Body = llvm::make_unique<ExprsAST>(std::move(Exprs));
		return llvm::make_unique<LetExprAST>(std::move(LetNames), std::move(Body),
			std::move(insideFuntion), 12);
	}
	// return nullptr;
}

static std::unique_ptr<ExprAST> ParseWhile();

/// primary
///   ::= identifierexpr
///   ::= numberexpr 4种
///   ::= parenexpr
///   ::= ifexpr
///   ::= letexpr
static std::unique_ptr<ExprAST> ParsePrimary() {
	switch (CurTok) {
	default:
		return LogError("unknown token when expecting an expression");
	case tok_identifier:
		return ParseIdentifierExpr();
	case tok_real:
		return ParseRealExpr();
		/* case tok_char:
		   return ParseCharExpr();*/
	case tok_int:
		return ParseIntExpr();
		/* case tok_string:
		   return ParseStringExpr();*/
	case '(':
		return ParseParenExpr();
	case tok_if:
		return ParseIfExpr();
	case tok_let:
		return ParseLetExpr();
	case tok_while:
		return ParseWhile();
	case tok_print:
		return ParsePrintExpr();
	}
}

// 自定义一元运算符
/// unary
///   ::= primary
///   ::= '!' unary
static std::unique_ptr<ExprAST> ParseUnary() {
	// If the current token is not an operator, it must be a primary expr.
	if (!isascii(CurTok) || CurTok == '(' || CurTok == ',')
		return ParsePrimary();

	// If this is a unary operator, read it.
	int Opc = CurTok;
	getNextToken();
	if (auto Operand = ParseUnary())
		return llvm::make_unique<UnaryExprAST>(Opc, std::move(Operand));
	return nullptr;
}

/// binoprhs
///   ::= ('+' unary)*
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
	std::unique_ptr<ExprAST> LHS) {
	// If this is a binop, find its precedence.
	while (true) {
		//判断优先级
		int TokPrec = GetTokPrecedence();

		// If this is a binop that binds at least as tightly as the current binop,
		// consume it, otherwise we are done.
		if (TokPrec < ExprPrec)
			return LHS;

		// Okay, we know this is a binop.
		int BinOp = CurTok;
		getNextToken(); // eat binop

		// Parse the unary expression after the binary operator.
		auto RHS = ParseUnary();
		if (!RHS)
			return nullptr;

		// If BinOp binds less tightly with RHS than the operator after RHS, let
		// the pending operator take RHS as its LHS.
		int NextPrec = GetTokPrecedence();
		if (TokPrec < NextPrec) {
			RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
			if (!RHS)
				return nullptr;
		}

		// Merge LHS/RHS.
		LHS =
			llvm::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
	}
}

/// expression
///   ::= unary binoprhs
///
static std::unique_ptr<ExprAST> ParseExpression() {
	auto LHS = ParseUnary();
	if (!LHS)
		return nullptr;

	return ParseBinOpRHS(0, std::move(LHS));
}

// parse whileExprAST
//示例：while ... do(exp1;exp2;...)
static std::unique_ptr<ExprAST> ParseWhile() {

	std::vector<std::unique_ptr<ExprAST>> Exprs;
	getNextToken(); // eat the while.
	auto end = ParseExpression();
	if (!end)
		return nullptr;
	if (CurTok != tok_do) {
		return LogError("expected 'do' after while condition value");
	}
	getNextToken(); // eat do
	if (CurTok != '(') {
		return LogError("expected '(' after 'do'");
	}
	getNextToken(); // eat '('
	auto Expr = ParseExpression();
	if (!Expr)
		return nullptr;
	if (CurTok == tok_semi) {
		getNextToken();
	}
	Exprs.push_back(std::move(Expr));
	while (CurTok != ')') {
		Expr = ParseExpression();
		if (!Expr)
			return nullptr;
		if (CurTok == tok_semi) {
			getNextToken(); // eat ';'
		}
		Exprs.push_back(std::move(Expr));
	}
	getNextToken(); // eat ')'

	//制造初始条件（start）
	auto start = llvm::make_unique<RealExprAST>(0);
	//制造步长（step）
	auto step = llvm::make_unique<RealExprAST>(1);

	auto body = llvm::make_unique<ExprsAST>(std::move(Exprs));

	return std::make_unique<whileExprAST>("slh", std::move(start), std::move(end),
		std::move(step), std::move(body));
}

// pat
static std::string ParsePattern(void) {
	switch (CurTok) {
	case '(':
	case ',': {
		getNextToken(); // eat '(' || ','
		std::string Arg = ParsePattern();
		if (Arg == "")
			return 0;
		getNextToken(); // eat arg
		return Arg;
	}
	case tok_identifier: {
		std::string IdName = IdentifierStr;
		getNextToken(); // eat 'id'
		return IdName;
	}
	case tok_real:
	case tok_int: {
		std::string IdName = std::to_string(NumVal);
		condNum = NumVal;
		getNextToken(); // eat 'id'
		return IdName;
	}
	default:
		return nullptr;
	}
}


static void ParseFun() {
	if (CurTok == ')') {
		getNextToken(); // eat ')'
	}
	if (CurTok == '=') {
		getNextToken();
	}
	else {
		printf("未输入等于号");
	}
	std::unique_ptr<ExprAST> thenBB = ParseExpression(); //得到then节点
	if (CurTok != '|') {
		printf("未输入字符|");
	}
	getNextToken(); // eat  '|'
	if (CurTok != tok_identifier) {
		printf("未输入函数名");
	}
	getNextToken(); // eat FnName
	if (CurTok == '(') {
		getNextToken(); // eat '('
	}
	if (CurTok != tok_identifier) {
		printf("未输入参数名");
	}
	std::string ArgName = IdentifierStr;
	std::vector<std::string> Args;
	Args.push_back(ArgName);
	getNextToken(); // eat 参数名
	if (CurTok == ')') {
		getNextToken(); // eat ')'
	}
	if (CurTok != '=') {
		printf("未输入等于号");
	}
	getNextToken();                                      // eat '='
	std::unique_ptr<ExprAST> elseBB = ParseExpression(); //得到else节点

	//以下是在试图创建条件节点
	std::unique_ptr<ExprAST> LHS =
		llvm::make_unique<VariableExprAST>(ArgName); //创建变量节点
	std::unique_ptr<ExprAST> RHS = llvm::make_unique<RealExprAST>(condNum);

	// Merge LHS/RHS.
	std::unique_ptr<ExprAST> ifBB = llvm::make_unique<BinaryExprAST>(
		(int)'~', std::move(LHS), std::move(RHS)); //得到condition节点

	//组合成一个总体的if节点
	B = llvm::make_unique<IfExprAST>(std::move(ifBB), std::move(thenBB),
		std::move(elseBB));

	P = llvm::make_unique<PrototypeAST>(FnName, Args, 0 != 0, 30);
}

/// prototype
///   ::= id '(' id* ')'
///   ::= binary LETTER number? (id, id)
///   ::= unary LETTER (id)
static std::unique_ptr<PrototypeAST> ParsePrototype() {

	unsigned Kind = 0; // 0 = identifier, 1 = unary, 2 = binary.
	unsigned BinaryPrecedence = 30;

	switch (CurTok) {
	default:
		return LogErrorP("Expected function name in prototype");
	case tok_identifier:
		FnName = IdentifierStr;
		Kind = 0;
		getNextToken();
		break;
	}
	std::vector<std::string> Args;
	while (1) {
		std::string Arg = ParsePattern();
		if (47 < (char)Arg[0] && 58 > (char)Arg[0]) {
			ParseFun(); //发现这是一个带|的函数，于是跳入特殊的函数处理函数中处理
			LineFun = 1; //将值置1，通知ParseDefinition函数，我们遇到了带|的函数
			//condNum = atof(&Arg[]);
			return llvm::make_unique<PrototypeAST>(FnName, Args, Kind != 0,
				BinaryPrecedence);
		}
		Args.push_back(Arg);
		if (CurTok == ')') {
			getNextToken(); // eat ')'
			break;
		}
		if (CurTok == '=')
			break;
	}
	if (CurTok == '=')
		getNextToken(); // eat '='
	else
		return LogErrorP("Not find '=' after proto");

	// Verify right number of names for operator.
	if (Kind && Args.size() != Kind)
		return LogErrorP("Invalid number of operands for operator");

	return llvm::make_unique<PrototypeAST>(FnName, Args, Kind != 0,
		BinaryPrecedence);
}

/// definition ::= 'fun' prototype expression
static std::unique_ptr<FunctionAST> ParseDefinition() {
	getNextToken(); // eat fun.
	auto Proto = ParsePrototype();
	if (LineFun == 1) { //检查是不是特殊的函数，如果是则进入该通道
		LineFun = 0;
		return llvm::make_unique<FunctionAST>(std::move(P), std::move(B));
	}
	if (!Proto)
		return nullptr;

	if (auto E = ParseExpression())
		return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
	return nullptr;
}

//  全局变量的定义
static std::unique_ptr<GVAST> ParseGlobalVarible() {
	getNextToken(); // eat 'val'
	std::string name = IdentifierStr;
	getNextToken(); // eat 变量名
	if (CurTok != '=') {
		std::cout << "here should be 'val'";
	}
	getNextToken(); // eat '='
	double num = NumVal;
	getNextToken(); // eat value
	return llvm::make_unique<GVAST>(name, num);
}

/// toplevelexpr ::= expression
// 其实就是将一切表达式都视为一种原型
static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
	if (auto E = ParseExpression()) {
		// Make an anonymous proto.
		auto Proto = llvm::make_unique<PrototypeAST>("__anon_expr",
			std::vector<std::string>());
		return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
	}
	return nullptr;
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, AllocaInst *> NamedValues;
static std::map<std::string, GlobalVariable *> GlobalValues;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

Value *LogErrorV(const char *Str) {
	LogError(Str);
	return nullptr;
}

Function *getFunction(std::string Name) {
	// First, see if the function has already been added to the current module.
	if (auto *F = TheModule->getFunction(Name))
		return F;

	// If not, check whether we can codegen the declaration from some existing
	// prototype.
	auto FI = FunctionProtos.find(Name);
	if (FI != FunctionProtos.end())
		return FI->second->codegen();

	// If no existing prototype exists, return null.
	return nullptr;
}

/// CreateEntryBlockAlloca - Create an alloca instruction in the entry block of
/// the function.  This is used for mutable variables etc.
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
	const std::string &LetName) {
	IRBuilder<> TmpB(&TheFunction->getEntryBlock(),
		TheFunction->getEntryBlock().begin());
	return TmpB.CreateAlloca(Type::getDoubleTy(TheContext), nullptr, LetName);
}

Value *RealExprAST::codegen() {
	return ConstantFP::get(TheContext, APFloat(Val));
}
Value *IntExprAST::codegen() {
	return ConstantFP::get(TheContext, APFloat(Val));
}
// Value *CharExprAST::codegen() {
//  return ConstantFP::get(TheContext, APFloat(0.0));
//}
// Value *StringExprAST::codegen() {
//  return ConstantFP::get(TheContext, APFloat(0.0));
//}
// TODO
// string和char的codegen

Value *ExprsAST::codegen() {
	Value *val = nullptr;
	for (unsigned i = 0, e = Exprs.size(); i != e; ++i) {
		val = Exprs[i]->codegen();
	}
	return val;
}
static void InitializeModule();
Value *PrintExprAST::codegen() {
	if (type == 0) {
		///输出字符串
		//首先声明函数extern（引入dll）
		std::vector<std::string> ArgNames;
		ArgNames.push_back("X");
		if (auto ProtoAST =
			llvm::make_unique<PrototypeAST>("putchard", ArgNames, false, 30)) {
			if (auto *FnIR = ProtoAST->codegen()) {
				FnIR->print(errs()); //输出：declare double @putchard(double)
				FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
			}
		}
		//将其拆分成很多个字符分别输出，调用extern“C”函数
		std::string pp = val;
		double singleChar = (double)' ';
		for (int i = 0; i < pp.length(); i++) {
			singleChar = (double)pp[i];
			//构造参数vector<ExprAST>
			std::vector<std::unique_ptr<ExprAST>> Args;
			auto argAST = llvm::make_unique<RealExprAST>(singleChar);
			Args.push_back(std::move(argAST));
			auto callAST =
				llvm::make_unique<CallExprAST>("putchard", std::move(Args));
			// return callAST->codegen();
		}
		//咳咳
		char context[200];
		int i;
		for (i = 0; i < pp.length(); i++) {
			context[i] = pp[i];
		}
		context[i] = '\0';
		printf(context);
		printf("\n");
		return nullptr;
	}
	else {
		//输出变量
		//咳咳
		if (llvm::make_unique<VariableExprAST>(val)->codegen()) {
			// JIT the module containing the anonymous expression, keeping a handle so
			// we can free it later.
			auto H = TheJIT->addModule(std::move(TheModule));
			InitializeModule();

			// Search the JIT for the __anon_expr symbol.
			auto ExprSymbol = TheJIT->findSymbol("__anon_expr");
			assert(ExprSymbol && "Function not found");

			// Get the symbol's address and cast it to the right type (takes no
			// arguments, returns a double) so we can call it as a native function.
			double(*FP)() =
				(double(*)())(intptr_t)cantFail(ExprSymbol.getAddress());
			fprintf(stderr, "%f\n", FP());

			// Delete the anonymous expression module from the JIT.
			TheJIT->removeModule(H);
		}
		return nullptr;
	}
}

Value *VariableExprAST::codegen() {
	// Look this variable up in the function.
	Value *V = NamedValues[Name];
	if (!V) {
		V = (AllocaInst *)GlobalValues[Name];
		if (!V) {
			return LogErrorV("Unknown variable name");
		}
	}
	// Load the value.
	return Builder.CreateLoad(V, Name.c_str());
}

Value *UnaryExprAST::codegen() {
	Value *OperandV = Operand->codegen();
	if (!OperandV)
		return nullptr;

	Function *F = getFunction(std::string("unary") + Opcode);
	if (!F)
		return LogErrorV("Unknown unary operator");

	return Builder.CreateCall(F, OperandV, "unop");
}

Value *BinaryExprAST::codegen() {
	// Special case '=' because we don't want to emit the LHS as an expression.
	if (Op == '=') {
		// Assignment requires the LHS to be an identifier.
		// This assume we're building without RTTI because LLVM builds that way by
		// default.  If you build LLVM with RTTI this can be changed to a
		// dynamic_cast for automatic error checking.
		VariableExprAST *LHSE = static_cast<VariableExprAST *>(LHS.get());
		if (!LHSE)
			return LogErrorV("destination of '=' must be a variable");
		// Codegen the RHS.
		Value *Val = RHS->codegen();
		if (!Val)
			return nullptr;

		// Look up the name.
		Value *Variable = NamedValues[LHSE->getName()];
		if (!Variable) {
			Variable = GlobalValues[LHSE->getName()];
			if (!Variable)
				return LogErrorV("Unknown variable name");
		}

		Builder.CreateStore(Val, Variable);
		return Val;
	}

	Value *L = LHS->codegen();
	Value *R = RHS->codegen();
	if (!L || !R)
		return nullptr;

	switch (Op) {
	case '+':
		return Builder.CreateFAdd(L, R, "addtmp");
	case '-':
		return Builder.CreateFSub(L, R, "subtmp");
	case '*':
		return Builder.CreateFMul(L, R, "multmp");
	case '/':
		return Builder.CreateFDiv(L, R, "divtmp");
	case '%':
		return Builder.CreateFRem(L, R, "remtmp");
	case '<':
		L = Builder.CreateFCmpULT(L, R, "cmptmp");
		// Convert bool 0/1 to double 0.0 or 1.0
		return Builder.CreateUIToFP(L, Type::getDoubleTy(TheContext), "booltmp");
	case '>':
		L = Builder.CreateFCmpUGT(L, R, "cmptmp");
		// Convert bool 0/1 to double 0.0 or 1.0
		return Builder.CreateUIToFP(L, Type::getDoubleTy(TheContext), "booltmp");
	case '~':
		L = Builder.CreateFCmpUEQ(L, R, "eqtmp");
		// Convert bool 0/1 to double 0.0 or 1.0
		return Builder.CreateUIToFP(L, Type::getDoubleTy(TheContext), "booltmp");
	default:
		break;
	}

	// If it wasn't a builtin binary operator, it must be a user defined one. Emit
	// a call to it.
	Function *F = getFunction(std::string("binary") + Op);
	assert(F && "binary operator not found!");
	Value *Ops[] = { L, R };
	return Builder.CreateCall(F, Ops, "binop");
}

Value *CallExprAST::codegen() {
	// Look up the name in the global module table.
	Function *CalleeF = getFunction(Callee);
	if (!CalleeF)
		return LogErrorV("Unknown function referenced");

	// If argument mismatch error.
	if (CalleeF->arg_size() != Args.size())
		return LogErrorV("Incorrect # arguments passed");

	std::vector<Value *> ArgsV;
	for (unsigned i = 0, e = Args.size(); i != e; ++i) {
		ArgsV.push_back(Args[i]->codegen());
		if (!ArgsV.back())
			return nullptr;
	}

	return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}

Value *whileExprAST::codegen() {
	Function *TheFunction = Builder.GetInsertBlock()->getParent();

	// Create an alloca for the variable in the entry block.
	AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);

	// Emit the start code first, without 'variable' in scope.
	Value *StartVal = Start->codegen();
	if (!StartVal)
		return nullptr;

	// Store the value into the alloca.
	Builder.CreateStore(StartVal, Alloca);

	// Make the new basic block for the loop header, inserting after current
	// block.
	BasicBlock *LoopBB = BasicBlock::Create(TheContext, "loop", TheFunction);

	// Insert an explicit fall through from the current block to the LoopBB.
	Builder.CreateBr(LoopBB);

	// Start insertion in LoopBB.
	Builder.SetInsertPoint(LoopBB);

	// Within the loop, the variable is defined equal to the PHI node.  If it
	// shadows an existing variable, we have to restore it, so save it now.
	//这就是括号内的局部变量的定义方式，先将原来的变量值存起来，将新的值更新入符号表
	AllocaInst *OldVal = NamedValues[VarName];
	NamedValues[VarName] = Alloca;

	// Emit the body of the loop.  This, like any other expr, can change the
	// current BB.  Note that we ignore the value computed by the body, but don't
	// allow an error.
	if (!Body->codegen())
		return nullptr;

	// Emit the step value.
	Value *StepVal = nullptr;
	if (Step) {
		StepVal = Step->codegen();
		if (!StepVal)
			return nullptr;
	}
	else {
		// If not specified, use 1.0.
		StepVal = ConstantFP::get(TheContext, APFloat(1.0));
	}

	// Compute the end condition.
	Value *EndCond = End->codegen();
	if (!EndCond)
		return nullptr;

	// Reload, increment, and restore the alloca.  This handles the case where
	// the body of the loop mutates the variable.
	Value *CurVar = Builder.CreateLoad(Alloca, VarName.c_str());
	Value *NextVar = Builder.CreateFAdd(CurVar, StepVal, "nextvar");
	Builder.CreateStore(NextVar, Alloca);

	// Convert condition to a bool by comparing equal to 0.0.
	EndCond = Builder.CreateFCmpONE(
		EndCond, ConstantFP::get(TheContext, APFloat(0.0)), "loopcond");

	// Create the "after loop" block and insert it.
	BasicBlock *AfterBB =
		BasicBlock::Create(TheContext, "afterloop", TheFunction);

	// Insert the conditional branch into the end of LoopEndBB.
	Builder.CreateCondBr(EndCond, LoopBB, AfterBB);

	// Any new code will be inserted in AfterBB.
	Builder.SetInsertPoint(AfterBB);

	// Restore the unshadowed variable.
	if (OldVal)
		NamedValues[VarName] = OldVal;
	else
		NamedValues.erase(VarName);

	// for expr always returns 0.0.
	return Constant::getNullValue(Type::getDoubleTy(TheContext));
}

Value *IfExprAST::codegen() {
	Value *CondV = Cond->codegen();
	if (!CondV)
		return nullptr;

	// Convert condition to a bool by comparing equal to 0.0.
	CondV = Builder.CreateFCmpONE(
		CondV, ConstantFP::get(TheContext, APFloat(0.0)), "ifcond");

	Function *TheFunction = Builder.GetInsertBlock()->getParent();

	// Create blocks for the then and else cases.  Insert the 'then' block at the
	// end of the function.
	BasicBlock *ThenBB = BasicBlock::Create(TheContext, "then", TheFunction);
	BasicBlock *ElseBB = BasicBlock::Create(TheContext, "else");
	BasicBlock *MergeBB = BasicBlock::Create(TheContext, "ifcont");

	Builder.CreateCondBr(CondV, ThenBB, ElseBB);

	// Emit then value.
	Builder.SetInsertPoint(ThenBB);

	Value *ThenV = Then->codegen();
	if (!ThenV)
		return nullptr;

	Builder.CreateBr(MergeBB);
	// Codegen of 'Then' can change the current block, update ThenBB for the PHI.
	ThenBB = Builder.GetInsertBlock();

	// Emit else block.
	TheFunction->getBasicBlockList().push_back(ElseBB);
	Builder.SetInsertPoint(ElseBB);

	Value *ElseV = Else->codegen();
	if (!ElseV)
		return nullptr;

	Builder.CreateBr(MergeBB);
	// Codegen of 'Else' can change the current block, update ElseBB for the PHI.
	ElseBB = Builder.GetInsertBlock();

	// Emit merge block.
	TheFunction->getBasicBlockList().push_back(MergeBB);
	Builder.SetInsertPoint(MergeBB);
	PHINode *PN = Builder.CreatePHI(Type::getDoubleTy(TheContext), 2, "iftmp");

	PN->addIncoming(ThenV, ThenBB);
	PN->addIncoming(ElseV, ElseBB);
	return PN;
}

static void InitializeModule();

Value *LetExprAST::codegen() {
	std::vector<AllocaInst *> OldBindings;

	Function *TheFunction = Builder.GetInsertBlock()->getParent();

	// Register all variables and emit their initializer.
	// 给每一个参数分配堆栈
	for (unsigned i = 0, e = LetNames.size(); i != e; ++i) {
		const std::string &LetName = LetNames[i].first;
		ExprAST *Init = LetNames[i].second.get();

		// Emit the initializer before adding the variable to scope, this prevents
		// the initializer from referencing the variable itself, and permits stuff
		// like this:
		//  let a = 1 in
		//    let a = a in ...   # refers to outer 'a'.
		Value *InitVal;
		if (Init) {
			InitVal = Init->codegen();
			if (!InitVal)
				return nullptr;
		}
		else { // If not specified, use 0.0.
			InitVal = ConstantFP::get(TheContext, APFloat(0.0));
		}
		// 对应每一个参数的名字分配堆栈空间
		AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, LetName);
		Builder.CreateStore(InitVal, Alloca);

		// Remember the old variable binding so that we can restore the binding when
		// we unrecurse.
		OldBindings.push_back(NamedValues[LetName]);

		// Remember this binding.下次引用的时候就可以直接查表得到堆栈地址
		NamedValues[LetName] = Alloca;
	}

	// Codegen the body, now that all lets are in scope.
	Value *BodyVal = Body->codegen();
	if (!BodyVal)
		return nullptr;

	// Pop all our variables from scope.
	for (unsigned i = 0, e = LetNames.size(); i != e; ++i)
		NamedValues[LetNames[i].first] = OldBindings[i];

	// Return the body computation.
	return BodyVal;
}

Function *PrototypeAST::codegen() {
	// Make the function type:  double(double,double) etc.
	std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(TheContext));
	FunctionType *FT =
		FunctionType::get(Type::getDoubleTy(TheContext), Doubles, false);

	Function *F =
		Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());
	// Set names for all arguments.
	unsigned Idx = 0;
	for (auto &Arg : F->args())
		Arg.setName(Args[Idx++]);

	return F;
}

Function *FunctionAST::codegen() {
	// Transfer ownership of the prototype to the FunctionProtos map, but keep a
	// reference to it for use below.
	auto &P = *Proto;
	FunctionProtos[Proto->getName()] = std::move(Proto);
	Function *TheFunction = getFunction(P.getName());
	if (!TheFunction)
		return nullptr;

	// If this is an operator, install it.
	if (P.isBinaryOp())
		BinopPrecedence[P.getOperatorName()] = P.getBinaryPrecedence();

	// Create a new basic block to start insertion into.
	BasicBlock *BB = BasicBlock::Create(TheContext, "entry", TheFunction);
	Builder.SetInsertPoint(BB);

	// Record the function arguments in the NamedValues map.
	NamedValues.clear();
	for (auto &Arg : TheFunction->args()) {
		// Create an alloca for this variable.
		AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Arg.getName());

		// Store the initial value into the alloca.
		Builder.CreateStore(&Arg, Alloca);

		// Add arguments to variable symbol table.
		NamedValues[Arg.getName()] = Alloca;
	}

	if (Value *RetVal = Body->codegen()) {
		// Finish off the function.
		Builder.CreateRet(RetVal);

		// Validate the generated code, checking for consistency.
		verifyFunction(*TheFunction);

		return TheFunction;
	}

	// Error reading body, remove function.
	TheFunction->eraseFromParent();

	if (P.isBinaryOp())
		BinopPrecedence.erase(P.getOperatorName());
	return nullptr;
}

GlobalVariable *GVAST::codegen() {

	GlobalVariable *global_val = new GlobalVariable(
		*TheModule, Type::getDoubleTy(TheContext), false,
		GlobalValue::ExternalLinkage,
		ConstantFP::get(Builder.getDoubleTy(), numVal), GVname);
	Builder.CreateStore(ConstantFP::get(TheContext, APFloat(numVal)), global_val);
	global_val->print(errs());
	GlobalValues[GVname] = global_val;
	return nullptr;
}

//===----------------------------------------------------------------------===//
// Top-Level parsing and JIT Driver
//===----------------------------------------------------------------------===//

static void InitializeModule() {
	// Open a new module.
	TheModule = llvm::make_unique<Module>("my cool jit", TheContext);
	TheModule->setDataLayout(TheJIT->getTargetMachine().createDataLayout());
}

static void HandleDefinition() {

	//改逻辑：如果不存在嵌套函数，则按照正常流程进行；如果有，则先处理了嵌套函数（理论上支持无限多层嵌套）
	if (auto FnAST = ParseDefinition()) {
		if (FnAST->Body->type == 12) {
			//如果是fun类型的let，我们就把他移出去先处理
			auto FunAST = FnAST->Body->getFun();
			if (auto *FnIR = FunAST->codegen()) {
				fprintf(stderr, "Read InsideFunction definition:");
				FnIR->print(errs());
				fprintf(stderr, "\n");
				TheJIT->addModule(std::move(TheModule));
				InitializeModule();
			}
		}
		//不管是不是嵌套函数，接下来都轮到主函数的codegen了
		if (auto *FnIR = FnAST->codegen()) {
			fprintf(stderr, "Read function definition:");
			FnIR->print(errs());
			fprintf(stderr, "\n");
			TheJIT->addModule(std::move(TheModule));
			InitializeModule();
		}
	}
	else {
		// Skip token for error recovery.
		getNextToken();
	}
}

static void HandleTopLevelExpression() {
	// Evaluate a top-level expression into an anonymous function.
	if (auto FnAST = ParseTopLevelExpr()) {
		if (FnAST->codegen()) {
			// JIT the module containing the anonymous expression, keeping a handle so
			// we can free it later.
			auto H = TheJIT->addModule(std::move(TheModule));
			InitializeModule();

			// Search the JIT for the __anon_expr symbol.
			auto ExprSymbol = TheJIT->findSymbol("__anon_expr");
			assert(ExprSymbol && "Function not found");

			// Get the symbol's address and cast it to the right type (takes no
			// arguments, returns a double) so we can call it as a native function.
			double(*FP)() =
				(double(*)())(intptr_t)cantFail(ExprSymbol.getAddress());
			fprintf(stderr, "Evaluated to %f\n", FP());

			// Delete the anonymous expression module from the JIT.
			TheJIT->removeModule(H);
		}
	}
	else {
		// Skip token for error recovery.
		getNextToken();
	}
}

static void HandleGlobalVarible() {
	if (auto globalvalAST = ParseGlobalVarible()) {
		auto GVIR = globalvalAST->codegen();
		fprintf(stderr, "Read global val definition:");
		fprintf(stderr, "\n");
		TheJIT->addModule(std::move(TheModule));
		InitializeModule();
	}
	else {
		// Skip token for error recovery.
		getNextToken();
	}
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
	while (true) {
		while (DadyLetsDrawTree == false) {
			fprintf(stderr, "ready> ");
			switch (CurTok) {
			case tok_eof:
				return;
			case tok_semi: // ignore top-level semicolons.
				getNextToken();
				break;
			case tok_def:
				HandleDefinition();
				break;
				/*case tok_extern:
				  HandleExtern();
				  break;*/
			case tok_val:
				HandleGlobalVarible();
				break;
			case tok_change:
				getNextToken();
				DadyLetsDrawTree = !DadyLetsDrawTree;
				if (DadyLetsDrawTree) {
					std::cout << "change to draw tree mode\n";
				}
				else {
					std::cout << "change to normal mode\n";
				}
				break;
			default:
				HandleTopLevelExpression();
				break;
			}
		}
		while (DadyLetsDrawTree == true) {
			fprintf(stderr, "ready> ");
			switch (CurTok) {
			case tok_eof:
				return;
			case tok_semi: // ignore top-level semicolons.
				getNextToken();
				break;
			case tok_def: { // int i = 0;
				auto Fn = ParseDefinition();
				Fn->printTree(0);
				break;
			}
			case tok_change:
				getNextToken();
				DadyLetsDrawTree = !DadyLetsDrawTree;
				if (DadyLetsDrawTree) {
					std::cout << "change to draw tree mode\n";
				}
				else {
					std::cout << "change to normal mode\n";
				}
				break;
			default: {
				auto FnAST = ParseTopLevelExpr();
				FnAST->printTree(0);
				break;
			}
			}
		}
	}
}

//===----------------------------------------------------------------------===//
// "Library" functions that can be "extern'd" from user code.
//===----------------------------------------------------------------------===//

/// putchard - putchar that takes a double and returns 0.
extern "C" double putchard(double X) {
	fputc((char)X, stderr);
	return 0.0;
}

/// printd - printf that takes a double prints it as "%f\n", returning 0.
// 打印一个数字，返回值为0
extern "C" double printd(double X) {
	fprintf(stderr, "%f\n", X);
	return 0;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

void drawTree() { DadyLetsDrawTree = true; }

int main() {
	InitializeNativeTarget();
	InitializeNativeTargetAsmPrinter();
	InitializeNativeTargetAsmParser();

	// Install standard binary operators.
	// 1 is lowest precedence.
	BinopPrecedence['='] = 2;
	BinopPrecedence['<'] = 10;
	BinopPrecedence['>'] = 10;
	BinopPrecedence['+'] = 20;
	BinopPrecedence['-'] = 20;
	BinopPrecedence['%'] = 40; // highest.
	BinopPrecedence['*'] = 40; // highest.
	BinopPrecedence['/'] = 40; // highest.

	// Prime the first token.
	fprintf(stderr, "ready> ");
	getNextToken();

	TheJIT = llvm::make_unique<KaleidoscopeJIT>();

	InitializeModule();

	// Run the main "interpreter loop" now.

	// drawTree();
	MainLoop();

	return 0;
}

//目前已实现功能：

//更新日志：
// 11.24以前更新：
//     if elseend、函数定义调用、表达式的计算（已有优先级机制）by:whuStone(石亮禾)
//     let...in...、局部变量定义    by:周佬（周浩宇）
// 11.24下午更新：实现了let in 语句中的多条语句      by:whuStone (石亮禾)
// 11.25下午更新：实现了函数的嵌套定义（let后面定义函数，理论上支持任意多层嵌套）by:whuStone(石亮禾) 
// 11.25晚上更新：实现了while循环    by:whuStone (石亮禾)
// 11.26下午更新：实现了print功能    by:whuStone (石亮禾)
// 11.26下午更新：改进了prototype的语法分析，使括号变得可选     by:TT (宛铠涛)
// 11.26晚上更新：新增了  /  %  >  运算符     by:whuStone (石亮禾)
// 11.26晚上更新：新增了函数的“重载”功能，即 '|'。     by:together
// 11.27上午更新：新增了AST树的展示功能（画在命令行上）。    by:whuStone(石亮禾)
// 11.27晚上更新：新增了全局变量的词法语法，但是IR未生成。   by:whuStone(石亮禾)
// 11.28上午更新：完成了全局变量的IR代码生成。已实现全局变量的功能。by:whuStone(石亮禾)
// 11.28晚上更新：对一些bug进行了修复，并增加了模式切换功能  by:whuStone(石亮禾)


//测试实例：
// let fun if while val | 的功能：
// fun s(0) = 1|s(e) = let val d = 8 in if e<3 then while d> 1 do(e = e + d; d = d - 1;) else e = e + 1 e end; 
// fun p(e) = let val c = 0 in while e > 0 do (c =  e+c;e=e-1) c; end;
// fun f(r) = while r > 0 do(s = s+r;r =r-1;);