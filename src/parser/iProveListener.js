// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');

// This class defines a complete listener for a parse tree produced by iProveParser.
function iProveListener() {
	antlr4.tree.ParseTreeListener.call(this);
	return this;
}

iProveListener.prototype = Object.create(antlr4.tree.ParseTreeListener.prototype);
iProveListener.prototype.constructor = iProveListener;

// Enter a parse tree produced by iProveParser#statement.
iProveListener.prototype.enterStatement = function(ctx) {
};

// Exit a parse tree produced by iProveParser#statement.
iProveListener.prototype.exitStatement = function(ctx) {
};


// Enter a parse tree produced by iProveParser#paramVar.
iProveListener.prototype.enterParamVar = function(ctx) {
};

// Exit a parse tree produced by iProveParser#paramVar.
iProveListener.prototype.exitParamVar = function(ctx) {
};


// Enter a parse tree produced by iProveParser#paramConst.
iProveListener.prototype.enterParamConst = function(ctx) {
};

// Exit a parse tree produced by iProveParser#paramConst.
iProveListener.prototype.exitParamConst = function(ctx) {
};


// Enter a parse tree produced by iProveParser#andExp.
iProveListener.prototype.enterAndExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#andExp.
iProveListener.prototype.exitAndExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#parenthesesExp.
iProveListener.prototype.enterParenthesesExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#parenthesesExp.
iProveListener.prototype.exitParenthesesExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#assumeExp.
iProveListener.prototype.enterAssumeExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#assumeExp.
iProveListener.prototype.exitAssumeExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#orExp.
iProveListener.prototype.enterOrExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#orExp.
iProveListener.prototype.exitOrExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#sqParenthesesExp.
iProveListener.prototype.enterSqParenthesesExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#sqParenthesesExp.
iProveListener.prototype.exitSqParenthesesExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#notExp.
iProveListener.prototype.enterNotExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#notExp.
iProveListener.prototype.exitNotExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#iffExp.
iProveListener.prototype.enterIffExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#iffExp.
iProveListener.prototype.exitIffExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#relationExp.
iProveListener.prototype.enterRelationExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#relationExp.
iProveListener.prototype.exitRelationExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#existsExp.
iProveListener.prototype.enterExistsExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#existsExp.
iProveListener.prototype.exitExistsExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#literalExp.
iProveListener.prototype.enterLiteralExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#literalExp.
iProveListener.prototype.exitLiteralExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#forallExp.
iProveListener.prototype.enterForallExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#forallExp.
iProveListener.prototype.exitForallExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#trueExp.
iProveListener.prototype.enterTrueExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#trueExp.
iProveListener.prototype.exitTrueExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#falseExp.
iProveListener.prototype.enterFalseExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#falseExp.
iProveListener.prototype.exitFalseExp = function(ctx) {
};


// Enter a parse tree produced by iProveParser#impliesExp.
iProveListener.prototype.enterImpliesExp = function(ctx) {
};

// Exit a parse tree produced by iProveParser#impliesExp.
iProveListener.prototype.exitImpliesExp = function(ctx) {
};



exports.iProveListener = iProveListener;