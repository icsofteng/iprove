// Generated from src/parser/Propositional.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');

// This class defines a complete listener for a parse tree produced by PropositionalParser.
function PropositionalListener() {
	antlr4.tree.ParseTreeListener.call(this);
	return this;
}

PropositionalListener.prototype = Object.create(antlr4.tree.ParseTreeListener.prototype);
PropositionalListener.prototype.constructor = PropositionalListener;

// Enter a parse tree produced by PropositionalParser#statement.
PropositionalListener.prototype.enterStatement = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#statement.
PropositionalListener.prototype.exitStatement = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#paramVar.
PropositionalListener.prototype.enterParamVar = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#paramVar.
PropositionalListener.prototype.exitParamVar = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#paramConst.
PropositionalListener.prototype.enterParamConst = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#paramConst.
PropositionalListener.prototype.exitParamConst = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#relationExp.
PropositionalListener.prototype.enterRelationExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#relationExp.
PropositionalListener.prototype.exitRelationExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#existsExp.
PropositionalListener.prototype.enterExistsExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#existsExp.
PropositionalListener.prototype.exitExistsExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#literalExp.
PropositionalListener.prototype.enterLiteralExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#literalExp.
PropositionalListener.prototype.exitLiteralExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#forallExp.
PropositionalListener.prototype.enterForallExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#forallExp.
PropositionalListener.prototype.exitForallExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#trueExp.
PropositionalListener.prototype.enterTrueExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#trueExp.
PropositionalListener.prototype.exitTrueExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#andExp.
PropositionalListener.prototype.enterAndExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#andExp.
PropositionalListener.prototype.exitAndExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#parenthesesExp.
PropositionalListener.prototype.enterParenthesesExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#parenthesesExp.
PropositionalListener.prototype.exitParenthesesExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#falseExp.
PropositionalListener.prototype.enterFalseExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#falseExp.
PropositionalListener.prototype.exitFalseExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#orExp.
PropositionalListener.prototype.enterOrExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#orExp.
PropositionalListener.prototype.exitOrExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#notExp.
PropositionalListener.prototype.enterNotExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#notExp.
PropositionalListener.prototype.exitNotExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#iffExp.
PropositionalListener.prototype.enterIffExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#iffExp.
PropositionalListener.prototype.exitIffExp = function(ctx) {
};


// Enter a parse tree produced by PropositionalParser#impliesExp.
PropositionalListener.prototype.enterImpliesExp = function(ctx) {
};

// Exit a parse tree produced by PropositionalParser#impliesExp.
PropositionalListener.prototype.exitImpliesExp = function(ctx) {
};



exports.PropositionalListener = PropositionalListener;