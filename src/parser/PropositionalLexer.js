// Generated from src/parser/Propositional.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\u0013o\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0003\u0002\u0003\u0002",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0004\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0006",
    "\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006",
    "\u0003\u0006\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\b",
    "\u0003\b\u0003\b\u0003\b\u0003\b\u0003\t\u0003\t\u0003\t\u0003\t\u0003",
    "\t\u0003\t\u0003\n\u0003\n\u0003\u000b\u0003\u000b\u0003\f\u0003\f\u0003",
    "\r\u0003\r\u0006\rR\n\r\r\r\u000e\rS\u0003\u000e\u0003\u000e\u0006\u000e",
    "X\n\u000e\r\u000e\u000e\u000eY\u0003\u000f\u0003\u000f\u0003\u000f\u0003",
    "\u000f\u0003\u000f\u0003\u000f\u0003\u000f\u0003\u0010\u0003\u0010\u0003",
    "\u0010\u0003\u0010\u0003\u0010\u0003\u0010\u0003\u0010\u0003\u0011\u0003",
    "\u0011\u0003\u0012\u0003\u0012\u0003\u0012\u0003\u0012\u0002\u0002\u0013",
    "\u0003\u0003\u0005\u0004\u0007\u0005\t\u0006\u000b\u0007\r\b\u000f\t",
    "\u0011\n\u0013\u000b\u0015\f\u0017\r\u0019\u000e\u001b\u000f\u001d\u0010",
    "\u001f\u0011!\u0012#\u0013\u0003\u0002\u0006\u0003\u0002C\\\u0003\u0002",
    "c|\u0005\u0002C\\aac|\u0005\u0002\u000b\f\u000f\u000f\"\"\u0002p\u0002",
    "\u0003\u0003\u0002\u0002\u0002\u0002\u0005\u0003\u0002\u0002\u0002\u0002",
    "\u0007\u0003\u0002\u0002\u0002\u0002\t\u0003\u0002\u0002\u0002\u0002",
    "\u000b\u0003\u0002\u0002\u0002\u0002\r\u0003\u0002\u0002\u0002\u0002",
    "\u000f\u0003\u0002\u0002\u0002\u0002\u0011\u0003\u0002\u0002\u0002\u0002",
    "\u0013\u0003\u0002\u0002\u0002\u0002\u0015\u0003\u0002\u0002\u0002\u0002",
    "\u0017\u0003\u0002\u0002\u0002\u0002\u0019\u0003\u0002\u0002\u0002\u0002",
    "\u001b\u0003\u0002\u0002\u0002\u0002\u001d\u0003\u0002\u0002\u0002\u0002",
    "\u001f\u0003\u0002\u0002\u0002\u0002!\u0003\u0002\u0002\u0002\u0002",
    "#\u0003\u0002\u0002\u0002\u0003%\u0003\u0002\u0002\u0002\u0005\'\u0003",
    "\u0002\u0002\u0002\u0007+\u0003\u0002\u0002\u0002\t/\u0003\u0002\u0002",
    "\u0002\u000b2\u0003\u0002\u0002\u0002\r:\u0003\u0002\u0002\u0002\u000f",
    ">\u0003\u0002\u0002\u0002\u0011C\u0003\u0002\u0002\u0002\u0013I\u0003",
    "\u0002\u0002\u0002\u0015K\u0003\u0002\u0002\u0002\u0017M\u0003\u0002",
    "\u0002\u0002\u0019O\u0003\u0002\u0002\u0002\u001bU\u0003\u0002\u0002",
    "\u0002\u001d[\u0003\u0002\u0002\u0002\u001fb\u0003\u0002\u0002\u0002",
    "!i\u0003\u0002\u0002\u0002#k\u0003\u0002\u0002\u0002%&\t\u0002\u0002",
    "\u0002&\u0004\u0003\u0002\u0002\u0002\'(\u0007p\u0002\u0002()\u0007",
    "q\u0002\u0002)*\u0007v\u0002\u0002*\u0006\u0003\u0002\u0002\u0002+,",
    "\u0007c\u0002\u0002,-\u0007p\u0002\u0002-.\u0007f\u0002\u0002.\b\u0003",
    "\u0002\u0002\u0002/0\u0007q\u0002\u000201\u0007t\u0002\u00021\n\u0003",
    "\u0002\u0002\u000223\u0007k\u0002\u000234\u0007o\u0002\u000245\u0007",
    "r\u0002\u000256\u0007n\u0002\u000267\u0007k\u0002\u000278\u0007g\u0002",
    "\u000289\u0007u\u0002\u00029\f\u0003\u0002\u0002\u0002:;\u0007k\u0002",
    "\u0002;<\u0007h\u0002\u0002<=\u0007h\u0002\u0002=\u000e\u0003\u0002",
    "\u0002\u0002>?\u0007v\u0002\u0002?@\u0007t\u0002\u0002@A\u0007w\u0002",
    "\u0002AB\u0007g\u0002\u0002B\u0010\u0003\u0002\u0002\u0002CD\u0007h",
    "\u0002\u0002DE\u0007c\u0002\u0002EF\u0007n\u0002\u0002FG\u0007u\u0002",
    "\u0002GH\u0007g\u0002\u0002H\u0012\u0003\u0002\u0002\u0002IJ\u0007*",
    "\u0002\u0002J\u0014\u0003\u0002\u0002\u0002KL\u0007+\u0002\u0002L\u0016",
    "\u0003\u0002\u0002\u0002MN\t\u0003\u0002\u0002N\u0018\u0003\u0002\u0002",
    "\u0002OQ\t\u0002\u0002\u0002PR\t\u0003\u0002\u0002QP\u0003\u0002\u0002",
    "\u0002RS\u0003\u0002\u0002\u0002SQ\u0003\u0002\u0002\u0002ST\u0003\u0002",
    "\u0002\u0002T\u001a\u0003\u0002\u0002\u0002UW\t\u0003\u0002\u0002VX",
    "\t\u0004\u0002\u0002WV\u0003\u0002\u0002\u0002XY\u0003\u0002\u0002\u0002",
    "YW\u0003\u0002\u0002\u0002YZ\u0003\u0002\u0002\u0002Z\u001c\u0003\u0002",
    "\u0002\u0002[\\\u0007h\u0002\u0002\\]\u0007q\u0002\u0002]^\u0007t\u0002",
    "\u0002^_\u0007c\u0002\u0002_`\u0007n\u0002\u0002`a\u0007n\u0002\u0002",
    "a\u001e\u0003\u0002\u0002\u0002bc\u0007g\u0002\u0002cd\u0007z\u0002",
    "\u0002de\u0007k\u0002\u0002ef\u0007u\u0002\u0002fg\u0007v\u0002\u0002",
    "gh\u0007u\u0002\u0002h \u0003\u0002\u0002\u0002ij\u0007.\u0002\u0002",
    "j\"\u0003\u0002\u0002\u0002kl\t\u0005\u0002\u0002lm\u0003\u0002\u0002",
    "\u0002mn\b\u0012\u0002\u0002n$\u0003\u0002\u0002\u0002\u0005\u0002S",
    "Y\u0003\b\u0002\u0002"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

function PropositionalLexer(input) {
	antlr4.Lexer.call(this, input);
    this._interp = new antlr4.atn.LexerATNSimulator(this, atn, decisionsToDFA, new antlr4.PredictionContextCache());
    return this;
}

PropositionalLexer.prototype = Object.create(antlr4.Lexer.prototype);
PropositionalLexer.prototype.constructor = PropositionalLexer;

Object.defineProperty(PropositionalLexer.prototype, "atn", {
        get : function() {
                return atn;
        }
});

PropositionalLexer.EOF = antlr4.Token.EOF;
PropositionalLexer.LITERAL = 1;
PropositionalLexer.NOT = 2;
PropositionalLexer.AND = 3;
PropositionalLexer.OR = 4;
PropositionalLexer.IMPLIES = 5;
PropositionalLexer.IFF = 6;
PropositionalLexer.TRUE = 7;
PropositionalLexer.FALSE = 8;
PropositionalLexer.BRACKET_OPEN = 9;
PropositionalLexer.BRACKET_CLOSE = 10;
PropositionalLexer.VARIABLE = 11;
PropositionalLexer.CONSTANT = 12;
PropositionalLexer.NAME = 13;
PropositionalLexer.FORALL = 14;
PropositionalLexer.EXISTS = 15;
PropositionalLexer.COMMA = 16;
PropositionalLexer.WS = 17;

PropositionalLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

PropositionalLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

PropositionalLexer.prototype.literalNames = [ null, null, "'not'", "'and'", 
                                              "'or'", "'implies'", "'iff'", 
                                              "'true'", "'false'", "'('", 
                                              "')'", null, null, null, "'forall'", 
                                              "'exists'", "','" ];

PropositionalLexer.prototype.symbolicNames = [ null, "LITERAL", "NOT", "AND", 
                                               "OR", "IMPLIES", "IFF", "TRUE", 
                                               "FALSE", "BRACKET_OPEN", 
                                               "BRACKET_CLOSE", "VARIABLE", 
                                               "CONSTANT", "NAME", "FORALL", 
                                               "EXISTS", "COMMA", "WS" ];

PropositionalLexer.prototype.ruleNames = [ "LITERAL", "NOT", "AND", "OR", 
                                           "IMPLIES", "IFF", "TRUE", "FALSE", 
                                           "BRACKET_OPEN", "BRACKET_CLOSE", 
                                           "VARIABLE", "CONSTANT", "NAME", 
                                           "FORALL", "EXISTS", "COMMA", 
                                           "WS" ];

PropositionalLexer.prototype.grammarFileName = "Propositional.g4";



exports.PropositionalLexer = PropositionalLexer;

