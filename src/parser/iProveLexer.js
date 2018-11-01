// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\u0017\u0085\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0004\u0013\t\u0013",
    "\u0004\u0014\t\u0014\u0004\u0015\t\u0015\u0004\u0016\t\u0016\u0003\u0002",
    "\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0007\u0003\u0007",
    "\u0003\u0007\u0003\b\u0003\b\u0003\b\u0003\b\u0003\b\u0003\b\u0003\b",
    "\u0003\b\u0003\t\u0003\t\u0003\t\u0003\n\u0003\n\u0003\n\u0003\n\u0003",
    "\u000b\u0003\u000b\u0003\u000b\u0003\u000b\u0003\u000b\u0003\f\u0003",
    "\f\u0003\f\u0003\f\u0003\f\u0003\f\u0003\r\u0003\r\u0003\u000e\u0003",
    "\u000e\u0003\u000f\u0003\u000f\u0003\u0010\u0003\u0010\u0003\u0011\u0003",
    "\u0011\u0003\u0012\u0003\u0012\u0003\u0013\u0003\u0013\u0006\u0013v",
    "\n\u0013\r\u0013\u000e\u0013w\u0003\u0014\u0003\u0014\u0006\u0014|\n",
    "\u0014\r\u0014\u000e\u0014}\u0003\u0015\u0003\u0015\u0003\u0016\u0003",
    "\u0016\u0003\u0016\u0003\u0016\u0002\u0002\u0017\u0003\u0003\u0005\u0004",
    "\u0007\u0005\t\u0006\u000b\u0007\r\b\u000f\t\u0011\n\u0013\u000b\u0015",
    "\f\u0017\r\u0019\u000e\u001b\u000f\u001d\u0010\u001f\u0011!\u0012#\u0013",
    "%\u0014\'\u0015)\u0016+\u0017\u0003\u0002\u0007\u0003\u0002C\\\u0003",
    "\u0002c|\u0004\u0002C\\c|\u0005\u0002C\\aac|\u0005\u0002\u000b\f\u000f",
    "\u000f\"\"\u0002\u0086\u0002\u0003\u0003\u0002\u0002\u0002\u0002\u0005",
    "\u0003\u0002\u0002\u0002\u0002\u0007\u0003\u0002\u0002\u0002\u0002\t",
    "\u0003\u0002\u0002\u0002\u0002\u000b\u0003\u0002\u0002\u0002\u0002\r",
    "\u0003\u0002\u0002\u0002\u0002\u000f\u0003\u0002\u0002\u0002\u0002\u0011",
    "\u0003\u0002\u0002\u0002\u0002\u0013\u0003\u0002\u0002\u0002\u0002\u0015",
    "\u0003\u0002\u0002\u0002\u0002\u0017\u0003\u0002\u0002\u0002\u0002\u0019",
    "\u0003\u0002\u0002\u0002\u0002\u001b\u0003\u0002\u0002\u0002\u0002\u001d",
    "\u0003\u0002\u0002\u0002\u0002\u001f\u0003\u0002\u0002\u0002\u0002!",
    "\u0003\u0002\u0002\u0002\u0002#\u0003\u0002\u0002\u0002\u0002%\u0003",
    "\u0002\u0002\u0002\u0002\'\u0003\u0002\u0002\u0002\u0002)\u0003\u0002",
    "\u0002\u0002\u0002+\u0003\u0002\u0002\u0002\u0003-\u0003\u0002\u0002",
    "\u0002\u00054\u0003\u0002\u0002\u0002\u0007;\u0003\u0002\u0002\u0002",
    "\tB\u0003\u0002\u0002\u0002\u000bF\u0003\u0002\u0002\u0002\rJ\u0003",
    "\u0002\u0002\u0002\u000fM\u0003\u0002\u0002\u0002\u0011U\u0003\u0002",
    "\u0002\u0002\u0013X\u0003\u0002\u0002\u0002\u0015\\\u0003\u0002\u0002",
    "\u0002\u0017a\u0003\u0002\u0002\u0002\u0019g\u0003\u0002\u0002\u0002",
    "\u001bi\u0003\u0002\u0002\u0002\u001dk\u0003\u0002\u0002\u0002\u001f",
    "m\u0003\u0002\u0002\u0002!o\u0003\u0002\u0002\u0002#q\u0003\u0002\u0002",
    "\u0002%s\u0003\u0002\u0002\u0002\'y\u0003\u0002\u0002\u0002)\u007f\u0003",
    "\u0002\u0002\u0002+\u0081\u0003\u0002\u0002\u0002-.\u0007c\u0002\u0002",
    "./\u0007u\u0002\u0002/0\u0007u\u0002\u000201\u0007w\u0002\u000212\u0007",
    "o\u0002\u000223\u0007g\u0002\u00023\u0004\u0003\u0002\u0002\u000245",
    "\u0007h\u0002\u000256\u0007q\u0002\u000267\u0007t\u0002\u000278\u0007",
    "c\u0002\u000289\u0007n\u0002\u00029:\u0007n\u0002\u0002:\u0006\u0003",
    "\u0002\u0002\u0002;<\u0007g\u0002\u0002<=\u0007z\u0002\u0002=>\u0007",
    "k\u0002\u0002>?\u0007u\u0002\u0002?@\u0007v\u0002\u0002@A\u0007u\u0002",
    "\u0002A\b\u0003\u0002\u0002\u0002BC\u0007p\u0002\u0002CD\u0007q\u0002",
    "\u0002DE\u0007v\u0002\u0002E\n\u0003\u0002\u0002\u0002FG\u0007c\u0002",
    "\u0002GH\u0007p\u0002\u0002HI\u0007f\u0002\u0002I\f\u0003\u0002\u0002",
    "\u0002JK\u0007q\u0002\u0002KL\u0007t\u0002\u0002L\u000e\u0003\u0002",
    "\u0002\u0002MN\u0007k\u0002\u0002NO\u0007o\u0002\u0002OP\u0007r\u0002",
    "\u0002PQ\u0007n\u0002\u0002QR\u0007k\u0002\u0002RS\u0007g\u0002\u0002",
    "ST\u0007u\u0002\u0002T\u0010\u0003\u0002\u0002\u0002UV\u0007?\u0002",
    "\u0002VW\u0007@\u0002\u0002W\u0012\u0003\u0002\u0002\u0002XY\u0007k",
    "\u0002\u0002YZ\u0007h\u0002\u0002Z[\u0007h\u0002\u0002[\u0014\u0003",
    "\u0002\u0002\u0002\\]\u0007v\u0002\u0002]^\u0007t\u0002\u0002^_\u0007",
    "w\u0002\u0002_`\u0007g\u0002\u0002`\u0016\u0003\u0002\u0002\u0002ab",
    "\u0007h\u0002\u0002bc\u0007c\u0002\u0002cd\u0007n\u0002\u0002de\u0007",
    "u\u0002\u0002ef\u0007g\u0002\u0002f\u0018\u0003\u0002\u0002\u0002gh",
    "\u0007*\u0002\u0002h\u001a\u0003\u0002\u0002\u0002ij\u0007+\u0002\u0002",
    "j\u001c\u0003\u0002\u0002\u0002kl\u0007]\u0002\u0002l\u001e\u0003\u0002",
    "\u0002\u0002mn\u0007_\u0002\u0002n \u0003\u0002\u0002\u0002op\t\u0002",
    "\u0002\u0002p\"\u0003\u0002\u0002\u0002qr\t\u0003\u0002\u0002r$\u0003",
    "\u0002\u0002\u0002su\t\u0002\u0002\u0002tv\t\u0004\u0002\u0002ut\u0003",
    "\u0002\u0002\u0002vw\u0003\u0002\u0002\u0002wu\u0003\u0002\u0002\u0002",
    "wx\u0003\u0002\u0002\u0002x&\u0003\u0002\u0002\u0002y{\t\u0003\u0002",
    "\u0002z|\t\u0005\u0002\u0002{z\u0003\u0002\u0002\u0002|}\u0003\u0002",
    "\u0002\u0002}{\u0003\u0002\u0002\u0002}~\u0003\u0002\u0002\u0002~(\u0003",
    "\u0002\u0002\u0002\u007f\u0080\u0007.\u0002\u0002\u0080*\u0003\u0002",
    "\u0002\u0002\u0081\u0082\t\u0006\u0002\u0002\u0082\u0083\u0003\u0002",
    "\u0002\u0002\u0083\u0084\b\u0016\u0002\u0002\u0084,\u0003\u0002\u0002",
    "\u0002\u0005\u0002w}\u0003\b\u0002\u0002"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

function iProveLexer(input) {
	antlr4.Lexer.call(this, input);
    this._interp = new antlr4.atn.LexerATNSimulator(this, atn, decisionsToDFA, new antlr4.PredictionContextCache());
    return this;
}

iProveLexer.prototype = Object.create(antlr4.Lexer.prototype);
iProveLexer.prototype.constructor = iProveLexer;

Object.defineProperty(iProveLexer.prototype, "atn", {
        get : function() {
                return atn;
        }
});

iProveLexer.EOF = antlr4.Token.EOF;
iProveLexer.ASSUME = 1;
iProveLexer.FORALL = 2;
iProveLexer.EXISTS = 3;
iProveLexer.NOT = 4;
iProveLexer.AND = 5;
iProveLexer.OR = 6;
iProveLexer.IMPLIES = 7;
iProveLexer.IMPLIES2 = 8;
iProveLexer.IFF = 9;
iProveLexer.TRUE = 10;
iProveLexer.FALSE = 11;
iProveLexer.BRACKET_OPEN = 12;
iProveLexer.BRACKET_CLOSE = 13;
iProveLexer.SQ_BRACKET_OPEN = 14;
iProveLexer.SQ_BRACKET_CLOSE = 15;
iProveLexer.LITERAL = 16;
iProveLexer.VARIABLE = 17;
iProveLexer.CONSTANT = 18;
iProveLexer.NAME = 19;
iProveLexer.COMMA = 20;
iProveLexer.WS = 21;

iProveLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

iProveLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

iProveLexer.prototype.literalNames = [ null, "'assume'", "'forall'", "'exists'", 
                                       "'not'", "'and'", "'or'", "'implies'", 
                                       "'=>'", "'iff'", "'true'", "'false'", 
                                       "'('", "')'", "'['", "']'", null, 
                                       null, null, null, "','" ];

iProveLexer.prototype.symbolicNames = [ null, "ASSUME", "FORALL", "EXISTS", 
                                        "NOT", "AND", "OR", "IMPLIES", "IMPLIES2", 
                                        "IFF", "TRUE", "FALSE", "BRACKET_OPEN", 
                                        "BRACKET_CLOSE", "SQ_BRACKET_OPEN", 
                                        "SQ_BRACKET_CLOSE", "LITERAL", "VARIABLE", 
                                        "CONSTANT", "NAME", "COMMA", "WS" ];

iProveLexer.prototype.ruleNames = [ "ASSUME", "FORALL", "EXISTS", "NOT", 
                                    "AND", "OR", "IMPLIES", "IMPLIES2", 
                                    "IFF", "TRUE", "FALSE", "BRACKET_OPEN", 
                                    "BRACKET_CLOSE", "SQ_BRACKET_OPEN", 
                                    "SQ_BRACKET_CLOSE", "LITERAL", "VARIABLE", 
                                    "CONSTANT", "NAME", "COMMA", "WS" ];

iProveLexer.prototype.grammarFileName = "iProve.g4";



exports.iProveLexer = iProveLexer;

