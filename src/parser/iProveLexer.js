// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\u0016|\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0004\u0013\t\u0013",
    "\u0004\u0014\t\u0014\u0004\u0015\t\u0015\u0003\u0002\u0003\u0002\u0003",
    "\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0004\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0007\u0003",
    "\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003",
    "\u0007\u0003\b\u0003\b\u0003\b\u0003\t\u0003\t\u0003\t\u0003\t\u0003",
    "\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003\u000b\u0003\u000b\u0003\u000b",
    "\u0003\u000b\u0003\u000b\u0003\u000b\u0003\f\u0003\f\u0003\r\u0003\r",
    "\u0003\u000e\u0003\u000e\u0003\u000f\u0003\u000f\u0003\u0010\u0003\u0010",
    "\u0003\u0011\u0003\u0011\u0003\u0012\u0003\u0012\u0006\u0012m\n\u0012",
    "\r\u0012\u000e\u0012n\u0003\u0013\u0003\u0013\u0006\u0013s\n\u0013\r",
    "\u0013\u000e\u0013t\u0003\u0014\u0003\u0014\u0003\u0015\u0003\u0015",
    "\u0003\u0015\u0003\u0015\u0002\u0002\u0016\u0003\u0003\u0005\u0004\u0007",
    "\u0005\t\u0006\u000b\u0007\r\b\u000f\t\u0011\n\u0013\u000b\u0015\f\u0017",
    "\r\u0019\u000e\u001b\u000f\u001d\u0010\u001f\u0011!\u0012#\u0013%\u0014",
    "\'\u0015)\u0016\u0003\u0002\u0007\u0003\u0002C\\\u0003\u0002c|\u0004",
    "\u0002C\\c|\u0005\u0002C\\aac|\u0005\u0002\u000b\f\u000f\u000f\"\"\u0002",
    "}\u0002\u0003\u0003\u0002\u0002\u0002\u0002\u0005\u0003\u0002\u0002",
    "\u0002\u0002\u0007\u0003\u0002\u0002\u0002\u0002\t\u0003\u0002\u0002",
    "\u0002\u0002\u000b\u0003\u0002\u0002\u0002\u0002\r\u0003\u0002\u0002",
    "\u0002\u0002\u000f\u0003\u0002\u0002\u0002\u0002\u0011\u0003\u0002\u0002",
    "\u0002\u0002\u0013\u0003\u0002\u0002\u0002\u0002\u0015\u0003\u0002\u0002",
    "\u0002\u0002\u0017\u0003\u0002\u0002\u0002\u0002\u0019\u0003\u0002\u0002",
    "\u0002\u0002\u001b\u0003\u0002\u0002\u0002\u0002\u001d\u0003\u0002\u0002",
    "\u0002\u0002\u001f\u0003\u0002\u0002\u0002\u0002!\u0003\u0002\u0002",
    "\u0002\u0002#\u0003\u0002\u0002\u0002\u0002%\u0003\u0002\u0002\u0002",
    "\u0002\'\u0003\u0002\u0002\u0002\u0002)\u0003\u0002\u0002\u0002\u0003",
    "+\u0003\u0002\u0002\u0002\u00052\u0003\u0002\u0002\u0002\u00079\u0003",
    "\u0002\u0002\u0002\t=\u0003\u0002\u0002\u0002\u000bA\u0003\u0002\u0002",
    "\u0002\rD\u0003\u0002\u0002\u0002\u000fL\u0003\u0002\u0002\u0002\u0011",
    "O\u0003\u0002\u0002\u0002\u0013S\u0003\u0002\u0002\u0002\u0015X\u0003",
    "\u0002\u0002\u0002\u0017^\u0003\u0002\u0002\u0002\u0019`\u0003\u0002",
    "\u0002\u0002\u001bb\u0003\u0002\u0002\u0002\u001dd\u0003\u0002\u0002",
    "\u0002\u001ff\u0003\u0002\u0002\u0002!h\u0003\u0002\u0002\u0002#j\u0003",
    "\u0002\u0002\u0002%p\u0003\u0002\u0002\u0002\'v\u0003\u0002\u0002\u0002",
    ")x\u0003\u0002\u0002\u0002+,\u0007h\u0002\u0002,-\u0007q\u0002\u0002",
    "-.\u0007t\u0002\u0002./\u0007c\u0002\u0002/0\u0007n\u0002\u000201\u0007",
    "n\u0002\u00021\u0004\u0003\u0002\u0002\u000223\u0007g\u0002\u000234",
    "\u0007z\u0002\u000245\u0007k\u0002\u000256\u0007u\u0002\u000267\u0007",
    "v\u0002\u000278\u0007u\u0002\u00028\u0006\u0003\u0002\u0002\u00029:",
    "\u0007p\u0002\u0002:;\u0007q\u0002\u0002;<\u0007v\u0002\u0002<\b\u0003",
    "\u0002\u0002\u0002=>\u0007c\u0002\u0002>?\u0007p\u0002\u0002?@\u0007",
    "f\u0002\u0002@\n\u0003\u0002\u0002\u0002AB\u0007q\u0002\u0002BC\u0007",
    "t\u0002\u0002C\f\u0003\u0002\u0002\u0002DE\u0007k\u0002\u0002EF\u0007",
    "o\u0002\u0002FG\u0007r\u0002\u0002GH\u0007n\u0002\u0002HI\u0007k\u0002",
    "\u0002IJ\u0007g\u0002\u0002JK\u0007u\u0002\u0002K\u000e\u0003\u0002",
    "\u0002\u0002LM\u0007?\u0002\u0002MN\u0007@\u0002\u0002N\u0010\u0003",
    "\u0002\u0002\u0002OP\u0007k\u0002\u0002PQ\u0007h\u0002\u0002QR\u0007",
    "h\u0002\u0002R\u0012\u0003\u0002\u0002\u0002ST\u0007v\u0002\u0002TU",
    "\u0007t\u0002\u0002UV\u0007w\u0002\u0002VW\u0007g\u0002\u0002W\u0014",
    "\u0003\u0002\u0002\u0002XY\u0007h\u0002\u0002YZ\u0007c\u0002\u0002Z",
    "[\u0007n\u0002\u0002[\\\u0007u\u0002\u0002\\]\u0007g\u0002\u0002]\u0016",
    "\u0003\u0002\u0002\u0002^_\u0007*\u0002\u0002_\u0018\u0003\u0002\u0002",
    "\u0002`a\u0007+\u0002\u0002a\u001a\u0003\u0002\u0002\u0002bc\u0007]",
    "\u0002\u0002c\u001c\u0003\u0002\u0002\u0002de\u0007_\u0002\u0002e\u001e",
    "\u0003\u0002\u0002\u0002fg\t\u0002\u0002\u0002g \u0003\u0002\u0002\u0002",
    "hi\t\u0003\u0002\u0002i\"\u0003\u0002\u0002\u0002jl\t\u0002\u0002\u0002",
    "km\t\u0004\u0002\u0002lk\u0003\u0002\u0002\u0002mn\u0003\u0002\u0002",
    "\u0002nl\u0003\u0002\u0002\u0002no\u0003\u0002\u0002\u0002o$\u0003\u0002",
    "\u0002\u0002pr\t\u0003\u0002\u0002qs\t\u0005\u0002\u0002rq\u0003\u0002",
    "\u0002\u0002st\u0003\u0002\u0002\u0002tr\u0003\u0002\u0002\u0002tu\u0003",
    "\u0002\u0002\u0002u&\u0003\u0002\u0002\u0002vw\u0007.\u0002\u0002w(",
    "\u0003\u0002\u0002\u0002xy\t\u0006\u0002\u0002yz\u0003\u0002\u0002\u0002",
    "z{\b\u0015\u0002\u0002{*\u0003\u0002\u0002\u0002\u0005\u0002nt\u0003",
    "\b\u0002\u0002"].join("");


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
iProveLexer.FORALL = 1;
iProveLexer.EXISTS = 2;
iProveLexer.NOT = 3;
iProveLexer.AND = 4;
iProveLexer.OR = 5;
iProveLexer.IMPLIES = 6;
iProveLexer.IMPLIES2 = 7;
iProveLexer.IFF = 8;
iProveLexer.TRUE = 9;
iProveLexer.FALSE = 10;
iProveLexer.BRACKET_OPEN = 11;
iProveLexer.BRACKET_CLOSE = 12;
iProveLexer.SQ_BRACKET_OPEN = 13;
iProveLexer.SQ_BRACKET_CLOSE = 14;
iProveLexer.LITERAL = 15;
iProveLexer.VARIABLE = 16;
iProveLexer.CONSTANT = 17;
iProveLexer.NAME = 18;
iProveLexer.COMMA = 19;
iProveLexer.WS = 20;

iProveLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

iProveLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

iProveLexer.prototype.literalNames = [ null, "'forall'", "'exists'", "'not'", 
                                       "'and'", "'or'", "'implies'", "'=>'", 
                                       "'iff'", "'true'", "'false'", "'('", 
                                       "')'", "'['", "']'", null, null, 
                                       null, null, "','" ];

iProveLexer.prototype.symbolicNames = [ null, "FORALL", "EXISTS", "NOT", 
                                        "AND", "OR", "IMPLIES", "IMPLIES2", 
                                        "IFF", "TRUE", "FALSE", "BRACKET_OPEN", 
                                        "BRACKET_CLOSE", "SQ_BRACKET_OPEN", 
                                        "SQ_BRACKET_CLOSE", "LITERAL", "VARIABLE", 
                                        "CONSTANT", "NAME", "COMMA", "WS" ];

iProveLexer.prototype.ruleNames = [ "FORALL", "EXISTS", "NOT", "AND", "OR", 
                                    "IMPLIES", "IMPLIES2", "IFF", "TRUE", 
                                    "FALSE", "BRACKET_OPEN", "BRACKET_CLOSE", 
                                    "SQ_BRACKET_OPEN", "SQ_BRACKET_CLOSE", 
                                    "LITERAL", "VARIABLE", "CONSTANT", "NAME", 
                                    "COMMA", "WS" ];

iProveLexer.prototype.grammarFileName = "iProve.g4";



exports.iProveLexer = iProveLexer;

