// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\u001b\u009d\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0004\u0013\t\u0013",
    "\u0004\u0014\t\u0014\u0004\u0015\t\u0015\u0004\u0016\t\u0016\u0004\u0017",
    "\t\u0017\u0004\u0018\t\u0018\u0004\u0019\t\u0019\u0004\u001a\t\u001a",
    "\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002",
    "\u0003\u0002\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0006\u0003\u0006",
    "\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0007\u0003\u0007\u0003\u0007",
    "\u0003\u0007\u0003\b\u0003\b\u0003\b\u0003\b\u0003\t\u0003\t\u0003\t",
    "\u0003\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003",
    "\u000b\u0003\u000b\u0003\u000b\u0003\f\u0003\f\u0003\f\u0003\r\u0003",
    "\r\u0003\r\u0003\r\u0003\u000e\u0003\u000e\u0003\u000e\u0003\u000e\u0003",
    "\u000f\u0003\u000f\u0003\u000f\u0003\u000f\u0003\u0010\u0003\u0010\u0003",
    "\u0010\u0003\u0010\u0003\u0010\u0003\u0011\u0003\u0011\u0003\u0011\u0003",
    "\u0011\u0003\u0011\u0003\u0011\u0003\u0012\u0003\u0012\u0003\u0013\u0003",
    "\u0013\u0003\u0014\u0003\u0014\u0003\u0015\u0003\u0015\u0003\u0016\u0003",
    "\u0016\u0003\u0017\u0006\u0017\u0092\n\u0017\r\u0017\u000e\u0017\u0093",
    "\u0003\u0018\u0003\u0018\u0003\u0019\u0003\u0019\u0003\u001a\u0003\u001a",
    "\u0003\u001a\u0003\u001a\u0002\u0002\u001b\u0003\u0003\u0005\u0004\u0007",
    "\u0005\t\u0006\u000b\u0007\r\b\u000f\t\u0011\n\u0013\u000b\u0015\f\u0017",
    "\r\u0019\u000e\u001b\u000f\u001d\u0010\u001f\u0011!\u0012#\u0013%\u0014",
    "\'\u0015)\u0016+\u0017-\u0018/\u00191\u001a3\u001b\u0003\u0002\u0005",
    "\u0003\u0002c|\u0004\u0002C\\c|\u0005\u0002\u000b\f\u000f\u000f\"\"",
    "\u0002\u009d\u0002\u0003\u0003\u0002\u0002\u0002\u0002\u0005\u0003\u0002",
    "\u0002\u0002\u0002\u0007\u0003\u0002\u0002\u0002\u0002\t\u0003\u0002",
    "\u0002\u0002\u0002\u000b\u0003\u0002\u0002\u0002\u0002\r\u0003\u0002",
    "\u0002\u0002\u0002\u000f\u0003\u0002\u0002\u0002\u0002\u0011\u0003\u0002",
    "\u0002\u0002\u0002\u0013\u0003\u0002\u0002\u0002\u0002\u0015\u0003\u0002",
    "\u0002\u0002\u0002\u0017\u0003\u0002\u0002\u0002\u0002\u0019\u0003\u0002",
    "\u0002\u0002\u0002\u001b\u0003\u0002\u0002\u0002\u0002\u001d\u0003\u0002",
    "\u0002\u0002\u0002\u001f\u0003\u0002\u0002\u0002\u0002!\u0003\u0002",
    "\u0002\u0002\u0002#\u0003\u0002\u0002\u0002\u0002%\u0003\u0002\u0002",
    "\u0002\u0002\'\u0003\u0002\u0002\u0002\u0002)\u0003\u0002\u0002\u0002",
    "\u0002+\u0003\u0002\u0002\u0002\u0002-\u0003\u0002\u0002\u0002\u0002",
    "/\u0003\u0002\u0002\u0002\u00021\u0003\u0002\u0002\u0002\u00023\u0003",
    "\u0002\u0002\u0002\u00035\u0003\u0002\u0002\u0002\u0005<\u0003\u0002",
    "\u0002\u0002\u0007C\u0003\u0002\u0002\u0002\tJ\u0003\u0002\u0002\u0002",
    "\u000bQ\u0003\u0002\u0002\u0002\rV\u0003\u0002\u0002\u0002\u000fZ\u0003",
    "\u0002\u0002\u0002\u0011^\u0003\u0002\u0002\u0002\u0013a\u0003\u0002",
    "\u0002\u0002\u0015i\u0003\u0002\u0002\u0002\u0017l\u0003\u0002\u0002",
    "\u0002\u0019o\u0003\u0002\u0002\u0002\u001bs\u0003\u0002\u0002\u0002",
    "\u001dw\u0003\u0002\u0002\u0002\u001f{\u0003\u0002\u0002\u0002!\u0080",
    "\u0003\u0002\u0002\u0002#\u0086\u0003\u0002\u0002\u0002%\u0088\u0003",
    "\u0002\u0002\u0002\'\u008a\u0003\u0002\u0002\u0002)\u008c\u0003\u0002",
    "\u0002\u0002+\u008e\u0003\u0002\u0002\u0002-\u0091\u0003\u0002\u0002",
    "\u0002/\u0095\u0003\u0002\u0002\u00021\u0097\u0003\u0002\u0002\u0002",
    "3\u0099\u0003\u0002\u0002\u000256\u0007c\u0002\u000267\u0007u\u0002",
    "\u000278\u0007u\u0002\u000289\u0007w\u0002\u00029:\u0007o\u0002\u0002",
    ":;\u0007g\u0002\u0002;\u0004\u0003\u0002\u0002\u0002<=\u0007h\u0002",
    "\u0002=>\u0007q\u0002\u0002>?\u0007t\u0002\u0002?@\u0007c\u0002\u0002",
    "@A\u0007n\u0002\u0002AB\u0007n\u0002\u0002B\u0006\u0003\u0002\u0002",
    "\u0002CD\u0007f\u0002\u0002DE\u0007g\u0002\u0002EF\u0007h\u0002\u0002",
    "FG\u0007k\u0002\u0002GH\u0007p\u0002\u0002HI\u0007g\u0002\u0002I\b\u0003",
    "\u0002\u0002\u0002JK\u0007g\u0002\u0002KL\u0007z\u0002\u0002LM\u0007",
    "k\u0002\u0002MN\u0007u\u0002\u0002NO\u0007v\u0002\u0002OP\u0007u\u0002",
    "\u0002P\n\u0003\u0002\u0002\u0002QR\u0007g\u0002\u0002RS\u0007z\u0002",
    "\u0002ST\u0007k\u0002\u0002TU\u0007v\u0002\u0002U\f\u0003\u0002\u0002",
    "\u0002VW\u0007p\u0002\u0002WX\u0007q\u0002\u0002XY\u0007v\u0002\u0002",
    "Y\u000e\u0003\u0002\u0002\u0002Z[\u0007c\u0002\u0002[\\\u0007p\u0002",
    "\u0002\\]\u0007f\u0002\u0002]\u0010\u0003\u0002\u0002\u0002^_\u0007",
    "q\u0002\u0002_`\u0007t\u0002\u0002`\u0012\u0003\u0002\u0002\u0002ab",
    "\u0007k\u0002\u0002bc\u0007o\u0002\u0002cd\u0007r\u0002\u0002de\u0007",
    "n\u0002\u0002ef\u0007k\u0002\u0002fg\u0007g\u0002\u0002gh\u0007u\u0002",
    "\u0002h\u0014\u0003\u0002\u0002\u0002ij\u0007?\u0002\u0002jk\u0007@",
    "\u0002\u0002k\u0016\u0003\u0002\u0002\u0002lm\u0007/\u0002\u0002mn\u0007",
    "@\u0002\u0002n\u0018\u0003\u0002\u0002\u0002op\u0007k\u0002\u0002pq",
    "\u0007h\u0002\u0002qr\u0007h\u0002\u0002r\u001a\u0003\u0002\u0002\u0002",
    "st\u0007>\u0002\u0002tu\u0007?\u0002\u0002uv\u0007@\u0002\u0002v\u001c",
    "\u0003\u0002\u0002\u0002wx\u0007>\u0002\u0002xy\u0007/\u0002\u0002y",
    "z\u0007@\u0002\u0002z\u001e\u0003\u0002\u0002\u0002{|\u0007v\u0002\u0002",
    "|}\u0007t\u0002\u0002}~\u0007w\u0002\u0002~\u007f\u0007g\u0002\u0002",
    "\u007f \u0003\u0002\u0002\u0002\u0080\u0081\u0007h\u0002\u0002\u0081",
    "\u0082\u0007c\u0002\u0002\u0082\u0083\u0007n\u0002\u0002\u0083\u0084",
    "\u0007u\u0002\u0002\u0084\u0085\u0007g\u0002\u0002\u0085\"\u0003\u0002",
    "\u0002\u0002\u0086\u0087\u0007*\u0002\u0002\u0087$\u0003\u0002\u0002",
    "\u0002\u0088\u0089\u0007+\u0002\u0002\u0089&\u0003\u0002\u0002\u0002",
    "\u008a\u008b\u0007]\u0002\u0002\u008b(\u0003\u0002\u0002\u0002\u008c",
    "\u008d\u0007_\u0002\u0002\u008d*\u0003\u0002\u0002\u0002\u008e\u008f",
    "\t\u0002\u0002\u0002\u008f,\u0003\u0002\u0002\u0002\u0090\u0092\t\u0003",
    "\u0002\u0002\u0091\u0090\u0003\u0002\u0002\u0002\u0092\u0093\u0003\u0002",
    "\u0002\u0002\u0093\u0091\u0003\u0002\u0002\u0002\u0093\u0094\u0003\u0002",
    "\u0002\u0002\u0094.\u0003\u0002\u0002\u0002\u0095\u0096\u0007.\u0002",
    "\u0002\u00960\u0003\u0002\u0002\u0002\u0097\u0098\u0007<\u0002\u0002",
    "\u00982\u0003\u0002\u0002\u0002\u0099\u009a\t\u0004\u0002\u0002\u009a",
    "\u009b\u0003\u0002\u0002\u0002\u009b\u009c\b\u001a\u0002\u0002\u009c",
    "4\u0003\u0002\u0002\u0002\u0004\u0002\u0093\u0003\b\u0002\u0002"].join("");


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
iProveLexer.DEFINE = 3;
iProveLexer.EXISTS = 4;
iProveLexer.EXIT = 5;
iProveLexer.NOT = 6;
iProveLexer.AND = 7;
iProveLexer.OR = 8;
iProveLexer.IMPLIES = 9;
iProveLexer.IMPLIES2 = 10;
iProveLexer.IMPLIES3 = 11;
iProveLexer.IFF = 12;
iProveLexer.IFF2 = 13;
iProveLexer.IFF3 = 14;
iProveLexer.TRUE = 15;
iProveLexer.FALSE = 16;
iProveLexer.BRACKET_OPEN = 17;
iProveLexer.BRACKET_CLOSE = 18;
iProveLexer.SQ_BRACKET_OPEN = 19;
iProveLexer.SQ_BRACKET_CLOSE = 20;
iProveLexer.VARIABLE = 21;
iProveLexer.IDENTIFIER = 22;
iProveLexer.COMMA = 23;
iProveLexer.COLON = 24;
iProveLexer.WS = 25;

iProveLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

iProveLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

iProveLexer.prototype.literalNames = [ null, "'assume'", "'forall'", "'define'", 
                                       "'exists'", "'exit'", "'not'", "'and'", 
                                       "'or'", "'implies'", "'=>'", "'->'", 
                                       "'iff'", "'<=>'", "'<->'", "'true'", 
                                       "'false'", "'('", "')'", "'['", "']'", 
                                       null, null, "','", "':'" ];

iProveLexer.prototype.symbolicNames = [ null, "ASSUME", "FORALL", "DEFINE", 
                                        "EXISTS", "EXIT", "NOT", "AND", 
                                        "OR", "IMPLIES", "IMPLIES2", "IMPLIES3", 
                                        "IFF", "IFF2", "IFF3", "TRUE", "FALSE", 
                                        "BRACKET_OPEN", "BRACKET_CLOSE", 
                                        "SQ_BRACKET_OPEN", "SQ_BRACKET_CLOSE", 
                                        "VARIABLE", "IDENTIFIER", "COMMA", 
                                        "COLON", "WS" ];

iProveLexer.prototype.ruleNames = [ "ASSUME", "FORALL", "DEFINE", "EXISTS", 
                                    "EXIT", "NOT", "AND", "OR", "IMPLIES", 
                                    "IMPLIES2", "IMPLIES3", "IFF", "IFF2", 
                                    "IFF3", "TRUE", "FALSE", "BRACKET_OPEN", 
                                    "BRACKET_CLOSE", "SQ_BRACKET_OPEN", 
                                    "SQ_BRACKET_CLOSE", "VARIABLE", "IDENTIFIER", 
                                    "COMMA", "COLON", "WS" ];

iProveLexer.prototype.grammarFileName = "iProve.g4";



exports.iProveLexer = iProveLexer;

