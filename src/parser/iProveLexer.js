// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\'\u00dd\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0004\u0013\t\u0013",
    "\u0004\u0014\t\u0014\u0004\u0015\t\u0015\u0004\u0016\t\u0016\u0004\u0017",
    "\t\u0017\u0004\u0018\t\u0018\u0004\u0019\t\u0019\u0004\u001a\t\u001a",
    "\u0004\u001b\t\u001b\u0004\u001c\t\u001c\u0004\u001d\t\u001d\u0004\u001e",
    "\t\u001e\u0004\u001f\t\u001f\u0004 \t \u0004!\t!\u0004\"\t\"\u0004#",
    "\t#\u0004$\t$\u0004%\t%\u0004&\t&\u0003\u0002\u0003\u0002\u0003\u0002",
    "\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006",
    "\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\b\u0003\b\u0003",
    "\b\u0003\b\u0003\t\u0003\t\u0003\t\u0003\n\u0003\n\u0003\n\u0003\n\u0003",
    "\n\u0003\n\u0003\n\u0003\n\u0003\u000b\u0003\u000b\u0003\u000b\u0003",
    "\f\u0003\f\u0003\f\u0003\r\u0003\r\u0003\r\u0003\r\u0003\u000e\u0003",
    "\u000e\u0003\u000e\u0003\u000e\u0003\u000f\u0003\u000f\u0003\u000f\u0003",
    "\u000f\u0003\u0010\u0003\u0010\u0003\u0010\u0003\u0010\u0003\u0010\u0003",
    "\u0011\u0003\u0011\u0003\u0011\u0003\u0011\u0003\u0011\u0003\u0011\u0003",
    "\u0012\u0003\u0012\u0003\u0013\u0003\u0013\u0003\u0014\u0003\u0014\u0003",
    "\u0015\u0003\u0015\u0003\u0016\u0003\u0016\u0003\u0017\u0006\u0017\u00aa",
    "\n\u0017\r\u0017\u000e\u0017\u00ab\u0003\u0018\u0003\u0018\u0003\u0019",
    "\u0003\u0019\u0003\u001a\u0006\u001a\u00b3\n\u001a\r\u001a\u000e\u001a",
    "\u00b4\u0003\u001b\u0007\u001b\u00b8\n\u001b\f\u001b\u000e\u001b\u00bb",
    "\u000b\u001b\u0003\u001b\u0003\u001b\u0006\u001b\u00bf\n\u001b\r\u001b",
    "\u000e\u001b\u00c0\u0003\u001c\u0003\u001c\u0003\u001d\u0003\u001d\u0003",
    "\u001d\u0003\u001e\u0003\u001e\u0003\u001f\u0003\u001f\u0003\u001f\u0003",
    " \u0003 \u0003 \u0003!\u0003!\u0003\"\u0003\"\u0003#\u0003#\u0003$\u0003",
    "$\u0003%\u0003%\u0003&\u0003&\u0003&\u0003&\u0002\u0002\'\u0003\u0003",
    "\u0005\u0004\u0007\u0005\t\u0006\u000b\u0007\r\b\u000f\t\u0011\n\u0013",
    "\u000b\u0015\f\u0017\r\u0019\u000e\u001b\u000f\u001d\u0010\u001f\u0011",
    "!\u0012#\u0013%\u0014\'\u0015)\u0016+\u0017-\u0018/\u00191\u001a3\u001b",
    "5\u001c7\u001d9\u001e;\u001f= ?!A\"C#E$G%I&K\'\u0003\u0002\u0007\u0003",
    "\u0002c|\u0004\u0002C\\c|\u0003\u00022;\u0003\u000200\u0005\u0002\u000b",
    "\f\u000f\u000f\"\"\u0002\u00e0\u0002\u0003\u0003\u0002\u0002\u0002\u0002",
    "\u0005\u0003\u0002\u0002\u0002\u0002\u0007\u0003\u0002\u0002\u0002\u0002",
    "\t\u0003\u0002\u0002\u0002\u0002\u000b\u0003\u0002\u0002\u0002\u0002",
    "\r\u0003\u0002\u0002\u0002\u0002\u000f\u0003\u0002\u0002\u0002\u0002",
    "\u0011\u0003\u0002\u0002\u0002\u0002\u0013\u0003\u0002\u0002\u0002\u0002",
    "\u0015\u0003\u0002\u0002\u0002\u0002\u0017\u0003\u0002\u0002\u0002\u0002",
    "\u0019\u0003\u0002\u0002\u0002\u0002\u001b\u0003\u0002\u0002\u0002\u0002",
    "\u001d\u0003\u0002\u0002\u0002\u0002\u001f\u0003\u0002\u0002\u0002\u0002",
    "!\u0003\u0002\u0002\u0002\u0002#\u0003\u0002\u0002\u0002\u0002%\u0003",
    "\u0002\u0002\u0002\u0002\'\u0003\u0002\u0002\u0002\u0002)\u0003\u0002",
    "\u0002\u0002\u0002+\u0003\u0002\u0002\u0002\u0002-\u0003\u0002\u0002",
    "\u0002\u0002/\u0003\u0002\u0002\u0002\u00021\u0003\u0002\u0002\u0002",
    "\u00023\u0003\u0002\u0002\u0002\u00025\u0003\u0002\u0002\u0002\u0002",
    "7\u0003\u0002\u0002\u0002\u00029\u0003\u0002\u0002\u0002\u0002;\u0003",
    "\u0002\u0002\u0002\u0002=\u0003\u0002\u0002\u0002\u0002?\u0003\u0002",
    "\u0002\u0002\u0002A\u0003\u0002\u0002\u0002\u0002C\u0003\u0002\u0002",
    "\u0002\u0002E\u0003\u0002\u0002\u0002\u0002G\u0003\u0002\u0002\u0002",
    "\u0002I\u0003\u0002\u0002\u0002\u0002K\u0003\u0002\u0002\u0002\u0003",
    "M\u0003\u0002\u0002\u0002\u0005T\u0003\u0002\u0002\u0002\u0007[\u0003",
    "\u0002\u0002\u0002\tb\u0003\u0002\u0002\u0002\u000bi\u0003\u0002\u0002",
    "\u0002\rn\u0003\u0002\u0002\u0002\u000fr\u0003\u0002\u0002\u0002\u0011",
    "v\u0003\u0002\u0002\u0002\u0013y\u0003\u0002\u0002\u0002\u0015\u0081",
    "\u0003\u0002\u0002\u0002\u0017\u0084\u0003\u0002\u0002\u0002\u0019\u0087",
    "\u0003\u0002\u0002\u0002\u001b\u008b\u0003\u0002\u0002\u0002\u001d\u008f",
    "\u0003\u0002\u0002\u0002\u001f\u0093\u0003\u0002\u0002\u0002!\u0098",
    "\u0003\u0002\u0002\u0002#\u009e\u0003\u0002\u0002\u0002%\u00a0\u0003",
    "\u0002\u0002\u0002\'\u00a2\u0003\u0002\u0002\u0002)\u00a4\u0003\u0002",
    "\u0002\u0002+\u00a6\u0003\u0002\u0002\u0002-\u00a9\u0003\u0002\u0002",
    "\u0002/\u00ad\u0003\u0002\u0002\u00021\u00af\u0003\u0002\u0002\u0002",
    "3\u00b2\u0003\u0002\u0002\u00025\u00b9\u0003\u0002\u0002\u00027\u00c2",
    "\u0003\u0002\u0002\u00029\u00c4\u0003\u0002\u0002\u0002;\u00c7\u0003",
    "\u0002\u0002\u0002=\u00c9\u0003\u0002\u0002\u0002?\u00cc\u0003\u0002",
    "\u0002\u0002A\u00cf\u0003\u0002\u0002\u0002C\u00d1\u0003\u0002\u0002",
    "\u0002E\u00d3\u0003\u0002\u0002\u0002G\u00d5\u0003\u0002\u0002\u0002",
    "I\u00d7\u0003\u0002\u0002\u0002K\u00d9\u0003\u0002\u0002\u0002MN\u0007",
    "c\u0002\u0002NO\u0007u\u0002\u0002OP\u0007u\u0002\u0002PQ\u0007w\u0002",
    "\u0002QR\u0007o\u0002\u0002RS\u0007g\u0002\u0002S\u0004\u0003\u0002",
    "\u0002\u0002TU\u0007h\u0002\u0002UV\u0007q\u0002\u0002VW\u0007t\u0002",
    "\u0002WX\u0007c\u0002\u0002XY\u0007n\u0002\u0002YZ\u0007n\u0002\u0002",
    "Z\u0006\u0003\u0002\u0002\u0002[\\\u0007f\u0002\u0002\\]\u0007g\u0002",
    "\u0002]^\u0007h\u0002\u0002^_\u0007k\u0002\u0002_`\u0007p\u0002\u0002",
    "`a\u0007g\u0002\u0002a\b\u0003\u0002\u0002\u0002bc\u0007g\u0002\u0002",
    "cd\u0007z\u0002\u0002de\u0007k\u0002\u0002ef\u0007u\u0002\u0002fg\u0007",
    "v\u0002\u0002gh\u0007u\u0002\u0002h\n\u0003\u0002\u0002\u0002ij\u0007",
    "g\u0002\u0002jk\u0007z\u0002\u0002kl\u0007k\u0002\u0002lm\u0007v\u0002",
    "\u0002m\f\u0003\u0002\u0002\u0002no\u0007p\u0002\u0002op\u0007q\u0002",
    "\u0002pq\u0007v\u0002\u0002q\u000e\u0003\u0002\u0002\u0002rs\u0007c",
    "\u0002\u0002st\u0007p\u0002\u0002tu\u0007f\u0002\u0002u\u0010\u0003",
    "\u0002\u0002\u0002vw\u0007q\u0002\u0002wx\u0007t\u0002\u0002x\u0012",
    "\u0003\u0002\u0002\u0002yz\u0007k\u0002\u0002z{\u0007o\u0002\u0002{",
    "|\u0007r\u0002\u0002|}\u0007n\u0002\u0002}~\u0007k\u0002\u0002~\u007f",
    "\u0007g\u0002\u0002\u007f\u0080\u0007u\u0002\u0002\u0080\u0014\u0003",
    "\u0002\u0002\u0002\u0081\u0082\u0007?\u0002\u0002\u0082\u0083\u0007",
    "@\u0002\u0002\u0083\u0016\u0003\u0002\u0002\u0002\u0084\u0085\u0007",
    "/\u0002\u0002\u0085\u0086\u0007@\u0002\u0002\u0086\u0018\u0003\u0002",
    "\u0002\u0002\u0087\u0088\u0007k\u0002\u0002\u0088\u0089\u0007h\u0002",
    "\u0002\u0089\u008a\u0007h\u0002\u0002\u008a\u001a\u0003\u0002\u0002",
    "\u0002\u008b\u008c\u0007>\u0002\u0002\u008c\u008d\u0007?\u0002\u0002",
    "\u008d\u008e\u0007@\u0002\u0002\u008e\u001c\u0003\u0002\u0002\u0002",
    "\u008f\u0090\u0007>\u0002\u0002\u0090\u0091\u0007/\u0002\u0002\u0091",
    "\u0092\u0007@\u0002\u0002\u0092\u001e\u0003\u0002\u0002\u0002\u0093",
    "\u0094\u0007v\u0002\u0002\u0094\u0095\u0007t\u0002\u0002\u0095\u0096",
    "\u0007w\u0002\u0002\u0096\u0097\u0007g\u0002\u0002\u0097 \u0003\u0002",
    "\u0002\u0002\u0098\u0099\u0007h\u0002\u0002\u0099\u009a\u0007c\u0002",
    "\u0002\u009a\u009b\u0007n\u0002\u0002\u009b\u009c\u0007u\u0002\u0002",
    "\u009c\u009d\u0007g\u0002\u0002\u009d\"\u0003\u0002\u0002\u0002\u009e",
    "\u009f\u0007*\u0002\u0002\u009f$\u0003\u0002\u0002\u0002\u00a0\u00a1",
    "\u0007+\u0002\u0002\u00a1&\u0003\u0002\u0002\u0002\u00a2\u00a3\u0007",
    "]\u0002\u0002\u00a3(\u0003\u0002\u0002\u0002\u00a4\u00a5\u0007_\u0002",
    "\u0002\u00a5*\u0003\u0002\u0002\u0002\u00a6\u00a7\t\u0002\u0002\u0002",
    "\u00a7,\u0003\u0002\u0002\u0002\u00a8\u00aa\t\u0003\u0002\u0002\u00a9",
    "\u00a8\u0003\u0002\u0002\u0002\u00aa\u00ab\u0003\u0002\u0002\u0002\u00ab",
    "\u00a9\u0003\u0002\u0002\u0002\u00ab\u00ac\u0003\u0002\u0002\u0002\u00ac",
    ".\u0003\u0002\u0002\u0002\u00ad\u00ae\u0007.\u0002\u0002\u00ae0\u0003",
    "\u0002\u0002\u0002\u00af\u00b0\u0007<\u0002\u0002\u00b02\u0003\u0002",
    "\u0002\u0002\u00b1\u00b3\t\u0004\u0002\u0002\u00b2\u00b1\u0003\u0002",
    "\u0002\u0002\u00b3\u00b4\u0003\u0002\u0002\u0002\u00b4\u00b2\u0003\u0002",
    "\u0002\u0002\u00b4\u00b5\u0003\u0002\u0002\u0002\u00b54\u0003\u0002",
    "\u0002\u0002\u00b6\u00b8\t\u0004\u0002\u0002\u00b7\u00b6\u0003\u0002",
    "\u0002\u0002\u00b8\u00bb\u0003\u0002\u0002\u0002\u00b9\u00b7\u0003\u0002",
    "\u0002\u0002\u00b9\u00ba\u0003\u0002\u0002\u0002\u00ba\u00bc\u0003\u0002",
    "\u0002\u0002\u00bb\u00b9\u0003\u0002\u0002\u0002\u00bc\u00be\t\u0005",
    "\u0002\u0002\u00bd\u00bf\t\u0004\u0002\u0002\u00be\u00bd\u0003\u0002",
    "\u0002\u0002\u00bf\u00c0\u0003\u0002\u0002\u0002\u00c0\u00be\u0003\u0002",
    "\u0002\u0002\u00c0\u00c1\u0003\u0002\u0002\u0002\u00c16\u0003\u0002",
    "\u0002\u0002\u00c2\u00c3\u0007>\u0002\u0002\u00c38\u0003\u0002\u0002",
    "\u0002\u00c4\u00c5\u0007>\u0002\u0002\u00c5\u00c6\u0007?\u0002\u0002",
    "\u00c6:\u0003\u0002\u0002\u0002\u00c7\u00c8\u0007@\u0002\u0002\u00c8",
    "<\u0003\u0002\u0002\u0002\u00c9\u00ca\u0007@\u0002\u0002\u00ca\u00cb",
    "\u0007?\u0002\u0002\u00cb>\u0003\u0002\u0002\u0002\u00cc\u00cd\u0007",
    "?\u0002\u0002\u00cd\u00ce\u0007?\u0002\u0002\u00ce@\u0003\u0002\u0002",
    "\u0002\u00cf\u00d0\u0007-\u0002\u0002\u00d0B\u0003\u0002\u0002\u0002",
    "\u00d1\u00d2\u0007/\u0002\u0002\u00d2D\u0003\u0002\u0002\u0002\u00d3",
    "\u00d4\u0007`\u0002\u0002\u00d4F\u0003\u0002\u0002\u0002\u00d5\u00d6",
    "\u0007,\u0002\u0002\u00d6H\u0003\u0002\u0002\u0002\u00d7\u00d8\u0007",
    "1\u0002\u0002\u00d8J\u0003\u0002\u0002\u0002\u00d9\u00da\t\u0006\u0002",
    "\u0002\u00da\u00db\u0003\u0002\u0002\u0002\u00db\u00dc\b&\u0002\u0002",
    "\u00dcL\u0003\u0002\u0002\u0002\u0007\u0002\u00ab\u00b4\u00b9\u00c0",
    "\u0003\b\u0002\u0002"].join("");


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
iProveLexer.INTEGER = 25;
iProveLexer.REAL = 26;
iProveLexer.LESSTHAN = 27;
iProveLexer.LESSTHANEQ = 28;
iProveLexer.GREATERTHAN = 29;
iProveLexer.GREATERTHANEQ = 30;
iProveLexer.DOUBLEEQUALS = 31;
iProveLexer.PLUS = 32;
iProveLexer.MINUS = 33;
iProveLexer.POWER = 34;
iProveLexer.MULTIPLY = 35;
iProveLexer.DIVIDE = 36;
iProveLexer.WS = 37;

iProveLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

iProveLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

iProveLexer.prototype.literalNames = [ null, "'assume'", "'forall'", "'define'", 
                                       "'exists'", "'exit'", "'not'", "'and'", 
                                       "'or'", "'implies'", "'=>'", "'->'", 
                                       "'iff'", "'<=>'", "'<->'", "'true'", 
                                       "'false'", "'('", "')'", "'['", "']'", 
                                       null, null, "','", "':'", null, null, 
                                       "'<'", "'<='", "'>'", "'>='", "'=='", 
                                       "'+'", "'-'", "'^'", "'*'", "'/'" ];

iProveLexer.prototype.symbolicNames = [ null, "ASSUME", "FORALL", "DEFINE", 
                                        "EXISTS", "EXIT", "NOT", "AND", 
                                        "OR", "IMPLIES", "IMPLIES2", "IMPLIES3", 
                                        "IFF", "IFF2", "IFF3", "TRUE", "FALSE", 
                                        "BRACKET_OPEN", "BRACKET_CLOSE", 
                                        "SQ_BRACKET_OPEN", "SQ_BRACKET_CLOSE", 
                                        "VARIABLE", "IDENTIFIER", "COMMA", 
                                        "COLON", "INTEGER", "REAL", "LESSTHAN", 
                                        "LESSTHANEQ", "GREATERTHAN", "GREATERTHANEQ", 
                                        "DOUBLEEQUALS", "PLUS", "MINUS", 
                                        "POWER", "MULTIPLY", "DIVIDE", "WS" ];

iProveLexer.prototype.ruleNames = [ "ASSUME", "FORALL", "DEFINE", "EXISTS", 
                                    "EXIT", "NOT", "AND", "OR", "IMPLIES", 
                                    "IMPLIES2", "IMPLIES3", "IFF", "IFF2", 
                                    "IFF3", "TRUE", "FALSE", "BRACKET_OPEN", 
                                    "BRACKET_CLOSE", "SQ_BRACKET_OPEN", 
                                    "SQ_BRACKET_CLOSE", "VARIABLE", "IDENTIFIER", 
                                    "COMMA", "COLON", "INTEGER", "REAL", 
                                    "LESSTHAN", "LESSTHANEQ", "GREATERTHAN", 
                                    "GREATERTHANEQ", "DOUBLEEQUALS", "PLUS", 
                                    "MINUS", "POWER", "MULTIPLY", "DIVIDE", 
                                    "WS" ];

iProveLexer.prototype.grammarFileName = "iProve.g4";



exports.iProveLexer = iProveLexer;

